"""Следит за публичными Telegram-каналами с вакансиями и присылает подходящие по брифу в Telegram.

Запуск по расписанию в GitHub Actions. Каждый запуск:
  1. читает веб-версию каналов (https://t.me/s/<канал>), только свежую страницу;
  2. отбирает посты по брифу (роль, бюджет, стоп-слова, возраст поста);
  3. отправляет новые подходящие посты в Telegram и запоминает их в state/seen.json.
"""
from __future__ import annotations

import argparse
import html
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path

from bs4 import BeautifulSoup

HERE = Path(__file__).resolve().parent
CONFIG = HERE / "config.json"
STATE = HERE / "state" / "seen.json"
SITE_LEADS = HERE / "docs" / "leads.json"
SITE_LEADS_MAX = 1000
MSK = timezone(timedelta(hours=3))
UA = "Mozilla/5.0 (compatible; lead-watch/1.0)"
TOKEN_RE = re.compile(r"^\d{5,}:[A-Za-z0-9_-]{30,}$")
CHAT_RE = re.compile(r"^(-?\d{3,}|@[A-Za-z0-9_]{5,})$")
POST_ID_RE = re.compile(r"^[A-Za-z0-9_]{4,64}/\d{1,9}$")

# ---------- фильтр по брифу (чистые функции) ----------

ROLE_RE = re.compile(
    r"smm|смм|контент[- ]?маркетолог|продюсер|редактор|автор\w*\s+текст|копирайтер|сценарист",
    re.I,
)
STOP_RES = {
    "тестовое задание": re.compile(r"тестов\w*\s+задани|тестовое\b", re.I),
    "анкета": re.compile(r"анкет|google\s*-?\s*форм|forms\.gle|docs\.google\.com/forms", re.I),
    "много этапов отбора": re.compile(r"этап\w*\s+отбор|следующ\w+\s+этап|несколько\s+этап", re.I),
}
RESUME_RE = re.compile(r"#резюме|^\s*резюме\b|ищу\s+работу", re.I | re.M)
CLOSED_RE = re.compile(r"вакансия\s+закрыта", re.I)

_NUM = r"\d{1,3}(?:[   .]\d{3})+|\d+(?:[.,]\d+)?"
MONEY_RE = re.compile(
    rf"(?P<pre>\bот|\bдо)?\s*(?P<a>{_NUM})\s*(?P<ma>к\b|k\b|тыс\.?|т\.?\s?р\.?)?"
    rf"(?:\s*(?:[-–—]\s*(?:до\s*)?|до\s+)(?P<b>{_NUM})\s*(?P<mb>к\b|k\b|тыс\.?|т\.?\s?р\.?)?)?"
    rf"\s*(?P<cur>₽|руб\w*|р\.(?!\w))?"
    rf"(?P<per>\s*(?:/|в|за)\s*(?:час|смену|день|недел\w*))?",
    re.I,
)


NOT_MONEY_AFTER_RE = re.compile(
    r"\w*\s*(?:подписчик|просмотр|человек|пользовател|клиент|охват|участник|лайк|заказ|учеников|студент)",
    re.I,
)
PAY_CONTEXT_RE = re.compile(r"зп|з/п|зарплат|оплат|доход|оклад|бюджет|ставк|фикс|вилк|выплат|\bот\b|\bдо\b", re.I)


def _to_rub(num: str, mult: str | None) -> int | None:
    s = re.sub(r"[   ]", "", num)
    if re.fullmatch(r"\d{1,3}(?:\.\d{3})+", s):
        s = s.replace(".", "")
    try:
        v = float(s.replace(",", "."))
    except ValueError:
        return None
    if mult:
        v *= 1000
    return int(v)


def parse_budget(text: str) -> tuple[int | None, int | None]:
    """(нижняя граница, верхняя граница) месячной оплаты в рублях; None — не найдено.

    Учитываются только суммы с явной валютой (₽, руб) или множителем (к, тыс).
    Почасовые, посменные суммы и суммы меньше 1000 ₽ отбрасываются.
    Если в посте несколько сумм, берётся самая высокая нижняя граница.
    """
    lowers, uppers = [], []
    for m in MONEY_RE.finditer(text):
        if not (m.group("cur") or m.group("ma") or m.group("mb")) or m.group("per"):
            continue
        if NOT_MONEY_AFTER_RE.match(text, m.end()):
            continue
        if not m.group("cur") and not PAY_CONTEXT_RE.search(text[max(0, m.start() - 40):m.start()]):
            continue
        shared = m.group("mb") or m.group("ma")
        a = _to_rub(m.group("a"), m.group("ma") or (shared if m.group("b") else None))
        b = _to_rub(m.group("b"), m.group("mb") or shared) if m.group("b") else None
        if a is None or a < 1000 or a > 10_000_000:
            continue
        if b is not None and (b < a or b > 10_000_000):
            b = None
        pre = (m.group("pre") or "").lower()
        if pre == "до" and b is None:
            uppers.append(a)
        else:
            lowers.append(a)
            if b:
                uppers.append(b)
    return (max(lowers) if lowers else None, max(uppers) if uppers else None)


@dataclass
class Verdict:
    send: bool
    level: str  # ok | warn | skip
    reason: str
    low: int | None = None
    high: int | None = None


def judge(text: str, min_budget: int, floor_budget: int) -> Verdict:
    if CLOSED_RE.search(text):
        return Verdict(False, "skip", "вакансия закрыта")
    if RESUME_RE.search(text):
        return Verdict(False, "skip", "резюме, а не вакансия")
    if not ROLE_RE.search(text):
        return Verdict(False, "skip", "роль не из брифа")
    for name, rx in STOP_RES.items():
        if rx.search(text):
            return Verdict(False, "skip", name)
    low, high = parse_budget(text)
    if low is None:
        return Verdict(True, "warn", "бюджет не указан или только потолок", low, high)
    if low < floor_budget:
        return Verdict(False, "skip", f"бюджет от {low} ниже {floor_budget}", low, high)
    if low < min_budget:
        return Verdict(True, "warn", f"ниже целевых {min_budget}", low, high)
    return Verdict(True, "ok", "подходит", low, high)


def rub(n: int) -> str:
    return f"{n:,}".replace(",", " ") + " ₽"


def format_message(post_id: str, text: str, v: Verdict) -> str:
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    title = lines[0][:140] if lines else "Вакансия"
    body = " ".join(lines[1:])
    excerpt = body[:450] + ("…" if len(body) > 450 else "")
    label = "✅ Подходит" if v.level == "ok" else "🟡 Уточнить: " + v.reason
    if v.low:
        budget = "от " + rub(v.low) + (" до " + rub(v.high) if v.high and v.high > v.low else "")
    elif v.high:
        budget = "до " + rub(v.high)
    else:
        budget = "не указан"
    channel = post_id.split("/")[0]
    out = [
        f"<b>{html.escape(label)}</b>",
        f"<b>{html.escape(title)}</b>",
        html.escape("Бюджет: " + budget),
    ]
    if excerpt:
        out.append(html.escape(excerpt))
    out.append(f'<a href="https://t.me/{html.escape(post_id)}">Открыть пост</a> · @{html.escape(channel)}')
    return "\n".join(out)[:4096]


ROLE_LABEL_RE = re.compile(r"(?:должность|позиция|роль)\b\s*[:—–-]?\s*(.+)", re.I)
LEAD_JUNK_RE = re.compile(r"^[^\wЁё]+")


def extract_role(text: str) -> str:
    lines = [LEAD_JUNK_RE.sub("", ln).strip() for ln in text.splitlines()]
    lines = [ln for ln in lines if ln]
    for i, ln in enumerate(lines[:12]):
        if re.fullmatch(r"(?:должность|позиция|роль)\s*:?", ln, re.I) and i + 1 < len(lines):
            return lines[i + 1][:120]
        m = ROLE_LABEL_RE.match(ln)
        if m:
            return m.group(1).strip()[:120]
    for ln in lines[:12]:
        if ROLE_RE.search(ln) and len(ln) <= 80 and not re.match(r"(о\s+)?компани", ln, re.I):
            return ln[:120]
    return (lines[0] if lines else "Вакансия")[:120]


def site_lead(post_id: str, text: str, v: Verdict, now: datetime) -> dict:
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    body = " ".join(lines)
    return {
        "id": "tg-" + post_id.replace("/", "-"),
        "url": f"https://t.me/{post_id}",
        "role": extract_role(text),
        "platform": "Telegram-чат",
        "client": "",
        "budget": v.low,
        "summary": body[:400] + ("…" if len(body) > 400 else ""),
        "level": v.level,
        "verdictText": "Подходит" if v.level == "ok" else "Уточнить: " + v.reason,
        "createdAt": now.isoformat().replace("+00:00", "Z"),
        "day": now.astimezone(MSK).date().isoformat(),
        "source": "bot",
    }


def load_site_leads() -> list[dict]:
    if not SITE_LEADS.is_file():
        return []
    data = json.loads(SITE_LEADS.read_text(encoding="utf-8"))
    items = data.get("leads", []) if isinstance(data, dict) else []
    return [x for x in items if isinstance(x, dict) and isinstance(x.get("id"), str)]


def save_site_leads(items: list[dict]) -> None:
    items = sorted(items, key=lambda x: str(x.get("createdAt", "")), reverse=True)[:SITE_LEADS_MAX]
    SITE_LEADS.parent.mkdir(parents=True, exist_ok=True)
    tmp = SITE_LEADS.with_suffix(".tmp")
    tmp.write_text(json.dumps({"leads": items}, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, SITE_LEADS)


# ---------- сеть ----------

def fetch(url: str) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Language": "ru"})
    with urllib.request.urlopen(req, timeout=25) as r:
        if r.status != 200:
            raise RuntimeError(f"HTTP {r.status}")
        return r.read().decode("utf-8", "replace")


def parse_channel(page: str) -> list[tuple[str, datetime | None, str]]:
    soup = BeautifulSoup(page, "html.parser")
    posts = []
    for node in soup.select("div.tgme_widget_message[data-post]"):
        pid = node.get("data-post", "")
        if not POST_ID_RE.match(pid):
            continue
        text_node = node.select_one(".tgme_widget_message_text")
        if text_node is None:
            continue
        for br in text_node.find_all("br"):
            br.replace_with("\n")
        text = text_node.get_text()
        when = None
        t = node.select_one("time[datetime]")
        if t is not None:
            try:
                when = datetime.fromisoformat(t["datetime"])
            except ValueError:
                when = None
        posts.append((pid, when, text))
    return posts


def tg_send(token: str, chat: str, text: str) -> tuple[bool, str]:
    body = urllib.parse.urlencode({
        "chat_id": chat, "text": text, "parse_mode": "HTML", "disable_web_page_preview": "true",
    }).encode()
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    for attempt in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, data=body), timeout=20) as r:
                res = json.loads(r.read().decode())
                return bool(res.get("ok")), str(res.get("description", ""))
        except urllib.error.HTTPError as e:
            try:
                res = json.loads(e.read().decode())
            except (ValueError, OSError):
                res = {"description": f"HTTP {e.code}"}
            retry = (res.get("parameters") or {}).get("retry_after")
            if e.code == 429 and isinstance(retry, int) and attempt < 2:
                time.sleep(min(retry, 60) + 1)
                continue
            return False, str(res.get("description", f"HTTP {e.code}"))
        except (urllib.error.URLError, TimeoutError) as e:
            if attempt < 2:
                time.sleep(3)
                continue
            return False, f"сеть: {e}"
    return False, "исчерпаны попытки"


# ---------- состояние ----------

def load_state() -> dict[str, str]:
    if not STATE.is_file():
        return {}
    data = json.loads(STATE.read_text(encoding="utf-8"))
    seen = data.get("seen", {}) if isinstance(data, dict) else {}
    return {k: v for k, v in seen.items() if isinstance(k, str) and isinstance(v, str)}


def save_state(seen: dict[str, str], keep_days: int) -> None:
    cutoff = (datetime.now(timezone.utc) - timedelta(days=keep_days)).isoformat()
    seen = {k: v for k, v in seen.items() if v >= cutoff}
    STATE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE.with_suffix(".tmp")
    tmp.write_text(json.dumps({"seen": dict(sorted(seen.items()))}, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, STATE)


# ---------- основной цикл ----------

def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):
            pass
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true", help="показать решения и сообщения, ничего не отправлять и не сохранять")
    args = ap.parse_args()

    cfg = json.loads(CONFIG.read_text(encoding="utf-8"))
    channels = [c for c in cfg["channels"] if re.fullmatch(r"[A-Za-z0-9_]{4,64}", c)]
    min_budget, floor_budget = int(cfg["min_budget"]), int(cfg["floor_budget"])
    max_age = timedelta(hours=int(cfg["max_age_hours"]))

    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    chat = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
    if not args.dry_run and not (TOKEN_RE.match(token) and CHAT_RE.match(chat)):
        print("Не заданы корректные TELEGRAM_BOT_TOKEN и TELEGRAM_CHAT_ID (секреты репозитория).")
        return 2

    seen = load_state()
    site = load_site_leads()
    site_ids = {x["id"] for x in site}
    now = datetime.now(timezone.utc)
    sent = skipped = 0
    failed = False
    for ch in channels:
        try:
            posts = parse_channel(fetch(f"https://t.me/s/{ch}"))
        except Exception as e:  # один недоступный канал не должен ронять остальные
            print(f"[{ch}] не загрузился: {e}")
            continue
        print(f"[{ch}] постов на странице: {len(posts)}")
        for pid, when, text in posts:
            if pid in seen:
                continue
            if when is None or now - when > max_age:
                seen[pid] = now.isoformat()
                continue
            v = judge(text, min_budget, floor_budget)
            if not v.send:
                skipped += 1
                seen[pid] = now.isoformat()
                if args.dry_run:
                    print(f"  пропуск {pid}: {v.reason}")
                continue
            msg = format_message(pid, text, v)
            lead = site_lead(pid, text, v, now)
            if args.dry_run:
                print(f"  ОТПРАВИЛ БЫ {pid} [{v.level}] роль на сайте: {lead['role']}\n{msg}\n")
                continue
            if lead["id"] in site_ids:  # уже есть на сайте (найдено вручную) — в Telegram не дублируем
                seen[pid] = now.isoformat()
                continue
            ok, err = tg_send(token, chat, msg)
            if not ok:
                print(f"Telegram не принял {pid}: {err}. Остальное уйдёт при следующем запуске.")
                failed = True
                break
            seen[pid] = now.isoformat()
            site.append(lead)
            site_ids.add(lead["id"])
            sent += 1
            time.sleep(1.1)
        if failed:
            break
    if not args.dry_run:
        save_state(seen, int(cfg["keep_state_days"]))
        if sent:
            save_site_leads(site)
    print(f"Отправлено: {sent}, отсеяно: {skipped}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
