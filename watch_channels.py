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
RESUME_RE = re.compile(
    r"#резюме|^\s*резюме\b|ищу\s+работу|ищу\s+(?:новых\s+)?(?:клиентов|проекты|заказы)|возьму\s+(?:в\s+работу|проект)"
    r"|беру\s+(?:в\s+работу|проекты|новых)|^\s*я\s*[—–-]\s*[А-ЯЁA-Z]\w+\.",
    re.I | re.M,
)
VACANCY_SIGNALS = [
    re.compile(r"ваканси[яю]\b|ищем|ищу\s+(?:в\s+команду|специалист|smm|смм|копирайт|редактор|сценарист|продюсер|автор)|требуется|нужен\b|нужна\b|в\s+команду", re.I),
    re.compile(r"обязанност|задачи|что\s+(?:нужно|предстоит)\s+делать|чем\s+предстоит", re.I),
    re.compile(r"условия\b|мы\s+предлагаем|график|формат\s+работы|удал[её]нн?о|удал[её]нка|гибрид|в\s+офис", re.I),
    re.compile(r"кому\s+писать|откликнуться|отклик\w*\s*:|пишите|резюме\s+(?:присылайте|отправляйте|в\s+лс)|контакт\w*\s*:", re.I),
    re.compile(r"зарплат|оплат|з/п|\bзп\b|оклад|доход|ставк|бюджет|₽|руб", re.I),
    re.compile(r"требования|ожидаем|опыт\s+(?:от|работы)|кого\s+ищем|навыки", re.I),
]


OFFICE_RE = re.compile(r"офис\w*|гибрид\w*", re.I)
NO_OFFICE_RE = re.compile(
    r"(?:без|вне|вместо|никакого|нет)\s+(?:\w+\s+){0,2}(?:офис|гибрид)"
    r"|не\s+(?:нужно|надо|требуется|обязательно|придётся|придется|ходить|ездить)\s+(?:\w+\s+){0,3}(?:в\s+)?офис",
    re.I,
)


def mentions_office(text: str) -> bool:
    """Работа в офисе или гибрид. Отрицания («без офиса», «не нужно ездить в офис») не считаются."""
    for m in OFFICE_RE.finditer(text):
        ctx = text[max(0, m.start() - 45):m.end()]
        if not NO_OFFICE_RE.search(ctx):
            return True
    return False


def looks_like_vacancy(text: str) -> bool:
    return sum(1 for rx in VACANCY_SIGNALS if rx.search(text)) >= 2
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
    if mentions_office(text):
        return Verdict(False, "skip", "офис или гибрид")
    if not looks_like_vacancy(text):
        return Verdict(False, "skip", "не похоже на вакансию")
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


def budget_text(v: Verdict) -> str:
    if v.low:
        return "от " + rub(v.low) + (" до " + rub(v.high) if v.high and v.high > v.low else "")
    if v.high:
        return "до " + rub(v.high)
    return ""


def description(text: str, role: str, limit: int = 450) -> str:
    """Текст поста без строки с ролью и служебных меток, в одну строку."""
    lines = [LEAD_JUNK_RE.sub("", HASHTAG_RE.sub("", ln)).strip() for ln in text.splitlines()]
    skip = {role.strip().lower(), "должность", "работодатель", "вакансия"}
    kept = [ln for ln in lines if ln and ln.lower().rstrip(":") not in skip]
    body = re.sub(r"\s+", " ", " ".join(kept)).strip()
    return body[:limit] + ("…" if len(body) > limit else "")


# ---------- контакты ----------

USERNAME_RE = re.compile(r"(?<![\w.@/])@([A-Za-z][A-Za-z0-9_]{3,31})\b")
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
PHONE_RE = re.compile(r"(?<!\d)(?:\+7|8)[\s(-]*\d{3}[\s)-]*\d{3}[\s-]*\d{2}[\s-]*\d{2}(?!\d)")
APPLY_TEXT_RE = re.compile(r"отклик|откликнуться|написать|связ|резюме|hr|рекрутер|apply|подать", re.I)
TME_RE = re.compile(r"^https?://(?:t\.me|telegram\.me)/([A-Za-z][A-Za-z0-9_]{3,31})/?$", re.I)


TME_TEXT_RE = re.compile(r"(?<![\w/])(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z][A-Za-z0-9_]{3,31})\b", re.I)


def channel_boilerplate(posts: list[tuple], min_count: int = 3) -> set[str]:
    """@username и ссылки, которые стоят в половине постов канала и больше: это подпись канала, а не работодатель."""
    counts: dict[str, int] = {}
    for _, _, text, links in posts:
        names = {m.group(1).lower() for m in USERNAME_RE.finditer(text)}
        names |= {m.group(1).lower() for href, _ in links if (m := TME_RE.match(href.strip()))}
        names |= {clean_url(href.strip()).lower() for href, _ in links if href.strip().startswith("https://")}
        for n in names:
            counts[n] = counts.get(n, 0) + 1
    threshold = max(min_count, len(posts) // 2)
    return {n for n, c in counts.items() if c >= threshold}


def clean_url(href: str) -> str:
    p = urllib.parse.urlsplit(href)
    return urllib.parse.urlunsplit((p.scheme, p.netloc, p.path, "", ""))


def extract_contacts(text: str, links: list[tuple[str, str]], channel: str,
                     ignore: set[str] = frozenset(), limit: int = 4) -> list[str]:
    """Контакты для отклика: ссылки-кнопки «Откликнуться», @username, t.me-ссылки, почта, телефон.

    Ссылки на сам канал, хештеги, посты канала и подписи канала (ignore) не считаются контактами.
    """
    out: list[str] = []

    def add(item: str) -> None:
        key = item.lower()
        if item and key not in (x.lower() for x in out) and len(out) < limit:
            out.append(item)

    ch = channel.lower()
    skip_names = {ch, "share", "s", "joinchat", "addlist"} | {x.lower() for x in ignore}
    for href, label in links:
        href = href.strip()
        if href.lower().startswith("mailto:"):
            add(href[7:].split("?")[0])
            continue
        if href.lower().startswith("tel:"):
            add(href[4:])
            continue
        m = TME_RE.match(href)
        if m:
            if m.group(1).lower() not in skip_names:
                add("@" + m.group(1))
            continue
        if not href.startswith("https://") or re.match(r"https://t\.me/", href, re.I):
            continue
        url = clean_url(href)
        if url.lower() in skip_names:
            continue
        if APPLY_TEXT_RE.search(label) or re.search(r"vetka\.dnative\.ru|hh\.ru/vacancy", href, re.I):
            add(url)
    for m in USERNAME_RE.finditer(text):
        if m.group(1).lower() not in skip_names:
            add("@" + m.group(1))
    for m in TME_TEXT_RE.finditer(text):
        if m.group(1).lower() not in skip_names:
            add("@" + m.group(1))
    for m in EMAIL_RE.finditer(text):
        add(m.group(0))
    for m in PHONE_RE.finditer(text):
        add(re.sub(r"[^\d+]", "", m.group(0)))
    return out


def format_message(post_id: str, text: str, v: Verdict, contacts: list[str]) -> str:
    role = extract_role(text)
    desc = description(text, role)
    label = "✅ Подходит" if v.level == "ok" else "🟡 Уточнить: " + v.reason
    channel = post_id.split("/")[0]
    out = [
        f"<b>{html.escape(label)}</b>",
        f"<b>Вакансия:</b> {html.escape(role)}",
        f"<b>Описание работы:</b> {html.escape(desc or 'в посте по ссылке')}",
        f"<b>ЗП:</b> {html.escape(budget_text(v) or 'не указана')}",
        f"<b>Контакты:</b> {html.escape(', '.join(contacts) or 'в посте по ссылке')}",
        f'<a href="https://t.me/{html.escape(post_id)}">Открыть пост</a> · @{html.escape(channel)}',
    ]
    return "\n".join(out)[:4096]


ROLE_LABEL_RE = re.compile(r"(?:должность|позиция|роль)\b\s*[:—–-]?\s*(.+)", re.I)
LEAD_JUNK_RE = re.compile(r"^[^\wЁё]+")
HASHTAG_RE = re.compile(r"#[\wЁё]+")


def extract_role(text: str) -> str:
    lines = [LEAD_JUNK_RE.sub("", HASHTAG_RE.sub("", ln)).strip(" \t,;|") for ln in text.splitlines()]
    lines = [ln for ln in lines if ln and ln.lower().rstrip(":") not in ("вакансия", "вакансии")]
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


def site_lead(post_id: str, text: str, v: Verdict, now: datetime, contacts: list[str]) -> dict:
    role = extract_role(text)
    return {
        "id": "tg-" + post_id.replace("/", "-"),
        "url": f"https://t.me/{post_id}",
        "role": role,
        "platform": "Telegram-чат",
        "client": "",
        "budget": v.low,
        "budgetText": budget_text(v),
        "contacts": ", ".join(contacts),
        "summary": description(text, role, 400),
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

def fetch(url: str, attempts: int = 3) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Language": "ru"})
    for i in range(attempts):
        try:
            with urllib.request.urlopen(req, timeout=25) as r:
                if r.status != 200:
                    raise RuntimeError(f"HTTP {r.status}")
                return r.read().decode("utf-8", "replace")
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            if i == attempts - 1:
                raise
            time.sleep(3 * (i + 1))
    raise RuntimeError("unreachable")


def parse_channel(page: str) -> list[tuple[str, datetime | None, str, list[tuple[str, str]]]]:
    soup = BeautifulSoup(page, "html.parser")
    posts = []
    for node in soup.select("div.tgme_widget_message[data-post]"):
        pid = node.get("data-post", "")
        if not POST_ID_RE.match(pid) or "service_message" in (node.get("class") or []):
            continue
        text_node = node.select_one(".tgme_widget_message_text")
        if text_node is None:
            continue
        for br in text_node.find_all("br"):
            br.replace_with("\n")
        links = [(a.get("href", ""), a.get_text(" ", strip=True)) for a in text_node.find_all("a")]
        # кнопки под постом («Откликнуться» и т.п.)
        links += [(a.get("href", ""), a.get_text(" ", strip=True))
                  for a in node.select(".tgme_widget_message_inline_button, .tgme_widget_message_inline_keyboard a")
                  if a.get("href")]
        text = text_node.get_text()
        when = None
        t = node.select_one("time[datetime]")
        if t is not None:
            try:
                when = datetime.fromisoformat(t["datetime"])
            except ValueError:
                when = None
        posts.append((pid, when, text, links))
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
    tg_enabled = bool(TOKEN_RE.match(token) and CHAT_RE.match(chat))
    if not args.dry_run and not tg_enabled:
        print("Telegram не настроен (нет секретов TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID): обновляю только сайт.")

    seen = load_state()
    site = load_site_leads()
    site_ids = {x["id"] for x in site}
    now = datetime.now(timezone.utc)
    sent = skipped = added = 0
    failed = False
    for ch in channels:
        try:
            posts = parse_channel(fetch(f"https://t.me/s/{ch}"))
        except Exception as e:  # один недоступный канал не должен ронять остальные
            print(f"[{ch}] не загрузился: {e}")
            continue
        print(f"[{ch}] постов на странице: {len(posts)}")
        boiler = channel_boilerplate(posts)
        for pid, when, text, links in posts:
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
            contacts = extract_contacts(text, links, ch, boiler)
            msg = format_message(pid, text, v, contacts)
            lead = site_lead(pid, text, v, now, contacts)
            if args.dry_run:
                print(f"  ОТПРАВИЛ БЫ {pid} [{v.level}]\n{msg}\n")
                continue
            if lead["id"] in site_ids:  # уже есть на сайте (найдено вручную) — в Telegram не дублируем
                seen[pid] = now.isoformat()
                continue
            if tg_enabled:
                ok, err = tg_send(token, chat, msg)
                if not ok:
                    print(f"Telegram не принял {pid}: {err}. Остальное уйдёт при следующем запуске.")
                    failed = True
                    break
                sent += 1
                time.sleep(1.1)
            seen[pid] = now.isoformat()
            site.append(lead)
            site_ids.add(lead["id"])
            added += 1
            print(f"  + {pid} [{v.level}] {lead['role']}")
        if failed:
            break
    if not args.dry_run:
        save_state(seen, int(cfg["keep_state_days"]))
        if added:
            save_site_leads(site)
    print(f"Добавлено на сайт: {added}, отправлено в Telegram: {sent}, отсеяно: {skipped}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
