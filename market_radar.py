#!/usr/bin/env python3
"""Market Radar: free, source-linked RSS alerts to a Telegram channel.

Python 3.10+ standard library only. No paid API and no trading signals.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
import hashlib
import html
import json
import logging
import os
from pathlib import Path
import re
import sqlite3
import time
from typing import Optional
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET

BASE_DIR = Path(__file__).resolve().parent
LOGGER = logging.getLogger("market_radar")
TEHRAN = timezone(timedelta(hours=3, minutes=30))
USER_AGENT = "MarketRadarPersonal/1.0 (+RSS reader; personal Telegram notifications)"

# All RSS URLs were traced to the publishers' official feed-directory pages.
# Financial news RSS feeds include headlines, not necessarily the entire article.
FEEDS = [
    {"name": "Federal Reserve | Monetary Policy", "url": "https://www.federalreserve.gov/feeds/press_monetary.xml", "topic": "fed", "official": True},
    {"name": "Federal Reserve | Speeches", "url": "https://www.federalreserve.gov/feeds/speeches.xml", "topic": "fed_speech", "official": True},
    {"name": "BLS | CPI", "url": "https://www.bls.gov/feed/cpi.rss", "topic": "cpi", "official": True},
    {"name": "BLS | Employment", "url": "https://www.bls.gov/feed/empsit.rss", "topic": "jobs", "official": True},
    {"name": "BLS | PPI", "url": "https://www.bls.gov/feed/ppi.rss", "topic": "ppi", "official": True},
    {"name": "BLS | JOLTS", "url": "https://www.bls.gov/feed/jolts.rss", "topic": "jobs", "official": True},
    {"name": "ECB | News", "url": "https://www.ecb.europa.eu/rss/press.html", "topic": "ecb", "official": True},
    {"name": "EIA | Press Releases", "url": "https://www.eia.gov/rss/press_rss.xml", "topic": "oil", "official": True},
    {"name": "EIA | Today in Energy", "url": "https://www.eia.gov/rss/todayinenergy.xml", "topic": "oil", "official": True},
    {"name": "SEC | Press Releases", "url": "https://www.sec.gov/news/pressreleases.rss", "topic": "sec", "official": True},
    {"name": "CNBC | Top News", "url": "https://www.cnbc.com/id/100003114/device/rss/rss.html", "topic": "global", "official": False},
    {"name": "CNBC | World News", "url": "https://www.cnbc.com/id/100727362/device/rss/rss.html", "topic": "global", "official": False},
    {"name": "CNBC | Economy", "url": "https://www.cnbc.com/id/20910258/device/rss/rss.html", "topic": "global", "official": False},
    {"name": "CoinDesk", "url": "https://www.coindesk.com/arc/outboundfeeds/rss/", "topic": "crypto", "official": False},
]

# These are screening terms, not a market-direction model. A title hit gets
# more weight than a hit in the summary. The full text is never invented.
PATTERNS = {
    "gold": [
        (r"\b(?:gold|bullion|xauusd|xau|precious metals|central bank gold)\b", 6),
        (r"\b(?:safe.haven|gold reserves|gold purchases)\b", 4),
    ],
    "macro": [
        (r"\b(?:fomc|federal reserve|the fed|fed chair|powell|rate decision|interest rates?|rate cuts?|rate hikes?|monetary policy|quantitative easing|quantitative tightening)\b", 5),
        (r"\b(?:cpi|consumer price index|core inflation|inflation data|pce|personal consumption expenditures|ppi|producer price index|nonfarm payrolls?|nfp|unemployment rate|jobs report|employment situation)\b", 5),
        (r"\b(?:treasury yields?|bond yields?|u\.s\. dollar|dollar index|dxy|jolts|job openings|gdp|recession|stagflation|debt ceiling|tariffs?|trade war)\b", 3),
    ],
    "geopolitics": [
        (r"\b(?:airstrikes?|missile attacks?|military strikes?|invasion|war|ceasefire|sanctions?|nuclear deal|strait of hormuz|shipping disruption|iran|israel|russia|ukraine|middle east)\b", 3),
    ],
    "crypto": [
        (r"\b(?:bitcoin|btc|ethereum|ether|eth|crypto|cryptocurrency|stablecoin|digital assets?|spot etf|exchange.traded fund|sec approval|sec rejects?|tokenization|coinbase|binance)\b", 4),
    ],
    "oil": [
        (r"\b(?:oil prices?|crude oil|brent|wti|opec\+?|petroleum|oil inventories?|oil production|barrels? per day|energy supply|gas supplies?|oil exports?|oil imports?)\b", 4),
    ],
    "stocks": [
        (r"\b(?:s&p 500|nasdaq|dow jones|wall street|equities|stock market|stock futures|earnings|nvidia|apple|microsoft|amazon|tesla|market selloff|market rally|stock index)\b", 3),
    ],
    "forex": [
        (r"\b(?:forex|currency markets?|foreign exchange|eur/usd|usd/jpy|gbp/usd|yen|euro|bank of japan|bank of england|ecb|european central bank|dollar)\b", 3),
    ],
}

BASE_SCORE = {"fed": 7, "fed_speech": 1, "cpi": 7, "jobs": 7, "ppi": 7, "ecb": 3, "oil": 1, "sec": 1, "global": 0, "crypto": 0}
TOPIC_CATEGORY = {"fed": "macro", "fed_speech": "macro", "cpi": "macro", "jobs": "macro", "ppi": "macro", "ecb": "forex", "oil": "oil", "sec": "stocks", "crypto": "crypto"}
TOPIC_LABEL = {"gold": "🥇 طلا", "macro": "💵 اقتصاد آمریکا / نرخ بهره", "geopolitics": "🌐 ریسک ژئوپلیتیک", "crypto": "₿ رمزارز", "oil": "🛢 نفت", "stocks": "📈 بورس آمریکا", "forex": "💱 فارکس"}
TOPIC_IMPACT = {
    "gold": "مستقیماً به طلا مربوط است. جهت و دامنه واکنش قیمت نیازمند بررسی بازار است.",
    "macro": "ممکن است انتظارات نرخ بهره، بازده اوراق و دلار را تغییر دهد و بر XAUUSD اثر بگذارد.",
    "geopolitics": "ممکن است تقاضای دارایی امن و قیمت انرژی را تغییر دهد. اثر قطعی بر طلا مشخص نیست.",
    "crypto": "به بازار رمزارز مرتبط است. نتیجه خبر به‌تنهایی جهت قیمت را مشخص نمی‌کند.",
    "oil": "ممکن است انتظارات عرضه، تقاضا و قیمت نفت را تغییر دهد.",
    "stocks": "ممکن است بر ریسک‌پذیری و شاخص‌های سهام آمریکا اثر بگذارد.",
    "forex": "ممکن است بر ارزهای اصلی و انتظارات سیاست پولی اثر بگذارد.",
}


@dataclass(frozen=True)
class Article:
    title: str
    url: str
    summary: str
    published: Optional[datetime]
    source: str
    topic: str
    official: bool


@dataclass(frozen=True)
class Assessment:
    score: int
    tier: str
    category: str
    gold_relevant: bool


def load_env(path: Path) -> None:
    if not path.is_file():
        return
    for line in path.read_text(encoding="utf-8-sig").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key, value = key.strip(), value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


def http_get(url: str, timeout: int = 15) -> bytes:
    request = Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml, */*"})
    with urlopen(request, timeout=timeout) as response:
        return response.read(3_000_000)


def clean_text(s: str) -> str:
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def child_text(node: ET.Element, names: set[str]) -> str:
    for child in node:
        if child.tag.split("}")[-1].lower() in names and child.text:
            return child.text.strip()
    return ""


def parse_date(s: str) -> Optional[datetime]:
    if not s:
        return None
    try:
        dt = parsedate_to_datetime(s)
    except (TypeError, ValueError, IndexError):
        try:
            dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except ValueError:
            return None
    return dt.replace(tzinfo=timezone.utc) if dt.tzinfo is None else dt.astimezone(timezone.utc)


def parse_feed(data: bytes, feed: dict) -> list[Article]:
    root = ET.fromstring(data)
    articles = []
    for node in root.iter():
        if node.tag.split("}")[-1].lower() not in {"item", "entry"}:
            continue
        title = clean_text(child_text(node, {"title"}))
        url = child_text(node, {"link"})
        # Atom <link href="..." rel="alternate" />
        if not url:
            for link in node:
                if link.tag.split("}")[-1].lower() == "link" and link.attrib.get("rel", "alternate") == "alternate":
                    url = link.attrib.get("href", "")
                    break
        summary = clean_text(child_text(node, {"description", "summary", "content", "encoded"}))
        pub = parse_date(child_text(node, {"pubdate", "published", "updated", "date"}))
        if title and url.startswith(("https://", "http://")):
            articles.append(Article(title, url, summary[:1200], pub, feed["name"], feed["topic"], feed["official"]))
    return articles


def assess(a: Article) -> Assessment:
    hits: dict[str, int] = {}
    title = a.title.lower()
    summary = a.summary.lower()
    for topic, rules in PATTERNS.items():
        weight = 0
        for pattern, value in rules:
            if re.search(pattern, title, re.IGNORECASE):
                weight = max(weight, value)
            elif re.search(pattern, summary, re.IGNORECASE):
                weight = max(weight, max(1, value // 2))
        if weight:
            hits[topic] = weight
    score = BASE_SCORE.get(a.topic, 0) + sum(hits.values())
    if a.topic == "fed_speech" and not hits.get("macro"):
        score = min(score, 3)  # A generic speech is not necessarily market-moving.
    # Gold takes priority even when the article comes from another feed.
    order = ["gold", "macro", "geopolitics", "crypto", "oil", "stocks", "forex"]
    category = next((t for t in order if t in hits), TOPIC_CATEGORY.get(a.topic, "stocks"))
    gold_relevant = bool(hits.get("gold") or hits.get("macro") or hits.get("geopolitics") or a.topic in {"fed", "cpi", "jobs", "ppi"})
    # Tiers are relevance filters, not proof of market impact.
    tier = "فوری / اهمیت بالا" if score >= 10 else "مهم" if score >= 5 else "کم‌اهمیت"
    return Assessment(score, tier, category, gold_relevant)


def canonical_url(raw: str) -> str:
    parts = urlsplit(raw)
    query = urlencode(sorted((k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if not k.lower().startswith("utm_") and k.lower() not in {"fbclid", "gclid"}))
    return urlunsplit((parts.scheme.lower(), parts.netloc.lower(), parts.path.rstrip("/") or "/", query, ""))


def fingerprint(a: Article) -> str:
    return hashlib.sha256(canonical_url(a.url).encode("utf-8")).hexdigest()


def create_db(db_path: Path) -> sqlite3.Connection:
    db = sqlite3.connect(db_path)
    db.execute("CREATE TABLE IF NOT EXISTS seen (fingerprint TEXT PRIMARY KEY, first_seen TEXT NOT NULL, status TEXT NOT NULL)")
    db.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
    db.commit()
    return db


def get_meta(db: sqlite3.Connection, key: str) -> Optional[str]:
    row = db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return row[0] if row else None


def put_meta(db: sqlite3.Connection, key: str, value: str) -> None:
    db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)", (key, value))
    db.commit()


def is_seen(db: sqlite3.Connection, key: str) -> bool:
    return db.execute("SELECT 1 FROM seen WHERE fingerprint=?", (key,)).fetchone() is not None


def mark_seen(db: sqlite3.Connection, key: str, status: str) -> None:
    db.execute("INSERT OR IGNORE INTO seen VALUES(?,?,?)", (key, datetime.now(timezone.utc).isoformat(), status))
    db.commit()


def telegram_send(text: str, token: str, channel: str) -> None:
    from urllib.request import urlopen as post_open
    from urllib.parse import urlencode as encode
    payload = encode({"chat_id": channel, "text": text, "disable_notification": "false", "link_preview_options": json.dumps({"is_disabled": True})}).encode("utf-8")
    req = Request(f"https://api.telegram.org/bot{token}/sendMessage", data=payload, headers={"Content-Type": "application/x-www-form-urlencoded"})
    try:
        with post_open(req, timeout=20) as response:
            body = json.loads(response.read())
    except HTTPError as exc:
        msg = exc.read().decode("utf-8", errors="replace")[:250]
        raise RuntimeError(f"Telegram HTTP {exc.code}: {msg}") from exc
    if not body.get("ok"):
        raise RuntimeError(f"Telegram rejected message: {str(body)[:300]}")


def format_alert(a: Article, rating: Assessment) -> str:
    published = a.published.astimezone(TEHRAN).strftime("%Y-%m-%d %H:%M") if a.published else "نامشخص"
    source_kind = "مرجع رسمی" if a.official else "رسانه خبری"
    # Original title stays intact to prevent silent numerical translation errors.
    attention = "🥇 اولویت طلا" if rating.gold_relevant else TOPIC_LABEL[rating.category]
    title = a.title[:300]
    return (f"{'🔴' if rating.score >= 10 else '🟠'} {rating.tier}\n"
            f"{attention}\n\n"
            f"عنوان اصلی: {title}\n\n"
            f"حوزه: {TOPIC_LABEL[rating.category]}\n"
            f"چرایی اهمیت: {TOPIC_IMPACT[rating.category]}\n\n"
            f"منبع: {a.source} ({source_kind})\n"
            f"زمان انتشار: {published}، تهران\n"
            f"لینک خبر: {a.url}\n\n"
            "یادآوری: این پیام خبر و طبقه‌بندی موضوعی است، نه سیگنال خرید یا فروش.")


def fetch_articles() -> tuple[list[Article], int]:
    result = []
    good = 0
    for feed in FEEDS:
        try:
            data = http_get(feed["url"])
            found = parse_feed(data, feed)
            good += 1
            result.extend(found)
            LOGGER.info("%s: %d items", feed["name"], len(found))
        except (ET.ParseError, ValueError, OSError, URLError, TimeoutError) as exc:
            LOGGER.warning("Feed unavailable: %s [%s]", feed["name"], exc)
    return result, good


def cycle(db: sqlite3.Connection, token: str, channel: str, *, preview: bool, max_age_hours: int, min_score: int, max_per_cycle: int) -> tuple[int, int]:
    now = datetime.now(timezone.utc)
    articles, good = fetch_articles()
    if not good:
        LOGGER.error("All feeds unavailable; nothing was marked as read.")
        return 0, 0
    started_raw = get_meta(db, "started_at")
    first_run = started_raw is None
    if first_run and not preview:
        put_meta(db, "started_at", now.isoformat())
    started = datetime.fromisoformat(started_raw) if started_raw else now
    distinct = {}
    for a in articles:
        distinct[fingerprint(a)] = a
    candidates = []
    for key, a in distinct.items():
        if is_seen(db, key):
            continue
        # Avoid flooding the channel with historical items when a feed recovers.
        if a.published and (a.published < now - timedelta(hours=max_age_hours) or a.published > now + timedelta(hours=2)):
            if not preview:
                mark_seen(db, key, "stale")
            continue
        if not preview and (first_run or (a.published and a.published < started)):
            mark_seen(db, key, "baseline")
            continue
        rating = assess(a)
        if rating.score < min_score:
            if not preview:
                mark_seen(db, key, "filtered")
            continue
        candidates.append((key, a, rating))
    candidates.sort(key=lambda r: (r[2].gold_relevant, r[2].score, r[1].published or datetime.min.replace(tzinfo=timezone.utc)), reverse=True)
    sent = 0
    for key, a, rating in candidates[:max_per_cycle]:
        alert = format_alert(a, rating)
        if preview:
            print("\n" + "="*45 + "\n" + alert + "\n")
        else:
            try:
                telegram_send(alert, token, channel)
            except (RuntimeError, TimeoutError, URLError, OSError) as exc:
                LOGGER.error("Telegram send failed. Will retry later: %s", exc)
                break
            mark_seen(db, key, "sent")
            sent += 1
            time.sleep(1)
    return sent, len(candidates)


def main() -> None:
    p = argparse.ArgumentParser(description="Source-linked RSS market alerts for Telegram")
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--test", action="store_true", help="Send one Telegram connection test")
    mode.add_argument("--once", action="store_true", help="Run a single check, then exit")
    mode.add_argument("--preview", action="store_true", help="Check feeds without posting or saving anything")
    args = p.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
    load_env(BASE_DIR / ".env")
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    channel = os.getenv("TELEGRAM_CHANNEL", "").strip()
    if not args.preview and (not token or not channel):
        p.error("Add TELEGRAM_BOT_TOKEN and TELEGRAM_CHANNEL to .env")
    if args.test:
        telegram_send("✅ Market Radar متصل شد. این یک پیام آزمایشی است. هیچ معامله‌ای انجام نشده است.", token, channel)
        print("Telegram test message sent.")
        return
    interval = max(60, int(os.getenv("CHECK_INTERVAL_SECONDS", "180")))
    min_score = max(1, int(os.getenv("MIN_SCORE", "5")))
    max_age_hours = max(1, int(os.getenv("MAX_AGE_HOURS", "24")))
    max_per_cycle = max(1, int(os.getenv("MAX_ALERTS_PER_CYCLE", "6")))
    db = create_db(Path(":memory:") if args.preview else BASE_DIR / "market_radar.sqlite3")
    try:
        while True:
            sent, candidates = cycle(db, token, channel, preview=args.preview, max_age_hours=max_age_hours, min_score=min_score, max_per_cycle=max_per_cycle)
            LOGGER.info("Cycle finished: %d sent, %d candidates", sent, candidates)
            if args.once or args.preview:
                break
            time.sleep(interval)
    except KeyboardInterrupt:
        LOGGER.info("Stopped by user")
    finally:
        db.close()


if __name__ == "__main__":
    main()
