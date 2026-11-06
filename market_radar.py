"""Market Radar v2.0": relevance-filtered news + truthful quote-style price ticker.

Python 3.10+ stdlib only. Never invents bid, ask, trades, or prices.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from difflib import SequenceMatcher
from zoneinfo import ZoneInfo
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
from time import monotonic
from typing import Optional
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qsl, urlencode, quote, quote_plus, urlsplit, urlunsplit
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET

BASE_DIR = Path(__file__).resolve().parent
LOGGER = logging.getLogger("market_radar")
TEHRAN = ZoneInfo("Asia/Tehran")
NEW_YORK = ZoneInfo("America/New_York")
DIGITS_FA = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
USER_AGENT = "MarketRadarPersonal/1.0 (+RSS reader; personal Telegram notifications)"

# Mix of directly published RSS feeds and labelled Google News search feeds.
# Not all hosts grant automated access from GitHub runners. Failure is logged.
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
    # Verified public publisher feeds, added for market-relevant breaking news.
    {"name": "BBC | World", "url": "https://feeds.bbci.co.uk/news/world/rss.xml", "topic": "global", "official": False},
    {"name": "BBC | Middle East", "url": "https://feeds.bbci.co.uk/news/world/middle_east/rss.xml", "topic": "global", "official": False},
    {"name": "BBC | Business", "url": "https://feeds.bbci.co.uk/news/business/rss.xml", "topic": "global", "official": False},
    {"name": "Al Jazeera | Latest", "url": "https://www.aljazeera.com/xml/rss/all.xml", "topic": "global", "official": False},
    {"name": "CNBC | Politics", "url": "https://www.cnbc.com/id/10000113/device/rss/rss.html", "topic": "global", "official": False},
    {"name": "CNBC | Finance", "url": "https://www.cnbc.com/id/10000664/device/rss/rss.html", "topic": "global", "official": False},
    {"name": "CNBC | Asia", "url": "https://www.cnbc.com/id/19832390/device/rss/rss.html", "topic": "global", "official": False},
    {"name": "NPR | World", "url": "https://feeds.npr.org/1004/rss.xml", "topic": "global", "official": False},
    {"name": "DW | English", "url": "https://rss.dw.com/rdf/rss-en-all", "topic": "global", "official": False},
    {"name": "The Guardian | World", "url": "https://www.theguardian.com/world/rss", "topic": "global", "official": False},
    # Google News search feed is an aggregator, not an official Reuters/AP RSS feed.
    {"name": "Google News | Reuters geopolitical search", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:reuters.com (Iran OR Israel OR Hormuz OR Gulf OR sanctions OR war OR oil) when:1d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    {"name": "Google News | AP geopolitical search", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:apnews.com (Iran OR Israel OR Hormuz OR Gulf OR strikes OR sanctions) when:1d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    # Israel: breaking/liveblog feeds are useful for rapid updates, but are not
    # proof by themselves that a contested claim is accurate.
    {"name": "Times of Israel | Breaking live blog", "url": "https://www.timesofisrael.com/feed/?post_type=liveblog_entry", "topic": "global", "official": False},
    {"name": "Times of Israel | Main", "url": "https://www.timesofisrael.com/feed/", "topic": "global", "official": False},
    {"name": "Jerusalem Post | Breaking", "url": "https://www.jpost.com/rss/rssfeedsheadlines.aspx", "topic": "global", "official": False},
    {"name": "Jerusalem Post | Iran", "url": "https://www.jpost.com/rss/rssfeedsiran", "topic": "global", "official": False},
    {"name": "Jerusalem Post | Middle East", "url": "https://www.jpost.com/rss/rssfeedsmiddleeastnews.aspx", "topic": "global", "official": False},
    # Iran: retain original Persian headlines without machine translation.
    {"name": "IRNA | English", "url": "https://en.irna.ir/rss", "topic": "global", "official": False},
    {"name": "Mehr | English", "url": "https://en.mehrnews.com/rss", "topic": "global", "official": False},
    {"name": "Mehr | Persian", "url": "https://www.mehrnews.com/rss", "topic": "global", "official": False},
    {"name": "ISNA | Persian", "url": "https://www.isna.ir/rss", "topic": "global", "official": False},
    {"name": "Tasnim | Persian", "url": "https://www.tasnimnews.com/fa/rss/feed/0/8/0/" + quote("مهمترین-اخبار-تسنیم"), "topic": "global", "official": False},
    {"name": "YJC | Persian", "url": "https://www.yjc.ir/fa/rss/allnews", "topic": "global", "official": False},
    # Google News is an index of publisher reports and may update later than
    # the publisher itself. These are supplementary, not direct official feeds.
    {"name": "Reuters via Google News | Iran and Israel", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:reuters.com (Iran OR Israel OR Pentagon OR Hormuz OR missile OR airstrike) when:1d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    {"name": "AP via Google News | Iran and Israel", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:apnews.com (Iran OR Israel OR Gulf OR strikes OR missiles OR ceasefire) when:1d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    {"name": "Haaretz via Google News", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:haaretz.com (Iran OR Israel OR military OR war OR ceasefire) when:1d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    {"name": "Ynet via Google News", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:ynetnews.com (Iran OR Israel OR Gulf OR military) when:1d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    {"name": "Iranian news via Google News", "url": "https://news.google.com/rss/search?q=" + quote_plus('(site:irna.ir OR site:isna.ir OR site:mehrnews.com OR site:tasnimnews.com) (ایران OR اسرائیل OR آمریکا OR جنگ OR حمله OR تحریم) when:1d') + "&hl=fa&gl=IR&ceid=IR:fa", "topic": "global", "official": False},
    {"name": "CENTCOM official releases via Google News", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:centcom.mil (Iran OR Israel OR Gulf OR shipping OR military) when:2d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
    {"name": "IDF official statements via Google News", "url": "https://news.google.com/rss/search?q=" + quote_plus('site:idf.il (Iran OR Israel OR missile OR strike) when:2d') + "&hl=en-US&gl=US&ceid=US:en", "topic": "global", "official": False},
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
        (r"\b(?:airstrikes?|missile attacks?|military strikes?|invasion|war|ceasefire|sanctions?|nuclear deal|strait of hormuz|shipping disruption|armed conflict|military operation|troop deployment|troops? deploy(?:ed|ment)?|naval blockade|drone attacks?|explosions?|missile launch|pentagon|red sea attack|tanker seized|escalat(?:e|es|ed|ion|ing)|military action|retaliation|ultimatum|peace agreement|military threat|warship)\b", 5),
        (r"\b(?:iran|israel|russia|ukraine|middle east|persian gulf|gulf states?|hormuz|iraq|yemen|lebanon|nuclear talks?|nuclear negotiations)\b", 2),
    ],
    "crypto": [
        (r"\b(?:bitcoin|btc|ethereum|ether|eth|crypto|cryptocurrency|stablecoin|digital assets?|spot etf|exchange.traded fund|sec approval|sec rejects?|tokenization|coinbase|binance)\b", 4),
    ],
    "oil": [
        (r"\b(?:oil prices?|crude oil|brent|wti|opec\+?|petroleum|oil inventories?|oil production|barrels? per day|energy supply|gas supplies?|oil exports?|oil imports?)\b", 4),
    ],
    "stocks": [
        (r"\b(?:s&p 500|nasdaq|dow jones|wall street|equities|stock market|stock futures|earnings|nvidia|apple|microsoft|amazon|tesla|market selloff|market rally|stock index|market crash|stock plunge)\b", 4),
    ],
    "forex": [
        (r"\b(?:forex|currency markets?|foreign exchange|eur/usd|usd/jpy|gbp/usd|yen|euro|bank of japan|bank of england|ecb|european central bank|dollar index|dxy|currency crisis|dollar)\b", 4),
        (r"(?:فارکس|بازار ارز|دلار|یورو|ین ژاپن|بانک مرکزی اروپا|شاخص دلار)", 3),
    ],
}
# Persian-language publisher headlines need the same relevance screening as
# English RSS titles. Keep triggers specific to meaningful market developments.
PATTERNS["gold"].append((r"(?:طلا|اونس|انس جهانی|شمش|ذخایر طلای|قیمت جهانی طلا)", 6))
PATTERNS["macro"].extend([
    (r"(?:فدرال رزرو|نرخ بهره|بانک مرکزی آمریکا|سیاست پولی|اشتغال آمریکا|گزارش اشتغال|تورم آمریکا|شاخص قیمت مصرف کننده|شاخص قیمت تولیدکننده|افزایش نرخ بهره|کاهش نرخ بهره)", 5),
    (r"(?:تعرفه تجاری|رکود اقتصادی|بازده اوراق|انتخابات میان.?دوره.?ای آمریکا)", 3),
])
PATTERNS["geopolitics"].extend([
    (r"(?:حمله|حملات|حملۀ|بمباران|موشک|پهپاد|پدافند|شلیک|انفجار|آتش.?بس|جنگ|درگیری|تلافی|ترور|رزمایش|حمله نظامی|هشدار نظامی|تحریم|درخواست تخلیه|محاصره دریایی|ناو جنگی|اعلام وضعیت اضطراری|آماده.?باش|تنگه هرمز|بستن تنگه|بسته شدن مسیر کشتیرانی|دستور حمله|تشدید تنش)", 5),
    (r"(?:ایران|اسرائیل|آمریکا|خلیج فارس|خاورمیانه|تنگه هرمز|لبنان|عراق|یمن|سوریه|دریای سرخ)", 2),
    (r"(?:مذاکرات هسته.?ای|توافق هسته.?ای|دیدار دیپلماتیک|مذاکرات ایران و آمریکا|گفت.?وگوهای صلح)", 5),
])
PATTERNS["oil"].append((r"(?:نفت|برنت|اوپک|پالایشگاه|صادرات نفت|تولید نفت|ذخایر نفت|نفت خام)", 4))
PATTERNS["crypto"].append((r"(?:بیت.?کوین|اتریوم|رمزارز|ارز دیجیتال|استیبل کوین)", 4))
PATTERNS["stocks"].append((r"(?:بورس آمریکا|وال استریت|نزدک|داوجونز|شاخص اس.?اند.?پی|بازار سهام آمریکا)", 4))

# Headlines posing hypothetical war scenarios should not masquerade as events.
OPINION_TITLE = re.compile(r"(?:\b(?:opinion|editorial|analysis|explainer)\s*[:|]\s*|آیا جنگ (?:می.?شود|خواهد شد)|احتمال وقوع جنگ چقدر)", re.I)
# Even trusted media may relay unverified early reports. Never label as confirmed.
MILITARY_ALERT = re.compile(
    r"(?:\b(?:airstrikes?|bombardment|missiles? (?:launched|fired)|launches? (?:an? )?(?:strike|attack)|war (?:begins|starts)|explosions?|attacks? (?:iran|israel|us)|invasion)\b|"
    r"(?:شروع جنگ|آغاز جنگ|حمله(?:های)? (?:نظامی|موشکی)|حمله (?:به|علیه)|حملات به|بمباران|انفجار|شلیک موشک|اصابت موشک|ترور|هدف قرار گرفت))", re.I
)

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
    # Persian zero-width joins must not hide phrases like «شاخص قیمت مصرف‌کننده».
    title = a.title.lower().replace("\u200c", " ")
    summary = a.summary.lower().replace("\u200c", " ")
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



# Editorial quality guard: evaluate the *headline*, not a long feed summary.
# Some RSS summaries contain unrelated sidebars (for example theatre programmes
# about war) which made the previous keyword-only filter too permissive.
# This is a conservative heuristic, not independent fact-checking.
NON_MARKET_TITLE = re.compile(
    r"(?:\b(?:tv series|movie|movies|film festival|celebrity|actor|actress|"
    r"musical|theatre|theater|wedding ceremony|entertainment|sports match|"
    r"football match|soccer match|streaming series|book review|art exhibition|"
    r"gold medal|olympics)\b|"
    r"(?:نمایش(?:نامه|‌نامه)?|تئاتر|فیلم(?:‌سینمایی)?|سریال|سینما|موسیقی|"
    r"جشنواره(?:‌ی)? (?:هنری|موسیقی|فیلم)|پخش(?:‌| )?(?:نمایش|سریال|فیلم|برنامه)|"
    r"بازیگر|کنسرت|مراسم عروسی|فوتبال|مسابقه ورزشی|برنامه تلویزیونی|"
    r"رمان(?:‌| )|مدال طلا|المپیک|"
    r"کتاب(?:‌| )?(?:داستان|رمان)))",
    re.I,
)
QUESTION_OR_SPECULATION = re.compile(
    r"(?:[؟?]|^\s*(?:آیا|چرا|چگونه|چه می(?:‌| )?شود اگر|"
    r"what if|could .{0,65}\?|will .{0,65}\?|is .{0,65}\?)|"
    r"\b(?:opinion|editorial|explainer|analysis:|what to know|"
    r"could it happen|predictions? for war|hypothetical|speculation)\b|"
    r"(?:سناریوهای احتمالی|پیش(?:‌| )?بینی جنگ|بررسی احتمال جنگ|"
    r"شاید|ممکن است|احتمال دارد|احتمال می(?:‌| )?رود|"
    r"پیش(?:‌| )?بینی می(?:‌| )?شود|اگر جنگ|فرضیه جنگ|"
    r"\b(?:could|might|would|possibly|hypothetical|rumou?r|predicts?|forecasts?)\b|"
    r"\bmay (?:attack|strike|start|trigger|hit|launch|rise|fall)\b|"
    r"احتمال جنگ چقدر|تحلیل:|یادداشت:|سرمقاله:|"
    r"در آستانه فاجعه هسته(?:‌| )?ای))",
    re.I,
)
UNVERIFIED_TITLE = re.compile(
    r"(?:\b(?:unverified|unconfirmed|no evidence|viral rumor|viral rumour|"
    r"false report|hoax)\b|(?:شایعه|خبر جعلی|بی(?:‌| )?اساس|"
    r"تأیید(?:‌| )?نشده|تایید(?:‌| )?نشده))",
    re.I,
)
ROUTINE_ADMIN_TITLE = re.compile(
    r"(?:\b(?:counterfeit banknotes?|banknote statistics?|"
    r"administrative notice|staff appointment|staff vacancies?)\b|"
    r"(?:اسکناس(?:‌| )?(?:تقلبی|جعلی)|داده(?:‌| )?های بانکی تقلبی|"
    r"آمار اسکناس(?:‌| )?(?:جعلی|تقلبی)|انتصاب کارکنان بانک))",
    re.I,
)
LOCAL_NONMARKET_TITLE = re.compile(
    r"(?:^\s*(?:امام جمعه|خطیب نماز جمعه|سخنران مراسم|"
    r"سخنگوی هیئت مذهبی)\b|(?:انسجام ملی|حماسه مقاومت|"
    r"محاسبات دشمن را ناکام|پرونده .*?(?:مراسم عروسی|دادسرای)|"
    r"سالگرد (?:جنگ|دفاع)|یادواره شهدا))",
    re.I,
)
# A price-only headline is redundant because this bot already edits one
# consolidated USD/18K-gold/coin message. Market-moving causes still pass.
DOMESTIC_TICKER_TITLE = re.compile(
    r"(?:^(?:قیمت امروز|جدول قیمت|نرخ روز|آخرین قیمت)\s+(?:طلا|سکه|دلار|ارز)|"
    r"^قیمت (?:روز|لحظه(?:‌| )?ای) (?:سکه|دلار|طلای ۱۸)|"
    r"^قیمت (?:دلار|طلا و سکه|سکه|طلای ۱۸ عیار).{0,75}"
    r"(?:بازار آزاد|امروز|لحظه(?:‌| )?ای)|"
    r"^نرخ (?:جدید|امروز|لحظه(?:‌| )?ای) (?:دلار|طلا|سکه))",
    re.I,
)
MARKET_POLICY_ACTION = re.compile(
    r"(?:\b(?:rate (?:decision|cut|hike)|interest rates?|inflation|"
    r"payrolls?|unemployment|fomc|cpi|ppi|monetary|tariff|"
    r"sanctions?|oil|gold|bullion|forex|stocks?|bitcoin|bond yields?)\b|"
    r"(?:نرخ بهره|تورم|اشتغال|تحریم|نفت|طلا|سکه|دلار|"
    r"فدرال رزرو|بازار ارز|اونس|سیاست پولی|تعرفه))",
    re.I,
)
GEO_EVENT_ACTION = re.compile(
    r"(?:\b(?:airstrikes?|missile (?:attacks?|launch(?:es)?|strikes?|fire|fired)|"
    r"military (?:strike|operation|attack|deployment|exercise)|"
    r"bombardment|explosions?|invasion|ceasefire|truce|"
    r"sanctions? (?:imposed|lifted|announced|expanded)|"
    r"(?:announces?|imposes?|lifts?|expands?) (?:new )?sanctions?|"
    r"nuclear (?:deal|talks|negotiations|strike|agreement)|"
    r"peace (?:deal|agreement|talks)|troop (?:deployment|withdrawal)|"
    r"naval blockade|blockade|drones? (?:struck|attacked)|"
    r"negotiations? (?:begin|resume|end)|"
    r"tensions? (?:escalate|rise)|war (?:begins|starts|ends)|"
    r"(?:attacks?|strikes?) (?:iran|israel|us|military|bases?|tanker)|"
    r"(?:iran|israel|us) (?:attacks?|strikes?)|"
    r"declares? war|orders? (?:military )?strikes?|"
    r"security alert|hormuz (?:closed|closure|blockade|blocked))\b|"
    r"(?:حمله(?:‌| )?(?:نظامی|موشکی|پهپادی)|حمله (?:به|علیه)|"
    r"حملات به|حملات موشکی|شلیک.{0,20}موشک|"
    r"(?:موشک|پهپاد).{0,35}(?:شلیک|اصابت|رهگیری)|"
    r"انفجار|بمباران|"
    r"اصابت موشک|آتش(?:‌| )?بس|اعلام جنگ|شروع جنگ|آغاز جنگ|"
    r"تحریم(?:‌| )?های جدید|وضع تحریم|لغو تحریم|"
    r"(?:اعمال|تشدید|تمدید|رفع|تصویب).{0,25}تحریم|"
    r"تحریم.{0,25}(?:اعلام|تشدید|لغو|تصویب|وضع|اعمال)|"
    r"مذاکرات هسته(?:‌| )?ای|توافق هسته(?:‌| )?ای|"
    r"مذاکرات (?:ایران|آمریکا|صلح)|مذاکره (?:با|میان)|"
    r"اعزام (?:نیرو|ناو)|استقرار (?:نیرو|ناو)|"
    r"بستن تنگه هرمز|مسدود (?:شدن|کردن) تنگه هرمز|"
    r"تبادل آتش|درگیری (?:نظامی|مرزی)|"
    r"جنگ [^،.]{1,45} آغاز شد|جنگ [^،.]{1,45} پایان یافت|"
    r"رزمایش (?:نظامی|دریایی)|تشدید تنش|عملیات نظامی|"
    r"دستور حمله|آماده(?:‌| )?باش نظامی|حمله سایبری|"
    r"بازداشت (?:رهبر|فرمانده)|خروج از توافق))",
    re.I,
)
GEO_ANCHOR = re.compile(
    r"(?:\b(?:iran|israel|america|american|united states|u\.s\.|us |"
    r"pentagon|hormuz|middle east|persian gulf|red sea|"
    r"russia|ukraine|iraq|yemen|lebanon|tehran|"
    r"china|taiwan|venezuela|saudi arabia|gaza|syria|north korea|"
    r"israeli|iranian|nuclear facility|tanker)\b|"
    r"(?:ایران|اسرائیل|آمریکا|خلیج فارس|تنگه هرمز|"
    r"دریای سرخ|اوکراین|روسیه|لبنان|عراق|یمن|تهران|"
    r"چین|تایوان|ونزوئلا|عربستان|غزه|سوریه|کره شمالی|"
    r"پایگاه نظامی|نفتکش))",
    re.I,
)


def news_is_report_worthy(a: Article, rating: Assessment) -> tuple[bool, str]:
    """Reject off-topic/fiction/speculative headlines before publishing.

    Scores still rank *eligible* market and geopolitical events. Neither a
    high score from a long RSS summary nor an official source alone overrides
    this independent relevance and editorial filter.
    """
    title = strip_source_suffix(clean_text(a.title)).replace("\u200c", " ")
    if len(title) < 12:
        return False, "too_short"
    if NON_MARKET_TITLE.search(title):
        return False, "entertainment_or_local"
    if QUESTION_OR_SPECULATION.search(title) or OPINION_TITLE.search(title):
        return False, "question_or_opinion"
    if UNVERIFIED_TITLE.search(title):
        return False, "unverified_claim"
    if ROUTINE_ADMIN_TITLE.search(title) or LOCAL_NONMARKET_TITLE.search(title):
        return False, "routine_or_commentary"
    if DOMESTIC_TICKER_TITLE.search(title):
        return False, "redundant_price_ticker"

    # Generic soft language about a war is not news of a new event.
    market_headline = any(
        re.search(pattern, title, re.I)
        for topic in ("gold", "macro", "oil", "stocks", "crypto", "forex")
        for pattern, _ in PATTERNS[topic]
    )
    geopolitical_headline = bool(GEO_EVENT_ACTION.search(title) and GEO_ANCHOR.search(title))
    # Publish monetary release headlines from official macro sources, but do
    # not include all peripheral bank-office or regulatory notices.
    official_release = bool(a.official and a.topic in {"fed", "cpi", "jobs", "ppi"}
                            and MARKET_POLICY_ACTION.search(title))
    if not (market_headline or geopolitical_headline or official_release):
        return False, "no_concrete_market_event"
    # Headlines like "Fed chair speaks at a conference" do not announce a
    # decision even though a generic reference to Fed earns keywords.
    if a.topic == "fed_speech" and not re.search(
        r"(?:rate cuts?|rate hikes?|inflation|policy|interest rates?|"
        r"نرخ بهره|تورم|سیاست پولی)", title, re.I
    ):
        return False, "generic_speech"
    return True, "relevant"

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
    db.execute("CREATE TABLE IF NOT EXISTS sent_titles (title_hash TEXT PRIMARY KEY)")
    # Private implementation detail: auditing source provenance without showing
    # source links or publisher names in Telegram messages.
    db.execute("CREATE TABLE IF NOT EXISTS observations (fingerprint TEXT PRIMARY KEY, title TEXT, source TEXT, published_utc TEXT, first_observed_utc TEXT)")
    db.execute("CREATE TABLE IF NOT EXISTS published_stories (fingerprint TEXT PRIMARY KEY, title TEXT, source TEXT, url TEXT, published_utc TEXT, sent_utc TEXT)")
    db.commit()
    return db


def get_meta(db: sqlite3.Connection, key: str) -> Optional[str]:
    row = db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return row[0] if row else None


def put_meta(db: sqlite3.Connection, key: str, value: str) -> None:
    db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)", (key, value))
    db.commit()


def is_seen(db: sqlite3.Connection, key: str) -> bool:
    row = db.execute("SELECT status FROM seen WHERE fingerprint=?", (key,)).fetchone()
    # Re-evaluate older low-score headlines after a threshold change. Keep
    # sent and baseline/stale items excluded. No old history is erased.
    return bool(row and row[0] != "filtered")


def mark_seen(db: sqlite3.Connection, key: str, status: str) -> None:
    db.execute("INSERT OR REPLACE INTO seen VALUES(?,?,?)", (key, datetime.now(timezone.utc).isoformat(), status))
    db.commit()


SOURCE_SUFFIX = re.compile(
    r"\s+[-|]\s+(?:Reuters|AP News|Associated Press|BBC(?: News)?|CNBC|The Guardian|"
    r"CoinDesk|Times of Israel|The Times of Israel|The Jerusalem Post|Jerusalem Post|JPost|"
    r"Ynet(?:news)?|Haaretz|IRNA|ISNA|Tasnim(?: News)?|Mehr(?: News Agency)?|"
    r"خبرگزاری (?:ایرنا|ایسنا|مهر|تسنیم|فارس|باشگاه خبرنگاران جوان)|ایرنا|ایسنا|تسنیم|مهر)\s*$", re.I
)


def strip_source_suffix(title: str) -> str:
    return SOURCE_SUFFIX.sub("", title).strip()


def title_key(a: Article) -> str:
    # Avoid repeating the same headline across BBC, CNBC and aggregation feeds.
    title = strip_source_suffix(a.title.lower())
    title = re.sub(r"[^\w\s]", " ", title, flags=re.UNICODE)
    title = re.sub(r"\s+", " ", title).strip()
    return hashlib.sha256(title.encode("utf-8")).hexdigest()


def already_sent_title(db: sqlite3.Connection, a: Article) -> bool:
    return db.execute("SELECT 1 FROM sent_titles WHERE title_hash=?", (title_key(a),)).fetchone() is not None


def _normalized_title(title: str) -> str:
    # Remove trailing media attribution, compare within the same language only.
    t = clean_text(title).casefold()
    t = strip_source_suffix(t)
    t = re.sub(r"[^\w\s]", " ", t, flags=re.UNICODE)
    return re.sub(r"\s+", " ", t).strip()


def similar_headlines(left: str, right: str) -> bool:
    """Catch close rewrites while preserving numerical updates and other events."""
    query, other = _normalized_title(left), _normalized_title(right)
    if len(query) < 25 or len(other) < 25:
        return query == other
    if bool(re.search(r"[\u0600-\u06ff]", query)) != bool(re.search(r"[\u0600-\u06ff]", other)):
        return False
    if numeric_tokens(query) != numeric_tokens(other):
        return False
    qt, ot = set(query.split()), set(other.split())
    if min(len(qt), len(ot)) < 5:
        return query == other
    jaccard = len(qt & ot) / max(1, len(qt | ot))
    return jaccard >= 0.82 or SequenceMatcher(None, query, other).ratio() >= 0.91


def near_duplicate(db: sqlite3.Connection, a: Article, *, lookback_h: int = 6) -> bool:
    """Conservative within-language similarity, never a multilingual fact checker."""
    since = (datetime.now(timezone.utc) - timedelta(hours=lookback_h)).isoformat()
    recent = db.execute("SELECT title FROM published_stories WHERE sent_utc >= ? ORDER BY sent_utc DESC LIMIT 150", (since,)).fetchall()
    return any(similar_headlines(a.title, row[0]) for row in recent)


def record_observations(db: sqlite3.Connection, articles: list[Article], now: datetime) -> None:
    rows = []
    for a in articles:
        if not a.published or not (now - timedelta(hours=36) <= a.published <= now + timedelta(hours=2)):
            continue
        rating = assess(a)
        if (rating.category != "geopolitics" and not any(re.search(pattern, a.title, re.IGNORECASE) for pattern, _ in PATTERNS["geopolitics"])) or rating.score < 4:
            continue
        rows.append((fingerprint(a), a.title[:500], a.source, a.published.isoformat(), now.isoformat()))
    if rows:
        db.executemany("INSERT OR IGNORE INTO observations VALUES (?,?,?,?,?)", rows)
        db.execute("DELETE FROM observations WHERE first_observed_utc < ?", ((now - timedelta(days=14)).isoformat(),))
        db.commit()
    LOGGER.info("Geopolitics source observations processed: %d", len(rows))


def mark_sent(db: sqlite3.Connection, key: str, a: Article) -> None:
    mark_seen(db, key, "sent")
    db.execute("INSERT OR IGNORE INTO sent_titles(title_hash) VALUES (?)", (title_key(a),))
    db.execute("INSERT OR IGNORE INTO published_stories VALUES (?,?,?,?,?,?)", (key, a.title, a.source, a.url, a.published.isoformat() if a.published else "", datetime.now(timezone.utc).isoformat()))
    db.execute("DELETE FROM published_stories WHERE sent_utc < ?", ((datetime.now(timezone.utc) - timedelta(days=21)).isoformat(),))
    db.commit()


def telegram_send(text: str, token: str, channel: str) -> None:
    """Send text and optionally a red inline button for exceptional alerts.

    The *only* button target is the user's own public Telegram channel.
    On a Telegram API rejecting button styling, retry without the keyboard.
    """
    from urllib.request import urlopen as post_open
    from urllib.parse import urlencode as encode

    fields = {
        "chat_id": channel,
        "text": text,
        "disable_notification": "false",
        "link_preview_options": json.dumps({"is_disabled": True}),
    }
    footer = channel_link(channel)
    if text.startswith("🔴") and footer and os.getenv("URGENT_RED_BUTTON", "1") != "0":
        button_text = "⚠️ گزارش اولیه" if "گزارش اولیه" in text.split("\n", 1)[0] else "🚨 فوری"
        fields["reply_markup"] = json.dumps({
            "inline_keyboard": [[{"text": button_text, "url": footer, "style": "danger"}]],
        }, ensure_ascii=False)

    def post(payload: dict[str, str]) -> None:
        req = Request(
            f"https://api.telegram.org/bot{token}/sendMessage",
            data=encode(payload).encode("utf-8"),
            headers={"Content-Type": "application/x-www-form-urlencoded"},
        )
        with post_open(req, timeout=20) as response:
            body = json.loads(response.read())
        if not body.get("ok"):
            raise RuntimeError(f"Telegram rejected message: {str(body)[:300]}")

    try:
        post(fields)
        return
    except HTTPError as exc:
        # Older Telegram infrastructure/clients may not support button style.
        # A rejected HTTP 400 means no message was sent, so fallback is safe.
        if exc.code == 400 and "reply_markup" in fields:
            LOGGER.warning("Telegram did not accept the styled button; sending plain message")
            fields.pop("reply_markup")
            try:
                post(fields)
                return
            except HTTPError as fallback_exc:
                err = fallback_exc.read().decode("utf-8", errors="replace")[:250]
                raise RuntimeError(f"Telegram HTTP {fallback_exc.code}: {err}") from fallback_exc
        err = exc.read().decode("utf-8", errors="replace")[:250]
        raise RuntimeError(f"Telegram HTTP {exc.code}: {err}") from exc


def channel_link(channel: str) -> str:
    """Only the user's public Telegram channel URL is included in posts."""
    channel = channel.strip()
    if re.fullmatch(r"@[A-Za-z0-9_]{5,32}", channel):
        return "https://t.me/" + channel[1:]
    LOGGER.warning("Public channel username not recognized; footer will be omitted")
    return ""


def to_fa_digits(text: str) -> str:
    return text.translate(DIGITS_FA)


def tehran_time(dt: Optional[datetime]) -> str:
    if dt is None:
        return "زمان انتشار اعلام نشده"
    local = dt.astimezone(TEHRAN)
    return to_fa_digits(local.strftime("%Y/%m/%d ، %H:%M")) + " به وقت تهران"


def compact_headline(raw: str, max_len: int = 175) -> str:
    """Do not copy hidden links or site tags from syndication headlines."""
    title = clean_text(raw)
    title = re.sub(r"(?:https?://|www\.)\S+", "", title, flags=re.I)
    title = strip_source_suffix(title)
    title = re.sub(r"\s+", " ", title).strip(" -|\n")
    if len(title) <= max_len:
        return title
    cut = title[:max_len].rsplit(" ", 1)[0].rstrip(" ,.;:")
    return (cut or title[:max_len]) + "…"


def numeric_tokens(text: str) -> list[str]:
    normalized = text.translate(str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789"))
    return sorted(re.findall(r"\d+(?:[.,]\d+)?", normalized))


def translate_title(title: str) -> str:
    """Optional no-key translation with conservative fallback to source title.

    5,000 characters/day anonymous quota, 500-byte input limit. It is not used
    for editorial verification and never changes trading figures unnoticed.
    """
    if os.getenv("TRANSLATE_TO_FA", "1").strip().lower() in {"0", "false", "no"}:
        return title
    if re.search(r"[\u0600-\u06ff]", title):
        return title
    source = compact_headline(title, 170)
    if not source or len(source.encode("utf-8")) > 500:
        return title
    try:
        url = "https://api.mymemory.translated.net/get?" + urlencode({"q": source, "langpair": "en|fa"})
        payload = json.loads(http_get(url, timeout=5))
        translated = clean_text(payload.get("responseData", {}).get("translatedText", ""))
        translated = compact_headline(translated, 175)
        if (not translated or not re.search(r"[\u0600-\u06ff]", translated)
                or numeric_tokens(source) != numeric_tokens(translated)
                or (re.search(r"\b(?:not|never|denies|denied|denial|no evidence|false report|without)\b", source, re.I)
                    and not re.search(r"(?:نیست|نیستند|نبود|نشد|نکرد|نمی|تکذیب|رد کرد|عدم |بدون|شایعه|نادرست)", translated))
                or translated.upper().startswith("MYMEMORY WARNING")
                or "QUERY LENGTH LIMIT" in translated.upper()):
            return source
        return translated
    except (ValueError, KeyError, TypeError, URLError, OSError, TimeoutError) as exc:
        LOGGER.info("Translation unavailable; original headline retained (%s)", type(exc).__name__)
        return source


# Importance is not the same as confidence. Do not label every selected
# headline "important" merely because it passed the relevance filter.
# Only specific exceptional developments receive a visible prefix.
MAJOR_MACRO_RELEASE = re.compile(
    r"(?:\b(?:fomc|federal funds rate|interest rate decision|rate decision|"
    r"employment situation|nonfarm payrolls?|consumer price index|cpi)\b|"
    r"نرخ بهره|تصمیم فدرال رزرو|گزارش اشتغال آمریکا|شاخص قیمت مصرف.کننده)",
    re.I,
)
EXCEPTIONAL_GEOPOLITICAL_EVENT = re.compile(
    r"(?:\b(?:war (?:begins|starts)|declares? war|declaration of war|"
    r"strait of hormuz (?:has been )?(?:closed|blocked)|"
    r"hormuz (?:closure|blockade)|full.scale invasion)\b|"
    r"آغاز جنگ|شروع جنگ|اعلام جنگ|بسته شدن تنگه هرمز|"
    r"مسدود شدن تنگه هرمز|حمله سراسری)",
    re.I,
)


def exceptional_prefix(a: Article, rating: Assessment) -> str:
    """Sparse labels for exceptional news, never for every ordinary report.

    For exceptional geopolitical claims without independent verification the
    prefix explicitly says that the item is a report, not a confirmed fact.
    """
    if EXCEPTIONAL_GEOPOLITICAL_EVENT.search(a.title):
        return "⚠️ گزارش اولیه"
    if a.official and a.topic in {"fed", "cpi", "jobs"} and MAJOR_MACRO_RELEASE.search(a.title):
        return "🚨 خبر مهم"
    return ""


def importance_marker(a: Article, rating: Assessment) -> str:
    """Color shows editorial priority, not independent verification or certainty.

    Only extraordinary events are red; regular high-score relevance is orange
    or yellow. Telegram doesn't allow coloring chat-bubble backgrounds.
    """
    exceptional = exceptional_prefix(a, rating)
    if exceptional == "⚠️ گزارش اولیه":
        return "🔴 ⚠️ گزارش اولیه"
    if exceptional == "🚨 خبر مهم":
        return "🔴 🚨 فوری"
    if rating.score >= 12:
        return "🟠"
    if rating.score >= 8:
        return "🟡"
    return "⚪"


def format_alert(a: Article, rating: Assessment, channel: str = "", *, translate: bool = False) -> str:
    """Compact headline with severity marker and only the user's channel URL.

    Ordinary articles intentionally omit timestamps and publisher names.
    Only dedicated economic calendar alerts have Tehran dates/times.
    """
    headline = compact_headline(a.title)
    if translate:
        headline = translate_title(headline)
    marker = importance_marker(a, rating)
    if marker.startswith("🔴"):
        body = marker + "\n\n" + headline
    else:
        body = marker + " " + headline
    footer = channel_link(channel)
    if footer:
        body += "\n\n🔗 " + footer
    return body


def fetch_articles() -> tuple[list[Article], int]:
    # Parallel fetching reduces slow-feeds blocking timely scans.
    def read_one(feed: dict) -> list[Article]:
        return parse_feed(http_get(feed["url"], timeout=12), feed)

    result: list[Article] = []
    good = 0
    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = {executor.submit(read_one, f): f for f in FEEDS}
        for future in as_completed(futures):
            feed = futures[future]
            try:
                found = future.result()
                good += 1
                result.extend(found)
                LOGGER.info("%s: %d items", feed["name"], len(found))
            except (ET.ParseError, ValueError, OSError, URLError, TimeoutError) as exc:
                LOGGER.warning("Feed unavailable: %s [%s]", feed["name"], exc)
    return result, good



# Verified release times. Dynamic BLS iCalendar is preferred over these fallback dates.
# The FOMC item is tied to the Fed's officially published Dec 2026 calendar.
BLS_ICS = "https://www.bls.gov/schedule/news_release/bls.ics"
FALLBACK_RELEASES = [
    ("NFP", "2026-11-06", "08:30"),
    ("CPI", "2026-11-10", "08:30"),
    ("PPI", "2026-11-13", "08:30"),
    ("NFP", "2026-12-04", "08:30"),
    ("CPI", "2026-12-10", "08:30"),
    ("PPI", "2026-12-15", "08:30"),
    ("NFP", "2027-01-08", "08:30"),
]
FOMC_RELEASES = [
    ("FOMC", "2026-12-09", "14:00"),
    ("نشست خبری فدرال رزرو", "2026-12-09", "14:30"),
]
EVENT_LABELS = {"NFP": "گزارش اشتغال آمریکا (NFP)", "CPI": "تورم آمریکا (CPI)",
                "PPI": "تورم تولیدکننده آمریکا (PPI)", "FOMC": "تصمیم نرخ بهره فدرال رزرو (FOMC)",
                "نشست خبری فدرال رزرو": "نشست خبری رئیس فدرال رزرو"}


def event_dt(date_str: str, hour_str: str) -> datetime:
    return datetime.strptime(date_str + " " + hour_str, "%Y-%m-%d %H:%M").replace(tzinfo=NEW_YORK).astimezone(timezone.utc)


def calendar_kind(summary: str) -> str:
    title = summary.lower()
    if "employment situation" in title or "nonfarm payroll" in title:
        return "NFP"
    if "consumer price index" in title or re.search(r"\bcpi\b", title):
        return "CPI"
    if "producer price index" in title or re.search(r"\bppi\b", title):
        return "PPI"
    return ""


def parse_bls_ics(payload: bytes) -> list[tuple[str, datetime]]:
    """Read official BLS iCalendar dates. Untimed events are skipped."""
    lines = []
    for ln in payload.decode("utf-8-sig", "replace").splitlines():
        if ln.startswith((" ", "\t")) and lines:
            lines[-1] += ln[1:]
        else:
            lines.append(ln)
    events = []
    entry = None
    for ln in lines:
        if ln == "BEGIN:VEVENT":
            entry = {}
        elif ln == "END:VEVENT" and entry is not None:
            summary = entry.get("SUMMARY", "")
            event_type = calendar_kind(summary)
            dt_entry = entry.get("DTSTART")
            if event_type and dt_entry:
                raw_key, raw_val = dt_entry
                try:
                    if re.fullmatch(r"\d{8}T\d{6}Z", raw_val):
                        d = datetime.strptime(raw_val, "%Y%m%dT%H%M%SZ").replace(tzinfo=timezone.utc)
                    elif re.fullmatch(r"\d{8}T\d{6}", raw_val):
                        tzid = re.search(r"TZID=([^;:]+)", raw_key)
                        tz = ZoneInfo(tzid.group(1)) if tzid else NEW_YORK
                        d = datetime.strptime(raw_val, "%Y%m%dT%H%M%S").replace(tzinfo=tz).astimezone(timezone.utc)
                    elif re.fullmatch(r"\d{8}T\d{4}", raw_val):
                        d = datetime.strptime(raw_val, "%Y%m%dT%H%M").replace(tzinfo=NEW_YORK).astimezone(timezone.utc)
                    else:
                        d = None  # Never guess a missing clock time.
                    if d:
                        events.append((event_type, d))
                except (ValueError, KeyError):
                    pass
            entry = None
        elif entry is not None and ":" in ln:
            k, v = ln.split(":", 1)
            entry[k.split(";", 1)[0]] = (k, v) if k.startswith("DTSTART") else v.replace("\\,", ",")
    return events


def load_calendar(db: sqlite3.Connection, now: datetime) -> list[tuple[str, datetime]]:
    """Use cached official calendar for 12h, fallback to confirmed release dates."""
    last = get_meta(db, "calendar_refreshed_at")
    cached = get_meta(db, "calendar_feed_entries")
    if last and cached:
        try:
            if now - datetime.fromisoformat(last) < timedelta(hours=12):
                entries = [(name, datetime.fromisoformat(iso)) for name, iso in json.loads(cached)]
            else:
                entries = []
        except (ValueError, TypeError, json.JSONDecodeError):
            entries = []
    else:
        entries = []
    if not entries:
        entries = []
        try:
            entries = parse_bls_ics(http_get(BLS_ICS, timeout=8))
            if entries:
                LOGGER.info("Official BLS calendar: %d timed events", len(entries))
        except (URLError, OSError, TimeoutError, ET.ParseError) as exc:
            LOGGER.warning("Official BLS calendar unavailable: %s", type(exc).__name__)
        # Only use date-specific fallback after failed or incomplete ICS input.
        mapped = {(n, d) for n, d in entries}
        for name, date_str, hour in FALLBACK_RELEASES:
            d = event_dt(date_str, hour)
            # Do not add an obsolete fallback if the official feed has moved
            # the release to another date in the same reference month.
            if not any(n == name and x.astimezone(NEW_YORK).strftime("%Y-%m") == date_str[:7]
                       for n, x in mapped):
                entries.append((name, d))
        put_meta(db, "calendar_feed_entries", json.dumps([(n, d.isoformat()) for n, d in entries]))
        put_meta(db, "calendar_refreshed_at", now.isoformat())
    entries.extend((n, event_dt(date_str, hour)) for n, date_str, hour in FOMC_RELEASES)
    return sorted(set(entries), key=lambda p: p[1])


def calendar_notices(db: sqlite3.Connection, token: str, channel: str, *, preview: bool = False) -> int:
    if os.getenv("CALENDAR_ENABLED", "1").lower() in {"0", "false", "no"}:
        return 0
    now = datetime.now(timezone.utc)
    events = load_calendar(db, now)
    count = 0
    for kind, release_time in events:
        remaining = (release_time - now).total_seconds() / 60
        if remaining <= 0 or remaining > 1440:
            continue
        # Send one 24-hour notice and one closer reminder. If the event
        # enters the last hour for the first time, send only the close notice.
        slot = "hour" if remaining <= 60 else "day"
        key = f"event:{kind}:{release_time.isoformat()}:{slot}"
        if get_meta(db, key):
            continue
        # Scheduled economic releases are the *only* regular messages that
        # contain a date and time, always converted from the event timezone.
        local = release_time.astimezone(TEHRAN)
        day = to_fa_digits(local.strftime("%Y/%m/%d"))
        hour = to_fa_digits(local.strftime("%H:%M"))
        body = (f"📊 {EVENT_LABELS.get(kind, kind)}\n\n"
                f"📅 {day} | 🕒 ساعت {hour} به وقت تهران")
        footer = channel_link(channel)
        if footer:
            body += "\n\n🔗 " + footer
        if preview:
            print("\n" + body)
            continue
        try:
            telegram_send(body, token, channel)
        except (RuntimeError, TimeoutError, URLError, OSError) as exc:
            LOGGER.warning("Calendar send failed: %s", exc)
            continue
        put_meta(db, key, now.isoformat())
        count += 1
        time.sleep(0.3)
    return count


def initial_digest(db: sqlite3.Connection, articles: list[Article], token: str,
                   channel: str, *, max_age_hours: int, min_score: int) -> int:
    """Publish up to 3 recent, clearly labelled headlines once, even if baselined.

    This is a one-time startup digest, not a breaking-news alert. Never send a
    previously sent URL, and leave all unselected headlines untouched.
    """
    if get_meta(db, "initial_digest_done"):
        return 0
    if db.execute("SELECT 1 FROM seen WHERE status = 'sent' LIMIT 1").fetchone():
        # The bot has already delivered real news, so no startup digest needed.
        put_meta(db, "initial_digest_done", "skipped: regular news already delivered")
        return 0

    now = datetime.now(timezone.utc)
    distinct = {fingerprint(a): a for a in articles}
    shortlist = []
    for key, a in distinct.items():
        if not a.published:
            continue
        if not (now - timedelta(hours=max_age_hours) <= a.published <= now + timedelta(hours=2)):
            continue
        assessment = assess(a)
        if assessment.score < min_score or not news_is_report_worthy(a, assessment)[0]:
            continue
        row = db.execute("SELECT status FROM seen WHERE fingerprint=?", (key,)).fetchone()
        if row and row[0] == "sent":
            continue
        shortlist.append((key, a, assessment))

    shortlist.sort(key=lambda entry: (
        entry[2].gold_relevant, entry[2].score,
        entry[1].published or datetime.min.replace(tzinfo=timezone.utc)
    ), reverse=True)
    sent = 0
    for key, a, assessment in shortlist[:3]:
        # A one-off digest needs a clear 'recent' label so older headlines are
        # never mistaken for breaking reports. This never repeats every cycle.
        message = "🗞 مرور خبرهای اخیر\n\n" + format_alert(a, assessment, channel, translate=True)
        try:
            telegram_send(message, token, channel)
        except (RuntimeError, TimeoutError, URLError, OSError) as exc:
            LOGGER.error("Initial digest Telegram delivery failed: %s", exc)
            break
        db.execute(
            "INSERT OR REPLACE INTO seen(fingerprint, first_seen, status) VALUES (?, ?, 'sent')",
            (key, now.isoformat()),
        )
        db.commit()
        sent += 1
        time.sleep(1)

    if sent:
        put_meta(db, "initial_digest_done", now.isoformat())
        LOGGER.info("Initial digest: %d recent headline(s) sent once", sent)
    else:
        LOGGER.info("Initial digest: no suitable recent headlines; nothing sent")
    return sent


def cycle(db: sqlite3.Connection, token: str, channel: str, *, preview: bool, max_age_hours: int, min_score: int, max_per_cycle: int) -> tuple[int, int]:
    now = datetime.now(timezone.utc)
    calendar_sent = calendar_notices(db, token, channel, preview=preview)
    articles, good = fetch_articles()
    if not good:
        LOGGER.error("All feeds unavailable; nothing was marked as read.")
        return calendar_sent, 0
    if not preview:
        record_observations(db, articles, now)
    started_raw = get_meta(db, "started_at")
    first_run = started_raw is None
    if first_run and not preview:
        put_meta(db, "started_at", now.isoformat())
    started = datetime.fromisoformat(started_raw) if started_raw else now
    distinct = {}
    for a in articles:
        distinct[fingerprint(a)] = a
    candidates = []
    stats = {"seen": 0, "stale": 0, "baseline": 0, "filtered": 0, "irrelevant": 0, "undated": 0, "duplicate": 0}
    quality_rejections: dict[str, int] = {}
    cycle_titles: set[str] = set()
    cycle_article_titles: list[str] = []
    for key, a in distinct.items():
        if is_seen(db, key):
            stats["seen"] += 1
            continue
        if not a.published and not a.official:
            stats["undated"] += 1
            continue
        # Avoid flooding the channel with historical items when a feed recovers.
        if a.published and (a.published < now - timedelta(hours=max_age_hours) or a.published > now + timedelta(hours=2)):
            stats["stale"] += 1
            if not preview:
                mark_seen(db, key, "stale")
            continue
        if not preview and (first_run or (a.published and a.published < started)):
            mark_seen(db, key, "baseline")
            stats["baseline"] += 1
            continue
        rating = assess(a)
        if OPINION_TITLE.search(a.title):
            stats["filtered"] += 1
            if not preview:
                mark_seen(db, key, "filtered")
            continue
        if rating.score < min_score:
            stats["filtered"] += 1
            if not preview:
                mark_seen(db, key, "filtered")
            continue
        worthy, reason = news_is_report_worthy(a, rating)
        if not worthy:
            stats["irrelevant"] += 1
            quality_rejections[reason] = quality_rejections.get(reason, 0) + 1
            if not preview:
                mark_seen(db, key, "irrelevant")
            continue
        tkey = title_key(a)
        if (tkey in cycle_titles or already_sent_title(db, a)
                or near_duplicate(db, a)
                or any(similar_headlines(a.title, title) for title in cycle_article_titles)):
            stats["duplicate"] += 1
            continue
        cycle_titles.add(tkey)
        cycle_article_titles.append(a.title)
        candidates.append((key, a, rating))
    LOGGER.info("Filter diagnostics: total=%d, unseen_candidates=%d, seen=%d, stale=%d, baseline=%d, below_score=%d, irrelevant=%d, undated=%d, duplicate=%d",
                len(distinct), len(candidates), stats["seen"], stats["stale"], stats["baseline"], stats["filtered"], stats["irrelevant"], stats["undated"], stats["duplicate"])
    LOGGER.info("Editorial filter reasons: %s", json.dumps(quality_rejections, ensure_ascii=False, sort_keys=True))
    candidates.sort(key=lambda r: (
        bool(MILITARY_ALERT.search(r[1].title)) and r[2].score >= 5,
        r[2].gold_relevant, r[2].score,
        r[1].published or datetime.min.replace(tzinfo=timezone.utc)
    ), reverse=True)
    day_key = "news_posts_" + now.astimezone(TEHRAN).strftime("%Y%m%d")
    # 0 means no artificial alert-count ceiling. Candidates not sent by the
    # runtime budget remain eligible in the next scheduled run.
    daily_limit = max(0, int(os.getenv("MAX_DAILY_ALERTS", "0")))
    already_today = int(get_meta(db, day_key) or 0)
    allowance = len(candidates)
    if max_per_cycle:
        allowance = min(allowance, max_per_cycle)
    if daily_limit:
        allowance = min(allowance, max(0, daily_limit - already_today))
    sent = 0
    cycle_budget = max(60, int(os.getenv("MAX_CYCLE_SECONDS", "420")))
    send_start = monotonic()
    for key, a, rating in candidates[:allowance]:
        if monotonic() - send_start >= cycle_budget:
            LOGGER.info("Runtime budget reached; %d pending headline(s) stay eligible for the next scan", allowance - sent)
            break
        alert = format_alert(a, rating, channel, translate=not preview)
        if preview:
            print("\n" + "=" * 45 + "\n" + alert + "\n")
        else:
            try:
                telegram_send(alert, token, channel)
            except (RuntimeError, TimeoutError, URLError, OSError) as exc:
                LOGGER.error("Telegram send failed. Will retry later: %s", exc)
                break
            mark_sent(db, key, a)
            sent += 1
            put_meta(db, day_key, str(already_today + sent))
            # Telegram advises not exceeding ~1 message/s in one chat.
            time.sleep(1.2)
    LOGGER.info("Publishing: %d sent this scan, %d selected, daily limit=%s, per-cycle limit=%s", sent, len(candidates), daily_limit or "none", max_per_cycle or "none")
    if not preview and sent == 0 and not candidates and allowance > 0:
        # One-time startup digest, if no real alerts have ever reached Telegram.
        sent += initial_digest(db, list(distinct.values()), token, channel,
                               max_age_hours=max_age_hours, min_score=min_score)
    return sent + calendar_sent, len(candidates)




# Price board: public no-key Iranian market data. Provider data updates at its
# own rate (~30 minutes), independently of the 5-minute GitHub check. Prices
# are NOT financial quotes or guaranteed real-time executions.
PRICE_FEED_URL = "https://raw.githubusercontent.com/iran-market/iran-market.github.io/main/data/popular.json"
PRICE_SYMBOLS = (
    ("USD_IRR_FREE", "💵 دلار آزاد"),
    ("GOLD_18K_IRR", "🥇 طلای ۱۸ عیار (هر گرم)"),
    ("COIN_EMAMI_IRR", "🪙 سکه امامی"),
    ("EUR_IRR_FREE", "💶 یورو آزاد"),
    ("USDT_IRR", "💠 تتر"),
)
CORE_PRICE_SYMBOLS = {"USD_IRR_FREE", "GOLD_18K_IRR", "COIN_EMAMI_IRR"}


def _price_record_time(record: dict) -> datetime | None:
    raw = record.get("timestamp")
    if not isinstance(raw, str) or not raw:
        return None
    try:
        dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
        return (dt.replace(tzinfo=timezone.utc) if dt.tzinfo is None else dt).astimezone(timezone.utc)
    except ValueError:
        return None


def normalize_price_feed(payload: bytes, *, now: datetime | None = None) -> dict[str, dict]:
    """Strictly validate price, currency, quote timestamp, and symbol."""
    now = now or datetime.now(timezone.utc)
    raw = json.loads(payload)
    records = raw.get("data")
    if not isinstance(records, list):
        raise ValueError("Price feed is missing data[]")
    selected = {}
    allowed = {symbol for symbol, _ in PRICE_SYMBOLS}
    for record in records:
        if not isinstance(record, dict) or record.get("symbol") not in allowed:
            continue
        if record.get("currency") != "IRT":
            continue  # No silent rial/toman conversion from an unexpected feed.
        value = record.get("price")
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            continue
        value = float(value)
        if not (0 < value < 1_000_000_000_000):
            continue
        quote_time = _price_record_time(record)
        if quote_time is None or quote_time > now + timedelta(minutes=10):
            continue
        # Reject numbers far too old even for a "last available" quote.
        if now - quote_time > timedelta(days=14):
            continue
        selected[record["symbol"]] = {"value": value, "time": quote_time, "stale": bool(record.get("stale"))}
    if not CORE_PRICE_SYMBOLS.issubset(selected):
        raise ValueError("Price feed does not have all three required rates (USD, 18K gold, Emami coin)")
    return selected


def _price_to_fa(value: float) -> str:
    return to_fa_digits(f"{value:,.0f}").replace(",", "٬")


# This public, keyless XAU/USD endpoint is independent of the Iranian market feed.
# It reports a reference spot price rather than an executable two-way quotation.
GOLD_SPOT_URL = "https://api.gold-api.com/price/XAU"


def _validated_utc_time(raw: object, now: datetime, *, max_days: int = 7) -> datetime | None:
    if not isinstance(raw, str) or not raw:
        return None
    try:
        dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            return None
        dt = dt.astimezone(timezone.utc)
    except (ValueError, TypeError):
        return None
    if not (now - timedelta(days=max_days) <= dt <= now + timedelta(minutes=10)):
        return None
    return dt


def normalize_gold_spot(payload: bytes, *, now: datetime | None = None) -> dict[str, object]:
    """Validate public gold-api.com XAU spot USD/oz, including its own quote timestamp."""
    now = now or datetime.now(timezone.utc)
    raw = json.loads(payload)
    if not isinstance(raw, dict) or raw.get("symbol") != "XAU":
        raise ValueError("Gold feed did not return XAU")
    # Gold-API documents currency=USD; older responses may omit currency.
    if raw.get("currency", "USD") != "USD":
        raise ValueError("XAU quote is not in USD")
    price = raw.get("price")
    if isinstance(price, bool) or not isinstance(price, (int, float)) or not 200 < float(price) < 20000:
        raise ValueError("Invalid gold spot quote")
    dt = _validated_utc_time(raw.get("updatedAt"), now, max_days=7)
    if dt is None:
        raise ValueError("Gold spot time missing or invalid")
    return {"value": float(price), "time": dt, "stale": False}


def normalize_extra_quotes(payload: bytes, *, now: datetime | None = None) -> dict[str, dict]:
    """Optional licensed JSON feed for real Tehran futures and melted-gold rates.

    Expected contract:
      {"currency":"IRT", "usd_futures_tehran":{"bid": ..., "ask": ...,
       "trade": ..., "timestamp":"2026-11-06T12:00:00Z"},
       "melted_gold_cash":{"price": ..., "timestamp":"..."}}
    A free-market USD reference is never re-labelled as a Tehran futures trade.
    """
    now = now or datetime.now(timezone.utc)
    raw = json.loads(payload)
    if not isinstance(raw, dict):
        raise ValueError("Extra feed is not a JSON object")
    base = raw.get("data", raw)
    if not isinstance(base, dict) or raw.get("currency", base.get("currency")) != "IRT":
        raise ValueError("Expected explicitly denominated toman values (IRT)")
    results = {}
    future = base.get("usd_futures_tehran")
    if isinstance(future, dict):
        ts = _validated_utc_time(future.get("timestamp"), now, max_days=2)
        fields = [future.get(k) for k in ("bid", "ask", "trade")]
        if ts and all(type(x) in (int, float) and 1000 < float(x) < 10000000 for x in fields):
            bid, ask, trade = [float(x) for x in fields]
            if bid <= ask:
                results["USD_FUTURES_TEHRAN"] = {
                    "bid": bid, "ask": ask, "trade": trade, "time": ts,
                    "stale": bool(future.get("stale", False))}
    melted = base.get("melted_gold_cash")
    if isinstance(melted, dict):
        ts = _validated_utc_time(melted.get("timestamp"), now, max_days=2)
        v = melted.get("price")
        if ts and type(v) in (int, float) and 1000000 < float(v) < 10000000000:
            results["MELTED_GOLD_CASH"] = {
                "value": float(v), "time": ts, "stale": bool(melted.get("stale", False))}
    return results


def _quote_age_bad(item: dict, now: datetime, max_fresh_minutes: int) -> bool:
    return bool(item.get("stale")) or (now-item["time"]).total_seconds() > 60*max_fresh_minutes


def _jalali_date(gregorian_date) -> str:
    """Convert Gregorian date to Solar Hijri for ticker quote timestamps."""
    gy, gm, gd = gregorian_date.year, gregorian_date.month, gregorian_date.day
    offsets = (0,31,59,90,120,151,181,212,243,273,304,334)
    if gy > 1600:
        jy, gy = 979, gy - 1600
    else:
        jy, gy = 0, gy - 621
    gy2 = gy + 1 if gm > 2 else gy
    days = (365*gy + (gy2+3)//4 - (gy2+99)//100 +
            (gy2+399)//400 - 80 + gd + offsets[gm-1])
    jy += 33*(days//12053)
    days %= 12053
    jy += 4*(days//1461)
    days %= 1461
    if days > 365:
        jy += (days-1)//365
        days = (days-1)%365
    if days < 186:
        jm, jd = 1 + days//31, 1 + days%31
    else:
        jm, jd = 7 + (days-186)//30, 1 + (days-186)%30
    return f"{jy:04d}/{jm:02d}/{jd:02d}"


def price_board_text(prices: dict[str, dict], channel: str, *, now: datetime | None = None,
                     max_fresh_minutes: int = 90) -> str:
    """Compact price ticker, all figures verifiable, no fabricated future bid/ask/trades."""
    now = now or datetime.now(timezone.utc)
    lines = ["📊 نرخ بازار تهران | دلار، طلا و سکه", ""]
    used_times = []
    stale_count = 0
    futures = prices.get("USD_FUTURES_TEHRAN")
    if futures:
        is_stale = _quote_age_bad(futures, now, max_fresh_minutes)
        suffix = " ⏳" if is_stale else ""
        lines += ["⛳️ دلار فردایی تهران" + suffix,
                  "🔵 خرید: " + _price_to_fa(futures['bid']) + " تومان",
                  "⭕ فروش: " + _price_to_fa(futures['ask']) + " تومان",
                  "✅ معامله: " + _price_to_fa(futures['trade']) + " تومان", ""]
        used_times.append(futures['time'])
        stale_count += int(is_stale)

    # A free-dollar mid/reference price is not an executable Tehran-futures bid or ask.
    labels = (
        ("USD_IRR_FREE", "💵 دلار آزاد"),
        ("MELTED_GOLD_CASH", "💰 آبشده نقدی"),
        ("GOLD_18K_IRR", "✨ طلای ۱۸ عیار (گرمی)"),
        ("COIN_EMAMI_IRR", "🪙 سکه امامی"),
        ("USDT_IRR", "💠 تتر [USDT]"),
        ("EUR_IRR_FREE", "💶 یورو آزاد"),
    )
    for symbol, label in labels:
        item = prices.get(symbol)
        if item is None:
            continue  # Never substitute an unrelated price for missing fields.
        is_stale = _quote_age_bad(item, now, max_fresh_minutes)
        lines.append(f"{label}: {_price_to_fa(item['value'])} تومان" + (" ⏳" if is_stale else ""))
        used_times.append(item['time'])
        stale_count += int(is_stale)

    ounce = prices.get("XAUUSD_SPOT")
    if ounce:
        stale = _quote_age_bad(ounce, now, max_fresh_minutes)
        marker = "⏳" if stale else "🌐"
        spot = to_fa_digits(f"{ounce['value']:,.2f}").replace(",", "٬")
        stamp = to_fa_digits(ounce['time'].astimezone(TEHRAN).strftime("%H:%M:%S"))
        lines += ["", f"{marker} اونس جهانی XAUUSD: {spot} دلار  [{stamp} تهران]"]
        used_times.append(ounce['time'])
        stale_count += int(stale)

    # Display time of the OLDEST quote in the board so it never looks fresher than it is.
    if used_times:
        oldest = min(used_times).astimezone(TEHRAN)
        jalali_time = _jalali_date(oldest.date()) + " " + oldest.strftime("%H:%M")
        lines.extend(["", "🕒 قدیمی‌ترین نرخ: " + to_fa_digits(jalali_time) + " تهران"])
    if stale_count:
        lines.append("⏳ بعضی نرخ‌ها قدیمی‌اند؛ آخرین قیمت ثبت‌شده نمایش داده شده.")
    footer = channel_link(channel)
    if footer:
        lines.extend(["", "🔗 " + footer])
    return "\n".join(lines)


def _telegram_price_request(method: str, token: str, values: dict[str, str]) -> dict:
    data = urlencode(values).encode("utf-8")
    req = Request(f"https://api.telegram.org/bot{token}/{method}", data=data,
                  headers={"Content-Type": "application/x-www-form-urlencoded"})
    try:
        with urlopen(req, timeout=20) as response:
            payload = json.loads(response.read())
    except HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")[:500]
        raise RuntimeError(f"Telegram {method} HTTP {exc.code}: {detail}") from exc
    if not payload.get("ok"):
        raise RuntimeError(f"Telegram {method}: {str(payload)[:450]}")
    return payload


def update_price_board(db: sqlite3.Connection, token: str, channel: str, *, preview: bool = False,
                       now: datetime | None = None) -> str:
    """One consolidated message per Tehran day, edited only on material updates.

    Provider errors leave prior post intact; the news workflow remains independent.
    """
    if os.getenv("PRICES_ENABLED", "1").strip().lower() in {"0", "false", "no"}:
        return "disabled"
    now = now or datetime.now(timezone.utc)
    try:
        # Query the public data file once. No paid API key needed.
        data = http_get(PRICE_FEED_URL, timeout=14)
        prices = normalize_price_feed(data, now=now)
    except (ValueError, json.JSONDecodeError, URLError, OSError, TimeoutError, HTTPError) as exc:
        LOGGER.warning("Price feed unavailable/invalid; leaving prior board untouched: %s", exc)
        return "unavailable"

    # Independent global spot quotation. A failure must not interrupt Iranian rates.
    if os.getenv("XAUUSD_ENABLED", "1").strip() not in {"0", "false", "no"}:
        try:
            spot = normalize_gold_spot(http_get(GOLD_SPOT_URL, timeout=8), now=now)
            prices["XAUUSD_SPOT"] = spot
        except (ValueError, json.JSONDecodeError, URLError, OSError, TimeoutError, HTTPError) as exc:
            LOGGER.warning("XAUUSD spot unavailable, preserving Iranian quotes: %s", exc)

    # Optionally attach licensed quote fields, if the owner supplies a verified URL.
    extra_url = os.getenv("MARKET_EXTRA_QUOTES_URL", "").strip()
    if extra_url:
        if not extra_url.startswith("https://"):
            LOGGER.warning("MARKET_EXTRA_QUOTES_URL must use HTTPS")
        else:
            try:
                extras = normalize_extra_quotes(http_get(extra_url, timeout=10), now=now)
                prices.update(extras)
            except (ValueError, json.JSONDecodeError, URLError, OSError, TimeoutError, HTTPError) as exc:
                LOGGER.warning("Optional Tehran futures/melted feed unavailable: %s", exc)

    max_age = max(30, int(os.getenv("PRICE_FRESH_MINUTES", "90")))
    body = price_board_text(prices, channel, now=now, max_fresh_minutes=max_age)
    if preview:
        print("\n===== PRICE BOARD PREVIEW =====\n" + body + "\n")
        return "preview"
    digest = hashlib.sha256(body.encode("utf-8")).hexdigest()
    day = now.astimezone(TEHRAN).strftime("%Y-%m-%d")
    prev_day = get_meta(db, "price_board_day")
    prev_id = get_meta(db, "price_board_message_id")
    prev_hash = get_meta(db, "price_board_hash")
    if prev_day == day and prev_id and prev_hash == digest:
        LOGGER.info("Price board unchanged; Telegram edit skipped")
        return "unchanged"

    base = {"chat_id": channel, "text": body, "link_preview_options": json.dumps({"is_disabled": True})}
    if prev_day == day and prev_id:
        try:
            _telegram_price_request("editMessageText", token, {**base, "message_id": str(int(prev_id))})
            put_meta(db, "price_board_hash", digest)
            LOGGER.info("Price board message %s edited with latest verified quotes", prev_id)
            return "edited"
        except RuntimeError as exc:
            msg = str(exc).lower()
            if "message is not modified" in msg:
                put_meta(db, "price_board_hash", digest)
                return "unchanged"
            # When a message has been manually deleted, replace it once.
            if not ("message to edit not found" in msg or "message can't be edited" in msg
                    or "message identifier is not specified" in msg):
                LOGGER.error("Price board edit failed; not creating duplicate post: %s", exc)
                return "edit_failed"

    try:
        reply = _telegram_price_request("sendMessage", token, base)
        msg_id = reply.get("result", {}).get("message_id")
        if not isinstance(msg_id, int) or msg_id < 1:
            LOGGER.error("Telegram returned no message_id; price post was sent but cannot be tracked")
            return "sent_untracked"
        put_meta(db, "price_board_message_id", str(msg_id))
        put_meta(db, "price_board_day", day)
        put_meta(db, "price_board_hash", digest)
        LOGGER.info("Price board posted in one message, id=%s", msg_id)
        return "posted"
    except (RuntimeError, URLError, OSError, TimeoutError) as exc:
        LOGGER.error("Price board send failed: %s", exc)
        return "send_failed"


def main() -> None:
    p = argparse.ArgumentParser(description="Compact RSS alerts with Tehran time for Telegram")
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--test", action="store_true", help="Send one Telegram connection test")
    mode.add_argument("--once", action="store_true", help="Run a single check, then exit")
    mode.add_argument("--preview", action="store_true", help="Check feeds without posting or saving anything")
    mode.add_argument("--prices-once", action="store_true", help="Only create/edit the consolidated price message")
    mode.add_argument("--prices-preview", action="store_true", help="Preview public prices without sending Telegram posts")
    args = p.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
    load_env(BASE_DIR / ".env")
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    channel = os.getenv("TELEGRAM_CHANNEL", "").strip()
    if not (args.preview or args.prices_preview) and (not token or not channel):
        p.error("Add TELEGRAM_BOT_TOKEN and TELEGRAM_CHANNEL to .env")
    if args.test:
        telegram_send("✅ اتصال Market Radar برقرار است." + ("\n\n🔗 " + channel_link(channel) if channel_link(channel) else ""), token, channel)
        print("Telegram test message sent.")
        return
    interval = max(60, int(os.getenv("CHECK_INTERVAL_SECONDS", "180")))
    min_score = max(1, int(os.getenv("MIN_SCORE", "4")))
    # A newsfeed restored after hours of downtime must not dump old headlines.
    # This editorial freshness cap works with the already-installed v1.8 YAML,
    # so phone users need to replace only market_radar.py.
    configured_age = max(1, int(os.getenv("MAX_AGE_HOURS", "24")))
    freshness_cap = max(1, int(os.getenv("NEWS_FRESHNESS_HOURS", "4")))
    max_age_hours = min(configured_age, freshness_cap)
    max_per_cycle = max(0, int(os.getenv("MAX_ALERTS_PER_CYCLE", "0")))
    db = create_db(Path(":memory:") if (args.preview or args.prices_preview) else BASE_DIR / "market_radar.sqlite3")
    try:
        if args.prices_once or args.prices_preview:
            status = update_price_board(db, token, channel, preview=args.prices_preview)
            LOGGER.info("Price-only update status: %s", status)
            return
        while True:
            # Rates are independent of RSS, so even when news feeds fail the
            # price bulletin gets its scheduled update.
            if not args.preview:
                status = update_price_board(db, token, channel)
                LOGGER.info("Price bulletin: %s", status)
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
