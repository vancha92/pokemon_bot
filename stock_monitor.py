#!/usr/bin/env python3
"""
Multi-store TCG stock monitor
-----------------------------
Watches five shops for products matching your keywords and notifies you via
Discord webhook and/or email the moment one is in stock (or preorderable):

  * Black Flame   (blackflamecollectibles.com, Squarespace)
  * Mythic Vault  (mythicvault.com, WooCommerce)
  * Buzzer        (buzzer.gr, WooCommerce)
  * Gamescape     (gamescape.gr, WooCommerce)
  * eFantasy      (efantasy.gr, custom platform)

Keyword matching is fuzzy:
  * case- and accent-insensitive ("pokemon" matches "Pokémon", Greek accents too)
  * abbreviations are expanded ("etb" <-> "Elite Trainer Box", "upc" <-> "Ultra Premium Collection")
  * small typos are tolerated ("phantasmel" still matches "Phantasmal")

Availability detection tries, in order: WooCommerce Store API -> product meta
tags -> schema.org JSON-LD -> stock CSS classes -> visible text (English + Greek).

Usage:
    python stock_monitor.py            # run forever (checks every CHECK_EVERY_SECONDS)
    python stock_monitor.py --once     # single check, then exit (GitHub Actions / cron)
    python stock_monitor.py --test     # send a test notification to verify your setup

Requires:
    pip install requests beautifulsoup4
"""

import argparse
import difflib
import html as html_lib
import json
import os
import re
import smtplib
import ssl
import time
import unicodedata
from datetime import datetime
from email.message import EmailMessage
from pathlib import Path
from urllib.parse import quote, unquote, urljoin, urlparse

import requests
from bs4 import BeautifulSoup

# ================================ CONFIG ================================

# --- What you get pinged for --------------------------------------------
# Each inner list is one "watch". A product alerts if ALL terms in a list
# are found in its title (fuzzy). Example: "30th Celebration Elite Trainer
# Box" triggers ["30th", "etb"] because "etb" expands to "elite trainer box".
KEYWORD_GROUPS = [
    ["30th", "etb"],
    ["30th", "elite"],
    ["upc"],
    ["ultra"],
    ["30th", "bundle"]
]

# Products whose title contains any of these are NEVER alerted.
# "ultra pro" is pre-filled because the keyword "ultra" would otherwise ping
# you for every Ultra PRO sleeve/binder/deck box. Remove it if you want those.
EXCLUDE_TERMS = [
    "ultra pro",
    "ultra clear",
    "dragon ball",
    "warhammer",
    "funko",
]

# Abbreviations the matcher expands automatically (works in both directions;
# add your own here):
ALIASES = {
    "etb": "elite trainer box",
    "upc": "ultra premium collection",
    "bb": "booster box",
}

# Typo tolerance: 0.8 forgives small misspellings; raise towards 1.0 for
# stricter matching (1.0 = exact words only).
FUZZY_THRESHOLD = 0.8

# --- The shops -----------------------------------------------------------
# type "woocommerce": tries the public Store API (JSON, includes live stock),
#                     falls back to normal HTML search, plus any "listings".
# type "search":      HTML search template ({q} = query) plus any "listings".
# type "html":        no search; crawls the "listings" pages only.
# "listings" are extra pages crawled every cycle (new arrivals, preorders,
# relevant categories). "product_needle" identifies product links; None means
# "keep any same-site link whose text matches the keywords".
STORES = [
    {
        "name": "Black Flame",
        "base": "https://www.blackflamecollectibles.com",
        "type": "html",
        "listings": ["/", "/shop/pokemon"],
        "product_needle": "/shop/p/",
        "paginate": True,          # Squarespace supports ?page=2
    },
    {
        "name": "Mythic Vault",
        "base": "https://mythicvault.com",
        "type": "woocommerce",
        "listings": [],
        "product_needle": "/product/",
    },
    {
        "name": "Buzzer",
        "base": "https://buzzer.gr",
        "type": "woocommerce",
        "listings": [
            "/product-category/nees-afixeis/",      # new arrivals / restocks
            "/product-category/proparangelies/",    # preorders
        ],
        "product_needle": "/product/",
    },
    {
        "name": "Gamescape",
        "base": "https://gamescape.gr",
        "type": "woocommerce",
        "listings": [
            "/new-products/",
            "/pre-orders/",
            "/product-category/trading-card-games/pokemon/etbs/",
            "/product-category/trading-card-games/pokemon/box-sets-more/",
        ],
        "product_needle": "/product/",
    },
    {
        "name": "eFantasy",
        "base": "https://www.efantasy.gr",
        "type": "search",
        "search": "/el/search-results?αναζήτηση={q}",
        "listings": [
            "/el/προϊόντα/νέες-αφίξεις",            # new arrivals
            "/el/προϊόντα/preorders",               # preorders
        ],
        "product_needle": None,
    },
]

# Also alert when a NEW matching product gets listed even if it's sold out
# (handy for catching listings the second they appear).
ALERT_ON_NEW_LISTING = False

LISTING_PAGES = 2            # ?page=2... for stores with "paginate": True
MAX_PAGE_CHECKS = 25         # per store per cycle, keeps things polite
CHECK_EVERY_SECONDS = 300    # 5 minutes. Please keep this >= 60.
REQUEST_DELAY = 0.8          # pause between individual requests

# ------------------------------- Discord --------------------------------
DISCORD_WEBHOOK_URL = os.getenv("DISCORD_WEBHOOK_URL", "")  # paste it here, or set as env var / GitHub secret
DISCORD_MENTION = ""         # e.g. "@everyone" if you want a hard ping

# -------------------------------- Email ---------------------------------
EMAIL_ENABLED = False
SMTP_HOST = "smtp.gmail.com"
SMTP_PORT = 465                                            # SSL
SMTP_USER = os.getenv("SMTP_USER", "you@gmail.com")        # your Gmail address (also used as sender)
SMTP_PASS = os.getenv("SMTP_PASS", "abcd efgh ijkl mnop")  # a Gmail App Password, NOT your normal password
EMAIL_TO = os.getenv("EMAIL_TO", "you@gmail.com")          # where alerts should be sent

# =========================================================================

STATE_FILE = Path(__file__).with_name("monitor_state.json")
HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; stock-notifier/2.0; personal use)"}
TIMEOUT = 25

# non-product paths ignored when a store has no product_needle
SKIP_PATHS = ("/search-results", "/product-category", "/cart", "/my-account",
              "/wishlist", "/blog", "/events", "/gift-cards", "/grading",
              "/tag/", "/page/", "/checkout", "/σύνδεση", "/καλάθι",
              "/συχνές", "/αρχική", "/συνδρομές", "/gift-cards", "/login")

# visible-text availability hints (last-resort layer; Greek is accent-stripped)
NEG_TEXT = ("sold out", "out of stock", "currently unavailable",
            "εξαντλη", "μη διαθεσιμ", "δεν ειναι διαθεσιμ")
POS_TEXT = ("add to cart", "add to basket", "προσθηκη στο καλαθι")


def log(msg: str) -> None:
    print(f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


# ---------------------------- fuzzy matching ----------------------------

def norm(text: str) -> str:
    """Lowercase + strip accents (Latin and Greek alike)."""
    text = unicodedata.normalize("NFKD", text or "")
    return "".join(c for c in text if not unicodedata.combining(c)).lower()


def _groups() -> list:
    groups = KEYWORD_GROUPS or []
    if groups and isinstance(groups[0], str):     # a flat list also works, as one group
        groups = [groups]
    return groups


def _expansions(keyword: str) -> set:
    """A keyword plus all its alias forms, e.g. 'etb' -> {'etb', 'elite trainer box'}."""
    k = norm(keyword).strip()
    forms = {k}
    if k in ALIASES:
        forms.add(norm(ALIASES[k]))
    for short, full in ALIASES.items():
        if k == norm(full):
            forms.add(norm(short))
    return forms


def _fuzzy_in(phrase: str, title_words: list) -> bool:
    """True if `phrase` appears somewhere in the title, tolerating small typos."""
    if len(phrase) < 4:          # too short to fuzzy-match safely
        return False
    kw_words = phrase.split()
    n = len(kw_words)
    for i in range(max(len(title_words) - n + 1, 0)):
        window = " ".join(title_words[i:i + n])
        if difflib.SequenceMatcher(None, phrase, window).ratio() >= FUZZY_THRESHOLD:
            return True
    return False


def _keyword_in_title(keyword: str, title_norm: str, title_words: list) -> bool:
    for form in _expansions(keyword):
        if len(form) <= 3:
            if form in title_words:               # short forms like "etb": whole word only
                return True
        elif form in title_norm or _fuzzy_in(form, title_words):
            return True
    return False


def matches(text: str) -> bool:
    t = norm(text)
    if any(norm(x) in t for x in EXCLUDE_TERMS):
        return False
    words = re.findall(r"[a-z0-9\u0370-\u03ff]+", t)
    return any(all(_keyword_in_title(k, t, words) for k in group) for group in _groups())


def search_queries() -> list:
    """One search query per keyword group, using the longest form of each term
    (so 'etb' is searched as 'elite trainer box', which store searches understand)."""
    queries = set()
    for group in _groups():
        parts = [max(_expansions(term), key=len) for term in group]
        queries.add(" ".join(parts))
    return sorted(queries)


# ------------------------------ web access ------------------------------

def get(url: str):
    r = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
    r.raise_for_status()
    return r


def harvest_links(page_html: str, base: str, needle) -> list:
    """Extract (product_url, link_text) pairs from a listing or search page."""
    soup = BeautifulSoup(page_html, "html.parser")
    host = urlparse(base).netloc.replace("www.", "")
    out = []
    for a in soup.find_all("a", href=True):
        href = urljoin(base, a["href"])
        u = urlparse(href)
        if u.scheme not in ("http", "https") or u.netloc.replace("www.", "") != host:
            continue
        path = unquote(u.path)
        if needle:
            if needle not in path:
                continue
        else:
            if path in ("", "/") or any(x in path for x in SKIP_PATHS):
                continue
        clean = href.split("?")[0].split("#")[0].rstrip("/")
        text = a.get_text(" ", strip=True)
        out.append((clean, text))
    return out


def parse_product_page(page_html: str, url: str) -> dict:
    """Title / availability / price from a product page — several fallbacks."""
    soup = BeautifulSoup(page_html, "html.parser")

    def meta(prop):
        tag = soup.find("meta", attrs={"property": prop})
        return html_lib.unescape((tag.get("content") or "").strip()) if tag else ""

    title = meta("og:title") or (soup.title.string.strip() if soup.title and soup.title.string else "")
    site = meta("og:site_name")
    if site and title:
        title = re.sub(rf"\s*[\|\-–—]\s*{re.escape(site)}.*$", "", title, flags=re.I).strip()
    title = title or url
    price = meta("product:sale_price:amount") or meta("product:price:amount")
    currency = meta("product:price:currency")

    available = None

    # 1) Open Graph product availability (Squarespace, Facebook plugins, ...)
    av_meta = meta("product:availability").replace(" ", "").lower()
    if av_meta:
        available = av_meta in ("instock", "available", "preorder", "presale", "limitedavailability")

    # 2) schema.org JSON-LD offers (WooCommerce, most SEO plugins)
    if available is None:
        for s in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(s.string or "")
            except (ValueError, TypeError):
                continue
            objs = data if isinstance(data, list) else [data]
            flat = []
            for o in objs:
                if isinstance(o, dict) and isinstance(o.get("@graph"), list):
                    flat.extend(o["@graph"])
                else:
                    flat.append(o)
            for obj in flat:
                if not isinstance(obj, dict):
                    continue
                offers = obj.get("offers")
                offers = offers if isinstance(offers, list) else [offers] if offers else []
                for off in offers:
                    if not isinstance(off, dict):
                        continue
                    if off.get("availability"):
                        av = str(off["availability"]).lower()
                        available = not any(w in av for w in ("outofstock", "soldout", "discontinued"))
                    if not price and off.get("price"):
                        price = str(off["price"])
                        currency = currency or str(off.get("priceCurrency") or "")

    # 3) WooCommerce stock CSS classes / add-to-cart button
    if available is None:
        if re.search(r'class="[^"]*(?:\bstock\b[^"]*\bout-of-stock\b|\bout-of-stock\b[^"]*\bstock\b)', page_html):
            available = False
        elif re.search(r'class="[^"]*\bstock\b[^"]*\bin-stock\b', page_html) \
                or "single_add_to_cart_button" in page_html:
            available = True

    # 4) visible text, English + Greek (negatives first: "μη διαθέσιμο"
    #    contains "διαθέσιμο", so order matters)
    if available is None:
        text = norm(soup.get_text(" ", strip=True))
        if any(x in text for x in NEG_TEXT):
            available = False
        elif any(x in text for x in POS_TEXT):
            available = True

    return {
        "title": title,
        "available": available,          # True / False / None (unknown)
        "price": f"{price} {currency}".strip() if price else "",
    }


# -------------------------- per-store gathering --------------------------

def woo_api_products(store: dict, query: str) -> list:
    """WooCommerce public Store API: JSON with live stock, no page scraping."""
    url = store["base"].rstrip("/") + "/wp-json/wc/store/v1/products"
    r = requests.get(url, params={"search": query, "per_page": 50},
                     headers=HEADERS, timeout=TIMEOUT)
    if r.status_code != 200:
        raise RuntimeError(f"HTTP {r.status_code}")
    data = r.json()
    if not isinstance(data, list):
        raise RuntimeError("unexpected payload")
    out = []
    for p in data:
        prices = p.get("prices") or {}
        price = ""
        raw = prices.get("price")
        if raw not in (None, ""):
            try:
                minor = int(prices.get("currency_minor_unit", 2))
                price = f"{int(raw) / (10 ** minor):.2f} {prices.get('currency_code', '')}".strip()
            except (ValueError, TypeError):
                price = str(raw)
        out.append({
            "url": (p.get("permalink") or "").split("?")[0].rstrip("/"),
            "title": html_lib.unescape(p.get("name") or ""),
            "available": bool(p.get("is_in_stock")),
            "price": price,
        })
    return out


def gather_store(store: dict, queries: list) -> list:
    """Return matching products for one store: [{url,title,available,price}].
    `available` may be None -> needs no further info but is treated as not-in-stock."""
    base = store["base"].rstrip("/")
    needle = store.get("product_needle")
    results = {}          # url -> product dict (availability already known)
    pool = {}             # url -> hint text  (needs a product-page fetch)

    # a) WooCommerce Store API (best case: titles AND stock in one JSON call)
    api_ok = False
    if store["type"] == "woocommerce":
        api_ok = True
        for q in queries:
            try:
                for p in woo_api_products(store, q):
                    if p["url"] and matches(p["title"]):
                        results[p["url"]] = p
            except Exception as e:
                api_ok = False
                log(f"{store['name']}: Store API unavailable ({e}); falling back to HTML search.")
                break
            time.sleep(REQUEST_DELAY)

    # b) HTML search (WooCommerce fallback, or "search"-type stores)
    search_tpl = None
    if store["type"] == "woocommerce" and not api_ok:
        search_tpl = "/?s={q}&post_type=product"
    elif store["type"] == "search":
        search_tpl = store["search"]
    if search_tpl:
        for q in queries:
            url = base + search_tpl.replace("{q}", quote(q))
            try:
                for purl, text in harvest_links(get(url).text, base, needle):
                    if purl not in results:
                        pool[purl] = (pool.get(purl, "") + " " + text).strip()
            except Exception as e:
                log(f"{store['name']}: search failed for '{q}': {e}")
            time.sleep(REQUEST_DELAY)

    # c) fixed listing pages (new arrivals, preorders, categories, homepage)
    for listing in store.get("listings", []):
        pages = LISTING_PAGES if store.get("paginate") else 1
        for page in range(1, pages + 1):
            url = base + listing if listing.startswith("/") else listing
            if page > 1:
                url += ("&" if "?" in url else "?") + f"page={page}"
            try:
                links = harvest_links(get(url).text, base, needle)
            except Exception as e:
                log(f"{store['name']}: could not load {url}: {e}")
                break
            new = 0
            for purl, text in links:
                if purl in results:
                    continue
                if purl not in pool:
                    new += 1
                pool[purl] = (pool.get(purl, "") + " " + text).strip()
            time.sleep(REQUEST_DELAY)
            if page > 1 and new == 0:
                break

    # keep only pool entries whose link text or URL slug matches the keywords
    candidates = [u for u, hint in pool.items()
                  if matches(hint) or matches(unquote(u).rsplit("/", 1)[-1].replace("-", " "))]

    # d) fetch each remaining candidate's product page for title + stock
    for purl in sorted(candidates)[:MAX_PAGE_CHECKS]:
        time.sleep(REQUEST_DELAY)
        try:
            info = parse_product_page(get(purl).text, purl)
        except Exception as e:
            log(f"{store['name']}: could not check {purl}: {e}")
            continue
        if not matches(info["title"]):        # confirm against the real title
            continue
        if info["available"] is None:
            log(f"{store['name']}: availability unknown for {purl}")
        results[purl] = {"url": purl, **info}
    if len(candidates) > MAX_PAGE_CHECKS:
        log(f"{store['name']}: {len(candidates) - MAX_PAGE_CHECKS} candidates skipped (MAX_PAGE_CHECKS)")

    log(f"{store['name']}: {len(results)} matching product(s) this cycle.")
    return list(results.values())


# ---------------------------- notifications -----------------------------

def notify_discord(text: str) -> None:
    if not DISCORD_WEBHOOK_URL:
        return
    content = f"{DISCORD_MENTION} {text}".strip()[:1900]
    r = requests.post(DISCORD_WEBHOOK_URL, json={"content": content}, timeout=TIMEOUT)
    if r.status_code not in (200, 204):
        log(f"Discord webhook error {r.status_code}: {r.text[:200]}")


def notify_email(subject: str, body: str) -> None:
    if not EMAIL_ENABLED:
        return
    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = subject, SMTP_USER, EMAIL_TO
    msg.set_content(body)
    with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, context=ssl.create_default_context()) as s:
        s.login(SMTP_USER, SMTP_PASS)
        s.send_message(msg)


def notify(subject: str, body: str) -> None:
    log(f"ALERT -> {subject}")
    try:
        notify_discord(f"**{subject}**\n{body}")
    except Exception as e:
        log(f"Discord failed: {e}")
    try:
        notify_email(subject, body)
    except Exception as e:
        log(f"Email failed: {e}")


# ------------------------------ main logic ------------------------------

def run_check(state: dict) -> dict:
    queries = search_queries()
    for store in STORES:
        try:
            products = gather_store(store, queries)
        except Exception as e:
            log(f"{store['name']}: check failed: {e}")
            continue

        for info in products:
            url = info["url"]
            prev = state.get(url)
            was_available = bool(prev and prev.get("available"))
            now_available = bool(info["available"])

            if now_available and not was_available:
                notify(f"🔥 IN STOCK at {store['name']}: {info['title']}",
                       f"{info['price']}\nBuy it here: {url}")
            elif prev is None and ALERT_ON_NEW_LISTING and not now_available:
                notify(f"👀 New listing at {store['name']} (not in stock yet): {info['title']}",
                       f"{info['price']}\n{url}")

            state[url] = {
                "available": now_available,
                "title": info["title"],
                "store": store["name"],
                "checked": datetime.now().isoformat(timespec="seconds"),
            }

    try:
        STATE_FILE.write_text(json.dumps(state, indent=2, ensure_ascii=False))
    except OSError as e:
        log(f"Could not save state file: {e}")
    return state


def load_state() -> dict:
    try:
        return json.loads(STATE_FILE.read_text())
    except (OSError, ValueError):
        return {}


def main() -> None:
    ap = argparse.ArgumentParser(description="Multi-store TCG stock monitor")
    ap.add_argument("--once", action="store_true", help="run one check and exit (GitHub Actions / cron)")
    ap.add_argument("--test", action="store_true", help="send a test notification and exit")
    args = ap.parse_args()

    if args.test:
        shops = ", ".join(s["name"] for s in STORES)
        notify("✅ Test notification",
               f"Your stock monitor is working.\nShops: {shops}\nWatches: {KEYWORD_GROUPS}\n"
               f"Search queries used: {search_queries()}")
        log("Test notification sent — check Discord and/or your inbox.")
        return

    state = load_state()
    if args.once:
        run_check(state)
        return

    log(f"Monitoring {len(STORES)} shops every {CHECK_EVERY_SECONDS}s. Watches: {KEYWORD_GROUPS}")
    log("Note: on the very first run you'll get alerts for matching items that are ALREADY in stock.")
    while True:
        try:
            state = run_check(state)
        except Exception as e:
            log(f"Check failed (will retry): {e}")
        time.sleep(CHECK_EVERY_SECONDS)


if __name__ == "__main__":
    main()
