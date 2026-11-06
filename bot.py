"""Pokémon / Riftbound restock watcher for Romanian shops.

Runs every few minutes (GitHub Actions), checks each shop in shops.json and
sends a Telegram message when a product is NEW, BACK IN STOCK or CHEAPER.

Env vars:
  TELEGRAM_TOKEN    - bot token from @BotFather
  TELEGRAM_CHAT_ID  - your chat id (see SETUP.md)
  REPORT=1          - send a summary of what every shop returned (for testing)
  DRY_RUN=1         - print messages instead of sending them
  PROXY_URL         - http://user:pass@host:port, used only by shops with "use_proxy": true
"""

import html
import json
import os
import random
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from zoneinfo import ZoneInfo
from urllib.parse import urljoin, urlsplit, urlunsplit

import requests
from bs4 import BeautifulSoup

HERE = os.path.dirname(os.path.abspath(__file__))
SHOPS_FILE = os.path.join(HERE, "shops.json")
STATE_FILE = os.environ.get("STATE_FILE", os.path.join(HERE, "state", "state.json"))

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")
TIMEOUT = 25

KEYWORD = re.compile(r"pok[eé]\u0301?mon|\bpkm\b|\bptcg\b|riftbound|league of legends", re.I)

# What a product is. Order matters: see classify().
GRADED = re.compile(r"\b(?:psa|cgc|bgs|sgc|ace|graad|tag|gg|beckett)\b[^|]{0,14}?\b\d{1,2}(?:\.5)?\b|"
                    r"\bgraded\b[^|]{0,14}?\b\d{1,2}(?:\.5)?\b", re.I)
ACCESSORY = re.compile(r"^up - |alcove|suport de joac|sleeve|top ?loader|binder|\balbum|portofoliu|portofolio|portfolio|playmat|deck ?box|"
                       r"card ?case|acrylic|acrilic|magnetic|protec[tț]i|one[- ]touch|card saver|"
                       r"\bdice\b|\bzaruri\b|divider|pagini|buzunare|depozitare|storage|carcas", re.I)
TCG_SEALED = re.compile(r"booster|elite trainer|\betb\b|blister|\bdecks?\b|\btins?\b|ultra[- ]premium|"
                        r"super[- ]premium|premium collection|starter|\bpack\b|\bpachet|\btcg\b|"
                        r"trading card game|build (?:and|&) battle|\bchest\b|trainer kit|pre-?rift|"
                        r"pre-?release|event kit|showdown|poster collection|figure (?:collection|box)|"
                        r"c[aă]r[tț]i de joc|cartona[sș]e|colec[tț]i[ae] de postere|holiday calendar|"
                        r"toolkit|\bvault\b|proving grounds", re.I)
MERCH = re.compile(r"rucsac|ghiozdan|backpack|\bgeant|\bbag\b|\bpenar|portofel|wallet|\bplu[sș]\b|plush|"
                   r"jucari|figurin|\bfigure|statuet|tricou|t-shirt|hanorac|hoodie|[sș]apc[aă]|\bcan[aă]\b|"
                   r"\bcani\b|\bmug\b|sticl[aă]|bottle|puzzle|lego|construx|stavebnice|\blamp|\bceas|"
                   r"\bpern[aă]|pillow|costum|pijama|[sș]osete|caiet|agend[aă]|breloc|keychain|poster|"
                   r"diecast|\bmagnet\b|benzi desenate|manga|\bcarte\b|jocuri? de societate|board game|funko|"
                   r"\bcap\b|de construit|\bpiese\b|joc interactiv|guess who|labyrinth|\bbol\b|ceramic|"
                   r"p[aă]tur[aă]|creioane|c[aă]ciul|cizme|bluz[aă]|e[sș]arf|pantaloni|cool club|lenjerie|"
                   r"prosop|halat|\d\s*(?:cm|ml)\b", re.I)
WEAK_SEALED = re.compile(r"collection|colec[tț]i[ae]|bundle|display|premium|\bbox\b|cutie|tcg", re.I)
SET_CODE = re.compile(r"\b[A-Z][A-Z0-9]{1,4} \d{2,3}\b")    # "EVS 111", "S12A 234"
SINGLE = re.compile(r"#\s?\d{1,3}\b|\b\d{1,3}/\d{2,3}\b|\([a-z0-9-]{2,8} \d{1,3}\)|"
                    r"[-|] ?(?:nm|lp|mp|hp)\b|\b(?:holo|reverse|illustration rare|full art)\b", re.I)
KIND_LABEL = {"sealed": "📦 Sealed", "single": "🃏 Single", "graded": "💎 Graded",
              "accessory": "🧰 Accessory", "unsure": "❔ Not sure what this is"}
PRICE = re.compile(r"\d[\d.,]*\s*(?:lei|ron|eur|€)(?![a-z])|(?<![a-z])(?:lei|ron|eur|€)\s*\d", re.I)
OOS = re.compile(r"stoc epuizat|epuizat|indisponibil|out of stock|sold out|"
                 r"nu (?:este|e) [iî]n stoc|vyprod[aá]no|stoc 0\b", re.I)
PRE = re.compile(r"precomand|pre-?order|pre-comand", re.I)
INSTOCK = re.compile(r"[iî]n stoc|adaug[aă] [iî]n co[sș]|add to cart|skladem|stoc limitat|"
                     r"ultimele buc", re.I)

# Prices in a product card that are NOT what you pay: left out before reading the card.
RON_AMOUNT = r"\d[\d.,]*\s*(?:lei|ron)\b"
PRICE_NOISE = re.compile(
    rf"{RON_AMOUNT}\s*(?:\(?\s*(?:f[aă]r[aă]|excl\w*|ex\.?|\+)\s*tva|/\s*(?:lun[aă]|rat[aă]))"   # "155 Lei fără TVA"
    rf"|(?:economise[sș]ti|salvezi|reducere|discount|transport|livrare|peste|minim|rate?)\b"
    rf"[^\d]{{0,25}}{RON_AMOUNT}"                                     # "economisești 20 lei"
    rf"|(?<!\S)[-−–]{RON_AMOUNT}", re.I)                              # "-20 lei"
RON_PRICE = re.compile(r"(\d[\d.,]*)\s*(?:lei|ron)\b|\b(?:lei|ron)\s*(\d[\d.,]*)", re.I)

EUR_PRICE = re.compile(r"(\d[\d.,]*)\s*(?:eur\b|€)|(?:\beur|€)\s*(\d[\d.,]*)", re.I)

STORE_ONLY = re.compile(r"disponibil [iî]n loca[tț]ii", re.I)

PRICE_DROP_MIN_PCT = 3     # smaller changes are usually rounding or currency updates
PRICE_DROP_MIN_LEI = 2
SINGLE_DROP_MIN_PCT = 10   # card prices move all the time, so singles need a bigger change
SINGLE_DROP_MIN_LEI = 20
SINGLE_MIN_PRICE = 50      # singles cheaper than this are tracked but never alerted
SUSPECT_DROP_PCT = 60      # a drop this big must show up in 2 runs (could be a misread page)
MAX_DROP_ALERTS = 5        # more drops than this from one shop arrive as one list
DROP_LIST_LINES = 20
PRICE_REPEAT_HOURS = 24    # a price bouncing up and down alerts once a day, not every bounce

READER_VERSION = 4         # bump when the shop readers change: every shop re-learns silently once
MIN_PAGE_DELAY = 1.5       # seconds between pages of one shop, on top of its own "delay"
MAX_EXTRA_PAGES = 30       # safety limit for "paged_urls"
INERTIA = {}               # site build ids, kept in the saved state
PAGE_STATS = {}            # (shop name, page) -> items found, or -1 on error
PAGES_BAD_BEFORE_WARNING = 72   # ~6 hours of failed runs for one page: short outages aren't news
DAILY_HOUR = 9             # daily health report, Romanian time
MISSES_FOR_GONE = 3        # runs an item must be missing before "reappear" counts
FAILS_BEFORE_WARNING = 72  # ~6 hours at 5-minute runs; the daily report still shows shorter ones
MAX_ALERTS_PER_SHOP = 12


# ---------------------------------------------------------------- helpers

def clean(text):
    return re.sub(r"\s+", " ", html.unescape(text or "")).strip()


LANG_PREFIX = re.compile(r"^(?:/(?:en|ro|hu|de|fr))+(?=/)", re.I)   # all of /ro/ro/... at once


def norm_url(url):
    """Stable product key: same product = same key, whatever link form the shop used
    (http/https, www, /en/ language prefix, trailing slash, query string)."""
    p = urlsplit(url)
    path = LANG_PREFIX.sub("", p.path).rstrip("/") or "/"
    return urlunsplit(("https", p.netloc.lower().replace("www.", ""), path, "", ""))


def avail_from_text(text):
    """True / False / None (unknown) + preorder flag, from visible card text."""
    pre = bool(PRE.search(text))
    if OOS.search(text):
        return False, pre
    if pre or INSTOCK.search(text):
        return True, pre
    return None, pre


def avail_from_schema(value):
    v = str(value or "").rsplit("/", 1)[-1].lower()
    if not v:
        return None, False
    if v in ("outofstock", "soldout", "discontinued"):
        return False, False
    if v in ("preorder", "presale", "backorder"):
        return True, True
    return True, False


def to_price(value):
    """Number from a shop's price: 56.69, "1.019,92", "1,199.90", "375,00", "1.200"."""
    if isinstance(value, (int, float)):
        return float(value) if value > 0 else None
    t = re.sub(r"[^\d.,]", "", str(value or "")).strip(".,")
    if not t:
        return None
    last = max(t.rfind("."), t.rfind(","))
    if last >= 0 and len(t) - last - 1 in (1, 2):      # the last separator is the decimal one
        t = re.sub(r"[.,]", "", t[:last]) + "." + t[last + 1:]
    else:
        t = re.sub(r"[.,]", "", t)
    try:
        return float(t) or None
    except ValueError:
        return None


def prices_from_text(text, pattern=RON_PRICE):
    """(current price, crossed-out price) from a product card's visible text.
    Shops print the two in either order, so the lower one is what you pay."""
    found = [to_price(a or b) for a, b in pattern.findall(PRICE_NOISE.sub(" ", text))]
    found = sorted({p for p in found if p})
    if not found:
        return None, None
    old = found[-1] if len(found) > 1 and found[0] >= found[-1] * 0.2 else None
    return found[0], old


def pause(shop):
    """A person doesn't open pages at fixed intervals, and neither should the bot."""
    time.sleep(max(shop.get("delay") or 0, MIN_PAGE_DELAY) * random.uniform(0.7, 1.6))


def classify(title, url="", hint=None):
    """sealed / single / graded / accessory / merch (dropped) / unsure (reported, and marked).
    "hint" is what the shop's page says it lists. Graded wins, since it's in the title."""
    if GRADED.search(title):
        return "graded"
    if hint:
        return hint
    path = urlsplit(url).path.lower()
    if "graded" in path:
        return "graded"
    if re.search(r"singles|raw-cards|carti-raw", path):
        return "single"
    if ACCESSORY.search(title):
        return "accessory"
    if TCG_SEALED.search(title):
        return "sealed"
    if MERCH.search(title):
        return "merch"
    if SINGLE.search(title) or SET_CODE.search(title):
        return "single"
    if re.search(r"\bpromo card\b|\bcard$", title, re.I):
        return "single"
    return "sealed" if WEAK_SEALED.search(title) else "unsure"


def hint_for(shop, url):
    """The product type a shop's page lists, from "kinds": {"part of the url": "single"}."""
    return next((k for part, k in (shop.get("kinds") or {}).items() if part in url), None)


def make_session():
    s = requests.Session()
    s.headers.update({
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Accept-Language": "ro-RO,ro;q=0.9,en-US;q=0.8,en;q=0.7",
        "Upgrade-Insecure-Requests": "1",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "none",
        "Sec-Fetch-User": "?1",
        "sec-ch-ua": '"Chromium";v="130", "Google Chrome";v="130", "Not?A_Brand";v="99"',
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": '"Windows"',
    })
    return s


def get(session, url, as_json=False):
    r = session.get(url, timeout=TIMEOUT,
                    headers={"Accept": "application/json"} if as_json else None)
    r.raise_for_status()
    return r.json() if as_json else r.text


# ---------------------------------------------------------------- readers

def read_shopify(session, shop):
    base = shop["base"].rstrip("/")
    items, errors = {}, []

    def add(p, require_keyword):
        tags = p.get("tags") or []
        tags = " ".join(tags) if isinstance(tags, list) else str(tags)
        blob = " ".join([p.get("title", ""), p.get("product_type", ""),
                         p.get("vendor", ""), tags])
        if require_keyword and not KEYWORD.search(blob):
            return
        variants = p.get("variants") or [{}]
        buyable = [v for v in variants if v.get("available")] or variants
        cheapest = min(buyable, key=lambda v: to_price(v.get("price")) or float("inf"))
        url = norm_url(f"{base}/products/{p['handle']}")
        items[url] = {
            "title": clean(p.get("title")),
            "url": f"{base}/products/{p['handle']}",
            "price": cheapest.get("price"),
            "old": cheapest.get("compare_at_price"),
            "available": any(v.get("available") for v in variants),
            "preorder": bool(PRE.search(p.get("title", "") + " " + tags)),
        }

    kw_colls = set(shop.get("filter_collections", []))
    sources = [(f"{base}/collections/{c}/products.json", c in kw_colls)
               for c in shop.get("collections", [])]
    if shop.get("scan_all"):
        sources.append((f"{base}/products.json", True))
    for src, need_kw in sources:
        before = len(items)
        failed = False
        for page in range(1, int(shop.get("max_pages", 2)) + 1):
            try:
                data = get(session, f"{src}?limit=250&page={page}", as_json=True)
            except Exception as e:  # noqa: BLE001
                errors.append(f"{src}: {e}")
                failed = page == 1
                break
            prods = data.get("products", [])
            for p in prods:
                add(p, need_kw)
            if len(prods) < 250:
                break
        PAGE_STATS[(shop["name"], src)] = -1 if failed else len(items) - before
    return items, errors, len(sources)


def read_woo(session, shop):
    base = shop["base"].rstrip("/")
    items, errors = {}, []
    per_page = int(shop.get("per_page", 100))
    for page in range(1, int(shop.get("max_pages", 2)) + 1):
        url = (f"{base}/wp-json/wc/store/v1/products?per_page={per_page}&page={page}"
               f"&orderby=date&order=desc")
        try:
            data = get(session, url, as_json=True)
        except Exception as e:  # noqa: BLE001
            errors.append(f"{url}: {e}")
            if page == 1:
                PAGE_STATS[(shop["name"], base + " (product feed)")] = -1
            break
        if page == 1:
            PAGE_STATS[(shop["name"], base + " (product feed)")] = len(data)
        for p in data:
            cats = " ".join(c.get("name", "") for c in p.get("categories", []))
            name = clean(p.get("name"))
            if not KEYWORD.search(f"{name} {cats}"):
                continue
            prices = p.get("prices") or {}
            unit = 10 ** int(prices.get("currency_minor_unit", 2))
            price = int(prices["price"]) / unit if prices.get("price") else None
            regular = int(prices["regular_price"]) / unit if prices.get("regular_price") else None
            items[norm_url(p["permalink"])] = {
                "title": name,
                "url": p["permalink"],
                "price": price,
                "old": regular,
                "available": bool(p.get("is_in_stock")),
                "preorder": bool(p.get("is_on_backorder")) or bool(PRE.search(name)),
            }
        if len(data) < per_page:
            break
    return items, errors, 1


def jsonld_products(soup, page_url):
    found = []

    def walk(node):
        if isinstance(node, list):
            for n in node:
                walk(n)
            return
        if not isinstance(node, dict):
            return
        types = node.get("@type")
        types = types if isinstance(types, list) else [types]
        if "Product" in types:
            offers = node.get("offers") or {}
            if isinstance(offers, list):
                offers = offers[0] if offers else {}
            url = node.get("url") or offers.get("url")
            if url and node.get("name"):
                a, pre = avail_from_schema(offers.get("availability"))
                found.append({
                    "title": clean(node["name"]),
                    "url": urljoin(page_url, url),
                    "price": offers.get("price") or offers.get("lowPrice"),
                    "available": a,
                    "preorder": pre or bool(PRE.search(node["name"])),
                })
        for v in node.values():
            if isinstance(v, (dict, list)):
                walk(v)

    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            walk(json.loads(tag.string or tag.get_text() or "null"))
        except (ValueError, TypeError):
            continue
    return found


def card_of(a, page_url, pattern=None):
    """Climb from a product link to its product card, stopping before the
    element that also contains other products."""
    def key(x):
        return norm_url(urljoin(page_url, x.get("href")))

    def is_product(x):
        return pattern.search(urlsplit(key(x)).path) if pattern else x.find("img")

    href = key(a)
    card = a
    for _ in range(6):
        parent = card.parent
        if parent is None or len(clean(parent.get_text(" "))) >= 400:
            break
        others = {key(x) for x in parent.find_all("a", href=True) if is_product(x)}
        others.discard(href)
        if others:
            break
        card = parent
    return card


SKU_PREFIX = re.compile(r"^[0-9a-f]{10,}\s+")


def title_of(a, card):
    name = card.select_one("a.name")           # Fyft: image names are camera file names
    if name and len(clean(name.get_text(" "))) > 5:
        return clean(name.get_text(" "))
    img = a.find("img")
    for cand in (a.get("title"), img.get("alt") if img else None):
        cand = SKU_PREFIX.sub("", clean(cand))
        if len(cand) > 5 and " " in cand:      # "boosterbox" is a file name, not a title
            return cand
    for h in card.find_all(["h2", "h3", "h4", "h5"]):
        t = clean(h.get_text(" "))
        if len(t) > 5:
            return t
    t = clean(a.get_text(" "))
    if len(t) > 5:
        return t
    t = PRICE.sub("", clean(card.get_text(" ")))
    return t[:120]


def html_products(soup, page_url, link_regex=None):
    host = urlsplit(page_url).netloc.replace("www.", "")
    out = {}
    pattern = re.compile(link_regex) if link_regex else None
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href or href.startswith(("#", "mailto:", "tel:", "javascript:")):
            continue
        full = urljoin(page_url, href)
        if host not in urlsplit(full).netloc:
            continue
        if pattern:
            if not pattern.search(urlsplit(full).path):
                continue
        elif not a.find("img") or len(clean(a.get_text(" "))) > 200:
            continue
        card = card_of(a, page_url, pattern)
        text = clean(card.get_text(" "))
        # a picture link is a product if its card has a price or a buy/stock label
        # (shops often hide the price of sold-out or pre-order items)
        av, pre = avail_from_text(text)
        if not pattern and (len(text) >= 400 or not (PRICE.search(text) or av is not None or pre)):
            continue
        key = norm_url(full)
        if key == norm_url(page_url) or key in out:
            continue
        title = title_of(a, card)
        if not title and pattern:
            title = urlsplit(full).path.rsplit("/", 1)[-1].replace("-", " ")
        price, old = prices_from_text(text)
        cur = None
        if not price:      # some shops show euros to visitors outside Romania
            price, old = prices_from_text(text, EUR_PRICE)
            cur = "€" if price else None
        out[key] = {"title": title, "url": full, "price": price, "old": old, "cur": cur,
                    "available": av, "preorder": pre, "card": text[:200]}
    return out


def read_html_page(session, shop, url, track=True, template=None):
    """Products on one page, or None if it couldn't be read. Raises nothing."""
    try:
        page = get(session, url)
    except Exception as e:  # noqa: BLE001
        code = e.response.status_code if isinstance(e, requests.HTTPError) and e.response is not None else 0
        return {"gone": code == 404, "slow_down": code in (403, 429, 503), "error": f"{url}: {e}"}
    soup = BeautifulSoup(page, "html.parser")
    found = {}
    if not shop.get("link_regex"):
        for p in jsonld_products(soup, url):
            found[norm_url(p["url"])] = p
    for k, v in html_products(soup, url, shop.get("link_regex")).items():
        if k not in found:
            found[k] = v           # shop data can leave products out: the page itself has them
            continue
        # shop data often says InStock for pre-orders, and rarely has the crossed-out price
        found[k]["preorder"] = found[k]["preorder"] or v["preorder"]
        if not found[k].get("price"):
            found[k]["price"], found[k]["cur"] = v["price"], v["cur"]
        found[k]["old"] = v["old"]
        if found[k].get("available") is None:
            found[k]["available"] = v["available"]
    everything = set(found)
    fu = shop.get("filter_urls") or []
    if fu == "all" or url in fu or template in fu:
        found = {k: v for k, v in found.items() if KEYWORD.search(v["title"] + " " + k)}
    for v in found.values():
        v["src"], v["hint"] = template or url, hint_for(shop, url)
    if not found and track:
        title = soup.title.get_text(" ", strip=True)[:60] if soup.title else ""
        print(f"    [debug] {url}: 0 products, {len(page)} bytes, title={title!r}")
    return {"found": found, "everything": everything}


def read_html(session, shop, urls=None):
    items, errors, listed = {}, [], set()
    is_fallback = urls is not None
    urls = urls or shop["urls"]
    if not is_fallback and shop.get("rotate_urls"):
        # small shops rate-limit: read the main pages every run, and the rest a few at a time
        spare, size = shop["rotate_urls"], int(shop.get("rotate_per_run", 4))
        start = int(time.time() // 300) * size % len(spare)
        urls = urls + (spare + spare)[start:start + size]
    for i, url in enumerate(urls):
        if i:
            pause(shop)
        res = read_html_page(session, shop, url)
        if "found" not in res:
            if res["gone"] and url in (shop.get("may_be_empty") or []):
                PAGE_STATS[(shop["name"], url)] = 0   # optional page that doesn't exist: fine
                continue
            errors.append(res["error"])
            PAGE_STATS[(shop["name"], url)] = -1
            if res["slow_down"]:                      # the shop said stop: leave it alone until next run
                return items, errors, len(urls)
            continue
        PAGE_STATS[(shop["name"], url)] = len(res["found"])
        items.update(res["found"])
        listed |= res["everything"]
    # Listings that span several pages: keep going until a page brings nothing new.
    for template in [] if is_fallback else shop.get("paged_urls", []):
        first = int(shop.get("paged_from", 2))
        for n in range(first, first + MAX_EXTRA_PAGES):
            pause(shop)
            url = template.replace("{n}", str(n))
            res = read_html_page(session, shop, url, track=False, template=template)
            if "found" not in res:
                if not res["gone"]:
                    errors.append(res["error"])
                if res["slow_down"]:
                    return items, errors, len(urls)
                break
            # stop when the page itself has nothing new, not when nothing passes the filter:
            # mixed lists have whole pages of other games between the Pokémon ones
            if not res["everything"] - listed:
                break
            listed |= res["everything"]
            items.update({k: v for k, v in res["found"].items() if k not in items})
    return items, errors, len(urls)


def inertia_props(session, shop, url):
    """Just the product data of a page, a fraction of the page's size (paid proxy traffic).
    The request needs the site's build id; it's kept in the saved state and refreshed on change."""
    for _ in range(2):
        info = INERTIA.get(shop["name"])
        if not info:
            tag = BeautifulSoup(get(session, url), "html.parser").find("script", attrs={"data-page": True})
            page = json.loads(tag.get_text())
            info = INERTIA[shop["name"]] = {"version": page["version"], "component": page["component"]}
        r = session.get(url, timeout=TIMEOUT, headers={
            "X-Inertia": "true", "X-Inertia-Version": str(info["version"]),
            "X-Inertia-Partial-Component": info["component"],
            "X-Inertia-Partial-Data": "products,currency",
            "X-Requested-With": "XMLHttpRequest", "Accept": "application/json"})
        if r.status_code == 409:        # the site was updated: fetch the new build id
            INERTIA.pop(shop["name"], None)
            continue
        r.raise_for_status()
        return r.json()["props"]
    raise ValueError("site build id keeps changing")


def read_inertia(session, shop):
    """Shops that send their product list as JSON (Secret Cards): exact stock and sale prices.
    The currency depends on the visitor's country, so "currency" rejects any other answer.
    "hourly_urls" are long lists where only what's new matters: their first page, once an hour."""
    base = shop["base"].rstrip("/")
    items, errors = {}, []

    def read_page(src, page):
        """Returns the list's last page number, or None if this page failed."""
        url = f"{src}{'&' if '?' in src else '?'}page={page}"
        try:
            props = inertia_props(session, shop, url)
            products = props["products"]
            currency = props.get("currency") or {}
            last = min(int(products.get("last_page") or 1), MAX_EXTRA_PAGES)
        except (requests.RequestException, ValueError, KeyError, TypeError, AttributeError) as e:
            errors.append(f"{url}: {e}")
            return None
        code = currency.get("code", "RON")
        if shop.get("currency") and code != shop["currency"]:
            errors.append(f"{url}: got prices in {code}")
            return None
        cur = None if code == "RON" else currency.get("symbol")
        for p in products.get("data", []):
            link = f"{base}/products/{p['slug']}"
            items[norm_url(link)] = {
                "title": clean(p.get("name")),
                "url": link,
                "price": p.get("current_price"),
                "old": p.get("base_price") if p.get("has_discount") else None,
                "cur": cur,
                "available": bool(p.get("is_in_stock")),
                "preorder": bool(p.get("is_preorder")),
                "src": src,
                "hint": hint_for(shop, src),
            }
        return last

    for src in shop["urls"]:
        before, page, last = len(items), 1, 1
        while page <= last:
            if page > 1:
                pause(shop)
            result = read_page(src, page)
            if result is None:
                break
            last, page = result, page + 1
        PAGE_STATS[(shop["name"], src)] = len(items) - before if len(items) > before or not errors else -1
    if datetime.now().minute < 5:
        for src in shop.get("hourly_urls", []):
            pause(shop)
            read_page(src, 1)
    return items, errors, len(shop["urls"])


READERS = {"shopify": read_shopify, "woo": read_woo, "html": read_html, "inertia": read_inertia}


def check_shop(shop):
    session = make_session()
    if shop.get("use_proxy"):
        proxy = os.environ.get("PROXY_URL", "").strip().strip('"').strip("'")
        if proxy.lower().startswith("curl -x"):
            proxy = proxy[7:].strip().split()[0].strip('"')
        if "://" not in proxy:
            proxy = "http://" + proxy   # accept the plain login:pass@host:port format too
        session.proxies.update({"http": proxy, "https": proxy})
    try:
        items, errors, n_sources = READERS[shop["type"]](session, shop)
        if not items and shop.get("fallback_urls"):
            items, errors2, n2 = read_html(session, shop, shop["fallback_urls"])
            errors = errors2 if items else errors + errors2
            n_sources += n2
    except Exception as e:  # noqa: BLE001
        return shop, {}, [str(e)], 1
    if shop.get("exclude"):
        ex = re.compile(shop["exclude"], re.I)
        items = {k: v for k, v in items.items() if not ex.search(v["title"] + " " + k)}
    for v in items.values():
        v["kind"] = classify(v["title"], v["url"], v.get("hint"))
    merch = [v["title"] for v in items.values() if v["kind"] == "merch"]
    if merch:
        print(f"    [merch left out] {shop['name']}: " + " ; ".join(t[:48] for t in merch[:40]))
    items = {k: v for k, v in items.items() if v["kind"] != "merch"}
    weak = [v["title"] for v in items.values() if v["kind"] == "sealed" and not v.get("hint")
            and not TCG_SEALED.search(v["title"])]
    if weak:
        print(f"    [sealed, by name only] {shop['name']}: " + " ; ".join(t[:48] for t in weak[:40]))
    unsure = [v["title"] for v in items.values() if v["kind"] == "unsure"]
    if unsure:
        print(f"    [unsure] {shop['name']}: " + " ; ".join(t[:48] for t in unsure[:40]))
    for v in items.values():
        v["price"] = to_price(v.get("price"))
        v["old"] = to_price(v.get("old"))
        if not v["price"] or not v["old"] or v["old"] <= v["price"]:
            v["old"] = None
    if shop.get("unknown_is_in_stock"):
        # shop only labels sold-out items; anything without the label is buyable
        for v in items.values():
            if v["available"] is None:
                v["available"] = True
    return shop, items, errors, n_sources


# ---------------------------------------------------------------- telegram

def send(text):
    token = os.environ.get("TELEGRAM_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    if os.environ.get("DRY_RUN") or not token or not chat:
        print("---- message ----\n" + text)
        return
    for attempt in range(6):
        try:
            r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage",
                              data={"chat_id": chat, "text": text[:4000],
                                    "parse_mode": "HTML",
                                    "disable_web_page_preview": "false"},
                              timeout=20)
            if r.status_code == 429:
                time.sleep(int(r.json().get("parameters", {}).get("retry_after", 3)))
                continue
            if not r.ok:
                print("Telegram error:", r.text, file=sys.stderr)
            return
        except requests.RequestException as e:
            print("Telegram error:", e, file=sys.stderr)
            time.sleep(2)


def lei(p, cur=None):
    return f"{p:.2f}".replace(".00", "") + " " + (cur or "lei")


def pct(old, new):
    return round((old - new) / old * 100)


def fmt_price(it):
    p, old = it.get("price"), it.get("old")
    if not p:
        return " · in stores only" if STORE_ONLY.search(it.get("card", "")) else " · price not shown"
    cur = it.get("cur")
    return f" · {lei(p, cur)}" + (f" (was {lei(old, cur)}, -{pct(old, p)}%)" if old else "")


def item_msg(kind, shop, it):
    label = {"new": "🆕 NEW", "restock": "🔁 BACK IN STOCK",
             "instock": "📦 NOW IN STOCK (was pre-order)"}[kind]
    pre = " (pre-order)" if it.get("preorder") else ""
    return (f"<b>{label}{pre}</b> · {html.escape(shop)}\n"
            f"{KIND_LABEL.get(it.get('kind'), '')}\n"
            f"{html.escape(it['title'])}{html.escape(fmt_price(it))}\n"
            f"{html.escape(it['url'])}")


def alerts_list_msg(shop, alerts):
    """Big drop: one message that still lists every item it can, with links."""
    head = (f"<b>📦 {len(alerts)} new or restocked</b> · {html.escape(shop)} "
            f"(big drop, or the shop changed its site)")
    lines, room = [], 3700 - len(head)
    for _, it in alerts:
        line = (f"• {KIND_LABEL.get(it.get('kind'), '')[:1]} "
                f"<a href=\"{html.escape(it['url'], quote=True)}\">{html.escape(it['title'][:60])}</a>"
                f"{html.escape(fmt_price(it))}")
        room -= len(line) + 1
        if room < 0:
            break
        lines.append(line)
    if len(alerts) > len(lines):
        lines.append(f"…and {len(alerts) - len(lines)} more")
    return "\n".join([head] + lines)


def deals_msg(shop, deals):
    """What one shop has on sale right now, biggest discounts first."""
    deals = sorted(deals, key=lambda it: pct(it["old"], it["price"]), reverse=True)
    head = f"<b>🏷 {len(deals)} on sale</b> · {html.escape(shop)}"
    lines, room = [], 3700 - len(head)
    for it in deals[:DROP_LIST_LINES]:
        cur = it.get("cur")
        line = (f"• {KIND_LABEL.get(it.get('kind'), '')[:1]} -{pct(it['old'], it['price'])}% "
                f"<a href=\"{html.escape(it['url'], quote=True)}\">{html.escape(it['title'][:60])}</a> "
                f"{lei(it['price'], cur)} (was {lei(it['old'], cur)})")
        room -= len(line) + 1
        if room < 0:
            break
        lines.append(line)
    if len(deals) > len(lines):
        lines.append(f"…and {len(deals) - len(lines)} more")
    return "\n".join([head] + lines)


def drop_msg(shop, it, before):
    return (f"<b>💸 PRICE DROP -{pct(before, it['price'])}%</b> · {html.escape(shop)}\n"
            f"{KIND_LABEL.get(it.get('kind'), '')}\n"
            f"{html.escape(it['title'])}\n"
            f"{lei(before, it.get('cur'))} → <b>{lei(it['price'], it.get('cur'))}</b>\n"
            f"{html.escape(it['url'])}")


def drops_list_msg(shop, drops):
    """Shop-wide sale: one message, biggest discounts first, within Telegram's size limit."""
    drops = sorted(drops, key=lambda d: pct(d[1], d[0]["price"]), reverse=True)
    head = f"<b>💸 {len(drops)} PRICE DROPS</b> · {html.escape(shop)}"
    lines, room = [], 3700 - len(head)
    for it, before in drops[:DROP_LIST_LINES]:
        line = (f"• {KIND_LABEL.get(it.get('kind'), '')[:1]} -{pct(before, it['price'])}% "
                f"<a href=\"{html.escape(it['url'], quote=True)}\">{html.escape(it['title'][:60])}</a> "
                f"{lei(before, it.get('cur'))} → {lei(it['price'], it.get('cur'))}")
        room -= len(line) + 1
        if room < 0:
            break
        lines.append(line)
    if len(drops) > len(lines):
        lines.append(f"…and {len(drops) - len(lines)} more")
    return "\n".join([head] + lines)


# ---------------------------------------------------------------- health

def health_text(state, shops, title):
    now = time.time()
    runs = [t for t in state.get("runs", []) if now - t < 24 * 3600]
    pages = state.get("pages", {})
    lines = [f"<b>{html.escape(title)}</b>",
             f"Checks in the last 24h: {len(runs)} (target ~288, one every 5 min)", ""]
    problems = 0
    for s in shops:
        name = s["name"]
        st = state.get("shops", {}).get(name, {})
        bad = [k.split(" | ", 1)[1] for k, r in pages.items()
               if k.startswith(name + " | ") and r.get("bad", 0) >= 3]
        if not st.get("last_ok"):
            lines.append(f"⏸ {html.escape(name)}: not checked yet")
            continue
        down = st.get("fails", 0) >= 3
        icon = "❌" if down else ("⚠️" if bad else "✅")
        problems += down or bool(bad)
        line = (f"{icon} {html.escape(name)}: {st.get('last_n', 0)} products "
                f"({st.get('last_av', 0)} in stock, {st.get('last_pr', 0)} priced)")
        if down:
            mins = int((now - st["last_ok"]) / 60)
            line += f" · not loading for {mins} min"
        elif bad:
            line += f" · {len(bad)} page(s) failing"
        lines.append(line)
    lines += ["", "All good 👍" if not problems else f"{problems} shop(s) need attention."]
    return "\n".join(lines)


def poll_commands(state):
    """Which of /status and /deals you sent to the bot since the last run."""
    token = os.environ.get("TELEGRAM_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    wanted = set()
    if not token or not chat:
        return wanted
    try:
        r = requests.get(f"https://api.telegram.org/bot{token}/getUpdates",
                         params={"offset": state.get("tg_offset", 0), "timeout": 0,
                                 "allowed_updates": json.dumps(["message"])},
                         timeout=15).json()
    except (requests.RequestException, ValueError):
        return wanted
    for u in r.get("result", []):
        state["tg_offset"] = u["update_id"] + 1
        m = u.get("message") or {}
        text = (m.get("text") or "").strip().lower().lstrip("/")
        if str(m.get("chat", {}).get("id")) != str(chat):
            continue
        if text.startswith("status"):
            wanted.add("status")
        elif text.startswith(("deals", "promo", "oferte", "reduceri")):
            wanted.add("deals")
    return wanted


# ---------------------------------------------------------------- main

def load_state():
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {"shops": {}}


def save_state(state):
    os.makedirs(os.path.dirname(STATE_FILE), exist_ok=True)
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, STATE_FILE)


def worth_alerting(it):
    return it.get("kind") != "single" or not it.get("price") or it["price"] >= SINGLE_MIN_PRICE


def check_drop(price, before, prev, rec, now, kind=None):
    """Decide on a lower price and update the saved record. Returns "alert" or None."""
    drop = before - price
    rec["pr"] = price
    rec.pop("pend", None)
    card = kind in ("single", "graded")
    if (drop < (SINGLE_DROP_MIN_LEI if card else PRICE_DROP_MIN_LEI)
            or drop / before * 100 < (SINGLE_DROP_MIN_PCT if card else PRICE_DROP_MIN_PCT)):
        return None
    if drop / before * 100 >= SUSPECT_DROP_PCT and prev.get("pend") != price:
        rec["pr"], rec["pend"] = before, price     # wait for the next run to confirm it
        return None
    if (prev.get("drop_p") and price >= prev["drop_p"]
            and now - prev.get("drop_t", 0) < PRICE_REPEAT_HOURS * 3600):
        return None                                # same offer already sent today
    rec["drop_p"], rec["drop_t"] = price, now
    return "alert"


def main():
    with open(SHOPS_FILE, encoding="utf-8") as f:
        shops = [s for s in json.load(f)["shops"] if s.get("enabled", True)]
    all_shops = list(shops)
    if not os.environ.get("PROXY_URL", "").strip():
        shops = [s for s in shops if not s.get("use_proxy")]  # no proxy saved yet
    state = load_state()
    INERTIA.clear()
    INERTIA.update(state.get("inertia", {}))
    report = bool(os.environ.get("REPORT"))
    messages, report_lines = [], []
    usable_shops = set()
    now = time.time()

    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(check_shop, shops))

    for shop, items, errors, n_sources in results:
        name = shop["name"]
        st = state["shops"].setdefault(name, {"items": {}, "fails": 0, "warned": False, "init": False})
        sig = json.dumps({"reader": READER_VERSION,
                          **{k: v for k, v in shop.items() if k not in ("note", "_help", "may_be_empty")}},
                         sort_keys=True)
        if st.get("sig") != sig:
            st["init"] = False   # shop settings changed: re-learn silently, no alert flood
            st["sig"] = sig
        complete = not errors
        usable = bool(items)

        line = f"{'✅' if usable else '❌'} {name}: {len(items)} items"
        if usable:
            n_av = sum(1 for i in items.values() if i["available"])
            n_pr = sum(1 for i in items.values() if i["price"])
            line += f" ({n_av} in stock, {n_pr} priced)"
            kinds = {}
            for i in items.values():
                kinds[i["kind"]] = kinds.get(i["kind"], 0) + 1
            line += " [" + " ".join(f"{k}:{n}" for k, n in sorted(kinds.items())) + "]"
            line += f" e.g. {next(iter(items.values()))['title'][:50]}"
        if errors:
            line += f" | errors: {len(errors)}/{n_sources}"
        report_lines.append(line)
        print(line)
        if usable and not n_pr:
            print(f"    [debug] no prices read, card text: {next(iter(items.values())).get('card', '')!r}")
        for e in errors:
            print("   ", e[:200])

        if not usable:
            st["fails"] += 1
            if st["fails"] >= FAILS_BEFORE_WARNING and not st["warned"] and st["init"]:
                messages.append(f"⚠️ <b>{html.escape(name)}</b> hasn't loaded for about 6 hours. "
                                f"The shop may be down or blocking the bot.")
                st["warned"] = True
            continue
        if st["warned"]:
            messages.append(f"✅ <b>{html.escape(name)}</b> is reachable again.")
        st["fails"], st["warned"] = 0, False
        usable_shops.add(name)
        st["last_n"] = len(items)
        st["last_av"] = sum(1 for i in items.values() if i["available"])
        st["last_pr"] = sum(1 for i in items.values() if i["price"])
        st["last_ok"] = now

        # re-key saved items with the current key rules (so a rule change never fakes "new" items)
        rekeyed = {}
        for k, rec in st["items"].items():
            nk = norm_url(k)
            old = rekeyed.get(nk)
            if old is None or rec.get("m", 0) < old.get("m", 0):
                rekeyed[nk] = rec
        st["items"] = rekeyed
        known = st["items"]
        if not st["init"]:
            for key, it in items.items():
                known[key] = {"t": it["title"][:120], "a": it["available"], "m": 0,
                              "p": bool(it.get("preorder")), "pr": it["price"]}
            st["pages_seen"] = sorted({it["src"] for it in items.values() if it.get("src")})
            st["init"] = True
            continue

        reappear = shop.get("reappear_is_restock", shop["type"] == "woo")
        alerts, drops = [], []
        pages_seen = set(st.get("pages_seen", []))
        for key, it in items.items():
            prev = known.get(key)
            n_before = len(alerts)
            if prev is None:
                # a page read for the first time isn't news: learn it, don't announce it
                first_look = it.get("src") and it["src"] not in pages_seen
                if it["available"] is not False and not first_look:
                    alerts.append(("new", it))
            elif prev.get("a") is False and it["available"] is True:
                alerts.append(("restock", it))
            elif reappear and prev.get("m", 0) >= MISSES_FOR_GONE and it["available"] is not False:
                alerts.append(("restock", it))
            elif prev.get("p") and not it.get("preorder") and it["available"] is True:
                alerts.append(("instock", it))   # pre-order is now shipping / in stock
            rec = {"t": it["title"][:120], "a": it["available"], "m": 0,
                   "p": bool(it.get("preorder")), "pr": (prev or {}).get("pr")}
            for k in ("drop_p", "drop_t"):
                if prev and k in prev:
                    rec[k] = prev[k]
            if it["price"]:
                before = rec["pr"]
                if (not before or it["price"] >= before or len(alerts) > n_before
                        or it["available"] is False):
                    rec["pr"] = it["price"]    # first price seen, a rise, or it's alerting anyway
                else:
                    if check_drop(it["price"], before, prev, rec, now, it.get("kind")) == "alert":
                        drops.append((it, before))
            known[key] = rec

        st["pages_seen"] = sorted(pages_seen | {it["src"] for it in items.values() if it.get("src")})
        alerts = [a for a in alerts if worth_alerting(a[1])]
        drops = [d for d in drops if worth_alerting(d[0])]

        if complete:
            for key, rec in known.items():
                if key not in items:
                    rec["m"] = min(rec.get("m", 0) + 1, 999)

        for kind, it in alerts:
            print(f"    alert {kind}: {it['title'][:70]}")
        if len(alerts) > MAX_ALERTS_PER_SHOP:
            messages.append(alerts_list_msg(name, alerts))
        else:
            messages.extend(item_msg(kind, name, it) for kind, it in alerts)
        for it, before in drops:
            print(f"    price drop: {it['title'][:60]} {before} -> {it['price']}")
        if len(drops) > MAX_DROP_ALERTS:
            messages.append(drops_list_msg(name, drops))
        else:
            messages.extend(drop_msg(name, it, before) for it, before in drops)

    # ------------------------------------------------ health check per page
    runs = [t for t in state.get("runs", []) if now - t < 26 * 3600]
    runs.append(now)
    state["runs"] = runs
    pages = state.setdefault("pages", {})
    for (sname, page), n in PAGE_STATS.items():
        shop = next((x for x in shops if x["name"] == sname), {})
        allowed_empty = shop.get("may_be_empty") or []
        empty_ok = allowed_empty == "all" or page in allowed_empty
        key = f"{sname} | {page}"
        rec = pages.setdefault(key, {"bad": 0, "warned": False})
        rec["n"] = n
        if n < 0 or (n == 0 and not empty_ok):
            rec["bad"] += 1
            # whole-shop outages already get their own warning above
            if (rec["bad"] >= PAGES_BAD_BEFORE_WARNING and not rec["warned"]
                    and sname in usable_shops):
                what = "keeps failing to load" if n < 0 else "keeps showing 0 products"
                messages.append(f"⚠️ <b>{html.escape(sname)}</b>: one page {what} (~6 hours).\n"
                                f"{html.escape(page)}")
                rec["warned"] = True
        else:
            if rec["warned"]:
                messages.append(f"✅ <b>{html.escape(sname)}</b>: page works again.\n{html.escape(page)}")
            rec.update(bad=0, warned=False, last_ok=now)
    current = {f"{a} | {b}" for a, b in PAGE_STATS}
    ran = {x["name"] for x in shops}
    for key in list(pages):
        if key.split(" | ", 1)[0] in ran and key not in current:
            del pages[key]

    # ------------------------------------------------ daily report + /status
    local = datetime.now(ZoneInfo("Europe/Bucharest"))
    today = local.strftime("%Y-%m-%d")
    if local.hour >= DAILY_HOUR and state.get("daily") != today:
        messages.append(health_text(state, all_shops, f"📊 Daily health check · {local:%d %b}"))
        state["daily"] = today
    commands = poll_commands(state)
    if "status" in commands:
        messages.append(health_text(state, all_shops, f"📋 Status · {local:%d %b %H:%M}"))
    if "deals" in commands or not state.get("deals_intro"):
        # sent once by itself, so promotions already running aren't missed; then on /deals
        state["deals_intro"] = True
        on_sale = [(shop["name"], [it for it in items.values()
                                   if it["old"] and it["available"] and worth_alerting(it)])
                   for shop, items, _, _ in results]
        on_sale = [(name, deals) for name, deals in on_sale if deals]
        messages.append(f"🏷 <b>Running promotions</b> in {len(on_sale)} shops. "
                        f"Send /deals any time for this list."
                        if on_sale else "🏷 No promotions found right now.")
        messages.extend(deals_msg(name, deals) for name, deals in on_sale)

    state["inertia"] = dict(INERTIA)
    save_state(state)

    if report:
        messages.append("📋 <b>Restock bot report</b>\n" + "\n".join(html.escape(l) for l in report_lines))
    for m in messages:
        send(m)
        time.sleep(0.4)


if __name__ == "__main__":
    main()
