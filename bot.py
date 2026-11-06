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

KEYWORD = re.compile(r"pok[eé]mon|\bpkm\b|riftbound|league of legends", re.I)
CARDS = re.compile(r"tcg|booster|elite trainer|\betb\b|c[aă]r[tț]i|carton[aș]|blister|\btin\b|"
                   r"collection|colec[tț]ie|deck|bundle|display|premium|binder|sleeve", re.I)
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
RON_PRICE = re.compile(r"(\d[\d.,]*)\s*(?:lei|ron)\b", re.I)

PRICE_DROP_MIN_PCT = 3     # smaller changes are usually rounding or currency updates
PRICE_DROP_MIN_LEI = 2
SUSPECT_DROP_PCT = 60      # a drop this big must show up in 2 runs (could be a misread page)
MAX_DROP_ALERTS = 5        # more drops than this from one shop arrive as one list
DROP_LIST_LINES = 20
PRICE_REPEAT_HOURS = 24    # a price bouncing up and down alerts once a day, not every bounce

PAGE_STATS = {}            # (shop name, page) -> items found, or -1 on error
PAGES_BAD_BEFORE_WARNING = 12   # ~1 hour of failed runs for one page
DAILY_HOUR = 9             # daily health report, Romanian time
MISSES_FOR_GONE = 3        # runs an item must be missing before "reappear" counts
FAILS_BEFORE_WARNING = 12  # ~1 hour at 5-minute runs
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


def prices_from_text(text):
    """(current price, crossed-out price) from a product card's visible text.
    Shops print the two in either order, so the lower one is what you pay."""
    found = [to_price(m) for m in RON_PRICE.findall(PRICE_NOISE.sub(" ", text))]
    found = sorted({p for p in found if p})
    if not found:
        return None, None
    old = found[-1] if len(found) > 1 and found[0] >= found[-1] * 0.2 else None
    return found[0], old


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


def card_of(a):
    """Climb from a product link to its product card, stopping before the
    element that also contains other products."""
    href = a.get("href")
    card = a
    for _ in range(6):
        parent = card.parent
        if parent is None or len(clean(parent.get_text(" "))) >= 400:
            break
        others = {x.get("href") for x in parent.find_all("a", href=True) if x.find("img")}
        others.discard(href)
        if others:
            break
        card = parent
    return card


def title_of(a, card):
    img = a.find("img")
    for cand in (a.get("title"), img.get("alt") if img else None):
        if cand and len(clean(cand)) > 5:
            return clean(cand)
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
        card = card_of(a)
        text = clean(card.get_text(" "))
        if not pattern and (len(text) >= 400 or not PRICE.search(text)):
            continue
        key = norm_url(full)
        if key == norm_url(page_url) or key in out:
            continue
        title = title_of(a, card)
        if not title and pattern:
            title = urlsplit(full).path.rsplit("/", 1)[-1].replace("-", " ")
        av, pre = avail_from_text(text)
        price, old = prices_from_text(text)
        out[key] = {"title": title, "url": full, "price": price, "old": old,
                    "available": av, "preorder": pre}
    return out


def read_html(session, shop, urls=None):
    items, errors = {}, []
    fu = shop.get("filter_urls") or []
    urls = urls or shop["urls"]
    for i, url in enumerate(urls):
        if i and shop.get("delay"):
            time.sleep(shop["delay"])
        try:
            page = get(session, url)
        except requests.HTTPError as e:
            optional = url in (shop.get("may_be_empty") or [])
            if optional and e.response is not None and e.response.status_code == 404:
                PAGE_STATS[(shop["name"], url)] = 0   # page 2 that doesn't exist yet: fine
                continue
            errors.append(f"{url}: {e}")
            PAGE_STATS[(shop["name"], url)] = -1
            continue
        except Exception as e:  # noqa: BLE001
            errors.append(f"{url}: {e}")
            PAGE_STATS[(shop["name"], url)] = -1
            continue
        soup = BeautifulSoup(page, "html.parser")
        found = {}
        if not shop.get("link_regex"):
            for p in jsonld_products(soup, url):
                found[norm_url(p["url"])] = p
        cards = html_products(soup, url, shop.get("link_regex"))
        if not found or len(cards) > len(found) + 2:
            found = cards          # no usable schema data on this page: read the product cards
        else:
            # schema data often says InStock for pre-orders; trust the visible label too
            # and it rarely has the crossed-out price, or sometimes any price
            for k, v in cards.items():
                if k in found:
                    if v["preorder"]:
                        found[k]["preorder"] = True
                    found[k]["price"] = found[k].get("price") or v["price"]
                    found[k]["old"] = v["old"]
        if fu == "all" or url in fu:
            found = {k: v for k, v in found.items() if KEYWORD.search(v["title"] + " " + k)}
        if not found:
            title = soup.title.get_text(" ", strip=True)[:60] if soup.title else ""
            print(f"    [debug] {url}: 0 products, {len(page)} bytes, title={title!r}")
        PAGE_STATS[(shop["name"], url)] = len(found)
        items.update(found)
    return items, errors, len(urls)


READERS = {"shopify": read_shopify, "woo": read_woo, "html": read_html}


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
    if shop.get("cards_only"):
        items = {k: v for k, v in items.items() if CARDS.search(v["title"])}
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
    for attempt in range(3):
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


def lei(p):
    return f"{p:.2f}".replace(".00", "") + " lei"


def pct(old, new):
    return round((old - new) / old * 100)


def fmt_price(it):
    p, old = it.get("price"), it.get("old")
    if not p:
        return " · price not shown"
    return f" · {lei(p)}" + (f" (was {lei(old)}, -{pct(old, p)}%)" if old else "")


def item_msg(kind, shop, it):
    label = {"new": "🆕 NEW", "restock": "🔁 BACK IN STOCK",
             "instock": "📦 NOW IN STOCK (was pre-order)"}[kind]
    pre = " (pre-order)" if it.get("preorder") else ""
    return (f"<b>{label}{pre}</b> · {html.escape(shop)}\n"
            f"{html.escape(it['title'])}{html.escape(fmt_price(it))}\n"
            f"{html.escape(it['url'])}")


def drop_msg(shop, it, before):
    return (f"<b>💸 PRICE DROP -{pct(before, it['price'])}%</b> · {html.escape(shop)}\n"
            f"{html.escape(it['title'])}\n"
            f"{lei(before)} → <b>{lei(it['price'])}</b>\n"
            f"{html.escape(it['url'])}")


def drops_list_msg(shop, drops):
    """Shop-wide sale: one message, biggest discounts first, within Telegram's size limit."""
    drops = sorted(drops, key=lambda d: pct(d[1], d[0]["price"]), reverse=True)
    head = f"<b>💸 {len(drops)} PRICE DROPS</b> · {html.escape(shop)}"
    lines, room = [], 3700 - len(head)
    for it, before in drops[:DROP_LIST_LINES]:
        line = (f"• -{pct(before, it['price'])}% "
                f"<a href=\"{html.escape(it['url'], quote=True)}\">{html.escape(it['title'][:60])}</a> "
                f"{lei(before)} → {lei(it['price'])}")
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


def poll_status_command(state):
    """True if you sent /status to the bot since the last run."""
    token = os.environ.get("TELEGRAM_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat:
        return False
    try:
        r = requests.get(f"https://api.telegram.org/bot{token}/getUpdates",
                         params={"offset": state.get("tg_offset", 0), "timeout": 0,
                                 "allowed_updates": json.dumps(["message"])},
                         timeout=15).json()
    except (requests.RequestException, ValueError):
        return False
    wanted = False
    for u in r.get("result", []):
        state["tg_offset"] = u["update_id"] + 1
        m = u.get("message") or {}
        text = (m.get("text") or "").strip().lower()
        if str(m.get("chat", {}).get("id")) == str(chat) and text.lstrip("/").startswith("status"):
            wanted = True
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


def check_drop(price, before, prev, rec, now):
    """Decide on a lower price and update the saved record. Returns "alert" or None."""
    drop = before - price
    rec["pr"] = price
    rec.pop("pend", None)
    if drop < PRICE_DROP_MIN_LEI or drop / before * 100 < PRICE_DROP_MIN_PCT:
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
    report = bool(os.environ.get("REPORT"))
    messages, report_lines = [], []
    usable_shops = set()
    now = time.time()

    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(check_shop, shops))

    for shop, items, errors, n_sources in results:
        name = shop["name"]
        st = state["shops"].setdefault(name, {"items": {}, "fails": 0, "warned": False, "init": False})
        sig = json.dumps({k: v for k, v in shop.items() if k not in ("note", "_help", "may_be_empty")}, sort_keys=True)
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
            line += f" e.g. {next(iter(items.values()))['title'][:50]}"
        if errors:
            line += f" | errors: {len(errors)}/{n_sources}"
        report_lines.append(line)
        print(line)
        for e in errors:
            print("   ", e[:200])

        if not usable:
            st["fails"] += 1
            if st["fails"] >= FAILS_BEFORE_WARNING and not st["warned"] and st["init"]:
                messages.append(f"⚠️ <b>{html.escape(name)}</b> hasn't loaded for about an hour. "
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
            st["init"] = True
            continue

        reappear = shop.get("reappear_is_restock", shop["type"] == "woo")
        alerts, drops = [], []
        for key, it in items.items():
            prev = known.get(key)
            n_before = len(alerts)
            if prev is None:
                if it["available"] is not False:
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
                    kind = check_drop(it["price"], before, prev, rec, now)
                    if kind == "alert":
                        drops.append((it, before))
            known[key] = rec

        if complete:
            for key, rec in known.items():
                if key not in items:
                    rec["m"] = min(rec.get("m", 0) + 1, 999)

        for kind, it in alerts:
            print(f"    alert {kind}: {it['title'][:70]}")
        if len(alerts) > MAX_ALERTS_PER_SHOP:
            sample = "\n".join("• " + html.escape(it["title"][:80] + fmt_price(it))
                                for _, it in alerts[:6])
            messages.append(f"📦 <b>{html.escape(name)}</b>: {len(alerts)} new or restocked items "
                            f"at once (big drop, or the shop changed its site):\n{sample}")
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
                messages.append(f"⚠️ <b>{html.escape(sname)}</b>: one page {what} (~1 hour).\n"
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
    if poll_status_command(state):
        messages.append(health_text(state, all_shops, f"📋 Status · {local:%d %b %H:%M}"))

    save_state(state)

    if report:
        messages.append("📋 <b>Restock bot report</b>\n" + "\n".join(html.escape(l) for l in report_lines))
    for m in messages:
        send(m)
        time.sleep(0.4)


if __name__ == "__main__":
    main()
