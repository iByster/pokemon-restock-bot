# Pokémon / Riftbound restock bot — setup

Checks 20 Romanian shops every ~5 minutes and messages you on Telegram when a
Pokémon or Riftbound product is **new** or **back in stock**. Free, runs in the
cloud, laptop can be off. Takes ~15 minutes, all doable from your phone.

## 1. Make your Telegram bot (3 min)
1. In Telegram, open **@BotFather** → send `/newbot`.
2. Pick a name (e.g. *Restock Alerts*) and a username ending in `bot`.
3. BotFather replies with a **token** like `123456789:AA...`. Copy it. Keep it private.
4. Open your new bot and send it any message (e.g. `hi`).
5. In a browser open:
   `https://api.telegram.org/bot<YOUR_TOKEN>/getUpdates`
   Find `"chat":{"id":` — the number after it is your **chat ID**.

## 2. Make a GitHub account + repo (5 min)
1. Sign up free at github.com.
2. Create a new repository, e.g. `pokemon-restock-bot`.
   - Set it to **Public** (public repos get unlimited free run time; your token stays secret either way).
3. Upload these files, keeping the folders:
   - `bot.py`
   - `shops.json`
   - `requirements.txt`
   - `.github/workflows/watch.yml`

   On phone: **Add file → Create new file**, type the name exactly
   (for the workflow type `.github/workflows/watch.yml` — the slashes create folders),
   paste the contents, **Commit**. Repeat per file.

## 3. Add your secrets (2 min)
Repo → **Settings → Secrets and variables → Actions → New repository secret**:
- `TELEGRAM_TOKEN` = the token from BotFather
- `TELEGRAM_CHAT_ID` = your chat ID

## 4. Turn it on and test (2 min)
1. Repo → **Actions** tab → enable workflows if asked.
2. Click **Restock watch → Run workflow** (leave "test report" ticked).
3. Within ~1 minute you get a Telegram **report**: ✅ / ❌ per shop and how many products it found.

The first run only *learns* what's already listed — no alerts. From then on you
only hear about new and restocked items.

## Good to know
- **Speed:** every 5 minutes, but GitHub sometimes starts runs a few minutes late.
- **Singles are skipped** (Secret Cards singles, toy-shop plushies) so you don't get spammed.
- **eMAG is excluded**, as you asked. **Flamey** is paused (its shop was in maintenance).
- **Carturesti and Smyk** couldn't be tested — check them in the first report.
- If a shop stops loading for about an hour you get one ⚠️ message, and a ✅ when it's back.
- To pause a shop, set `"enabled": false` in `shops.json`. To add one, send Claude the link.
- Big drops (12+ items at once from one shop) arrive as one summary message.
