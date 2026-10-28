# Swing Bot Mobile — free-to-start cloud version

This package reuses the supplied `swing_bot.py` scoring/trade-plan logic and publishes a phone-first web app. It does **not** place trades or connect to a brokerage.

## What it does

- Runs the existing bot's ranking and trade-plan logic on GitHub-hosted runners, not on your work computer.
- Publishes a mobile web app that can be added to the iPhone Home Screen.
- Separates U.S. and Canadian opportunities, displays the inherited +5% / +10% targets and stop levels, and includes news/momentum pages.
- Uses a starter list of U.S. names plus Canadian/venture symbols. Edit `watchlist.txt` in the repository to change the universe.
- Tracks holdings entered in the iPhone app locally in that browser. Export a JSON backup from the Holdings tab.

## Important limitations

- The free workflow is scheduled, not a permanently running process. GitHub may delay scheduled jobs; the app refreshes published data once per minute, but new data only appears after a scan finishes.
- Yahoo Finance data is unofficial, may be delayed or throttled, and can fail. Never assume the app's displayed price is an executable quote.
- Intraday momentum runs during the regular U.S. session only. The broader screen/news can update during off-hours runs.
- Holdings entered on the iPhone are stored on that device/browser and **are not synchronized to the cloud scanner**. Their displayed P/L is calculated in the app from the latest quote data it has. It cannot send reliable background push alerts while closed.
- The starter repo is intended for a personal research tool. The free GitHub Pages route requires publishing the repository publicly in most free setups; the source and watchlist will therefore be visible. Do not put passwords, brokerage credentials, account numbers, or private portfolio data in the repo.
- Do not commit API keys. Optional credentials must be added as GitHub Actions repository secrets only if you later add a supported provider.
- GitHub Actions scheduled workflows are not guaranteed to start at the exact cron minute. This is not a substitute for a professional real-time feed.

## Deploy it once

1. Create or sign in to a GitHub account.
2. Create a **new public repository** (for example `swing-bot-mobile`). Do not upload account numbers, API keys, or private holdings.
3. Upload the contents of this folder to the repository, including the `.github/workflows/cloud-scan.yml` file. Ensure the repository root contains `cloud_scan.py`, `swing_bot.py`, `requirements.txt`, and `watchlist.txt`.
4. In GitHub, open **Settings → Pages** and set **Build and deployment → Source** to **GitHub Actions**.
5. Open **Actions → Cloud scan and publish iPhone dashboard → Run workflow**. Wait for the scan and deploy jobs to finish.
6. Open the deployed Pages URL shown in the `github-pages` environment. It will look like `https://YOUR-USERNAME.github.io/YOUR-REPOSITORY/`.
7. On the iPhone, open that URL in Safari. Tap **Share → Add to Home Screen → Add**. Launch it from the new Home Screen icon.
8. Check **Actions** after the first run. If the scanner reports data errors, try a manual workflow run later; Yahoo can rate-limit automated requests.

## API keys / accounts

Required:
- **GitHub account** — free account is enough for this personal starter deployment.
- No API key is required for the starter scanner. It uses the existing bot's Yahoo Finance-based data functions and public headline sources.

Optional later:
- A supported paid market-data API key can improve reliability and coverage, but the existing bot's current code only uses Alpaca when `PRICE_FEED=alpaca` and valid `ALPACA_KEY` / `ALPACA_SECRET` are provided. Alpaca market data plan/market coverage must be checked before relying on it for Canadian symbols.
- `ANTHROPIC_API_KEY` is not required in this free build; AI enrichment is disabled in the scheduled scanner.
- Telegram/Discord notifications are not configured in this starter.

## Editing the universe

Edit `watchlist.txt` in GitHub. Use one Yahoo Finance symbol per line, such as `AAPL`, `CNQ.TO`, `QIMC.CN`, or `GSVR.V`. Commit the change. The next scheduled run will use the updated list.

## Strategy notes

The source defaults are preserved: 5% first target, 10% second target, five-session horizon, and the existing maximum stop filter. These are screening parameters, not predictions or guaranteed returns. The workflow currently sets `ACCOUNT_SIZE=10000`; change that value in `.github/workflows/cloud-scan.yml` if you want the bot's share-sizing calculations to use a different hypothetical account size. Do not use a public repository for personal financial data.

## Local test (optional)

```bash
python -m pip install -r requirements.txt
python cloud_scan.py
```

The first successful run writes `docs/data.json` and copies the generated HTML research pages into `docs/`.
