#!/usr/bin/env python3
"""
Swing Bot v3 research build - rank potential 5-10% swing setups with conservative risk checks.

Commands
  screen          Suggested BUY-IN / SELL-OUT trade screen (terminal + trade_screen.html)
  momentum        Early price movers + same-time relative volume (early_momentum.html)
  picks           Same ranking, plain list
  monitor         Run all week: Monday picks, setup alerts, position alerts
  backtest        Approximate walk-forward test (add --hourly for intraday sequencing)
  grade           Grade last weeks' logged picks against what actually happened
  scorecard       Which signals (news / social / insiders / score) actually paid off
  doctor          Check every data source and key works from YOUR machine
  build-universe  Build a watchlist from a big ticker list using LIQUIDITY ONLY
  auto-universe   Discover US/Canadian exchange-listed symbols and build a liquid watchlist
  add-position    Track a trade (stop / scale-out / time-stop / Friday alerts)
  positions       Show tracked positions

Setup:  pip install yfinance pandas numpy requests
Env (all optional):
  ANTHROPIC_API_KEY, CLAUDE_MODEL (default claude-haiku-5-5)
  TELEGRAM_BOT_TOKEN + TELEGRAM_CHAT_ID, DISCORD_WEBHOOK_URL
  ACCOUNT_SIZE (default 10000), PRICE_FEED=yahoo|alpaca (ALPACA_KEY/ALPACA_SECRET/ALPACA_FEED)

RESEARCH / ALERT TOOL ONLY. NOT FINANCIAL ADVICE. It never places trades.
"""

import argparse
import http.server
import socket
import threading
import csv
import io
import glob
import hashlib
import html
import json
import os
import tempfile
import time
import re
import sys
import time
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta
from email.utils import parsedate_to_datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests

# =============================== CONFIG =======================================

WATCHLIST_FILE = "watchlist.txt"
FILINGS_DIR = Path("filings_csv")         # SEDAR+/SEDI/insider CSV exports (ticker,date,kind[,detail,url])
STATE_DIR = Path(os.getenv("SWING_STATE_DIR", ".swing_state"))
HTML_SCREEN = "trade_screen.html"
LAST_PENNY_ROWS: list[dict] = []  # separately ranked penny-stock candidates for the HTML screen
LAST_SCREEN_ROWS: list[dict] = []  # all watchlist symbols that passed technical/liquidity checks, not just Top 20

# ---- Hard liquidity filters --------------------------------------------------
MIN_AVG_VOLUME = 100_000        # 20-day average daily volume (shares)
MIN_TODAY_VOLUME = 100_000      # latest / projected daily volume (shares)
MIN_DOLLAR_VOLUME = 50_000      # avg daily $ traded
MIN_PRICE = 0.20
IGNORE_VOLUME_FILTER = os.getenv("IGNORE_VOLUME", "0") == "1"   # or use the --ignore-volume flag

# ---- Trade plan --------------------------------------------------------------
TARGET_1 = 0.05
TARGET_2 = 0.10
STOP_MIN = 0.03                 # stop = 1.5 x ATR%, but never tighter than this
MAX_STOP_PCT = 0.04             # keep +5% target reward/risk at 1.25:1 or better
HORIZON_DAYS = 5
TIME_STOP_MIN_GAIN = 0.01       # Wednesday close: exit if not above +1%
CHASE_ATR_MULT = 0.75           # don't buy more than 0.75 ATR above the planned entry

# ---- Sizing -------------------------------------------------------------------
ACCOUNT_SIZE = float(os.getenv("ACCOUNT_SIZE", 10_000))
RISK_PCT = 0.01                 # max loss per trade as a fraction of account
MAX_POSITION_PCT = 0.20         # max position size as a fraction of account
MAX_PARTICIPATION = 0.02        # never hold more than 2% of average daily volume

# ---- Validation ---------------------------------------------------------------
OOS_FRACTION = 0.40             # last 40% of history is held out as out-of-sample
EDGE_TECH_THRESHOLD = 50        # technical score treated as the "validated tier"
EDGE_MIN_TRADES = 30
EDGE_MIN_PF = 1.10

# ---- Scanning / alerts -------------------------------------------------------
SCAN_INTERVAL_SEC = 60           # price/alert scan every 60 seconds
HTML_REFRESH_SEC = 30            # browser auto-reload of trade_screen.html every 30 seconds
NEWS_REFRESH_MIN = 10            # re-check headlines per ticker at most this often (avoids throttling)
SOCIAL_REFRESH_MIN = 10          # re-check StockTwits/Reddit per ticker at most this often
ALERT_SCORE = 65
ENRICH_TOP_N = 20
PICKS_TOP_N = 20
ALERT_COOLDOWN_HOURS = 4
NEWS_MAX_AGE_HOURS = 48
# Separate discovery scanner: it deliberately does not apply the regular swing bot's
# 4% stop / overextension gates, because its job is to flag movers for human review.
MOMENTUM_MOVE_ALERT_PCT = 0.02       # early move alert at +2% from prior close
MOMENTUM_STRONG_MOVE_PCT = 0.05      # strong move alert at +5%
MOMENTUM_RVOL_ALERT = 2.0            # 2x same-time historical volume = unusual
MOMENTUM_RVOL_EXCEPTIONAL = 3.0      # 3x = exceptional
MOMENTUM_UNIVERSE_CAP = 300          # additional candidates from market_universe.txt
MOMENTUM_INTRADAY_INTERVAL = "5m"    # use same-time cumulative volume, not full-day volume

# ---- Sources -----------------------------------------------------------------
CA_SUFFIXES = (".TO", ".V", ".CN", ".NE")


def market_side(ticker: str) -> str:
    """Return the listing side inferred from the ticker suffix convention used by this bot."""
    t = str(ticker).strip().upper()
    return "CANADA 🇨🇦" if t.endswith(CA_SUFFIXES) else "USA 🇺🇸"


def market_currency(ticker: str) -> str:
    """Currency label for prices quoted by the bot's Yahoo Finance ticker convention."""
    return "CAD" if market_side(ticker).startswith("CANADA") else "USD"
CA_NEWS_SITES = ["ceo.ca", "newsfilecorp.com", "newswire.ca", "globenewswire.com", "businesswire.com",
                 "sedarplus.ca", "tmx.com", "money.tmx.com", "ca.finance.yahoo.com", "bnnbloomberg.ca",
                 "theglobeandmail.com", "financialpost.com", "reuters.com", "seekingalpha.com",
                 "marketwatch.com", "benzinga.com", "prnewswire.com", "accesswire.com", "investing.com"]
US_NEWS_SITES = ["reuters.com", "apnews.com", "bloomberg.com", "marketwatch.com", "benzinga.com",
                 "prnewswire.com", "businesswire.com", "globenewswire.com", "sec.gov", "finance.yahoo.com",
                 "cnbc.com", "wsj.com", "investing.com", "seekingalpha.com"]
REDDIT_SUBS = ["wallstreetbets", "stocks", "pennystocks", "options", "Daytrading", "StockMarket",
               "Baystreetbets", "CanadianInvestor", "CanadianStocks", "TSXV", "SecurityAnalysis"]

BULLISH_KW = [
    "upgrade", "beats", "record revenue", "approval", "approved", "contract", "partnership",
    "acquire", "acquisition", "buyback", "drill results", "high-grade", "assay", "breakthrough",
    "raises guidance", "strategic investment", "insider buying", "letter of intent", "loi",
]
BEARISH_KW = [
    "downgrade", "misses", "offering", "bought deal", "private placement", "non-brokered",
    "dilution", "lawsuit", "investigation", "subpoena", "cease trade", "going concern",
    "resigns", "recall", "short report", "short seller", "bankruptcy", "halt",
]
RUMOR_KW = [
    "rumor", "rumour", "reportedly", "sources say", "people familiar", "in talks",
    "considering", "exploring a sale", "takeover", "speculation", "unconfirmed",
    "said to be", "according to reports", "whispers",
]

ET_TZ = ZoneInfo("America/New_York")
UA = {"User-Agent": "Mozilla/5.0 (swing-bot research script)"}

# =============================== STATE ========================================


def _load_state() -> dict:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    f = STATE_DIR / "state.json"
    base = {"cooldowns": {}, "news": {}, "names": {}, "buzz": {}, "last_picks_week": "", "edge": {}}
    if f.exists():
        try:
            base.update(json.loads(f.read_text()))
        except json.JSONDecodeError:
            pass
    return base


def _atomic_json_save(dest: Path, value) -> None:
    """Write JSON through a unique same-directory temp file; tolerate brief Windows locks."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp_name = None
    try:
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(dest.parent),
                                         prefix=dest.stem + "_", suffix=".json.tmp", delete=False) as tmp:
            tmp_name = tmp.name
            json.dump(value, tmp, indent=1, default=float)
            tmp.flush()
            os.fsync(tmp.fileno())
        last_error = None
        for attempt in range(5):
            try:
                os.replace(tmp_name, dest)
                tmp_name = None
                return
            except PermissionError as exc:
                last_error = exc
                if attempt < 4:
                    time.sleep(0.15 * (attempt + 1))
        raise last_error
    finally:
        if tmp_name and os.path.exists(tmp_name):
            try:
                os.unlink(tmp_name)
            except OSError:
                pass


def _save_state(s: dict) -> None:
    """Write state atomically so an interrupted process cannot leave truncated JSON."""
    _atomic_json_save(STATE_DIR / "state.json", s)


STATE = _load_state()


def cooldown_ok(key: str, hours: float = ALERT_COOLDOWN_HOURS) -> bool:
    now = datetime.now()
    prev = STATE["cooldowns"].get(key)
    if prev and now - datetime.fromisoformat(prev) < timedelta(hours=hours):
        return False
    STATE["cooldowns"][key] = now.isoformat()
    _save_state(STATE)
    return True


# =============================== NOTIFY =======================================


def notify(message: str) -> None:
    print(f"\n[{datetime.now():%a %H:%M:%S}] {message}\n", flush=True)
    tok, chat = os.getenv("TELEGRAM_BOT_TOKEN"), os.getenv("TELEGRAM_CHAT_ID")
    if tok and chat:
        try:
            requests.post(f"https://api.telegram.org/bot{tok}/sendMessage",
                          json={"chat_id": chat, "text": message[:4000],
                                "disable_web_page_preview": True}, timeout=10)
        except requests.RequestException as e:
            print(f"Telegram error: {e}")
    hook = os.getenv("DISCORD_WEBHOOK_URL")
    if hook:
        try:
            requests.post(hook, json={"content": message[:1900]}, timeout=10)
        except requests.RequestException as e:
            print(f"Discord error: {e}")


# =============================== TIME / FORMAT HELPERS ========================


def market_is_open(now=None) -> bool:
    """Regular session for NYSE/Nasdaq/TSX/TSXV (9:30-16:00 ET). Ignores holidays."""
    now = now or datetime.now(ET_TZ)
    if now.weekday() >= 5:
        return False
    o = now.replace(hour=9, minute=30, second=0, microsecond=0)
    c = now.replace(hour=16, minute=0, second=0, microsecond=0)
    return o <= now <= c


def day_fraction_elapsed(now=None) -> float:
    now = now or datetime.now(ET_TZ)
    o = now.replace(hour=9, minute=30, second=0, microsecond=0)
    return min(max((now - o).total_seconds() / 60 / 390, 0.1), 1.0)


def target_monday(now=None) -> datetime:
    """The Monday the current picks are for (this Monday, or next if it's Sat/Sun)."""
    now = now or datetime.now(ET_TZ)
    d = now.date() - timedelta(days=now.weekday())
    if now.weekday() >= 5:
        d += timedelta(days=7)
    return datetime(d.year, d.month, d.day)


def px(x: float) -> str:
    return f"{x:,.4f}" if x < 1 else f"{x:,.2f}"


# =============================== PRICE DATA ===================================


def _yahoo_daily(tickers: list[str], period: str) -> dict[str, pd.DataFrame]:
    import yfinance as yf
    out = {}
    for i in range(0, len(tickers), 40):
        chunk = tickers[i:i + 40]
        try:
            raw = yf.download(chunk, period=period, interval="1d", group_by="ticker",
                              progress=False, auto_adjust=True, threads=True)
        except Exception as e:
            print(f"Yahoo download failed for {chunk}: {e}")
            continue
        for t in chunk:
            try:
                d = raw[t] if isinstance(raw.columns, pd.MultiIndex) else raw
                d = d.dropna(how="all")
                if not d.empty:
                    out[t] = d
            except KeyError:
                print(f"  no data for {t}")
    return out


def _yahoo_intraday(tickers: list[str], interval: str = "60m", period: str = "730d") -> dict[str, pd.DataFrame]:
    """Hourly bars (Yahoo allows ~730 days of 60m). Used to resolve stop-vs-target order."""
    import yfinance as yf
    out = {}
    for i in range(0, len(tickers), 20):
        chunk = tickers[i:i + 20]
        try:
            raw = yf.download(chunk, period=period, interval=interval, group_by="ticker",
                              progress=False, auto_adjust=True, threads=True)
        except Exception as e:
            print(f"Yahoo intraday failed for {chunk}: {e}")
            continue
        for t in chunk:
            try:
                d = raw[t] if isinstance(raw.columns, pd.MultiIndex) else raw
                d = d.dropna(subset=["Open", "High", "Low", "Close"])
                if not d.empty:
                    out[t] = d
            except KeyError:
                pass
    return out


def _alpaca_daily(tickers: list[str], days: int = 800) -> dict[str, pd.DataFrame]:
    key, secret = os.getenv("ALPACA_KEY"), os.getenv("ALPACA_SECRET")
    if not (key and secret):
        return {}
    feed = os.getenv("ALPACA_FEED", "iex")
    if feed == "iex":
        print("WARNING: Alpaca 'iex' feed reports only IEX-exchange volume (understates real volume). "
              "Set ALPACA_FEED=sip if you have the paid plan.")
    hdr = {"APCA-API-KEY-ID": key, "APCA-API-SECRET-KEY": secret}
    start = (datetime.utcnow() - timedelta(days=days)).strftime("%Y-%m-%d")
    rows: dict[str, list] = {}
    token = None
    while True:
        params = {"symbols": ",".join(tickers), "timeframe": "1Day", "start": start,
                  "limit": 10000, "adjustment": "all", "feed": feed}
        if token:
            params["page_token"] = token
        try:
            r = requests.get("https://data.alpaca.markets/v2/stocks/bars", headers=hdr,
                             params=params, timeout=20)
            r.raise_for_status()
            j = r.json()
        except requests.RequestException as e:
            print(f"Alpaca error: {e}")
            break
        for sym, bars in (j.get("bars") or {}).items():
            rows.setdefault(sym, []).extend(bars)
        token = j.get("next_page_token")
        if not token:
            break
    out = {}
    for sym, bars in rows.items():
        d = pd.DataFrame(bars)
        d.index = pd.to_datetime(d["t"])
        d = d.rename(columns={"o": "Open", "h": "High", "l": "Low", "c": "Close", "v": "Volume"})
        out[sym] = d[["Open", "High", "Low", "Close", "Volume"]]
    return out


def fetch_daily(tickers: list[str], period: str = "1y") -> dict[str, pd.DataFrame]:
    data: dict[str, pd.DataFrame] = {}
    if os.getenv("PRICE_FEED", "yahoo").lower() == "alpaca":
        us = [t for t in tickers if not t.upper().endswith(CA_SUFFIXES)]
        data.update(_alpaca_daily(us))
    rest = [t for t in tickers if t not in data]
    if rest:
        data.update(_yahoo_daily(rest, period))
    return data


# =============================== TECHNICAL FEATURES ===========================


def rsi(close: pd.Series, n: int = 14) -> float:
    d = close.diff()
    g = d.clip(lower=0).ewm(alpha=1 / n, adjust=False).mean()
    l = (-d.clip(upper=0)).ewm(alpha=1 / n, adjust=False).mean()
    avg_gain, avg_loss = float(g.iloc[-1]), float(l.iloc[-1])
    if avg_loss <= 1e-12:
        return 100.0 if avg_gain > 1e-12 else 50.0
    if avg_gain <= 1e-12:
        return 0.0
    rs = avg_gain / avg_loss
    return float(100 - 100 / (1 + rs))


def forward_stats(df: pd.DataFrame, target: float, stop: float,
                  horizon: int = HORIZON_DAYS, lookback: int = 120) -> tuple[float, float, int]:
    """Estimate target-first and stop-first rates over the next `horizon` bars.

    If a daily bar touches both target and stop, count it as stop-first because
    daily bars do not reveal intraday order. This is a diagnostic, not a forecast.
    """
    o, h, l = (df[k].to_numpy(dtype=float) for k in ("Open", "High", "Low"))
    n = len(df)
    target_first = stop_first = cnt = 0
    start = max(0, n - horizon - lookback)
    for i in range(start, n - horizon + 1):
        entry = o[i]
        if not np.isfinite(entry) or entry <= 0:
            continue
        target_px, stop_px = entry * (1 + target), entry * (1 - stop)
        cnt += 1
        outcome = None
        for j in range(i, min(i + horizon, n)):
            if l[j] <= stop_px:  # conservative tie-break if both levels hit in one bar
                outcome = "stop"
                break
            if h[j] >= target_px:
                outcome = "target"
                break
        if outcome == "target":
            target_first += 1
        elif outcome == "stop":
            stop_first += 1
    if cnt == 0:
        return 0.0, 0.0, 0
    return target_first / cnt, stop_first / cnt, cnt


def compute_features(df: pd.DataFrame, live: bool = False,
                     target: float = TARGET_1, stop: float = 0.04) -> dict | None:
    df = df.dropna(subset=["Open", "High", "Low", "Close"])
    if len(df) < 60:
        return None
    c, h, l, v = df["Close"], df["High"], df["Low"], df["Volume"].fillna(0)
    price = float(c.iloc[-1])
    if price <= 0:
        return None

    avg_vol = float(v.iloc[-21:-1].mean())
    last_vol = float(v.iloc[-1])
    if live and market_is_open() and df.index[-1].date() == datetime.now(ET_TZ).date():
        last_vol /= day_fraction_elapsed()
    rvol = last_vol / avg_vol if avg_vol > 0 else 0.0

    tr = pd.concat([h - l, (h - c.shift()).abs(), (l - c.shift()).abs()], axis=1).max(axis=1)
    atr_pct = float(tr.rolling(14).mean().iloc[-1] / price)
    sma20_series, sma50_series = c.rolling(20).mean(), c.rolling(50).mean()
    sma20, sma50 = float(sma20_series.iloc[-1]), float(sma50_series.iloc[-1])
    high20 = float(h.iloc[-21:-1].max())
    # MACD(12,26,9): confirmation only, never a standalone entry trigger.
    ema12, ema26 = c.ewm(span=12, adjust=False).mean(), c.ewm(span=26, adjust=False).mean()
    macd_line = ema12 - ema26
    macd_signal = macd_line.ewm(span=9, adjust=False).mean()
    macd_hist = float((macd_line - macd_signal).iloc[-1])
    macd_hist_prev = float((macd_line - macd_signal).iloc[-2])
    # Simple structure check: compare recent 5-bar swing range with the preceding 5 bars.
    higher_highs = float(h.iloc[-5:].max()) > float(h.iloc[-10:-5].max())
    higher_lows = float(l.iloc[-5:].min()) > float(l.iloc[-10:-5].min())
    trend_structure = higher_highs and higher_lows
    pullback_dist = price / sma20 - 1 if sma20 > 0 else 0.0
    touch, stop_rate, samples = forward_stats(df, target, stop)

    return {
        "price": price, "avg_vol": avg_vol, "last_vol": last_vol, "dollar_vol": avg_vol * price,
        "rvol": rvol, "rsi": rsi(c),
        "roc5": price / float(c.iloc[-6]) - 1, "roc10": price / float(c.iloc[-11]) - 1,
        "above_sma20": price > sma20, "sma20_gt_sma50": sma20 > sma50,
        "sma20": sma20, "sma50": sma50, "pullback_dist": pullback_dist,
        "macd_hist": macd_hist, "macd_hist_rising": macd_hist > macd_hist_prev,
        "higher_highs": higher_highs, "higher_lows": higher_lows, "trend_structure": trend_structure,
        "high20": high20, "breakout_ratio": price / high20 if high20 > 0 else 0,
        "atr_pct": atr_pct, "touch_rate": touch, "stop_rate": stop_rate, "samples": samples,
        "chg_today": price / float(c.iloc[-2]) - 1,
    }


def liquidity_gate(f: dict) -> tuple[bool, str]:
    if f["price"] < MIN_PRICE:
        return False, f"price ${f['price']:.2f} < ${MIN_PRICE}"
    if IGNORE_VOLUME_FILTER:
        return True, ""
    if f["avg_vol"] < MIN_AVG_VOLUME:
        return False, f"avg vol {f['avg_vol']:,.0f} < {MIN_AVG_VOLUME:,}"
    if f["last_vol"] < MIN_TODAY_VOLUME:
        return False, f"latest vol {f['last_vol']:,.0f} < {MIN_TODAY_VOLUME:,}"
    if f["dollar_vol"] < MIN_DOLLAR_VOLUME:
        return False, f"avg $ volume ${f['dollar_vol']:,.0f} < ${MIN_DOLLAR_VOLUME:,}"
    return True, ""


def tech_score(f: dict) -> tuple[float, list[str]]:
    """Heuristic technical score (nominal positive maximum 70), minus risk penalties."""
    s, why = 0.0, []
    if f["above_sma20"]:
        s += 7; why.append("above 20d SMA")
    if f["sma20_gt_sma50"]:
        s += 6; why.append("20d > 50d SMA (uptrend)")
    if f.get("trend_structure"):
        s += 5; why.append("higher highs + higher lows")
    elif f.get("higher_highs") or f.get("higher_lows"):
        s += 1; why.append("mixed recent price structure")
    if f.get("macd_hist", 0) > 0 and f.get("macd_hist_rising"):
        s += 5; why.append("MACD positive and strengthening")
    elif f.get("macd_hist", 0) < 0:
        s -= 3; why.append("MACD below signal (momentum caution)")
    if 0.03 <= f["roc10"] <= 0.30:
        s += 6; why.append(f"10d momentum {f['roc10']:+.1%}")
    elif f["roc10"] > 0.40:
        s -= 6; why.append(f"extended: 10d {f['roc10']:+.0%} (chase risk)")
    if 55 <= f["rsi"] <= 68:
        s += 6; why.append(f"RSI {f['rsi']:.0f} (positive momentum)")
    elif 68 < f["rsi"] <= 75:
        s += 2; why.append(f"RSI {f['rsi']:.0f} (strong but extended)")
    elif f["rsi"] > 75:
        s -= 8; why.append(f"RSI {f['rsi']:.0f} (overbought / chase risk)")
    s += min(max((f["rvol"] - 1) / 1.5, 0), 1) * 20
    if f["rvol"] >= 1.5:
        why.append(f"volume {f['rvol']:.1f}x normal")
    br = f["breakout_ratio"]
    if br >= 1.0:
        s += 10; why.append("breaking 20d high")
    elif br >= 0.98:
        s += 7; why.append("within 2% of 20d high")
    elif br >= 0.95:
        s += 3
    # Pullbacks are useful only when the longer trend remains constructive.
    pdist = float(f.get("pullback_dist", 0.0))
    if f.get("sma20_gt_sma50") and -0.025 <= pdist <= 0.01 and f.get("rsi", 50) >= 40:
        s += 5; why.append("controlled pullback near 20d SMA")
    if f.get("chg_today", 0) >= 0.08:
        s -= 8; why.append("large one-day spike (chase risk)")
    # Target-first rate avoids inflated scores when the stop was hit earlier.
    # Historical windows are diagnostics, not calibrated probability forecasts.
    s += min(f["touch_rate"] / 0.35, 1) * 15
    why.append(f"historical target-first rate {f['touch_rate']:.0%} over {f['samples']} windows (diagnostic only)")
    if f["stop_rate"] > 0.30:
        s -= 10; why.append(f"stop-first rate elevated ({f['stop_rate']:.0%})")
    elif f["stop_rate"] > 0.20:
        s -= 5; why.append(f"stop-first rate {f['stop_rate']:.0%}")
    return max(0.0, min(80.0, s)), why


def classify_setup(f: dict, plan: dict | None = None) -> tuple[str, str]:
    """Label the chart setup; a label is a screening aid, not a trade instruction."""
    if plan is not None and (not plan.get("ok", False) or plan.get("rr1", 0) < 1.25):
        return "AVOID", "risk/reward or volatility fails the entry gate"
    if f.get("rvol", 0) < 0.8:
        return "AVOID", "volume is weak; confirm liquidity and spread"
    if f.get("rsi", 50) > 75 or f.get("chg_today", 0) >= 0.08:
        return "AVOID", "overextended; do not chase a sharp move"
    br = f.get("breakout_ratio", 0)
    if br >= 1.0 and f.get("rvol", 0) >= 1.2:
        return "BREAKOUT", "above 20-day resistance with volume confirmation"
    if (f.get("sma20_gt_sma50") and -0.025 <= f.get("pullback_dist", 0) <= 0.01
            and f.get("rsi", 50) >= 40 and f.get("macd_hist_rising")):
        return "PULLBACK", "near 20-day average in an uptrend; momentum improving"
    if f.get("above_sma20") and f.get("sma20_gt_sma50") and f.get("roc10", 0) > 0:
        return "TREND CONTINUATION", "price and moving-average trend remain positive"
    return "WATCH", "setup confirmation is incomplete"


# =============================== TRADE PLAN (BUY-IN / SELL-OUT) ===============


def size_position(plan: dict, f: dict) -> dict:
    """Shares limited by risk budget, max position size, and share of daily volume."""
    risk_ps = plan["entry"] - plan["stop"]
    opts = {
        "risk budget": ACCOUNT_SIZE * RISK_PCT / risk_ps if risk_ps > 0 else 0,
        "position cap": ACCOUNT_SIZE * MAX_POSITION_PCT / plan["entry"],
        "liquidity (2% of volume)": MAX_PARTICIPATION * f["avg_vol"],
    }
    limit = min(opts, key=opts.get)
    shares = int(max(0, np.floor(opts[limit])))
    return {"shares": shares, "cost": shares * plan["entry"], "risk": shares * risk_ps, "limit": limit}


def trade_plan(f: dict, entry_override: float | None = None) -> dict:
    """Suggested buy-in zone and sell-out levels, all scaled to the stock's own volatility."""
    ref, atr = float(f["price"]), float(f["atr_pct"])
    if not np.isfinite(ref) or ref <= 0 or not np.isfinite(atr) or atr <= 0:
        raise ValueError("trade_plan requires a positive finite price and ATR percentage")
    if entry_override is not None and (not np.isfinite(entry_override) or entry_override <= 0):
        raise ValueError("entry_override must be a positive finite price")
    stop_pct = max(1.5 * atr, STOP_MIN)
    br, trigger = f["breakout_ratio"], None
    if 0.97 <= br < 1.0:
        style = "breakout buy-stop (buy only if it trades through the trigger)"
        trigger = f["high20"] * 1.002
        lo, hi, entry = trigger, trigger * (1 + 0.3 * atr), trigger
    elif br >= 1.0:
        style = "continuation limit (already through its 20d high; don't chase)"
        lo, hi, entry = ref * (1 - 0.3 * atr), ref * (1 + 0.3 * atr), ref
    else:
        style = "pullback limit (buy the dip toward support)"
        lo, hi = ref * (1 - 0.5 * atr), ref * (1 + 0.1 * atr)
        entry = (lo + hi) / 2
    if entry_override:
        entry = entry_override
    plan = {
        "style": style, "trigger": trigger, "buy_lo": lo, "buy_hi": hi, "entry": entry,
        "chase": entry * (1 + CHASE_ATR_MULT * atr),
        "stop": entry * (1 - stop_pct), "stop_pct": stop_pct,
        "t1": entry * (1 + TARGET_1), "t2": entry * (1 + TARGET_2),
        "trail": entry * atr, "rr1": TARGET_1 / stop_pct, "rr2": TARGET_2 / stop_pct,
        "ok": stop_pct <= MAX_STOP_PCT,
    }
    # Reject weak first-target reward/risk even if volatility is within the stop cap.
    plan["rr_ok"] = plan["rr1"] >= 1.25
    plan["ok"] = bool(plan["ok"] and plan["rr_ok"])
    plan["size"] = size_position(plan, f)
    return plan


# =============================== NEWS (+ LLM RATING) ==========================


def company_name(ticker: str) -> str:
    names = STATE["names"]
    if ticker in names:
        return names[ticker]
    name = ""
    try:
        import yfinance as yf
        info = yf.Ticker(ticker).info
        name = info.get("shortName") or info.get("longName") or ""
    except Exception:
        pass
    names[ticker] = name
    _save_state(STATE)
    return name


def google_news(query: str) -> list[dict]:
    url = ("https://news.google.com/rss/search?q=" + urllib.parse.quote(query)
           + "&hl=en-CA&gl=CA&ceid=CA:en")
    try:
        r = requests.get(url, headers=UA, timeout=12)
        r.raise_for_status()
        root = ET.fromstring(r.content)
    except (requests.RequestException, ET.ParseError):
        return []
    out = []
    cutoff = datetime.now(ET_TZ) - timedelta(hours=NEWS_MAX_AGE_HOURS)
    for it in root.iter("item"):
        try:
            when = parsedate_to_datetime(it.findtext("pubDate") or "")
        except (TypeError, ValueError):
            when = None
        if when and when < cutoff:
            continue
        out.append({"title": (it.findtext("title") or "").strip(),
                    "link": (it.findtext("link") or "").strip(),
                    "source": (it.findtext("source") or "").strip()})
    return out[:15]


def news_queries(ticker: str) -> list[str]:
    base = ticker.split(".")[0]
    name = company_name(ticker)
    label = f'"{name}"' if name else base
    if ticker.upper().endswith(CA_SUFFIXES):
        sites = " OR ".join(f"site:{s}" for s in CA_NEWS_SITES)
        return [f"{label} (TSX OR TSXV OR CSE) when:2d", f"{label} ({sites}) when:2d",
                f'"{base}" stock financing earnings contract when:2d']
    sites = " OR ".join(f"site:{s}" for s in US_NEWS_SITES)
    return [f"{label} stock when:2d", f"{label} ({sites}) when:2d",
            f'"{base}" stock SEC earnings guidance contract when:2d']


def keyword_rate(title: str) -> dict:
    t = title.lower()
    rumor = any(k in t for k in RUMOR_KW)
    bull = any(k in t for k in BULLISH_KW)
    bear = any(k in t for k in BEARISH_KW)
    if bear and not bull:
        return {"direction": "bearish", "catalyst": 5, "credibility": 6, "rumor": rumor}
    if bull or rumor:
        return {"direction": "bullish", "catalyst": 5 if bull else 3,
                "credibility": 3 if rumor else 6, "rumor": rumor}
    return {"direction": "neutral", "catalyst": 0, "credibility": 5, "rumor": False}


def llm_rate(ticker: str, name: str, titles: list[str]) -> list[dict] | None:
    key = os.getenv("ANTHROPIC_API_KEY")
    if not key or not titles:
        return None
    prompt = (
        f"You are screening news for a 1-week swing trade (buy Monday, sell Friday, primary +5% target, optional +10% stretch target) "
        f"in {name or ticker} ({ticker}).\n"
        "Rate each headline. Reply with ONLY a JSON array, one object per headline in order:\n"
        '{"i":0,"direction":"bullish|bearish|neutral","catalyst":0-10 (how likely to move price within '
        'days),"credibility":0-10 (official release/major outlet = high; anonymous/forum/speculative = low),'
        '"rumor":true|false}\n'
        "Treat dilutive financings (bought deals, private placements) as bearish. "
        "Headlines:\n" + "\n".join(f"{i}. {t}" for i, t in enumerate(titles))
    )
    try:
        r = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={"x-api-key": key, "anthropic-version": "2023-06-01",
                     "content-type": "application/json"},
            json={"model": os.getenv("CLAUDE_MODEL", "claude-haiku-5-5"), "max_tokens": 1200,
                  "messages": [{"role": "user", "content": prompt}]},
            timeout=40)
        r.raise_for_status()
        text = "".join(b.get("text", "") for b in r.json()["content"])
        text = re.sub(r"^```(?:json)?|```$", "", text.strip(), flags=re.M).strip()
        arr = json.loads(text)
        by_i = {int(x["i"]): x for x in arr}
        return [by_i.get(i) or keyword_rate(t) for i, t in enumerate(titles)]
    except Exception as e:
        print(f"  LLM rating failed ({e}); using keyword fallback")
        return None


def _contrib(r: dict) -> float:
    mag = r["catalyst"] * r["credibility"] / 10
    return mag if r["direction"] == "bullish" else -mag if r["direction"] == "bearish" else 0.0


def news_signal(ticker: str, use_llm: bool = True) -> dict:
    """Fetch headlines, rate only NEW ones, cache ratings. Returns net score -10..10."""
    cache = STATE["news"].setdefault(ticker, [])
    cutoff = (datetime.now() - timedelta(hours=NEWS_MAX_AGE_HOURS)).isoformat()
    cache[:] = [x for x in cache if x["ts"] >= cutoff]
    known = {x["h"] for x in cache}

    fresh, seen = [], set()
    fetched = STATE.setdefault("news_fetched", {})
    last = fetched.get(ticker)
    due = not last or (datetime.now() - datetime.fromisoformat(last)).total_seconds() >= NEWS_REFRESH_MIN * 60
    if due:                                  # otherwise reuse cached ratings (keeps 2-min scans polite)
        fetched[ticker] = datetime.now().isoformat()
        for q in news_queries(ticker):
            for it in google_news(q):
                h = hashlib.md5(it["title"].encode()).hexdigest()[:12]
                if h in known or h in seen:
                    continue
                seen.add(h)
                it["h"] = h
                fresh.append(it)
            time.sleep(0.4)

    if fresh:
        ratings = llm_rate(ticker, company_name(ticker), [x["title"] for x in fresh]) if use_llm else None
        for i, it in enumerate(fresh):
            r = (ratings[i] if ratings else None) or keyword_rate(it["title"])
            r = {"direction": r.get("direction", "neutral"), "catalyst": float(r.get("catalyst", 0)),
                 "credibility": float(r.get("credibility", 5)), "rumor": bool(r.get("rumor", False))}
            cache.append({**r, "h": it["h"], "title": it["title"], "link": it["link"],
                          "source": it["source"], "ts": datetime.now().isoformat()})
    _save_state(STATE)

    pos = max([_contrib(x) for x in cache if _contrib(x) > 0], default=0.0)
    neg = min([_contrib(x) for x in cache if _contrib(x) < 0], default=0.0)
    rumors = [x for x in cache if x["rumor"]]
    best = sorted(cache, key=lambda x: abs(_contrib(x)), reverse=True)[:3]
    return {"net": max(-10.0, min(10.0, pos + neg)), "neg": neg, "rumors": rumors,
            "top": best, "new_count": len(fresh)}


# =============================== SOCIAL =======================================


def stocktwits_signal(ticker: str) -> dict:
    try:
        r = requests.get(f"https://api.stocktwits.com/api/2/streams/symbol/{ticker}.json",
                         headers=UA, timeout=10)
        r.raise_for_status()
        msgs = r.json().get("messages", [])
    except Exception:
        return {"msgs": 0, "bull_ratio": None}
    bull = bear = 0
    for m in msgs:
        s = ((m.get("entities") or {}).get("sentiment") or {}).get("basic")
        bull += s == "Bullish"
        bear += s == "Bearish"
    tagged = bull + bear
    return {"msgs": len(msgs), "bull_ratio": bull / tagged if tagged >= 8 else None}


def _reddit_url(base: str) -> str:
    return (f"https://www.reddit.com/r/{'+'.join(REDDIT_SUBS)}/search.json?"
            + urllib.parse.urlencode({"q": f'"${base}" OR "{base}"', "restrict_sr": 1,
                                      "sort": "new", "t": "day", "limit": 100}))


def reddit_signal(ticker: str) -> dict:
    base = ticker.split(".")[0].upper()
    if len(base) < 3:
        return {"mentions": 0, "buzz": 0.0}
    try:
        r = requests.get(_reddit_url(base), headers=UA, timeout=12)
        r.raise_for_status()
        posts = r.json()["data"]["children"]
    except Exception:
        return {"mentions": 0, "buzz": 0.0}
    pat = re.compile(rf"(?<![A-Za-z])\$?{re.escape(base)}(?![A-Za-z])")
    n = sum(1 for p in posts if pat.search(p["data"].get("title", "") + " " + p["data"].get("selftext", "")))
    today = datetime.now().strftime("%Y-%m-%d")
    hist = STATE["buzz"].setdefault(ticker, [])
    rec = STATE["buzz"][ticker] = [x for x in hist if isinstance(x, list) and x[0] != today][-14:]
    base_counts = [x[1] for x in rec[-7:]]
    baseline = float(np.mean(base_counts)) if base_counts else None
    rec.append([today, n])
    buzz = n / max(baseline, 1.0) if baseline is not None else 0.0
    return {"mentions": n, "buzz": buzz}


def social_points(ticker: str) -> tuple[float, list[str]]:
    cache = STATE.setdefault("social_cache", {})
    c = cache.get(ticker)
    if c and (datetime.now() - datetime.fromisoformat(c["ts"])).total_seconds() < SOCIAL_REFRESH_MIN * 60:
        return c["pts"], c["why"]
    pts, why = 0.0, []
    st = stocktwits_signal(ticker)
    if st["bull_ratio"] is not None and st["bull_ratio"] >= 0.65:
        pts += 2; why.append(f"StockTwits {st['bull_ratio']:.0%} bullish")
    rd = reddit_signal(ticker)
    if rd["mentions"] >= 5 and rd["buzz"] >= 3:
        pts += 2; why.append(f"Reddit buzz {rd['buzz']:.1f}x ({rd['mentions']} mentions/24h)")
    time.sleep(0.5)
    cache[ticker] = {"ts": datetime.now().isoformat(), "pts": pts, "why": why}
    _save_state(STATE)
    return pts, why


# =============================== FILINGS / INSIDERS ===========================


def filings_signal(ticker: str) -> dict:
    """Reads CSVs you export from SEDAR+/SEDI/Canadian Insider etc. into ./filings_csv.
    Columns: ticker,date,kind[,detail,url]. Falls back to Yahoo insider data (mostly US)."""
    out = {"insider_buy": False, "block": "", "notes": []}
    base = ticker.split(".")[0].upper()
    found = False
    for p in glob.glob(str(FILINGS_DIR / "*.csv")):
        try:
            df = pd.read_csv(p)
            df.columns = [c.strip().lower() for c in df.columns]
            df["date"] = pd.to_datetime(df["date"], errors="coerce")
        except Exception:
            continue
        if not {"ticker", "date", "kind"} <= set(df.columns):
            continue
        sub = df[df["ticker"].astype(str).str.upper().str.split(".").str[0] == base]
        for _, r in sub.iterrows():
            found = True
            age = (datetime.now() - r["date"]).days if pd.notna(r["date"]) else 999
            kind = str(r["kind"]).lower()
            if age <= 90 and re.search(r"cease trade|\bcto\b|halt|going concern", kind):
                out["block"] = f"{r['kind']} ({r['date']:%Y-%m-%d})"
            if age <= 14 and re.search(r"insider.*(buy|acqui|purchase)|acquisition|purchase", kind):
                out["insider_buy"] = True
                out["notes"].append(f"insider buy {r['date']:%Y-%m-%d}")
    if not found:
        try:
            import yfinance as yf
            tx = yf.Ticker(ticker).insider_transactions
            if tx is not None and not tx.empty:
                col_date = next((c for c in tx.columns if "date" in c.lower()), None)
                col_txt = next((c for c in tx.columns if c.lower() in ("text", "transaction")), None)
                if col_date and col_txt:
                    d = pd.to_datetime(tx[col_date], errors="coerce")
                    recent = tx[(datetime.now() - d).dt.days <= 14]
                    if recent[col_txt].astype(str).str.contains("Purchase|Buy", case=False).any():
                        out["insider_buy"] = True
                        out["notes"].append("recent insider purchase (Yahoo)")
        except Exception:
            pass
    return out


# =============================== TRADE SIMULATION =============================


def simulate_trade(bars: pd.DataFrame, entry: float, t1: float, t2: float, stop: float,
                   scale_out: bool = True) -> tuple[float, str, bool]:
    """Walk bars (daily or hourly) from the entry bar through Friday.
    Rules: stop first if stop and target are in the same bar (conservative); at T1 sell half and
    move the stop to breakeven; remaining half exits at T2, breakeven stop, Wednesday time-stop
    (if never reached +1%), or Friday close. Returns (return, outcome, hit_t1)."""
    pos, realized, cur_stop, hit_t1 = 1.0, 0.0, stop, False
    last_close = entry
    for d, g in bars.groupby(bars.index.date):
        for o, h, l, c in zip(g["Open"], g["High"], g["Low"], g["Close"]):
            last_close = c
            # On OHLC bars, do not assume T1 and T2 were reached in sequence in the
            # same bar. T2 is eligible only if the position was already scaled out
            # before this bar began (or on a later hourly bar).
            hit_t1_before_bar = hit_t1
            if o <= cur_stop and o != entry:                       # gap through the stop
                realized += pos * (o / entry - 1)
                return realized, "t1_be" if hit_t1 else "stop", hit_t1
            if hit_t1 and o >= t2:
                realized += pos * (o / entry - 1)
                return realized, "t2", True
            if l <= cur_stop:
                realized += pos * (cur_stop / entry - 1)
                return realized, "t1_be" if hit_t1 else "stop", hit_t1
            if not hit_t1 and h >= t1:
                if not scale_out:
                    return t1 / entry - 1, "t1", True
                realized += 0.5 * (t1 / entry - 1)
                pos, hit_t1, cur_stop = 0.5, True, max(cur_stop, entry)
            if hit_t1_before_bar and h >= t2:
                realized += pos * (t2 / entry - 1)
                return realized, "t2", True
        if d.weekday() == 2 and not hit_t1 and (last_close / entry - 1) < TIME_STOP_MIN_GAIN:
            realized += pos * (last_close / entry - 1)
            return realized, "time_stop", hit_t1
    realized += pos * (last_close / entry - 1)
    return realized, "t1_fri" if hit_t1 else "friday", hit_t1


# =============================== SCORING PIPELINE =============================


# Fallback Canadian symbols are added only when the active watchlist has fewer than
# 20 Canadian listings. Existing watchlist entries are preserved and ranked normally.
# These are candidate symbols, not buy recommendations; quote/history filters still apply.
CANADIAN_FALLBACK_TICKERS = [
    "RY.TO", "TD.TO", "BNS.TO", "BMO.TO", "CM.TO", "NA.TO", "MFC.TO", "SLF.TO",
    "GWO.TO", "POW.TO", "IFC.TO", "BN.TO", "BAM.TO", "FTS.TO", "EMA.TO", "ENB.TO",
    "TRP.TO", "PPL.TO", "KEY.TO", "CNQ.TO", "SU.TO", "CVE.TO", "IMO.TO", "CP.TO",
    "CNR.TO", "TFII.TO", "WCN.TO", "WSP.TO", "ATD.TO", "DOL.TO", "MRU.TO", "L.TO",
    "QSR.TO", "CTC-A.TO", "MG.TO", "SHOP.TO", "CSU.TO", "DSG.TO", "GIB-A.TO", "OTEX.TO",
    "KXS.TO", "LSPD.TO", "WELL.TO", "HPS-A.TO", "CLS.TO", "EQB.TO", "CWB.TO", "AC.TO",
    "NTR.TO", "AEM.TO", "ABX.TO", "FNV.TO", "K.TO", "WDO.TO", "EQX.TO", "OR.TO",
    "CCO.TO", "DML.TO", "NXE.TO", "HUT.TO", "BITF.TO", "GLXY.TO", "MDA.TO", "QIMC.CN",
    "GSVR.V", "PNG.V", "VGCX.TO", "LUN.TO", "ERO.TO", "HBM.TO", "TECK-B.TO", "FM.TO",
    "CS.TO", "BTO.TO", "PAAS.TO", "AGI.TO", "AYA.TO", "ARIS.TO", "IVN.TO", "DPM.TO",
    "SVM.TO", "WFG.TO", "IFP.TO", "NVEI.TO", "BBD-B.TO", "BIR.TO", "PEY.TO", "TOU.TO",
    "ARX.TO", "MEG.TO", "PSK.TO", "CCL-B.TO", "GIL.TO", "MTY.TO", "PBH.TO",
]

def load_watchlist() -> list[str]:
    p = Path(WATCHLIST_FILE)
    if not p.exists():
        sys.exit(f"{WATCHLIST_FILE} not found. Create it (one ticker per line) or run auto-universe.")
    out = []
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.split("#")[0].strip().upper()
        if line:
            out.append(line)
    out = list(dict.fromkeys(out))
    canadian_count = sum(t.endswith(CA_SUFFIXES) for t in out)
    if canadian_count < PICKS_TOP_N:
        added = [t for t in CANADIAN_FALLBACK_TICKERS if t not in out and t.endswith(CA_SUFFIXES)]
        out.extend(added)
        print(
            f"Canadian coverage: watchlist has {canadian_count} Canadian tickers; "
            f"added {len(added)} Canadian fallback candidates so the screen can rank both markets. "
            "Only tickers with usable price history and passing filters will appear."
        )
    return out


def technical_pass(data: dict[str, pd.DataFrame], live: bool) -> list[dict]:
    rows, illiquid, wide = [], [], []
    for t, df in data.items():
        f = compute_features(df, live=live)
        if not f:
            continue
        ok, why_not = liquidity_gate(f)
        if not ok:
            illiquid.append((t, why_not))
            continue
        plan = trade_plan(f)
        if not plan["ok"]:
            wide.append((t, plan["stop_pct"]))
            continue
        setup, setup_note = classify_setup(f, plan)
        sc, why = tech_score(f)
        why.insert(0, f"setup: {setup} — {setup_note}")
        rows.append({"ticker": t, "f": f, "tech": sc, "why": why, "plan": plan,
                     "setup": setup, "setup_note": setup_note})
    rows.sort(key=lambda r: r["tech"], reverse=True)
    if illiquid:
        print(f"Filtered {len(illiquid)} on liquidity (e.g. "
              + "; ".join(f"{t}: {w}" for t, w in illiquid[:3]) + ")")
    if wide:
        print(f"Filtered {len(wide)} as too volatile for a +5-10% plan (needs stop > {MAX_STOP_PCT:.0%}; e.g. "
              + ", ".join(f"{t} {s:.0%}" for t, s in wide[:3]) + ")")
    return rows


def enrich(row: dict, use_llm=True, use_social=True, use_news=True) -> dict:
    t = row["ticker"]
    ext, reasons = 0.0, []
    row["news"], row["filings"] = None, filings_signal(t)
    row["social_pts"] = 0.0
    if row["filings"]["block"]:
        row["blocked"] = f"BLOCKED: {row['filings']['block']}"
    if use_news:
        n = news_signal(t, use_llm)
        row["news"] = n
        ext += max(-10.0, min(12.0, n["net"] / 10 * 12))
        if n["net"] >= 3:
            reasons.append(f"catalyst news (score {n['net']:.1f}/10)")
        if n["neg"] <= -5:
            row["blocked"] = row.get("blocked") or "BEARISH NEWS: " + (n["top"][0]["title"][:70] if n["top"] else "")
        if n["rumors"]:
            reasons.append("unverified rumor detected (no score bonus applied)")
    if use_social:
        pts, why = social_points(t)
        ext += pts; reasons += why
        row["social_pts"] = pts
    if row["filings"]["insider_buy"]:
        ext += 4; reasons.append("insider buying")
    row["ext"], row["ext_why"] = ext, reasons
    # Separate descriptive news/social momentum from the technical trade score.
    # Rumours are displayed but never add a positive momentum bonus.
    news_net = float((row.get("news") or {}).get("net", 0.0))
    social = float(row.get("social_pts", 0.0))
    momentum = 50.0 + news_net * 3.0 + social * 5.0
    if row.get("news") and row["news"].get("rumors") and news_net <= 0:
        momentum = min(momentum, 52.0)
    row["momentum"] = max(0.0, min(100.0, momentum))
    row["total"] = max(0.0, min(100.0, row["tech"] + ext))
    return row


# =============================== VALIDATION (BACKTEST) ========================


def week_bars(daily: pd.DataFrame, i: int, hourly: pd.DataFrame | None) -> pd.DataFrame:
    start = daily.index[i]
    end = start + timedelta(days=5)
    if hourly is not None and not hourly.empty:
        d0, d1 = start.date(), end.date()
        hb = hourly[(hourly.index.date >= d0) & (hourly.index.date <= d1)]
        if len(hb) >= 3 and hb.index[0].date() == d0:
            return hb
    wk = daily.iloc[i:i + HORIZON_DAYS]
    return wk[wk.index <= end]


def find_entry_fill(bars: pd.DataFrame, plan: dict) -> tuple[int | None, float | None, str]:
    """Simulate a conservative entry order using only each bar's OHLC.

    Breakout setups use a buy-stop at the trigger. Pullback/continuation setups use
    a limit at the planned entry. If the open gaps through a stop/limit, use the
    open as the executable price when appropriate. OHLC bars cannot reveal the
    exact intrabar sequence, so the later exit simulation remains conservative.
    Returns (bar_position, fill_price, reason).
    """
    if bars.empty:
        return None, None, "no_bars"
    style = str(plan.get("style", "" )).lower()
    chase = float(plan.get("chase", 0.0))
    lo, hi = float(plan.get("buy_lo", 0.0)), float(plan.get("buy_hi", float("inf")))
    entry = float(plan.get("entry", 0.0))
    trigger = plan.get("trigger")
    for pos, (_, bar) in enumerate(bars.iterrows()):
        o, h, l = (float(bar[k]) for k in ("Open", "High", "Low"))
        if not all(np.isfinite(x) and x > 0 for x in (o, h, l)) or l > min(o, h) or h < max(o, l):
            continue
        if "breakout buy-stop" in style and trigger is not None:
            trig = float(trigger)
            if o > chase:
                # Do not chase a gap above the allowed price; a later bar may set up again.
                continue
            if o >= trig:
                fill = o  # stop order gaps: fill at the opening price, not the trigger
                if fill <= chase:
                    return pos, fill, "breakout_gap_fill"
            elif h >= trig:
                return pos, trig, "breakout_trigger_fill"
        else:
            # Resting buy limit: a gap down fills at the open, otherwise at the limit.
            if o < lo:
                continue  # gap below the planned zone; avoid treating a falling knife as a fill
            if o <= entry and o >= lo:
                return pos, o, "limit_gap_fill"
            if l <= entry <= hi:
                return pos, entry, "limit_fill"
    return None, None, "no_fill_in_window"


def run_backtest(data: dict[str, pd.DataFrame], hourly: dict[str, pd.DataFrame] | None = None,
                 cost: float = 0.005) -> pd.DataFrame:
    """Walk-forward weekly simulation with explicit breakout-stop / limit entry fills.

    Features and plans are built only from bars before Monday. Entry orders are then
    simulated over the following week. OHLC-only bars cannot reconstruct intrabar
    order exactly; ambiguous stop/target bars are resolved conservatively. `cost`
    is the estimated all-in round-trip friction as a fraction of position value.
    """
    if not np.isfinite(cost) or cost < 0 or cost >= 1:
        raise ValueError("cost must be a finite fraction in [0, 1)")
    rows = []
    for t, df in data.items():
        df = df.dropna(subset=["Open", "High", "Low", "Close"]).sort_index()
        idx = df.index
        hdf = (hourly or {}).get(t)
        for i in range(70, len(df) - 1):
            if idx[i].weekday() != 0:
                continue
            history = df.iloc[:i]
            f = compute_features(history, live=False)
            if not f:
                continue
            plan = trade_plan(f)
            bars = week_bars(df, i, hdf)
            if len(bars) < 3 or bars.index[-1].weekday() < 3:
                continue
            liquid, _ = liquidity_gate(f)
            sc, _ = tech_score(f)
            fill_pos, entry, fill_reason = find_entry_fill(bars, plan) if plan["ok"] else (None, None, "plan_rejected")
            if entry is None or fill_pos is None:
                rows.append({"ticker": t, "date": idx[i], "ret": 0.0, "gross_ret": 0.0,
                             "cost_pct": cost, "why": fill_reason, "hit": False, "score": sc,
                             "entry": np.nan, "plan_entry": plan["entry"], "buy_lo": plan["buy_lo"],
                             "buy_hi": plan["buy_hi"], "stop_pct": plan["stop_pct"],
                             "fill_type": fill_reason, "filled": False, "tradable": False, "liquid": bool(liquid)})
                continue
            # Start at the fill bar. If stop and target are both inside the entry bar,
            # the simulator takes the conservative stop-first outcome.
            exit_bars = bars.iloc[fill_pos:]
            stop = entry * (1 - plan["stop_pct"])
            ret, why, hit = simulate_trade(exit_bars, entry, entry * (1 + TARGET_1),
                                           entry * (1 + TARGET_2), stop)
            rows.append({"ticker": t, "date": idx[i], "ret": ret - cost, "gross_ret": ret,
                         "cost_pct": cost, "why": why, "hit": hit, "score": sc,
                         "entry": entry, "plan_entry": plan["entry"], "buy_lo": plan["buy_lo"],
                         "buy_hi": plan["buy_hi"], "stop_pct": plan["stop_pct"],
                         "fill_type": fill_reason, "filled": True,
                         "tradable": bool(liquid and plan["ok"]), "liquid": bool(liquid)})
    return pd.DataFrame(rows)


def _stats(df: pd.DataFrame) -> dict:
    if df.empty:
        return {}
    # Candidate rows without a simulated fill are not trades and must not dilute returns.
    if "filled" in df.columns:
        df = df[df["filled"].astype(bool)]
    if df.empty:
        return {}
    r = df["ret"]
    gw, gl = r[r > 0].sum(), -r[r < 0].sum()
    wins, losses = r[r > 0], r[r < 0]
    return {"trades": len(r), "win%": (r > 0).mean() * 100, "t1%": df["hit"].mean() * 100,
            "stop%": (df["why"] == "stop").mean() * 100, "avg%": r.mean() * 100,
            "median%": r.median() * 100, "worst%": r.min() * 100,
            "best%": r.max() * 100, "avg_win%": wins.mean() * 100 if len(wins) else 0.0,
            "avg_loss%": losses.mean() * 100 if len(losses) else 0.0,
            "expectancy_dollars_per_1000": r.mean() * 1000,
            "pf": gw / gl if gl > 0 else (float("inf") if gw > 0 else 0.0)}


def edge_verdict(res: pd.DataFrame) -> dict:
    """Judge the validated tier (tradable + tech score >= threshold) on OUT-OF-SAMPLE weeks only."""
    if res.empty:
        return {"ok": False, "text": "no backtest data"}
    cut = res["date"].quantile(1 - OOS_FRACTION)
    base = res[(res["date"] >= cut) & res["tradable"]]
    oos = base[base["score"] >= EDGE_TECH_THRESHOLD]
    s, b = _stats(oos), _stats(base)
    if not s or s["trades"] < EDGE_MIN_TRADES:
        n = s.get("trades", 0) if s else 0
        return {"ok": False, "text": f"INSUFFICIENT DATA: only {n} out-of-sample trades at tech>={EDGE_TECH_THRESHOLD} "
                                     f"(need {EDGE_MIN_TRADES}). Treat picks as a watch-list, not signals."}
    # Trades in the same week are correlated (market-wide moves), so test on WEEKLY average returns.
    wk = oos.groupby("date")["ret"].mean()
    t_stat = wk.mean() / (wk.std(ddof=1) / np.sqrt(len(wk))) if len(wk) > 2 and wk.std(ddof=1) > 0 else 0.0
    if not b:
        return {"ok": False, "text": "NO VALID BASELINE: no tradable out-of-sample trades; treat picks as a watch-list."}
    beats_base = s["avg%"] > b["avg%"]
    ok = s["avg%"] > 0 and s["pf"] >= EDGE_MIN_PF and beats_base and t_stat >= 1.65 and len(wk) >= 8
    txt = (f"out-of-sample, tech>={EDGE_TECH_THRESHOLD}: {s['trades']} trades over {len(wk)} weeks, "
           f"win {s['win%']:.0f}%, +5% hit {s['t1%']:.0f}%, avg {s['avg%']:+.2f}% (all tradable: {b['avg%']:+.2f}%), "
           f"PF {s['pf']:.2f}, t-stat {t_stat:.1f}")
    if ok:
        return {"ok": True, "text": "EDGE FOUND (still not a guarantee): " + txt}
    why = []
    if not beats_base:
        why.append("score filter doesn't beat the unfiltered tradable baseline")
    if len(wk) < 8:
        why.append("too few independent weeks for a meaningful statistical check")
    if t_stat < 1.65:
        why.append("not statistically distinguishable from luck")
    if s["avg%"] <= 0 or s["pf"] < EDGE_MIN_PF:
        why.append("expectancy too thin after costs")
    return {"ok": False, "text": "NO PROVEN EDGE (" + "; ".join(why) + "): " + txt}


def edge_check(data: dict[str, pd.DataFrame], force: bool = False) -> dict:
    today = datetime.now().strftime("%Y-%m-%d")
    c = STATE.get("edge") or {}
    if not force and c.get("date") == today:
        return c["verdict"]
    print("Running validation backtest on your watchlist (cached for the day)...")
    v = edge_verdict(run_backtest(data))
    STATE["edge"] = {"date": today, "verdict": v}
    _save_state(STATE)
    return v


def print_backtest(res: pd.DataFrame, hourly: bool) -> None:
    if res.empty:
        print("No trades generated (not enough data?).")
        return
    print(f"\nExit simulation: {'HOURLY bars' if hourly else 'DAILY bars (stop assumed first if both hit in a day)'}"
          f"; scale-out 50% at +{TARGET_1:.0%}, stop to breakeven, Wed time-stop, Fri exit.")
    cut = res["date"].quantile(1 - OOS_FRACTION)
    for label, part in (("ALL HISTORY", res), ("IN-SAMPLE (older)", res[res["date"] < cut]),
                        ("OUT-OF-SAMPLE (newest, the one that matters)", res[res["date"] >= cut])):
        if part.empty:
            continue
        print(f"\n== {label}: {part['date'].min():%Y-%m-%d} to {part['date'].max():%Y-%m-%d} ==")
        if "filled" in part.columns:
            print(f"Candidates: {len(part)} | simulated fills: {int(part['filled'].sum())} | no-fill/rejected: {int((~part['filled']).sum())}")
        print(f"{'Strategy':<34}{'Trades':>7}{'Win%':>7}{'+5%':>6}{'Stop%':>7}{'Avg%':>7}{'Med%':>7}{'Worst%':>8}{'PF':>6}")
        executed = part[part["filled"].astype(bool)] if "filled" in part.columns else part
        tiers = [("Executed entries (all)", executed), ("Tradable (volume+plan)", executed[executed["tradable"]])]
        tiers += [(f"Tradable + tech >= {th}", part[part["tradable"] & (part["score"] >= th)]) for th in (40, 50, 60, 70)]
        for name, d in tiers:
            s = _stats(d)
            if not s:
                print(f"{name:<34}{'0':>7}")
                continue
            print(f"{name:<34}{s['trades']:>7}{s['win%']:>7.1f}{s['t1%']:>6.0f}{s['stop%']:>7.1f}"
                  f"{s['avg%']:>7.2f}{s['median%']:>7.2f}{s['worst%']:>8.1f}{s['pf']:>6.2f}")
    v = edge_verdict(res)
    print(f"\nVERDICT: {v['text']}")
    filled = res[res["filled"].astype(bool)] if "filled" in res.columns else res
    if not filled.empty:
        print("\nSCORE BUCKET DIAGNOSTIC (executed trades only; not a calibrated probability model)")
        for lo, hi in ((0, 40), (40, 50), (50, 60), (60, 70), (70, 101)):
            group = filled[(filled["score"] >= lo) & (filled["score"] < hi)]
            st = _stats(group)
            if st:
                print(f"  score {lo:>3}-{hi-1:<3}: n={st['trades']:<4} win={st['win%']:>5.1f}% "
                      f"avg={st['avg%']:>+6.2f}% PF={st['pf']:.2f}")
        print("\nYEARLY EXECUTED-TRADE SUMMARY (overlapping ticker trades are not a portfolio equity curve)")
        filled = filled.copy()
        filled["year"] = pd.to_datetime(filled["date"]).dt.year
        for year, group in filled.groupby("year"):
            st = _stats(group)
            print(f"  {year}: n={st['trades']:<4} win={st['win%']:>5.1f}% avg={st['avg%']:>+6.2f}% "
                  f"worst={st['worst%']:>+6.2f}% PF={st['pf']:.2f}")
    print("Caveats: entries now simulate breakout buy-stops and resting limit orders from OHLC bars, but "
          "intrabar order remains ambiguous and no queue/partial-fill model is available. Cost is a flat "
          "all-in friction deduction per executed trade (set --cost accordingly); gaps can exceed stops. "
          "The current watchlist may have survivorship bias and omit delisted names. Use `grade` + `scorecard` "
          "for prospective forward validation; paper-trade before risking capital.")


# =============================== JOURNAL (FORWARD TEST) =======================

JOURNAL_COLS = ["monday", "logged", "ticker", "total", "tech", "ext", "news_net", "rumor", "social_pts",
                "insider", "rvol", "touch_rate", "entry", "chase", "stop_pct", "style",
                "ret", "outcome", "hit_t1", "graded"]


def _journal_path() -> Path:
    STATE_DIR.mkdir(exist_ok=True)
    return STATE_DIR / "journal.csv"


def log_picks(picks: list[dict]) -> None:
    """Snapshot each pick WITH its news/social/insider signals so they can be graded after Friday."""
    p, monday = _journal_path(), f"{target_monday():%Y-%m-%d}"
    old = pd.read_csv(p, dtype=str, keep_default_na=False) if p.exists() else pd.DataFrame(columns=JOURNAL_COLS)
    have = set(zip(old["monday"], old["ticker"]))
    rows = []
    for r in picks:
        if (monday, r["ticker"]) in have:
            continue
        f, pl, n = r["f"], r["plan"], r.get("news") or {}
        rows.append({"monday": monday, "logged": datetime.now().isoformat(timespec="minutes"),
                     "ticker": r["ticker"], "total": round(r["total"], 1), "tech": round(r["tech"], 1),
                     "ext": round(r.get("ext", 0), 1), "news_net": round(n.get("net", 0), 1),
                     "rumor": int(bool(n.get("rumors"))), "social_pts": r.get("social_pts", 0),
                     "insider": int(bool((r.get("filings") or {}).get("insider_buy"))),
                     "rvol": round(f["rvol"], 2), "touch_rate": round(f["touch_rate"], 2),
                     "entry": pl["entry"], "chase": pl["chase"], "stop_pct": round(pl["stop_pct"], 4),
                     "style": pl["style"][:12], "ret": "", "outcome": "", "hit_t1": "", "graded": ""})
    if rows:
        pd.concat([old, pd.DataFrame(rows)], ignore_index=True).to_csv(p, index=False)
        print(f"Journal: logged {len(rows)} picks for week of {monday}.")


def grade_journal() -> None:
    p = _journal_path()
    if not p.exists():
        print("No journal yet. Run `screen` or `picks` first (picks are logged automatically).")
        return
    df = pd.read_csv(p, dtype=str, keep_default_na=False)
    today = datetime.now(ET_TZ).date()
    pend = df[(df["graded"] != "yes") & (pd.to_datetime(df["monday"]).dt.date + timedelta(days=4) < today)]
    if pend.empty:
        print("Nothing to grade yet (picks are graded after their Friday has passed).")
        return
    data = fetch_daily(sorted(pend["ticker"].unique()), "6mo")
    n = 0
    for i, r in pend.iterrows():
        d = data.get(r["ticker"])
        if d is None:
            continue
        m = pd.to_datetime(r["monday"])
        bars = d[(d.index.tz_localize(None) if d.index.tz is not None else d.index) >= m]
        bars = bars[(bars.index.tz_localize(None) if bars.index.tz is not None else bars.index) <= m + timedelta(days=4)]
        if bars.empty or bars.index[0].weekday() != 0:
            continue
        o = float(bars["Open"].iloc[0])
        sp = float(r["stop_pct"])
        if o > float(r["chase"]):
            df.loc[i, ["ret", "outcome", "hit_t1", "graded"]] = ["0", "skipped_gap_up", "0", "yes"]
        else:
            ret, why, hit = simulate_trade(bars, o, o * (1 + TARGET_1), o * (1 + TARGET_2), o * (1 - sp))
            df.loc[i, ["ret", "outcome", "hit_t1", "graded"]] = [f"{ret - 0.005:.5f}", why, str(int(hit)), "yes"]
        n += 1
    df.to_csv(p, index=False)
    print(f"Graded {n} picks.")


def scorecard() -> None:
    p = _journal_path()
    if not p.exists():
        print("No journal yet.")
        return
    df = pd.read_csv(p, dtype=str, keep_default_na=False)
    g = df[(df["graded"] == "yes") & (df["outcome"] != "skipped_gap_up")].copy()
    if g.empty:
        print("No graded trades yet. Let a full week pass, then run `grade`.")
        return
    for c in ("ret", "total", "tech", "news_net", "rumor", "social_pts", "insider", "hit_t1"):
        g[c] = pd.to_numeric(g[c], errors="coerce")

    def line(name, d):
        if d.empty:
            return f"{name:<30}{'0':>6}"
        r = d["ret"]
        gl = -r[r < 0].sum()
        pf = r[r > 0].sum() / gl if gl > 0 else float("inf")
        return f"{name:<30}{len(d):>6}{(r > 0).mean() * 100:>8.0f}{d['hit_t1'].mean() * 100:>7.0f}{r.mean() * 100:>8.2f}{pf:>7.2f}"

    print(f"\n{'Group':<30}{'Trades':>6}{'Win%':>8}{'+5%':>7}{'Avg%':>8}{'PF':>7}")
    print(line("ALL logged picks", g))
    for name, mask in [("Catalyst news (net>=3)", g["news_net"] >= 3), ("No catalyst news", g["news_net"] < 3),
                       ("Social buzz/sentiment", g["social_pts"] > 0), ("No social signal", g["social_pts"] == 0),
                       ("Insider buying", g["insider"] == 1), ("Rumor chatter", g["rumor"] == 1),
                       ("Total score >= 65", g["total"] >= 65), ("Total score 50-65", (g["total"] >= 50) & (g["total"] < 65)),
                       ("Total score < 50", g["total"] < 50)]:
        print(line(name, g[mask]))
    print("\nA signal is only worth its points if its group beats the 'without' group over 30+ trades.")
    print("Re-weight tech_score()/enrich() accordingly.")


# =============================== TRADE SCREEN =================================


def edge_banner(v: dict | None) -> str:
    if not v:
        return "Edge check skipped."
    return ("✅ " if v["ok"] else "⚠️  ") + v["text"]


def recommendation(r: dict, verdict: dict | None = None) -> tuple[str, str]:
    """Conservative classification; never emits a trade-ready label on stale/invalid inputs."""
    blocked = r.get("blocked")
    score, tech = float(r.get("total", 0)), float(r.get("tech", 0))
    plan = r.get("plan") or {}
    size = plan.get("size") or {}
    status = str(r.get("status", "UNKNOWN")).upper()
    if blocked:
        return "PASS", str(blocked)
    if not plan.get("ok", False) or int(size.get("shares", 0)) < 1:
        return "PASS", "risk/reward or position sizing fails the configured rules"
    if status == "SKIP":
        return "PASS", r.get("status_txt", "price is outside the acceptable entry conditions")
    if status in ("STALE", "UNKNOWN", "") or str(r.get("now_src", "last close")).startswith("last close"):
        return "WATCH ONLY", "no sufficiently current quote; verify price and spread before considering an order"
    if verdict is None or not verdict.get("ok", False):
        if score >= 60 and tech >= EDGE_TECH_THRESHOLD:
            return "WATCH ONLY", "the strategy has no proven out-of-sample edge yet"
        return "PASS / WATCHLIST", "validation has not established an edge"
    if status != "BUY":
        if score >= 60:
            return "WATCH", "setup is not currently inside the planned entry conditions"
        return "PASS", "score below the bot's watch threshold"
    if score >= 75 and tech >= EDGE_TECH_THRESHOLD:
        return "POTENTIAL SETUP", "historical validation passed; independently verify quote, spread, news and order fill"
    if score >= 60:
        return "WATCH", "wait for stronger confirmation; do not chase"
    return "PASS", "score below the bot's watch threshold"


def ticket_lines(rank: int, r: dict, width: int = 78, verdict: dict | None = None) -> list[str]:
    f, p, sz = r["f"], r["plan"], r["plan"]["size"]
    star = "★" if r["tech"] >= EDGE_TECH_THRESHOLD else " "
    rec, rec_why = recommendation(r, verdict)
    L = ["═" * width,
         f"#{rank} {r['ticker']}  [{market_side(r['ticker'])} · {market_currency(r['ticker'])}]  recommendation: {rec} — {rec_why}",
         f"score {r['total']:.0f}{star} (tech {r['tech']:.0f} + catalysts "
         f"{r.get('ext', 0):+.0f})   now ${px(r.get('now', f['price']))}   vol {f['last_vol']:,.0f} ({f['rvol']:.1f}x)",
         "─ BUY-IN " + "─" * (width - 9),
         f"  Right now  : ${px(r.get('now', f['price']))} ({r.get('now_src', 'last close')}) -> "
         f"{r.get('status', '')}: {r.get('status_txt', '')}",
         "  When       : Mon 9:45-10:30 ET (skip the first 15 min); use limit orders, not market",
         f"  Setup      : {p['style']}"]
    if p["trigger"]:
        L.append(f"  Trigger    : buy-stop ${px(p['trigger'])}")
    L += [f"  Buy zone   : ${px(p['buy_lo'])} - ${px(p['buy_hi'])}   (aim ~${px(p['entry'])})",
          f"  Skip if    : opens above ${px(p['chase'])} (chasing) or below ${px(p['stop'])} (stop level)",
          f"  Size       : {sz['shares']:,} sh = ${sz['cost']:,.0f}  (risk ${sz['risk']:,.0f}; "
          f"limited by {sz['limit']}; account ${ACCOUNT_SIZE:,.0f})",
          "─ SELL-OUT " + "─" * (width - 11),
          f"  Stop       : ${px(p['stop'])} (-{p['stop_pct']:.1%}); after +5% hits, raise to breakeven ${px(p['entry'])}",
          f"  Target 1   : ${px(p['t1'])} (+{TARGET_1:.0%})  sell HALF",
          f"  Target 2   : ${px(p['t2'])} (+{TARGET_2:.0%})  sell the rest, or trail ${px(p['trail'])} below the high",
          f"  Time stops : Wed close: exit if still under +{TIME_STOP_MIN_GAIN:.0%} | Fri 3:45pm ET: exit everything",
          f"  Odds/risk  : reward:risk {p['rr1']:.2f} to T1, {p['rr2']:.2f} to T2 | last 6 months: +5% touched in "
          f"{f['touch_rate']:.0%} of weeks, -5% in {f['stop_rate']:.0%}"]
    for w in (r["why"] + r.get("ext_why", []))[:5]:
        L.append(f"  • {w}")
    for x in (r.get("news") or {}).get("top", [])[:2]:
        tag = "RUMOR" if x["rumor"] else x["direction"]
        L.append(f"  📰 [{tag}] {x['title'][:100]}")
    return L


def render_terminal(picks: list[dict], verdict: dict | None) -> str:
    out = [f"\nTRADE SCREEN  -  week of {target_monday():%a %b %d}  -  {datetime.now():%H:%M}",
           edge_banner(verdict), "TOP 20 PER MARKET, ranked independently. Screening guidance only; skip rather than chase.", ""]
    hdr = f"{'#':<3}{'Ticker':<10}{'Market':<13}{'Rec':<18}{'Score':>6}{'Now':>10}{'Status':>8}{'Buy zone':>20}{'Stop':>10}{'T1 (+5%)':>10}{'T2 (+10%)':>11}{'Shares':>8}{'$ Risk':>8}"
    for group, prefix in (("USA 🇺🇸", "USA"), ("CANADA 🇨🇦", "CANADA")):
        subset = [r for r in picks if market_side(r["ticker"]).startswith(prefix)]
        out += [f"\n{'=' * 18} {group} — {len(subset)} stocks {'=' * 18}", hdr, "-" * len(hdr)]
        for i, r in enumerate(subset, 1):
            plan = r["plan"]
            rec, _ = recommendation(r, verdict)
            out.append(f"{i:<3}{r['ticker']:<10}{market_side(r['ticker']):<13}{rec:<18}{r['total']:>6.0f}{px(r.get('now', r['f']['price'])):>10}{r.get('status', ''):>8}{'$' + px(plan['buy_lo']) + '-' + px(plan['buy_hi']):>20}"
                       f"{px(plan['stop']):>10}{px(plan['t1']):>10}{px(plan['t2']):>11}{plan['size']['shares']:>8,}{plan['size']['risk']:>8,.0f}")
        for i, r in enumerate(subset, 1):
            out += [""] + ticket_lines(i, r, verdict=verdict)
    out.append("\nNot financial advice. Verify prices and news yourself before trading.")
    return "\n".join(out)


HTML_CSS = """
:root{--bg:#f6f7f9;--card:#fff;--text:#1b1f24;--muted:#667085;--line:#e4e7ec;--buy:#067647;--buybg:#ecfdf3;--sell:#b42318;--sellbg:#fef3f2;--warn:#b54708;--warnbg:#fffaeb;--ok:#067647;--okbg:#ecfdf3}
:root:not([data-theme="light"]){color-scheme:light dark}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#0f1216;--card:#171b21;--text:#e8eaed;--muted:#98a2b3;--line:#2a313b;--buy:#4ade80;--buybg:#10281b;--sell:#f87171;--sellbg:#2d1616;--warn:#fbbf24;--warnbg:#2b2210;--ok:#4ade80;--okbg:#10281b}}
:root{box-sizing:border-box;padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}
*,*:before,*:after{box-sizing:inherit}
body{margin:0;background:var(--bg);color:var(--text);font:15px/1.45 system-ui,-apple-system,Segoe UI,Roboto,sans-serif;padding:16px}
h1{font-size:24px;margin:0 0 4px;letter-spacing:-.02em}.sub{color:var(--muted);margin-bottom:12px}
body{background:linear-gradient(180deg,#101827 0,#111827 220px,var(--bg) 220px);color:var(--text)}
h1{color:#f8fafc}.sub{color:#b8c5d6}.market-title{margin:24px 0 10px;padding:10px 12px;border-left:4px solid #60a5fa;background:#1e293b;color:#f8fafc;border-radius:6px}
a{color:#60a5fa}.pill{display:inline-block;padding:2px 8px;border-radius:999px;font-weight:700;font-size:12px;background:#263548;color:#cbd5e1}.mom-hot{background:#153d2b;color:#86efac}.mom-warm{background:#493a14;color:#fde68a}.mom-cold{background:#4a2025;color:#fca5a5}
.banner{padding:10px 12px;border-radius:8px;margin:10px 0;border:1px solid var(--line)}
.banner.ok{background:var(--okbg);color:var(--ok)}.banner.warn{background:var(--warnbg);color:var(--warn)}.news-alert{background:#3b160d;color:#ffcfb8;border:2px solid #ff6b35;box-shadow:0 0 12px #ff6b3544}.news-alert-chip{display:inline-block;margin:4px;padding:4px 7px;border-radius:6px;background:#7c2d12;color:#fff7ed;font-weight:800}.news-new{background:#ff1744;color:white;border-radius:4px;padding:2px 4px}.news-none{background:var(--card);color:var(--muted)}
.wrap{overflow-x:auto;margin-bottom:16px}
table{border-collapse:collapse;width:100%;min-width:640px;background:var(--card);border:1px solid var(--line);border-radius:8px}
th,td{padding:8px 10px;text-align:right;border-bottom:1px solid var(--line);white-space:nowrap}
th:first-child,td:first-child,th:nth-child(2),td:nth-child(2){text-align:left}
th{color:var(--muted);font-weight:600;font-size:12px;text-transform:uppercase}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(330px,1fr));gap:14px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px}
.card h2{margin:0 0 2px;font-size:17px}.meta{color:var(--muted);font-size:13px;margin-bottom:10px}
.sec{border-radius:8px;padding:8px 10px;margin-bottom:8px}
.sec h3{margin:0 0 6px;font-size:12px;text-transform:uppercase;letter-spacing:.05em}
.buy{background:var(--buybg)}.buy h3{color:var(--buy)}.sell{background:var(--sellbg)}.sell h3{color:var(--sell)}
.r{display:flex;justify-content:space-between;gap:10px;padding:2px 0}.r span{color:var(--muted)}.r b{text-align:right}
.why{color:var(--muted);font-size:13px;margin:6px 0 0;padding-left:18px}
.portfolio{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px;margin:14px 0 20px;box-shadow:0 5px 18px rgba(0,0,0,.08)}.portfolio h2{margin:0 0 4px}.formgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(125px,1fr));gap:8px;margin:12px 0}.portfolio input,.portfolio select,.portfolio button{font:inherit;padding:8px;border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--text);min-width:0;width:100%}.portfolio button{cursor:pointer;font-weight:700;background:#1d4ed8;color:#fff;border-color:#1d4ed8}.portfolio button.secondary{background:var(--bg);color:var(--text);border-color:var(--line)}.p-status{display:inline-block;border-radius:5px;padding:3px 6px;font-weight:800;font-size:12px}.p-hold{background:var(--okbg);color:var(--ok)}.p-sell{background:var(--sellbg);color:var(--sell)}.p-watch{background:var(--warnbg);color:var(--warn)}.pnl-positive{color:var(--ok);font-weight:800}.pnl-negative{color:var(--sell);font-weight:800}.smallnote{font-size:12px;color:var(--muted)}.company-name{display:inline-block;color:var(--muted);font-size:12px;white-space:normal;max-width:220px}.position-actions{display:flex;gap:6px;min-width:150px}.position-actions button{width:auto;padding:5px 8px}.fees{display:flex;gap:16px;flex-wrap:wrap;margin:8px 0;color:var(--muted);font-size:13px}
.foot{color:var(--muted);font-size:12px;margin-top:16px}
.s-buy{color:var(--buy);font-weight:700;background:var(--buybg)}.s-skip{color:var(--sell);font-weight:700;background:var(--sellbg)}.s-wait,.s-watch{color:var(--warn);font-weight:700;background:var(--warnbg)}
tr:hover{background:rgba(96,165,250,.08)}.card{box-shadow:0 5px 18px rgba(0,0,0,.08)}.card h2{color:var(--text)}
"""


def news_score_alert_banner() -> str:
    """Dashboard banner for positive news scores above +3, including recent threshold crossings."""
    alerts = STATE.get("news_score_alerts", {})
    active = []
    now = datetime.now(ET_TZ)
    for ticker, item in alerts.items():
        try:
            score = float(item.get("score", 0))
        except (TypeError, ValueError, AttributeError):
            continue
        if score <= 3:
            continue
        badge = ""
        crossed = item.get("crossed_at")
        if crossed:
            try:
                stamp = datetime.fromisoformat(crossed)
                if stamp.tzinfo is None:
                    stamp = stamp.replace(tzinfo=ET_TZ)
                if (now - stamp).total_seconds() <= 6 * 3600:
                    badge = " <strong class='news-new'>NEW &gt; +3</strong>"
            except (TypeError, ValueError):
                pass
        active.append((score, ticker, badge))
    active.sort(reverse=True)
    if not active:
        return "<div class='banner news-none'><b>News threshold watch:</b> no cached positive news scores currently above +3/10. This is not proof that no news exists; data coverage may be incomplete.</div>"
    items = " ".join(f"<span class='news-alert-chip'>{html.escape(ticker)} {score:+.1f}/10{badge}</span>" for score, ticker, badge in active[:20])
    extra = f" <span class='smallnote'>+{len(active)-20} more</span>" if len(active) > 20 else ""
    return "<div class='banner news-alert'><b>🚨 NEWS SCORE ABOVE +3/10 — REVIEW:</b> " + items + extra + " <a href='news_watch.html'>Open News Watch</a><div class='smallnote'>Scores are directional research flags, not trade instructions. Verify the headline and current quote.</div></div>"


def refresh_existing_trade_screen_alert() -> None:
    """Refresh only the alert slot in an already-generated trade screen after each news cycle."""
    screen = Path(HTML_SCREEN)
    if not screen.exists():
        return
    try:
        doc = screen.read_text(encoding="utf-8")
        start_tag, end_tag = "<!-- NEWS_SCORE_ALERT_START -->", "<!-- NEWS_SCORE_ALERT_END -->"
        slot = start_tag + news_score_alert_banner() + end_tag
        if start_tag in doc and end_tag in doc:
            start = doc.index(start_tag)
            end = doc.index(end_tag, start) + len(end_tag)
            updated = doc[:start] + slot + doc[end:]
        elif "<h1>Trade Screen</h1>" in doc:
            updated = doc.replace("<h1>Trade Screen</h1>", "<h1>Trade Screen</h1>" + slot, 1)
        else:
            return
        if updated != doc:
            screen.write_text(updated, encoding="utf-8")
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"Could not refresh trade-screen news alert: {type(exc).__name__}: {exc}", flush=True)


def render_html(picks: list[dict], verdict: dict | None, path: str = HTML_SCREEN) -> str:
    e = html.escape

    def row(label, val):
        return f"<div class='r'><span>{e(label)}</span><b>{e(str(val))}</b></div>"

    def volume_badge(rvol):
        try:
            rv = max(0.0, float(rvol))
        except (TypeError, ValueError):
            rv = 0.0
        delta = rv - 1.0
        if rv >= 1.5:
            bg, fg, label = "#064e3b", "#a7f3d0", "HIGH VOLUME"
        elif rv >= 1.0:
            bg, fg, label = "#1e3a8a", "#bfdbfe", "ABOVE AVG" if rv > 1.02 else "AVERAGE"
        elif rv >= 0.7:
            bg, fg, label = "#713f12", "#fde68a", "BELOW AVG"
        else:
            bg, fg, label = "#7f1d1d", "#fecaca", "LOW VOLUME"
        delta_text = f"+{delta:.1f}×" if delta >= 0 else f"−{abs(delta):.1f}×"
        return f"<span title='Relative volume compared with average daily volume' style='display:inline-block;padding:4px 7px;border-radius:6px;background:{bg};color:{fg};font-weight:800;white-space:nowrap'>{rv:.1f}× avg ({delta_text})<br><small style='color:{fg};font-weight:600'>{label}</small></span>"

    # Read the latest generated momentum rows and render them inline above the USA market.
    # This keeps the main trade screen as the single dashboard; the separate page remains available.
    momentum_section = ""
    try:
        momentum_path = Path("early_momentum.html")
        if momentum_path.exists():
            momentum_doc = momentum_path.read_text(encoding="utf-8", errors="replace")
            momentum_match = re.search(r"<tbody>(.*?)</tbody>", momentum_doc, flags=re.S | re.I)
            momentum_rows_html = momentum_match.group(1).strip() if momentum_match else ""
            # Do not copy the scanner's empty-state placeholder into the alert table.
            if "No qualifying intraday movers found" in momentum_rows_html:
                momentum_rows_html = ""
            momentum_section = (
                "<section id='early-momentum' class='momentum-inline'>"
                "<h2 class='market-title'>🚨 EARLY MOMENTUM ALERTS — LIVE DISCOVERY</h2>"
                "<div class='sub'>Price moves and unusual same-time volume. These are discovery alerts, not automatic buy signals. "
                "Daily RVOL in the market tables is different from same-time intraday RVOL here.</div>"
                "<div class='banner warn'>Strong price move does not necessarily mean volume confirms the breakout. Check quote freshness, spread, news and risk before trading.</div>"
                "<div class='wrap'><table><thead><tr><th>Ticker / Market</th><th>Alert</th><th>Move</th><th>Last</th>"
                "<th>Same-time RVOL</th><th>Session volume</th><th>Last bar</th><th>Headline check</th></tr></thead><tbody>"
                + (momentum_rows_html or "<tr><td colspan='8'>No momentum rows available yet. The section will populate after a successful intraday scan.</td></tr>")
                + "</tbody></table></div>"
                "<p><a href='early_momentum.html'>Open full Early Momentum Scanner</a></p></section>"
            )
    except Exception as momentum_render_exc:
        momentum_section = (
            "<section id='early-momentum' class='momentum-inline'>"
            "<h2 class='market-title'>🚨 EARLY MOMENTUM ALERTS — LIVE DISCOVERY</h2>"
            "<div class='banner warn'>Momentum results are temporarily unavailable. The scanner may not have completed a successful run.</div>"
            "<p><a href='early_momentum.html'>Open Early Momentum Scanner</a></p></section>"
        )

    banner_cls = "ok" if (verdict and verdict["ok"]) else "warn"
    trs, cards = {"USA": [], "CANADA": []}, {"USA": [], "CANADA": []}
    ranks = {"USA": 0, "CANADA": 0}
    for r in picks:
        group = "CANADA" if market_side(r["ticker"]).startswith("CANADA") else "USA"
        ranks[group] += 1
        i = ranks[group]
        f, p, sz = r["f"], r["plan"], r["plan"]["size"]
        star = " ★" if r["tech"] >= EDGE_TECH_THRESHOLD else ""
        rec, rec_why = recommendation(r, verdict)
        cname = company_name(r["ticker"]) or r["ticker"]
        trs[group].append(f"<tr><td>{i}</td><td><b>{e(r['ticker'])}{star}</b><br><small class='company-name'>{e(cname)}</small></td><td>{e(market_side(r['ticker']))}</td><td>{e(rec)}</td><td>{e(r.get('setup', 'WATCH'))}</td><td>{r['total']:.0f}</td>"
                   f"<td>${px(r.get('now', f['price']))}</td><td>{volume_badge(f.get('rvol', 0))}</td><td class='s-{r.get('status', 'watch').lower()}'>{r.get('status', '')}</td>"
                   f"<td><span class='pill {'mom-hot' if r.get('momentum',50)>=65 else 'mom-cold' if r.get('momentum',50)<=40 else 'mom-warm'}'>{r.get('momentum',50):.0f}/100</span></td>"
                   f"<td>${px(p['buy_lo'])} - {px(p['buy_hi'])}</td><td>${px(p['stop'])}</td>"
                   f"<td>${px(p['t1'])}</td><td>${px(p['t2'])}</td><td>{sz['shares']:,}</td><td>${sz['risk']:,.0f}</td></tr>")
        buy = [row("Right now", f"${px(r.get('now', f['price']))} ({r.get('now_src', 'last close')}): {r.get('status', '')}"),
               row("When", "Mon 9:45-10:30 ET, limit orders"), row("Setup", f"{r.get('setup', 'WATCH')} — {p['style'].split(' (')[0]}")]
        if p["trigger"]:
            buy.append(row("Trigger", f"buy-stop ${px(p['trigger'])}"))
        buy += [row("Buy zone", f"${px(p['buy_lo'])} - ${px(p['buy_hi'])}"),
                row("Skip if", f"opens > ${px(p['chase'])} or < ${px(p['stop'])}"),
                row("Size", f"{sz['shares']:,} sh = ${sz['cost']:,.0f}"),
                row("Max loss", f"${sz['risk']:,.0f} (limited by {sz['limit']})")]
        sell = [row("Stop", f"${px(p['stop'])} (-{p['stop_pct']:.1%})"),
                row("After +5%", f"sell half; stop to ${px(p['entry'])}"),
                row("Target 1", f"${px(p['t1'])} (+{TARGET_1:.0%})"),
                row("Target 2", f"${px(p['t2'])} (+{TARGET_2:.0%}) or trail ${px(p['trail'])}"),
                row("Wed close", f"exit if under +{TIME_STOP_MIN_GAIN:.0%}"),
                row("Fri 3:45pm ET", "exit everything"),
                row("Reward:risk", f"{p['rr1']:.2f} (T1) / {p['rr2']:.2f} (T2)")]
        why = "".join(f"<li>{e(w)}</li>" for w in (r["why"] + r.get("ext_why", []))[:5])
        news = "".join(f"<li>[{'RUMOR' if x['rumor'] else e(x['direction'])}] {e(x['title'][:100])}</li>"
                       for x in (r.get("news") or {}).get("top", [])[:2])
        cards[group].append(
            f"<div class='card'><h2>#{i} {e(r['ticker'])}{star} — {e(market_side(r['ticker']))} — {e(rec)}</h2>"
            f"<div class='company-name'>{e(cname)}</div><div class='meta'>{e(rec_why)} · {market_currency(r['ticker'])} quotes · score {r['total']:.0f} · now ${px(r.get('now', f['price']))} · latest volume {f['last_vol']:,.0f} "
            f"· +5% touched {f['touch_rate']:.0%} of recent weeks</div>"
            f"<div class='sec'><h3>Technical confirmation</h3>{row('Setup', r.get('setup', 'WATCH'))}{row('RSI (14)', f"{f.get('rsi', 0):.0f}")}{row('MACD', 'positive / strengthening' if f.get('macd_hist', 0) > 0 and f.get('macd_hist_rising') else 'mixed / caution')}{row('Price vs 20d SMA', f"{f.get('pullback_dist', 0):+.1%}")}{row('Trend structure', 'higher highs + higher lows' if f.get('trend_structure') else 'mixed')}</div>"
            f"<div class='sec'><h3>Volume score</h3>{row('Relative to 20-day average', f'{f.get("rvol", 0):.1f}× average ({f.get("rvol", 0)-1:+.1f}× vs average)')}{row('Average daily shares', f'{f.get("avg_vol", 0):,.0f}')}{row('Latest / estimated daily shares', f'{f.get("last_vol", 0):,.0f}')}</div>"
            f"<div class='sec'><h3>News & social momentum</h3>{row('Momentum score', f"{r.get('momentum', 50):.0f}/100 — {'strong' if r.get('momentum',50)>=65 else 'weak' if r.get('momentum',50)<=40 else 'mixed'}")}{row('Social contribution', f"{r.get('social_pts',0):.0f} points")}</div>"
            f"<div class='sec buy'><h3>Buy-in</h3>{''.join(buy)}</div>"
            f"<div class='sec sell'><h3>Sell-out</h3>{''.join(sell)}</div>"
            f"<ul class='why'>{why}{news}</ul></div>")
    penny_trs = {"USA": [], "CANADA": []}
    penny_ranks = {"USA": 0, "CANADA": 0}
    for r in LAST_PENNY_ROWS:
        group = "CANADA" if market_side(r["ticker"]).startswith("CANADA") else "USA"
        penny_ranks[group] += 1
        f, p = r["f"], r["plan"]
        mom = float(r.get("momentum", 50))
        risk_flag = "WIDE SPREAD / VOLATILITY CHECK" if p.get("stop_pct", 0) > 0.07 else ("LOW RELATIVE VOLUME" if f.get("rvol", 0) < 2 else "")
        catalyst = "; ".join(str(x.get("title", ""))[:75] for x in (r.get("news") or {}).get("top", [])[:1]) or "No headline catalyst found"
        penny_name = company_name(r["ticker"]) or r["ticker"]
        penny_trs[group].append(
            f"<tr><td>{penny_ranks[group]}</td><td><b>{e(r['ticker'])}</b><br><small class='company-name'>{e(penny_name)}</small></td><td>{e(market_side(r['ticker']))}</td>"
            f"<td>${px(r.get('now', f['price']))}</td><td>{volume_badge(f.get('rvol', 0))}</td>"
            f"<td><span class='pill {'mom-hot' if mom >= 65 else 'mom-cold' if mom <= 40 else 'mom-warm'}'>{mom:.0f}/100</span></td>"
            f"<td>${px(p['buy_lo'])}–${px(p['buy_hi'])}</td><td>${px(p['stop'])}</td>"
            f"<td>${px(p['entry'] * 1.05)}</td><td>${px(p['entry'] * 1.10)}</td>"
            f"<td>{e(risk_flag or 'Check current spread')}</td><td title='{e(catalyst)}'>{e(catalyst[:78])}</td></tr>"
        )
    penny_html = "<h2 class='market-title'>🚨 PENNY STOCK MOMENTUM WATCHLIST</h2><div class='sub'>Separate speculative watchlist · US under $5 / Canada under C$2 · candidates must pass the program's existing price-history, liquidity and trade-plan filters. Verify live spread and order-book depth before trading.</div>"
    for key, label in (("USA", "🇺🇸 U.S. Penny Stocks (under US$5)"), ("CANADA", "🇨🇦 Canadian Penny Stocks (under C$2)")):
        penny_html += f"<h3>{label} — Top {len(penny_trs[key])}</h3>"
        if not penny_trs[key]:
            penny_html += "<div class='banner warn'>No penny-stock candidates passed the current filters in the active watchlist.</div>"
        else:
            penny_html += "<div class='wrap'><table><thead><tr><th>#</th><th>Ticker</th><th>Market</th><th>Now</th><th>Volume vs Avg.</th><th>News/Social Mom.</th><th>Buy zone</th><th>Stop</th><th>+5% target</th><th>+10% target</th><th>Risk check</th><th>Latest headline</th></tr></thead><tbody>" + "".join(penny_trs[key]) + "</tbody></table></div>"

    # Inject all technically eligible watchlist rows, not just Top 20 picks. This lets
    # browser-held positions still display price/relative-volume data when not ranked in Top 20.
    # Live intraday quotes exist only for rows passed through attach_live(); otherwise label
    # the value explicitly as last close, never as a live quote.
    screen_prices = {}
    _portfolio_rows = list(LAST_SCREEN_ROWS) + list(picks) + list(LAST_PENNY_ROWS)
    for _r in _portfolio_rows:
        _ticker = str(_r.get("ticker", "")).upper()
        _price = float(_r.get("now", _r.get("f", {}).get("price", 0)) or 0)
        if _ticker and _price > 0:
            _f = _r.get("f", {}) or {}
            screen_prices[_ticker] = {
                "price": _price, "currency": market_currency(_ticker),
                "source": str(_r.get("now_src", "last close (not a current quote)")),
                "status": str(_r.get("status", "STALE")),
                "momentum": float(_r.get("momentum", 0) or 0),
                "rvol": float(_f.get("rvol", 0) or 0),
                "roc10": float(_f.get("roc10", 0) or 0),
                "above_sma20": bool(_f.get("above_sma20", False)),
                "sma20_gt_sma50": bool(_f.get("sma20_gt_sma50", False)),
                "signal_available": bool(_f),
            }
    prices_json = json.dumps(screen_prices, separators=(",", ":")).replace("</", r"<\/")
    portfolio_html = """<section class='portfolio' id='portfolio'>
      <h2>📌 MY OPEN POSITIONS — PURCHASE PRICE & SELL MONITOR</h2>
      <div class='sub'>Holdings are saved in this browser. Price/volume data is now injected for all technically eligible watchlist symbols, not just Top 20. If the feed fails, the page clearly labels last close versus a live bar; enter a manual price when no usable data is available. Keep holdings in watchlist.txt.</div>
      <div class='formgrid'>
        <input id='pTicker' placeholder='Ticker (e.g. CNQ.TO)' aria-label='Ticker' maxlength='24'>
        <input id='pShares' type='number' min='0.000001' step='any' placeholder='Shares / units' aria-label='Shares'>
        <input id='pBuy' type='number' min='0.000001' step='any' placeholder='Purchase price' aria-label='Purchase price'>
        <select id='pCurrency' aria-label='Currency'><option value='AUTO'>Auto currency</option><option value='CAD'>CAD</option><option value='USD'>USD</option></select>
        <input id='pDate' type='date' aria-label='Purchase date' title='Purchase date'>
        <input id='pCurrent' type='number' min='0' step='any' placeholder='Current price (optional)' aria-label='Manual current price'>
        <button id='pAdd' type='button'>Add position</button>
      </div>
      <div class='fees'><span><b>Commission:</b> C$6.50 per buy or sell order</span><span><b>Round-trip estimate:</b> C$13.00 per position</span><label>USD per C$1 <input id='pFx' type='number' min='0.01' max='2' step='0.001' value='0.72' style='width:82px;display:inline-block;padding:4px' title='Used to convert CAD commissions into USD for USD holdings'></label></div>
      <div class='smallnote'>Net P/L estimates deduct the C$6.50 buy commission plus one estimated C$6.50 sell commission; each additional partial-sale order adds another C$6.50. USD holdings convert commissions using the editable FX estimate above. Taxes, FX fees, and other costs are excluded. Stop and targets are editable planning alerts, not broker orders. Momentum-extension advice appears only when a holding has a current screen signal with strong relative volume and positive trend; missing signals are not treated as bullish.</div>
      <div id='pSummary' class='banner'>No positions added yet.</div>
      <div class='wrap'><table id='pTable'><thead><tr><th>Ticker</th><th>Currency</th><th>Purchase date</th><th>Shares</th><th>Purchase price</th><th>Current price</th><th>Volume vs avg.</th><th>Stop alert</th><th>Target 1</th><th>Target 2</th><th>Gross P/L</th><th>Est. net P/L after fees</th><th>Net return</th><th>Sell monitor</th><th>Momentum / target advice</th><th>Actions</th></tr></thead><tbody id='pRows'><tr><td colspan='16'>Add a position above to start monitoring.</td></tr></tbody></table></div>
      <div id='pClosedWrap' style='display:none'><h3>Closed positions</h3><div class='wrap'><table><thead><tr><th>Ticker</th><th>Shares</th><th>Buy</th><th>Sell</th><th>Estimated realized net P/L</th><th>Date closed</th></tr></thead><tbody id='pClosedRows'></tbody></table></div><button type='button' class='secondary' id='pClearClosed'>Clear closed history</button></div>
    </section>"""
    portfolio_js = r"""<script>
    const SCREEN_PRICES = __SCREEN_PRICES__;
    const PORT_KEY = 'swingBotOpenPositionsV1'; const CLOSED_KEY = 'swingBotClosedPositionsV1';
    const $ = id => document.getElementById(id);
    const num = v => Number.isFinite(Number(v)) ? Number(v) : 0;
    const money = (v,c) => (c === 'USD' ? 'US$' : 'C$') + num(v).toLocaleString(undefined,{minimumFractionDigits:2,maximumFractionDigits:2});
    const volumeLabel = rv => {if(rv===undefined||rv===null||!Number.isFinite(Number(rv))||Number(rv)<=0)return '<span class="p-status p-watch">No volume data</span>';rv=Number(rv);const d=rv-1,delta=(d>=0?'+':'−')+Math.abs(d).toFixed(1)+'×';const cls=rv>=1.5?'p-hold':rv<0.7?'p-sell':'p-watch';const label=rv>=1.5?'HIGH':rv>1.02?'ABOVE AVG':rv>=0.98?'AVERAGE':rv>=0.7?'BELOW AVG':'LOW';return '<span class="p-status '+cls+'">'+rv.toFixed(1)+'× avg ('+delta+')<br>'+label+'</span>';};
    const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
    const load = key => { try { return JSON.parse(localStorage.getItem(key) || '[]'); } catch(e) { return []; } };
    const save = (key, v) => localStorage.setItem(key, JSON.stringify(v));
    const autoCurrency = t => /\.(TO|V|CN|NE|TSXV|TSX|CVE|NEO)$/i.test(t) ? 'CAD' : 'USD';
    function fx(){const v=num($('pFx').value);return v>0&&v<2?v:0.72;}
    function livePrice(p){const hit=SCREEN_PRICES[p.ticker.toUpperCase()];if(hit && hit.price>0)return {price:num(hit.price),source:hit.source||'screen data',metrics:hit};if(num(p.manualPrice)>0)return {price:num(p.manualPrice),source:'manual quote'};return {price:0,source:'no quote'};}
    function calc(p){const q=livePrice(p), c=p.currency, shares=num(p.shares), buy=num(p.buy), fee=c==='CAD'?13:13*fx();const gross=q.price>0?(q.price-buy)*shares:null;const net=gross===null?null:gross-fee;const invested=buy*shares+(c==='CAD'?6.5:6.5*fx());let status='WAIT — NEED PRICE', cls='p-watch';if(q.price>0){if(num(p.stop)>0&&q.price<=num(p.stop)){status='SELL ALERT — STOP';cls='p-sell';}else if(num(p.target2)>0&&q.price>=num(p.target2)){status='TARGET 2 HIT — REVIEW EXIT';cls='p-sell';}else if(num(p.target1)>0&&q.price>=num(p.target1)){status='TARGET 1 HIT — REVIEW PARTIAL SELL';cls='p-watch';}else{status='HOLD / MONITOR';cls='p-hold';}}const m=q.metrics||{};let advice='No current trend signal for this holding; keep the existing plan and verify the quote.', adviceClass='p-watch';if(m.signal_available&&m.momentum>=65&&m.rvol>=1.5&&m.roc10>=0.03&&m.above_sma20&&m.sma20_gt_sma50){adviceClass='p-hold';if(q.price>0&&num(p.target1)>0&&q.price>=num(p.target1)*0.985){advice='STRONG TREND + '+m.rvol.toFixed(1)+'× volume: consider extending target 2 from +10% to +12% of entry; take partial profit at target 1 and trail the remainder about 2.5% below the recent high. Do not widen the stop.';}else{advice='Momentum/volume strong ('+m.rvol.toFixed(1)+'× volume); hold to current plan for now. Reassess target extension near target 1.';}}else if(m.signal_available){adviceClass='p-watch';advice='No extension trigger: momentum/volume trend is not strong enough. Follow the original targets and stop.';}return {q,gross,net,ret:net===null||!invested?null:net/invested,fee,status,cls,advice,adviceClass};}
    function render(){const positions=load(PORT_KEY), rows=$('pRows');let grossCAD=0,netCAD=0,grossUSD=0,netUSD=0,hasCAD=false,hasUSD=false;rows.innerHTML='';if(!positions.length)rows.innerHTML='<tr><td colspan="16">No open positions. Add one above after a purchase.</td></tr>';positions.forEach((p,i)=>{const x=calc(p);if(x.gross!==null){if(p.currency==='CAD'){grossCAD+=x.gross;hasCAD=true;}else{grossUSD+=x.gross;hasUSD=true;}}if(x.net!==null){if(p.currency==='CAD')netCAD+=x.net;else netUSD+=x.net;}const tr=document.createElement('tr');tr.innerHTML=`<td><b>${esc(p.ticker)}</b><div class="smallnote">${esc(x.q.source)}</div></td><td>${esc(p.currency)}</td><td>${esc(p.date||'—')}</td><td>${num(p.shares).toLocaleString()}</td><td>${money(p.buy,p.currency)}</td><td>${x.q.price>0?money(x.q.price,p.currency):'<span class="p-status p-watch">Enter quote</span>'}<input aria-label="Manual current price for ${esc(p.ticker)}" data-field="manualPrice" data-i="${i}" type="number" min="0" step="any" value="${num(p.manualPrice)||''}" placeholder="manual quote" style="width:100px;margin-top:4px"></td><td>${volumeLabel(x.q.metrics?.rvol)}</td><td><input data-field="stop" data-i="${i}" type="number" min="0" step="any" value="${num(p.stop)||''}" style="width:90px" aria-label="Stop for ${esc(p.ticker)}"></td><td><input data-field="target1" data-i="${i}" type="number" min="0" step="any" value="${num(p.target1)||''}" style="width:90px" aria-label="Target one for ${esc(p.ticker)}"></td><td><input data-field="target2" data-i="${i}" type="number" min="0" step="any" value="${num(p.target2)||''}" style="width:90px" aria-label="Target two for ${esc(p.ticker)}"></td><td class="${x.gross===null?'':x.gross>=0?'pnl-positive':'pnl-negative'}">${x.gross===null?'—':money(x.gross,p.currency)}</td><td class="${x.net===null?'':x.net>=0?'pnl-positive':'pnl-negative'}">${x.net===null?'—':money(x.net,p.currency)}<div class="smallnote">Includes estimated ${money(x.fee,p.currency)} round-trip fees</div></td><td>${x.ret===null?'—':(x.ret*100).toFixed(2)+'%'}</td><td><span class="p-status ${x.cls}">${esc(x.status)}</span></td><td><span class="p-status ${x.adviceClass}">${esc(x.advice)}</span></td><td><div class="position-actions"><button type="button" data-sell="${i}" class="secondary">Mark sold</button><button type="button" data-remove="${i}" class="secondary">Remove</button></div></td>`;rows.appendChild(tr);});const negative=(hasCAD&&netCAD<0)||(hasUSD&&netUSD<0);$('pSummary').textContent=`Open positions: ${positions.length} · Gross P/L: ${hasCAD?money(grossCAD,'CAD')+' CAD':''}${hasCAD&&hasUSD?' / ':''}${hasUSD?money(grossUSD,'USD')+' USD':''} · Estimated net after fees: ${hasCAD?money(netCAD,'CAD')+' CAD':''}${hasCAD&&hasUSD?' / ':''}${hasUSD?money(netUSD,'USD')+' USD':''}${!hasCAD&&!hasUSD?'awaiting quotes':''}.`;if(positions.length===0)$('pSummary').className='banner';else $('pSummary').className='banner '+(negative?'warn':'ok');const closed=load(CLOSED_KEY);$('pClosedWrap').style.display=closed.length?'block':'none';$('pClosedRows').innerHTML=closed.map(p=>`<tr><td>${esc(p.ticker)}</td><td>${num(p.shares).toLocaleString()}</td><td>${money(p.buy,p.currency)}</td><td>${money(p.sell,p.currency)}</td><td class="${num(p.net)>=0?'pnl-positive':'pnl-negative'}">${money(p.net,p.currency)}</td><td>${esc(p.closedDate||'')}</td></tr>`).join('');}
    $('pAdd').addEventListener('click',()=>{const ticker=$('pTicker').value.trim().toUpperCase(),shares=num($('pShares').value),buy=num($('pBuy').value);if(!ticker||shares<=0||buy<=0){alert('Enter a ticker, positive share count, and purchase price.');return;}const currency=$('pCurrency').value==='AUTO'?autoCurrency(ticker):$('pCurrency').value;const manualPrice=num($('pCurrent').value);const positions=load(PORT_KEY);positions.push({id:Date.now().toString(36)+Math.random().toString(36).slice(2,6),ticker,shares,buy,currency,date:$('pDate').value||new Date().toISOString().slice(0,10),manualPrice,stop:buy*0.95,target1:buy*1.05,target2:buy*1.10});save(PORT_KEY,positions);$('pTicker').value='';$('pShares').value='';$('pBuy').value='';$('pCurrent').value='';render();});
    $('pRows').addEventListener('change',ev=>{const el=ev.target;if(!el.dataset.field)return;const positions=load(PORT_KEY),i=num(el.dataset.i);if(!positions[i])return;positions[i][el.dataset.field]=num(el.value);save(PORT_KEY,positions);render();});
    $('pRows').addEventListener('click',ev=>{const sell=ev.target.dataset.sell,remove=ev.target.dataset.remove;if(sell!==undefined){const positions=load(PORT_KEY),p=positions[num(sell)];if(!p)return;const x=calc(p);if(x.q.price<=0){alert('No current price is available. Enter a manual current price first.');return;}const fee=p.currency==='CAD'?13:13*fx();const net=(x.q.price-num(p.buy))*num(p.shares)-fee;const closed=load(CLOSED_KEY);closed.unshift({...p,sell:x.q.price,net,closedDate:new Date().toISOString().slice(0,10)});save(CLOSED_KEY,closed);positions.splice(num(sell),1);save(PORT_KEY,positions);render();}else if(remove!==undefined){if(!confirm('Remove this position without recording a sale?'))return;const positions=load(PORT_KEY);positions.splice(num(remove),1);save(PORT_KEY,positions);render();}});
    $('pFx').addEventListener('change',render);$('pClearClosed').addEventListener('click',()=>{if(confirm('Clear all closed-position history?')){save(CLOSED_KEY,[]);render();}});
    $('pDate').value=new Date().toISOString().slice(0,10);render();
    </script>""".replace("__SCREEN_PRICES__", prices_json)
    doc = ("<!doctype html><html lang='en'><head><meta charset='utf-8'>"
           "<meta name='viewport' content='width=device-width, initial-scale=1, viewport-fit=cover'>"
           "<meta http-equiv='refresh' content='" + str(HTML_REFRESH_SEC) + "'><title>Trade Screen</title>"
           "<style>" + HTML_CSS + "</style></head><body>"
           f"<h1>Trade Screen</h1><p><a href='early_momentum.html'>🚨 Early Momentum Scanner</a> · <a href='news_watch.html'>News Watch</a></p><div class='sub'>Week of {target_monday():%a %b %d} · generated {datetime.now():%a %H:%M} "
           f"· account ${ACCOUNT_SIZE:,.0f}, risk {RISK_PCT:.0%}/trade · <a href='options_watch.html'>Open Options Watch</a></div>"
           f"<div class='banner {banner_cls}'>{e(edge_banner(verdict))}</div>"
           + "<!-- NEWS_SCORE_ALERT_START -->" + news_score_alert_banner() + "<!-- NEWS_SCORE_ALERT_END -->"
           + portfolio_html
           + momentum_section
           + "".join(
               f"<h2>{label} — Top {len(trs[key])} stocks</h2>"
               + ("" if trs[key] else "<div class='banner warn'>No qualifying stocks found for this market. Check the active watchlist, ticker suffixes, data feed, and liquidity filters.</div>")
               + "<div class='wrap'><table><thead><tr><th>#</th><th>Ticker</th><th>Market</th><th>Recommendation</th><th>Setup</th><th>Score</th><th>Now</th><th>Volume vs Avg.</th><th>Status</th><th>News/Social Mom.</th><th>Buy zone</th><th>Stop</th><th>Primary +5%</th><th>Stretch +10%</th><th>Shares</th><th>Risk</th></tr></thead><tbody>" + "".join(trs[key]) + "</tbody></table></div><div class='grid'>" + "".join(cards[key]) + "</div>"
               for key, label in (("USA", "🇺🇸 USA MARKET"), ("CANADA", "🇨🇦 CANADIAN MARKET"))
           )
           + penny_html
           + portfolio_js
           + "<div class='foot'>Market indicator is inferred from ticker suffix: .TO/.V/.CN/.NE = Canada (CAD); other symbols = USA (USD). Verify exchange and quote currency before ordering. ★ = meets the validated technical threshold. If a stock opens above its "
           "'skip' level, pass; don't chase. News/social momentum is descriptive, based on available headline and public-post signals; it is not independently validated and rumours do not receive a positive bonus. Options Watch is a separate research page and may have incomplete/delayed data. Recommendation labels are conservative screen classifications, not personalized financial advice or validated buy signals.</div></body></html>")
    Path(path).write_text(doc, encoding="utf-8")
    return path


# =============================== PICKS / SCREEN ===============================


def live_prices(tickers: list[str]) -> dict[str, tuple[float, str]]:
    """Latest Yahoo 1m bar available; it may be delayed and includes pre/post-market.
    It is not a guaranteed real-time executable quote."""
    out: dict[str, tuple[float, str]] = {}
    if not tickers:
        return out
    try:
        import yfinance as yf
        raw = yf.download(tickers, period="1d", interval="1m", group_by="ticker",
                          progress=False, prepost=True, threads=True)
        for t in tickers:
            try:
                d = raw[t] if isinstance(raw.columns, pd.MultiIndex) else raw
                c = d["Close"].dropna()
                if not c.empty:
                    ts = c.index[-1]
                    out[t] = (float(c.iloc[-1]), ts.isoformat())
            except (KeyError, ValueError):
                pass
    except Exception as e:
        print(f"  live price lookup failed ({e}); showing last daily close instead")
    return out


def price_status(price: float, plan: dict) -> tuple[str, str]:
    """Where is the current price relative to the planned buy-in? Returns (short code, explanation)."""
    lo, hi, chase, stop, trig = plan["buy_lo"], plan["buy_hi"], plan["chase"], plan["stop"], plan["trigger"]
    if price <= stop:
        return "SKIP", f"below the stop level ${px(stop)}: setup broken"
    if price > chase:
        return "SKIP", f"{price / hi - 1:+.1%} above the zone, past the chase limit ${px(chase)}: don't chase"
    if trig and price < trig:
        return "WAIT", f"waiting for the trigger ${px(trig)} ({trig / price - 1:+.1%} away)"
    if price > hi:
        return "WAIT", f"{price / hi - 1:+.1%} above the zone: wait for a pullback to ${px(hi)}"
    if price >= lo:
        return "BUY", "inside the buy zone: OK to place your limit order"
    return "WATCH", f"{price / lo - 1:+.1%} below the zone: cheaper than planned, check why before buying"


def attach_live(picks: list[dict]) -> None:
    q = live_prices([r["ticker"] for r in picks])
    now = datetime.now(ET_TZ)
    session_open = market_is_open(now)
    for r in picks:
        if r["ticker"] in q:
            price, ts_text = q[r["ticker"]]
            r["now"], r["now_src"] = price, f"Yahoo 1m bar {ts_text}"
            try:
                ts = datetime.fromisoformat(ts_text)
                if ts.tzinfo is None:
                    ts = ts.replace(tzinfo=ET_TZ)
                age_minutes = (now - ts.astimezone(ET_TZ)).total_seconds() / 60
            except (TypeError, ValueError):
                age_minutes = float("inf")
            r["status"], r["status_txt"] = price_status(r["now"], r["plan"])
            if not session_open:
                r["status"], r["status_txt"] = "CLOSED", "regular market is closed; do not treat extended-hours pricing as an executable signal"
            elif age_minutes < -2 or age_minutes > 15:
                r["status"], r["status_txt"] = "STALE", f"latest Yahoo bar is {age_minutes:.0f} minutes old; verify a current executable quote"
        else:
            r["now"], r["now_src"] = r["f"]["price"], "last close (not a current quote)"
            r["status"], r["status_txt"] = "STALE", "last close only; obtain a current executable quote before any trade"


def run_picks(top=PICKS_TOP_N, use_llm=True, use_social=True, use_news=True,
              live=False, validate=True, split_markets=False) -> tuple[list[dict], dict | None]:
    wl = load_watchlist()
    us_count = sum(not t.endswith(CA_SUFFIXES) for t in wl)
    ca_count = len(wl) - us_count
    print(f"Scanning {len(wl)} tickers: {us_count} USA / {ca_count} Canadian candidates...")
    data = fetch_daily(wl, "2y" if validate else "1y")
    verdict = edge_check(data) if validate else (STATE.get("edge") or {}).get("verdict")
    rows = technical_pass(data, live)
    if split_markets:
        # Enrich the leading candidates on each market separately so US volume cannot crowd out Canada.
        candidates = []
        for prefix in ("USA", "CANADA"):
            candidates.extend([r for r in rows if market_side(r["ticker"]).startswith(prefix)][:max(ENRICH_TOP_N, top)])
        candidate_ids = {id(r) for r in candidates}
        for r in candidates:
            enrich(r, use_llm, use_social, use_news)
        for r in rows:
            if id(r) not in candidate_ids:
                r["total"], r["ext"], r["ext_why"] = r["tech"], 0.0, []
    else:
        for r in rows[:ENRICH_TOP_N]:
            enrich(r, use_llm, use_social, use_news)
        for r in rows[ENRICH_TOP_N:]:
            r["total"], r["ext"], r["ext_why"] = r["tech"], 0.0, []
    rows = [r for r in rows if not r.get("blocked")]
    rows.sort(key=lambda r: r["total"], reverse=True)
    # Build a distinct penny-stock shortlist from the same validated candidate pool.
    # Use stricter price buckets and keep it separate from the main-market Top 20.
    global LAST_PENNY_ROWS
    penny_candidates = []
    for r in rows:
        price = float(r.get("now", r["f"].get("price", 0)) or 0)
        is_canadian = market_side(r["ticker"]).startswith("CANADA")
        if price <= 0 or price >= (2.0 if is_canadian else 5.0):
            continue
        penny_candidates.append(r)
    # Enrich the best penny candidates not already enriched by the main screen.
    for prefix in ("USA", "CANADA"):
        subset = [r for r in penny_candidates if market_side(r["ticker"]).startswith(prefix)]
        for r in subset[:20]:
            if "momentum" not in r:
                enrich(r, use_llm, use_social, use_news)
    penny_candidates = [r for r in penny_candidates if not r.get("blocked")]
    penny_candidates.sort(key=lambda r: (float(r.get("momentum", 50)), float(r.get("total", r.get("tech", 0)))), reverse=True)
    LAST_PENNY_ROWS = []
    for prefix in ("USA", "CANADA"):
        LAST_PENNY_ROWS.extend([r for r in penny_candidates if market_side(r["ticker"]).startswith(prefix)][:20])
    attach_live(LAST_PENNY_ROWS)
    if split_markets:
        selected = []
        for prefix in ("USA", "CANADA"):
            selected.extend([r for r in rows if market_side(r["ticker"]).startswith(prefix)][:top])
    else:
        selected = rows[:top]
    attach_live(selected)
    # Build the portfolio quote/volume map from the ENTIRE downloaded watchlist,
    # independently of technical, liquidity, volatility, news, and Top-20 filters.
    # This lets browser-held positions keep showing their last known daily price and
    # historical volume metrics even when they are not trade-screen candidates.
    global LAST_SCREEN_ROWS
    all_watchlist_rows = []
    for _ticker, _df in data.items():
        try:
            _features = compute_features(_df, live=live)
            if not _features:
                continue
            all_watchlist_rows.append({
                "ticker": _ticker,
                "f": _features,
                "now": float(_features.get("price", 0) or 0),
                "now_src": "last daily close (not a current quote)",
                "status": "STALE",
                "momentum": float(_features.get("roc10", 0) or 0) * 100,
            })
        except Exception as _err:
            print(f"  Portfolio data skipped for {_ticker}: {_err}")
    # Keep ranked rows last so their better quote/status data overrides the daily fallback.
    LAST_SCREEN_ROWS = all_watchlist_rows + list(rows)
    return selected, verdict


# =============================== POSITIONS ====================================


def _pos_file() -> Path:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    return STATE_DIR / "positions.json"


def load_positions() -> list[dict]:
    f = _pos_file()
    return json.loads(f.read_text()) if f.exists() else []


def save_positions(p: list[dict]) -> None:
    _atomic_json_save(_pos_file(), p)


def add_position(ticker: str, entry: float, shares: int = 0) -> None:
    """Uses the same volatility-scaled plan as the screen (stop from ATR, +5/+10% targets)."""
    t = ticker.upper()
    plan = None
    d = fetch_daily([t], "1y").get(t)
    f = compute_features(d) if d is not None else None
    if f:
        plan = trade_plan(f, entry_override=entry)
    stop_pct = plan["stop_pct"] if plan else 0.05
    trail = plan["trail"] if plan else entry * 0.03
    ps = [p for p in load_positions() if p["ticker"] != t]
    ps.append({"ticker": t, "entry": entry, "shares": shares, "date": datetime.now(ET_TZ).strftime("%Y-%m-%d"),
               "t1": entry * (1 + TARGET_1), "t2": entry * (1 + TARGET_2), "stop": entry * (1 - stop_pct),
               "trail": trail, "be": False, "fired": []})
    save_positions(ps)
    print(f"Tracking {t} @ {entry}: stop {entry*(1-stop_pct):.4f} (-{stop_pct:.1%}), "
          f"T1 {entry*(1+TARGET_1):.4f}, T2 {entry*(1+TARGET_2):.4f}, trail {trail:.4f}")


def check_positions(now=None) -> None:
    ps = load_positions()
    if not ps:
        return
    now = now or datetime.now(ET_TZ)
    data = fetch_daily([p["ticker"] for p in ps], "3mo")
    mins = now.hour * 60 + now.minute
    for p in ps:
        df = data.get(p["ticker"])
        if df is None or df.empty:
            continue
        price = float(df["Close"].iloc[-1])
        later = df[df.index.strftime("%Y-%m-%d") > p["date"]]
        hi = max(price, float(later["High"].max())) if not later.empty else price
        lo = min(price, float(later["Low"].min())) if not later.empty else price
        pnl = price / p["entry"] - 1
        feat = compute_features(df) if len(df) >= 60 else None
        strong_trend = bool(feat and feat.get("rvol", 0) >= 1.5 and feat.get("roc10", 0) >= 0.03
                            and feat.get("above_sma20") and feat.get("sma20_gt_sma50"))

        def fire(tag: str, msg: str) -> bool:
            if tag in p["fired"]:
                return False
            p["fired"].append(tag)
            notify(msg)
            return True

        stop_tag = "be_stop" if p.get("be") else "stop"
        if lo <= p["stop"]:
            fire(stop_tag, f"🛑 {p['ticker']} hit {'BREAKEVEN ' if p.get('be') else ''}STOP "
                           f"${px(p['stop'])} (now ${px(price)}, {pnl:+.1%}). Exit the remaining position.")
        if hi >= p["t2"]:
            if strong_trend:
                fire("t2", f"🚀 {p['ticker']} reached the +10% target ${px(p['t2'])}; trend remains strong "
                             f"(relative volume {feat['rvol']:.1f}x, 10-day momentum {feat['roc10']:+.1%}). "
                             f"Rather than automatically selling the entire remainder, consider taking partial profit "
                             f"and extending the final target to about +12% of entry, while trailing the rest ~2.5% "
                             f"below the recent high. Do not widen the stop; reassess if volume/momentum fades.")
            else:
                fire("t2", f"🎯🎯 {p['ticker']} reached the +10% target ${px(p['t2'])} (now ${px(price)}, {pnl:+.1%}). "
                             f"Trend-extension criteria are not strong; consider selling the remainder per the original plan.")
        elif hi >= p["t1"]:
            if fire("t1", f"🎯 {p['ticker']} hit +5% ${px(p['t1'])} (now ${px(price)}, {pnl:+.1%}). "
                          f"SELL HALF and raise stop to breakeven ${px(p['entry'])}."):
                p["stop"], p["be"] = max(p["stop"], p["entry"]), True
        if "t1" in p["fired"] and hi - price >= p.get("trail", 0) > 0:
            fire("trail", f"📉 {p['ticker']} pulled back ${px(hi - price)} from its high ${px(hi)} "
                          f"(trail ${px(p['trail'])}). Consider selling the rest.")
        if now.weekday() == 2 and mins >= 15 * 60 + 30 and "t1" not in p["fired"] and pnl < TIME_STOP_MIN_GAIN:
            fire("wed", f"⏱ TIME-STOP: {p['ticker']} is {pnl:+.1%} on Wednesday with no +5% yet. "
                        f"Plan says exit.")
        if now.weekday() == 4 and mins >= 15 * 60 + 30:
            fire("fri", f"⏰ FRIDAY: {p['ticker']} at ${px(price)} ({pnl:+.1%}). Sell everything by 3:45pm ET.")
    save_positions(ps)


# =============================== MONITOR ======================================


def monday_picks_due(now: datetime) -> bool:
    return now.weekday() == 0 and now.hour >= 8 and STATE["last_picks_week"] != now.strftime("%G-W%V")


def run_news_watch_cycle(batch_size: int = 12, use_llm: bool = True, use_social: bool = True) -> None:
    """Continuously research headlines and public chatter, including outside market hours.

    This is deliberately a watch-for-open signal, not an executable buy/sell signal:
    after-hours and rumor-driven moves need fresh quotes, spread/liquidity checks, and
    confirmation during the next regular session.
    """
    tickers = load_watchlist()
    if not tickers:
        print("News watch: watchlist.txt is empty; add tickers before monitoring.", flush=True)
        return
    cursor = int(STATE.get("news_watch_cursor", 0)) % len(tickers)
    batch = [tickers[(cursor + i) % len(tickers)] for i in range(min(max(1, batch_size), len(tickers)))]
    STATE["news_watch_cursor"] = (cursor + len(batch)) % len(tickers)
    rows = []
    for ticker in batch:
        try:
            n = news_signal(ticker, use_llm=use_llm)
            rows.append({"ticker": ticker, "news": n, "social": 0.0, "social_why": []})
        except Exception as exc:
            print(f"News watch {ticker}: {type(exc).__name__}: {exc}", flush=True)
    # Track threshold crossings for user-visible notices on both dashboards.
    alert_state = STATE.setdefault("news_score_alerts", {})
    alert_now = datetime.now(ET_TZ).isoformat(timespec="seconds")
    for row in rows:
        ticker = row["ticker"]
        score = max(-10.0, min(10.0, float((row.get("news") or {}).get("net", 0))))
        previous = alert_state.get(ticker, {})
        try:
            previous_score = float(previous.get("score", 0))
        except (TypeError, ValueError, AttributeError):
            previous_score = 0.0
        crossed_at = previous.get("crossed_at")
        if score > 3 and previous_score <= 3:
            crossed_at = alert_now
            print(f"🚨 NEWS SCORE ALERT: {ticker} crossed above +3/10 to {score:+.1f}/10", flush=True)
        alert_state[ticker] = {"score": score, "updated_at": alert_now, "crossed_at": crossed_at}
    # Use the more expensive public-post checks only for the most news-active symbols.
    if use_social:
        social_candidates = sorted(rows, key=lambda r: abs(float((r.get("news") or {}).get("net", 0))), reverse=True)[:min(4, len(rows))]
        for row in social_candidates:
            try:
                pts, why = social_points(row["ticker"])
                row["social"], row["social_why"] = pts, why
            except Exception as exc:
                print(f"Social watch {row['ticker']}: {type(exc).__name__}: {exc}", flush=True)
    # Include previously cached symbols as well as this cycle's batch so the page is a
    # persistent rolling dashboard, not just the most recent batch.
    by_ticker = {r["ticker"]: r for r in rows}
    for ticker, cache in STATE.get("news", {}).items():
        if ticker not in by_ticker and cache:
            fresh = [x for x in cache if x.get("ts") and x.get("title")]
            if fresh:
                pos = max([_contrib(x) for x in fresh if _contrib(x) > 0], default=0.0)
                neg = min([_contrib(x) for x in fresh if _contrib(x) < 0], default=0.0)
                by_ticker[ticker] = {"ticker": ticker, "news": {"net": max(-10.0, min(10.0, pos + neg)),
                    "rumors": [x for x in fresh if x.get("rumor")],
                    "top": sorted(fresh, key=lambda x: abs(_contrib(x)), reverse=True)[:3], "new_count": 0},
                    "social": float(STATE.get("social_cache", {}).get(ticker, {}).get("pts", 0)),
                    "social_why": STATE.get("social_cache", {}).get(ticker, {}).get("why", [])}
    ranked = []
    for row in by_ticker.values():
        n = row.get("news") or {}
        net = float(n.get("net", 0))
        rumor = bool(n.get("rumors"))
        social = float(row.get("social", 0))
        if net >= 3 or (social >= 2 and net > 0):
            label, rationale = "WATCH FOR OPEN", "positive catalyst/chatter; confirm with fresh price and liquidity"
        elif net <= -3:
            label, rationale = "CAUTION", "negative catalyst risk; check filings and any dilution/news"
        elif rumor:
            label, rationale = "UNVERIFIED RUMOR", "do not trade on rumor alone; seek a primary source"
        elif social >= 2:
            label, rationale = "CHATTER WATCH", "public discussion elevated; not proof of a catalyst"
        else:
            label, rationale = "MONITOR", "no strong directional news signal detected"
        row.update({"label": label, "rationale": rationale, "signal_strength": abs(net) + social})
        ranked.append(row)
    ranked.sort(key=lambda r: (r["label"] not in ("WATCH FOR OPEN", "CAUTION", "UNVERIFIED RUMOR", "CHATTER WATCH"), -r["signal_strength"]))
    generated = datetime.now(ET_TZ).strftime("%Y-%m-%d %H:%M:%S ET")
    # Balance the visible feed across Canadian and US listings when both have results.
    # Rank remains signal-first within each market; alternate sides so one larger market
    # cannot crowd the other out of the 100-row dashboard.
    ca_ranked = [r for r in ranked if market_side(r["ticker"]).startswith("CANADA")]
    us_ranked = [r for r in ranked if not market_side(r["ticker"]).startswith("CANADA")]
    balanced = []
    for idx in range(max(len(ca_ranked), len(us_ranked))):
        # Start with US, then Canada; alternate whenever both sides have results.
        if idx < len(us_ranked): balanced.append(us_ranked[idx])
        if idx < len(ca_ranked): balanced.append(ca_ranked[idx])
    body = []
    for r in balanced[:100]:
        ticker = html.escape(r["ticker"])
        name = company_name(r["ticker"]) or r["ticker"]
        name_html = html.escape(name)
        n = r.get("news") or {}
        links = []
        for item in n.get("top", [])[:3]:
            title = html.escape(str(item.get("title", "")[:220]))
            url = html.escape(str(item.get("link", "")), quote=True)
            source = html.escape(str(item.get("source", "") or "source not identified"))
            tag = "RUMOR / UNVERIFIED" if item.get("rumor") else str(item.get("direction", "neutral")).upper()
            first_seen = html.escape(str(item.get("ts", ""))[:16].replace("T", " "))
            links.append(f'''<li><b>[{html.escape(tag)}]</b> <a href="{url}" target="_blank" rel="noopener">{title}</a> <small>({source}; first seen {first_seen})</small></li>''')
        social_text = ", ".join(r.get("social_why", [])) or ("No strong public-post signal" if not r.get("social") else f"social points {r['social']:.0f}")
        score = max(-10.0, min(10.0, float(n.get("net", 0))))
        magnitude = abs(score)
        if magnitude >= 7:
            score_class = "score-high-pos" if score > 0 else ("score-high-neg" if score < 0 else "score-low")
            row_class = "alert-positive" if score > 0 else ("alert-negative" if score < 0 else "")
        elif magnitude >= 4:
            score_class = "score-mid-pos" if score > 0 else ("score-mid-neg" if score < 0 else "score-mid")
            row_class = "watch-positive" if score > 0 else ("watch-negative" if score < 0 else "")
        else:
            score_class = "score-low-pos" if score > 0 else ("score-low-neg" if score < 0 else "score-low")
            row_class = ""
        if n.get("rumors"): row_class = (row_class + " rumor-row").strip()
        rumor_cell = "<b class='rumor-flag'>YES — VERIFY</b>" if n.get("rumors") else "No"
        is_canada = market_side(r["ticker"]).startswith("CANADA")
        market_class = "market-canada" if is_canada else "market-us"
        market_label = "🇨🇦 CANADA" if is_canada else "🇺🇸 USA"
        # Inline styles deliberately reinforce market colours so broad dashboard CSS
        # or positive/negative alert styles cannot hide the red/blue market indicator.
        market_style = ("border-left:6px solid #dc2626 !important;background-color:rgba(220,38,38,.13) !important;"
                        if is_canada else
                        "border-left:6px solid #2563eb !important;background-color:rgba(37,99,235,.13) !important;")
        tag_style = ("display:inline-block;color:#fecaca;background:#7f1d1d;border:1px solid #dc2626;"
                     if is_canada else
                     "display:inline-block;color:#bfdbfe;background:#1e40af;border:1px solid #2563eb;")
        body.append(f"<tr class='{row_class} {market_class}' data-market='{('CA' if is_canada else 'US')}'><td style='{market_style}'><b>{ticker}</b><br><small class='company-name'>{name_html}</small><br><span class='market-tag' style='{tag_style}padding:2px 6px;border-radius:4px;font-size:11px;font-weight:800'>{market_label}</span></td><td><b>{html.escape(r['label'])}</b><br><small>{html.escape(r['rationale'])}</small></td><td><span class='score-pill {score_class}'>{score:+.1f}/10</span></td><td>{rumor_cell}</td><td>{html.escape(social_text)}</td><td><ul>{''.join(links) or '<li>No recent headline cached</li>'}</ul></td></tr>")
    page = """<!doctype html><html><head><meta charset='utf-8'><meta http-equiv='refresh' content='60'><meta name='viewport' content='width=device-width,initial-scale=1'><title>After-Hours News & Rumor Watch</title><style>""" + HTML_CSS + """body{padding:18px}.market-canada td:first-child{border-left:5px solid #dc2626;background:rgba(220,38,38,.07)}.market-us td:first-child{border-left:5px solid #2563eb;background:rgba(37,99,235,.08)}.market-tag{display:inline-block;font-size:11px;font-weight:800;padding:2px 6px;border-radius:4px}.market-canada .market-tag{color:#fecaca;background:#7f1d1d}.market-us .market-tag{color:#bfdbfe;background:#1e40af}.company-name{display:inline-block;color:var(--muted);font-size:12px;white-space:normal;max-width:210px}.market-canada td,.market-us td{border-bottom:1px solid var(--line)}.wrap{width:100%;max-width:100%;overflow-x:hidden}table{width:100%;max-width:100%;table-layout:fixed;border-collapse:collapse}th,td{box-sizing:border-box;vertical-align:top;min-width:0!important;white-space:normal;overflow-wrap:anywhere;word-break:normal;padding:8px 6px}th:nth-child(1),td:nth-child(1){width:12%}th:nth-child(2),td:nth-child(2){width:18%}th:nth-child(3),td:nth-child(3){width:8%}th:nth-child(4),td:nth-child(4){width:8%}th:nth-child(5),td:nth-child(5){width:15%}th:nth-child(6),td:nth-child(6){width:39%}td:last-child{min-width:0!important;width:39%;text-align:left}td:last-child ul{margin:0;padding-left:18px;text-align:left}td:last-child li{margin:4px 0;padding-left:0;text-align:left}td:last-child a{display:inline;white-space:normal;overflow-wrap:anywhere}li{margin:4px 0}small{color:#94a3b8}.banner{margin:14px 0}.score-pill{display:inline-block;padding:5px 9px;border-radius:7px;font-weight:800;white-space:nowrap;border:1px solid transparent}.score-low{background:#263244;color:#d1d9e6;border-color:#475569}.score-low-pos{background:#123b35;color:#86efac;border-color:#22765e}.score-low-neg{background:#422027;color:#fda4af;border-color:#85404b}.score-mid{background:#5a3a0b;color:#fde68a;border-color:#b7791f}.score-mid-pos{background:#166534;color:#bbf7d0;border-color:#22c55e}.score-mid-neg{background:#7f1d1d;color:#fecaca;border-color:#ef4444}.score-high-pos{background:#00e676;color:#052e16;border-color:#b9ffd7;box-shadow:0 0 12px #00e67699;animation:pulse-green 1.4s infinite}.score-high-neg{background:#ff1744;color:#fff;border-color:#ffcdd2;box-shadow:0 0 14px #ff174499;animation:pulse-red 1.2s infinite}.alert-positive td{background:rgba(0,230,118,.08)}.alert-negative td{background:rgba(255,23,68,.10)}.rumor-row td:first-child{border-left:4px solid #facc15}.rumor-flag{color:#facc15;background:#422006;border:1px solid #eab308;border-radius:5px;padding:3px 5px;white-space:nowrap}@keyframes pulse-green{50%{box-shadow:0 0 20px #00e676dd}}@keyframes pulse-red{50%{box-shadow:0 0 22px #ff1744dd}}@media(prefers-reduced-motion:reduce){.score-high-pos,.score-high-neg{animation:none}}</style></head><body><h1>🌙 After-Hours News, Chatter & Rumor Watch</h1><div class='sub'>Generated """ + generated + """ · rotating scan of the active watchlist · refreshes every 2 minutes</div><div class='banner warn'><b>Important:</b> These are research/watch-for-open classifications, not buy/sell orders or validated predictions. Forum posts and rumors may be false or manipulated. Rumors never receive an automatic bullish recommendation. Verify the original source, official filings, next-session price, spread, volume and liquidity before considering a trade. Quotes may be stale while markets are closed.</div>" + news_score_alert_banner() + "<div class='wrap'><table><thead><tr><th>Ticker / Market</th><th>Research classification</th><th>News score</th><th>Rumor detected</th><th>Public chatter</th><th>Recent headlines / posts</th></tr></thead><tbody>""" + "".join(body) + """</tbody></table></div><p><a href='trade_screen.html'>Open regular trade screen</a> · <a href='early_momentum.html'>Early Momentum Scanner</a></p><div class='foot'>Sources are public RSS/news search and publicly accessible StockTwits/Reddit signals where available. Coverage is incomplete, source access can fail, and ticker-name ambiguity can produce false matches. A social signal means attention, not necessarily buying pressure.</div></body></html>"""
    Path("news_watch.html").write_text(page, encoding="utf-8")
    refresh_existing_trade_screen_alert()
    _save_state(STATE)
    print(f"[{generated}] After-hours news watch refreshed: {len(batch)} tickers scanned; dashboard: news_watch.html", flush=True)


def _momentum_symbols(max_universe: int = MOMENTUM_UNIVERSE_CAP) -> list[str]:
    """Use active watchlist plus a bounded sample from the broader discovered universe."""
    symbols = list(load_watchlist())
    universe_path = Path("market_universe.txt")
    if universe_path.exists() and max_universe > 0:
        try:
            extra = []
            for line in universe_path.read_text(encoding="utf-8").splitlines():
                t = line.split("#")[0].strip().upper()
                if t and t not in symbols:
                    extra.append(t)
            # Keep all active-watchlist symbols, then add extra names to broaden discovery.
            symbols.extend(extra[:max_universe])
        except OSError as exc:
            print(f"Momentum scanner: could not read {universe_path}: {exc}")
    return list(dict.fromkeys(symbols))


def fetch_intraday_momentum(tickers: list[str]) -> list[dict]:
    """Find session movers using 5-minute bars and time-of-day matched volume baselines."""
    try:
        import yfinance as yf
    except Exception as exc:
        raise RuntimeError("Early Momentum scanner requires yfinance: pip install yfinance") from exc

    now = datetime.now(ET_TZ)
    if not market_is_open(now):
        print("Early Momentum scanner: regular market is closed; waiting for next session.")
        return []
    results: list[dict] = []
    # Small batches avoid Yahoo's multi-symbol response becoming too large or fragile.
    for start in range(0, len(tickers), 20):
        chunk = tickers[start:start + 20]
        try:
            raw = yf.download(chunk, period="5d", interval=MOMENTUM_INTRADAY_INTERVAL,
                              group_by="ticker", progress=False, auto_adjust=True,
                              threads=True, prepost=False)
        except Exception as exc:
            print(f"Momentum intraday batch failed ({chunk[0]}…): {exc}")
            continue
        for ticker in chunk:
            try:
                d = raw[ticker] if isinstance(raw.columns, pd.MultiIndex) else raw
                d = d.dropna(subset=["Close", "Volume"]).copy()
                if d.empty:
                    continue
                idx = pd.to_datetime(d.index)
                if idx.tz is None:
                    idx = idx.tz_localize(ET_TZ)
                else:
                    idx = idx.tz_convert(ET_TZ)
                d.index = idx
                d = d[d.index.date <= now.date()]
                today = d[d.index.date == now.date()]
                prior_days = sorted({x.date() for x in d.index if x.date() < now.date()})
                if today.empty or not prior_days:
                    continue
                # Previous session close: last available bar from the most recent prior date.
                prev_date = prior_days[-1]
                prev = d[d.index.date == prev_date]
                prev_close = float(prev["Close"].iloc[-1])
                current_price = float(today["Close"].iloc[-1])
                if prev_close <= 0 or current_price <= 0:
                    continue
                move = current_price / prev_close - 1
                current_minutes = max(0, int((today.index[-1].hour * 60 + today.index[-1].minute) - (9 * 60 + 30)))
                # Compare cumulative volume through this same session minute on previous sessions.
                same_time_volumes = []
                for day in prior_days[-5:]:
                    hist = d[d.index.date == day]
                    if hist.empty:
                        continue
                    mins = (hist.index.hour * 60 + hist.index.minute) - (9 * 60 + 30)
                    cum = float(hist.loc[mins <= current_minutes, "Volume"].sum())
                    if cum > 0:
                        same_time_volumes.append(cum)
                current_cum_vol = float(today["Volume"].sum())
                baseline = float(np.median(same_time_volumes)) if same_time_volumes else 0.0
                rvol = current_cum_vol / baseline if baseline > 0 else 0.0
                # Do not flag ordinary low-volume noise. A price-move alert can still show
                # without RVOL, but the row explicitly says volume baseline unavailable.
                if move < MOMENTUM_MOVE_ALERT_PCT and rvol < MOMENTUM_RVOL_ALERT:
                    continue
                if move >= MOMENTUM_STRONG_MOVE_PCT:
                    level = "STRONG +5%" 
                elif move >= MOMENTUM_MOVE_ALERT_PCT and rvol >= MOMENTUM_RVOL_ALERT:
                    level = "EARLY +2% + RVOL"
                elif rvol >= MOMENTUM_RVOL_EXCEPTIONAL:
                    level = "EXCEPTIONAL RVOL 3x+"
                elif rvol >= MOMENTUM_RVOL_ALERT:
                    level = "UNUSUAL RVOL 2x+"
                else:
                    level = "MOVE WATCH"
                results.append({"ticker": ticker, "market": "CANADA" if ticker.upper().endswith(CA_SUFFIXES) else "USA",
                                "price": current_price, "prev_close": prev_close, "move": move,
                                "volume": current_cum_vol, "baseline": baseline, "rvol": rvol,
                                "level": level, "bar_time": today.index[-1].strftime("%H:%M ET")})
            except (KeyError, ValueError, TypeError, IndexError, AttributeError):
                continue
    results.sort(key=lambda r: (r["move"] >= MOMENTUM_STRONG_MOVE_PCT,
                                r["rvol"] >= MOMENTUM_RVOL_EXCEPTIONAL,
                                r["move"], r["rvol"]), reverse=True)
    return results


def run_momentum_scan(max_universe: int = MOMENTUM_UNIVERSE_CAP, use_news: bool = True,
                      send_alerts: bool = True) -> list[dict]:
    """Write early_momentum.html and alert on meaningful new price/volume/news events."""
    now = datetime.now(ET_TZ)
    symbols = _momentum_symbols(max_universe)
    print(f"Early Momentum scanner: checking {len(symbols)} tickers with 5-minute bars…", flush=True)
    rows = fetch_intraday_momentum(symbols)
    # Headlines are checked only for detected movers to avoid making hundreds of RSS calls.
    if use_news:
        for row in rows[:30]:
            try:
                n = news_signal(row["ticker"], use_llm=False)
                row["news"] = n
                row["headlines"] = [x.get("title", "") for x in (n or {}).get("top", [])[:2] if x.get("title")]
                row["news_score"] = float((n or {}).get("net", 0))
            except Exception as exc:
                row["news"] = None
                row["headlines"] = []
                row["news_score"] = 0.0
                print(f"Momentum news lookup failed for {row['ticker']}: {exc}")
    else:
        for row in rows:
            row["headlines"], row["news_score"] = [], 0.0

    # Persisted alert keys prevent the same ticker from notifying every 2-minute cycle.
    alert_state = STATE.setdefault("momentum_alerts", {})
    alert_lines = []
    for r in rows:
        news_hit = bool(r.get("headlines")) and abs(float(r.get("news_score", 0))) >= 3
        tier = "strong" if r["move"] >= MOMENTUM_STRONG_MOVE_PCT else (
            "early" if r["move"] >= MOMENTUM_MOVE_ALERT_PCT and r["rvol"] >= MOMENTUM_RVOL_ALERT else
            "volume" if r["rvol"] >= MOMENTUM_RVOL_ALERT else "watch")
        old = alert_state.get(r["ticker"], {})
        if not isinstance(old, dict):
            old = {}
        previous_date = str(old.get("date", ""))
        last_tier = old.get("tier", "") if previous_date == now.strftime("%Y-%m-%d") else ""
        tier_rank = {"watch": 0, "volume": 1, "early": 2, "strong": 3}
        key = f"{now:%Y-%m-%d}:{tier}"
        news_already_alerted_today = bool(old.get("news_hit", False)) if previous_date == now.strftime("%Y-%m-%d") else False
        new_event = (tier in ("strong", "early", "volume") and tier_rank.get(tier, 0) > tier_rank.get(last_tier, 0)) or (news_hit and not news_already_alerted_today)
        if send_alerts and new_event:
            headline = (f" | News score {r.get('news_score', 0):+.1f}: " + " / ".join(r.get("headlines", [])[:1])) if news_hit else ""
            alert_lines.append(f"{r['market']} {r['ticker']} {r['move']:+.1%}, same-time RVOL {r['rvol']:.1f}x, ${r['price']:.4g} — {r['level']}{headline}")
        alert_state[r["ticker"]] = {"tier": tier, "key": key, "date": now.strftime("%Y-%m-%d"),
                                    "news_hit": news_hit or (old.get("news_hit", False) if previous_date == now.strftime("%Y-%m-%d") else False),
                                    "updated": now.isoformat(timespec="seconds")}
    _save_state(STATE)

    body = []
    for r in rows[:100]:
        market_class = "market-canada" if r["market"] == "CANADA" else "market-us"
        headlines = "<br>".join(html.escape(x[:140]) for x in r.get("headlines", [])[:2]) or "No matching headline found"
        color = "#dc2626" if r["market"] == "CANADA" else "#2563eb"
        body.append(f"<tr class='{market_class}'><td style='border-left:6px solid {color}'><b>{html.escape(r['ticker'])}</b><br><small>{r['market']}</small></td>"
                    f"<td><b>{html.escape(r['level'])}</b></td><td>{r['move']:+.2%}</td><td>${r['price']:.4g}</td>"
                    f"<td>{r['rvol']:.2f}×</td><td>{r['volume']:,.0f}<br><small>same-time median {r['baseline']:,.0f}</small></td>"
                    f"<td>{html.escape(r['bar_time'])}</td><td>{headlines}</td></tr>")
    page = """<!doctype html><html><head><meta charset='utf-8'><meta http-equiv='refresh' content='60'><meta name='viewport' content='width=device-width,initial-scale=1'><title>Early Momentum Scanner</title><style>
    body{font-family:Segoe UI,Arial;background:#0b1220;color:#e5e7eb;margin:20px}h1{margin-bottom:6px}.sub,small{color:#9ca3af}.banner{padding:12px;margin:12px 0;background:#33230b;border:1px solid #a16207;border-radius:8px}.wrap{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:13px}th,td{padding:9px 7px;border-bottom:1px solid #334155;text-align:left;vertical-align:top}th{position:sticky;top:0;background:#111827}.market-canada td:first-child{background:rgba(220,38,38,.08)}.market-us td:first-child{background:rgba(37,99,235,.08)}a{color:#93c5fd}</style></head><body>""" + \
        f"<h1>🚨 Early Momentum & Unusual Volume</h1><div class='sub'>Generated {now:%Y-%m-%d %H:%M:%S ET} · {len(symbols)} candidates checked · 5-minute bars</div>" + \
        "<div class='banner'><b>Discovery only — not a buy signal.</b> Early alert: +2% from prior close with at least 2× same-time volume. Strong move: +5%. Exceptional volume: 3× same-time baseline. The scanner deliberately does not apply the regular bot's overextension or 4% stop gates; those remain in the separate Confirmed Swing screen. Verify news, spread, halts, dilution, liquidity and live quotes before acting. Coverage is limited to watchlist.txt plus up to the configured number of symbols in market_universe.txt.</div>" + \
        "<div class='wrap'><table><thead><tr><th>Ticker / market</th><th>Alert</th><th>Move</th><th>Last</th><th>Same-time RVOL</th><th>Session volume</th><th>Last bar</th><th>Headline check</th></tr></thead><tbody>" + \
        ("".join(body) if body else "<tr><td colspan='8'>No qualifying intraday movers found. Check market hours, data feed and universe coverage.</td></tr>") + \
        "</tbody></table></div><p><a href='trade_screen.html'>Confirmed Swing screen</a> · <a href='news_watch.html'>News Watch</a></p></body></html>"
    Path("early_momentum.html").write_text(page, encoding="utf-8")
    print(f"Early Momentum scanner: {len(rows)} movers; dashboard: early_momentum.html", flush=True)
    if alert_lines:
        notify("🚨 EARLY MOMENTUM ALERTS\n" + "\n".join(alert_lines[:12]) + "\nReview early_momentum.html; discovery alerts are not trade instructions.")
    return rows


def start_mobile_dashboard_server() -> None:
    """Serve only the generated HTML dashboards to devices on the private network."""
    port = int(os.getenv("SWING_WEB_PORT", "8765"))
    allowed_pages = {
        "trade_screen.html", "news_watch.html", "early_momentum.html", "options_watch.html"
    }

    class DashboardHandler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            path = urllib.parse.urlsplit(self.path).path
            if path in ("/", "/index.html"):
                page = "trade_screen.html"
            else:
                page = path.lstrip("/")
            if page not in allowed_pages:
                self.send_error(404, "Dashboard page not found")
                return
            file_path = Path.cwd() / page
            if not file_path.is_file():
                self.send_error(404, "Dashboard has not been generated yet")
                return
            try:
                payload = file_path.read_bytes()
            except OSError:
                self.send_error(500, "Unable to read dashboard")
                return
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(payload)))
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.end_headers()
            self.wfile.write(payload)

        def log_message(self, fmt, *args):
            # Keep the trading monitor console readable; the server remains available.
            return

    try:
        server = http.server.ThreadingHTTPServer(("0.0.0.0", port), DashboardHandler)
        server.daemon_threads = True
        threading.Thread(target=server.serve_forever, name="mobile-dashboard", daemon=True).start()
        try:
            lan_ip = socket.gethostbyname(socket.gethostname())
        except OSError:
            lan_ip = "<PC-IP>"
        print(f"Mobile dashboard server ready on port {port}. On the same Wi-Fi, open http://{lan_ip}:{port}/ on your iPhone. "
              "For access away from home, use a private VPN such as Tailscale; do not port-forward this server to the public internet.", flush=True)
    except OSError as exc:
        print(f"Mobile dashboard server could not start on port {port}: {exc}. The bot will continue normally.", flush=True)


def run_monitor(args) -> None:
    start_mobile_dashboard_server()
    # The browser's meta-refresh only reloads the HTML file; it cannot regenerate
    # the stock data embedded in that file. Refresh the regular screen periodically
    # after hours too, so its generated timestamp and latest available daily closes
    # do not remain stuck at the last market-open scan.
    closed_screen_refresh_sec = 5 * 60
    last_closed_screen_refresh = time.time() - closed_screen_refresh_sec
    print(f"Monitor started. News/social research runs while markets are closed. Scan every {SCAN_INTERVAL_SEC}s. "
          f"The trade screen refreshes at least every {closed_screen_refresh_sec // 60} minutes after hours. Ctrl+C to stop.")
    while True:
        now = datetime.now(ET_TZ)
        try:
            run_news_watch_cycle(batch_size=getattr(args, "news_batch_size", 12),
                                 use_llm=not args.no_llm, use_social=not args.no_social)
            if monday_picks_due(now) or args.force_picks:
                args.force_picks = False
                STATE["last_picks_week"] = now.strftime("%G-W%V")
                _save_state(STATE)
                picks, verdict = run_picks(PICKS_TOP_N, not args.no_llm, not args.no_social,
                                           live=market_is_open(now), validate=True, split_markets=True)
                log_picks(picks)
                render_html(picks, verdict)
                notify("📅 MONDAY TRADE SCREEN\n" + edge_banner(verdict) + "\n\n"
                       + "\n\n".join("\n".join(ticket_lines(i + 1, r, 60, verdict)) for i, r in enumerate(picks[:3])))
            if market_is_open(now) or args.always:
                # Separate discovery scan runs before the conservative swing filters so sharp
                # movers are visible even if they fail the regular stop/overextension gates.
                try:
                    run_momentum_scan(max_universe=getattr(args, "momentum_universe_cap", MOMENTUM_UNIVERSE_CAP),
                                      use_news=not args.no_llm, send_alerts=True)
                except Exception as momentum_exc:
                    print(f"Early Momentum scanner error: {type(momentum_exc).__name__}: {momentum_exc}", flush=True)
                check_positions(now)
                picks, verdict = run_picks(PICKS_TOP_N, not args.no_llm, not args.no_social,
                                           live=True, validate=False, split_markets=True)
                for r in picks[:5]:
                    if r["total"] >= ALERT_SCORE and cooldown_ok(f"sig:{r['ticker']}"):
                        notify("🔔 SETUP ALERT\n" + "\n".join(ticket_lines(1, r, 60, verdict)))
                render_html(picks, verdict)
            else:
                # Recalculate using the latest available daily bars while the market
                # is closed. Quotes may still be the last close; do not imply that
                # this is live after-hours pricing.
                now_epoch = time.time()
                screen_exists = Path(HTML_SCREEN).exists()
                if (not screen_exists) or (now_epoch - last_closed_screen_refresh >= closed_screen_refresh_sec):
                    try:
                        picks, verdict = run_picks(PICKS_TOP_N, not args.no_llm, not args.no_social,
                                                   live=False, validate=False, split_markets=True)
                        render_html(picks, verdict)
                        last_closed_screen_refresh = now_epoch
                        print(f"[{now:%a %H:%M}] after-hours trade screen refreshed from latest available daily data; "
                              f"quotes may reflect the last close", flush=True)
                    except Exception as screen_exc:
                        print(f"After-hours trade-screen refresh failed: {type(screen_exc).__name__}: {screen_exc}", flush=True)
                else:
                    print(f"[{now:%a %H:%M}] market closed; next full trade-screen refresh in "
                          f"{max(0, int((closed_screen_refresh_sec - (now_epoch - last_closed_screen_refresh)) / 60))} min",
                          flush=True)
        except Exception as e:
            print(f"Cycle error: {e}")
        time.sleep(SCAN_INTERVAL_SEC)


# =============================== DOCTOR / UNIVERSE ============================


def run_doctor() -> None:
    results = []

    def chk(name, fn):
        try:
            ok, msg = fn()
        except Exception as e:
            ok, msg = False, f"{type(e).__name__}: {e}"
        results.append((name, "PASS" if ok else "FAIL", msg))

    chk("Yahoo daily (US: AAPL)", lambda: (lambda d: (bool(d), f"{len(d.get('AAPL', []))} bars"))(fetch_daily(["AAPL"], "1mo")))
    chk("Yahoo daily (TSX: SHOP.TO)", lambda: (lambda d: (bool(d), f"{len(d.get('SHOP.TO', []))} bars"))(fetch_daily(["SHOP.TO"], "1mo")))
    chk("Yahoo hourly (AAPL)", lambda: (lambda d: (bool(d), f"{len(d.get('AAPL', []))} bars"))(_yahoo_intraday(["AAPL"], "60m", "5d")))
    chk("Google News RSS", lambda: (lambda n: (len(n) > 0, f"{len(n)} headlines"))(google_news("Apple stock when:7d")))
    chk("CA wires via RSS (ceo.ca etc.)", lambda: (lambda n: (len(n) > 0, f"{len(n)} headlines"))(
        google_news('"Shopify" (site:newswire.ca OR site:globenewswire.com OR site:ceo.ca) when:30d')))
    chk("StockTwits", lambda: (lambda s: (s["msgs"] > 0, f"{s['msgs']} messages"))(stocktwits_signal("AAPL")))
    chk("Reddit search", lambda: (lambda r: (r.status_code == 200, f"HTTP {r.status_code}"))(
        requests.get(_reddit_url("NVDA"), headers=UA, timeout=12)))
    if os.getenv("ANTHROPIC_API_KEY"):
        chk("Claude headline rating", lambda: (lambda r: (bool(r), str(r[0]) if r else "no response"))(
            llm_rate("AAPL", "Apple", ["Apple beats earnings estimates, raises guidance"])))
    else:
        results.append(("Claude headline rating", "SKIP", "ANTHROPIC_API_KEY not set (keyword fallback will be used)"))
    results.append(("Telegram", "OK" if os.getenv("TELEGRAM_BOT_TOKEN") and os.getenv("TELEGRAM_CHAT_ID") else "SKIP",
                    "configured" if os.getenv("TELEGRAM_BOT_TOKEN") else "not configured"))
    results.append(("Discord", "OK" if os.getenv("DISCORD_WEBHOOK_URL") else "SKIP",
                    "configured" if os.getenv("DISCORD_WEBHOOK_URL") else "not configured"))
    n_csv = len(glob.glob(str(FILINGS_DIR / "*.csv")))
    results.append(("Filings CSV folder", "OK" if n_csv else "SKIP", f"{n_csv} file(s) in {FILINGS_DIR}/"))
    results.append(("Watchlist", "OK" if Path(WATCHLIST_FILE).exists() else "FAIL", WATCHLIST_FILE))
    print(f"\n{'Check':<34}{'Result':<7} Detail")
    for n, s, m in results:
        print(f"{n:<34}{s:<7} {m}")
    print("\nAnything FAIL: check your internet/firewall, then re-run. Reddit often blocks without OAuth; "
          "the bot just skips that signal when it fails.")


def build_universe(src: str, out: str, max_n: int) -> None:
    """Filter a ticker list using liquidity and trade-plan checks, not past performance."""
    tickers = [l.split("#")[0].strip().upper() for l in Path(src).read_text().splitlines() if l.split("#")[0].strip()]
    tickers = list(dict.fromkeys(tickers))
    print(f"Checking {len(tickers)} tickers for liquidity (this can take a while)...")
    data = fetch_daily(tickers, "1y")
    keep = []
    for t, df in data.items():
        f = compute_features(df)
        if f and liquidity_gate(f)[0] and trade_plan(f)["ok"]:
            keep.append((t, f["dollar_vol"]))
    keep.sort(key=lambda x: x[1], reverse=True)
    if max_n > 0:
        keep = keep[:max_n]
    Path(out).write_text("# Auto-built by build-universe (liquidity only)\n" + "\n".join(t for t, _ in keep) + "\n", encoding="utf-8")
    print(f"Wrote {len(keep)} liquid tickers to {out}; {len(data)} had price data")


US_LISTING_URLS = {
    "nasdaq": "https://www.nasdaqtrader.com/dynamic/SymDir/nasdaqlisted.txt",
    "other": "https://www.nasdaqtrader.com/dynamic/SymDir/otherlisted.txt",
}
TMX_MOC_URL = "https://www.tsx.com/en/trading/market-data-and-statistics/market-statistics-and-reports/tsx-tsxv-moc-eligible-stocks"
_NON_COMMON_TERMS = (" WARRANT", " WARRANTS", " WTS", " RIGHT", " RIGHTS", " UNIT", " UNITS",
                      " PREFERRED", " DEBENTURE", " DEBENTURES", " NOTE", " NOTES", " BOND", " BONDS",
                      " ETF", " ETN", " EXCHANGE TRADED", " WHEN ISSUED", " WHEN DISTRIBUTED")


def _is_common_stock_name(name: str) -> bool:
    """Conservative name filter: excludes most funds and non-common-stock security types."""
    n = " " + re.sub(r"[^A-Z0-9]+", " ", str(name).upper()).strip() + " "
    return not any(term in n for term in _NON_COMMON_TERMS)


def parse_nasdaq_directory(text: str, other_exchange: bool = False) -> list[str]:
    """Parse NasdaqTrader pipe-delimited security directories without needing pandas."""
    lines = [line for line in text.splitlines() if line.strip() and not line.startswith("File Creation Time")]
    if not lines:
        return []
    reader = csv.DictReader(lines, delimiter="|")
    out = []
    for row in reader:
        symbol = (row.get("ACT Symbol") if other_exchange else row.get("Symbol")) or ""
        name = row.get("Security Name", "")
        test = (row.get("Test Issue") or "N").upper()
        etf = (row.get("ETF") or "N").upper()
        if not symbol or test == "Y" or etf == "Y" or not _is_common_stock_name(name):
            continue
        # Yahoo Finance uses a hyphen for many US share-class symbols (e.g. BRK-B).
        symbol = symbol.strip().upper().replace(".", "-")
        if re.fullmatch(r"[A-Z0-9-]{1,15}", symbol):
            out.append(symbol)
    return list(dict.fromkeys(out))


def discover_market_symbols(timeout: int = 20) -> tuple[list[str], dict[str, str]]:
    """Discover US exchange listings plus the publicly listed TMX TSX/TSXV MOC universe.

    NasdaqTrader provides daily Nasdaq and other-exchange directories. TMX's public MOC
    eligible list is a useful TSX/TSXV source but is not a complete directory of every
    Canadian listing; this limitation is recorded rather than silently overstating coverage.
    """
    symbols: list[str] = []
    status: dict[str, str] = {}
    session = requests.Session()
    session.headers.update(UA)
    for label, url in US_LISTING_URLS.items():
        try:
            r = session.get(url, timeout=timeout)
            r.raise_for_status()
            found = parse_nasdaq_directory(r.text, other_exchange=(label == "other"))
            if not found:
                raise ValueError("directory returned no eligible common-stock symbols")
            symbols.extend(found)
            status[f"US {label}"] = f"{len(found)} symbols"
        except Exception as exc:
            status[f"US {label}"] = f"FAILED: {type(exc).__name__}: {exc}"

    try:
        r = session.get(TMX_MOC_URL, timeout=timeout)
        r.raise_for_status()
        tables = pd.read_html(io.StringIO(r.text))
        ca: list[str] = []
        for table in tables:
            cols = {str(c).strip().lower(): c for c in table.columns}
            sym_col = next((cols[c] for c in cols if c in ("symbol", "ticker")), None)
            market_col = next((cols[c] for c in cols if "market" in c or "exchange" in c), None)
            name_col = next((cols[c] for c in cols if "company" in c or "name" in c), None)
            if sym_col is None or market_col is None:
                continue
            for _, row in table.iterrows():
                raw = str(row[sym_col]).strip().upper()
                market = str(row[market_col]).strip().upper()
                name = str(row[name_col]) if name_col is not None else ""
                if market not in ("TSX", "TSXV", "TSX VENTURE") or not raw or raw == "NAN":
                    continue
                if not _is_common_stock_name(name):
                    continue
                # Yahoo Finance's common suffixes for TSX and TSX Venture listings.
                suffix = ".V" if "VENTURE" in market or market == "TSXV" else ".TO"
                raw = raw.replace(":TSX", "").replace(":TSXV", "").strip().replace(".", "-")
                ca.append(raw + suffix)
        ca = list(dict.fromkeys(ca))
        if not ca:
            raise ValueError("no TSX/TSXV symbols parsed from the public TMX table")
        symbols.extend(ca)
        status["Canada TSX/TSXV"] = f"{len(ca)} symbols (TMX MOC-eligible list; not every Canadian listing)"
    except Exception as exc:
        status["Canada TSX/TSXV"] = f"FAILED: {type(exc).__name__}: {exc}"

    symbols = list(dict.fromkeys(symbols))
    if not symbols:
        raise RuntimeError("No market symbols downloaded. Check your internet connection and try again. " + repr(status))
    return symbols, status


def auto_universe(out: str = WATCHLIST_FILE, candidates_out: str = "market_universe.txt",
                  max_n: int = 150, scan: bool = True) -> None:
    """Refresh a full candidate file and optionally filter it to the bot's liquid watchlist.

    max_n=0 means no cap on the final liquid watchlist. Full candidates are always saved
    separately so the active scan doesn't accidentally balloon to thousands of symbols.
    """
    symbols, status = discover_market_symbols()
    Path(candidates_out).write_text(
        "# Auto-discovered exchange-listed stock candidates; generated " + datetime.now().isoformat(timespec="seconds") + "\n"
        + "\n".join(symbols) + "\n", encoding="utf-8")
    print("Market symbol discovery:")
    for source, result in status.items():
        print(f"  {source}: {result}")
    print(f"Saved {len(symbols)} unique candidate symbols to {candidates_out}")
    if not scan:
        print("Discovery only: active watchlist was not changed. Use --filter to build a liquid watchlist.")
        return
    print("Filtering candidates by 1-year price history, liquidity, and trade-plan checks. This may take a long time...")
    build_universe(candidates_out, out, max_n)
    print(f"Active watchlist updated: {out}")
    print("Note: US coverage uses NasdaqTrader exchange directories; Canadian coverage uses TMX's public TSX/TSXV MOC list, which is not exhaustive. OTC and some Canadian listings may be missing.")



# =============================== OPTIONS WATCH ================================

def options_watch(tickers: list[str] | None = None, out: str = "options_watch.html") -> str:
    """Create an informational US-listed options watch from Yahoo Finance snapshots.
    Does not recommend a contract or place orders. Quotes may be delayed/incomplete.
    """
    try:
        import yfinance as yf
    except Exception as exc:
        raise RuntimeError("Options Watch requires yfinance. Run: pip install yfinance") from exc
    if not tickers:
        tickers = [t for t in load_watchlist() if not t.endswith(CA_SUFFIXES)][:40]
    rows = []
    today = datetime.now(ET_TZ).date()
    for ticker in list(dict.fromkeys(t.upper() for t in tickers))[:60]:
        try:
            obj = yf.Ticker(ticker)
            expiries = list(obj.options or [])
            if not expiries:
                rows.append((ticker, "—", "No option chain returned", "—", "—", "—", "—", "—"))
                continue
            suitable = []
            for exp in expiries:
                dte = (datetime.strptime(exp, "%Y-%m-%d").date() - today).days
                if 7 <= dte <= 45:
                    suitable.append((dte, exp))
            if not suitable:
                suitable = [( (datetime.strptime(exp, "%Y-%m-%d").date()-today).days, exp) for exp in expiries if (datetime.strptime(exp, "%Y-%m-%d").date()-today).days >= 0][:1]
            if not suitable:
                rows.append((ticker, "—", "No future expiry", "—", "—", "—", "—", "—"))
                continue
            dte, exp = min(suitable, key=lambda z: abs(z[0]-21))
            chain = obj.option_chain(exp)
            for side, df in (("CALL", chain.calls), ("PUT", chain.puts)):
                if df is None or df.empty:
                    continue
                d = df.copy()
                for col in ("volume", "openInterest", "bid", "ask", "impliedVolatility", "strike"):
                    if col not in d:
                        d[col] = np.nan
                d["volume"] = pd.to_numeric(d["volume"], errors="coerce").fillna(0)
                d["openInterest"] = pd.to_numeric(d["openInterest"], errors="coerce").fillna(0)
                d["bid"] = pd.to_numeric(d["bid"], errors="coerce")
                d["ask"] = pd.to_numeric(d["ask"], errors="coerce")
                d["spread_pct"] = (d["ask"]-d["bid"])/((d["ask"]+d["bid"])/2).replace(0, np.nan)*100
                d = d[(d["volume"] >= 10) | (d["openInterest"] >= 100)]
                d = d[(d["bid"] > 0) & (d["ask"] >= d["bid"]) & (d["spread_pct"] <= 25)]
                if d.empty:
                    continue
                d["liquidity"] = d["volume"] + d["openInterest"] * .1
                # Show the most active/liquid contracts, not an entry recommendation.
                for _, c in d.nlargest(2, "liquidity").iterrows():
                    iv = float(c["impliedVolatility"])*100 if pd.notna(c["impliedVolatility"]) else float("nan")
                    rows.append((ticker, side, exp, f"{int(dte)}", f"${float(c['strike']):.2f}",
                                 f"${float(c['bid']):.2f} / ${float(c['ask']):.2f}",
                                 f"{int(c['volume'])} / {int(c['openInterest'])}",
                                 f"{iv:.1f}%" if np.isfinite(iv) else "—"))
            time.sleep(.15)
        except Exception as exc:
            rows.append((ticker, "—", f"Data unavailable: {type(exc).__name__}", "—", "—", "—", "—", "—"))
    body = "".join("<tr>" + "".join(f"<td>{html.escape(str(v))}</td>" for v in r) + "</tr>" for r in rows)
    page = """<!doctype html><html><head><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'>
    <title>Options Watch</title><style>""" + HTML_CSS + """</style></head><body><h1>Options Watch</h1>
    <div class='sub'>Generated """ + datetime.now(ET_TZ).strftime("%Y-%m-%d %H:%M ET") + """ · US-listed symbols only · Yahoo snapshot data</div>
    <div class='banner warn'>Research watch only. Options can expire worthless. No contract is a recommendation. Verify current quotes, spread, volume, open interest, expiry and implied volatility with your broker before acting. Canadian-listed options and some US symbols may not be available through this feed.</div>
    <div class='wrap'><table><thead><tr><th>Ticker</th><th>Side</th><th>Expiry</th><th>DTE</th><th>Strike</th><th>Bid / Ask</th><th>Volume / OI</th><th>IV</th></tr></thead><tbody>""" + body + """</tbody></table></div>
    <p><a href='trade_screen.html'>← Back to Trade Screen</a></p><div class='foot'>Contracts shown are selected for basic displayed liquidity and spread checks only. The page does not assess expected value, Greeks, earnings risk, assignment, or suitability.</div></body></html>"""
    Path(out).write_text(page, encoding="utf-8")
    print(f"Options watch written: {out} ({len(rows)} rows)")
    return out

# =============================== CLI ==========================================


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--top", type=int, default=PICKS_TOP_N)
        p.add_argument("--no-llm", action="store_true")
        p.add_argument("--no-social", action="store_true")
        p.add_argument("--no-news", action="store_true")
        p.add_argument("--no-validate", action="store_true", help="skip the edge-check backtest")
        p.add_argument("--no-log", action="store_true", help="don't write picks to the forward-test journal")
        p.add_argument("--notify", action="store_true")
        p.add_argument("--ignore-volume", action="store_true", help="turn OFF the minimum-volume filters")

    common(sub.add_parser("screen", help="buy-in / sell-out trade screen"))
    common(sub.add_parser("picks", help="plain ranked list"))
    m = sub.add_parser("monitor")
    m.add_argument("--no-llm", action="store_true")
    m.add_argument("--no-social", action="store_true")
    m.add_argument("--always", action="store_true")
    m.add_argument("--force-picks", action="store_true")
    m.add_argument("--news-batch-size", type=int, default=12,
                   help="watchlist tickers to check for news each cycle, even when markets are closed (default 12)")
    m.add_argument("--ignore-volume", action="store_true", help="turn OFF the minimum-volume filters")
    b = sub.add_parser("backtest")
    b.add_argument("--period", default="2y")
    b.add_argument("--hourly", action="store_true", help="resolve stop-vs-target order with 60m bars (~2y max)")
    b.add_argument("--cost", type=float, default=0.005,
                   help="estimated all-in round-trip friction as a fraction (0.005 = 0.5%%)")
    b.add_argument("--ignore-volume", action="store_true", help="turn OFF the minimum-volume filters")
    sub.add_parser("grade")
    sub.add_parser("scorecard")
    sub.add_parser("doctor")
    mm = sub.add_parser("momentum", help="scan early price movers and unusual same-time volume")
    mm.add_argument("--universe-cap", type=int, default=MOMENTUM_UNIVERSE_CAP,
                     help="maximum additional symbols from market_universe.txt (default 300; 0 disables extras)")
    mm.add_argument("--no-news", action="store_true", help="skip headline checks for detected movers")
    mm.add_argument("--no-notify", action="store_true", help="write dashboard without push notifications")
    u = sub.add_parser("build-universe")
    u.add_argument("source")
    u.add_argument("--out", default=WATCHLIST_FILE)
    u.add_argument("--max", type=int, default=150, help="maximum final tickers; use 0 for no cap")
    au = sub.add_parser("auto-universe", help="discover US/Canadian listings and refresh a liquid watchlist")
    au.add_argument("--out", default=WATCHLIST_FILE, help="active watchlist file (default watchlist.txt)")
    au.add_argument("--candidates-out", default="market_universe.txt", help="save full discovered candidate list here")
    au.add_argument("--max", type=int, default=150, help="maximum liquid watchlist size; 0 means no cap")
    au.add_argument("--discover-only", action="store_true", help="save discovered candidates but do not change watchlist")
    au.add_argument("--no-filter", action="store_true", help="same as --discover-only")
    a = sub.add_parser("add-position")
    a.add_argument("ticker")
    a.add_argument("entry", type=float)
    a.add_argument("--shares", type=int, default=0)
    sub.add_parser("positions")
    ow = sub.add_parser("options-watch", help="build an informational options-chain watch page")
    ow.add_argument("--tickers", default="", help="comma-separated US tickers; defaults to first 40 US watchlist symbols")
    ow.add_argument("--out", default="options_watch.html")
    args = ap.parse_args()
    if getattr(args, "ignore_volume", False):
        global IGNORE_VOLUME_FILTER
        IGNORE_VOLUME_FILTER = True
        print("NOTE: minimum-volume filters are OFF. Thin stocks can have wide spreads and hard exits.")

    if args.cmd in ("screen", "picks"):
        picks, verdict = run_picks(args.top, not args.no_llm, not args.no_social, not args.no_news,
                                   live=market_is_open(), validate=not args.no_validate,
                                   split_markets=(args.cmd == "screen"))
        if not picks:
            print("No setups passed the filters.")
            return
        if not args.no_log:
            log_picks(picks)
        if args.cmd == "screen":
            print(render_terminal(picks, verdict))
            print(f"\nHTML screen written: {render_html(picks, verdict)}")
        else:
            print("\n" + edge_banner(verdict))
            for i, r in enumerate(picks, 1):
                print("\n".join(ticket_lines(i, r, verdict=verdict)))
        if args.notify:
            notify("📅 TRADE SCREEN\n" + edge_banner(verdict) + "\n\n"
                   + "\n\n".join("\n".join(ticket_lines(i + 1, r, 60, verdict)) for i, r in enumerate(picks[:3])))
    elif args.cmd == "monitor":
        run_monitor(args)
    elif args.cmd == "backtest":
        wl = load_watchlist()
        print(f"Backtesting {len(wl)} tickers over {args.period} ...")
        data = fetch_daily(wl, args.period)
        hourly = _yahoo_intraday(list(data)) if args.hourly else None
        print_backtest(run_backtest(data, hourly, args.cost), bool(hourly))
    elif args.cmd == "grade":
        grade_journal()
    elif args.cmd == "scorecard":
        scorecard()
    elif args.cmd == "doctor":
        run_doctor()
    elif args.cmd == "momentum":
        run_momentum_scan(max_universe=max(0, args.universe_cap), use_news=not args.no_news,
                          send_alerts=not args.no_notify)
    elif args.cmd == "build-universe":
        build_universe(args.source, args.out, args.max)
    elif args.cmd == "auto-universe":
        auto_universe(args.out, args.candidates_out, args.max, scan=not (args.discover_only or args.no_filter))
    elif args.cmd == "add-position":
        add_position(args.ticker, args.entry, args.shares)
    elif args.cmd == "positions":
        for p in load_positions():
            print(p)
    elif args.cmd == "options-watch":
        symbols = [x.strip().upper() for x in args.tickers.split(",") if x.strip()] or None
        options_watch(symbols, args.out)


if __name__ == "__main__":
    main()
