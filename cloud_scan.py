#!/usr/bin/env python3
"""Run one cloud scan, using the user's existing Swing Bot scoring logic, and publish mobile JSON."""
from __future__ import annotations
import json, shutil, traceback
from datetime import datetime, timezone
from pathlib import Path

import swing_bot as bot

ROOT = Path(__file__).resolve().parent
DOCS = ROOT / "docs"
DOCS.mkdir(exist_ok=True)

def safe_float(value, default=None):
    try:
        if value is None:
            return default
        out = float(value)
        if out != out or abs(out) == float("inf"):
            return default
        return round(out, 4)
    except (TypeError, ValueError):
        return default

def compact_row(r, rank=0):
    f = r.get("f") or {}
    p = r.get("plan") or {}
    return {
        "ticker": str(r.get("ticker", "")),
        "market": "CANADA" if bot.market_side(str(r.get("ticker", ""))).startswith("CANADA") else "USA",
        "rank": rank,
        "score": safe_float(r.get("total", r.get("tech"))),
        "tech": safe_float(r.get("tech")),
        "momentum": safe_float(r.get("momentum")),
        "price": safe_float(r.get("now", f.get("price"))),
        "price_source": str(r.get("now_src", "latest available daily bar")),
        "status": str(r.get("status", "WATCH")),
        "status_text": str(r.get("status_txt", "")),
        "setup": str(r.get("setup", "WATCH")),
        "recommendation": str(bot.recommendation(r, None)[0]) if "plan" in r else "WATCH",
        "volume": safe_float(f.get("last_vol")),
        "relative_volume": safe_float(f.get("rvol")),
        "buy_low": safe_float(p.get("buy_lo")),
        "buy_high": safe_float(p.get("buy_hi")),
        "entry": safe_float(p.get("entry")),
        "stop": safe_float(p.get("stop")),
        "target_1": safe_float(p.get("t1")),
        "target_2": safe_float(p.get("t2")),
        "shares": int(p.get("size", {}).get("shares", 0)) if p.get("size") else None,
        "news": [
            {"title": str(x.get("title", ""))[:220], "url": str(x.get("url", "")),
             "direction": str(x.get("direction", "")), "rumor": bool(x.get("rumor", False))}
            for x in ((r.get("news") or {}).get("top") or [])[:2]
        ],
    }

def copy_if_exists(name):
    src = ROOT / name
    dst = DOCS / name
    if src.exists():
        shutil.copy2(src, dst)

def main():
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    market_open = bot.market_is_open()
    result = {
        "generated_at": now,
        "market_open": market_open,
        "market_timezone": "America/New_York",
        "scan_interval_note": "Scheduled cloud scan; GitHub Actions can run late. Quotes may be delayed.",
        "strategy": {"target_1_pct": 5, "target_2_pct": 10, "max_stop_pct": 4, "horizon_days": 5},
        "source": "Existing Swing Bot v3 ranking and trade-plan logic",
        "universe_count": 0,
        "picks": [],
        "universe": [],
        "momentum": [],
        "errors": [],
    }

    try:
        # News research is run in batches and uses public sources; AI/social APIs are optional.
        try:
            bot.run_news_watch_cycle(batch_size=12, use_llm=False, use_social=False)
        except Exception as exc:
            result["errors"].append("News watch: " + type(exc).__name__ + ": " + str(exc)[:180])

        # Intraday momentum is only meaningful during the regular US market session.
        if market_open:
            try:
                momentum_rows = bot.run_momentum_scan(max_universe=100, use_news=True, send_alerts=False) or []
                result["momentum"] = [{
                    "ticker": str(r.get("ticker", "")),
                    "market": str(r.get("market", "USA")),
                    "level": str(r.get("level", "WATCH")),
                    "move_pct": safe_float(float(r.get("move", 0)) * 100),
                    "price": safe_float(r.get("price")),
                    "rvol": safe_float(r.get("rvol")),
                    "volume": safe_float(r.get("volume")),
                    "headline": str((r.get("headlines") or [""])[0])[:220],
                    "bar_time": str(r.get("bar_time", "")),
                } for r in momentum_rows[:100]]
            except Exception as exc:
                result["errors"].append("Momentum scan: " + type(exc).__name__ + ": " + str(exc)[:180])

        picks, verdict = bot.run_picks(
            top=20, use_llm=False, use_social=False, use_news=True,
            live=market_open, validate=False, split_markets=True
        )
        bot.render_html(picks, verdict)
        result["picks"] = [compact_row(r, i + 1) for i, r in enumerate(picks)]
        result["universe"] = [compact_row(r) for r in bot.LAST_SCREEN_ROWS]
        result["universe_count"] = len(result["universe"])
        result["edge_check"] = {
            "ok": bool(verdict.get("ok")) if verdict else None,
            "summary": str(verdict.get("summary", "")) if verdict else "Historical edge check not run on every scheduled scan.",
        }
    except Exception as exc:
        result["errors"].append("Main scan: " + type(exc).__name__ + ": " + str(exc)[:250])
        result["traceback"] = traceback.format_exc()[-3000:]

    (DOCS / "data.json").write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    for page in ("trade_screen.html", "news_watch.html", "early_momentum.html", "options_watch.html"):
        copy_if_exists(page)
    print(f"Published {len(result['picks'])} ranked picks and {len(result['universe'])} universe rows to docs/data.json")
    if result["errors"]:
        print("Scan warnings:", *result["errors"], sep="\n- ")

if __name__ == "__main__":
    main()
