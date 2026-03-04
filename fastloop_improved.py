#!/usr/bin/env python3
"""
Polymarket FastLoop Trader — Improved
======================================
Multi-signal momentum strategy for Polymarket 5-minute fast markets.

Improvements over original:
  - Funding rate confirmation (Binance perps)
  - Order book imbalance confirmation
  - Accurate fee-adjusted EV with configurable buffer
  - Time-of-day filtering (skip low-liquidity hours)
  - Volatility-adjusted position sizing
  - Win rate tracking and calibration reporting
  - Smart market selection (target time window, not just soonest)
  - Raised default momentum threshold (1.0% vs 0.5%)

Usage:
    python fastloop_improved.py              # Paper mode (default)
    python fastloop_improved.py --live       # Real trades
    python fastloop_improved.py --stats      # P&L + calibration report
    python fastloop_improved.py --resolve    # Fetch real outcomes for open trades
    python fastloop_improved.py --positions  # Show open Simmer positions
    python fastloop_improved.py --config     # Show current config
    python fastloop_improved.py --quiet      # For cron/heartbeat
    python fastloop_improved.py --set KEY=VALUE

Requires:
    SIMMER_API_KEY environment variable
"""

import os
import sys
import json
import math
import argparse
import re
from datetime import datetime, timezone, timedelta
from urllib.request import urlopen, Request
from urllib.error import HTTPError, URLError

sys.stdout.reconfigure(line_buffering=True)

# =============================================================================
# Configuration
# =============================================================================

CONFIG_SCHEMA = {
    "entry_threshold":   {"default": 0.05,    "env": "SIMMER_SPRINT_ENTRY",       "type": float,
                          "help": "Min price divergence from 50¢ to trigger"},
    "min_momentum_pct":  {"default": 1.0,     "env": "SIMMER_SPRINT_MOMENTUM",    "type": float,
                          "help": "Min % price move (was 0.5 in original — raised for real edge)"},
    "max_position":      {"default": 5.0,     "env": "SIMMER_SPRINT_MAX_POSITION","type": float,
                          "help": "Max $ per trade (before vol adjustment)"},
    "signal_source":     {"default": "binance","env": "SIMMER_SPRINT_SIGNAL",     "type": str,
                          "help": "binance or coingecko"},
    "lookback_minutes":  {"default": 5,       "env": "SIMMER_SPRINT_LOOKBACK",    "type": int,
                          "help": "Minutes of candle history for momentum"},
    "min_time_remaining":{"default": 60,      "env": "SIMMER_SPRINT_MIN_TIME",    "type": int,
                          "help": "Hard floor: skip markets with less than N seconds left"},
    "target_time_min":   {"default": 90,      "env": None,                         "type": int,
                          "help": "Prefer markets with >= N seconds left (sweet spot)"},
    "target_time_max":   {"default": 210,     "env": None,                         "type": int,
                          "help": "Prefer markets with <= N seconds left (sweet spot)"},
    "asset":             {"default": "BTC",   "env": "SIMMER_SPRINT_ASSET",       "type": str,
                          "help": "BTC, ETH, or SOL"},
    "window":            {"default": "5m",    "env": "SIMMER_SPRINT_WINDOW",      "type": str,
                          "help": "5m or 15m market window"},
    "volume_confidence": {"default": True,    "env": "SIMMER_SPRINT_VOL_CONF",    "type": bool,
                          "help": "Skip signals with volume < 0.5x average"},
    "require_funding":   {"default": False,   "env": None,                         "type": bool,
                          "help": "Require funding rate to confirm momentum direction"},
    "require_orderbook": {"default": False,   "env": None,                         "type": bool,
                          "help": "Require order book imbalance to confirm direction"},
    "time_filter":       {"default": True,    "env": None,                         "type": bool,
                          "help": "Skip 02:00–06:00 UTC low-liquidity window"},
    "vol_sizing":        {"default": True,    "env": None,                         "type": bool,
                          "help": "Scale position size down during high volatility"},
    "fee_buffer":        {"default": 0.05,    "env": None,                         "type": float,
                          "help": "Extra divergence required above fee breakeven"},
    "daily_budget":      {"default": 10.0,    "env": "SIMMER_SPRINT_DAILY_BUDGET","type": float,
                          "help": "Max real $ spend per UTC day"},
    "starting_balance":  {"default": 1000.0,  "env": None,                         "type": float,
                          "help": "Paper portfolio starting balance"},
}

TRADE_SOURCE      = "sdk:fastloop-improved"
LEDGER_FILE       = "fastloop_ledger.json"
ASSET_SYMBOLS     = {"BTC": "BTCUSDT",  "ETH": "ETHUSDT",  "SOL": "SOLUSDT"}
ASSET_PERP_SYMBOLS= {"BTC": "BTCUSDT",  "ETH": "ETHUSDT",  "SOL": "SOLUSDT"}
ASSET_PATTERNS    = {"BTC": ["bitcoin up or down"], "ETH": ["ethereum up or down"], "SOL": ["solana up or down"]}
COINGECKO_IDS     = {"BTC": "bitcoin",  "ETH": "ethereum", "SOL": "solana"}
MIN_SHARES        = 5
SMART_SIZING_PCT  = 0.05
LOW_LIQ_HOURS     = set(range(2, 7))   # 02:00–06:00 UTC
_automaton_reported = False


def _load_config(config_file=None):
    if config_file is None:
        config_file = os.path.join(os.path.dirname(__file__), "config.json")
    file_cfg = {}
    if os.path.exists(config_file):
        try:
            with open(config_file) as f:
                file_cfg = json.load(f)
        except Exception:
            pass
    result = {}
    for key, spec in CONFIG_SCHEMA.items():
        if key in file_cfg:
            result[key] = file_cfg[key]
        elif spec.get("env") and os.environ.get(spec["env"]):
            val = os.environ[spec["env"]]
            t = spec.get("type", str)
            try:
                result[key] = (val.lower() in ("true", "1", "yes")) if t == bool else t(val)
            except (ValueError, TypeError):
                result[key] = spec["default"]
        else:
            result[key] = spec["default"]
    return result


def _update_config(updates, config_file=None):
    if config_file is None:
        config_file = os.path.join(os.path.dirname(__file__), "config.json")
    existing = {}
    if os.path.exists(config_file):
        try:
            with open(config_file) as f:
                existing = json.load(f)
        except Exception:
            pass
    existing.update(updates)
    with open(config_file, "w") as f:
        json.dump(existing, f, indent=2)
    return existing


cfg = _load_config()
MAX_POSITION_USD = cfg["max_position"]
_automaton_max = os.environ.get("AUTOMATON_MAX_BET")
if _automaton_max:
    MAX_POSITION_USD = min(MAX_POSITION_USD, float(_automaton_max))

# =============================================================================
# Ledger (paper + live trade log)
# =============================================================================

def _load_ledger():
    ledger_path = os.path.join(os.path.dirname(__file__), LEDGER_FILE)
    if os.path.exists(ledger_path):
        try:
            with open(ledger_path) as f:
                return json.load(f)
        except Exception:
            pass
    return {
        "starting_balance": cfg["starting_balance"],
        "paper_balance": cfg["starting_balance"],
        "trades": [],
        "daily": {},
    }


def _save_ledger(ledger):
    ledger_path = os.path.join(os.path.dirname(__file__), LEDGER_FILE)
    with open(ledger_path, "w") as f:
        json.dump(ledger, f, indent=2, default=str)


def _get_daily(ledger):
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    return ledger["daily"].setdefault(today, {"spent": 0.0, "trades": 0, "pnl": 0.0})


def _record_paper_trade(ledger, trade_dict):
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    day = ledger["daily"].setdefault(today, {"spent": 0.0, "trades": 0, "pnl": 0.0})
    day["spent"] += trade_dict["amount_usd"]
    day["trades"] += 1
    ledger["paper_balance"] -= trade_dict["amount_usd"]
    ledger["trades"].append(trade_dict)
    _save_ledger(ledger)


# =============================================================================
# HTTP helper
# =============================================================================

def _api(url, timeout=12):
    try:
        req = Request(url, headers={"User-Agent": "fastloop-improved/1.0"})
        with urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode())
    except HTTPError as e:
        try:
            return {"error": json.loads(e.read())["msg"]}
        except Exception:
            return {"error": str(e)}
    except Exception as e:
        return {"error": str(e)}


# =============================================================================
# Simmer client
# =============================================================================

_client = None

def get_client(live=True):
    global _client
    if _client is None:
        try:
            from simmer_sdk import SimmerClient
        except ImportError:
            print("Error: simmer-sdk not installed. Run: pip install simmer-sdk")
            sys.exit(1)
        api_key = os.environ.get("SIMMER_API_KEY")
        if not api_key:
            print("Error: SIMMER_API_KEY not set. Get from simmer.markets/dashboard → SDK tab")
            sys.exit(1)
        venue = os.environ.get("TRADING_VENUE", "polymarket")
        _client = SimmerClient(api_key=api_key, venue=venue, live=live)
    return _client


# =============================================================================
# Market Discovery
# =============================================================================

def _parse_end_time(question):
    """Parse ET end time from fast market question string."""
    pattern = r'(\w+ \d+),.*?-\s*(\d{1,2}:\d{2}(?:AM|PM))\s*ET'
    m = re.search(pattern, question)
    if not m:
        return None
    try:
        year = datetime.now(timezone.utc).year
        dt = datetime.strptime(f"{m.group(1)} {year} {m.group(2)}", "%B %d %Y %I:%M%p")
        return dt.replace(tzinfo=timezone.utc) + timedelta(hours=5)  # ET → UTC
    except Exception:
        return None


def discover_fast_markets(asset="BTC", window="5m"):
    patterns = ASSET_PATTERNS.get(asset, ASSET_PATTERNS["BTC"])
    url = ("https://gamma-api.polymarket.com/markets"
           "?limit=20&closed=false&tag=crypto&order=createdAt&ascending=false")
    result = _api(url)
    if not result or (isinstance(result, dict) and result.get("error")):
        return []
    markets = []
    for m in result:
        q = (m.get("question") or "").lower()
        slug = m.get("slug", "")
        if any(p in q for p in patterns) and f"-{window}-" in slug and not m.get("closed"):
            try:
                prices = json.loads(m.get("outcomePrices", "[]"))
                yes_price = float(prices[0]) if prices else 0.5
            except Exception:
                yes_price = 0.5
            markets.append({
                "question":     m.get("question", ""),
                "slug":         slug,
                "condition_id": m.get("conditionId", ""),
                "end_time":     _parse_end_time(m.get("question", "")),
                "yes_price":    yes_price,
                "fee_rate_bps": int(m.get("feeRateBps") or m.get("fee_rate_bps") or 1000),
            })
    return markets


def select_best_market(markets):
    """
    Improved market selection: prefer markets in the target time window
    (target_time_min to target_time_max seconds remaining).
    Falls back to any market above min_time_remaining.
    """
    now = datetime.now(timezone.utc)
    target_min = cfg["target_time_min"]
    target_max = cfg["target_time_max"]
    min_floor  = cfg["min_time_remaining"]

    sweet_spot, fallback = [], []
    for m in markets:
        end = m.get("end_time")
        if not end:
            continue
        secs = (end - now).total_seconds()
        if secs < min_floor:
            continue
        if target_min <= secs <= target_max:
            sweet_spot.append((secs, m))
        else:
            fallback.append((secs, m))

    if sweet_spot:
        sweet_spot.sort(key=lambda x: x[0])
        return sweet_spot[0][1], True   # (market, in_sweet_spot)
    if fallback:
        fallback.sort(key=lambda x: x[0])
        return fallback[0][1], False
    return None, False


# =============================================================================
# Signal 1: Momentum (Binance klines)
# =============================================================================

def get_momentum_signal(asset="BTC", source="binance", lookback=5):
    if source == "coingecko":
        cg = COINGECKO_IDS.get(asset, "bitcoin")
        r  = _api(f"https://api.coingecko.com/api/v3/simple/price?ids={cg}&vs_currencies=usd")
        price = (r or {}).get(cg, {}).get("usd") if not (r or {}).get("error") else None
        if not price:
            return None
        return {"momentum_pct": 0, "direction": "neutral", "price_now": price,
                "price_then": price, "volume_ratio": 1.0, "strong": False}

    symbol = ASSET_SYMBOLS.get(asset, "BTCUSDT")
    url    = f"https://api.binance.com/api/v3/klines?symbol={symbol}&interval=1m&limit={lookback}"
    result = _api(url)
    if not result or isinstance(result, dict):
        return None
    try:
        candles      = result
        price_then   = float(candles[0][1])
        price_now    = float(candles[-1][4])
        momentum_pct = (price_now - price_then) / price_then * 100
        vols         = [float(c[5]) for c in candles]
        avg_vol      = sum(vols) / len(vols)
        vol_ratio    = vols[-1] / avg_vol if avg_vol > 0 else 1.0
        return {
            "momentum_pct": momentum_pct,
            "direction":    "up" if momentum_pct > 0 else "down",
            "price_now":    price_now,
            "price_then":   price_then,
            "avg_volume":   avg_vol,
            "volume_ratio": vol_ratio,
            "strong":       abs(momentum_pct) >= cfg["min_momentum_pct"],
        }
    except Exception:
        return None


# =============================================================================
# Signal 2: Funding Rate
# =============================================================================

def get_funding_signal(asset="BTC"):
    """
    Fetch Binance perpetual funding rate.
    Returns: {"rate": float, "confirms": bool, "direction_bias": "long"|"short"|"neutral"}

    Logic:
      Positive funding = longs paying shorts = market is long-heavy.
      If momentum is UP and funding is very positive (>0.01%), longs are crowded
      → contrarian signal, momentum may be exhausted → does NOT confirm.
      If momentum is UP and funding is negative → squeezed shorts fuel the move → CONFIRMS.
    """
    symbol = ASSET_PERP_SYMBOLS.get(asset, "BTCUSDT")
    url    = f"https://fapi.binance.com/fapi/v1/fundingRate?symbol={symbol}&limit=1"
    result = _api(url)
    if not result or isinstance(result, dict) and result.get("error"):
        return {"rate": None, "available": False}
    try:
        rate = float(result[0]["fundingRate"])
        if rate > 0.0001:
            bias = "long"    # market is long-heavy
        elif rate < -0.0001:
            bias = "short"   # market is short-heavy
        else:
            bias = "neutral"
        return {"rate": rate, "bias": bias, "available": True}
    except Exception:
        return {"rate": None, "available": False}


def funding_confirms(funding, momentum_direction):
    """
    Returns True if funding rate supports the momentum direction.
    UP momentum confirmed when funding is negative (shorts being squeezed).
    DOWN momentum confirmed when funding is positive (longs being squeezed).
    Neutral funding = inconclusive = does not confirm (conservative).
    """
    if not funding.get("available"):
        return None  # unavailable — don't block the trade
    bias = funding["bias"]
    if momentum_direction == "up":
        return bias == "short"    # negative funding confirms upward move
    else:
        return bias == "long"     # positive funding confirms downward move


# =============================================================================
# Signal 3: Order Book Imbalance
# =============================================================================

def get_orderbook_signal(asset="BTC", levels=20):
    """
    Fetch Binance L2 order book and compute bid/ask depth imbalance.
    imbalance = (bid_depth - ask_depth) / total_depth
    > +0.10 → buy pressure → confirms UP
    < -0.10 → sell pressure → confirms DOWN
    """
    symbol = ASSET_SYMBOLS.get(asset, "BTCUSDT")
    url    = f"https://api.binance.com/api/v3/depth?symbol={symbol}&limit={levels}"
    result = _api(url)
    if not result or result.get("error"):
        return {"imbalance": None, "available": False}
    try:
        bid_depth = sum(float(b[1]) for b in result.get("bids", []))
        ask_depth = sum(float(a[1]) for a in result.get("asks", []))
        total     = bid_depth + ask_depth
        if total == 0:
            return {"imbalance": 0, "available": True}
        imbalance = (bid_depth - ask_depth) / total
        return {
            "imbalance":  round(imbalance, 4),
            "bid_depth":  bid_depth,
            "ask_depth":  ask_depth,
            "available":  True,
        }
    except Exception:
        return {"imbalance": None, "available": False}


def orderbook_confirms(ob, momentum_direction):
    """Returns True if order book imbalance aligns with momentum direction."""
    if not ob.get("available") or ob.get("imbalance") is None:
        return None  # unavailable — don't block
    imbalance = ob["imbalance"]
    THRESHOLD = 0.10
    if momentum_direction == "up":
        return imbalance > THRESHOLD
    else:
        return imbalance < -THRESHOLD


# =============================================================================
# Volatility-Adjusted Sizing
# =============================================================================

def get_24h_volatility(asset="BTC"):
    """
    Calculate 24h realised volatility from Binance hourly candles.
    Returns annualised vol as a decimal (e.g. 0.85 = 85% annualised).
    """
    symbol = ASSET_SYMBOLS.get(asset, "BTCUSDT")
    url    = f"https://api.binance.com/api/v3/klines?symbol={symbol}&interval=1h&limit=25"
    result = _api(url)
    if not result or isinstance(result, dict):
        return None
    try:
        closes = [float(c[4]) for c in result]
        if len(closes) < 2:
            return None
        returns   = [(closes[i] / closes[i-1] - 1) for i in range(1, len(closes))]
        mean      = sum(returns) / len(returns)
        variance  = sum((r - mean) ** 2 for r in returns) / len(returns)
        hourly_sd = math.sqrt(variance)
        daily_vol = hourly_sd * math.sqrt(24)
        return daily_vol
    except Exception:
        return None


def volatility_adjusted_size(max_size, asset="BTC"):
    """
    Scale position size by volatility.
    Target risk: 2% of position swings 1 daily-vol unit.
    High vol → smaller size. Low vol → full size.
    """
    vol = get_24h_volatility(asset)
    if vol is None or vol <= 0:
        return max_size
    target_vol = 0.02   # 2% daily vol = "normal"
    scale      = min(1.0, target_vol / vol)
    return round(max_size * scale, 2)


# =============================================================================
# Fee-Accurate EV
# =============================================================================

def fee_adjusted_breakeven(entry_price, fee_rate):
    """
    Calculate exact win-rate breakeven after Polymarket fee.
    win_profit   = (1 - entry_price) * (1 - fee_rate)
    breakeven    = entry_price / (win_profit + entry_price)
    """
    win_profit = (1 - entry_price) * (1 - fee_rate)
    if win_profit + entry_price == 0:
        return 1.0
    return entry_price / (win_profit + entry_price)


def required_divergence(entry_price, fee_rate, buffer=0.05):
    """Minimum divergence above 50¢ needed to have positive EV."""
    be  = fee_adjusted_breakeven(entry_price, fee_rate)
    div = (be - 0.50) + buffer
    return max(div, cfg["entry_threshold"])  # never lower than entry_threshold


# =============================================================================
# Time-of-Day Filter
# =============================================================================

def is_low_liquidity_window():
    """Returns True if current UTC hour is in the low-liquidity block."""
    hour = datetime.now(timezone.utc).hour
    return hour in LOW_LIQ_HOURS


# =============================================================================
# Outcome Resolution (fetch real Polymarket result)
# =============================================================================

def resolve_trade_outcome(condition_id):
    """
    Fetch real resolution from Polymarket Gamma API.
    Returns "yes", "no", or None if still unresolved.
    """
    if not condition_id:
        return None
    url    = f"https://gamma-api.polymarket.com/markets?conditionId={condition_id}"
    result = _api(url)
    if not result or isinstance(result, dict):
        return None
    try:
        market = result[0] if isinstance(result, list) else result
        if not market.get("closed"):
            return None  # still live
        prices = json.loads(market.get("outcomePrices", "[]"))
        if not prices:
            return None
        yes_price = float(prices[0])
        return "yes" if yes_price > 0.95 else "no"
    except Exception:
        return None


def resolve_open_trades(ledger):
    """Fetch real outcomes for expired open trades and update ledger."""
    now = datetime.now(timezone.utc)
    resolved = 0
    for t in ledger["trades"]:
        if t.get("status") != "open":
            continue
        end_str = t.get("end_time")
        if not end_str:
            continue
        try:
            end_time = datetime.fromisoformat(end_str)
            if end_time.tzinfo is None:
                end_time = end_time.replace(tzinfo=timezone.utc)
        except Exception:
            continue
        if now < end_time + timedelta(minutes=1):
            continue  # give 1 min buffer for resolution to propagate
        outcome = resolve_trade_outcome(t.get("condition_id"))
        if outcome is None:
            continue  # not resolved yet
        fee_rate   = t.get("fee_rate", 0.10)
        entry_price= t.get("entry_price", 0.5)
        amount     = t.get("amount_usd", 0)
        won        = (outcome == t.get("side"))
        payout     = (amount / entry_price) * (1 - fee_rate) if won else 0
        pnl        = payout - amount
        t["status"]      = "won" if won else "lost"
        t["pnl"]         = round(pnl, 4)
        t["outcome"]     = outcome
        t["resolved_at"] = now.isoformat()
        if t.get("mode") == "paper":
            ledger["paper_balance"] += payout
        date = t.get("date", now.strftime("%Y-%m-%d"))
        if date in ledger["daily"]:
            ledger["daily"][date]["pnl"] = ledger["daily"][date].get("pnl", 0) + pnl
        resolved += 1
    if resolved:
        _save_ledger(ledger)
    return resolved


# =============================================================================
# Stats / Calibration Report
# =============================================================================

def show_stats(ledger):
    trades   = ledger["trades"]
    closed   = [t for t in trades if t.get("status") in ("won", "lost")]
    open_    = [t for t in trades if t.get("status") == "open"]
    live_    = [t for t in closed if t.get("mode") == "live"]
    paper_   = [t for t in closed if t.get("mode") == "paper"]

    def _stats_block(label, subset):
        if not subset:
            print(f"  {label}: no closed trades yet")
            return
        wins       = [t for t in subset if t.get("status") == "won"]
        total_pnl  = sum(t.get("pnl", 0) for t in subset)
        total_cost = sum(t.get("amount_usd", 0) for t in subset)
        win_rate   = len(wins) / len(subset) * 100
        roi        = total_pnl / total_cost * 100 if total_cost > 0 else 0
        avg_win    = sum(t["pnl"] for t in wins) / len(wins) if wins else 0
        losses     = [t for t in subset if t.get("status") == "lost"]
        avg_loss   = sum(t["pnl"] for t in losses) / len(losses) if losses else 0
        print(f"  {label}: {len(subset)} closed | "
              f"WR {win_rate:.1f}% | P&L ${total_pnl:+.2f} | ROI {roi:+.1f}%")
        print(f"    avg win ${avg_win:+.2f} | avg loss ${avg_loss:+.2f}")

    print("\n⚡ FastLoop Improved — Stats & Calibration")
    print("=" * 55)
    print(f"  Paper balance:     ${ledger.get('paper_balance', cfg['starting_balance']):.2f} "
          f"(started ${ledger['starting_balance']:.2f})")
    print(f"  Open trades:       {len(open_)}")
    _stats_block("Paper", paper_)
    _stats_block("Live",  live_)

    # Calibration: win rate by momentum band
    if closed:
        print("\n  📈 Calibration: win rate by momentum strength")
        bands = [(0, 0.5), (0.5, 1.0), (1.0, 1.5), (1.5, 2.0), (2.0, 99)]
        for lo, hi in bands:
            band = [t for t in closed if lo <= abs(t.get("momentum_pct", 0)) < hi]
            if not band:
                continue
            wins = sum(1 for t in band if t.get("status") == "won")
            wr   = wins / len(band) * 100
            flag = " ✅" if wr >= 63 else " ⚠️ " if wr >= 55 else " ❌"
            print(f"    {lo:.1f}–{hi:.1f}% mom: {len(band)} trades, WR {wr:.0f}%{flag}")
        print("    (Need ≥63% WR to profit after 10% fee)")

        # Calibration: by time of day
        print("\n  🕐 Calibration: win rate by UTC hour")
        hour_data = {}
        for t in closed:
            try:
                h = datetime.fromisoformat(t["timestamp"]).hour
                hour_data.setdefault(h, []).append(t)
            except Exception:
                pass
        for h in sorted(hour_data):
            grp  = hour_data[h]
            wins = sum(1 for t in grp if t.get("status") == "won")
            wr   = wins / len(grp) * 100
            flag = "✅" if wr >= 63 else "⚠️ " if wr >= 55 else "❌"
            print(f"    UTC {h:02d}:xx  {len(grp):>3} trades  WR {wr:.0f}%  {flag}")

    # Recent trades
    print("\n  🔁 Last 10 trades:")
    for t in reversed(trades[-10:]):
        icon  = {"open": "⏳", "won": "✅", "lost": "❌"}.get(t.get("status"), "?")
        pnl   = f"${t['pnl']:+.2f}" if t.get("pnl") is not None else "pending"
        mode  = "[P]" if t.get("mode") == "paper" else "[L]"
        mom   = f"{t.get('momentum_pct', 0):+.2f}%"
        print(f"    {icon}{mode} {t['timestamp'][:16]}  {t.get('side','?').upper():<3}  "
              f"${t.get('amount_usd', 0):.2f}  mom={mom}  → {pnl}")

    # Daily summary
    if ledger["daily"]:
        print("\n  📅 Last 7 days (UTC):")
        for date in sorted(ledger["daily"].keys())[-7:]:
            d = ledger["daily"][date]
            print(f"    {date}  trades={d['trades']}  "
                  f"spent=${d['spent']:.2f}  pnl=${d.get('pnl', 0):+.2f}")


# =============================================================================
# Trade Execution
# =============================================================================

def execute_trade(market_id, side, amount):
    try:
        result = get_client().trade(
            market_id=market_id, side=side, amount=amount, source=TRADE_SOURCE
        )
        return {
            "success":      result.success,
            "trade_id":     result.trade_id,
            "shares_bought":result.shares_bought,
            "error":        result.error,
            "simulated":    result.simulated,
        }
    except Exception as e:
        return {"error": str(e)}


def import_market(slug):
    url = f"https://polymarket.com/event/{slug}"
    try:
        result = get_client().import_market(url)
    except Exception as e:
        return None, str(e)
    if not result:
        return None, "No response"
    if result.get("error"):
        return None, result["error"]
    status    = result.get("status")
    market_id = result.get("market_id")
    if status in ("imported", "already_exists"):
        return market_id, None
    if status == "resolved":
        alts = result.get("active_alternatives", [])
        return None, f"Resolved. Alternative: {alts[0].get('id') if alts else 'none'}"
    return None, f"Unexpected status: {status}"


# =============================================================================
# Main Strategy
# =============================================================================

def run(dry_run=True, positions_only=False, show_config=False,
        smart_sizing=False, quiet=False):

    global _automaton_reported
    skip_reasons = []

    def log(msg, force=False):
        if not quiet or force:
            print(msg)

    def bail(summary, reason=None):
        """Early exit with automaton report."""
        global _automaton_reported
        if reason:
            skip_reasons.append(reason)
        if not quiet:
            print(f"📊 Summary: {summary}")
        if os.environ.get("AUTOMATON_MANAGED") and not _automaton_reported:
            print(json.dumps({"automaton": {
                "signals": 0, "trades_attempted": 0, "trades_executed": 0,
                "skip_reason": ", ".join(dict.fromkeys(skip_reasons)) or "no_signal"
            }}))
            _automaton_reported = True

    log("⚡ FastLoop Improved Trader")
    log("=" * 50)
    mode_label = "[DRY RUN — paper mode]" if dry_run else "[LIVE]"
    log(f"\n  {mode_label}")

    if show_config:
        log("\n⚙️  Current config:")
        for k, v in cfg.items():
            log(f"    {k}: {v}")
        log(f"\n  Config file: {os.path.join(os.path.dirname(__file__), 'config.json')}")
        return

    # Initialise Simmer client early to validate API key
    get_client(live=not dry_run)
    ledger = _load_ledger()

    if positions_only:
        log("\n📊 Simmer Positions (fast markets):")
        try:
            from dataclasses import asdict
            positions = [asdict(p) for p in get_client().get_positions()]
            sprint = [p for p in positions if "up or down" in (p.get("question", "") or "").lower()]
            if not sprint:
                log("  No open fast market positions")
            for p in sprint:
                log(f"  • {p.get('question', '')[:60]}")
                log(f"    YES:{p.get('shares_yes',0):.1f} | NO:{p.get('shares_no',0):.1f} | "
                    f"P&L:${p.get('pnl',0):.2f}")
        except Exception as e:
            log(f"  Error fetching positions: {e}")
        return

    log(f"\n⚙️  Config summary:")
    log(f"  Asset: {cfg['asset']} {cfg['window']} | "
        f"momentum ≥ {cfg['min_momentum_pct']}% | divergence ≥ {cfg['entry_threshold']} | "
        f"max ${MAX_POSITION_USD:.2f}")
    log(f"  Signals: momentum{'+ funding' if cfg['require_funding'] else ''}"
        f"{'+ orderbook' if cfg['require_orderbook'] else ''} | "
        f"time_filter={'on' if cfg['time_filter'] else 'off'} | "
        f"vol_sizing={'on' if cfg['vol_sizing'] else 'off'}")

    daily = _get_daily(ledger)
    remaining_budget = cfg["daily_budget"] - daily["spent"]
    log(f"  Budget: ${remaining_budget:.2f} remaining today (${daily['spent']:.2f}/${cfg['daily_budget']:.2f})")

    # ── Gate 0: Time-of-day filter ───────────────────────────────────────────
    if cfg["time_filter"] and is_low_liquidity_window():
        hour = datetime.now(timezone.utc).hour
        bail(f"Skip (low-liquidity UTC hour {hour:02d}:xx — set time_filter=false to override)",
             "low_liquidity_hour")
        return

    # ── Step 1: Discover & select market ────────────────────────────────────
    log(f"\n🔍 Discovering {cfg['asset']} {cfg['window']} fast markets...")
    markets = discover_fast_markets(cfg["asset"], cfg["window"])
    log(f"  Found {len(markets)} active markets")
    if not markets:
        bail("No markets available")
        return

    best, in_sweet_spot = select_best_market(markets)
    if not best:
        bail(f"No markets with >{cfg['min_time_remaining']}s remaining")
        return

    now       = datetime.now(timezone.utc)
    secs_left = (best["end_time"] - now).total_seconds()
    yes_price = best["yes_price"]
    fee_rate  = best["fee_rate_bps"] / 10000

    log(f"\n🎯 Market: {best['question']}")
    log(f"  Time left: {secs_left:.0f}s {'(sweet spot ✓)' if in_sweet_spot else '(fallback)'}")
    log(f"  YES price: ${yes_price:.3f} | Fee: {fee_rate:.0%}")

    # ── Step 2: Fetch momentum ───────────────────────────────────────────────
    log(f"\n📈 Signal 1 — Momentum ({cfg['signal_source']})...")
    mom = get_momentum_signal(cfg["asset"], cfg["signal_source"], cfg["lookback_minutes"])
    if not mom:
        bail("Failed to fetch price data", "price_fetch_failed")
        return

    momentum_pct = abs(mom["momentum_pct"])
    direction    = mom["direction"]
    log(f"  {cfg['asset']}: ${mom['price_now']:,.2f} (was ${mom['price_then']:,.2f})")
    log(f"  Momentum: {mom['momentum_pct']:+.3f}% | Vol ratio: {mom['volume_ratio']:.2f}x | "
        f"Direction: {direction.upper()}")

    if momentum_pct < cfg["min_momentum_pct"]:
        bail(f"Skip (momentum {momentum_pct:.3f}% < min {cfg['min_momentum_pct']}%)", "weak_momentum")
        return

    if cfg["volume_confidence"] and mom["volume_ratio"] < 0.5:
        bail(f"Skip (low volume: {mom['volume_ratio']:.2f}x avg)", "low_volume")
        return

    log(f"  ✓ Momentum gate passed")

    # ── Step 3: Funding rate ─────────────────────────────────────────────────
    funding_ok = True
    if cfg["require_funding"]:
        log(f"\n📉 Signal 2 — Funding rate...")
        funding = get_funding_signal(cfg["asset"])
        if funding.get("available"):
            rate_pct = (funding["rate"] or 0) * 100
            confirms = funding_confirms(funding, direction)
            log(f"  Rate: {rate_pct:+.4f}% | Bias: {funding['bias']} | "
                f"Confirms {direction.upper()}: {'✓' if confirms else '✗'}")
            if confirms is False:
                bail(f"Skip (funding rate opposes momentum: {funding['bias']} bias vs {direction} move)",
                     "funding_conflict")
                return
            if confirms is True:
                log(f"  ✓ Funding confirmation")
        else:
            log(f"  ⚠️  Funding rate unavailable — skipping this gate")
    else:
        log(f"  Signal 2 (funding): off")

    # ── Step 4: Order book ───────────────────────────────────────────────────
    ob_imbalance_val = None
    if cfg["require_orderbook"]:
        log(f"\n📊 Signal 3 — Order book imbalance...")
        ob = get_orderbook_signal(cfg["asset"])
        if ob.get("available") and ob.get("imbalance") is not None:
            ob_imbalance_val = ob["imbalance"]
            confirms = orderbook_confirms(ob, direction)
            log(f"  Imbalance: {ob['imbalance']:+.3f} | "
                f"Confirms {direction.upper()}: {'✓' if confirms else ('✗' if confirms is False else '?')}")
            if confirms is False:
                bail(f"Skip (order book opposes momentum: imbalance {ob['imbalance']:+.3f})",
                     "orderbook_conflict")
                return
            if confirms is True:
                log(f"  ✓ Order book confirmation")
        else:
            log(f"  ⚠️  Order book unavailable — skipping this gate")
    else:
        log(f"  Signal 3 (orderbook): off")

    # ── Step 5: Divergence + EV check ───────────────────────────────────────
    log(f"\n🧠 EV Analysis...")
    if direction == "up":
        side       = "yes"
        entry_price= yes_price
        divergence = 0.50 + cfg["entry_threshold"] - yes_price
        rationale  = f"{cfg['asset']} up {mom['momentum_pct']:+.3f}% but YES only ${yes_price:.3f}"
    else:
        side       = "no"
        entry_price= 1 - yes_price
        divergence = yes_price - (0.50 - cfg["entry_threshold"])
        rationale  = f"{cfg['asset']} down {mom['momentum_pct']:+.3f}% but YES still ${yes_price:.3f}"

    if divergence <= 0:
        bail(f"Skip (no divergence: {divergence:.3f} — market already priced in)",
             "no_divergence")
        return

    req_div    = required_divergence(entry_price, fee_rate, cfg["fee_buffer"])
    breakeven  = fee_adjusted_breakeven(entry_price, fee_rate)
    log(f"  Side: {side.upper()} | Entry: ${entry_price:.3f}")
    log(f"  Actual divergence:   {divergence:.3f}")
    log(f"  Required divergence: {req_div:.3f} (fee breakeven {breakeven:.1%} + {cfg['fee_buffer']:.2f} buffer)")

    if divergence < req_div:
        bail(f"Skip (divergence {divergence:.3f} < required {req_div:.3f} after {fee_rate:.0%} fee)",
             "insufficient_ev")
        return

    log(f"  ✓ EV gate passed (edge: {divergence - req_div:.3f} above threshold)", force=True)

    # ── Step 6: Position sizing ──────────────────────────────────────────────
    log(f"\n💰 Sizing...")
    if cfg["vol_sizing"] and cfg["signal_source"] == "binance":
        position_size = volatility_adjusted_size(MAX_POSITION_USD, cfg["asset"])
        vol = get_24h_volatility(cfg["asset"])
        log(f"  24h vol: {(vol or 0)*100:.2f}% | Vol-adjusted size: ${position_size:.2f}")
    else:
        position_size = MAX_POSITION_USD
        log(f"  Fixed size: ${position_size:.2f}")

    if smart_sizing:
        try:
            portfolio = get_client().get_portfolio()
            balance = getattr(portfolio, "balance_usdc", 0) or 0
            smart   = balance * SMART_SIZING_PCT
            position_size = min(position_size, smart)
            log(f"  Smart sizing (5% of ${balance:.2f}): ${smart:.2f} → using ${position_size:.2f}")
        except Exception:
            pass

    # Budget clamp
    position_size = min(position_size, remaining_budget)
    if position_size < 0.50:
        bail(f"Skip (position ${position_size:.2f} too small — daily budget ${remaining_budget:.2f} remaining)",
             "budget_exhausted")
        return

    # Min shares check
    if entry_price > 0 and (MIN_SHARES * entry_price) > position_size:
        bail(f"Skip (need ${MIN_SHARES * entry_price:.2f} for min {MIN_SHARES} shares, have ${position_size:.2f})",
             "position_too_small")
        return

    log(f"  Final size: ${position_size:.2f}", force=True)

    # ── Step 7: Signal summary ───────────────────────────────────────────────
    log(f"\n✅ All gates passed — TRADE", force=True)
    log(f"   {rationale}", force=True)
    log(f"   Divergence {divergence:.3f} | Momentum {momentum_pct:.3f}% | "
        f"Size ${position_size:.2f}", force=True)

    # ── Step 8: Import + Execute ─────────────────────────────────────────────
    log(f"\n🔗 Importing market to Simmer...", force=True)
    market_id, import_err = import_market(best["slug"])
    if not market_id:
        log(f"  ❌ Import failed: {import_err}", force=True)
        if os.environ.get("AUTOMATON_MANAGED"):
            print(json.dumps({"automaton": {
                "signals": 1, "trades_attempted": 1, "trades_executed": 0,
                "execution_errors": [str(import_err)[:120]]
            }}))
            _automaton_reported = True
        return

    log(f"  ✅ Market ID: {market_id[:16]}...", force=True)
    tag = "PAPER" if dry_run else "LIVE"
    log(f"  Placing {side.upper()} ${position_size:.2f} ({tag})...", force=True)
    result = execute_trade(market_id, side, position_size)

    trade_executed = 0
    if result and result.get("success"):
        shares    = result.get("shares_bought") or 0
        trade_id  = result.get("trade_id")
        simulated = result.get("simulated", dry_run)
        log(f"  ✅ {'[PAPER] ' if simulated else ''}Bought {shares:.1f} {side.upper()} "
            f"@ ${entry_price:.3f}", force=True)
        trade_executed = 1

        # Record in ledger
        trade_record = {
            "timestamp":     now.isoformat(),
            "date":          now.strftime("%Y-%m-%d"),
            "mode":          "paper" if simulated else "live",
            "asset":         cfg["asset"],
            "side":          side,
            "market":        best["question"],
            "slug":          best["slug"],
            "condition_id":  best.get("condition_id", ""),
            "end_time":      best["end_time"].isoformat() if best.get("end_time") else None,
            "entry_price":   entry_price,
            "amount_usd":    round(position_size, 2),
            "shares":        shares,
            "divergence":    round(divergence, 4),
            "momentum_pct":  round(mom["momentum_pct"], 4),
            "volume_ratio":  round(mom["volume_ratio"], 2),
            "ob_imbalance":  ob_imbalance_val,
            "fee_rate":      fee_rate,
            "trade_id":      trade_id,
            "status":        "open",
            "pnl":           None,
        }
        if simulated:
            _record_paper_trade(ledger, trade_record)
        else:
            # Live trade: update daily budget tracker
            daily = _get_daily(ledger)
            daily["spent"]  += position_size
            daily["trades"] += 1
            ledger["trades"].append(trade_record)
            _save_ledger(ledger)

    else:
        err = (result.get("error") if result else "No response") or "Unknown"
        log(f"  ❌ Trade failed: {err}", force=True)

    # Summary
    print(f"\n📊 Summary:")
    print(f"  Market:    {best['question'][:55]}")
    print(f"  Signal:    {direction.upper()} {momentum_pct:.3f}% | YES ${yes_price:.3f}")
    print(f"  Action:    {'PAPER' if dry_run else ('TRADED' if trade_executed else 'FAILED')} "
          f"{side.upper()} ${position_size:.2f}")

    if os.environ.get("AUTOMATON_MANAGED"):
        amount = round(position_size, 2) if trade_executed else 0
        report = {
            "signals": 1,
            "trades_attempted": 1,
            "trades_executed":  trade_executed,
            "amount_usd":       amount,
        }
        print(json.dumps({"automaton": report}))
        _automaton_reported = True


# =============================================================================
# CLI
# =============================================================================

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="FastLoop Improved Trader")
    parser.add_argument("--live",         action="store_true", help="Execute real trades")
    parser.add_argument("--dry-run",      action="store_true", help="Paper mode (default)")
    parser.add_argument("--positions",    action="store_true", help="Show Simmer positions")
    parser.add_argument("--config",       action="store_true", help="Show current config")
    parser.add_argument("--stats",        action="store_true", help="P&L and calibration report")
    parser.add_argument("--resolve",      action="store_true", help="Fetch real outcomes for open trades")
    parser.add_argument("--smart-sizing", action="store_true", help="Size by portfolio balance")
    parser.add_argument("--quiet", "-q",  action="store_true", help="Only print on trades/errors")
    parser.add_argument("--set",          action="append",     metavar="KEY=VALUE", help="Update config")
    args = parser.parse_args()

    if args.set:
        updates = {}
        for item in args.set:
            if "=" not in item:
                print(f"Invalid: {item}  →  use KEY=VALUE")
                sys.exit(1)
            key, val = item.split("=", 1)
            if key not in CONFIG_SCHEMA:
                print(f"Unknown key '{key}'. Valid: {', '.join(CONFIG_SCHEMA)}")
                sys.exit(1)
            t = CONFIG_SCHEMA[key]["type"]
            try:
                updates[key] = (val.lower() in ("true","1","yes")) if t == bool else t(val)
            except ValueError:
                print(f"Bad value for {key}: {val}")
                sys.exit(1)
        _update_config(updates)
        print(f"✅ Config updated: {json.dumps(updates)}")
        sys.exit(0)

    if args.stats:
        show_stats(_load_ledger())
        sys.exit(0)

    if args.resolve:
        ledger   = _load_ledger()
        resolved = resolve_open_trades(ledger)
        print(f"✅ Resolved {resolved} trade(s) against real Polymarket outcomes")
        if resolved:
            show_stats(ledger)
        sys.exit(0)

    run(
        dry_run=       not args.live,
        positions_only=args.positions,
        show_config=   args.config,
        smart_sizing=  args.smart_sizing,
        quiet=         args.quiet,
    )

    # Fallback automaton report for early exits not caught inside run()
    if os.environ.get("AUTOMATON_MANAGED") and not _automaton_reported:
        print(json.dumps({"automaton": {
            "signals": 0, "trades_attempted": 0, "trades_executed": 0,
            "skip_reason": "no_signal"
        }}))
