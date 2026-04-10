"""
MUESA v3.0 - Momentum Breakout System
Binance Futures | LONG Only | Structure + Volume + Breakout
"""

import os
import time
import math
import json
import logging
import sqlite3
import threading
from datetime import datetime, timezone

from dotenv import load_dotenv
load_dotenv(override=True)

import ccxt
import requests
from flask import Flask

# ─────────────────────────────────────────────
#  CONFIGURATION
# ─────────────────────────────────────────────

BINANCE_API_KEY    = os.getenv("BINANCE_API_KEY", "")
BINANCE_API_SECRET = os.getenv("BINANCE_API_SECRET", "")
TELEGRAM_TOKEN     = os.getenv("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID   = os.getenv("TELEGRAM_CHAT_ID", "")

# ── Scan
SCAN_INTERVAL_MIN    = 5
CANDLE_BUFFER_SEC    = 5
CANDLE_LIMIT         = 100

# ── Universe
VOLUME_FLOOR_USDT    = 50_000_000
SKIP_TOP_N_COINS     = 50
SCAN_BAND_SIZE       = 150

# ── Position
MAX_OPEN_POSITIONS   = 1
MAX_WATCHLIST        = 5
WALLET_ALLOC_PCT     = 0.25
LEVERAGE             = 5
MARGIN_MODE          = "ISOLATED"

# ── Breakout parameters
CONSOL_LOOKBACK_MIN  = 12       # min candles in consolidation zone
CONSOL_LOOKBACK_MAX  = 20       # max candles in consolidation zone
CONSOL_MAX_RANGE     = 0.06     # max range % for valid consolidation (6%)
CONSOL_MAX_RANGE_HARD= 0.08     # hard skip if range > 8%
BREAKOUT_MIN_PCT     = 0.005    # close must be ≥ 0.5% above range high
BREAKOUT_BODY_MIN    = 0.60     # breakout candle body ≥ 60% of range
UPPER_WICK_MAX_PCT   = 0.40     # skip if upper wick > 40% of candle range
VOLUME_SURGE_MIN     = 2.0      # hard minimum — below this → skip
VOLUME_SURGE_PREF    = 2.5      # preferred — 2x–2.5x treated as weak signal
CONSOL_PREF_MIN      = 0.03     # preferred range lower bound (3%)
CONSOL_PREF_MAX      = 0.05     # preferred range upper bound (5%)
MAX_ENTRY_DELAY      = 3        # max candles after breakout to still enter
MOVE_FILTER_1H_PCT   = 0.15     # skip if already moved ≥ 15% in last 1H

# ── Risk / Reward (structure-based SL)
SL_BUFFER_PCT        = 0.002    # SL placed 0.2% below range low
TP1_R                = 2.0      # TP1 at 2R → move SL to breakeven
TRAIL_CALLBACK_PCT   = 2.0      # TP2 trailing stop callback % (replaces fixed 4R)

# ── Guards
SL_COOLDOWN_HOURS    = 24
BTC_CRASH_1H_PCT     = 0.05
DASHBOARD_PORT       = 8080
DB_PATH              = "muesa.db"

SIGNAL_EXCLUDE = {
    "BTC/USDT:USDT", "ETH/USDT:USDT", "BNB/USDT:USDT", "SOL/USDT:USDT",
    "XRP/USDT:USDT", "ADA/USDT:USDT", "DOGE/USDT:USDT", "TRX/USDT:USDT",
    "TON/USDT:USDT", "LINK/USDT:USDT",
}

SESSIONS: dict[str, tuple[int, int]] = {
    "Asia":     (1,  4),
    "London":   (7,  10),
    "New York": (13, 16),
}

# ─────────────────────────────────────────────
#  LOGGING
# ─────────────────────────────────────────────

import sys

_file_handler   = logging.FileHandler("muesa.log", encoding="utf-8")
_stream_handler = logging.StreamHandler(sys.stdout)
try:
    sys.stdout.reconfigure(encoding="utf-8")
except AttributeError:
    pass

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[_file_handler, _stream_handler],
)
log = logging.getLogger("MUESA")

# ─────────────────────────────────────────────
#  STATE
# ─────────────────────────────────────────────

open_positions: dict[str, dict]  = {}
last_reset_day: int              = -1
current_session: str             = ""
sl_hit_symbols: dict[str, float] = {}
_current_scan_id: int            = -1
last_weekly_calc_day: int        = -1
trading_paused: bool             = False
scanning_paused: bool            = False

# ─────────────────────────────────────────────
#  DATABASE
# ─────────────────────────────────────────────

def init_db() -> None:
    conn = sqlite3.connect(DB_PATH)
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS scans (
            scan_id       INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp     TEXT,
            next_scan     TEXT,
            btc_trend     TEXT,
            btc_1h_change REAL,
            total_coins   INTEGER DEFAULT 0,
            signals_found INTEGER DEFAULT 0,
            trades_taken  INTEGER DEFAULT 0,
            session_name  TEXT
        );
        CREATE TABLE IF NOT EXISTS coin_scores (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            scan_id      INTEGER REFERENCES scans(scan_id),
            symbol       TEXT,
            direction    TEXT,
            total_score  REAL DEFAULT 0,
            volume_pts   REAL DEFAULT 0,
            rvol_ratio   REAL DEFAULT 0,
            final_score  REAL,
            rationale    TEXT,
            blocked      INTEGER DEFAULT 0,
            block_reason TEXT,
            entry_reasons TEXT
        );
        CREATE TABLE IF NOT EXISTS trades (
            trade_id      INTEGER PRIMARY KEY AUTOINCREMENT,
            scan_id       INTEGER REFERENCES scans(scan_id),
            timestamp     TEXT,
            symbol        TEXT,
            direction     TEXT DEFAULT 'LONG',
            entry_price   REAL,
            sl            REAL,
            tp1           REAL,
            tp2           REAL,
            qty           REAL,
            rvol          REAL,
            entry_reasons TEXT,
            status        TEXT DEFAULT 'open'
        );
        CREATE TABLE IF NOT EXISTS position_checks (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp     TEXT,
            symbol        TEXT,
            entry_price   REAL,
            current_price REAL,
            pnl_pct       REAL,
            pnl_usdt      REAL,
            position_size REAL
        );
        CREATE TABLE IF NOT EXISTS weekly_stats (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            week_start    TEXT,
            calculated_at TEXT,
            total_trades  INTEGER DEFAULT 0,
            win_rate      REAL DEFAULT 0,
            best_coin     TEXT
        );
        CREATE TABLE IF NOT EXISTS bot_state (
            key   TEXT PRIMARY KEY,
            value TEXT
        );
        INSERT OR IGNORE INTO bot_state (key,value) VALUES ('trading_paused','0');
        INSERT OR IGNORE INTO bot_state (key,value) VALUES ('scanning_paused','0');
        CREATE TABLE IF NOT EXISTS watchlist (
            id       INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol   TEXT UNIQUE NOT NULL,
            added_at TEXT
        );
    """)
    conn.commit()
    conn.close()

def _db_conn() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.execute("PRAGMA journal_mode=WAL")
    return conn

def db_create_scan(timestamp, next_scan, btc_trend, btc_1h_change, session_name) -> int:
    try:
        conn = _db_conn()
        cur  = conn.execute(
            "INSERT INTO scans (timestamp,next_scan,btc_trend,btc_1h_change,session_name)"
            " VALUES (?,?,?,?,?)",
            (timestamp, next_scan, btc_trend, round(btc_1h_change, 4), session_name),
        )
        scan_id = cur.lastrowid
        conn.commit(); conn.close()
        return scan_id
    except Exception as e:
        log.debug(f"db_create_scan: {e}"); return -1

def db_finish_scan(scan_id, total_coins, signals_found, trades_taken) -> None:
    try:
        conn = _db_conn()
        conn.execute(
            "UPDATE scans SET total_coins=?,signals_found=?,trades_taken=? WHERE scan_id=?",
            (total_coins, signals_found, trades_taken, scan_id),
        )
        conn.commit(); conn.close()
    except Exception as e:
        log.debug(f"db_finish_scan: {e}")

def db_log_coin(scan_id, symbol, details, blocked, block_reason="") -> int:
    try:
        entry_reasons = ", ".join(details.get("entry_reasons", []))
        rvol          = details.get("rvol_ratio", 0.0)
        conn = _db_conn()
        cur  = conn.execute(
            "INSERT INTO coin_scores "
            "(scan_id,symbol,direction,total_score,rvol_ratio,blocked,block_reason,entry_reasons)"
            " VALUES (?,?,?,?,?,?,?,?)",
            (scan_id, symbol, "LONG", round(rvol * 10, 2), round(rvol, 2),
             1 if blocked else 0, block_reason, entry_reasons),
        )
        row_id = cur.lastrowid
        conn.commit(); conn.close()
        return row_id
    except Exception as e:
        log.debug(f"db_log_coin: {e}"); return -1

def db_mark_signal(row_id, rationale) -> None:
    try:
        conn = _db_conn()
        conn.execute(
            "UPDATE coin_scores SET final_score=100, rationale=? WHERE id=?",
            (rationale, row_id),
        )
        conn.commit(); conn.close()
    except Exception as e:
        log.debug(f"db_mark_signal: {e}")

def db_log_trade(scan_id, symbol, entry, sl, tp1, tp2, qty, rvol, entry_reasons) -> int:
    try:
        conn = _db_conn()
        cur  = conn.execute(
            "INSERT INTO trades "
            "(scan_id,timestamp,symbol,entry_price,sl,tp1,tp2,qty,rvol,entry_reasons,status)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?)",
            (scan_id, datetime.now(timezone.utc).isoformat(),
             symbol, entry, sl, tp1, tp2, qty, rvol, entry_reasons, "open"),
        )
        trade_id = cur.lastrowid
        conn.commit(); conn.close()
        return trade_id
    except Exception as e:
        log.debug(f"db_log_trade: {e}"); return -1

def db_update_trade_status(symbol, status) -> None:
    try:
        conn = _db_conn()
        conn.execute(
            "UPDATE trades SET status=? WHERE symbol=? AND status='open'"
            " AND trade_id=(SELECT MAX(trade_id) FROM trades WHERE symbol=? AND status='open')",
            (status, symbol, symbol),
        )
        conn.commit(); conn.close()
    except Exception as e:
        log.debug(f"db_update_trade_status: {e}")

def db_log_position_check(symbol, entry_price, current_price, pnl_pct, pnl_usdt, qty) -> None:
    try:
        conn = _db_conn()
        conn.execute(
            "INSERT INTO position_checks "
            "(timestamp,symbol,entry_price,current_price,pnl_pct,pnl_usdt,position_size)"
            " VALUES (?,?,?,?,?,?,?)",
            (datetime.now(timezone.utc).isoformat(), symbol,
             round(entry_price, 8), round(current_price, 8),
             round(pnl_pct, 4), round(pnl_usdt, 4), round(qty, 6)),
        )
        conn.commit(); conn.close()
    except Exception as e:
        log.debug(f"db_log_position_check: {e}")

def db_get_state(key) -> str:
    try:
        conn = _db_conn()
        row  = conn.execute("SELECT value FROM bot_state WHERE key=?", (key,)).fetchone()
        conn.close()
        return row[0] if row else "0"
    except Exception:
        return "0"

def db_set_state(key, value) -> None:
    try:
        conn = _db_conn()
        conn.execute("INSERT OR REPLACE INTO bot_state (key,value) VALUES (?,?)", (key, value))
        conn.commit(); conn.close()
    except Exception as e:
        log.debug(f"db_set_state: {e}")

def db_get_watchlist() -> list[dict]:
    try:
        conn = _db_conn()
        rows = conn.execute("SELECT id,symbol,added_at FROM watchlist ORDER BY added_at DESC").fetchall()
        conn.close()
        return [{"id": r[0], "symbol": r[1], "added_at": r[2]} for r in rows]
    except Exception:
        return []

def db_add_watchlist(symbol) -> bool:
    try:
        conn = _db_conn()
        conn.execute(
            "INSERT OR IGNORE INTO watchlist (symbol, added_at) VALUES (?,?)",
            (symbol, datetime.now(timezone.utc).isoformat()),
        )
        changed = conn.execute("SELECT changes()").fetchone()[0]
        conn.commit(); conn.close()
        return changed > 0
    except Exception as e:
        log.debug(f"db_add_watchlist: {e}"); return False

def db_remove_watchlist(symbol) -> None:
    try:
        conn = _db_conn()
        conn.execute("DELETE FROM watchlist WHERE symbol=?", (symbol,))
        conn.commit(); conn.close()
    except Exception as e:
        log.debug(f"db_remove_watchlist: {e}")

def db_load_watchlist_symbols() -> set[str]:
    return {r["symbol"] for r in db_get_watchlist()}

def db_get_watchlist_status() -> list[dict]:
    items = db_get_watchlist()
    try:
        conn = _db_conn()
        for item in items:
            row = conn.execute("""
                SELECT cs.rvol_ratio, cs.final_score, s.timestamp, cs.entry_reasons, cs.block_reason, cs.blocked
                FROM coin_scores cs LEFT JOIN scans s ON cs.scan_id = s.scan_id
                WHERE cs.symbol=? ORDER BY cs.id DESC LIMIT 1
            """, (item["symbol"],)).fetchone()
            if row:
                item["last_rvol"]    = row[0] or 0
                item["last_final"]   = row[1] or 0
                item["last_scan"]    = (row[2] or "")[:19].replace("T", " ")
                item["last_reasons"] = row[3] or ""
                item["last_blocked"] = bool(row[5])
                item["block_reason"] = row[4] or ""
            else:
                item.update({"last_rvol": 0, "last_final": 0, "last_scan": "Not scanned",
                             "last_reasons": "", "last_blocked": False, "block_reason": ""})
        conn.close()
    except Exception:
        pass
    return items

def load_bot_state() -> None:
    global trading_paused, scanning_paused
    trading_paused  = db_get_state("trading_paused")  == "1"
    scanning_paused = db_get_state("scanning_paused") == "1"
    if trading_paused:  log.info("Bot state restored: TRADING PAUSED")
    if scanning_paused: log.info("Bot state restored: SCANNING PAUSED")

def db_calc_weekly_stats() -> None:
    try:
        conn = _db_conn()
        conn.row_factory = sqlite3.Row
        week_start = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        rows       = conn.execute("SELECT * FROM trades WHERE timestamp >= date('now','-7 days')").fetchall()
        if not rows:
            conn.close(); return
        total    = len(rows)
        wins     = sum(1 for r in rows if r["status"] in ("tp1_hit", "tp2_hit"))
        win_rate = round(wins / total * 100, 1) if total else 0
        coin_wins: dict[str, int] = {}
        for r in rows:
            if r["status"] in ("tp1_hit", "tp2_hit"):
                coin_wins[r["symbol"]] = coin_wins.get(r["symbol"], 0) + 1
        best_coin = max(coin_wins, key=coin_wins.get) if coin_wins else "N/A"
        conn.execute(
            "INSERT INTO weekly_stats (week_start,calculated_at,total_trades,win_rate,best_coin)"
            " VALUES (?,?,?,?,?)",
            (week_start, datetime.now(timezone.utc).isoformat(), total, win_rate, best_coin),
        )
        conn.commit(); conn.close()
        log.info(f"Weekly stats: {total} trades | win_rate={win_rate}% | best={best_coin}")
    except Exception as e:
        log.error(f"db_calc_weekly_stats: {e}")

# ─────────────────────────────────────────────
#  FLASK DASHBOARD
# ─────────────────────────────────────────────

_flask_app = Flask(__name__)

def _db_fetch(query, params=()):
    try:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        rows = conn.execute(query, params).fetchall()
        conn.close()
        return [dict(r) for r in rows]
    except Exception:
        return []

@_flask_app.route("/")
def dashboard() -> str:
    scan      = (_db_fetch("SELECT * FROM scans ORDER BY scan_id DESC LIMIT 1") or [{}])[0]
    signals   = _db_fetch(
        "SELECT cs.*, s.timestamp AS ts FROM coin_scores cs "
        "LEFT JOIN scans s ON cs.scan_id=s.scan_id "
        "WHERE cs.blocked=0 AND cs.final_score IS NOT NULL "
        "ORDER BY cs.id DESC LIMIT 30"
    )
    trades    = _db_fetch("SELECT * FROM trades ORDER BY trade_id DESC LIMIT 20")
    blocked   = _db_fetch(
        "SELECT cs.*, s.timestamp AS ts FROM coin_scores cs "
        "LEFT JOIN scans s ON cs.scan_id=s.scan_id "
        "WHERE cs.blocked=1 AND cs.block_reason NOT IN ('signal_exclusion','open_position','sl_cooldown') "
        "ORDER BY cs.id DESC LIMIT 50"
    )
    weekly    = (_db_fetch("SELECT * FROM weekly_stats ORDER BY id DESC LIMIT 1") or [{}])[0]
    watchlist = db_get_watchlist_status()
    top_coins = _db_fetch(
        "SELECT symbol, COUNT(*) AS cnt FROM coin_scores "
        "WHERE blocked=0 AND final_score IS NOT NULL "
        "GROUP BY symbol ORDER BY cnt DESC LIMIT 10"
    )
    today_utc   = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    trade_today = len([t for t in trades if (t.get("timestamp") or "").startswith(today_utc)])

    def fmt_ts(ts):
        if not ts: return "—"
        try: return ts[11:19] + " UTC"
        except: return ts

    def status_badge(s):
        c = {"open": "#58a6ff", "tp1_hit": "#2ea043", "tp2_hit": "#2ea043",
             "sl_hit": "#da3633", "closed": "#8b949e"}.get(s, "#8b949e")
        return f'<span style="background:{c}22;color:{c};padding:2px 7px;border-radius:4px;font-size:11px">{s}</span>'

    signals_rows = "".join(
        f'<tr style="background:#1a3a1a">'
        f'<td>{fmt_ts(r.get("ts",""))}</td>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td style="color:#2ea043">LONG ⚡</td>'
        f'<td style="color:#58a6ff">{r.get("rvol_ratio",0):.1f}x</td>'
        f'<td style="color:#8b949e;font-size:11px">{r.get("entry_reasons","")}</td>'
        f'</tr>'
        for r in signals
    ) or '<tr><td colspan="5" style="text-align:center;color:#8b949e;padding:20px">No signals yet</td></tr>'

    trades_rows = "".join(
        f'<tr style="background:#1a3a1a">'
        f'<td>{fmt_ts(r.get("timestamp",""))}</td>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td>{r["entry_price"]}</td>'
        f'<td style="color:#da3633">{r["sl"]}</td>'
        f'<td style="color:#2ea043">{r["tp1"]}</td>'
        f'<td style="color:#2ea043">{r["tp2"]}</td>'
        f'<td>{r["qty"]}</td>'
        f'<td style="color:#58a6ff">{r.get("rvol",0):.1f}x</td>'
        f'<td>{status_badge(r.get("status","open"))}</td>'
        f'</tr>'
        for r in trades
    ) or '<tr><td colspan="9" style="text-align:center;color:#8b949e;padding:20px">No trades yet</td></tr>'

    blocked_rows = "".join(
        f'<tr><td>{fmt_ts(r.get("ts",""))}</td>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td style="color:#da3633;font-size:12px">{r.get("block_reason","")}</td></tr>'
        for r in blocked
    ) or '<tr><td colspan="3" style="text-align:center;color:#8b949e;padding:20px">No blocks</td></tr>'

    top_rows = "".join(
        f'<tr><td><b>{r["symbol"]}</b></td><td style="color:#58a6ff">{r["cnt"]}</td></tr>'
        for r in top_coins
    ) or '<tr><td colspan="2" style="text-align:center;color:#8b949e;padding:20px">Not enough data</td></tr>'

    def wl_slot(items, idx):
        base = "background:#161b22;border:1px solid #30363d;border-radius:8px;padding:14px 16px;margin-bottom:10px"
        if idx < len(items):
            r   = items[idx]
            sym = r["symbol"]
            col = "#2ea043" if r.get("last_final", 0) > 0 and not r.get("last_blocked") else "#8b949e"
            lbl = "Signal Fired!" if r.get("last_final", 0) > 0 and not r.get("last_blocked") else (r.get("block_reason") or "Monitoring")
            return (
                f'<div style="{base};border-left:3px solid {col}">'
                f'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px">'
                f'  <span style="font-weight:bold;color:#58a6ff">Slot {idx+1}</span>'
                f'  <b style="color:#c9d1d9">{sym}</b>'
                f'  <form method="POST" action="/watchlist/remove" style="margin:0">'
                f'    <input type="hidden" name="symbol" value="{sym}">'
                f'    <button style="background:#3d1010;border:1px solid #da3633;color:#da3633;border-radius:5px;padding:3px 10px;cursor:pointer;font-size:11px">Remove</button>'
                f'  </form>'
                f'</div>'
                f'<div style="font-size:12px;color:#8b949e">Last: {r.get("last_scan","—")} | '
                f'RVOL: {r.get("last_rvol",0):.1f}x | <span style="color:{col}">{lbl}</span></div>'
                f'<div style="font-size:11px;color:#8b949e;margin-top:4px">{r.get("last_reasons","")}</div>'
                f'</div>'
            )
        return (
            f'<div style="{base};border-left:3px solid #21262d;opacity:0.7">'
            f'<div style="display:flex;align-items:center;gap:8px">'
            f'  <span style="font-size:14px;color:#8b949e">Slot {idx+1} — Empty</span>'
            f'  <form method="POST" action="/watchlist/add" style="display:flex;gap:6px;margin:0">'
            f'    <input name="symbol" placeholder="e.g. NOM or SOLUSDT" style="background:#0d1117;border:1px solid #30363d;color:#c9d1d9;padding:5px 10px;border-radius:5px;font-size:12px;width:180px">'
            f'    <button type="submit" style="background:#1f6feb;border:none;color:#fff;border-radius:5px;padding:5px 14px;cursor:pointer;font-size:12px">+ Add</button>'
            f'  </form>'
            f'</div></div>'
        )

    w = weekly
    html = f"""<!DOCTYPE html><html lang="en"><head>
<meta charset="UTF-8"><meta http-equiv="refresh" content="30">
<title>MUESA v3.0 — Momentum Breakout</title>
<style>
  *{{margin:0;padding:0;box-sizing:border-box}}
  body{{background:#0d1117;color:#c9d1d9;font-family:'Segoe UI',system-ui,monospace;font-size:14px}}
  h1{{font-size:22px;color:#58a6ff;padding:20px 24px 4px}}
  .sub{{color:#8b949e;padding:0 24px 16px;font-size:13px}}
  .grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(175px,1fr));gap:12px;padding:0 24px 20px}}
  .card{{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:14px 16px}}
  .card .label{{color:#8b949e;font-size:11px;text-transform:uppercase;letter-spacing:1px;margin-bottom:6px}}
  .card .value{{font-size:22px;font-weight:bold;color:#58a6ff;line-height:1.2}}
  .card .sub-val{{font-size:12px;color:#8b949e;margin-top:3px}}
  section{{padding:0 24px 24px}}
  h2{{font-size:14px;color:#8b949e;text-transform:uppercase;letter-spacing:1px;margin-bottom:10px;border-bottom:1px solid #21262d;padding-bottom:6px}}
  table{{width:100%;border-collapse:collapse;background:#161b22;border-radius:8px;overflow:hidden;border:1px solid #30363d}}
  th{{background:#21262d;color:#8b949e;font-size:11px;text-transform:uppercase;padding:7px 10px;text-align:left;white-space:nowrap}}
  td{{padding:7px 10px;border-bottom:1px solid #21262d;font-size:13px}}
  .btn{{background:#21262d;border:1px solid #30363d;color:#c9d1d9;padding:6px 14px;border-radius:6px;cursor:pointer;font-size:13px}}
  .btn.pause{{background:#3d2200;border-color:#d29922;color:#d29922}}
  .btn.stop{{background:#3d1010;border-color:#da3633;color:#da3633}}
  .two-col{{display:grid;grid-template-columns:1fr 1fr;gap:20px;padding:0 24px 24px}}
  @media(max-width:800px){{.two-col{{grid-template-columns:1fr}}}}
</style></head><body>
<h1>⚡ MUESA v3.0 — Momentum Breakout</h1>
<p class="sub">LONG Only · No AI · No Scoring · Structure + Volume + Breakout · 15m</p>
<div class="grid">
  <div class="card"><div class="label">Strategy</div><div class="value" style="font-size:13px;color:#2ea043">Momentum Breakout</div><div class="sub-val">RVOL≥{VOLUME_SURGE_MIN}x (pref≥{VOLUME_SURGE_PREF}x) · Range 3–5% · TP1={TP1_R:.0f}R+Trail</div></div>
  <div class="card"><div class="label">Open Positions</div><div class="value {'green' if open_positions else ''}">{len(open_positions)}/{MAX_OPEN_POSITIONS}</div><div class="sub-val">{'Active: ' + ', '.join(open_positions.keys()) if open_positions else 'Idle'}</div></div>
  <div class="card"><div class="label">Today's Trades</div><div class="value">{trade_today}</div><div class="sub-val">Total: {len(trades)}</div></div>
  <div class="card"><div class="label">Session</div><div class="value" style="font-size:16px">{current_session or 'Off-Hours'}</div><div class="sub-val">BTC 1H: {scan.get('btc_1h_change',0):+.2f}%</div></div>
  <div class="card"><div class="label">Win Rate (7d)</div><div class="value">{w.get('win_rate','—')}%</div><div class="sub-val">Trades: {w.get('total_trades','—')}</div></div>
  <div class="card"><div class="label">Best Coin (7d)</div><div class="value" style="font-size:16px">{w.get('best_coin','—')}</div><div class="sub-val">Top performer</div></div>
  <div class="card"><div class="label">Last Scan</div><div class="value" style="font-size:13px">{fmt_ts(scan.get('timestamp',''))}</div><div class="sub-val">Next: {fmt_ts(scan.get('next_scan',''))}</div></div>
  <div class="card"><div class="label">Signals Found</div><div class="value">{scan.get('signals_found',0)}</div><div class="sub-val">Coins scanned: {scan.get('total_coins',0)}</div></div>
</div>
<section style="padding:0 24px 12px">
  <div style="display:flex;gap:10px;flex-wrap:wrap">
    <form method="POST" action="/toggle_trading">
      <button class="btn {'pause' if trading_paused else ''}">{'▶ Resume Trading' if trading_paused else '⏸ Pause Trading'}</button>
    </form>
    <form method="POST" action="/toggle_scanning">
      <button class="btn {'stop' if scanning_paused else ''}">{'▶ Resume Scanning' if scanning_paused else '⏹ Pause Scanning'}</button>
    </form>
  </div>
</section>
<section>
  <h2>Breakout Signals (last 30)</h2>
  <table><tr><th>Time</th><th>Symbol</th><th>Dir</th><th>RVOL</th><th>Conditions</th></tr>
  {signals_rows}</table>
</section>
<section>
  <h2>Trades Executed (last 20)</h2>
  <table><tr><th>Time</th><th>Symbol</th><th>Entry</th><th>SL</th><th>TP1 (2R)</th><th>TP2 (4R)</th><th>Qty</th><th>RVOL</th><th>Status</th></tr>
  {trades_rows}</table>
</section>
<section>
  <h2>Watchlist ({len(watchlist)}/{MAX_WATCHLIST} slots)</h2>
  {"".join(wl_slot(watchlist, i) for i in range(MAX_WATCHLIST))}
</section>
<div class="two-col">
  <section style="padding:0">
    <h2>Blocked Coins (last 50)</h2>
    <table><tr><th>Time</th><th>Symbol</th><th>Block Reason</th></tr>{blocked_rows}</table>
  </section>
  <section style="padding:0">
    <h2>Top Breakout Coins</h2>
    <table><tr><th>Symbol</th><th>Signal Count</th></tr>{top_rows}</table>
  </section>
</div>
</body></html>"""
    return html

@_flask_app.route("/toggle_trading", methods=["POST"])
def toggle_trading():
    global trading_paused
    trading_paused = not trading_paused
    db_set_state("trading_paused", "1" if trading_paused else "0")
    state = "PAUSED" if trading_paused else "RESUMED"
    log.info(f"Trading {state} via dashboard.")
    send_telegram(f"*MUESA — Trading {state}*\n{'No new trades.' if trading_paused else 'Execution active.'}")
    return ("", 204)

@_flask_app.route("/toggle_scanning", methods=["POST"])
def toggle_scanning():
    global scanning_paused
    scanning_paused = not scanning_paused
    db_set_state("scanning_paused", "1" if scanning_paused else "0")
    state = "PAUSED" if scanning_paused else "RESUMED"
    log.info(f"Scanning {state} via dashboard.")
    send_telegram(f"*MUESA — Scanning {state}*")
    return ("", 204)

@_flask_app.route("/watchlist/add", methods=["POST"])
def watchlist_add():
    from flask import request as _req
    raw = (_req.form.get("symbol") or "").strip().upper()
    if not raw: return ("", 204)
    if raw.endswith("/USDT:USDT"):  symbol = raw
    elif raw.endswith("USDT"):      symbol = f"{raw[:-4]}/USDT:USDT"
    else:                           symbol = f"{raw}/USDT:USDT"
    if len(db_get_watchlist()) >= MAX_WATCHLIST:
        return ("Watchlist full", 400)
    if db_add_watchlist(symbol):
        log.info(f"Watchlist: added {symbol}")
        send_telegram(f"📋 *Watchlist* — Added `{symbol}`")
    return ("", 204)

@_flask_app.route("/watchlist/remove", methods=["POST"])
def watchlist_remove():
    from flask import request as _req
    symbol = (_req.form.get("symbol") or "").strip()
    if symbol:
        db_remove_watchlist(symbol)
        log.info(f"Watchlist: removed {symbol}")
        send_telegram(f"📋 *Watchlist* — Removed `{symbol}`")
    return ("", 204)

def start_dashboard() -> None:
    import logging as _lg
    _lg.getLogger("werkzeug").setLevel(_lg.ERROR)
    t = threading.Thread(
        target=lambda: _flask_app.run(host="0.0.0.0", port=DASHBOARD_PORT, debug=False, use_reloader=False),
        daemon=True,
    )
    t.start()
    log.info(f"Dashboard running at http://0.0.0.0:{DASHBOARD_PORT}")

# ─────────────────────────────────────────────
#  TELEGRAM
# ─────────────────────────────────────────────

def send_telegram(message: str) -> None:
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        log.warning("Telegram not configured — skipping alert.")
        return
    try:
        resp = requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            json={"chat_id": TELEGRAM_CHAT_ID, "text": message, "parse_mode": "Markdown"},
            timeout=10,
        )
        resp.raise_for_status()
    except Exception as e:
        log.error(f"Telegram failed: {e}")

# ─────────────────────────────────────────────
#  EXCHANGE
# ─────────────────────────────────────────────

def create_exchange() -> ccxt.binanceusdm:
    exchange = ccxt.binanceusdm({
        "apiKey": BINANCE_API_KEY,
        "secret": BINANCE_API_SECRET,
        "enableRateLimit": True,
        "options": {"defaultType": "future", "adjustForTimeDifference": True},
    })
    exchange.set_sandbox_mode(False)
    return exchange

# ─────────────────────────────────────────────
#  TIMING / SESSION
# ─────────────────────────────────────────────

def next_candle_close_utc() -> datetime:
    interval = SCAN_INTERVAL_MIN * 60
    now_ts   = time.time()
    close_ts = now_ts + (interval - now_ts % interval)
    return datetime.fromtimestamp(close_ts, tz=timezone.utc)

def seconds_until_scan() -> float:
    interval = SCAN_INTERVAL_MIN * 60
    return (interval - time.time() % interval) + CANDLE_BUFFER_SEC

def get_active_session(now: datetime) -> str | None:
    for name, (start, end) in SESSIONS.items():
        if start <= now.hour < end:
            return name
    return None

# ─────────────────────────────────────────────
#  BTC CRASH GUARD
# ─────────────────────────────────────────────

def get_btc_crash(exchange: ccxt.binanceusdm) -> dict:
    ctx: dict = {"crash": False, "change_1h_pct": 0.0}
    try:
        ohlcv = exchange.fetch_ohlcv("BTC/USDT:USDT", "1h", limit=3)
        if len(ohlcv) >= 2:
            change = (float(ohlcv[-1][4]) - float(ohlcv[-2][4])) / float(ohlcv[-2][4])
            ctx["change_1h_pct"] = round(change * 100, 3)
            if change <= -BTC_CRASH_1H_PCT:
                ctx["crash"] = True
    except Exception as e:
        log.error(f"BTC crash check failed: {e}")
    return ctx

# ─────────────────────────────────────────────
#  SIGNAL DETECTION — MOMENTUM BREAKOUT
# ─────────────────────────────────────────────

def detect_consolidation(ohlcv_15m: list) -> tuple[bool, float, float, float, str]:
    """
    Find the tightest valid consolidation in the last 12–20 candles.
    Excludes the last 3 candles (potential breakout area).

    Range tiers:
      > 8%       → hard skip
      6–8%       → valid but weak  (quality=0.5)
      3–5%       → preferred tight (quality=1.0)
      < 3%       → too tight, may be noise — still valid (quality=0.8)

    Returns (found, range_high, range_low, range_pct, desc).
    Picks the setup with the best quality score (tightest preferred range wins).
    """
    n = len(ohlcv_15m)
    if n < CONSOL_LOOKBACK_MIN + 5:
        return False, 0.0, 0.0, 0.0, "insufficient data"

    best: tuple | None = None   # (range_high, range_low, range_pct, lookback, quality)

    for lookback in range(CONSOL_LOOKBACK_MIN, min(CONSOL_LOOKBACK_MAX + 1, n - 2)):
        candles = ohlcv_15m[-(lookback + 3):-3]
        if len(candles) < CONSOL_LOOKBACK_MIN:
            continue

        range_high = max(float(c[2]) for c in candles)
        range_low  = min(float(c[3]) for c in candles)
        if range_low <= 0:
            continue

        range_pct = (range_high - range_low) / range_low

        if range_pct > CONSOL_MAX_RANGE_HARD:   # > 8% → hard skip
            continue
        if range_pct > CONSOL_MAX_RANGE:        # 6–8% → skip
            continue

        # Quality scoring — prefer 3–5%
        if CONSOL_PREF_MIN <= range_pct <= CONSOL_PREF_MAX:
            quality = 1.0   # ideal tight range
        elif range_pct < CONSOL_PREF_MIN:
            quality = 0.8   # very tight — valid but may be noise
        else:
            quality = 0.5   # 5–6% — allowed but weak

        if best is None or quality > best[4] or (quality == best[4] and range_pct < best[2]):
            best = (range_high, range_low, range_pct, lookback, quality)

    if best:
        rh, rl, rp, lb, q = best
        tier = "tight" if q == 1.0 else ("v.tight" if q == 0.8 else "loose")
        return True, rh, rl, rp, f"Structure {lb}c range={rp:.1%} [{tier}]"

    return False, 0.0, 0.0, 0.0, "no consolidation found"


def detect_breakout(ohlcv_15m: list, range_high: float) -> tuple[bool, int, str]:
    """
    Look for a valid breakout candle in the last MAX_ENTRY_DELAY candles.
    Conditions: close ≥ 0.5% above range_high · body ≥ 60% · upper wick ≤ 40% · bullish.
    Returns (found, candle_offset, desc).  offset=1 → last closed candle.
    """
    for offset in range(1, MAX_ENTRY_DELAY + 1):
        if len(ohlcv_15m) < offset + 2:
            break

        c     = ohlcv_15m[-offset]
        open_ = float(c[1]); high = float(c[2])
        low   = float(c[3]); close = float(c[4])

        if close <= open_:          # must be bullish
            continue

        rng = high - low
        if rng <= 0:
            continue

        body_pct       = abs(close - open_) / rng
        upper_wick_pct = (high - close) / rng

        if upper_wick_pct > UPPER_WICK_MAX_PCT:     # wick > 40% → weak
            continue

        if range_high <= 0:
            continue

        breakout_pct = (close - range_high) / range_high
        if breakout_pct < BREAKOUT_MIN_PCT:         # < 0.5% above range
            continue

        if body_pct < BREAKOUT_BODY_MIN:            # body < 60%
            continue

        return True, offset, f"Breakout +{breakout_pct:.1%} body={body_pct:.0%} delay={offset}c"

    return False, 0, "no valid breakout in last 3 candles"


def check_volume_surge(ohlcv_15m: list, bo_offset: int) -> tuple[bool, float, str]:
    """
    Compare volume at the breakout candle to the 20-period avg before it.
    Hard minimum: 2x. Preferred: 2.5x+.
    Returns (passed, rvol_ratio, tier).
      tier = "strong" (≥2.5x) | "weak" (2–2.5x) | "fail" (<2x)
    """
    n = len(ohlcv_15m)
    if n < bo_offset + 22:
        return False, 0.0, "fail"

    volumes = [float(c[5]) for c in ohlcv_15m]
    bo_vol  = volumes[-bo_offset]
    base    = volumes[-(bo_offset + 20):-bo_offset]
    avg_vol = sum(base) / len(base) if base else 0.0

    if avg_vol <= 0:
        return False, 0.0, "fail"

    rvol = round(bo_vol / avg_vol, 2)

    if rvol < VOLUME_SURGE_MIN:
        return False, rvol, "fail"

    tier = "strong" if rvol >= VOLUME_SURGE_PREF else "weak"
    return True, rvol, tier


def check_1h_move(exchange: ccxt.binanceusdm, symbol: str) -> tuple[bool, float]:
    """
    Skip if price already moved ≥ 15% in the last 1H (late entry).
    Returns (should_skip, move_pct).
    """
    try:
        ohlcv = exchange.fetch_ohlcv(symbol, "1h", limit=2)
        if ohlcv:
            c = ohlcv[-1]
            open_1h, close_1h = float(c[1]), float(c[4])
            if open_1h > 0:
                move = abs(close_1h - open_1h) / open_1h
                return move >= MOVE_FILTER_1H_PCT, round(move * 100, 2)
    except Exception:
        pass
    return False, 0.0


def compute_breakout_signal(
    exchange: ccxt.binanceusdm,
    symbol: str,
    vol_24h: float,
    ohlcv_15m: list,
) -> tuple[bool, dict]:
    """
    LONG-only momentum breakout signal.

    Order of checks:
      1. 1H move filter  — skip if ≥ 15% already moved (late entry guard)
      2. Consolidation   — 12–20 candles, range ≤ 6% (prefer 3–5%)
      3. Breakout candle — within last 3 candles, close ≥ 0.5% above range,
                           body ≥ 60%, upper wick ≤ 40%
      4. Volume surge    — ≥ 2x hard min (prefer ≥ 2.5x)

    Priority score (0–2): used to rank signals when multiple fire same scan.
      +1 if volume ≥ 2.5x (strong)
      +1 if range 3–5% (tight)

    TP1 = 2R (fixed), TP2 = trailing stop (TRAIL_CALLBACK_PCT%).
    Returns (passed, details).
    """
    details: dict = {"direction": "LONG", "blocks": [], "entry_reasons": [], "vol_24h": vol_24h}

    if len(ohlcv_15m) < 30:
        details["blocks"].append("insufficient candle data")
        return False, details

    # 1. 1H move filter — skip if ≥ 15% already moved
    skip_1h, move_1h = check_1h_move(exchange, symbol)
    details["move_1h_pct"] = move_1h
    if skip_1h:
        details["blocks"].append(f"Already moved {move_1h:.1f}% in 1H — late entry")
        return False, details

    # 2. Consolidation (structure)
    consol_ok, range_high, range_low, range_pct, consol_desc = detect_consolidation(ohlcv_15m)
    details["range_high"] = round(range_high, 8)
    details["range_low"]  = round(range_low, 8)
    details["range_pct"]  = round(range_pct * 100, 2)
    if not consol_ok:
        details["blocks"].append(f"No structure: {consol_desc}")
        return False, details
    details["entry_reasons"].append(consol_desc)

    # 3. Breakout candle — must be within last MAX_ENTRY_DELAY (3) candles
    bo_ok, bo_offset, bo_desc = detect_breakout(ohlcv_15m, range_high)
    details["bo_offset"] = bo_offset
    if not bo_ok:
        details["blocks"].append(f"No valid breakout in last {MAX_ENTRY_DELAY} candles")
        return False, details
    details["entry_reasons"].append(bo_desc)

    # 4. Volume surge — ≥ 2x hard min, prefer ≥ 2.5x
    vol_ok, rvol, vol_tier = check_volume_surge(ohlcv_15m, bo_offset)
    details["rvol_ratio"] = rvol
    details["vol_tier"]   = vol_tier
    if not vol_ok:
        details["blocks"].append(f"Volume too low RVOL={rvol:.2f}x (min {VOLUME_SURGE_MIN}x)")
        return False, details
    vol_label = f"Volume {rvol:.1f}x ({'strong' if vol_tier == 'strong' else 'weak — prefer ≥2.5x'})"
    details["entry_reasons"].append(vol_label)

    # Calculate SL (structure-based) and TP
    price    = float(ohlcv_15m[-1][4])
    sl_price = round(range_low * (1 - SL_BUFFER_PCT), 8)
    R        = price - sl_price

    if R <= 0:
        details["blocks"].append("Invalid R — price at or below SL")
        return False, details

    tp1_price = round(price + TP1_R * R, 8)
    # TP2 = trailing stop — no fixed price target, callback set at execution

    details["price"]      = round(price, 8)
    details["sl"]         = sl_price
    details["tp1"]        = tp1_price
    details["tp2"]        = None          # trailing — no fixed level
    details["R"]          = round(R, 8)
    details["sl_pct"]     = round((price - sl_price) / price * 100, 2)
    details["tp1_pct"]    = round((tp1_price - price) / price * 100, 2)
    details["size_mult"]  = 1.0

    # Priority score for execution ranking (higher = better setup)
    priority = 0
    if vol_tier == "strong":                                    # ≥ 2.5x volume
        priority += 1
    if CONSOL_PREF_MIN <= range_pct <= CONSOL_PREF_MAX:        # 3–5% tight range
        priority += 1
    details["priority"] = priority

    return True, details

# ─────────────────────────────────────────────
#  POSITION SIZING
# ─────────────────────────────────────────────

def get_position_size(exchange: ccxt.binanceusdm, symbol: str, price: float,
                      size_mult: float = 1.0) -> float:
    try:
        balance   = exchange.fetch_balance()
        usdt_free = float(balance["USDT"]["free"])
        notional  = usdt_free * WALLET_ALLOC_PCT * size_mult * LEVERAGE
        qty       = notional / price
        market    = exchange.market(symbol)
        step      = float(market.get("precision", {}).get("amount", 0.001))
        if step > 0:
            qty = math.floor(qty / step) * step
        return round(qty, 6)
    except Exception as e:
        log.error(f"Position sizing error {symbol}: {e}")
        return 0.0

# ─────────────────────────────────────────────
#  TRADE EXECUTION
# ─────────────────────────────────────────────

def set_leverage_and_margin(exchange: ccxt.binanceusdm, symbol: str) -> None:
    try:
        exchange.set_leverage(LEVERAGE, symbol)
        exchange.set_margin_mode(MARGIN_MODE.lower(), symbol)
    except Exception as e:
        log.warning(f"Leverage/margin {symbol}: {e}")


def open_long(
    exchange: ccxt.binanceusdm,
    symbol: str,
    details: dict,
    session: str,
) -> bool:
    """Execute LONG with structure-based SL, TP1=2R, TP2=trailing stop. Returns True on success."""
    price      = details.get("price", 0.0)
    sl_price   = details.get("sl", 0.0)
    conditions = details.get("entry_reasons", [])
    rvol       = details.get("rvol_ratio", 0.0)

    if price <= 0 or sl_price <= 0:
        log.warning(f"Invalid price/SL for {symbol}")
        return False

    qty = get_position_size(exchange, symbol, price, details.get("size_mult", 1.0))
    if qty <= 0:
        log.warning(f"Invalid qty for {symbol}")
        return False

    try:
        set_leverage_and_margin(exchange, symbol)
        order       = exchange.create_order(symbol=symbol, type="market", side="buy", amount=qty)
        entry_price = float(order.get("average") or price)
        order_id    = order.get("id", "N/A")

        # Recalculate TP1 from actual fill (keep structure SL)
        R         = entry_price - sl_price
        tp1_price = round(entry_price + TP1_R * R, 8)

        # SL — closes entire position
        exchange.create_order(
            symbol=symbol, type="stop_market", side="sell", amount=qty,
            params={"stopPrice": sl_price, "closePosition": True},
        )
        # TP1 — half position at 2R
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="sell",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp1_price, "reduceOnly": True},
        )
        # TP2 — trailing stop on remaining half (callback = TRAIL_CALLBACK_PCT%)
        exchange.create_order(
            symbol=symbol, type="trailing_stop_market", side="sell",
            amount=round(qty / 2, 6),
            params={"callbackRate": TRAIL_CALLBACK_PCT, "reduceOnly": True},
        )

        open_positions[symbol] = {
            "direction": "LONG", "entry": entry_price, "qty": qty,
            "sl": sl_price, "tp1": tp1_price, "tp2": "trailing",
            "order_id": order_id, "opened_at": datetime.now(timezone.utc).isoformat(),
        }

        entry_reasons = ", ".join(conditions)
        db_log_trade(
            _current_scan_id, symbol, entry_price, sl_price,
            tp1_price, 0.0, qty, rvol, entry_reasons,   # tp2=0 = trailing
        )

        sl_pct  = round((entry_price - sl_price) / entry_price * 100, 2)
        tp1_pct = round((tp1_price - entry_price) / entry_price * 100, 2)
        cond_text = "\n".join(f"  ✓ {c}" for c in conditions)

        log.info(
            f"LONG opened: {symbol} @ {entry_price} | SL={sl_price}(-{sl_pct:.1f}%) "
            f"TP1={tp1_price}(+{tp1_pct:.1f}%) TP2=trailing({TRAIL_CALLBACK_PCT}%) RVOL={rvol:.1f}x"
        )
        send_telegram(
            f"*MUESA — LONG OPENED* ⚡\n"
            f"─────────────────────\n"
            f"Symbol  : `{symbol}`\n"
            f"Session : `{session}`\n"
            f"Entry   : `{entry_price}`\n"
            f"Qty     : `{qty}`\n"
            f"SL      : `{sl_price}` (-{sl_pct:.1f}%) ← range low\n"
            f"TP1     : `{tp1_price}` (+{tp1_pct:.1f}%) ← 2R\n"
            f"TP2     : Trailing stop ({TRAIL_CALLBACK_PCT}% callback) ← rides momentum\n"
            f"─────────────────────\n"
            f"*Breakout Conditions*\n{cond_text}\n"
            f"─────────────────────\n"
            f"RVOL  : `{rvol:.1f}x`\n"
            f"Range : `{details.get('range_low',0):.4f}` → `{details.get('range_high',0):.4f}`"
        )
        return True

    except Exception as e:
        log.error(f"LONG order failed {symbol}: {e}")
        send_telegram(f"*MUESA ERROR* — LONG failed `{symbol}`:\n`{e}`")
        return False

# ─────────────────────────────────────────────
#  POSITION MONITOR
# ─────────────────────────────────────────────

POSITION_CHECK_INTERVAL = 10

def _log_position_snapshots(exchange: ccxt.binanceusdm) -> None:
    for symbol, pos in list(open_positions.items()):
        try:
            entry_price   = float(pos.get("entry") or 0)
            qty           = float(pos.get("qty") or 0)
            current_price = float(exchange.fetch_ticker(symbol).get("last") or 0)
            if entry_price <= 0 or current_price <= 0:
                continue
            pnl_pct  = (current_price - entry_price) / entry_price * 100
            pnl_usdt = (current_price - entry_price) * qty
            log.info(
                f"[POS] {symbol} LONG | entry={entry_price} now={current_price} "
                f"| PnL={pnl_pct:+.2f}% / {pnl_usdt:+.4f} USDT"
            )
            db_log_position_check(symbol, entry_price, current_price, pnl_pct, pnl_usdt, qty)
        except Exception as e:
            log.debug(f"Position snapshot failed {symbol}: {e}")


def position_monitor_loop(exchange: ccxt.binanceusdm) -> None:
    while True:
        time.sleep(POSITION_CHECK_INTERVAL)
        if open_positions:
            _log_position_snapshots(exchange)
            sync_open_positions(exchange)


def sync_open_positions(exchange: ccxt.binanceusdm) -> None:
    if not open_positions:
        return
    try:
        live_symbols = {
            p["symbol"] for p in exchange.fetch_positions()
            if float(p.get("contracts") or 0) > 0
        }
        for sym in [s for s in list(open_positions.keys()) if s not in live_symbols]:
            pos      = open_positions.pop(sym, {})
            entry    = float(pos.get("entry") or 0)
            sl_price = float(pos.get("sl") or 0)
            try:
                last_price = float(exchange.fetch_ticker(sym).get("last") or 0)
                sl_hit     = last_price > 0 and sl_price > 0 and last_price <= sl_price * 1.001
                if sl_hit:
                    sl_hit_symbols[sym] = time.time()
                    db_update_trade_status(sym, "sl_hit")
                    send_telegram(f"🔴 *SL Hit*\n`{sym}` LONG | Entry: `{entry}` | SL: `{sl_price}`")
                    log.info(f"SL hit: {sym} — {SL_COOLDOWN_HOURS}h cooldown")
                else:
                    db_update_trade_status(sym, "closed")
                    send_telegram(f"✅ *Position Closed*\n`{sym}` LONG | Entry: `{entry}`")
            except Exception:
                db_update_trade_status(sym, "closed")
            log.info(f"Position closed: {sym} [LONG]")
    except Exception as e:
        log.error(f"Position sync error: {e}")

# ─────────────────────────────────────────────
#  UNIVERSE
# ─────────────────────────────────────────────

def get_top_symbols(exchange: ccxt.binanceusdm) -> list[tuple[str, float]]:
    try:
        tickers  = exchange.fetch_tickers()
        pairs    = [(s, float(t.get("quoteVolume") or 0))
                    for s, t in tickers.items() if s.endswith("/USDT:USDT")]
        filtered = sorted([(s, v) for s, v in pairs if v >= VOLUME_FLOOR_USDT],
                          key=lambda x: x[1], reverse=True)
        result   = filtered[SKIP_TOP_N_COINS : SKIP_TOP_N_COINS + SCAN_BAND_SIZE]
        log.info(f"Scan band: {len(result)} coins | rank {SKIP_TOP_N_COINS+1}-{SKIP_TOP_N_COINS+len(result)}")
        return result
    except Exception as e:
        log.error(f"get_top_symbols: {e}"); return []

# ─────────────────────────────────────────────
#  DAILY / WEEKLY RESET
# ─────────────────────────────────────────────

def maybe_reset_daily(now: datetime) -> None:
    global last_reset_day, last_weekly_calc_day
    if now.day != last_reset_day:
        last_reset_day = now.day
        log.info("Daily reset.")
        if now.weekday() == 6 and now.day != last_weekly_calc_day:
            last_weekly_calc_day = now.day
            threading.Thread(target=db_calc_weekly_stats, daemon=True).start()
            log.info("Weekly stats triggered.")

# ─────────────────────────────────────────────
#  SCAN CYCLE
# ─────────────────────────────────────────────

def run_scan(exchange: ccxt.binanceusdm, candle_close: datetime) -> None:
    global current_session, _current_scan_id

    now    = datetime.now(timezone.utc)
    lag_ms = (now - candle_close).total_seconds() * 1000
    maybe_reset_daily(now)
    next_close = next_candle_close_utc()
    session    = get_active_session(now) or "Off-Hours"

    if session != current_session:
        current_session = session

    log.info(
        f"=== Scan {now.strftime('%Y-%m-%d %H:%M:%S')} UTC | "
        f"lag +{lag_ms:.0f}ms | session={session} | "
        f"open={len(open_positions)}/{MAX_OPEN_POSITIONS} ==="
    )

    sync_open_positions(exchange)

    btc_crash = get_btc_crash(exchange)
    _current_scan_id = db_create_scan(
        now.isoformat(), next_close.isoformat(),
        "crash" if btc_crash["crash"] else "ok",
        btc_crash.get("change_1h_pct", 0.0), session,
    )

    # Purge expired SL cooldowns
    cutoff = time.time() - SL_COOLDOWN_HOURS * 3600
    for s in [s for s, ts in sl_hit_symbols.items() if ts < cutoff]:
        del sl_hit_symbols[s]

    if len(open_positions) >= MAX_OPEN_POSITIONS:
        log.info("Max positions reached — skipping scan.")
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    log.info(f"BTC 1H: {btc_crash['change_1h_pct']:+.2f}% | crash={btc_crash['crash']}")
    if btc_crash["crash"]:
        send_telegram(f"⚠️ *Crash Guard* — BTC dropped `{btc_crash['change_1h_pct']:.2f}%` in 1H.")
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    symbol_vols = get_top_symbols(exchange)
    if not symbol_vols:
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    # Inject watchlist
    watchlist_symbols = db_load_watchlist_symbols()
    top_set           = {s for s, _ in symbol_vols}
    if watchlist_symbols:
        try:    tickers = exchange.fetch_tickers()
        except: tickers = {}
        for wl_sym in sorted(watchlist_symbols):
            if wl_sym not in top_set and wl_sym not in SIGNAL_EXCLUDE:
                wl_vol = float((tickers.get(wl_sym) or {}).get("quoteVolume") or 0)
                symbol_vols.append((wl_sym, wl_vol))
                log.info(f"[WATCHLIST] {wl_sym} injected")

    signals_found = 0
    trades_taken  = 0
    candidates: list[tuple[int, float, str, dict]] = []  # (priority, rvol, symbol, details)

    for symbol, vol_24h in symbol_vols:

        if symbol in SIGNAL_EXCLUDE:
            db_log_coin(_current_scan_id, symbol, {}, True, "signal_exclusion"); continue

        if symbol in open_positions:
            db_log_coin(_current_scan_id, symbol, {}, True, "open_position"); continue

        if symbol in sl_hit_symbols:
            db_log_coin(_current_scan_id, symbol, {}, True, "sl_cooldown"); continue

        if len(open_positions) >= MAX_OPEN_POSITIONS:
            break

        # Fetch 15m candles only
        try:
            ohlcv_15m = exchange.fetch_ohlcv(symbol, "15m", limit=CANDLE_LIMIT)
            time.sleep(0.05)
        except Exception as e:
            log.debug(f"OHLCV fetch failed {symbol}: {e}"); continue

        # Run signal check
        passed, details = compute_breakout_signal(exchange, symbol, vol_24h, ohlcv_15m)
        block_reason    = ", ".join(details.get("blocks", [])) if not passed else ""
        row_id = db_log_coin(_current_scan_id, symbol, details, not passed, block_reason)

        if not passed:
            log.debug(f"{symbol} — {block_reason}")
            continue

        signals_found += 1
        priority = details.get("priority", 0)
        rvol     = details.get("rvol_ratio", 0.0)
        rng_pct  = details.get("range_pct", 0.0)
        log.info(
            f"✅ SIGNAL: {symbol} | RVOL={rvol:.1f}x [{details.get('vol_tier','?')}] | "
            f"range={rng_pct:.1f}% | SL=-{details.get('sl_pct',0):.1f}% "
            f"TP1=+{details.get('tp1_pct',0):.1f}% TP2=trailing | "
            f"priority={priority}/2 | [{', '.join(details.get('entry_reasons',[]))}]"
        )
        db_mark_signal(row_id, f"Breakout RVOL={rvol:.1f}x priority={priority}/2")
        candidates.append((priority, rvol, symbol, details))

    # Sort: highest priority first, then highest RVOL as tiebreaker
    candidates.sort(key=lambda x: (x[0], x[1]), reverse=True)

    if candidates:
        best = candidates[0]
        log.info(
            f"Best signal: {best[2]} priority={best[0]}/2 RVOL={best[1]:.1f}x "
            f"(from {len(candidates)} candidate{'s' if len(candidates) > 1 else ''})"
        )

    if trading_paused:
        log.info("Trading PAUSED — signals logged, not executed.")

    for priority, rvol, symbol, details in candidates[:1]:
        if trading_paused:
            break
        if symbol in open_positions:
            continue
        if open_long(exchange, symbol, details, session):
            trades_taken += 1

    db_finish_scan(_current_scan_id, len(symbol_vols), signals_found, trades_taken)
    log.info(f"=== Scan complete | signals={signals_found} trades={trades_taken} ===")

# ─────────────────────────────────────────────
#  MAIN LOOP
# ─────────────────────────────────────────────

def main() -> None:
    log.info("MUESA v3.0 starting — Momentum Breakout System")
    init_db()
    load_bot_state()
    start_dashboard()
    send_telegram(
        "*MUESA v3.0* — Momentum Breakout System\n"
        "Strategy: Structure + Volume + Breakout | LONG only | No AI\n"
        f"RVOL≥{VOLUME_SURGE_MIN}x (pref≥{VOLUME_SURGE_PREF}x) · Range 3–5% · TP1={TP1_R:.0f}R + Trailing({TRAIL_CALLBACK_PCT}%)\n"
        f"Dashboard: http://139.59.23.165:{DASHBOARD_PORT}"
    )

    exchange = create_exchange()
    try:
        exchange.load_markets()
        log.info(f"Connected to Binance Futures — {len(exchange.markets)} markets loaded.")
    except Exception as e:
        log.critical(f"Exchange connection failed: {e}")
        send_telegram(f"*MUESA CRITICAL* — Binance failed:\n`{e}`")
        return

    threading.Thread(target=position_monitor_loop, args=(exchange,), daemon=True).start()
    log.info(f"Position monitor started — checking every {POSITION_CHECK_INTERVAL}s.")

    while True:
        if scanning_paused:
            log.info("Scanning PAUSED — sleep mode.")
            time.sleep(10)
            continue

        candle_close = next_candle_close_utc()
        wait         = seconds_until_scan()
        log.info(
            f"Waiting {wait:.1f}s — next candle at "
            f"{candle_close.strftime('%Y-%m-%d %H:%M:%S')} UTC"
        )
        time.sleep(wait)

        if scanning_paused:
            continue

        try:
            run_scan(exchange, candle_close)
        except KeyboardInterrupt:
            log.info("MUESA stopped by user.")
            send_telegram("*MUESA v3.0* stopped manually.")
            break
        except Exception as e:
            log.error(f"Unhandled scan error: {e}")
            send_telegram(f"*MUESA ERROR*:\n`{e}`")
            time.sleep(60)


if __name__ == "__main__":
    main()
