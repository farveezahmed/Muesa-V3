"""
MUESA v3.0 - Crypto Trading Bot
Binance Futures | Claude AI Analysis | Telegram Alerts
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
load_dotenv(override=True)   # override=True ensures .env values win over system env vars

import ccxt
import anthropic
import requests
from flask import Flask

# ─────────────────────────────────────────────
#  CONFIGURATION
# ─────────────────────────────────────────────

BINANCE_API_KEY    = os.getenv("BINANCE_API_KEY", "")
BINANCE_API_SECRET = os.getenv("BINANCE_API_SECRET", "")
CLAUDE_API_KEY     = os.getenv("ANTHROPIC_API_KEY", "")
TELEGRAM_TOKEN     = os.getenv("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID   = os.getenv("TELEGRAM_CHAT_ID", "")

CLAUDE_MODEL         = "claude-haiku-4-5-20251001"
SCAN_INTERVAL_MIN    = 5              # scan every 5 min (still uses 15m candle data)
MIN_USDT_VOLUME      = 200_000_000   # hard skip below 200M
HIGH_USDT_VOLUME     = 500_000_000   # tier-1 volume threshold
TOP_N_COINS          = 100
MAX_OPEN_POSITIONS   = 1             # hard block if 1 already open
MAX_TRADES_SESSION   = 1             # max 1 trade per session window
MAX_TRADES_DAY       = 2             # max 2 trades per calendar day (UTC)
WALLET_ALLOC_PCT     = 0.25
LEVERAGE             = 5
MARGIN_MODE          = "ISOLATED"
SL_PCT               = 0.03
TP1_PCT              = 0.06
TP2_PCT              = 0.10
SCORE_CLAUDE_CALL    = 65
SCORE_TRADE_EXEC     = 75
SL_COOLDOWN_HOURS    = 24
BTC_MOVE_3H_PCT      = 0.02          # 2% BTC 3-candle 1H move → direction block
COIN_MOVE_4H_PCT     = 0.15          # 15% coin move in last 4H candle → skip
CANDLE_BUFFER_SEC    = 5             # seconds after candle close before scanning
DASHBOARD_PORT       = 8080          # Flask dashboard port
DB_PATH              = "muesa.db"    # SQLite database file

# Symbols excluded from signal generation (too liquid / low volatility alpha)
# BTC context fetching is NOT affected — BTC is still used for market context.
SIGNAL_EXCLUDE = {
    "BTC/USDT:USDT",
    "ETH/USDT:USDT",
    "BNB/USDT:USDT",
    "SOL/USDT:USDT",
    "XRP/USDT:USDT",
    "ADA/USDT:USDT",
    "DOGE/USDT:USDT",
    "TRX/USDT:USDT",
    "TON/USDT:USDT",
    "LINK/USDT:USDT",
}

# Indicator settings
EMA_SHORT    = 7
EMA_MID      = 25
RSI_PERIOD   = 14
CANDLE_LIMIT = 150

# Timeframes fetched per coin
COIN_TIMEFRAMES = ["15m", "1h", "4h", "1d", "1w"]

# Active trading sessions (UTC hour: inclusive start, exclusive end)
SESSIONS: dict[str, tuple[int, int]] = {
    "Asia":     (1,  4),
    "London":   (7,  10),
    "New York": (13, 16),
}

# ─────────────────────────────────────────────
#  LOGGING
# ─────────────────────────────────────────────

import sys

# Cross-platform UTF-8 logging (works on Windows cp1252 and Linux)
_file_handler   = logging.FileHandler("muesa.log", encoding="utf-8")
_stream_handler = logging.StreamHandler(sys.stdout)
try:
    # Windows: reconfigure stdout to UTF-8 if possible
    sys.stdout.reconfigure(encoding="utf-8")
except AttributeError:
    pass  # Linux/already UTF-8 — no action needed

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[_file_handler, _stream_handler],
)
log = logging.getLogger("MUESA")

# ─────────────────────────────────────────────
#  STATE
# ─────────────────────────────────────────────

open_positions: dict[str, dict] = {}
daily_trade_count: int   = 0
last_reset_day: int      = -1
session_trade_count: int = 0
current_session: str     = ""
sl_hit_symbols: dict[str, float] = {}   # symbol → unix timestamp of SL hit
_current_scan_id: int    = -1           # scan_id of the currently running scan
last_weekly_calc_day: int = -1          # track Sunday weekly stats calculation

# ─────────────────────────────────────────────
#  DATABASE (SQLite) — comprehensive schema v2
# ─────────────────────────────────────────────

def init_db() -> None:
    conn = sqlite3.connect(DB_PATH)
    conn.executescript("""
        -- ── scans: one row per scan cycle
        CREATE TABLE IF NOT EXISTS scans (
            scan_id           INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp         TEXT,
            next_scan         TEXT,
            btc_trend         TEXT,
            btc_1h_change     REAL,
            total_coins       INTEGER DEFAULT 0,
            signals_found     INTEGER DEFAULT 0,
            trades_taken      INTEGER DEFAULT 0,
            session_name      TEXT
        );

        -- ── coin_scores: every coin × direction × scan — full picture
        CREATE TABLE IF NOT EXISTS coin_scores (
            id                INTEGER PRIMARY KEY AUTOINCREMENT,
            scan_id           INTEGER REFERENCES scans(scan_id),
            symbol            TEXT,
            direction         TEXT,
            total_score       REAL DEFAULT 0,
            trend_pts         REAL DEFAULT 0,
            volume_pts        REAL DEFAULT 0,
            rsi_pts           REAL DEFAULT 0,
            oi_pts            REAL DEFAULT 0,
            retest_pts        REAL DEFAULT 0,
            funding_pts       REAL DEFAULT 0,
            bottom_bounce_pts REAL DEFAULT 0,
            claude_score      REAL,
            final_score       REAL,
            rationale         TEXT,
            blocked           INTEGER DEFAULT 0,
            block_reason      TEXT,
            entry_reasons     TEXT
        );

        -- ── trades: executed positions with full lifecycle tracking
        CREATE TABLE IF NOT EXISTS trades (
            trade_id      INTEGER PRIMARY KEY AUTOINCREMENT,
            scan_id       INTEGER REFERENCES scans(scan_id),
            timestamp     TEXT,
            symbol        TEXT,
            direction     TEXT,
            entry_price   REAL,
            sl            REAL,
            tp1           REAL,
            tp2           REAL,
            qty           REAL,
            score         REAL,
            entry_reasons TEXT,
            status        TEXT DEFAULT 'open'
        );

        -- ── weekly_stats: auto-calculated every Sunday UTC
        CREATE TABLE IF NOT EXISTS weekly_stats (
            id                INTEGER PRIMARY KEY AUTOINCREMENT,
            week_start        TEXT,
            calculated_at     TEXT,
            total_trades      INTEGER DEFAULT 0,
            win_rate          REAL DEFAULT 0,
            avg_score         REAL DEFAULT 0,
            best_pattern      TEXT,
            best_session      TEXT,
            best_coin         TEXT,
            avg_entry_quality REAL DEFAULT 0
        );

        -- ── legacy compat view: keep dashboard queries working
        CREATE VIEW IF NOT EXISTS signals AS
            SELECT id, scan_id, symbol, direction,
                   total_score AS tech_score, claude_score, final_score, rationale,
                   (SELECT timestamp FROM scans s WHERE s.scan_id = coin_scores.scan_id) AS ts
            FROM coin_scores WHERE blocked=0 AND final_score IS NOT NULL;

        CREATE VIEW IF NOT EXISTS blocked AS
            SELECT id, scan_id, symbol, direction, block_reason AS reason,
                   (SELECT timestamp FROM scans s WHERE s.scan_id = coin_scores.scan_id) AS ts
            FROM coin_scores WHERE blocked=1 AND block_reason NOT IN ('signal_exclusion','open_position','sl_cooldown');
    """)
    conn.commit()
    conn.close()

def _db_conn() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.execute("PRAGMA journal_mode=WAL")   # allows concurrent reads while writing
    return conn

def db_create_scan(timestamp: str, next_scan: str, btc_trend: str,
                   btc_1h_change: float, session_name: str) -> int:
    """Insert a new scan record and return its scan_id."""
    try:
        conn = _db_conn()
        cur  = conn.execute(
            "INSERT INTO scans (timestamp,next_scan,btc_trend,btc_1h_change,session_name)"
            " VALUES (?,?,?,?,?)",
            (timestamp, next_scan, btc_trend, round(btc_1h_change, 4), session_name),
        )
        scan_id = cur.lastrowid
        conn.commit()
        conn.close()
        return scan_id
    except Exception as e:
        log.debug(f"db_create_scan error: {e}")
        return -1

def db_finish_scan(scan_id: int, total_coins: int,
                   signals_found: int, trades_taken: int) -> None:
    """Update scan record at end with totals."""
    try:
        conn = _db_conn()
        conn.execute(
            "UPDATE scans SET total_coins=?,signals_found=?,trades_taken=? WHERE scan_id=?",
            (total_coins, signals_found, trades_taken, scan_id),
        )
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug(f"db_finish_scan error: {e}")

def db_log_coin(scan_id: int, symbol: str, direction: str, details: dict,
                blocked: bool, block_reason: str = "") -> int:
    """
    Log one coin/direction row to coin_scores. Returns row id.
    Call for EVERY coin in every scan — including excluded, zero-score, and blocked.
    """
    try:
        entry_reasons = ", ".join(details.get("entry_reasons", []))
        conn = _db_conn()
        cur  = conn.execute(
            "INSERT INTO coin_scores "
            "(scan_id,symbol,direction,total_score,trend_pts,volume_pts,rsi_pts,oi_pts,"
            " retest_pts,funding_pts,bottom_bounce_pts,blocked,block_reason,entry_reasons)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                scan_id, symbol, direction,
                round(float(details.get("total", 0)), 2),
                round(float(details.get("htf_pts", 0)), 2),
                round(float(details.get("vol_pts", 0) + details.get("rvol_pts", 0)), 2),
                round(float(details.get("rsi_pts", 0)), 2),
                round(float(details.get("oi_pts", 0)), 2),
                round(float(details.get("retest_pts", 0)), 2),
                round(float(details.get("fund_pts", 0)), 2),
                round(float(details.get("bounce_pts", 0)), 2),
                1 if blocked else 0,
                block_reason,
                entry_reasons,
            ),
        )
        row_id = cur.lastrowid
        conn.commit()
        conn.close()
        return row_id
    except Exception as e:
        log.debug(f"db_log_coin error: {e}")
        return -1

def db_update_coin_claude(row_id: int, claude_score: float,
                          final_score: float, rationale: str) -> None:
    """After Claude call: store claude/final scores and rationale on the coin_scores row."""
    try:
        conn = _db_conn()
        conn.execute(
            "UPDATE coin_scores SET claude_score=?,final_score=?,rationale=? WHERE id=?",
            (round(claude_score, 2), round(final_score, 2), rationale, row_id),
        )
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug(f"db_update_coin_claude error: {e}")

def db_log_trade(scan_id: int, symbol: str, direction: str, entry: float,
                 sl: float, tp1: float, tp2: float, qty: float,
                 score: float, entry_reasons: str) -> int:
    """Insert trade record; returns trade_id."""
    try:
        conn = _db_conn()
        cur  = conn.execute(
            "INSERT INTO trades "
            "(scan_id,timestamp,symbol,direction,entry_price,sl,tp1,tp2,qty,score,entry_reasons,status)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
            (scan_id, datetime.now(timezone.utc).isoformat(),
             symbol, direction, entry, sl, tp1, tp2, qty, score, entry_reasons, "open"),
        )
        trade_id = cur.lastrowid
        conn.commit()
        conn.close()
        return trade_id
    except Exception as e:
        log.debug(f"db_log_trade error: {e}")
        return -1

def db_update_trade_status(symbol: str, status: str) -> None:
    """Update the most recent open trade for a symbol to new status."""
    try:
        conn = _db_conn()
        conn.execute(
            "UPDATE trades SET status=? WHERE symbol=? AND status='open'"
            " AND trade_id=(SELECT MAX(trade_id) FROM trades WHERE symbol=? AND status='open')",
            (status, symbol, symbol),
        )
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug(f"db_update_trade_status error: {e}")

def db_calc_weekly_stats() -> None:
    """Calculate weekly stats from the trades table and store in weekly_stats."""
    try:
        conn = _db_conn()
        conn.row_factory = sqlite3.Row

        # All trades in last 7 days
        week_start = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        rows = conn.execute(
            "SELECT * FROM trades WHERE timestamp >= date('now','-7 days')"
        ).fetchall()

        if not rows:
            conn.close()
            return

        total    = len(rows)
        wins     = sum(1 for r in rows if r["status"] in ("tp1_hit", "tp2_hit"))
        win_rate = round(wins / total * 100, 1) if total else 0
        avg_score = round(sum(float(r["score"] or 0) for r in rows) / total, 1) if total else 0
        avg_entry = avg_score  # same metric for now

        # Best pattern: most common entry_reasons among wins
        win_patterns: dict[str, int] = {}
        for r in rows:
            if r["status"] in ("tp1_hit", "tp2_hit"):
                for p in (r["entry_reasons"] or "").split(","):
                    p = p.strip()
                    if p:
                        win_patterns[p] = win_patterns.get(p, 0) + 1
        best_pattern = max(win_patterns, key=win_patterns.get) if win_patterns else "N/A"

        # Best session: scan session with most wins — join to scans
        session_wins: dict[str, int] = {}
        for r in rows:
            if r["status"] in ("tp1_hit", "tp2_hit"):
                scan_row = conn.execute(
                    "SELECT session_name FROM scans WHERE scan_id=?", (r["scan_id"],)
                ).fetchone()
                sess = (scan_row["session_name"] if scan_row else None) or "Off-Hours"
                session_wins[sess] = session_wins.get(sess, 0) + 1
        best_session = max(session_wins, key=session_wins.get) if session_wins else "N/A"

        # Best coin: symbol with most wins
        coin_wins: dict[str, int] = {}
        for r in rows:
            if r["status"] in ("tp1_hit", "tp2_hit"):
                coin_wins[r["symbol"]] = coin_wins.get(r["symbol"], 0) + 1
        best_coin = max(coin_wins, key=coin_wins.get) if coin_wins else "N/A"

        conn.execute(
            "INSERT INTO weekly_stats "
            "(week_start,calculated_at,total_trades,win_rate,avg_score,"
            " best_pattern,best_session,best_coin,avg_entry_quality)"
            " VALUES (?,?,?,?,?,?,?,?,?)",
            (week_start, datetime.now(timezone.utc).isoformat(),
             total, win_rate, avg_score, best_pattern, best_session, best_coin, avg_entry),
        )
        conn.commit()
        conn.close()
        log.info(
            f"Weekly stats stored: {total} trades | win_rate={win_rate}% | "
            f"best_coin={best_coin} | best_session={best_session}"
        )
    except Exception as e:
        log.error(f"db_calc_weekly_stats error: {e}")

# ─────────────────────────────────────────────
#  FLASK DASHBOARD
# ─────────────────────────────────────────────

_flask_app = Flask(__name__)

def _db_fetch(query: str, params: tuple = ()) -> list:
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
    latest_scan = (_db_fetch("SELECT * FROM scans ORDER BY scan_id DESC LIMIT 1") or [{}])[0]
    next_scan   = (_db_fetch("SELECT * FROM scans ORDER BY scan_id DESC LIMIT 1") or [{}])[0]
    signals     = _db_fetch(
        "SELECT cs.*, s.timestamp AS ts, s.session_name FROM coin_scores cs "
        "LEFT JOIN scans s ON cs.scan_id=s.scan_id "
        "WHERE cs.blocked=0 AND cs.final_score IS NOT NULL "
        "ORDER BY cs.id DESC LIMIT 30"
    )
    trades      = _db_fetch("SELECT * FROM trades ORDER BY trade_id DESC LIMIT 20")
    blocked     = _db_fetch(
        "SELECT cs.*, s.timestamp AS ts FROM coin_scores cs "
        "LEFT JOIN scans s ON cs.scan_id=s.scan_id "
        "WHERE cs.blocked=1 AND cs.block_reason NOT IN ('signal_exclusion','open_position','sl_cooldown') "
        "ORDER BY cs.id DESC LIMIT 50"
    )
    weekly      = (_db_fetch("SELECT * FROM weekly_stats ORDER BY id DESC LIMIT 1") or [{}])[0]
    top_coins   = _db_fetch(
        "SELECT symbol, direction, AVG(total_score) AS avg_score, COUNT(*) AS appearances "
        "FROM coin_scores WHERE blocked=0 AND total_score > 0 "
        "GROUP BY symbol, direction ORDER BY avg_score DESC LIMIT 10"
    )

    today_utc   = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    trade_today = len([t for t in trades if (t.get("timestamp") or "").startswith(today_utc)])
    scan = latest_scan

    def row_color(direction: str) -> str:
        return "#1a3a1a" if direction == "LONG" else "#3a1a1a"

    def badge(direction: str) -> str:
        c = "#2ea043" if direction == "LONG" else "#da3633"
        return f'<span style="background:{c};color:#fff;padding:2px 8px;border-radius:4px;font-size:12px">{direction}</span>'

    def score_color(s) -> str:
        s = float(s or 0)
        if s >= 80: return "#2ea043"
        if s >= 65: return "#d29922"
        return "#8b949e"

    def fmt_ts(ts: str) -> str:
        if not ts: return "—"
        try:    return ts[11:19] + " UTC"
        except: return ts

    def status_badge(s: str) -> str:
        colors = {"open":"#58a6ff","tp1_hit":"#2ea043","tp2_hit":"#2ea043",
                  "sl_hit":"#da3633","closed":"#8b949e"}
        c = colors.get(s, "#8b949e")
        return f'<span style="background:{c}22;color:{c};padding:2px 7px;border-radius:4px;font-size:11px">{s}</span>'

    signals_rows = "".join(
        f'<tr style="background:{row_color(r["direction"])}">'
        f'<td>{fmt_ts(r.get("ts",""))}</td>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td>{badge(r["direction"])}</td>'
        f'<td style="color:{score_color(r["total_score"])}">{r["total_score"]}</td>'
        f'<td style="color:{score_color(r["claude_score"])}">{r["claude_score"]}</td>'
        f'<td style="color:{score_color(r["final_score"])};font-weight:bold">{r["final_score"]}</td>'
        f'<td style="color:#8b949e;font-size:11px">{r.get("entry_reasons") or ""}</td>'
        f'<td style="color:#8b949e;font-size:11px">{r.get("rationale","")}</td>'
        f'</tr>'
        for r in signals
    ) or '<tr><td colspan="8" style="text-align:center;color:#8b949e;padding:20px">No signals yet — waiting for first scan</td></tr>'

    trades_rows = "".join(
        f'<tr style="background:{row_color(r["direction"])}">'
        f'<td>{fmt_ts(r.get("timestamp",""))}</td>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td>{badge(r["direction"])}</td>'
        f'<td>{r["entry_price"]}</td>'
        f'<td style="color:#da3633">{r["sl"]}</td>'
        f'<td style="color:#2ea043">{r["tp1"]}</td>'
        f'<td style="color:#2ea043">{r["tp2"]}</td>'
        f'<td>{r["qty"]}</td>'
        f'<td style="color:{score_color(r["score"])};font-weight:bold">{r["score"]}</td>'
        f'<td style="color:#8b949e;font-size:11px">{r.get("entry_reasons","")}</td>'
        f'<td>{status_badge(r.get("status","open"))}</td>'
        f'</tr>'
        for r in trades
    ) or '<tr><td colspan="11" style="text-align:center;color:#8b949e;padding:20px">No trades executed yet</td></tr>'

    blocked_rows = "".join(
        f'<tr>'
        f'<td>{fmt_ts(r.get("ts",""))}</td>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td>{badge(r["direction"])}</td>'
        f'<td style="color:#da3633;font-size:12px">{r.get("block_reason","")}</td>'
        f'</tr>'
        for r in blocked
    ) or '<tr><td colspan="4" style="text-align:center;color:#8b949e;padding:20px">No blocks recorded</td></tr>'

    top_coin_rows = "".join(
        f'<tr>'
        f'<td><b>{r["symbol"]}</b></td>'
        f'<td>{badge(r["direction"])}</td>'
        f'<td style="color:{score_color(r["avg_score"])};font-weight:bold">{round(float(r["avg_score"]),1)}</td>'
        f'<td style="color:#8b949e">{r["appearances"]}</td>'
        f'</tr>'
        for r in top_coins
    ) or '<tr><td colspan="4" style="text-align:center;color:#8b949e;padding:20px">Not enough data yet</td></tr>'

    w = weekly
    html = f"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="UTF-8">
<meta http-equiv="refresh" content="30">
<title>MUESA v3.0 Dashboard</title>
<style>
  *{{margin:0;padding:0;box-sizing:border-box}}
  body{{background:#0d1117;color:#c9d1d9;font-family:'Segoe UI',system-ui,monospace;font-size:14px}}
  h1{{font-size:22px;color:#58a6ff;padding:20px 24px 4px}}
  .sub{{color:#8b949e;padding:0 24px 16px;font-size:13px}}
  .grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(175px,1fr));gap:12px;padding:0 24px 20px}}
  .card{{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:14px 16px}}
  .card .label{{color:#8b949e;font-size:11px;text-transform:uppercase;letter-spacing:1px;margin-bottom:6px}}
  .card .value{{font-size:22px;font-weight:bold;color:#58a6ff;line-height:1.2}}
  .card .value.green{{color:#2ea043}} .card .value.yellow{{color:#d29922}} .card .value.red{{color:#da3633}}
  .card .sub-val{{font-size:12px;color:#8b949e;margin-top:3px}}
  section{{padding:0 24px 24px}}
  h2{{font-size:14px;color:#8b949e;text-transform:uppercase;letter-spacing:1px;margin-bottom:10px;border-bottom:1px solid #21262d;padding-bottom:6px}}
  table{{width:100%;border-collapse:collapse;background:#161b22;border-radius:8px;overflow:hidden;border:1px solid #30363d;margin-bottom:4px}}
  th{{background:#21262d;color:#8b949e;font-size:11px;text-transform:uppercase;letter-spacing:1px;padding:7px 10px;text-align:left;white-space:nowrap}}
  td{{padding:7px 10px;border-bottom:1px solid #21262d;vertical-align:middle;font-size:13px}}
  tr:last-child td{{border-bottom:none}}
  tr:hover td{{background:#1c2128}}
  .two-col{{display:grid;grid-template-columns:1fr 1fr;gap:16px;padding:0 24px 24px}}
  .status-dot{{width:9px;height:9px;border-radius:50%;background:#2ea043;display:inline-block;margin-right:6px;animation:pulse 2s infinite}}
  @keyframes pulse{{0%,100%{{opacity:1}}50%{{opacity:.4}}}}
  .refresh-bar{{display:flex;justify-content:space-between;align-items:center;padding:0 24px 8px;color:#8b949e;font-size:12px}}
</style>
</head><body>
<h1>&#9685; MUESA v3.0</h1>
<div class="sub">Binance Futures · Claude AI · SQLite Logging · Auto-refresh 30s</div>
<div class="refresh-bar">
  <span><span class="status-dot"></span>Bot running · Scan #{scan.get("scan_id","—")} · Session: {scan.get("session_name","—")}</span>
  <span>Updated: {datetime.now(timezone.utc).strftime('%H:%M:%S')} UTC</span>
</div>

<div class="grid">
  <div class="card">
    <div class="label">Last Scan</div>
    <div class="value" style="font-size:15px">{fmt_ts(scan.get("timestamp",""))}</div>
    <div class="sub-val">BTC {scan.get("btc_trend","—")} · {scan.get("btc_1h_change",0):+.2f}% 1H</div>
  </div>
  <div class="card">
    <div class="label">Next Scan</div>
    <div class="value" style="font-size:15px">{fmt_ts(scan.get("next_scan",""))}</div>
    <div class="sub-val">Every {SCAN_INTERVAL_MIN}m · 15m candle data</div>
  </div>
  <div class="card">
    <div class="label">Coins Scanned</div>
    <div class="value">{scan.get("total_coins",0)}</div>
    <div class="sub-val">{scan.get("signals_found",0)} signals found</div>
  </div>
  <div class="card">
    <div class="label">Trades Today</div>
    <div class="value {'green' if trade_today==0 else 'yellow'}">{trade_today}<span style="font-size:14px;color:#8b949e"> / {MAX_TRADES_DAY}</span></div>
    <div class="sub-val">{scan.get("trades_taken",0)} this scan</div>
  </div>
  <div class="card">
    <div class="label">Open Positions</div>
    <div class="value {'red' if open_positions else 'green'}">{len(open_positions)}<span style="font-size:14px;color:#8b949e"> / {MAX_OPEN_POSITIONS}</span></div>
    <div class="sub-val">{", ".join(open_positions.keys()) or "None"}</div>
  </div>
  <div class="card">
    <div class="label">Weekly Stats</div>
    <div class="value {'green' if float(w.get('win_rate',0))>=50 else 'red'}" style="font-size:18px">{w.get("win_rate","—")}%</div>
    <div class="sub-val">{w.get("total_trades","—")} trades · avg {w.get("avg_score","—")}</div>
  </div>
  <div class="card">
    <div class="label">Best Coin (Week)</div>
    <div class="value" style="font-size:15px">{w.get("best_coin","—")}</div>
    <div class="sub-val">Session: {w.get("best_session","—")}</div>
  </div>
  <div class="card">
    <div class="label">Best Pattern (Week)</div>
    <div class="value" style="font-size:13px;padding-top:4px">{w.get("best_pattern","—")}</div>
    <div class="sub-val">Entry quality avg: {w.get("avg_entry_quality","—")}</div>
  </div>
</div>

<section>
  <h2>Recent Signals — Claude Called ({len(signals)})</h2>
  <table>
    <tr><th>Time</th><th>Symbol</th><th>Dir</th><th>Tech</th><th>Claude</th><th>Final</th><th>Entry Reasons</th><th>Rationale</th></tr>
    {signals_rows}
  </table>
</section>

<section>
  <h2>Recent Trades ({len(trades)})</h2>
  <table>
    <tr><th>Time</th><th>Symbol</th><th>Dir</th><th>Entry</th><th>SL</th><th>TP1</th><th>TP2</th><th>Qty</th><th>Score</th><th>Entry Reasons</th><th>Status</th></tr>
    {trades_rows}
  </table>
</section>

<div class="two-col">
  <section style="padding:0">
    <h2>Blocked Coins — Scoring Failures (last 50)</h2>
    <table>
      <tr><th>Time</th><th>Symbol</th><th>Dir</th><th>Block Reason</th></tr>
      {blocked_rows}
    </table>
  </section>
  <section style="padding:0">
    <h2>Top Coins by Avg Score</h2>
    <table>
      <tr><th>Symbol</th><th>Dir</th><th>Avg Score</th><th>Appearances</th></tr>
      {top_coin_rows}
    </table>
  </section>
</div>

</body></html>"""
    return html

def start_dashboard() -> None:
    """Start Flask dashboard in a background daemon thread."""
    import logging as _lg
    _lg.getLogger("werkzeug").setLevel(_lg.ERROR)  # suppress Flask request logs
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
    url     = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    payload = {"chat_id": TELEGRAM_CHAT_ID, "text": message, "parse_mode": "Markdown"}
    try:
        resp = requests.post(url, json=payload, timeout=10)
        resp.raise_for_status()
    except Exception as e:
        log.error(f"Telegram send failed: {e}")

# ─────────────────────────────────────────────
#  EXCHANGE SETUP
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
#  INDICATOR HELPERS
# ─────────────────────────────────────────────

def calc_ema(closes: list[float], period: int) -> list[float]:
    if len(closes) < period:
        return []
    k   = 2.0 / (period + 1)
    ema = [sum(closes[:period]) / period]
    for price in closes[period:]:
        ema.append(price * k + ema[-1] * (1 - k))
    return ema

def calc_rsi(closes: list[float], period: int = 14) -> float:
    if len(closes) < period + 1:
        return 50.0
    deltas   = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    gains    = [max(d, 0)    for d in deltas[-period:]]
    losses   = [abs(min(d, 0)) for d in deltas[-period:]]
    avg_gain = sum(gains)  / period
    avg_loss = sum(losses) / period
    if avg_loss == 0:
        return 100.0
    return 100 - (100 / (1 + avg_gain / avg_loss))

def ema_aligned(ohlcv: list, direction: str) -> bool:
    """True if EMA7 > EMA25 (LONG) or EMA7 < EMA25 (SHORT) on given candle list."""
    if len(ohlcv) < EMA_MID + 3:
        return False
    closes    = [c[4] for c in ohlcv]
    ema7_arr  = calc_ema(closes, EMA_SHORT)
    ema25_arr = calc_ema(closes, EMA_MID)
    if not ema7_arr or not ema25_arr:
        return False
    return (ema7_arr[-1] > ema25_arr[-1]) if direction == "LONG" else (ema7_arr[-1] < ema25_arr[-1])

# ─────────────────────────────────────────────
#  CANDLE CLOSE TIMING  (:00, :15, :30, :45 UTC)
# ─────────────────────────────────────────────

def next_candle_close_utc() -> datetime:
    interval = SCAN_INTERVAL_MIN * 60
    now_ts   = time.time()
    close_ts = now_ts + (interval - now_ts % interval)
    return datetime.fromtimestamp(close_ts, tz=timezone.utc)

def seconds_until_scan() -> float:
    interval      = SCAN_INTERVAL_MIN * 60
    secs_to_close = interval - (time.time() % interval)
    return secs_to_close + CANDLE_BUFFER_SEC

# ─────────────────────────────────────────────
#  SESSION MANAGEMENT
# ─────────────────────────────────────────────

def get_active_session(now: datetime) -> str | None:
    """Return active session name or None if outside all windows."""
    hour = now.hour
    for name, (start, end) in SESSIONS.items():
        if start <= hour < end:
            return name
    return None

# ─────────────────────────────────────────────
#  STEP 1 — BTC CONTEXT CHECK
# ─────────────────────────────────────────────

def get_btc_context(exchange: ccxt.binanceusdm) -> dict:
    """
    Fetch BTC/USDT 1H and 4H data.
    Returns:
      block_long    : bool  — BTC dropped ≥2% in last 3 1H candles
      block_short   : bool  — BTC pumped ≥2% in last 3 1H candles
      trend_4h      : str   — "bullish" | "bearish" | "neutral"
      change_3h_pct : float — raw BTC 3-candle 1H change %
    """
    ctx: dict = {
        "block_long":    False,
        "block_short":   False,
        "trend_4h":      "neutral",
        "change_3h_pct": 0.0,
    }
    try:
        # ── 3-candle 1H price change (use last 3 fully closed candles)
        ohlcv_1h = exchange.fetch_ohlcv("BTC/USDT:USDT", "1h", limit=6)
        if len(ohlcv_1h) >= 4:
            # [-4:-1] → 3 closed candles, excluding current open
            closes_3h  = [c[4] for c in ohlcv_1h[-4:-1]]
            change     = (closes_3h[-1] - closes_3h[0]) / closes_3h[0]
            ctx["change_3h_pct"] = round(change * 100, 3)
            if change <= -BTC_MOVE_3H_PCT:
                ctx["block_long"]  = True
            elif change >= BTC_MOVE_3H_PCT:
                ctx["block_short"] = True

        # ── 4H EMA trend
        ohlcv_4h = exchange.fetch_ohlcv("BTC/USDT:USDT", "4h", limit=CANDLE_LIMIT)
        if len(ohlcv_4h) >= EMA_MID + 5:
            closes_4h = [c[4] for c in ohlcv_4h]
            ema7_arr  = calc_ema(closes_4h, EMA_SHORT)
            ema25_arr = calc_ema(closes_4h, EMA_MID)
            if ema7_arr and ema25_arr:
                diff_pct = (ema7_arr[-1] - ema25_arr[-1]) / ema25_arr[-1]
                if diff_pct > 0.001:
                    ctx["trend_4h"] = "bullish"
                elif diff_pct < -0.001:
                    ctx["trend_4h"] = "bearish"

    except Exception as e:
        log.error(f"BTC context fetch failed: {e}")

    return ctx

# ─────────────────────────────────────────────
#  MULTI-TIMEFRAME OHLCV
# ─────────────────────────────────────────────

def fetch_multi_tf_ohlcv(exchange: ccxt.binanceusdm, symbol: str) -> dict[str, list]:
    result: dict[str, list] = {}
    for tf in COIN_TIMEFRAMES:
        try:
            result[tf] = exchange.fetch_ohlcv(symbol, tf, limit=CANDLE_LIMIT)
            time.sleep(0.05)
        except Exception as e:
            log.debug(f"OHLCV {tf} fetch failed for {symbol}: {e}")
            result[tf] = []
    return result

# ─────────────────────────────────────────────
#  SCORING: HTF TREND — 25 pts
# ─────────────────────────────────────────────

def score_htf_trend(ohlcv_by_tf: dict, direction: str) -> tuple[float, bool]:
    """
    1W: EMA7 vs EMA25 aligned → +15
    1D: EMA7 vs EMA25 aligned → +10
    Hard block if 1D strongly opposing (EMA diff > 0.5%).
    Returns (points, blocked).
    """
    points = 0.0

    # ── 1W
    candles_1w = ohlcv_by_tf.get("1w", [])
    if ema_aligned(candles_1w, direction):
        points += 15.0

    # ── 1D
    candles_1d = ohlcv_by_tf.get("1d", [])
    if len(candles_1d) >= EMA_MID + 3:
        closes    = [c[4] for c in candles_1d]
        ema7_arr  = calc_ema(closes, EMA_SHORT)
        ema25_arr = calc_ema(closes, EMA_MID)
        if ema7_arr and ema25_arr:
            ema7     = ema7_arr[-1]
            ema25    = ema25_arr[-1]
            diff_pct = abs(ema7 - ema25) / ema25
            # Block if 1D strongly opposing (>0.5% separation wrong way)
            if direction == "LONG"  and ema7 < ema25 and diff_pct > 0.005:
                return points, True
            if direction == "SHORT" and ema7 > ema25 and diff_pct > 0.005:
                return points, True
            if direction == "LONG"  and ema7 > ema25:
                points += 10.0
            if direction == "SHORT" and ema7 < ema25:
                points += 10.0

    return points, False

# ─────────────────────────────────────────────
#  SCORING: BTC CONTEXT — 15 pts
# ─────────────────────────────────────────────

def score_btc_context(trend_4h: str, direction: str) -> float:
    """
    Aligns → +15 | Neutral → +5 | Opposing → -15
    """
    if direction == "LONG":
        if trend_4h == "bullish": return 15.0
        if trend_4h == "neutral": return 5.0
        return -15.0
    else:  # SHORT
        if trend_4h == "bearish": return 15.0
        if trend_4h == "neutral": return 5.0
        return -15.0

# ─────────────────────────────────────────────
#  SCORING: LTF ALIGNMENT — 20 pts
# ─────────────────────────────────────────────

def score_ltf_alignment(ohlcv_by_tf: dict, direction: str) -> tuple[float, int, bool]:
    """
    4H = +7 | 1H = +7 | 15m = +6 if EMA7 aligned with direction.
    Hard block if < 2 timeframes aligned.
    Returns (points, aligned_count, blocked).
    """
    tf_weights = {"4h": 7.0, "1h": 7.0, "15m": 6.0}
    points        = 0.0
    aligned_count = 0

    for tf, pts in tf_weights.items():
        candles = ohlcv_by_tf.get(tf, [])
        if ema_aligned(candles, direction):
            points += pts
            aligned_count += 1

    return points, aligned_count, aligned_count < 2

# ─────────────────────────────────────────────
#  SCORING: VOLUME & OI — ~20 pts
# ─────────────────────────────────────────────

def _oi_value(entry: dict) -> float:
    return float(entry.get("openInterestValue") or entry.get("openInterest") or 0)

def score_volume_oi(
    vol_24h: float,
    ohlcv_15m: list,
    exchange: ccxt.binanceusdm,
    symbol: str,
    direction: str,
    price_now: float,
    price_prev: float,
) -> tuple[float, float, float, float, bool]:
    """
    Base vol: >500M=+10, 200M-500M=+7, <200M=skip.
    RVOL    : >2x=+10, 1.5x=+7, 1.2x=+4, <0.5x=-15.
    OI      : aligned with direction = +5.
    Returns (vol_pts, rvol_pts, oi_pts, total, skip_coin).
    """
    if vol_24h < MIN_USDT_VOLUME:
        return 0.0, 0.0, 0.0, 0.0, True

    vol_pts = 10.0 if vol_24h >= HIGH_USDT_VOLUME else 7.0

    rvol_pts = 0.0
    if len(ohlcv_15m) >= 21:
        volumes = [c[5] for c in ohlcv_15m]
        avg_vol = sum(volumes[-21:-1]) / 20
        if avg_vol > 0:
            rvol = volumes[-1] / avg_vol
            if   rvol >= 2.0: rvol_pts = 10.0
            elif rvol >= 1.5: rvol_pts = 7.0
            elif rvol >= 1.2: rvol_pts = 4.0
            elif rvol < 0.5:  rvol_pts = -15.0

    oi_pts = 0.0
    try:
        history = exchange.fetch_open_interest_history(symbol, "15m", limit=3)
        if history and len(history) >= 2:
            oi_now  = _oi_value(history[-1])
            oi_prev = _oi_value(history[-2])
            if oi_prev > 0:
                oi_rising    = oi_now > oi_prev
                price_rising = price_now > price_prev
                if direction == "LONG"  and oi_rising and price_rising:     oi_pts = 5.0
                if direction == "SHORT" and not oi_rising and not price_rising: oi_pts = 5.0
    except Exception as e:
        log.debug(f"OI fetch failed for {symbol}: {e}")

    total = vol_pts + rvol_pts + oi_pts
    return vol_pts, rvol_pts, oi_pts, total, False

# ─────────────────────────────────────────────
#  SCORING: RETEST DETECTION — 15 pts
# ─────────────────────────────────────────────

def score_retest_detection(
    ohlcv_4h: list,
    ohlcv_15m: list,
    direction: str,
) -> tuple[float, bool]:
    """
    If coin moved ≥15% in last 4H candle:
      Check all 5 retest conditions.
      All 5 met  → +15, allow trade (confirmed retest).
      Any fail   → BLOCK (don't chase the move).
    If coin moved <15% → (0, False) — retest check not required.

    Conditions for LONG (buy the dip after pump):
      1. Price pulled back ≥10% from recent high.
      2. Price within 2% of EMA7, EMA25, or recent swing low.
      3. Volume declining on last 3 pullback candles.
      4. RSI reset to 40–55.
      5. Current candle is green (close > open).

    Conditions for SHORT (short the dead-cat bounce after dump):
      1. Price bounced ≥10% from recent low.
      2. Price within 2% of EMA7, EMA25, or recent swing high.
      3. Volume declining on last 3 bounce candles.
      4. RSI reset to 45–60.
      5. Current candle is red (close < open).

    Returns (points, blocked).
    """
    if not ohlcv_4h or not ohlcv_15m:
        return 0.0, False

    # ── Check 4H move magnitude
    last_4h = ohlcv_4h[-1]
    open_4h = float(last_4h[1])
    if open_4h == 0:
        return 0.0, False

    move_4h = abs(float(last_4h[4]) - open_4h) / open_4h
    if move_4h < COIN_MOVE_4H_PCT:
        return 0.0, False   # <15% move — retest check not required, no block

    # ── 15%+ move detected — evaluate all 5 conditions
    closes  = [c[4] for c in ohlcv_15m]
    highs   = [c[2] for c in ohlcv_15m]
    lows    = [c[3] for c in ohlcv_15m]
    volumes = [c[5] for c in ohlcv_15m]
    last_c  = ohlcv_15m[-1]
    price   = float(closes[-1])

    ema7_arr  = calc_ema(closes, EMA_SHORT)
    ema25_arr = calc_ema(closes, EMA_MID)
    ema7      = ema7_arr[-1]  if ema7_arr  else price
    ema25     = ema25_arr[-1] if ema25_arr else price

    def near(level: float) -> bool:
        return abs(price - level) / price <= 0.02

    if direction == "LONG":
        # Cond 1: pulled back ≥10% from recent 20-candle high
        recent_high = max(highs[-20:]) if len(highs) >= 20 else max(highs)
        cond1 = recent_high > 0 and (recent_high - price) / recent_high >= 0.10

        # Cond 2: price within 2% of EMA7, EMA25, or recent swing low
        swing_low = min(lows[-10:]) if len(lows) >= 10 else min(lows)
        cond2 = near(ema7) or near(ema25) or near(swing_low)

        # Cond 3: volume declining across last 3 closed candles
        pull_vols = volumes[-4:-1]
        cond3 = len(pull_vols) == 3 and all(pull_vols[i] >= pull_vols[i + 1] for i in range(2))

        # Cond 4: RSI reset to 40–55
        rsi   = calc_rsi(closes, RSI_PERIOD)
        cond4 = 40 <= rsi <= 55

        # Cond 5: current candle is green
        cond5 = float(last_c[4]) > float(last_c[1])

    else:  # SHORT
        # Cond 1: bounced ≥10% from recent 20-candle low (dead-cat)
        recent_low = min(lows[-20:]) if len(lows) >= 20 else min(lows)
        cond1 = recent_low > 0 and (price - recent_low) / recent_low >= 0.10

        # Cond 2: price within 2% of EMA7, EMA25, or recent swing high
        swing_high = max(highs[-10:]) if len(highs) >= 10 else max(highs)
        cond2 = near(ema7) or near(ema25) or near(swing_high)

        # Cond 3: volume declining on last 3 bounce candles
        pull_vols = volumes[-4:-1]
        cond3 = len(pull_vols) == 3 and all(pull_vols[i] >= pull_vols[i + 1] for i in range(2))

        # Cond 4: RSI reset to 45–60
        rsi   = calc_rsi(closes, RSI_PERIOD)
        cond4 = 45 <= rsi <= 60

        # Cond 5: current candle is red (rejection)
        cond5 = float(last_c[4]) < float(last_c[1])

    conditions = (cond1, cond2, cond3, cond4, cond5)
    log.debug(
        f"Retest check ({direction}) — "
        f"pullback={cond1} near_level={cond2} vol_decline={cond3} "
        f"rsi={cond4} candle={cond5}"
    )

    if all(conditions):
        return 15.0, False   # confirmed retest — bonus points, allow trade
    return 0.0, True         # 15%+ move but retest not confirmed — BLOCK

# ─────────────────────────────────────────────
#  SCORING: FUNDING RATE — 5 pts
# ─────────────────────────────────────────────

def score_funding(
    exchange: ccxt.binanceusdm,
    symbol: str,
    direction: str,
) -> tuple[float, bool]:
    """
    LONG : funding < 0 → +5 | > +0.1% → BLOCK
    SHORT: funding > 0 → +5 | < -0.1% → BLOCK
    Returns (points, blocked).
    """
    try:
        fr_data = exchange.fetch_funding_rate(symbol)
        rate    = float(fr_data.get("fundingRate") or 0)
        if direction == "LONG":
            if rate >  0.001: return 0.0, True
            if rate <  0:     return 5.0, False
        else:
            if rate < -0.001: return 0.0, True
            if rate >  0:     return 5.0, False
        return 0.0, False
    except Exception as e:
        log.debug(f"Funding rate fetch failed for {symbol}: {e}")
        return 0.0, False

# ─────────────────────────────────────────────
#  SCORING: RSI CONFIRMING — 5 pts
# ─────────────────────────────────────────────

def score_rsi_confirming(closes: list[float], direction: str) -> tuple[float, float, bool]:
    """
    LONG : RSI 30-60 → +5
    SHORT: RSI 40-70 → +5
    RSI > 80 or < 20 → -10 penalty + hard block.
    Returns (points, rsi_value, blocked).
    """
    rsi = calc_rsi(closes, RSI_PERIOD)
    if rsi > 80 or rsi < 20:
        return -10.0, rsi, True
    if direction == "LONG"  and 30 <= rsi <= 60: return 5.0, rsi, False
    if direction == "SHORT" and 40 <= rsi <= 70: return 5.0, rsi, False
    return 0.0, rsi, False

# ─────────────────────────────────────────────
#  SCORING: BOTTOM BOUNCE — up to +20 pts (LONG only)
# ─────────────────────────────────────────────

def score_bottom_bounce(ohlcv_15m: list) -> tuple[float, bool]:
    """
    Awards +20 bonus points for a LONG when ALL 5 conditions are met:
      1. Price dropped >= 20% in last 48 candles (12h)
      2. RSI dipped below 30 at some point in last 10 candles (oversold)
      3. Current price >= 3% above the 10-candle recent low (bounce starting)
      4. Current candle volume >= 1.5x the 20-candle average (buyers entering)
      5. EMA7 now > EMA7 three candles ago (turning up)

    Returns (points, bounce_detected).
      +20, True  — all 5 conditions met
        0, False — drop < 20% (no check triggered)
        0, False — drop >= 20% but not all conditions met (no penalty)
    """
    if len(ohlcv_15m) < 50:
        return 0.0, False

    closes  = [c[4] for c in ohlcv_15m]
    volumes = [c[5] for c in ohlcv_15m]

    # ── Condition 1: >= 20% drop in last 48 candles
    window_48  = closes[-49:-1]          # 48 closed candles before current
    high_48    = max(window_48)
    price_now  = closes[-1]
    drop_pct   = (high_48 - price_now) / high_48 if high_48 > 0 else 0.0
    if drop_pct < 0.20:
        return 0.0, False               # drop < 20% — bottom bounce not triggered

    # ── Condition 2: RSI below 30 at some point in last 10 candles
    rsi_oversold = False
    for i in range(len(closes) - 10, len(closes)):
        if i < RSI_PERIOD:
            continue
        r = calc_rsi(closes[:i + 1], RSI_PERIOD)
        if r < 30:
            rsi_oversold = True
            break

    # ── Condition 3: Current price >= 3% above 10-candle low
    recent_low   = min(closes[-10:])
    bounce_pct   = (price_now - recent_low) / recent_low if recent_low > 0 else 0.0
    bouncing     = bounce_pct >= 0.03

    # ── Condition 4: Current volume >= 1.5x 20-candle average
    avg_vol_20   = sum(volumes[-21:-1]) / 20 if len(volumes) >= 21 else 0.0
    cur_vol      = volumes[-1]
    vol_surge    = avg_vol_20 > 0 and cur_vol >= avg_vol_20 * 1.5

    # ── Condition 5: EMA7 now > EMA7 three candles ago (turning up)
    ema7_now  = calc_ema(closes,       EMA_SHORT)
    ema7_prev = calc_ema(closes[:-3],  EMA_SHORT) if len(closes) > 3 else ema7_now
    ema_turning_up = ema7_now > ema7_prev

    if rsi_oversold and bouncing and vol_surge and ema_turning_up:
        return 20.0, True

    return 0.0, False   # drop >= 20% but conditions not all met — no penalty

# ─────────────────────────────────────────────
#  UNIFIED SCORER
# ─────────────────────────────────────────────

def compute_score(
    exchange: ccxt.binanceusdm,
    symbol: str,
    vol_24h: float,
    ohlcv_by_tf: dict[str, list],
    direction: str,
    btc_ctx: dict,
) -> tuple[float, dict, bool]:
    """
    Score breakdown (max 100 pts + up to 20 bonus):
      HTF Trend      25 pts  (1W=15, 1D=10)
      BTC Context    15 pts
      LTF Align      20 pts  (4H=7, 1H=7, 15m=6)
      Volume + OI   ~20 pts  (vol=10, rvol=10, oi=5)
      Retest         15 pts  (only when coin moved >=15% in 4H)
      Funding         5 pts
      RSI             5 pts
      Bottom Bounce  +20 bonus (LONG only, all 5 conditions)
    Returns (score, details, blocked).
    """
    details: dict = {"direction": direction, "blocks": []}
    ohlcv_15m  = ohlcv_by_tf.get("15m", [])
    ohlcv_4h   = ohlcv_by_tf.get("4h",  [])
    closes_15m = [c[4] for c in ohlcv_15m] if ohlcv_15m else []
    price_now  = closes_15m[-1] if closes_15m else 0.0
    price_prev = closes_15m[-2] if len(closes_15m) >= 2 else price_now

    # ── STEP 1: BTC direction block — overrides everything
    if direction == "LONG"  and btc_ctx.get("block_long"):
        details["blocks"].append(f"BTC_dropped_{BTC_MOVE_3H_PCT*100:.0f}pct_3H")
        return 0.0, details, True
    if direction == "SHORT" and btc_ctx.get("block_short"):
        details["blocks"].append(f"BTC_pumped_{BTC_MOVE_3H_PCT*100:.0f}pct_3H")
        return 0.0, details, True

    # ── Volume (<200M = skip coin entirely)
    vol_pts, rvol_pts, oi_pts, vol_total, skip = score_volume_oi(
        vol_24h, ohlcv_15m, exchange, symbol, direction, price_now, price_prev
    )
    if skip:
        details["blocks"].append("volume<200M")
        return 0.0, details, True
    details["vol_pts"]  = round(vol_pts, 1)
    details["rvol_pts"] = round(rvol_pts, 1)
    details["oi_pts"]   = round(oi_pts, 1)

    # ── Retest Detection (15%+ move check — block or bonus)
    retest_pts, retest_blocked = score_retest_detection(ohlcv_4h, ohlcv_15m, direction)
    details["retest_pts"] = round(retest_pts, 1)
    if retest_blocked:
        details["blocks"].append("coin_15pct_move_retest_not_confirmed")
        return 0.0, details, True

    # ── Bottom Bounce (LONG only — +20 bonus if all 5 conditions met)
    bounce_pts = 0.0
    if direction == "LONG":
        bounce_pts, bounce_detected = score_bottom_bounce(ohlcv_15m)
        details["bounce_pts"] = round(bounce_pts, 1)
        if bounce_detected:
            details.setdefault("entry_reasons", []).append("Bottom Bounce +20")
    else:
        details["bounce_pts"] = 0.0

    # ── HTF Trend (1W + 1D)
    htf_pts, htf_blocked = score_htf_trend(ohlcv_by_tf, direction)
    details["htf_pts"] = round(htf_pts, 1)
    if htf_blocked:
        details["blocks"].append("1D_strongly_opposing")
        return 0.0, details, True

    # ── LTF Alignment (4H, 1H, 15m)
    ltf_pts, ltf_aligned, ltf_blocked = score_ltf_alignment(ohlcv_by_tf, direction)
    details["ltf_pts"]     = round(ltf_pts, 1)
    details["ltf_aligned"] = ltf_aligned
    if ltf_blocked:
        details["blocks"].append(f"only_{ltf_aligned}_LTF_aligned")
        return 0.0, details, True

    # ── BTC Context (4H EMA alignment vs direction)
    btc_pts = score_btc_context(btc_ctx.get("trend_4h", "neutral"), direction)
    details["btc_pts"]      = round(btc_pts, 1)
    details["btc_trend_4h"] = btc_ctx.get("trend_4h", "neutral")

    # ── Funding Rate
    fund_pts, fund_blocked = score_funding(exchange, symbol, direction)
    details["fund_pts"] = round(fund_pts, 1)
    if fund_blocked:
        details["blocks"].append("funding_extreme")
        return 0.0, details, True

    # ── RSI Confirming (5 pts, -10 if extreme)
    rsi_pts, rsi_val, rsi_blocked = score_rsi_confirming(closes_15m, direction)
    details["rsi"]     = round(rsi_val, 2)
    details["rsi_pts"] = round(rsi_pts, 1)
    if rsi_blocked:
        details["blocks"].append(f"RSI_extreme_{rsi_val:.1f}")
        return 0.0, details, True

    total = htf_pts + btc_pts + ltf_pts + vol_total + retest_pts + fund_pts + rsi_pts + bounce_pts
    total = max(0.0, min(100.0, total))   # cap at 100 — bounce bonus pushes score up, normalized here

    details["price"] = round(price_now, 8)
    details["total"] = round(total, 1)

    return round(total, 1), details, False

# ─────────────────────────────────────────────
#  CLAUDE ANALYSIS
# ─────────────────────────────────────────────

def call_claude(symbol: str, details: dict, direction: str) -> tuple[float, str]:
    """Returns (adjusted_score 0-100, rationale string)."""
    api_key = os.getenv("ANTHROPIC_API_KEY") or CLAUDE_API_KEY
    client = anthropic.Anthropic(api_key=api_key)

    retest_label = f"CONFIRMED +{details.get('retest_pts', 0)}" if details.get("retest_pts", 0) > 0 else "n/a"
    prompt = f"""You are MUESA, a professional crypto futures trading AI.

Review this signal for {symbol} on Binance Futures — {direction}.

Score breakdown:
  HTF Trend (1W+1D)     : {details.get('htf_pts', 0)} / 25
  BTC 4H Context ({details.get('btc_trend_4h', 'N/A')}) : {details.get('btc_pts', 0)} / 15
  LTF Align ({details.get('ltf_aligned', 0)}/3 TF)      : {details.get('ltf_pts', 0)} / 20
  Volume                : {details.get('vol_pts', 0)} / 10
  RVOL                  : {details.get('rvol_pts', 0)} / 10
  Open Interest         : {details.get('oi_pts', 0)} / 5
  Retest Detection      : {retest_label} / 15
  Funding Rate          : {details.get('fund_pts', 0)} / 5
  RSI ({details.get('rsi', 'N/A')})              : {details.get('rsi_pts', 0)} / 5
  Base total            : {details.get('total', 0)} / 100
  Price                 : {details.get('price', 'N/A')}
  Direction             : {direction}

Be conservative. Penalise weak HTF trend, poor LTF alignment, or opposing BTC context.
Return ONLY this JSON (no markdown):
{{"score": <integer 0-100>, "rationale": "<max 20 words>"}}"""

    try:
        message = client.messages.create(
            model=CLAUDE_MODEL,
            max_tokens=150,
            messages=[{"role": "user", "content": prompt}],
        )
        raw = message.content[0].text.strip()
        # Claude sometimes wraps response in markdown fences — extract the JSON object
        import re as _re
        match = _re.search(r'\{[^{}]+\}', raw, _re.DOTALL)
        if not match:
            log.error(f"Claude returned no JSON for {symbol}. Raw: {repr(raw[:120])}")
            return 0.0, "Claude analysis failed."
        data      = json.loads(match.group())
        score     = max(0, min(100, int(data.get("score", 0))))
        rationale = str(data.get("rationale", ""))
        return float(score), rationale
    except Exception as e:
        log.error(f"Claude API error for {symbol}: {e}")
        return 0.0, "Claude analysis failed."

# ─────────────────────────────────────────────
#  POSITION SIZING
# ─────────────────────────────────────────────

def get_position_size(exchange: ccxt.binanceusdm, symbol: str, price: float) -> float:
    try:
        balance   = exchange.fetch_balance()
        usdt_free = float(balance["USDT"]["free"])
        notional  = usdt_free * WALLET_ALLOC_PCT * LEVERAGE
        qty       = notional / price
        market    = exchange.market(symbol)
        step      = float(market.get("precision", {}).get("amount", 0.001))
        if step > 0:
            qty = math.floor(qty / step) * step
        return round(qty, 6)
    except Exception as e:
        log.error(f"Position sizing error for {symbol}: {e}")
        return 0.0

# ─────────────────────────────────────────────
#  TRADE EXECUTION
# ─────────────────────────────────────────────

def set_leverage_and_margin(exchange: ccxt.binanceusdm, symbol: str) -> None:
    try:
        exchange.set_leverage(LEVERAGE, symbol)
        exchange.set_margin_mode(MARGIN_MODE.lower(), symbol)
    except Exception as e:
        log.warning(f"Leverage/margin setup for {symbol}: {e}")

def _build_trade_alert(
    direction: str,
    symbol: str,
    entry: float,
    qty: float,
    sl: float,
    tp1: float,
    tp2: float,
    details: dict,
    rationale: str,
    final_score: float,
    session: str,
) -> str:
    sl_side  = "-3%" if direction == "LONG" else "+3%"
    tp1_side = "+6%" if direction == "LONG" else "-6%"
    tp2_side = "+10%" if direction == "LONG" else "-10%"
    return (
        f"*MUESA v3.0 — {direction} OPENED*\n"
        f"─────────────────────\n"
        f"Symbol  : `{symbol}`\n"
        f"Session : `{session}`\n"
        f"Entry   : `{entry}`\n"
        f"Qty     : `{qty}`\n"
        f"SL      : `{sl}` ({sl_side})\n"
        f"TP1     : `{tp1}` ({tp1_side})\n"
        f"TP2     : `{tp2}` ({tp2_side})\n"
        f"─────────────────────\n"
        f"*Score Breakdown ({final_score}/100)*\n"
        f"HTF Trend   : `{details.get('htf_pts', 0)}` / 25\n"
        f"BTC 4H ({details.get('btc_trend_4h','?')}) : `{details.get('btc_pts', 0)}` / 15\n"
        f"LTF Align   : `{details.get('ltf_pts', 0)}` / 20  ({details.get('ltf_aligned', 0)}/3 TF)\n"
        f"Volume      : `{details.get('vol_pts', 0)}` + RVOL `{details.get('rvol_pts', 0)}`\n"
        f"OI          : `{details.get('oi_pts', 0)}`\n"
        f"Retest      : `{details.get('retest_pts', 0)}` / 15\n"
        f"Funding     : `{details.get('fund_pts', 0)}`\n"
        f"RSI ({details.get('rsi','?')})   : `{details.get('rsi_pts', 0)}`\n"
        f"─────────────────────\n"
        f"AI Note : _{rationale}_"
    )

def open_long(
    exchange: ccxt.binanceusdm,
    symbol: str,
    price: float,
    details: dict,
    rationale: str,
    final_score: float,
    session: str,
) -> bool:
    """Returns True if trade was successfully opened."""
    global daily_trade_count, session_trade_count

    qty = get_position_size(exchange, symbol, price)
    if qty <= 0:
        log.warning(f"Invalid qty for {symbol}, skipping.")
        return

    sl_price  = round(price * (1 - SL_PCT), 8)
    tp1_price = round(price * (1 + TP1_PCT), 8)
    tp2_price = round(price * (1 + TP2_PCT), 8)

    try:
        set_leverage_and_margin(exchange, symbol)
        order = exchange.create_order(
            symbol=symbol, type="market", side="buy", amount=qty,
            params={"positionSide": "LONG"},
        )
        entry_price = float(order.get("average") or price)
        order_id    = order.get("id", "N/A")

        # Recalculate SL/TP from actual fill
        sl_price  = round(entry_price * (1 - SL_PCT), 8)
        tp1_price = round(entry_price * (1 + TP1_PCT), 8)
        tp2_price = round(entry_price * (1 + TP2_PCT), 8)

        exchange.create_order(
            symbol=symbol, type="stop_market", side="sell", amount=qty,
            params={"stopPrice": sl_price, "closePosition": True, "positionSide": "LONG"},
        )
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="sell",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp1_price, "positionSide": "LONG"},
        )
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="sell",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp2_price, "positionSide": "LONG"},
        )

        daily_trade_count   += 1
        session_trade_count += 1
        open_positions[symbol] = {
            "direction": "LONG", "entry": entry_price, "qty": qty,
            "sl": sl_price, "tp1": tp1_price, "tp2": tp2_price,
            "order_id": order_id, "opened_at": datetime.now(timezone.utc).isoformat(),
        }
        entry_reasons = ", ".join(details.get("entry_reasons", []))
        db_log_trade(_current_scan_id, symbol, "LONG", entry_price,
                     sl_price, tp1_price, tp2_price, qty, final_score, entry_reasons)
        log.info(f"LONG opened: {symbol} @ {entry_price}  score={final_score}")
        send_telegram(_build_trade_alert(
            "LONG", symbol, entry_price, qty, sl_price, tp1_price, tp2_price,
            details, rationale, final_score, session,
        ))
        return True
    except Exception as e:
        log.error(f"LONG order failed for {symbol}: {e}")
        send_telegram(f"*MUESA ERROR* — LONG order failed `{symbol}`:\n`{e}`")
        return False

def open_short(
    exchange: ccxt.binanceusdm,
    symbol: str,
    price: float,
    details: dict,
    rationale: str,
    final_score: float,
    session: str,
) -> bool:
    """Returns True if trade was successfully opened."""
    global daily_trade_count, session_trade_count

    qty = get_position_size(exchange, symbol, price)
    if qty <= 0:
        log.warning(f"Invalid qty for {symbol}, skipping.")
        return

    sl_price  = round(price * (1 + SL_PCT), 8)
    tp1_price = round(price * (1 - TP1_PCT), 8)
    tp2_price = round(price * (1 - TP2_PCT), 8)

    try:
        set_leverage_and_margin(exchange, symbol)
        order = exchange.create_order(
            symbol=symbol, type="market", side="sell", amount=qty,
            params={"positionSide": "SHORT"},
        )
        entry_price = float(order.get("average") or price)
        order_id    = order.get("id", "N/A")

        # Recalculate SL/TP from actual fill
        sl_price  = round(entry_price * (1 + SL_PCT), 8)
        tp1_price = round(entry_price * (1 - TP1_PCT), 8)
        tp2_price = round(entry_price * (1 - TP2_PCT), 8)

        exchange.create_order(
            symbol=symbol, type="stop_market", side="buy", amount=qty,
            params={"stopPrice": sl_price, "closePosition": True, "positionSide": "SHORT"},
        )
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="buy",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp1_price, "positionSide": "SHORT"},
        )
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="buy",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp2_price, "positionSide": "SHORT"},
        )

        daily_trade_count   += 1
        session_trade_count += 1
        open_positions[symbol] = {
            "direction": "SHORT", "entry": entry_price, "qty": qty,
            "sl": sl_price, "tp1": tp1_price, "tp2": tp2_price,
            "order_id": order_id, "opened_at": datetime.now(timezone.utc).isoformat(),
        }
        entry_reasons = ", ".join(details.get("entry_reasons", []))
        db_log_trade(_current_scan_id, symbol, "SHORT", entry_price,
                     sl_price, tp1_price, tp2_price, qty, final_score, entry_reasons)
        log.info(f"SHORT opened: {symbol} @ {entry_price}  score={final_score}")
        send_telegram(_build_trade_alert(
            "SHORT", symbol, entry_price, qty, sl_price, tp1_price, tp2_price,
            details, rationale, final_score, session,
        ))
        return True
    except Exception as e:
        log.error(f"SHORT order failed for {symbol}: {e}")
        send_telegram(f"*MUESA ERROR* — SHORT order failed `{symbol}`:\n`{e}`")
        return False

# ─────────────────────────────────────────────
#  POSITION MONITOR
# ─────────────────────────────────────────────

def sync_open_positions(exchange: ccxt.binanceusdm) -> None:
    if not open_positions:
        return
    try:
        positions    = exchange.fetch_positions()
        live_symbols = {
            p["symbol"] for p in positions
            if float(p.get("contracts") or 0) > 0
        }
        closed = [s for s in list(open_positions.keys()) if s not in live_symbols]
        for sym in closed:
            pos       = open_positions.pop(sym, {})
            direction = pos.get("direction", "LONG")
            entry     = float(pos.get("entry") or 0)
            sl        = float(pos.get("sl") or 0)

            # Detect SL hit by proximity of last price to SL
            try:
                ticker     = exchange.fetch_ticker(sym)
                last_price = float(ticker.get("last") or 0)
                sl_hit     = False
                if direction == "LONG"  and last_price > 0 and entry > 0:
                    sl_hit = last_price <= entry * (1 - SL_PCT * 0.9)
                elif direction == "SHORT" and last_price > 0 and entry > 0:
                    sl_hit = last_price >= entry * (1 + SL_PCT * 0.9)
                if sl_hit:
                    sl_hit_symbols[sym] = time.time()
                    log.info(f"SL hit detected: {sym} — {SL_COOLDOWN_HOURS}h cooldown applied")
                    db_update_trade_status(sym, "sl_hit")
                else:
                    db_update_trade_status(sym, "closed")
            except Exception:
                db_update_trade_status(sym, "closed")

            log.info(f"Position closed: {sym} [{direction}]")
            send_telegram(
                f"*MUESA — Position Closed*\n"
                f"Symbol    : `{sym}`\n"
                f"Direction : `{direction}`\n"
                f"Entry     : `{pos.get('entry', 'N/A')}`"
            )
    except Exception as e:
        log.error(f"Position sync error: {e}")

# ─────────────────────────────────────────────
#  TOP COINS BY VOLUME
# ─────────────────────────────────────────────

def get_top_symbols(exchange: ccxt.binanceusdm) -> list[tuple[str, float]]:
    """Return top N [(symbol, vol_24h)] sorted by 24h USDT volume descending.
    Fetches ALL Binance futures USDT-M perpetuals — no minimum volume filter.
    Binance futures symbols are formatted as BASE/USDT:USDT (perpetuals only).
    """
    try:
        tickers    = exchange.fetch_tickers()
        usdt_pairs = [
            (sym, float(t.get("quoteVolume") or 0))
            for sym, t in tickers.items()
            if sym.endswith("/USDT:USDT")   # perpetual futures format
        ]
        sorted_pairs = sorted(usdt_pairs, key=lambda x: x[1], reverse=True)
        result       = sorted_pairs[:TOP_N_COINS]
        log.info(f"Top {len(result)} coins by volume fetched (total USDT pairs: {len(usdt_pairs)})")
        return result
    except Exception as e:
        log.error(f"Failed to fetch tickers: {e}")
        return []

# ─────────────────────────────────────────────
#  DAILY RESET
# ─────────────────────────────────────────────

def maybe_reset_daily(now: datetime) -> None:
    global daily_trade_count, last_reset_day, last_weekly_calc_day
    if now.day != last_reset_day:
        daily_trade_count = 0
        last_reset_day    = now.day
        log.info("Daily trade counter reset.")
        # Every Sunday UTC — calculate weekly stats
        if now.weekday() == 6 and now.day != last_weekly_calc_day:
            last_weekly_calc_day = now.day
            threading.Thread(target=db_calc_weekly_stats, daemon=True).start()
            log.info("Weekly stats calculation triggered (Sunday).")

# ─────────────────────────────────────────────
#  SCAN CYCLE
# ─────────────────────────────────────────────

def run_scan(exchange: ccxt.binanceusdm, candle_close: datetime) -> None:
    global session_trade_count, current_session, _current_scan_id

    now    = datetime.now(timezone.utc)
    lag_ms = (now - candle_close).total_seconds() * 1000
    maybe_reset_daily(now)

    log.info(
        f"=== Scan started {now.strftime('%Y-%m-%d %H:%M:%S')} UTC | "
        f"candle closed {candle_close.strftime('%H:%M:%S')} UTC | "
        f"lag +{lag_ms:.0f}ms ==="
    )
    next_close = next_candle_close_utc()

    # ── Session tracking (resets per-session trade counter)
    session = get_active_session(now) or "Off-Hours"
    if session != current_session:
        session_trade_count = 0
        current_session     = session
        log.info(f"Session changed: {session}")

    log.info(f"Session: {session} | session trades: {session_trade_count}/{MAX_TRADES_SESSION} | daily: {daily_trade_count}/{MAX_TRADES_DAY}")

    sync_open_positions(exchange)

    # ── Create scan record in DB (placeholder — updated at end with totals)
    btc_prelim = get_btc_context(exchange)  # fetch here so scan_id captures BTC context
    _current_scan_id = db_create_scan(
        now.isoformat(), next_close.isoformat(),
        btc_prelim.get("trend_4h", "neutral"),
        btc_prelim.get("change_3h_pct", 0.0),
        session,
    )

    # Purge expired SL cooldowns
    cutoff  = time.time() - SL_COOLDOWN_HOURS * 3600
    expired = [s for s, ts in sl_hit_symbols.items() if ts < cutoff]
    for s in expired:
        del sl_hit_symbols[s]

    # Hard limits
    if len(open_positions) >= MAX_OPEN_POSITIONS:
        log.info(f"Max open positions ({MAX_OPEN_POSITIONS}) reached. Skipping scan.")
        return
    if session_trade_count >= MAX_TRADES_SESSION:
        log.info(f"{session} session trade limit ({MAX_TRADES_SESSION}) reached. Skipping scan.")
        return
    if daily_trade_count >= MAX_TRADES_DAY:
        log.info(f"Daily trade limit ({MAX_TRADES_DAY}) reached. Skipping scan.")
        return

    # ── BTC context (already fetched above for DB — reuse)
    btc_ctx = btc_prelim
    log.info(
        f"BTC context | 3H change: {btc_ctx['change_3h_pct']:+.2f}% | "
        f"4H trend: {btc_ctx['trend_4h']} | "
        f"block_long={btc_ctx['block_long']} block_short={btc_ctx['block_short']}"
    )

    symbol_vols = get_top_symbols(exchange)
    if not symbol_vols:
        log.warning("No symbols qualified. Skipping scan.")
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    candidates: list[tuple[float, str, str, dict, int]] = []  # (score, sym, dir, details, coin_row_id)
    signals_found = 0

    for symbol, vol_24h in symbol_vols:

        # ── Coins excluded from signal generation — log and skip
        if symbol in SIGNAL_EXCLUDE:
            log.debug(f"{symbol} — skipped (signal exclusion list)")
            for direction in ("LONG", "SHORT"):
                db_log_coin(_current_scan_id, symbol, direction, {}, True, "signal_exclusion")
            continue

        # ── Already in an open position — log and skip
        if symbol in open_positions:
            for direction in ("LONG", "SHORT"):
                db_log_coin(_current_scan_id, symbol, direction, {}, True, "open_position")
            continue

        # ── SL cooldown active — log and skip
        if symbol in sl_hit_symbols:
            log.debug(f"{symbol} — skipped (SL cooldown active)")
            for direction in ("LONG", "SHORT"):
                db_log_coin(_current_scan_id, symbol, direction, {}, True, "sl_cooldown")
            continue

        if len(open_positions) >= MAX_OPEN_POSITIONS:
            break

        ohlcv_by_tf = fetch_multi_tf_ohlcv(exchange, symbol)

        best_score     = 0.0
        best_direction = None
        best_details: dict = {}
        best_row_id: int   = -1

        for direction in ("LONG", "SHORT"):
            score, details, blocked = compute_score(
                exchange, symbol, vol_24h, ohlcv_by_tf, direction, btc_ctx
            )
            block_reason = ", ".join(details.get("blocks", [])) if blocked else ""
            # ── Log EVERY coin/direction to DB regardless of score or block status
            row_id = db_log_coin(_current_scan_id, symbol, direction, details, blocked, block_reason)

            if not blocked and score > best_score:
                best_score     = score
                best_direction = direction
                best_details   = details
                best_row_id    = row_id

        if best_direction is None or best_score < SCORE_CLAUDE_CALL:
            log.debug(f"{symbol} — best score {best_score:.1f} < {SCORE_CLAUDE_CALL}")
            continue

        signals_found += 1
        log.info(
            f"{symbol} [{best_direction}] score={best_score} >= {SCORE_CLAUDE_CALL} -> calling Claude | "
            f"htf={best_details.get('htf_pts')} ltf={best_details.get('ltf_pts')} "
            f"btc={best_details.get('btc_pts')} vol={best_details.get('vol_pts')} "
            f"rvol={best_details.get('rvol_pts')} retest={best_details.get('retest_pts')} "
            f"fund={best_details.get('fund_pts')} rsi={best_details.get('rsi_pts')}"
        )

        claude_score, rationale = call_claude(symbol, best_details, best_direction)
        final_score = round((best_score + claude_score) / 2, 1)

        log.info(
            f"{symbol} [{best_direction}] tech={best_score} claude={claude_score} "
            f"final={final_score} | {rationale}"
        )

        # ── Update coin_scores row with Claude result
        db_update_coin_claude(best_row_id, claude_score, final_score, rationale)

        if final_score >= SCORE_TRADE_EXEC:
            candidates.append((final_score, symbol, best_direction, best_details, best_row_id))
            best_details["_rationale"]   = rationale
            best_details["_final_score"] = final_score

        time.sleep(0.3)

    # Execute best candidate only (1 per scan)
    candidates.sort(key=lambda x: x[0], reverse=True)
    trades_taken = 0

    for final_score, symbol, direction, details, _row_id in candidates[:1]:
        if session_trade_count >= MAX_TRADES_SESSION:
            break
        if daily_trade_count >= MAX_TRADES_DAY:
            break
        if symbol in open_positions:
            continue

        price     = details.get("price", 0.0)
        rationale = details.get("_rationale", f"{direction} score {final_score}/100")

        if direction == "LONG":
            if open_long(exchange, symbol, price, details, rationale, final_score, session):
                trades_taken += 1
        else:
            if open_short(exchange, symbol, price, details, rationale, final_score, session):
                trades_taken += 1

    db_finish_scan(_current_scan_id, len(symbol_vols), signals_found, trades_taken)

    log.info(
        f"=== Scan complete | open: {len(open_positions)}/{MAX_OPEN_POSITIONS} | "
        f"session: {session_trade_count}/{MAX_TRADES_SESSION} | "
        f"daily: {daily_trade_count}/{MAX_TRADES_DAY} ==="
    )

# ─────────────────────────────────────────────
#  MAIN LOOP
# ─────────────────────────────────────────────

def main() -> None:
    log.info("MUESA v3.0 starting...")
    init_db()
    start_dashboard()
    send_telegram(
        "*MUESA v3.0* started.\n"
        "Sessions: Asia 01-04 | London 07-10 | New York 13-16 UTC\n"
        f"Scanning Binance Futures every {SCAN_INTERVAL_MIN} minutes (15m candle data).\n"
        f"Dashboard: http://139.59.23.165:{DASHBOARD_PORT}"
    )

    exchange = create_exchange()

    try:
        exchange.load_markets()
        log.info(f"Connected to Binance Futures — {len(exchange.markets)} markets loaded.")
    except Exception as e:
        log.critical(f"Exchange connection failed: {e}")
        send_telegram(f"*MUESA CRITICAL* — cannot connect to Binance:\n`{e}`")
        return

    while True:
        candle_close = next_candle_close_utc()
        wait         = seconds_until_scan()
        log.info(
            f"Waiting {wait:.1f}s — next candle closes at "
            f"{candle_close.strftime('%Y-%m-%d %H:%M:%S')} UTC, "
            f"scan starts +{CANDLE_BUFFER_SEC}s after close"
        )
        time.sleep(wait)

        try:
            run_scan(exchange, candle_close)
        except KeyboardInterrupt:
            log.info("MUESA stopped by user.")
            send_telegram("*MUESA v3.0* stopped manually.")
            break
        except Exception as e:
            log.error(f"Unhandled error in scan cycle: {e}")
            send_telegram(f"*MUESA ERROR* — unhandled exception:\n`{e}`")
            time.sleep(60)

if __name__ == "__main__":
    main()
