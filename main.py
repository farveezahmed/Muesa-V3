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
MIN_USDT_VOLUME      = 200_000_000   # volume scoring tier boundary (NOT a filter)
HIGH_USDT_VOLUME     = 500_000_000   # tier-1 volume threshold
TOP_N_COINS          = 100
MAX_OPEN_POSITIONS   = 1             # hard block if 1 already open
MAX_WATCHLIST        = 5             # maximum watchlist slots
WALLET_ALLOC_PCT     = 0.25
LEVERAGE             = 5
MARGIN_MODE          = "ISOLATED"
SL_PCT               = 0.03
TP1_PCT              = 0.06
TP2_PCT              = 0.10
SCORE_CLAUDE_CALL    = 65
SCORE_TRADE_EXEC     = 75
SL_COOLDOWN_HOURS    = 24
BTC_CRASH_1H_PCT     = 0.05          # 5% BTC 1H drop → market crash block (all trades)
COIN_MOVE_4H_PCT     = 0.15          # 15% coin move in last 4H candle → skip
CANDLE_BUFFER_SEC    = 5             # seconds after candle close before scanning
DASHBOARD_PORT       = 8080          # Flask dashboard port
DB_PATH              = "muesa.db"    # SQLite database file

# Symbols excluded from signal generation (too liquid / low volatility alpha)
# BTC is only used as an emergency crash detector (>5% 1H drop blocks all trades).
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
last_reset_day: int      = -1
current_session: str     = ""
sl_hit_symbols: dict[str, float] = {}   # symbol → unix timestamp of SL hit
_current_scan_id: int    = -1           # scan_id of the currently running scan
last_weekly_calc_day: int = -1          # track Sunday weekly stats calculation

# ── Bot control state (persisted to DB on change)
trading_paused: bool  = False   # pause trade execution only (scanning continues)
scanning_paused: bool = False   # pause scanning entirely (sleep mode)

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
            phase2_pts        REAL DEFAULT 0,
            fib_pts           REAL DEFAULT 0,
            oi_analysis_pts   REAL DEFAULT 0,
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

        -- ── position_checks: every 10s snapshot of each open position
        CREATE TABLE IF NOT EXISTS position_checks (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp     TEXT,
            symbol        TEXT,
            direction     TEXT,
            entry_price   REAL,
            current_price REAL,
            pnl_pct       REAL,
            pnl_usdt      REAL,
            position_size REAL
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

        -- ── bot_state: persist pause/resume state across restarts
        CREATE TABLE IF NOT EXISTS bot_state (
            key   TEXT PRIMARY KEY,
            value TEXT
        );
        INSERT OR IGNORE INTO bot_state (key,value) VALUES ('trading_paused','0');
        INSERT OR IGNORE INTO bot_state (key,value) VALUES ('scanning_paused','0');

        -- ── watchlist: user-defined coins always included in every scan
        CREATE TABLE IF NOT EXISTS watchlist (
            id       INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol   TEXT UNIQUE NOT NULL,
            added_at TEXT
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
    # ── Schema migration: add phase2_pts column to existing databases
    try:
        conn.execute("ALTER TABLE coin_scores ADD COLUMN phase2_pts REAL DEFAULT 0")
        conn.commit()
    except Exception:
        pass   # column already exists — no action needed
    try:
        conn.execute("ALTER TABLE coin_scores ADD COLUMN fib_pts REAL DEFAULT 0")
        conn.commit()
    except Exception:
        pass
    try:
        conn.execute("ALTER TABLE coin_scores ADD COLUMN oi_analysis_pts REAL DEFAULT 0")
        conn.commit()
    except Exception:
        pass
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
            " retest_pts,funding_pts,bottom_bounce_pts,phase2_pts,fib_pts,oi_analysis_pts,"
            " blocked,block_reason,entry_reasons)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
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
                round(float(details.get("phase2_pts", 0)), 2),
                round(float(details.get("fib_pts", 0)), 2),
                round(float(details.get("oi_analysis_pts", 0)), 2),
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

def db_log_position_check(
    symbol: str, direction: str, entry_price: float,
    current_price: float, pnl_pct: float, pnl_usdt: float,
    position_size: float,
) -> None:
    """Log a 10-second position snapshot to position_checks table."""
    try:
        conn = _db_conn()
        conn.execute(
            "INSERT INTO position_checks "
            "(timestamp,symbol,direction,entry_price,current_price,pnl_pct,pnl_usdt,position_size)"
            " VALUES (?,?,?,?,?,?,?,?)",
            (
                datetime.now(timezone.utc).isoformat(),
                symbol, direction,
                round(entry_price, 8),
                round(current_price, 8),
                round(pnl_pct, 4),
                round(pnl_usdt, 4),
                round(position_size, 6),
            ),
        )
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug(f"db_log_position_check error: {e}")

def db_get_state(key: str) -> str:
    """Read a bot_state value from DB."""
    try:
        conn = _db_conn()
        row  = conn.execute("SELECT value FROM bot_state WHERE key=?", (key,)).fetchone()
        conn.close()
        return row[0] if row else "0"
    except Exception:
        return "0"

def db_set_state(key: str, value: str) -> None:
    """Write a bot_state value to DB."""
    try:
        conn = _db_conn()
        conn.execute("INSERT OR REPLACE INTO bot_state (key,value) VALUES (?,?)", (key, value))
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug(f"db_set_state error: {e}")

def db_get_watchlist() -> list[dict]:
    """Return all watchlist symbols."""
    try:
        conn  = _db_conn()
        rows  = conn.execute("SELECT * FROM watchlist ORDER BY added_at DESC").fetchall()
        cols  = [d[0] for d in conn.execute("SELECT * FROM watchlist LIMIT 0").description or []]
        conn.close()
        return [dict(zip(cols, r)) for r in rows]
    except Exception:
        try:
            conn2 = _db_conn()
            rows2 = conn2.execute("SELECT id, symbol, added_at FROM watchlist ORDER BY added_at DESC").fetchall()
            conn2.close()
            return [{"id": r[0], "symbol": r[1], "added_at": r[2]} for r in rows2]
        except Exception:
            return []

def db_add_watchlist(symbol: str) -> bool:
    """Add a symbol to watchlist. Returns True if added, False if duplicate."""
    try:
        conn = _db_conn()
        conn.execute(
            "INSERT OR IGNORE INTO watchlist (symbol, added_at) VALUES (?,?)",
            (symbol, datetime.now(timezone.utc).isoformat()),
        )
        changed = conn.execute("SELECT changes()").fetchone()[0]
        conn.commit()
        conn.close()
        return changed > 0
    except Exception as e:
        log.debug(f"db_add_watchlist error: {e}")
        return False

def db_remove_watchlist(symbol: str) -> None:
    """Remove a symbol from watchlist."""
    try:
        conn = _db_conn()
        conn.execute("DELETE FROM watchlist WHERE symbol=?", (symbol,))
        conn.commit()
        conn.close()
    except Exception as e:
        log.debug(f"db_remove_watchlist error: {e}")

def db_get_watchlist_status() -> list[dict]:
    """Return watchlist coins enriched with last scan score and time."""
    items = db_get_watchlist()
    try:
        conn = _db_conn()
        for item in items:
            sym = item["symbol"]
            row = conn.execute("""
                SELECT cs.total_score, cs.final_score, cs.direction,
                       s.timestamp AS scan_time, cs.entry_reasons, cs.block_reason, cs.blocked
                FROM coin_scores cs
                LEFT JOIN scans s ON cs.scan_id = s.scan_id
                WHERE cs.symbol = ?
                ORDER BY cs.id DESC LIMIT 1
            """, (sym,)).fetchone()
            if row:
                item["last_score"]    = row[0] or 0
                item["last_final"]    = row[1] or 0
                item["last_dir"]      = row[2] or "—"
                item["last_scan"]     = (row[3] or "")[:19].replace("T", " ")
                item["last_reasons"]  = row[4] or ""
                item["last_blocked"]  = bool(row[6])
                item["block_reason"]  = row[5] or ""
            else:
                item["last_score"]   = 0
                item["last_final"]   = 0
                item["last_dir"]     = "—"
                item["last_scan"]    = "Not scanned yet"
                item["last_reasons"] = ""
                item["last_blocked"] = False
                item["block_reason"] = ""
        conn.close()
    except Exception:
        pass
    return items

def db_load_watchlist_symbols() -> set[str]:
    """Return set of watchlist symbol strings."""
    return {r["symbol"] for r in db_get_watchlist()}

def load_bot_state() -> None:
    """Load persisted pause states into memory on startup."""
    global trading_paused, scanning_paused
    trading_paused  = db_get_state("trading_paused")  == "1"
    scanning_paused = db_get_state("scanning_paused") == "1"
    if trading_paused:
        log.info("Bot state restored: TRADING PAUSED")
    if scanning_paused:
        log.info("Bot state restored: SCANNING PAUSED")

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
    watchlist   = db_get_watchlist_status()
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

    def _wl_status_badge(score: float, blocked: bool, block_reason: str) -> tuple[str, str]:
        """Return (color, label) for watchlist slot status indicator."""
        if blocked:
            return "#8b949e", f"Blocked: {block_reason[:30]}" if block_reason else "Blocked"
        if score >= SCORE_CLAUDE_CALL:
            return "#d29922", f"&#9888; Close! Score {score:.0f} — Claude threshold"
        if score >= 50:
            return "#58a6ff", f"Building — Score {score:.0f}"
        if score > 0:
            return "#8b949e", f"Weak — Score {score:.0f}"
        return "#8b949e", "Not scanned yet"

    def _wl_slot(wl_items: list, idx: int) -> str:
        """Render one watchlist slot — filled or empty."""
        slot_base = "background:#161b22;border:1px solid #30363d;border-radius:8px;padding:14px 16px;margin-bottom:10px"
        if idx < len(wl_items):
            r      = wl_items[idx]
            sym    = r["symbol"]
            score  = float(r.get("last_score") or 0)
            final  = float(r.get("last_final") or 0)
            disp_score = final if final > 0 else score
            s_color, s_label = _wl_status_badge(score, r.get("last_blocked", False), r.get("block_reason",""))
            reasons = r.get("last_reasons","") or "—"
            scan_t  = r.get("last_scan","Not scanned yet")
            dir_badge = badge(r["last_dir"]) if r["last_dir"] not in ("—","") else '<span style="color:#8b949e">—</span>'
            score_bar_w = min(100, int(disp_score))
            score_bar_c = "#2ea043" if disp_score >= SCORE_TRADE_EXEC else "#d29922" if disp_score >= SCORE_CLAUDE_CALL else "#58a6ff"
            return (
                f'<div style="{slot_base};border-left:3px solid {s_color}">'
                f'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px">'
                f'  <div style="display:flex;align-items:center;gap:10px">'
                f'    <span style="font-size:16px;font-weight:bold;color:#58a6ff">Slot {idx+1}</span>'
                f'    <b style="font-size:15px;color:#c9d1d9">{sym}</b>'
                f'    {dir_badge}'
                f'  </div>'
                f'  <form method="POST" action="/watchlist/remove" style="margin:0">'
                f'    <input type="hidden" name="symbol" value="{sym}">'
                f'    <button type="submit" style="background:#3d1010;border:1px solid #da3633;color:#da3633;border-radius:5px;padding:4px 12px;cursor:pointer;font-size:12px">Remove</button>'
                f'  </form>'
                f'</div>'
                f'<div style="background:#0d1117;border-radius:4px;height:6px;margin-bottom:8px">'
                f'  <div style="background:{score_bar_c};width:{score_bar_w}%;height:6px;border-radius:4px;transition:width .3s"></div>'
                f'</div>'
                f'<div style="display:flex;gap:20px;flex-wrap:wrap;font-size:12px;color:#8b949e">'
                f'  <span>Score: <b style="color:{score_color(disp_score)}">{disp_score:.1f}/100</b></span>'
                f'  <span>Last scan: <b style="color:#c9d1d9">{scan_t}</b></span>'
                f'  <span style="color:{s_color}">{s_label}</span>'
                f'</div>'
                f'<div style="font-size:11px;color:#8b949e;margin-top:5px">Patterns: {reasons}</div>'
                f'</div>'
            )
        else:
            return (
                f'<div style="{slot_base};border-left:3px solid #21262d;opacity:0.7">'
                f'<div style="display:flex;align-items:center;gap:8px">'
                f'  <span style="font-size:14px;color:#8b949e">Slot {idx+1} — Empty</span>'
                f'  <form method="POST" action="/watchlist/add" style="display:flex;gap:6px;margin:0">'
                f'    <input name="symbol" placeholder="e.g. NOM or SOLUSDT" style="background:#0d1117;border:1px solid #30363d;color:#c9d1d9;padding:5px 10px;border-radius:5px;font-size:12px;width:180px" />'
                f'    <button type="submit" style="background:#1f6feb;border:none;color:#fff;border-radius:5px;padding:5px 14px;cursor:pointer;font-size:12px">+ Add</button>'
                f'  </form>'
                f'</div>'
                f'</div>'
            )

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
  .ctrl-bar{{display:flex;gap:12px;align-items:center;padding:0 24px 16px;flex-wrap:wrap}}
  .ctrl-btn{{border:none;border-radius:6px;padding:8px 20px;font-size:13px;font-weight:bold;cursor:pointer;transition:opacity .15s}}
  .ctrl-btn:hover{{opacity:.8}}
  .banner{{margin:0 24px 12px;border-radius:6px;padding:10px 16px;font-weight:bold;font-size:14px;display:flex;align-items:center;gap:8px}}
  .banner-red{{background:#3d1010;border:1px solid #da3633;color:#da3633}}
  .banner-green{{background:#0d2818;border:1px solid #2ea043;color:#2ea043}}
</style>
</head><body>
<h1>&#9685; MUESA v3.0</h1>
<div class="sub">Binance Futures · Claude AI · SQLite Logging · Auto-refresh 30s</div>
<div class="refresh-bar">
  <span><span class="status-dot"></span>Bot running · Scan #{scan.get("scan_id","—")} · Session: {scan.get("session_name","—")}</span>
  <span>Updated: {datetime.now(timezone.utc).strftime('%H:%M:%S')} UTC</span>
</div>

{"<div class='banner banner-red'>&#9888; SCANNING PAUSED — Bot is in sleep mode. No scans or trades.</div>" if scanning_paused else ""}
{"<div class='banner banner-red'>&#9888; TRADING PAUSED — Scanning active but no new trades will open.</div>" if trading_paused and not scanning_paused else ""}
{"<div class='banner banner-green'>&#10003; ACTIVE — Scanning and trading running normally.</div>" if not trading_paused and not scanning_paused else ""}

<div class="ctrl-bar">
  <form method="POST" action="/toggle_trading" style="display:inline">
    <button class="ctrl-btn" style="background:{'#3d1010;color:#da3633;border:2px solid #da3633' if trading_paused else '#0d2818;color:#2ea043;border:2px solid #2ea043'}">
      {'&#9646;&#9646; TRADING: PAUSED' if trading_paused else '&#9654; TRADING: ACTIVE'}
    </button>
  </form>
  <form method="POST" action="/toggle_scanning" style="display:inline">
    <button class="ctrl-btn" style="background:{'#3d1010;color:#da3633;border:2px solid #da3633' if scanning_paused else '#0d2818;color:#2ea043;border:2px solid #2ea043'}">
      {'&#9646;&#9646; SCANNING: PAUSED' if scanning_paused else '&#9654; SCANNING: ACTIVE'}
    </button>
  </form>
  <span style="color:#8b949e;font-size:12px">Click to toggle · Changes take effect immediately</span>
</div>

<div class="grid">
  <div class="card">
    <div class="label">Last Scan</div>
    <div class="value" style="font-size:15px">{fmt_ts(scan.get("timestamp",""))}</div>
    <div class="sub-val">BTC 1H: {scan.get("btc_1h_change",0):+.2f}%{" ⚠️ CRASH BLOCK" if scan.get("btc_trend") == "crash" else ""}</div>
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
    <div class="value {'green' if trade_today==0 else 'yellow'}">{trade_today}</div>
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

<section>
  <h2>&#11088; Watchlist — {len(watchlist)}/{MAX_WATCHLIST} Slots Used · Scanned Every {SCAN_INTERVAL_MIN}m</h2>
  {"".join(_wl_slot(watchlist, i) for i in range(MAX_WATCHLIST))}
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

@_flask_app.route("/toggle_trading", methods=["POST"])
def toggle_trading():
    global trading_paused
    trading_paused = not trading_paused
    db_set_state("trading_paused", "1" if trading_paused else "0")
    state = "PAUSED" if trading_paused else "RESUMED"
    log.info(f"Trading {state} via dashboard button.")
    msg = f"*MUESA — Trading {state}*\nScanning continues. {'No new trades will open.' if trading_paused else 'Trade execution is active.'}"
    send_telegram(msg)
    return ("", 204)

@_flask_app.route("/toggle_scanning", methods=["POST"])
def toggle_scanning():
    global scanning_paused
    scanning_paused = not scanning_paused
    db_set_state("scanning_paused", "1" if scanning_paused else "0")
    state = "PAUSED" if scanning_paused else "RESUMED"
    log.info(f"Scanning {state} via dashboard button.")
    msg = f"*MUESA — Scanning {state}*\n{'Bot is in sleep mode. No scans or trades.' if scanning_paused else 'Scanning and trading are active.'}"
    send_telegram(msg)
    return ("", 204)

@_flask_app.route("/watchlist/add", methods=["POST"])
def watchlist_add():
    from flask import request as _req
    raw = (_req.form.get("symbol") or "").strip().upper()
    if not raw:
        return ("", 204)
    # Normalise: NOM → NOM/USDT:USDT,  SOLUSDT → SOL/USDT:USDT
    if raw.endswith("/USDT:USDT"):
        symbol = raw
    elif raw.endswith("USDT"):
        base   = raw[:-4]
        symbol = f"{base}/USDT:USDT"
    else:
        symbol = f"{raw}/USDT:USDT"
    current = db_get_watchlist()
    if len(current) >= MAX_WATCHLIST:
        log.warning(f"Watchlist full ({MAX_WATCHLIST} slots) — cannot add {symbol}")
        return ("Watchlist full", 400)
    added = db_add_watchlist(symbol)
    if added:
        log.info(f"Watchlist: added {symbol}")
        send_telegram(f"📋 *Watchlist Updated* — Added `{symbol}`\nWill be included in every scan.")
    return ("", 204)

@_flask_app.route("/watchlist/remove", methods=["POST"])
def watchlist_remove():
    from flask import request as _req
    symbol = (_req.form.get("symbol") or "").strip()
    if symbol:
        db_remove_watchlist(symbol)
        log.info(f"Watchlist: removed {symbol}")
        send_telegram(f"📋 *Watchlist Updated* — Removed `{symbol}`")
    return ("", 204)

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
#  STEP 1 — BTC CRASH CHECK
# ─────────────────────────────────────────────

def get_btc_crash(exchange: ccxt.binanceusdm) -> dict:
    """
    Emergency crash detector: fetch last 2 closed 1H BTC candles.
    Returns:
      crash         : bool  — BTC dropped ≥5% in last 1H candle
      change_1h_pct : float — raw 1H % change
    """
    ctx: dict = {"crash": False, "change_1h_pct": 0.0}
    try:
        ohlcv_1h = exchange.fetch_ohlcv("BTC/USDT:USDT", "1h", limit=3)
        if len(ohlcv_1h) >= 2:
            # [-2] = last fully closed candle
            prev_close = float(ohlcv_1h[-2][4])
            last_close = float(ohlcv_1h[-1][4])
            change = (last_close - prev_close) / prev_close
            ctx["change_1h_pct"] = round(change * 100, 3)
            if change <= -BTC_CRASH_1H_PCT:
                ctx["crash"] = True
    except Exception as e:
        log.error(f"BTC crash check failed: {e}")
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
#  SCORING: HTF TREND — 20 pts
# ─────────────────────────────────────────────

def score_htf_trend(ohlcv_by_tf: dict, direction: str) -> tuple[float, bool]:
    """
    1W aligned → +10 | 1D aligned → +10 | both → +20 | one → +10 | none → 0.
    No hard block — opposing daily is just 0 pts.
    Returns (points, False).
    """
    points = 0.0

    candles_1w = ohlcv_by_tf.get("1w", [])
    if ema_aligned(candles_1w, direction):
        points += 10.0

    candles_1d = ohlcv_by_tf.get("1d", [])
    if ema_aligned(candles_1d, direction):
        points += 10.0

    return points, False

# ─────────────────────────────────────────────
#  SCORING: BTC CONTEXT — 15 pts
# ─────────────────────────────────────────────

# ─────────────────────────────────────────────
#  SCORING: LTF ALIGNMENT — 15 pts
# ─────────────────────────────────────────────

def score_ltf_alignment(ohlcv_by_tf: dict, direction: str) -> tuple[float, int, bool]:
    """
    Trend alignment: 4H=+5, 1H=+5, 15m=+5 — ALL 3 must align (hard block if <3/3).
    Returns (points, aligned_count, trend_confirmed).
    """
    tf_weights = {"4h": 5.0, "1h": 5.0, "15m": 5.0}
    points        = 0.0
    aligned_count = 0

    for tf, pts in tf_weights.items():
        candles = ohlcv_by_tf.get(tf, [])
        if ema_aligned(candles, direction):
            points += pts
            aligned_count += 1

    return points, aligned_count, aligned_count >= 3

# ─────────────────────────────────────────────
#  SCORING: VOLUME & OI — 20 pts
# ─────────────────────────────────────────────

def _oi_value(entry: dict) -> float:
    return float(entry.get("openInterestValue") or entry.get("openInterest") or 0)

def score_volume_oi(
    ohlcv_15m: list,
    exchange: ccxt.binanceusdm,
    symbol: str,
    direction: str,
    price_now: float,
    price_prev: float,
) -> tuple[float, float, float, bool, float]:
    """
    RVOL: >2.0=12, 1.5-2.0=9, 1.0-1.5=6, 0.5-1.0=3, <0.5=hard block.
    OI  : rising+direction=8, flat (<0.1% change)=3, falling/against=0.
    Returns (rvol_pts, oi_pts, total, blocked, rvol_ratio).
    """
    rvol_pts   = 0.0
    rvol_ratio = 0.0
    blocked    = False

    if len(ohlcv_15m) >= 21:
        volumes = [c[5] for c in ohlcv_15m]
        avg_vol = sum(volumes[-21:-1]) / 20
        if avg_vol > 0:
            rvol       = volumes[-1] / avg_vol
            rvol_ratio = round(rvol, 3)
            if   rvol >= 2.0: rvol_pts = 12.0
            elif rvol >= 1.5: rvol_pts = 9.0
            elif rvol >= 1.0: rvol_pts = 6.0
            elif rvol >= 0.5: rvol_pts = 3.0
            else:             blocked  = True

    if rvol_ratio < 0.5:
        blocked = True

    oi_pts = 0.0
    try:
        history = exchange.fetch_open_interest_history(symbol, "15m", limit=3)
        if history and len(history) >= 2:
            oi_now  = _oi_value(history[-1])
            oi_prev = _oi_value(history[-2])
            if oi_prev > 0:
                oi_chg_pct   = abs(oi_now - oi_prev) / oi_prev
                oi_rising    = oi_now > oi_prev
                oi_flat      = oi_chg_pct < 0.001
                price_rising = price_now > price_prev
                if direction == "LONG":
                    if oi_rising and price_rising: oi_pts = 8.0
                    elif oi_flat:                  oi_pts = 3.0
                else:
                    if not oi_rising and not price_rising: oi_pts = 8.0
                    elif oi_flat:                          oi_pts = 3.0
    except Exception as e:
        log.debug(f"OI fetch failed for {symbol}: {e}")

    total = rvol_pts + oi_pts
    return rvol_pts, oi_pts, total, blocked, rvol_ratio

# ─────────────────────────────────────────────
#  SCORING: MARKET STRUCTURE BONUS — 5 pts
# ─────────────────────────────────────────────

def score_market_structure_bonus(ohlcv_15m: list, direction: str) -> tuple[float, bool]:
    """
    Award +5 when market structure aligns: HH+HL for LONG, LH+LL for SHORT.
    Independent of Phase 2 — standalone check on 15m candles.
    Returns (points, aligned).
    """
    if len(ohlcv_15m) < 20:
        return 0.0, False
    highs = [float(c[2]) for c in ohlcv_15m]
    lows  = [float(c[3]) for c in ohlcv_15m]
    aligned, _ = _detect_market_structure(highs, lows, direction)
    return (5.0, True) if aligned else (0.0, False)

# ─────────────────────────────────────────────
#  ENTRY CANDLE QUALITY CHECK — hard block
# ─────────────────────────────────────────────

def check_entry_candle_quality(ohlcv_15m: list, direction: str) -> tuple[bool, str]:
    """
    Checks the last two fully closed 15m candles for a quality entry setup.
    Returns (passed, reason_if_failed).

    LONG conditions (all must pass):
      1. Second-to-last candle is bearish (close < open) — showing pullback
      2. Last candle is bullish (close > open) — showing bounce
      3. Last candle body >= 40% of its high-to-low range — strong conviction
      4. Last candle closes in upper 60% of its range — buyers in control

    SHORT conditions (all must pass):
      1. Second-to-last candle is bullish (close > open) — showing rise
      2. Last candle is bearish (close < open) — showing rejection
      3. Last candle body >= 40% of its high-to-low range — strong conviction
      4. Last candle closes in lower 60% of its range — sellers in control
    """
    if len(ohlcv_15m) < 3:
        return False, "insufficient candle data"

    # Use last two fully closed candles ([-3] and [-2], [-1] is current open)
    prev_c = ohlcv_15m[-3]   # second-to-last closed
    last_c = ohlcv_15m[-2]   # last closed

    prev_open  = float(prev_c[1]); prev_close = float(prev_c[4])
    last_open  = float(last_c[1]); last_close = float(last_c[4])
    last_high  = float(last_c[2]); last_low   = float(last_c[3])

    candle_range = last_high - last_low
    if candle_range <= 0:
        return False, "zero range candle"

    body_size  = abs(last_close - last_open)
    body_ratio = body_size / candle_range           # condition 3: >= 0.40
    close_pos  = (last_close - last_low) / candle_range  # condition 4: position in range

    if direction == "LONG":
        # Condition 1: prev candle bearish (pullback)
        if prev_close >= prev_open:
            return False, "no pullback candle before entry"
        # Condition 2: last candle bullish (bounce)
        if last_close <= last_open:
            return False, "entry candle not bullish"
        # Condition 3: body strength
        if body_ratio < 0.40:
            return False, f"weak body {body_ratio:.0%} < 40%"
        # Condition 4: close in upper 60% of range
        if close_pos < 0.40:
            return False, f"close in lower range ({close_pos:.0%})"

    else:  # SHORT
        # Condition 1: prev candle bullish (rise)
        if prev_close <= prev_open:
            return False, "no rise candle before entry"
        # Condition 2: last candle bearish (rejection)
        if last_close >= last_open:
            return False, "entry candle not bearish"
        # Condition 3: body strength
        if body_ratio < 0.40:
            return False, f"weak body {body_ratio:.0%} < 40%"
        # Condition 4: close in lower 60% of range
        if close_pos > 0.60:
            return False, f"close in upper range ({close_pos:.0%})"

    return True, ""

# ─────────────────────────────────────────────
#  SCORING: RETEST DETECTION — 12 pts staged
# ─────────────────────────────────────────────

def score_retest_detection(
    ohlcv_4h: list,
    ohlcv_15m: list,
    direction: str,
) -> tuple[float, bool]:
    """
    Staged retest scoring — only activates when 4H move >= 15%.
    Points awarded per confirmed condition (no hard block):
      Break + Volume   : +2  (key level broken with vol surge)
      Pullback         : +3  (price pulled back/bounced >= 10% from extreme)
      Rejection Wick   : +3  (wick touched key level within 2%)
      Volume Spike     : +2  (current vol >= 1.5x avg at the retest)
      Confirm Candle   : +2  (candle closes in direction's favor)
    Returns (points, False).  Never blocks.
    """
    if not ohlcv_4h or not ohlcv_15m:
        return 0.0, False

    last_4h = ohlcv_4h[-1]
    open_4h = float(last_4h[1])
    if open_4h == 0:
        return 0.0, False

    move_4h = abs(float(last_4h[4]) - open_4h) / open_4h
    if move_4h < COIN_MOVE_4H_PCT:
        return 0.0, False   # <15% move — retest check not triggered

    closes  = [float(c[4]) for c in ohlcv_15m]
    highs   = [float(c[2]) for c in ohlcv_15m]
    lows    = [float(c[3]) for c in ohlcv_15m]
    volumes = [float(c[5]) for c in ohlcv_15m]
    last_c  = ohlcv_15m[-1]
    avg_vol = sum(volumes[-21:-1]) / 20 if len(volumes) >= 21 else 0.0
    points  = 0.0

    # Break + Volume: key level broken with volume surge
    breakout_ok, _ = _validate_breakout(ohlcv_15m, direction)
    if breakout_ok:
        points += 2.0

    if direction == "LONG":
        recent_high  = max(highs[-20:]) if len(highs) >= 20 else max(highs)
        key_level    = min(lows[-13:-3]) if len(lows) >= 13 else min(lows)
        wick_touch   = float(last_c[3])   # low wick
        confirm_ok   = float(last_c[4]) > float(last_c[1])  # green close

        # Pullback: >= 10% from recent high
        if recent_high > 0 and (recent_high - closes[-1]) / recent_high >= 0.10:
            points += 3.0
        # Rejection Wick: low wick within 2% of key support
        if key_level > 0 and abs(wick_touch - key_level) / key_level <= 0.02:
            points += 3.0

    else:  # SHORT
        recent_low   = min(lows[-20:]) if len(lows) >= 20 else min(lows)
        key_level    = max(highs[-13:-3]) if len(highs) >= 13 else max(highs)
        wick_touch   = float(last_c[2])   # high wick
        confirm_ok   = float(last_c[4]) < float(last_c[1])  # red close

        # Bounce: >= 10% from recent low
        if recent_low > 0 and (closes[-1] - recent_low) / recent_low >= 0.10:
            points += 3.0
        # Rejection Wick: high wick within 2% of key resistance
        if key_level > 0 and abs(wick_touch - key_level) / key_level <= 0.02:
            points += 3.0

    # Volume Spike: current vol >= 1.5x average
    if avg_vol > 0 and volumes[-1] >= avg_vol * 1.5:
        points += 2.0

    # Confirm Candle: closes in direction's favor
    if confirm_ok:
        points += 2.0

    log.debug(f"Retest staged [{direction}]: 4H_move={move_4h:.1%} points={points:.0f}/12")
    return points, False

# ─────────────────────────────────────────────
#  SCORING: FUNDING RATE — 4 pts
# ─────────────────────────────────────────────

def score_funding(
    exchange: ccxt.binanceusdm,
    symbol: str,
    direction: str,
) -> tuple[float, bool]:
    """
    LONG : extreme favor (<-0.05%)=+4 | favorable (<0)=+2 | neutral=+1 | against=0
           extreme against (>+0.1%) → hard block
    SHORT: extreme favor (>+0.05%)=+4 | favorable (>0)=+2 | neutral=+1 | against=0
           extreme against (<-0.1%) → hard block
    Returns (points, blocked).
    """
    try:
        fr_data = exchange.fetch_funding_rate(symbol)
        rate    = float(fr_data.get("fundingRate") or 0)
        if direction == "LONG":
            if rate >  0.001:  return 0.0, True     # extreme against → block
            if rate < -0.0005: return 4.0, False    # extreme favor
            if rate <  0:      return 2.0, False    # favorable
            return 1.0, False                        # neutral
        else:
            if rate < -0.001:  return 0.0, True     # extreme against → block
            if rate >  0.0005: return 4.0, False    # extreme favor
            if rate >  0:      return 2.0, False    # favorable
            return 1.0, False                        # neutral
    except Exception as e:
        log.debug(f"Funding rate fetch failed for {symbol}: {e}")
        return 0.0, False

# ─────────────────────────────────────────────
#  SCORING: RSI CONFIRMING — 4 pts
# ─────────────────────────────────────────────

def score_rsi_confirming(closes: list[float], direction: str) -> tuple[float, float, bool]:
    """
    Divergence (price new extreme, RSI disagrees) → +4
    Cross 50 (RSI crossed 50 in right direction last 3 candles)  → +3
    Trending  (RSI moving in right direction)                     → +2
    Flat                                                          → 0
    RSI > 80 or < 20 → hard block (0 pts, blocked=True).
    Returns (points, rsi_value, blocked).
    """
    if len(closes) < RSI_PERIOD + 6:
        return 0.0, 50.0, False

    rsi_now   = calc_rsi(closes,       RSI_PERIOD)
    rsi_prev  = calc_rsi(closes[:-3],  RSI_PERIOD)
    rsi_older = calc_rsi(closes[:-6],  RSI_PERIOD)

    if rsi_now > 80 or rsi_now < 20:
        return 0.0, rsi_now, True

    if direction == "LONG":
        # Bullish divergence: price at new 10-candle low, RSI is not
        price_new_low = closes[-1] < min(closes[-10:-1])
        if price_new_low and rsi_now > rsi_prev:
            return 4.0, rsi_now, False
        # Cross 50 from below
        if rsi_prev < 50 <= rsi_now:
            return 3.0, rsi_now, False
        # Trending up
        if rsi_now > rsi_prev > rsi_older and rsi_now >= 45:
            return 2.0, rsi_now, False
    else:  # SHORT
        # Bearish divergence: price at new 10-candle high, RSI is not
        price_new_high = closes[-1] > max(closes[-10:-1])
        if price_new_high and rsi_now < rsi_prev:
            return 4.0, rsi_now, False
        # Cross 50 from above
        if rsi_prev > 50 >= rsi_now:
            return 3.0, rsi_now, False
        # Trending down
        if rsi_now < rsi_prev < rsi_older and rsi_now <= 55:
            return 2.0, rsi_now, False

    return 0.0, rsi_now, False

# ─────────────────────────────────────────────
#  SCORING: CANDLESTICK PATTERN — 7 pts
# ─────────────────────────────────────────────

def score_candlestick(ohlcv_15m: list, direction: str) -> tuple[float, str]:
    """
    Very Strong (BullishEngulfing, MorningStar, BearishEngulfing, EveningStar) → 7 pts
    Strong      (Hammer, ShootingStar, BullPinbar, BearPinbar,
                 PiercingLine, DarkCloudCover)                                 → 5 pts
    Moderate    (any other detected pattern)                                   → 3 pts
    Returns (pts, pattern_name).
    """
    found, name = _detect_candle_pattern(ohlcv_15m, direction)
    if not found:
        return 0.0, ""
    very_strong = {"BullishEngulfing", "MorningStar", "BearishEngulfing", "EveningStar"}
    strong      = {"Hammer", "ShootingStar", "BullPinbar", "BearPinbar",
                   "PiercingLine", "DarkCloudCover"}
    if name in very_strong:
        return 7.0, name
    if name in strong:
        return 5.0, name
    return 3.0, name


# ─────────────────────────────────────────────
#  SCORING: CHART PATTERNS — 8 pts
# ─────────────────────────────────────────────

def _detect_candle_pattern(ohlcv: list, direction: str) -> tuple[bool, str]:
    """
    Scan the last 3 candles for classic reversal/continuation patterns.
    LONG  : Hammer, BullishEngulfing, PiercingLine, MorningStar, BullPinbar
    SHORT : ShootingStar, BearishEngulfing, DarkCloudCover, EveningStar, BearPinbar
    Returns (found, pattern_name).
    """
    if len(ohlcv) < 3:
        return False, ""

    c1, c2, c3 = ohlcv[-3], ohlcv[-2], ohlcv[-1]   # oldest → newest

    def anatomy(c):
        o, h, l, cl = float(c[1]), float(c[2]), float(c[3]), float(c[4])
        total      = h - l if h > l else 1e-9
        body       = abs(cl - o)
        upper_wick = h - max(o, cl)
        lower_wick = min(o, cl) - l
        return o, h, l, cl, body, total, upper_wick, lower_wick

    o1, h1, l1, c_1, b1, t1, uw1, lw1 = anatomy(c1)
    o2, h2, l2, c_2, b2, t2, uw2, lw2 = anatomy(c2)
    o3, h3, l3, c_3, b3, t3, uw3, lw3 = anatomy(c3)

    if direction == "LONG":
        # Hammer: small body, long lower wick >= 2x body AND >= 10% of range, tiny upper wick
        if (b3 <= t3 * 0.35 and lw3 >= b3 * 2.0 and lw3 >= t3 * 0.10
                and uw3 <= b3 * 0.5 and t3 > 0):
            return True, "Hammer"
        # Bullish Engulfing: prev red, curr green body fully engulfs prev body (both real bodies)
        if (c_2 < o2 and c_3 > o3 and b2 > 0 and b3 > 0
                and o3 <= c_2 and c_3 >= o2 and b3 > b2):
            return True, "BullishEngulfing"
        # Piercing Line: prev red, curr green opens below prev low, closes > 50% into prev body
        mid2 = (o2 + c_2) / 2
        if (c_2 < o2 and c_3 > o3 and b2 > 0 and b3 > 0
                and o3 < l2 and c_3 > mid2 and c_3 < o2):
            return True, "PiercingLine"
        # Morning Star: red → small/doji → green recovering > 50% into first candle
        if (c_1 < o1 and b1 > 0 and b2 <= t2 * 0.25 and c_3 > o3 and b3 > 0
                and c_3 > o1 - (o1 - c_1) * 0.5):
            return True, "MorningStar"
        # Bullish Pinbar: lower wick >= 60% of range AND > 0, close in upper 25%
        if lw3 >= t3 * 0.60 and lw3 > 0 and c_3 >= h3 - t3 * 0.25:
            return True, "BullPinbar"

    else:  # SHORT
        # Shooting Star: small body, long upper wick >= 2x body AND >= 10% of range, tiny lower wick
        if (b3 <= t3 * 0.35 and uw3 >= b3 * 2.0 and uw3 >= t3 * 0.10
                and lw3 <= b3 * 0.5 and t3 > 0):
            return True, "ShootingStar"
        # Bearish Engulfing: prev green, curr red body fully engulfs prev body (both real bodies)
        if (c_2 > o2 and c_3 < o3 and b2 > 0 and b3 > 0
                and o3 >= c_2 and c_3 <= o2 and b3 > b2):
            return True, "BearishEngulfing"
        # Dark Cloud Cover: prev green, curr red opens above prev high, closes < 50% into prev body
        mid2 = (o2 + c_2) / 2
        if (c_2 > o2 and c_3 < o3 and b2 > 0 and b3 > 0
                and o3 > h2 and c_3 < mid2 and c_3 > o2):
            return True, "DarkCloudCover"
        # Evening Star: green → small/doji → red recovering > 50% into first candle
        if (c_1 > o1 and b1 > 0 and b2 <= t2 * 0.25 and c_3 < o3 and b3 > 0
                and c_3 < o1 + (c_1 - o1) * 0.5):
            return True, "EveningStar"
        # Bearish Pinbar: upper wick >= 60% of range AND > 0, close in lower 25%
        if uw3 >= t3 * 0.60 and uw3 > 0 and c_3 <= l3 + t3 * 0.25:
            return True, "BearPinbar"

    return False, ""


def _detect_market_structure(highs: list, lows: list, direction: str) -> tuple[bool, str]:
    """
    Find last 3 pivot highs and lows; check for bullish (HH+HL) or bearish (LH+LL) structure.
    Uses a symmetric ±3-candle window on all-but-last-3 candles to avoid look-ahead bias.
    Returns (aligned_with_direction, structure_label).
    """
    if len(highs) < 20:
        return False, "insufficient_data"

    window = 3
    h = highs[:-window]   # exclude last 3 so pivots can be confirmed symmetrically
    l = lows[:-window]

    pivot_highs: list[float] = []
    pivot_lows:  list[float] = []

    for i in range(window, len(h) - window):
        seg_h = h[i - window : i + window + 1]
        seg_l = l[i - window : i + window + 1]
        if h[i] == max(seg_h) and (not pivot_highs or h[i] != pivot_highs[-1]):
            pivot_highs.append(h[i])
        if l[i] == min(seg_l) and (not pivot_lows or l[i] != pivot_lows[-1]):
            pivot_lows.append(l[i])

    if len(pivot_highs) < 2 or len(pivot_lows) < 2:
        return False, "insufficient_pivots"

    rph = pivot_highs[-min(3, len(pivot_highs)):]   # last up-to-3 pivot highs
    rpl = pivot_lows[-min(3, len(pivot_lows)):]     # last up-to-3 pivot lows

    hh = all(rph[i] > rph[i - 1] for i in range(1, len(rph)))   # Higher Highs
    hl = all(rpl[i] > rpl[i - 1] for i in range(1, len(rpl)))   # Higher Lows
    lh = all(rph[i] < rph[i - 1] for i in range(1, len(rph)))   # Lower Highs
    ll = all(rpl[i] < rpl[i - 1] for i in range(1, len(rpl)))   # Lower Lows

    if   hh and hl: structure = "HH+HL"
    elif lh and ll: structure = "LH+LL"
    else:           structure = "neutral"

    if direction == "LONG":  return (hh and hl), structure
    else:                    return (lh and ll), structure


def _validate_breakout(ohlcv: list, direction: str) -> tuple[bool, float]:
    """
    Confirm a directional breakout/breakdown with three sub-conditions:
      1. Price closed beyond the 10-candle key level (resistance or support).
      2. Current candle volume >= 1.3x the 20-period average.
      3. Candle momentum: close in the upper/lower 40% of the candle range.
    All three must be true. Returns (confirmed, key_level).
    """
    if len(ohlcv) < 25:
        return False, 0.0

    highs   = [float(c[2]) for c in ohlcv]
    lows    = [float(c[3]) for c in ohlcv]
    closes  = [float(c[4]) for c in ohlcv]
    volumes = [float(c[5]) for c in ohlcv]

    cur_h, cur_l, cur_c = highs[-1], lows[-1], closes[-1]
    cur_range = cur_h - cur_l if cur_h > cur_l else 1e-9
    avg_vol   = sum(volumes[-21:-1]) / 20
    vol_surge = avg_vol > 0 and volumes[-1] >= avg_vol * 1.3

    if direction == "LONG":
        # Resistance: highest high of last 10 fully completed candles
        key_level = max(highs[-13:-3])
        broke     = cur_c > key_level
        momentum  = (cur_c - cur_l) / cur_range >= 0.60    # close in upper 40% of range
        return (broke and vol_surge and momentum), round(key_level, 8)
    else:
        # Support: lowest low of last 10 fully completed candles
        key_level = min(lows[-13:-3])
        broke     = cur_c < key_level
        momentum  = (cur_h - cur_c) / cur_range >= 0.60    # close in lower 40% of range
        return (broke and vol_surge and momentum), round(key_level, 8)


def score_chart_patterns(ohlcv_15m: list, direction: str) -> tuple[float, str]:
    """
    Chart pattern scoring — 8 pts max:
      Very Strong (8): Phase2 all 3 components (candle+structure+breakout)
                    OR Bottom Bounce LONG (20% drop, oversold RSI, vol surge, EMA turning)
      Strong      (6): Market structure + double bottom/top confirmation
      Moderate    (4): Market structure aligned only
    Returns (pts, description).
    """
    if len(ohlcv_15m) < 30:
        return 0.0, ""

    highs = [float(c[2]) for c in ohlcv_15m]
    lows  = [float(c[3]) for c in ohlcv_15m]

    # ── Very Strong: Phase2 (candle + structure + breakout all agree)
    pattern_ok,   pattern_name = _detect_candle_pattern(ohlcv_15m, direction)
    structure_ok, struct_label = _detect_market_structure(highs, lows, direction)
    breakout_ok,  key_level    = _validate_breakout(ohlcv_15m, direction)

    log.debug(
        f"ChartPtn [{direction}]: candle={pattern_ok}({pattern_name}) "
        f"structure={structure_ok}({struct_label}) breakout={breakout_ok}(lvl={key_level})"
    )

    if pattern_ok and structure_ok and breakout_ok:
        desc = f"{pattern_name}+{struct_label}+BO@{key_level:.4f}"
        return 8.0, desc

    # ── Very Strong: Bottom Bounce (LONG only — all 5 conditions)
    if direction == "LONG" and len(ohlcv_15m) >= 50:
        closes  = [float(c[4]) for c in ohlcv_15m]
        volumes = [float(c[5]) for c in ohlcv_15m]
        window_48 = closes[-49:-1]
        high_48   = max(window_48) if window_48 else 0
        price_now = closes[-1]
        drop_pct  = (high_48 - price_now) / high_48 if high_48 > 0 else 0.0
        if drop_pct >= 0.20:
            rsi_oversold = False
            for i in range(len(closes) - 10, len(closes)):
                if i >= RSI_PERIOD:
                    r = calc_rsi(closes[:i + 1], RSI_PERIOD)
                    if r < 30:
                        rsi_oversold = True
                        break
            recent_low  = min(closes[-10:])
            bounce_pct  = (price_now - recent_low) / recent_low if recent_low > 0 else 0.0
            avg_vol_20  = sum(volumes[-21:-1]) / 20 if len(volumes) >= 21 else 0
            vol_surge   = avg_vol_20 > 0 and volumes[-1] >= avg_vol_20 * 1.5
            ema7_arr    = calc_ema(closes,       EMA_SHORT)
            ema7_prev   = calc_ema(closes[:-3],  EMA_SHORT) if len(closes) > 3 else ema7_arr
            ema_up      = (ema7_arr[-1] if ema7_arr else 0) > (ema7_prev[-1] if ema7_prev else 0)
            if rsi_oversold and bounce_pct >= 0.03 and vol_surge and ema_up:
                return 8.0, "Bottom Bounce"

    # ── Strong: Market structure + double bottom/top
    if structure_ok:
        double_pattern = False
        if len(lows) >= 20:
            if direction == "LONG":
                sorted_lows = sorted(lows[-20:])
                if len(sorted_lows) >= 2 and abs(sorted_lows[0] - sorted_lows[1]) / (sorted_lows[0] + 1e-9) < 0.02:
                    double_pattern = True
            else:
                sorted_highs = sorted(highs[-20:], reverse=True)
                if len(sorted_highs) >= 2 and abs(sorted_highs[0] - sorted_highs[1]) / (sorted_highs[0] + 1e-9) < 0.02:
                    double_pattern = True
        if double_pattern:
            dbl_label = "Double Bottom" if direction == "LONG" else "Double Top"
            return 6.0, f"{struct_label}+{dbl_label}"
        return 4.0, struct_label

    return 0.0, ""

# ─────────────────────────────────────────────
#  PATTERN 1: FIBONACCI RETRACEMENT — up to 10 pts
# ─────────────────────────────────────────────

def score_fibonacci_retracement(
    ohlcv_4h: list,
    ohlcv_15m: list,
    price_now: float,
    direction: str,
) -> tuple[float, str]:
    """
    Tiered Fibonacci scoring — requires RVOL >= 1.2 as gate:
      0.618 or 0.500 + RVOL>=1.2 + rejection bounce (0.5%) → 10 pts
      0.382 or 0.786 + RVOL>=1.2 + rejection bounce (0.5%) → 8 pts
      Any fib level  + RVOL>=1.2 (no rejection required)   → 4 pts
      RVOL < 1.2                                            → 0 pts
    Returns (pts, label).
    """
    if len(ohlcv_4h) < 10 or len(ohlcv_15m) < 22 or price_now <= 0:
        return 0.0, ""

    candles    = ohlcv_4h[-50:] if len(ohlcv_4h) >= 50 else ohlcv_4h
    swing_high = max(float(c[2]) for c in candles)
    swing_low  = min(float(c[3]) for c in candles)
    rng        = swing_high - swing_low
    if rng <= 0:
        return 0.0, ""

    levels = {
        "0.382": swing_low + 0.382 * rng,
        "0.500": swing_low + 0.500 * rng,
        "0.618": swing_low + 0.618 * rng,
        "0.786": swing_low + 0.786 * rng,
    }
    premium_levels = {"0.618", "0.500"}

    vols     = [float(c[5]) for c in ohlcv_15m]
    avg_vol  = sum(vols[-21:-1]) / 20 if len(vols) >= 21 else 0
    cur_vol  = vols[-1]
    fib_rvol = (cur_vol / avg_vol) if avg_vol > 0 else 0.0

    if fib_rvol < 1.2:
        log.debug(f"Fibonacci — RVOL={fib_rvol:.2f} < 1.2 gate")
        return 0.0, ""

    last_c    = ohlcv_15m[-1]
    last_low  = float(last_c[3])
    last_high = float(last_c[2])

    best_pts   = 0.0
    best_label = ""

    for label, level in levels.items():
        if level <= 0:
            continue

        if direction == "LONG":
            level_touched = abs(last_low - level) / level <= 0.015
            bounced       = price_now >= level * 1.005
        else:
            level_touched = abs(last_high - level) / level <= 0.015
            bounced       = price_now <= level * 0.995

        if not level_touched:
            continue

        if bounced:
            pts  = 10.0 if label in premium_levels else 8.0
            desc = f"Fibonacci {label} + RVOL{fib_rvol:.1f} + Rejection"
        else:
            pts  = 4.0
            desc = f"Fibonacci {label} + RVOL{fib_rvol:.1f}"

        if pts > best_pts:
            best_pts   = pts
            best_label = desc

    if best_pts > 0:
        log.debug(f"Fib [{direction}]: {best_label} +{best_pts:.0f}pts @ price={price_now}")
    return best_pts, best_label


# ─────────────────────────────────────────────
#  PATTERN 2: OI ANALYSIS — up to +15 pts
# ─────────────────────────────────────────────

def score_oi_analysis(
    exchange: ccxt.binanceusdm,
    symbol: str,
    direction: str,
    price_now: float,
    price_prev: float,
) -> tuple[float, list]:
    """
    Detailed Open Interest analysis — 4 directional conditions + spike bonus.

      LONG  + OI rising  + price rising  → +10  "OI Bullish Confirmation"
      SHORT + OI rising  + price falling → +10  "OI Bearish Confirmation"
      LONG  + OI falling + price rising  → +5   "Short Squeeze"
      SHORT + OI falling + price falling → +5   "Long Liquidation"
      OI grew >20% over last 4 candles   → +5   "OI Spike Detected"  (stacks)

    The spike bonus stacks on top of whichever directional condition fires.
    Returns (pts, reasons_list).
    """
    pts: float        = 0.0
    reasons: list     = []
    try:
        history = exchange.fetch_open_interest_history(symbol, "15m", limit=6)
        if not history or len(history) < 2:
            return 0.0, []

        oi_now  = _oi_value(history[-1])
        oi_prev = _oi_value(history[-2])
        if oi_prev <= 0 or oi_now <= 0:
            return 0.0, []

        oi_rising    = oi_now > oi_prev
        price_rising = price_now > price_prev

        if direction == "LONG":
            if oi_rising and price_rising:
                pts += 10.0
                reasons.append("OI Bullish Confirmation")
            elif not oi_rising and price_rising:
                pts += 5.0
                reasons.append("Short Squeeze")
        else:  # SHORT
            if oi_rising and not price_rising:
                pts += 10.0
                reasons.append("OI Bearish Confirmation")
            elif not oi_rising and not price_rising:
                pts += 5.0
                reasons.append("Long Liquidation")

        # OI spike: >20% growth over last 4 completed candles
        if len(history) >= 5:
            oi_4ago = _oi_value(history[-5])
            if oi_4ago > 0:
                spike_pct = (oi_now - oi_4ago) / oi_4ago
                if spike_pct > 0.20:
                    pts += 5.0
                    reasons.append("OI Spike Detected")

    except Exception as e:
        log.debug(f"OI analysis failed for {symbol}: {e}")

    return pts, reasons


# ─────────────────────────────────────────────
#  UNIFIED SCORER
# ─────────────────────────────────────────────

def compute_score(
    exchange: ccxt.binanceusdm,
    symbol: str,
    vol_24h: float,
    ohlcv_by_tf: dict[str, list],
    direction: str,
) -> tuple[float, dict, bool]:
    """
    100-pt scoring framework:
      HTF Trend        : 20 pts  (1W=10, 1D=10)
      LTF Alignment    : 15 pts  (4H=5, 1H=5, 15m=5 — ALL 3 required)
      RVOL             : 12 pts  (>2.0=12, 1.5=9, 1.0=6, 0.5=3, <0.5=block)
      OI               : 8 pts   (rising+direction=8, flat=3, against=0)
      Retest           : 12 pts  (staged — only when 4H move >=15%)
      Fibonacci        : 10 pts  (0.618/0.5+rvol+bounce=10, 0.382/0.786=8, touch=4)
      Chart Patterns   : 8 pts   (Very Strong=8, Strong=6, Moderate=4)
      Candlestick      : 7 pts   (Very Strong=7, Strong=5, Moderate=3)
      RSI              : 4 pts   (divergence=4, cross50=3, trending=2; >80/<20=block)
      Funding          : 4 pts   (extreme=4, favorable=2, neutral=1; extreme against=block)
    Total max: 100 pts — capped.

    6-Layer Confluence Counter (position sizing):
      Layer 1: RVOL >= 1.2
      Layer 2: OI confirmed (oi_pts >= 8)
      Layer 3: All 3 LTF aligned
      Layer 4: Structure confirmed (retest or chart pattern)
      Layer 5: Fibonacci confirmed (fib_pts > 0)
      Layer 6: RSI signal (rsi_pts >= 3)
    Minimum 3/6 to trade | 3=50% size | 4=75% | 5-6=100%

    Returns (score, details, blocked).
    """
    details: dict = {"direction": direction, "blocks": []}
    ohlcv_15m  = ohlcv_by_tf.get("15m", [])
    ohlcv_4h   = ohlcv_by_tf.get("4h",  [])
    closes_15m = [float(c[4]) for c in ohlcv_15m] if ohlcv_15m else []
    price_now  = closes_15m[-1] if closes_15m else 0.0
    price_prev = closes_15m[-2] if len(closes_15m) >= 2 else price_now

    # ── Volume & OI (RVOL=12 pts, OI=8 pts; RVOL<0.5 = hard block)
    rvol_pts, oi_pts, vol_total, vol_blocked, rvol_ratio = score_volume_oi(
        ohlcv_15m, exchange, symbol, direction, price_now, price_prev
    )
    details["rvol_pts"]  = round(rvol_pts, 1)
    details["oi_pts"]    = round(oi_pts, 1)
    details["rvol_ratio"] = rvol_ratio

    if vol_blocked:
        details["blocks"].append(f"Zero Volume Block (RVOL={rvol_ratio:.2f} < 0.5)")
        log.debug(f"Zero Volume Block [{direction}]: RVOL={rvol_ratio:.3f}")
        return 0.0, details, True

    # ── HTF Trend (1W=10, 1D=10 — no hard block)
    htf_pts, _ = score_htf_trend(ohlcv_by_tf, direction)
    details["htf_pts"] = round(htf_pts, 1)

    # ── LTF Alignment (4H+1H+15m — ALL 3 required, hard block if <3)
    ltf_pts, ltf_aligned, trend_confirmed = score_ltf_alignment(ohlcv_by_tf, direction)
    details["ltf_pts"]     = round(ltf_pts, 1)
    details["ltf_aligned"] = ltf_aligned
    if not trend_confirmed:
        details["blocks"].append(f"LTF Trend Block ({ltf_aligned}/3 aligned)")
        return 0.0, details, True

    # ── Retest Detection (staged 12 pts — never blocks)
    retest_pts, _ = score_retest_detection(ohlcv_4h, ohlcv_15m, direction)
    details["retest_pts"] = round(retest_pts, 1)
    if retest_pts > 0:
        details.setdefault("entry_reasons", []).append(f"Retest +{retest_pts:.0f}")

    # ── Fibonacci (tiered 10/8/4 pts — RVOL>=1.2 gate inside)
    fib_pts, fib_label = score_fibonacci_retracement(ohlcv_4h, ohlcv_15m, price_now, direction)
    details["fib_pts"] = round(fib_pts, 1)
    if fib_label:
        details.setdefault("entry_reasons", []).append(fib_label)

    # ── Chart Patterns (8 pts tiered)
    chart_pts, chart_desc = score_chart_patterns(ohlcv_15m, direction)
    details["chart_pts"] = round(chart_pts, 1)
    if chart_desc:
        details.setdefault("entry_reasons", []).append(f"ChartPtn: {chart_desc}")

    # ── Candlestick (7 pts tiered)
    candle_pts, candle_name = score_candlestick(ohlcv_15m, direction)
    details["candle_pts"] = round(candle_pts, 1)
    if candle_name:
        details.setdefault("entry_reasons", []).append(f"Candle: {candle_name}")

    # ── Funding Rate (4 pts tiered — extreme against = hard block)
    fund_pts, fund_blocked = score_funding(exchange, symbol, direction)
    details["fund_pts"] = round(fund_pts, 1)
    if fund_blocked:
        details["blocks"].append("funding_extreme_against")
        return 0.0, details, True

    # ── RSI (4 pts tiered — >80/<20 = hard block)
    rsi_pts, rsi_val, rsi_blocked = score_rsi_confirming(closes_15m, direction)
    details["rsi"]     = round(rsi_val, 2)
    details["rsi_pts"] = round(rsi_pts, 1)
    if rsi_blocked:
        details["blocks"].append(f"RSI_extreme_{rsi_val:.1f}")
        return 0.0, details, True

    # ── 6-Layer Confluence Counter
    layer1_vol     = rvol_ratio >= 1.2
    layer2_oi      = oi_pts >= 8.0
    layer3_trend   = trend_confirmed                         # all 3 LTF (already gated above)
    layer4_struct  = (retest_pts > 0 or chart_pts > 0)
    layer5_fib     = fib_pts > 0
    layer6_rsi     = rsi_pts >= 3

    conf_map = {
        "Volume":    layer1_vol,
        "OI":        layer2_oi,
        "Trend":     layer3_trend,
        "Structure": layer4_struct,
        "Fibonacci": layer5_fib,
        "RSI":       layer6_rsi,
    }
    confluence_count  = sum(conf_map.values())
    confluence_names  = [k for k, v in conf_map.items() if v]
    missing_names     = [k for k, v in conf_map.items() if not v]
    details["confluence"]       = confluence_count
    details["conf_confirmed"]   = ", ".join(confluence_names)
    details["ltf_aligned"]      = ltf_aligned

    log.debug(
        f"Confluence [{direction}] {confluence_count}/6 — "
        f"{', '.join(confluence_names)} | missing: {', '.join(missing_names)}"
    )

    if confluence_count < 3:
        details["blocks"].append(
            f"Confluence {confluence_count}/6 — need 3 min | missing: {', '.join(missing_names)}"
        )
        return 0.0, details, True

    # ── Position size multiplier based on confluence
    if confluence_count >= 5:
        size_mult = 1.00
    elif confluence_count == 4:
        size_mult = 0.75
    else:
        size_mult = 0.50
    details["size_mult"]       = size_mult
    details["confluence_count"] = confluence_count

    total = (htf_pts + ltf_pts + rvol_pts + oi_pts + retest_pts
             + fib_pts + chart_pts + candle_pts + fund_pts + rsi_pts)
    total = max(0.0, min(100.0, total))

    details["price"] = round(price_now, 8)
    details["total"] = round(total, 1)

    # ── Entry Candle Quality (final gate)
    candle_ok, candle_fail_reason = check_entry_candle_quality(ohlcv_15m, direction)
    if not candle_ok:
        details["blocks"].append(f"Weak Entry Candle: {candle_fail_reason}")
        log.debug(f"Entry candle quality FAILED [{direction}]: {candle_fail_reason}")
        return 0.0, details, True

    return round(total, 1), details, False

# ─────────────────────────────────────────────
#  CLAUDE ANALYSIS
# ─────────────────────────────────────────────

def call_claude(symbol: str, details: dict, direction: str) -> tuple[float, str]:
    """Returns (adjusted_score 0-100, rationale string)."""
    api_key = os.getenv("ANTHROPIC_API_KEY") or CLAUDE_API_KEY
    client = anthropic.Anthropic(api_key=api_key)

    fib_label    = next((r for r in details.get("entry_reasons", []) if r.startswith("Fibonacci")), "n/a")
    chart_label  = next((r for r in details.get("entry_reasons", []) if r.startswith("ChartPtn")), "n/a")
    candle_label = next((r for r in details.get("entry_reasons", []) if r.startswith("Candle")), "n/a")
    retest_label = next((r for r in details.get("entry_reasons", []) if r.startswith("Retest")), "n/a")
    size_pct     = int(details.get("size_mult", 1.0) * 100)
    prompt = f"""You are MUESA, a professional crypto futures trading AI.

Review this signal for {symbol} on Binance Futures — {direction}.

Score breakdown (100 pts system):
  HTF Trend (1W+1D)    : {details.get('htf_pts', 0)} / 20
  LTF Align ({details.get('ltf_aligned', 0)}/3 TF)    : {details.get('ltf_pts', 0)} / 15
  Confluence           : {details.get('conf_confirmed', '—')} ({details.get('confluence', 0)}/6)
  RVOL                 : {details.get('rvol_pts', 0)} / 12
  Open Interest        : {details.get('oi_pts', 0)} / 8
  Retest (staged)      : {retest_label} / 12
  Fibonacci            : {fib_label} / 10
  Chart Pattern        : {chart_label} / 8
  Candlestick          : {candle_label} / 7
  Funding Rate         : {details.get('fund_pts', 0)} / 4
  RSI ({details.get('rsi', 'N/A')})             : {details.get('rsi_pts', 0)} / 4
  Base total           : {details.get('total', 0)} / 100
  Position size        : {size_pct}% of allocation
  Price                : {details.get('price', 'N/A')}
  Direction            : {direction}

Be conservative. Penalise weak HTF trend, poor LTF alignment, or low confluence.
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

def get_position_size(exchange: ccxt.binanceusdm, symbol: str, price: float,
                      size_mult: float = 1.0) -> float:
    """
    size_mult: 0.50 (3/6 confluence) | 0.75 (4/6) | 1.00 (5-6/6).
    """
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
        f"HTF Trend    : `{details.get('htf_pts', 0)}` / 20\n"
        f"LTF Align    : `{details.get('ltf_pts', 0)}` / 15  ({details.get('ltf_aligned', 0)}/3 TF)\n"
        f"Confluence   : `{details.get('conf_confirmed', '—')}` ({details.get('confluence', 0)}/6)\n"
        f"RVOL         : `{details.get('rvol_pts', 0)}` / 12  (x{details.get('rvol_ratio', 0):.2f})\n"
        f"OI           : `{details.get('oi_pts', 0)}` / 8\n"
        f"Retest       : `{details.get('retest_pts', 0)}` / 12\n"
        f"Fibonacci    : `{details.get('fib_pts', 0)}` / 10\n"
        f"Chart Ptn    : `{details.get('chart_pts', 0)}` / 8\n"
        f"Candlestick  : `{details.get('candle_pts', 0)}` / 7\n"
        f"Funding      : `{details.get('fund_pts', 0)}` / 4\n"
        f"RSI ({details.get('rsi','?')})    : `{details.get('rsi_pts', 0)}` / 4\n"
        f"Size         : `{int(details.get('size_mult', 1.0) * 100)}%` of allocation\n"
        f"─────────────────────\n"
        f"Patterns    : _{', '.join(details.get('entry_reasons', [])) or 'None'}_\n"
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
    size_mult = details.get("size_mult", 1.0)
    qty = get_position_size(exchange, symbol, price, size_mult)
    if qty <= 0:
        log.warning(f"Invalid qty for {symbol}, skipping.")
        return False

    sl_price  = round(price * (1 - SL_PCT), 8)
    tp1_price = round(price * (1 + TP1_PCT), 8)
    tp2_price = round(price * (1 + TP2_PCT), 8)

    try:
        set_leverage_and_margin(exchange, symbol)
        # One-Way Mode — no positionSide in params (account is not Hedge Mode)
        order = exchange.create_order(
            symbol=symbol, type="market", side="buy", amount=qty,
        )
        entry_price = float(order.get("average") or price)
        order_id    = order.get("id", "N/A")

        # Recalculate SL/TP from actual fill price
        sl_price  = round(entry_price * (1 - SL_PCT), 8)
        tp1_price = round(entry_price * (1 + TP1_PCT), 8)
        tp2_price = round(entry_price * (1 + TP2_PCT), 8)

        # SL: closePosition closes entire position without specifying amount
        exchange.create_order(
            symbol=symbol, type="stop_market", side="sell", amount=qty,
            params={"stopPrice": sl_price, "closePosition": True},
        )
        # TP1: half position — reduceOnly ensures it only reduces, never flips
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="sell",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp1_price, "reduceOnly": True},
        )
        # TP2: remaining half
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="sell",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp2_price, "reduceOnly": True},
        )

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
    size_mult = details.get("size_mult", 1.0)
    qty = get_position_size(exchange, symbol, price, size_mult)
    if qty <= 0:
        log.warning(f"Invalid qty for {symbol}, skipping.")
        return False

    sl_price  = round(price * (1 + SL_PCT), 8)
    tp1_price = round(price * (1 - TP1_PCT), 8)
    tp2_price = round(price * (1 - TP2_PCT), 8)

    try:
        set_leverage_and_margin(exchange, symbol)
        # One-Way Mode — no positionSide in params (account is not Hedge Mode)
        order = exchange.create_order(
            symbol=symbol, type="market", side="sell", amount=qty,
        )
        entry_price = float(order.get("average") or price)
        order_id    = order.get("id", "N/A")

        # Recalculate SL/TP from actual fill price
        sl_price  = round(entry_price * (1 + SL_PCT), 8)
        tp1_price = round(entry_price * (1 - TP1_PCT), 8)
        tp2_price = round(entry_price * (1 - TP2_PCT), 8)

        # SL: closePosition closes entire position without specifying amount
        exchange.create_order(
            symbol=symbol, type="stop_market", side="buy", amount=qty,
            params={"stopPrice": sl_price, "closePosition": True},
        )
        # TP1: half position — reduceOnly ensures it only reduces, never flips
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="buy",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp1_price, "reduceOnly": True},
        )
        # TP2: remaining half
        exchange.create_order(
            symbol=symbol, type="take_profit_market", side="buy",
            amount=round(qty / 2, 6),
            params={"stopPrice": tp2_price, "reduceOnly": True},
        )

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

POSITION_CHECK_INTERVAL = 10   # seconds between position snapshots

def _log_position_snapshots(exchange: ccxt.binanceusdm) -> None:
    """
    For every open position: fetch current price, calculate PnL,
    and write a row to position_checks.  Called every 10 seconds.
    """
    for symbol, pos in list(open_positions.items()):
        try:
            direction    = pos.get("direction", "LONG")
            entry_price  = float(pos.get("entry") or 0)
            qty          = float(pos.get("qty")   or 0)
            ticker       = exchange.fetch_ticker(symbol)
            current_price = float(ticker.get("last") or 0)
            if entry_price <= 0 or current_price <= 0:
                continue
            if direction == "LONG":
                pnl_pct  = (current_price - entry_price) / entry_price * 100
                pnl_usdt = (current_price - entry_price) * qty
            else:
                pnl_pct  = (entry_price - current_price) / entry_price * 100
                pnl_usdt = (entry_price - current_price) * qty
            log.info(
                f"[POS CHECK] {symbol} {direction} | entry={entry_price} "
                f"now={current_price} | PnL={pnl_pct:+.2f}% / {pnl_usdt:+.4f} USDT | qty={qty}"
            )
            db_log_position_check(
                symbol, direction, entry_price, current_price, pnl_pct, pnl_usdt, qty
            )
        except Exception as e:
            log.debug(f"Position snapshot failed for {symbol}: {e}")


def position_monitor_loop(exchange: ccxt.binanceusdm) -> None:
    """
    Background thread: every 10 seconds check all open positions,
    log a snapshot to DB, and detect closes/SL hits.
    """
    while True:
        time.sleep(POSITION_CHECK_INTERVAL)
        if open_positions:
            _log_position_snapshots(exchange)
            sync_open_positions(exchange)


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
            sl_price  = float(pos.get("sl")    or 0)   # actual SL price stored at trade open

            # Detect SL hit: last price at or beyond the stored SL level (with 10% tolerance)
            try:
                ticker     = exchange.fetch_ticker(sym)
                last_price = float(ticker.get("last") or 0)
                sl_hit     = False
                if direction == "LONG"  and last_price > 0 and sl_price > 0:
                    sl_hit = last_price <= sl_price * 1.001   # within 0.1% above SL
                elif direction == "SHORT" and last_price > 0 and sl_price > 0:
                    sl_hit = last_price >= sl_price * 0.999   # within 0.1% below SL
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
    global last_reset_day, last_weekly_calc_day
    if now.day != last_reset_day:
        last_reset_day = now.day
        log.info("Daily counter reset.")
        # Every Sunday UTC — calculate weekly stats
        if now.weekday() == 6 and now.day != last_weekly_calc_day:
            last_weekly_calc_day = now.day
            threading.Thread(target=db_calc_weekly_stats, daemon=True).start()
            log.info("Weekly stats calculation triggered (Sunday).")

# ─────────────────────────────────────────────
#  SCAN CYCLE
# ─────────────────────────────────────────────

def run_scan(exchange: ccxt.binanceusdm, candle_close: datetime) -> None:
    global current_session, _current_scan_id

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
        current_session = session
        log.info(f"Session changed: {session}")

    log.info(f"Session: {session} | open positions: {len(open_positions)}/{MAX_OPEN_POSITIONS}")

    sync_open_positions(exchange)

    # ── BTC crash check (emergency block only — >5% 1H drop)
    btc_crash = get_btc_crash(exchange)
    _current_scan_id = db_create_scan(
        now.isoformat(), next_close.isoformat(),
        "crash" if btc_crash["crash"] else "ok",
        btc_crash.get("change_1h_pct", 0.0),
        session,
    )

    # Purge expired SL cooldowns
    cutoff  = time.time() - SL_COOLDOWN_HOURS * 3600
    expired = [s for s, ts in sl_hit_symbols.items() if ts < cutoff]
    for s in expired:
        del sl_hit_symbols[s]

    # Hard limits — finish scan record before returning so DB row isn't left with 0/0/0
    if len(open_positions) >= MAX_OPEN_POSITIONS:
        log.info(f"Max open positions ({MAX_OPEN_POSITIONS}) reached. Skipping scan.")
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    log.info(f"BTC 1H change: {btc_crash['change_1h_pct']:+.2f}% | crash_block={btc_crash['crash']}")
    if btc_crash["crash"]:
        send_telegram(
            f"⚠️ *Market Crash Detected* — BTC dropped "
            f"`{btc_crash['change_1h_pct']:.2f}%` in 1H. All trades blocked."
        )
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    symbol_vols = get_top_symbols(exchange)
    if not symbol_vols:
        log.warning("No symbols qualified. Skipping scan.")
        db_finish_scan(_current_scan_id, 0, 0, 0)
        return

    # ── Inject watchlist coins (always scanned regardless of volume ranking)
    watchlist_symbols = db_load_watchlist_symbols()
    top_symbols_set   = {s for s, _ in symbol_vols}
    if watchlist_symbols:
        tickers = {}
        try:
            tickers = exchange.fetch_tickers()
        except Exception:
            pass
        for wl_sym in sorted(watchlist_symbols):
            if wl_sym not in top_symbols_set and wl_sym not in SIGNAL_EXCLUDE:
                wl_vol = float((tickers.get(wl_sym) or {}).get("quoteVolume") or 0)
                symbol_vols.append((wl_sym, wl_vol))
                log.info(f"[WATCHLIST] {wl_sym} injected into scan (vol={wl_vol:,.0f})")
                send_telegram(f"👁 *Watchlist Scan* — Monitoring `{wl_sym}` this cycle.")

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
                exchange, symbol, vol_24h, ohlcv_by_tf, direction
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
            f"vol={best_details.get('vol_pts')} rvol={best_details.get('rvol_pts')} "
            f"oi={best_details.get('oi_pts')} struct={best_details.get('struct_pts')} "
            f"retest={best_details.get('retest_pts')} fund={best_details.get('fund_pts')} "
            f"rsi={best_details.get('rsi_pts')} phase2={best_details.get('phase2_pts')} "
            f"fib={best_details.get('fib_pts')} oi_analysis={best_details.get('oi_analysis_pts')} | "
            f"patterns=[{', '.join(best_details.get('entry_reasons', []))}]"
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

    if trading_paused:
        log.info("Trading is PAUSED — skipping trade execution this scan.")

    for final_score, symbol, direction, details, _row_id in candidates[:1]:
        if trading_paused:
            break
        if symbol in open_positions:
            continue

        price     = details.get("price", 0.0)
        rationale = details.get("_rationale", f"{direction} score {final_score}/100")

        is_watchlist = symbol in watchlist_symbols
        if is_watchlist:
            send_telegram(
                f"⭐ *Watchlist Trade Triggered!*\n"
                f"`{symbol}` [{direction}] scored `{final_score}/100`\n"
                f"Reasons: {', '.join(details.get('entry_reasons', [])) or 'N/A'}\n"
                f"Claude: _{rationale}_"
            )

        if direction == "LONG":
            if open_long(exchange, symbol, price, details, rationale, final_score, session):
                trades_taken += 1
        else:
            if open_short(exchange, symbol, price, details, rationale, final_score, session):
                trades_taken += 1

    db_finish_scan(_current_scan_id, len(symbol_vols), signals_found, trades_taken)

    log.info(
        f"=== Scan complete | open: {len(open_positions)}/{MAX_OPEN_POSITIONS} ==="
    )

# ─────────────────────────────────────────────
#  MAIN LOOP
# ─────────────────────────────────────────────

def main() -> None:
    log.info("MUESA v3.0 starting...")
    init_db()
    load_bot_state()   # restore trading_paused / scanning_paused from DB
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

    # Start background position monitor — checks every 10s, logs to DB
    threading.Thread(target=position_monitor_loop, args=(exchange,), daemon=True).start()
    log.info(f"Position monitor started — checking every {POSITION_CHECK_INTERVAL}s.")

    while True:
        # ── Scanning pause: sleep in 10s ticks so dashboard stays live and state updates apply
        if scanning_paused:
            log.info("Scanning is PAUSED — bot in sleep mode. Checking again in 10s.")
            time.sleep(10)
            continue

        candle_close = next_candle_close_utc()
        wait         = seconds_until_scan()
        log.info(
            f"Waiting {wait:.1f}s — next candle closes at "
            f"{candle_close.strftime('%Y-%m-%d %H:%M:%S')} UTC, "
            f"scan starts +{CANDLE_BUFFER_SEC}s after close"
        )
        time.sleep(wait)

        if scanning_paused:
            continue   # re-check in case paused while sleeping

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
