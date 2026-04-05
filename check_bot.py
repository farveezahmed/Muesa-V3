#!/usr/bin/env python3
"""
check_bot.py — MUESA Bot Status Checker
Run on server: python check_bot.py
Run with live refresh: watch -n 10 python check_bot.py
"""

import sqlite3
import subprocess
import sys
import os
from datetime import datetime, timezone

DB_PATH = os.path.join(os.path.dirname(__file__), "muesa.db")


def hr(char="─", n=54):
    print(char * n)


def fmt_age(seconds: float) -> str:
    if seconds < 60:
        return f"{seconds:.0f}s ago"
    elif seconds < 3600:
        return f"{seconds/60:.1f}m ago"
    else:
        return f"{seconds/3600:.1f}h ago"


def check_process() -> bool:
    """Returns True if main.py is running."""
    running = False
    try:
        result = subprocess.run(
            ["pgrep", "-fa", "python"],
            capture_output=True, text=True
        )
        for line in result.stdout.splitlines():
            if "main.py" in line:
                pid = line.split()[0]
                print(f"  ✅  Bot RUNNING  — PID {pid}")
                running = True
                break
        if not running:
            print("  ❌  Bot NOT RUNNING")
    except FileNotFoundError:
        # Windows fallback
        try:
            result = subprocess.run(
                ["tasklist", "/FI", "IMAGENAME eq python.exe"],
                capture_output=True, text=True
            )
            if "python" in result.stdout.lower():
                print("  ⚠️   Python process found (run on server for PID detail)")
            else:
                print("  ❌  No python process found")
        except Exception:
            print("  ⚠️   Process check unavailable on this OS")
    except Exception as e:
        print(f"  ⚠️   Process check error: {e}")
    return running


def check_db():
    if not os.path.exists(DB_PATH):
        print(f"\n  ❌  DB not found: {DB_PATH}")
        return

    try:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        cur  = conn.cursor()
        now  = datetime.now(timezone.utc)

        # ── Last scan
        hr()
        print("  LAST SCAN")
        hr()
        cur.execute("""
            SELECT scan_id, timestamp, total_coins, signals_found,
                   trades_taken, session_name
            FROM scans ORDER BY scan_id DESC LIMIT 1
        """)
        row = cur.fetchone()
        if row:
            ts  = row["timestamp"] or ""
            try:
                scan_dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
                age     = (now - scan_dt).total_seconds()
                age_str = fmt_age(age)
                warn    = "  ⚠️  STALE > 10 min!" if age > 600 else ""
            except Exception:
                age_str = "unknown"
                warn    = ""
            print(f"  Scan ID   : #{row['scan_id']}")
            print(f"  Time      : {ts}  ({age_str}){warn}")
            print(f"  Session   : {row['session_name'] or '—'}")
            print(f"  Coins     : {row['total_coins'] or 0} scanned")
            print(f"  Signals   : {row['signals_found'] or 0} found")
            print(f"  Trades    : {row['trades_taken'] or 0} taken")
        else:
            print("  No scans found in DB yet.")

        # ── Open positions
        hr()
        print("  OPEN POSITIONS")
        hr()
        cur.execute("""
            SELECT symbol, direction, entry_price, sl, tp1, tp2, score, timestamp
            FROM trades WHERE status='open'
            ORDER BY timestamp DESC
        """)
        positions = cur.fetchall()
        if positions:
            for p in positions:
                print(f"  {p['symbol']:<22} {p['direction']:<6} "
                      f"entry={p['entry_price']}  score={p['score']:.0f}")
                print(f"  {'':22}         "
                      f"SL={p['sl']}  TP1={p['tp1']}  TP2={p['tp2']}")
        else:
            print("  No open positions.")

        # ── Last 15 scored coins (current scan cycle)
        hr()
        print("  LAST 15 SCORED COINS (most recent scan)")
        hr()
        cur.execute("""
            SELECT cs.symbol, cs.direction, cs.total_score, cs.final_score,
                   cs.blocked, cs.block_reason, cs.entry_reasons,
                   cs.claude_score
            FROM coin_scores cs
            WHERE cs.scan_id = (SELECT MAX(scan_id) FROM scans)
            ORDER BY cs.id DESC
            LIMIT 15
        """)
        coins = cur.fetchall()
        if coins:
            for c in coins:
                if c["blocked"]:
                    reason = (c["block_reason"] or "blocked")[:35]
                    status = f"🚫 {reason}"
                else:
                    fs = c["final_score"] or c["total_score"] or 0
                    cs = c["claude_score"] or 0
                    status = f"✅ base={c['total_score']:.0f}  claude={cs:.0f}  final={fs:.0f}"
                print(f"  {c['symbol']:<22} {c['direction']:<6}  {status}")
        else:
            print("  No coins scored yet in this scan.")

        # ── Recent trades (last 5)
        hr()
        print("  RECENT TRADES (last 5)")
        hr()
        cur.execute("""
            SELECT symbol, direction, entry_price, score, status, timestamp
            FROM trades
            ORDER BY trade_id DESC LIMIT 5
        """)
        trades = cur.fetchall()
        if trades:
            for t in trades:
                icon = "🟢" if t["status"] == "open" else "⚪"
                print(f"  {icon} {t['symbol']:<22} {t['direction']:<6} "
                      f"@ {t['entry_price']}  score={t['score']:.0f}  [{t['status']}]")
        else:
            print("  No trades found.")

        hr("═")
        conn.close()

    except sqlite3.Error as e:
        print(f"\n  ❌  DB error: {e}")


def main():
    hr("═")
    print(f"  MUESA BOT STATUS — {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC")
    hr("═")
    print("  PROCESS")
    hr()
    check_process()
    check_db()


if __name__ == "__main__":
    main()
