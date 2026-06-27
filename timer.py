"""
timer.py
════════════════════════════════════════════════════════════════════════
Complete timer management system.

Contains:
  - Database layer (WAL, disk-full recovery, maintenance)
  - Session management (login, logout, validation, inactivity timeout)
  - Background tasks (timer loop, tournament loop, session cleanup, DB maintenance)
  - Safe Discord wrappers (channel edit/delete, message edit — with correct retry)
  - Panel builder (DesignerView-based admin dashboard)
  - All UI components (views, modals, selects, buttons, confirms)
  - Validation helpers
  - Timezone conversion
  - Audit + error logging
  - Startup integrity check
  - Slash command handler
"""

from __future__ import annotations

import asyncio
import os
import shutil
import sqlite3
import traceback
import uuid
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

import aiosqlite
import discord

import i as ix
from i import IxResult

# ════════════════════════════════════════════════════════════════════════
# CONFIG
# ════════════════════════════════════════════════════════════════════════

TIMER_LOG_ID = int(os.getenv("TIMER_LOG", "0"))
ERROR_LOG_ID = int(os.getenv("ERROR_LOG", os.getenv("TIMER_LOG", "0")))

DAX: set[int] = {
    1485974710847013014,
    1428800178848010331,
}

DB_PATH               = "bot.db"
MAX_YEARS_AHEAD       = 10
SESSION_TIMEOUT_SECS  = 15 * 60   # 15 minutes of inactivity

# Bot reference — set by main.py via set_bot()
_bot: discord.Bot | None = None


def set_bot(bot: discord.Bot) -> None:
    global _bot
    _bot = bot


def get_bot() -> discord.Bot:
    assert _bot is not None, "set_bot() must be called before using timer.py"
    return _bot


# ════════════════════════════════════════════════════════════════════════
# TIMEZONE OPTIONS
# ════════════════════════════════════════════════════════════════════════

TIMEZONE_OPTIONS: dict[str, str] = {
    "🇬🇧 London (GMT/BST)":        "Europe/London",
    "🇪🇺 Central Europe (CET)":    "Europe/Paris",
    "🇷🇺 Moscow (MSK)":            "Europe/Moscow",
    "🌍 East Africa (EAT)":        "Africa/Nairobi",
    "🌍 West Africa (WAT)":        "Africa/Lagos",
    "🇸🇦 Gulf / Arabia (AST)":     "Asia/Riyadh",
    "🇮🇳 India (IST)":             "Asia/Kolkata",
    "🇸🇬 Singapore (SGT)":         "Asia/Singapore",
    "🇯🇵 Japan (JST)":             "Asia/Tokyo",
    "🇦🇺 Australia/Sydney (AEST)": "Australia/Sydney",
    "🇧🇷 Brazil (BRT)":            "America/Sao_Paulo",
    "🇺🇸 US Eastern (ET)":         "America/New_York",
    "🇺🇸 US Central (CT)":         "America/Chicago",
    "🇺🇸 US Mountain (MT)":        "America/Denver",
    "🇺🇸 US Pacific (PT)":         "America/Los_Angeles",
}

# ════════════════════════════════════════════════════════════════════════
# SESSION MANAGEMENT
# guild_id → {user_id, user_name, session_id, last_activity}
# ════════════════════════════════════════════════════════════════════════

PANEL_SESSION: dict[int, dict] = {}
_SESSION_LOGIN_LOCK = asyncio.Lock()


def session_login(guild_id: int, user_id: int, user_name: str) -> str | None:
    """Create or refresh a session. Returns new session_id, or None if blocked."""
    existing = PANEL_SESSION.get(guild_id)
    if existing and existing["user_id"] != user_id:
        return None
    sid = str(uuid.uuid4())
    PANEL_SESSION[guild_id] = {
        "user_id":       user_id,
        "user_name":     user_name,
        "session_id":    sid,
        "last_activity": datetime.now(timezone.utc),
    }
    return sid


def session_logout(guild_id: int, user_id: int) -> None:
    s = PANEL_SESSION.get(guild_id)
    if s and s["user_id"] == user_id:
        del PANEL_SESSION[guild_id]


def get_session(guild_id: int) -> dict | None:
    return PANEL_SESSION.get(guild_id)


def validate_session(guild_id: int, user_id: int, session_id: str) -> bool:
    """True only when user+session match and session is not timed out."""
    s = PANEL_SESSION.get(guild_id)
    if not s:
        return False
    if s["user_id"] != user_id or s["session_id"] != session_id:
        return False
    elapsed = (datetime.now(timezone.utc) - s["last_activity"]).total_seconds()
    if elapsed > SESSION_TIMEOUT_SECS:
        del PANEL_SESSION[guild_id]
        return False
    return True


def touch_session(guild_id: int, user_id: int, session_id: str) -> None:
    s = PANEL_SESSION.get(guild_id)
    if s and s["user_id"] == user_id and s["session_id"] == session_id:
        s["last_activity"] = datetime.now(timezone.utc)


def session_is_expired(guild_id: int) -> bool:
    s = PANEL_SESSION.get(guild_id)
    if not s:
        return False
    elapsed = (datetime.now(timezone.utc) - s["last_activity"]).total_seconds()
    return elapsed > SESSION_TIMEOUT_SECS


# ════════════════════════════════════════════════════════════════════════
# IN-MEMORY STATE
# ════════════════════════════════════════════════════════════════════════

# (guild_id, user_id) → selected timer channel_id
CURRENT_SELECTION: dict[tuple[int, int], str] = {}

# Per-guild in-flight debounce keys
_DEBOUNCE: dict[int, set] = {}


def _debounce_acquire(guild_id: int, key: str) -> bool:
    s = _DEBOUNCE.setdefault(guild_id, set())
    if key in s:
        return False
    s.add(key)
    return True


def _debounce_release(guild_id: int, key: str) -> None:
    _DEBOUNCE.get(guild_id, set()).discard(key)


# Mutex protecting tournament channel creation against race conditions
_TOURNAMENT_CREATION_LOCK = asyncio.Lock()

# ════════════════════════════════════════════════════════════════════════
# DATABASE LAYER
# Single shared WAL connection, serialised by asyncio lock.
#
# Failure model
# ─────────────
# sqlite3.OperationalError: database or disk is full
#   The write has NOT been applied. Discord-side action must be
#   aborted so DB and Discord state remain in sync.
#
# Recovery hierarchy (cheapest → most expensive)
#   1. PRAGMA wal_checkpoint(TRUNCATE) — flush + truncate WAL to 0 bytes
#   2. Retry the original statement once
#   3. If still failing: raise DBDiskFullError
#
# Note: VACUUM is NOT used during disk-full recovery — VACUUM needs free
# space equal to the DB size and will fail on a full disk, compounding
# the problem. VACUUM runs only on the scheduled maintenance path.
# ════════════════════════════════════════════════════════════════════════

_WAL_SIZE_LIMIT_BYTES  = 64 * 1024 * 1024   # 64 MB hard cap
_WAL_AUTOCHECKPOINT    = 500                 # pages (~2 MB at default page size)
_MAINTENANCE_INTERVAL_HOURS = 6
_DISK_WARN_THRESHOLD_MB     = 200


class DBError(RuntimeError):
    """Base class for database layer errors."""


class DBDiskFullError(DBError):
    """
    Raised when SQLite cannot commit because the filesystem is full.
    The attempted write has NOT been applied. Discord-side state must
    NOT be changed when this is raised — abort the operation entirely.
    """


_DB_CONN: aiosqlite.Connection | None = None
_DB_LOCK = asyncio.Lock()


async def _get_db() -> aiosqlite.Connection:
    global _DB_CONN
    if _DB_CONN is None:
        _DB_CONN = await aiosqlite.connect(DB_PATH)
        _DB_CONN.row_factory = aiosqlite.Row
        await _DB_CONN.execute("PRAGMA journal_mode=WAL")
        await _DB_CONN.execute(f"PRAGMA journal_size_limit={_WAL_SIZE_LIMIT_BYTES}")
        await _DB_CONN.execute(f"PRAGMA wal_autocheckpoint={_WAL_AUTOCHECKPOINT}")
        await _DB_CONN.execute("PRAGMA synchronous=NORMAL")
        await _DB_CONN.execute("PRAGMA foreign_keys=ON")
        await _DB_CONN.execute("PRAGMA temp_store=MEMORY")
        await _DB_CONN.execute("PRAGMA cache_size=-8192")
    return _DB_CONN


def _is_disk_full(exc: Exception) -> bool:
    msg = str(exc).lower()
    return "disk" in msg or "full" in msg or "no space" in msg


async def _emergency_checkpoint() -> bool:
    try:
        db = await _get_db()
        await db.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        await db.commit()
        print("[DB] Emergency WAL checkpoint(TRUNCATE) completed.")
        return True
    except Exception as e:
        print(f"[DB] Emergency checkpoint failed: {e}")
        return False


async def _db_exec(sql: str, params: tuple = ()) -> None:
    async with _DB_LOCK:
        db = await _get_db()
        for attempt in range(2):
            try:
                await db.execute(sql, params)
                await db.commit()
                return
            except Exception as exc:
                if _is_disk_full(exc):
                    if attempt == 0:
                        print(f"[DB] Disk-full — emergency checkpoint. SQL: {sql[:80]}")
                        await _emergency_checkpoint()
                        continue
                    raise DBDiskFullError(
                        "SQLite commit failed: database or disk is full. "
                        f"SQL: {sql[:120]}"
                    ) from exc
                raise DBError(f"Database write failed: {exc}  SQL: {sql[:120]}") from exc


async def _db_one(sql: str, params: tuple = ()):
    async with _DB_LOCK:
        db = await _get_db()
        try:
            async with db.execute(sql, params) as cur:
                return await cur.fetchone()
        except Exception as exc:
            raise DBError(f"Database read failed: {exc}  SQL: {sql[:120]}") from exc


async def _db_all(sql: str, params: tuple = ()) -> list:
    async with _DB_LOCK:
        db = await _get_db()
        try:
            async with db.execute(sql, params) as cur:
                return await cur.fetchall()
        except Exception as exc:
            raise DBError(f"Database read failed: {exc}  SQL: {sql[:120]}") from exc


# ── Disk usage helpers ───────────────────────────────────────────────

def _db_file_sizes() -> dict[str, int]:
    return {
        "db":  os.path.getsize(DB_PATH)           if os.path.exists(DB_PATH)           else 0,
        "wal": os.path.getsize(DB_PATH + "-wal")  if os.path.exists(DB_PATH + "-wal")  else 0,
    }


def _free_disk_mb() -> float:
    try:
        return shutil.disk_usage(os.path.dirname(os.path.abspath(DB_PATH))).free / (1024 * 1024)
    except Exception:
        return -1.0


# ── Maintenance ───────────────────────────────────────────────────────

async def db_maintenance() -> dict:
    stats: dict = {
        "started_at": datetime.now(timezone.utc).isoformat(),
        "before":     _db_file_sizes(),
        "free_mb":    _free_disk_mb(),
        "checkpoint": False,
        "truncate":   False,
        "vacuum":     False,
        "errors":     [],
    }

    async with _DB_LOCK:
        db = await _get_db()

        try:
            await db.execute("PRAGMA wal_checkpoint(FULL)")
            await db.commit()
            stats["checkpoint"] = True
        except Exception as e:
            stats["errors"].append(f"checkpoint(FULL): {e}")

        try:
            await db.execute("PRAGMA wal_checkpoint(TRUNCATE)")
            await db.commit()
            stats["truncate"] = True
        except Exception as e:
            stats["errors"].append(f"checkpoint(TRUNCATE): {e}")

        free_mb = _free_disk_mb()
        db_mb   = stats["before"]["db"] / (1024 * 1024)
        if free_mb < 0 or free_mb > max(db_mb * 1.5, _DISK_WARN_THRESHOLD_MB * 2):
            try:
                await db.execute("VACUUM")
                await db.commit()
                stats["vacuum"] = True
            except Exception as e:
                stats["errors"].append(f"VACUUM: {e}")
        else:
            stats["errors"].append(
                f"VACUUM skipped — free disk {free_mb:.0f} MB below safe threshold"
            )

    stats["after"]       = _db_file_sizes()
    stats["finished_at"] = datetime.now(timezone.utc).isoformat()
    return stats


async def db_maintenance_loop() -> None:
    await get_bot().wait_until_ready()
    await asyncio.sleep(60)   # let integrity check complete first

    while True:
        try:
            stats = await db_maintenance()

            before_db  = stats["before"]["db"]  / (1024 * 1024)
            before_wal = stats["before"]["wal"] / (1024 * 1024)
            after_db   = stats["after"]["db"]   / (1024 * 1024)
            after_wal  = stats["after"]["wal"]  / (1024 * 1024)
            free_mb    = stats["free_mb"]

            result = "warn" if (stats["errors"] or (0 <= free_mb < _DISK_WARN_THRESHOLD_MB)) else "ok"

            lines = [
                f"DB:  {before_db:.2f} MB → {after_db:.2f} MB",
                f"WAL: {before_wal:.2f} MB → {after_wal:.2f} MB",
                f"Free: {free_mb:.0f} MB",
                f"Checkpoint {'✅' if stats['checkpoint'] else '❌'}  "
                f"Truncate {'✅' if stats['truncate'] else '❌'}  "
                f"VACUUM {'✅' if stats['vacuum'] else '❌'}",
            ]
            if stats["errors"]:
                lines.append("Errors: " + " | ".join(stats["errors"]))
            if 0 <= free_mb < _DISK_WARN_THRESHOLD_MB:
                lines.append(f"⚠️ LOW DISK: {free_mb:.0f} MB free")

            await audit_log(
                action="DB MAINTENANCE",
                result=result,
                detail="\n".join(lines),
            )
        except Exception as e:
            await log_error("db_maintenance_loop", e)

        await asyncio.sleep(_MAINTENANCE_INTERVAL_HOURS * 3600)


async def _handle_db_disk_full(location: str, exc: DBDiskFullError, context: str = "") -> None:
    free_mb = _free_disk_mb()
    sizes   = _db_file_sizes()
    detail  = (
        f"Operation: {location}\n"
        f"Context: {context or 'n/a'}\n"
        f"DB: {sizes['db'] / (1024*1024):.2f} MB  "
        f"WAL: {sizes['wal'] / (1024*1024):.2f} MB  "
        f"Free: {free_mb:.0f} MB\n"
        f"Write was NOT applied. Discord state was NOT changed."
    )
    await log_error(f"DB DISK FULL — {location}", exc, detail)
    await audit_log(action="DB DISK FULL — WRITE ABORTED", result="error", detail=detail)


# ════════════════════════════════════════════════════════════════════════
# DATABASE INIT + PUBLIC HELPERS
# ════════════════════════════════════════════════════════════════════════

async def init_db() -> None:
    async with _DB_LOCK:
        db = await _get_db()
        await db.executescript("""
            CREATE TABLE IF NOT EXISTS timers (
                channel_id  TEXT PRIMARY KEY,
                name        TEXT NOT NULL,
                end_time    TEXT NOT NULL,
                warned      INTEGER NOT NULL DEFAULT 0,
                no_delete   INTEGER NOT NULL DEFAULT 0,
                ended       INTEGER NOT NULL DEFAULT 0,
                last_check  TEXT
            );
            CREATE TABLE IF NOT EXISTS tournament_channels (
                channel_id  TEXT PRIMARY KEY,
                message_id  TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS tournament_settings (
                id          INTEGER PRIMARY KEY CHECK (id = 1),
                skip_next   INTEGER NOT NULL DEFAULT 0
            );
            INSERT OR IGNORE INTO tournament_settings (id, skip_next) VALUES (1, 0);
        """)
        try:
            await db.execute(
                "ALTER TABLE timers ADD COLUMN ended INTEGER NOT NULL DEFAULT 0"
            )
        except Exception:
            pass   # column already exists
        await db.commit()


# ── Timer CRUD ────────────────────────────────────────────────────────

async def db_get_timer(channel_id: str):
    return await _db_one("SELECT * FROM timers WHERE channel_id = ?", (channel_id,))


async def db_all_timers() -> list:
    return await _db_all("SELECT * FROM timers")


async def db_upsert_timer(
    channel_id: str, name: str, end_time: str,
    warned: bool = False, no_delete: bool = False,
    ended: bool = False, last_check: str | None = None,
) -> None:
    try:
        await _db_exec("""
            INSERT INTO timers (channel_id, name, end_time, warned, no_delete, ended, last_check)
            VALUES (?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(channel_id) DO UPDATE SET
                name=excluded.name, end_time=excluded.end_time,
                warned=excluded.warned, no_delete=excluded.no_delete,
                ended=excluded.ended, last_check=excluded.last_check
        """, (channel_id, name, end_time, int(warned), int(no_delete), int(ended), last_check))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_upsert_timer", e, f"name={name}")
        raise
    except DBError as e:
        await log_error("db_upsert_timer", e, f"channel_id={channel_id}")
        raise


async def db_update_timer_field(channel_id: str, **kwargs) -> None:
    allowed  = {"name", "end_time", "warned", "no_delete", "ended", "last_check"}
    filtered = {k: v for k, v in kwargs.items() if k in allowed}
    if not filtered:
        return
    sets = ", ".join(f"{k} = ?" for k in filtered)
    vals = tuple(int(v) if isinstance(v, bool) else v for v in filtered.values())
    try:
        await _db_exec(f"UPDATE timers SET {sets} WHERE channel_id = ?", (*vals, channel_id))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_update_timer_field", e, f"fields={list(filtered)}")
        raise
    except DBError as e:
        await log_error("db_update_timer_field", e, f"channel_id={channel_id}")
        raise


async def db_delete_timer(channel_id: str) -> None:
    try:
        await _db_exec("DELETE FROM timers WHERE channel_id = ?", (channel_id,))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_delete_timer", e, channel_id)
        raise
    except DBError as e:
        await log_error("db_delete_timer", e, f"channel_id={channel_id}")
        raise


# ── Tournament CRUD ───────────────────────────────────────────────────

async def db_all_tournament_channels() -> list:
    return await _db_all("SELECT * FROM tournament_channels")


async def db_add_tournament_channel(channel_id: str, message_id: str) -> None:
    try:
        await _db_exec(
            "INSERT OR REPLACE INTO tournament_channels (channel_id, message_id) VALUES (?, ?)",
            (channel_id, message_id),
        )
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_add_tournament_channel", e, f"channel_id={channel_id}")
        raise
    except DBError as e:
        await log_error("db_add_tournament_channel", e)
        raise


async def db_delete_tournament_channel(channel_id: str) -> None:
    try:
        await _db_exec("DELETE FROM tournament_channels WHERE channel_id = ?", (channel_id,))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_delete_tournament_channel", e, f"channel_id={channel_id}")
        raise
    except DBError as e:
        await log_error("db_delete_tournament_channel", e)
        raise


async def db_get_skip_next() -> bool:
    row = await _db_one("SELECT skip_next FROM tournament_settings WHERE id = 1")
    return bool(row["skip_next"]) if row else False


async def db_set_skip_next(value: bool) -> None:
    try:
        await _db_exec(
            "UPDATE tournament_settings SET skip_next = ? WHERE id = 1", (int(value),)
        )
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_set_skip_next", e, f"value={value}")
        raise
    except DBError as e:
        await log_error("db_set_skip_next", e)
        raise


# ════════════════════════════════════════════════════════════════════════
# STRUCTURED LOGGING
# ════════════════════════════════════════════════════════════════════════

async def audit_log(
    action: str,
    guild=None,
    user=None,
    target_channel=None,
    result: str = "ok",
    detail: str = "",
    session_id: str = "",
) -> None:
    bot    = get_bot()
    log_ch = bot.get_channel(TIMER_LOG_ID)
    if not log_ch:
        return

    r = result.lower()
    if r in ("blocked", "error", "failed"):
        color, icon = discord.Color.red(), "🚨"
    elif r in ("warn", "warning", "expired"):
        color, icon = discord.Color.yellow(), "⚠️"
    else:
        color, icon = discord.Color.green(), "✅"

    ts = datetime.now(timezone.utc)

    view = discord.ui.DesignerView(timeout=None)
    c    = discord.ui.Container(color=color)
    c.add_text(f"{icon} **{action}**")
    c.add_separator(divider=True)

    lines = [f"<t:{int(ts.timestamp())}:F>  `[{result.upper()}]`"]
    if guild:
        lines.append(f"Guild: {guild.name}")
    if user:
        lines.append(f"User: {user.display_name} (`{user.id}`)")
    if target_channel:
        ch_str = target_channel.mention if hasattr(target_channel, "mention") else str(target_channel)
        lines.append(f"Channel: {ch_str}")
    if session_id:
        lines.append(f"Session: `{session_id[:8]}…`")
    if detail:
        lines.append(detail)

    c.add_text("\n".join(lines))
    view.add_item(c)

    try:
        await log_ch.send(view=view)
    except Exception:
        pass


async def log_error(location: str, error: Exception, extra: str = "") -> None:
    tb        = traceback.format_exc()
    timestamp = datetime.now(timezone.utc)
    print(f"[ERROR][{location}] {error}\n{tb}")

    bot    = get_bot()
    log_ch = bot.get_channel(ERROR_LOG_ID)
    if not log_ch:
        return

    tb_short = tb[-900:] if len(tb) > 900 else tb

    view = discord.ui.DesignerView(timeout=None)
    c    = discord.ui.Container(color=discord.Color.red())
    c.add_text(f"❌ **Error in `{location}`**")
    c.add_separator(divider=True)
    c.add_text(f"<t:{int(timestamp.timestamp())}:F>")
    c.add_separator()
    c.add_text(f"**Error:**\n```\n{str(error)[:600]}\n```")
    if extra:
        c.add_separator()
        c.add_text(f"**Context:**\n{extra[:400]}")
    c.add_separator()
    c.add_text(f"**Traceback:**\n```py\n{tb_short}\n```")
    view.add_item(c)

    try:
        await log_ch.send(view=view)
    except Exception:
        pass


async def send_timer_log(
    title: str, timer_name: str, end_time: datetime,
    channel=None, extra: str | None = None,
) -> None:
    bot    = get_bot()
    log_ch = bot.get_channel(TIMER_LOG_ID)
    if not log_ch:
        return

    is_ended = "ENDED" in title.upper()
    color    = discord.Color.red() if is_ended else discord.Color.blurple()

    view = discord.ui.DesignerView(timeout=None)
    c    = discord.ui.Container(color=color)
    c.add_text(f"📡 **{title}**\n\n**{timer_name}**")
    c.add_separator(divider=True)
    c.add_text(
        f"Ends: <t:{int(end_time.timestamp())}:F>\n"
        f"Remaining: <t:{int(end_time.timestamp())}:R>"
    )
    if channel:
        c.add_separator()
        c.add_text(f"Channel: {channel.mention}")
    if extra:
        c.add_separator()
        c.add_text(extra)
    view.add_item(c)

    try:
        await log_ch.send(view=view)
    except Exception:
        pass


# ════════════════════════════════════════════════════════════════════════
# VALIDATION
# ════════════════════════════════════════════════════════════════════════

def validate_end_time(end: datetime) -> str | None:
    now = datetime.now(timezone.utc)
    if end <= now:
        return "That time is in the past. Please enter a future date and time."
    max_end = now + timedelta(days=int(365.25 * MAX_YEARS_AHEAD))
    if end > max_end:
        return (
            f"Date too far in the future.\n"
            f"Maximum: **{max_end.strftime('%Y-%m-%d')}** (current year + {MAX_YEARS_AHEAD})."
        )
    return None


# ════════════════════════════════════════════════════════════════════════
# TOURNAMENT REGIONS
# ════════════════════════════════════════════════════════════════════════

def get_regions(week_offset: int = 0) -> list[dict]:
    now    = datetime.now(timezone.utc)
    friday = (now - timedelta(days=now.weekday() - 4)).replace(
        hour=0, minute=0, second=0, microsecond=0
    ) + timedelta(weeks=week_offset)

    def build(fri):
        return [
            {"name": "🌏 Asia & Middle East",
             "start": fri.replace(hour=8),
             "end":   (fri + timedelta(days=2)).replace(hour=13)},
            {"name": "🌍 Africa & Europe",
             "start": fri.replace(hour=18),
             "end":   (fri + timedelta(days=2)).replace(hour=23)},
            {"name": "🌎 America",
             "start": (fri + timedelta(days=1)).replace(hour=0),
             "end":   (fri + timedelta(days=3)).replace(hour=5)},
        ]

    if week_offset != 0:
        return build(friday)

    this_week = build(friday)
    last_end  = max(r["end"] for r in this_week)
    if any(r["start"] <= now <= r["end"] for r in this_week) or now <= last_end + timedelta(days=1):
        return this_week
    return build(friday + timedelta(days=7))


# ════════════════════════════════════════════════════════════════════════
# TOURNAMENT VIEW BUILDER
# ════════════════════════════════════════════════════════════════════════

COLOR_LIVE     = discord.Color(0x01B201)
COLOR_UPCOMING = discord.Color(0xFFD800)
COLOR_ENDED    = discord.Color(0xD51717)


def build_tournament_view(skipped: bool = False) -> discord.ui.DesignerView:
    view   = discord.ui.DesignerView()
    now    = datetime.now(timezone.utc)
    offset = 1 if skipped else 0

    regions  = get_regions(week_offset=offset)
    last_end = max(r["end"] for r in regions)

    for region in regions:
        if now < region["start"]:
            color, status = COLOR_UPCOMING, "🟡 UPCOMING"
        elif region["start"] <= now <= region["end"]:
            color, status = COLOR_LIVE, "🟢 LIVE"
        else:
            color, status = COLOR_ENDED, "🔴 ENDED"

        c = discord.ui.Container(color=color)
        c.add_text(f"**{region['name']} — {status}**")
        c.add_separator()
        c.add_text(
            f"Start: <t:{int(region['start'].timestamp())}:F>\n"
            f"End:   <t:{int(region['end'].timestamp())}:F>"
        )
        view.add_item(c)

    all_ended = all(now > r["end"] for r in regions)
    if all_ended and now <= last_end + timedelta(days=1):
        c2           = discord.ui.Container(color=discord.Color.dark_gray())
        next_regions = get_regions(week_offset=offset + 1)
        next_start   = min(r["start"] for r in next_regions)
        c2.add_text(f"Next tournament starts <t:{int(next_start.timestamp())}:R>")
        view.add_item(c2)

    return view


# ════════════════════════════════════════════════════════════════════════
# CHANNEL-NAME HELPER
# ════════════════════════════════════════════════════════════════════════

def format_timer_channel_name(name: str, end: datetime) -> str:
    secs = (end - datetime.now(timezone.utc)).total_seconds()
    if secs <= 0:
        return f"⏲️ {name} » ENDED"
    elif secs < 3600:
        return f"⏲️ {name} » {max(0, int(secs // 60))}M"
    else:
        diff = end - datetime.now(timezone.utc)
        return f"⏲️ {name} » {diff.days}D {diff.seconds // 3600}H"


# ════════════════════════════════════════════════════════════════════════
# SAFE DISCORD WRAPPERS
#
# The original code used `discord.RateLimited` which does not exist in
# Pycord / discord.py. This caused an AttributeError that masked the
# actual network error. All wrappers now use proper exception types:
#   - discord.HTTPException (with status 429 check for rate limits)
#   - discord.DiscordServerError (5xx transient errors)
#   - discord.NotFound (404 — channel/message gone)
#   - asyncio.TimeoutError (connection timeout)
#   - aiohttp.ClientError (network-level errors)
# Transient failures (429, 5xx, timeouts) are retried with exponential
# backoff. Non-transient failures are logged and return False immediately.
# ════════════════════════════════════════════════════════════════════════

def _is_rate_limited(exc: discord.HTTPException) -> bool:
    """True if the HTTP exception is a 429 rate limit response."""
    return getattr(exc, "status", 0) == 429


def _retry_after(exc: discord.HTTPException) -> float:
    """Extract retry_after from a 429 response, defaulting to 1.0 s."""
    return float(getattr(exc, "retry_after", 1.0))


async def safe_channel_edit(channel, retries: int = 3, **kwargs) -> bool:
    for attempt in range(retries + 1):
        try:
            await channel.edit(**kwargs)
            return True
        except discord.NotFound:
            return False
        except discord.HTTPException as e:
            if _is_rate_limited(e):
                await asyncio.sleep(_retry_after(e) + 0.5)
                continue
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
            else:
                await log_error("safe_channel_edit", e, f"channel={channel.id}")
                return False
        except (asyncio.TimeoutError, Exception) as e:
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
            else:
                await log_error("safe_channel_edit", e, f"channel={channel.id}")
                return False
    return False


async def safe_channel_delete(channel, retries: int = 3) -> bool:
    for attempt in range(retries + 1):
        try:
            await channel.delete()
            return True
        except discord.NotFound:
            return True   # already gone — treat as success
        except discord.HTTPException as e:
            if _is_rate_limited(e):
                await asyncio.sleep(_retry_after(e) + 0.5)
                continue
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
            else:
                await log_error("safe_channel_delete", e, f"channel={channel.id}")
                return False
        except (asyncio.TimeoutError, Exception) as e:
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
            else:
                await log_error("safe_channel_delete", e, f"channel={channel.id}")
                return False
    return False


async def safe_message_edit(message, retries: int = 3, **kwargs) -> bool:
    for attempt in range(retries + 1):
        try:
            await message.edit(**kwargs)
            return True
        except discord.NotFound:
            return False
        except discord.HTTPException as e:
            if _is_rate_limited(e):
                await asyncio.sleep(_retry_after(e) + 0.5)
                continue
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
            else:
                await log_error("safe_message_edit", e)
                return False
        except (asyncio.TimeoutError, Exception) as e:
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
            else:
                await log_error("safe_message_edit", e)
                return False
    return False


# ════════════════════════════════════════════════════════════════════════
# PANEL REFRESH HELPER
# ════════════════════════════════════════════════════════════════════════

async def refresh_panel(itx: discord.Interaction, session_id: str) -> None:
    new_view = await _build_panel_view(itx.guild, session_id)
    await ix.safe_panel_refresh(itx, new_view)


# ════════════════════════════════════════════════════════════════════════
# CENTRALIZED TIMER CLEANUP
# ════════════════════════════════════════════════════════════════════════

async def cleanup_timer(channel_id: str, reason: str = "unknown", guild=None) -> None:
    task = TIMER_TASKS.pop(channel_id, None)
    if task and not task.done():
        task.cancel()
    await db_delete_timer(channel_id)
    stale = [k for k, v in list(CURRENT_SELECTION.items()) if v == channel_id]
    for k in stale:
        CURRENT_SELECTION.pop(k, None)

    ch_label = channel_id
    if guild:
        ch = guild.get_channel(int(channel_id))
        ch_label = f"#{ch.name}" if ch else channel_id

    await audit_log(
        action="AUTO CLEANUP — Timer",
        guild=guild, result="ok",
        detail=f"channel={ch_label}  reason={reason}",
    )


# ════════════════════════════════════════════════════════════════════════
# TIMER TASK  (per-channel, precise scheduling)
# ════════════════════════════════════════════════════════════════════════

TIMER_TASKS: dict[str, asyncio.Task] = {}


async def run_timer_task(channel_id: str) -> None:
    await get_bot().wait_until_ready()

    while True:
        try:
            row = await db_get_timer(channel_id)
            if not row:
                TIMER_TASKS.pop(channel_id, None)
                return

            if row["ended"]:
                TIMER_TASKS.pop(channel_id, None)
                return

            channel = get_bot().get_channel(int(channel_id))
            if not channel:
                await cleanup_timer(channel_id, reason="channel not in cache")
                return

            now  = datetime.now(timezone.utc)
            end  = datetime.fromisoformat(row["end_time"])
            secs = (end - now).total_seconds()

            # ── Timer ended ──────────────────────────────────────────
            if secs <= 0:
                await asyncio.sleep(3)

                if row["no_delete"]:
                    try:
                        await db_update_timer_field(channel_id, ended=True)
                    except DBDiskFullError:
                        TIMER_TASKS.pop(channel_id, None)
                        return
                    await safe_channel_edit(channel, name=f"⏲️ {row['name']} » ENDED")
                    TIMER_TASKS.pop(channel_id, None)
                    await send_timer_log("🏁 TIMER ENDED (END MODE)", row["name"], end, channel=channel)
                    await audit_log(
                        action="TIMER ENDED — END MODE",
                        guild=channel.guild,
                        detail=f"name={row['name']}  channel preserved",
                    )
                else:
                    try:
                        await db_delete_timer(channel_id)
                    except DBDiskFullError:
                        TIMER_TASKS.pop(channel_id, None)
                        return
                    TIMER_TASKS.pop(channel_id, None)
                    stale = [k for k, v in list(CURRENT_SELECTION.items()) if v == channel_id]
                    for k in stale:
                        CURRENT_SELECTION.pop(k, None)
                    await safe_channel_delete(channel)
                    await send_timer_log("⏹️ TIMER ENDED", row["name"], end)
                    await audit_log(
                        action="TIMER ENDED",
                        guild=channel.guild,
                        detail=f"name={row['name']}  channel deleted",
                    )
                return

            # ── 1-hour warning ───────────────────────────────────────
            if not row["warned"] and 0 < secs <= 3600:
                await send_timer_log("⚠️ 1 HOUR REMAINING", row["name"], end, channel=channel)
                await db_update_timer_field(channel_id, warned=True)

            # ── Update channel name ──────────────────────────────────
            new_name = format_timer_channel_name(row["name"], end)
            if channel.name != new_name:
                ok = await safe_channel_edit(channel, name=new_name)
                if not ok and not get_bot().get_channel(int(channel_id)):
                    await cleanup_timer(channel_id, reason="channel disappeared", guild=channel.guild)
                    return

            await db_update_timer_field(channel_id, last_check=now.isoformat())

            # ── Compute next sleep ───────────────────────────────────
            now   = datetime.now(timezone.utc)
            fresh = await db_get_timer(channel_id)
            if not fresh:
                return
            end  = datetime.fromisoformat(fresh["end_time"])
            secs = (end - now).total_seconds()

            if secs <= 0:
                await asyncio.sleep(5)
                continue

            if secs < 3600:
                mins_past  = (now.minute - end.minute) % 5
                wait_mins  = 5 - mins_past if mins_past != 0 else 5
                sleep_secs = wait_mins * 60 - now.second + end.second
                if sleep_secs <= 2:
                    sleep_secs += 300
            else:
                next_update = now.replace(minute=end.minute, second=end.second, microsecond=0)
                if next_update <= now:
                    next_update += timedelta(hours=1)
                sleep_secs = (next_update - now).total_seconds()
                if sleep_secs < 2:
                    sleep_secs += 3600

            await asyncio.sleep(max(5, min(sleep_secs, max(5, secs))))

        except asyncio.CancelledError:
            return
        except Exception as e:
            await log_error("run_timer_task", e, f"channel_id={channel_id}")
            await asyncio.sleep(30)


def start_timer_task(channel_id: str) -> None:
    old = TIMER_TASKS.pop(channel_id, None)
    if old and not old.done():
        old.cancel()
    TIMER_TASKS[channel_id] = get_bot().loop.create_task(run_timer_task(channel_id))


# ════════════════════════════════════════════════════════════════════════
# TOURNAMENT LOOP  (per-channel task)
# ════════════════════════════════════════════════════════════════════════

TOURNAMENT_TASKS: dict[str, asyncio.Task] = {}


async def _tournament_loop(channel, message) -> None:
    while True:
        try:
            now     = datetime.now(timezone.utc)
            regions = get_regions()

            future_times = (
                [r["start"] for r in regions if now < r["start"]] +
                [r["end"]   for r in regions if now < r["end"]]
            )
            time_left  = (min(future_times) - now).total_seconds() if future_times else 3600
            sleep_time = 300 if time_left <= 900 else (600 if time_left <= 3600 else 60)

            skip_next = await db_get_skip_next()
            ok = await safe_message_edit(message, view=build_tournament_view(skipped=skip_next))
            if not ok:
                await db_delete_tournament_channel(str(channel.id))
                TOURNAMENT_TASKS.pop(str(channel.id), None)
                await audit_log(
                    action="AUTO CLEANUP — Tournament",
                    guild=channel.guild,
                    detail="message no longer exists",
                )
                return

            is_live  = any(r["start"] <= now <= r["end"] for r in regions)
            new_name = "tournament-»-started" if is_live else "tournament-»-end"
            if channel.name != new_name:
                await safe_channel_edit(channel, name=new_name)

            await asyncio.sleep(sleep_time)

        except asyncio.CancelledError:
            return
        except Exception as e:
            await log_error("_tournament_loop", e)
            await asyncio.sleep(10)


def start_tournament_task(channel, message) -> None:
    cid = str(channel.id)
    old = TOURNAMENT_TASKS.get(cid)
    if old and not old.done():
        return
    TOURNAMENT_TASKS[cid] = get_bot().loop.create_task(_tournament_loop(channel, message))


# ════════════════════════════════════════════════════════════════════════
# TOURNAMENT RUNNER  (mutex-protected)
# ════════════════════════════════════════════════════════════════════════

async def get_active_tournament_channel(guild):
    for row in await db_all_tournament_channels():
        ch = guild.get_channel(int(row["channel_id"]))
        if not ch:
            await db_delete_tournament_channel(row["channel_id"])
            continue
        return ch
    return None


async def run_tournament(guild):
    """Returns (channel, already_existed: bool). Protected by async mutex."""
    async with _TOURNAMENT_CREATION_LOCK:
        existing = await get_active_tournament_channel(guild)
        if existing:
            return existing, True

        skip_next = await db_get_skip_next()
        now       = datetime.now(timezone.utc)
        if skip_next:
            channel_name = "tournament-»-end"
        else:
            is_live      = any(r["start"] <= now <= r["end"] for r in get_regions())
            channel_name = "tournament-»-started" if is_live else "tournament-»-end"

        ch = await guild.create_text_channel(
            name=channel_name,
            overwrites={
                guild.default_role: discord.PermissionOverwrite(
                    view_channel=True, send_messages=False
                )
            },
        )
        msg = await ch.send(view=build_tournament_view(skipped=skip_next))
        try:
            await db_add_tournament_channel(str(ch.id), str(msg.id))
        except DBDiskFullError:
            await safe_channel_delete(ch)
            raise
        start_tournament_task(ch, msg)
        return ch, False


# ════════════════════════════════════════════════════════════════════════
# BACKGROUND SESSION CLEANUP
# ════════════════════════════════════════════════════════════════════════

async def session_cleanup_loop() -> None:
    await get_bot().wait_until_ready()
    while True:
        try:
            await asyncio.sleep(60)
            now = datetime.now(timezone.utc)
            for guild_id in list(PANEL_SESSION):
                s = PANEL_SESSION.get(guild_id)
                if not s:
                    continue
                elapsed = (now - s["last_activity"]).total_seconds()
                if elapsed > SESSION_TIMEOUT_SECS:
                    user_name = s["user_name"]
                    del PANEL_SESSION[guild_id]
                    stale = [
                        (g, u) for (g, u) in list(CURRENT_SELECTION)
                        if g == guild_id and u == s["user_id"]
                    ]
                    for k in stale:
                        CURRENT_SELECTION.pop(k, None)
                    await audit_log(
                        action="SESSION EXPIRED — AUTO LOGOUT",
                        result="expired",
                        detail=f"user={user_name}  guild_id={guild_id}  idle={int(elapsed // 60)}m",
                    )
        except asyncio.CancelledError:
            return
        except Exception as e:
            await log_error("session_cleanup_loop", e)


# ════════════════════════════════════════════════════════════════════════
# CONFIRMATION VIEW
# ════════════════════════════════════════════════════════════════════════

class ConfirmView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=30)
        self.confirmed = False

    @discord.ui.button(label="✅ Confirm", style=discord.ButtonStyle.green, custom_id="confirm_yes")
    async def yes(self, btn, itx: discord.Interaction):
        self.confirmed = True
        self.stop()
        await ix.safe_defer(itx, ephemeral=True, silent=True)

    @discord.ui.button(label="✖ Cancel", style=discord.ButtonStyle.secondary, custom_id="confirm_no")
    async def no(self, btn, itx: discord.Interaction):
        self.confirmed = False
        self.stop()
        await ix.safe_send_response(itx, content="Cancelled.")


# ════════════════════════════════════════════════════════════════════════
# EXTEND
# ════════════════════════════════════════════════════════════════════════

EXTEND_OPTIONS = [
    ("1 Hour",  timedelta(hours=1)),
    ("1 Day",   timedelta(days=1)),
    ("1 Week",  timedelta(weeks=1)),
    ("1 Month", timedelta(days=30)),
]


class ExtendDurationSelect(discord.ui.Select):
    def __init__(self, channel_id: str, timer_name: str, session_id: str):
        self.channel_id = channel_id
        self.timer_name = timer_name
        self.session_id = session_id
        super().__init__(
            placeholder="Select extension duration…",
            options=[
                discord.SelectOption(label=lbl, value=str(i))
                for i, (lbl, _) in enumerate(EXTEND_OPTIONS)
            ],
        )

    async def callback(self, itx: discord.Interaction):
        if not validate_session(itx.guild.id, itx.user.id, self.session_id):
            return await ix.reply_session_expired(itx)
        touch_session(itx.guild.id, itx.user.id, self.session_id)

        dkey = f"extend_{self.channel_id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            idx, (label, delta) = int(self.values[0]), EXTEND_OPTIONS[int(self.values[0])]
            row = await db_get_timer(self.channel_id)
            if not row:
                return await ix.safe_send_response(itx, content="Timer not found.")

            new_end = datetime.fromisoformat(row["end_time"]) + delta
            err     = validate_end_time(new_end)
            if err:
                return await ix.safe_send_response(itx, content=err)

            ts           = int(new_end.timestamp())
            confirm_view = ConfirmView()
            await ix.safe_send_response(
                itx,
                content=(
                    f"Extend **{self.timer_name}** by **{label}**?\n"
                    f"New end: <t:{ts}:F> (<t:{ts}:R>)"
                ),
                view=confirm_view,
            )
            await confirm_view.wait()
            if not confirm_view.confirmed:
                return

            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired during confirmation.")

            try:
                await db_update_timer_field(
                    self.channel_id, end_time=new_end.isoformat(), warned=False, no_delete=False
                )
            except DBDiskFullError:
                return await ix.safe_followup(
                    itx,
                    "Database is full — extension could not be saved.\n"
                    "The timer was not changed. Free up disk space and try again.",
                )

            ch = itx.guild.get_channel(int(self.channel_id))
            if ch:
                await safe_channel_edit(ch, name=format_timer_channel_name(self.timer_name, new_end))
            start_timer_task(self.channel_id)

            await ix.safe_followup(
                itx,
                f"**{self.timer_name}** extended by **{label}**.\n"
                f"New end: <t:{ts}:F> (<t:{ts}:R>)",
            )
            await audit_log(
                action="EXTEND TIMER", guild=itx.guild, user=itx.user,
                target_channel=ch, detail=f"by {label}  new_end=<t:{ts}:F>",
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)


class ExtendView(discord.ui.View):
    def __init__(self, channel_id: str, timer_name: str, session_id: str):
        super().__init__(timeout=60)
        self.add_item(ExtendDurationSelect(channel_id, timer_name, session_id))


# ════════════════════════════════════════════════════════════════════════
# TIMEZONE CONVERTER
# ════════════════════════════════════════════════════════════════════════

class TimezoneSelect(discord.ui.Select):
    def __init__(self):
        super().__init__(
            placeholder="Select your timezone…",
            options=[
                discord.SelectOption(label=lbl, value=tz)
                for lbl, tz in TIMEZONE_OPTIONS.items()
            ][:25],
        )

    async def callback(self, itx: discord.Interaction):
        await ix.safe_send_modal(itx, TimezoneConvertModal(self.values[0]))


class TimezoneSelectView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=60)
        self.add_item(TimezoneSelect())


class TimezoneConvertModal(discord.ui.Modal):
    def __init__(self, tz_name: str):
        super().__init__(title="Convert Time to UTC")
        self.tz_name    = tz_name
        self.date_input = discord.ui.InputText(
            label="Date (YYYY-MM-DD)", placeholder="2026-06-01", required=True
        )
        self.time_input = discord.ui.InputText(
            label="Local Time (HH:MM, 24h)", placeholder="20:30", required=True
        )
        self.add_item(self.date_input)
        self.add_item(self.time_input)

    async def callback(self, itx: discord.Interaction):
        try:
            local_dt = datetime.fromisoformat(
                f"{self.date_input.value}T{self.time_input.value}:00"
            ).replace(tzinfo=ZoneInfo(self.tz_name))
        except Exception:
            return await ix.safe_modal_response(
                itx,
                "Invalid date/time format.\nDate: `YYYY-MM-DD`   Time: `HH:MM`",
            )
        utc_dt   = local_dt.astimezone(timezone.utc)
        ts       = int(utc_dt.timestamp())
        tz_label = next((k for k, v in TIMEZONE_OPTIONS.items() if v == self.tz_name), self.tz_name)
        await ix.safe_modal_response(
            itx,
            f"**Timezone Conversion**\n\n"
            f"Local ({tz_label}): `{local_dt.strftime('%Y-%m-%d %H:%M')}`\n"
            f"UTC: `{utc_dt.strftime('%Y-%m-%d %H:%M')}`\n\n"
            f"Discord: <t:{ts}:F>  (<t:{ts}:R>)\n\n"
            f"Use in Create Timer:\n"
            f"> Date: `{utc_dt.strftime('%Y-%m-%d')}`\n"
            f"> Time: `{utc_dt.strftime('%H:%M')}`",
        )


# ════════════════════════════════════════════════════════════════════════
# MODALS
# ════════════════════════════════════════════════════════════════════════

class CreateTimerModal(discord.ui.Modal):
    def __init__(self, session_id: str):
        super().__init__(title="Create Timer")
        self.session_id = session_id
        self.name_input = discord.ui.InputText(
            label="Name", placeholder="e.g. Season 3", required=True
        )
        self.date_input = discord.ui.InputText(
            label="Date (YYYY-MM-DD, UTC)", placeholder="2026-06-01", required=True
        )
        self.time_input = discord.ui.InputText(
            label="Time (HH:MM, UTC 24h)", placeholder="18:30", required=True
        )
        self.add_item(self.name_input)
        self.add_item(self.date_input)
        self.add_item(self.time_input)

    async def callback(self, itx: discord.Interaction):
        if not validate_session(itx.guild.id, itx.user.id, self.session_id):
            return await ix.reply_session_expired(itx)
        touch_session(itx.guild.id, itx.user.id, self.session_id)

        try:
            end = datetime.fromisoformat(
                f"{self.date_input.value}T{self.time_input.value}:00"
            ).replace(tzinfo=timezone.utc)
        except ValueError:
            return await ix.safe_modal_response(
                itx, "Invalid format.\nDate: `YYYY-MM-DD`   Time: `HH:MM`"
            )

        err = validate_end_time(end)
        if err:
            return await ix.safe_modal_response(itx, err)

        channel_name = format_timer_channel_name(self.name_input.value, end)
        overwrites   = {
            itx.guild.default_role: discord.PermissionOverwrite(view_channel=True, connect=False),
            itx.guild.me:           discord.PermissionOverwrite(view_channel=True, connect=True),
        }
        try:
            ch = await itx.guild.create_voice_channel(name=channel_name, overwrites=overwrites)
        except Exception as e:
            await log_error("CreateTimerModal", e)
            return await ix.safe_modal_response(itx, f"Failed to create channel: {e}")

        try:
            await db_upsert_timer(str(ch.id), self.name_input.value, end.isoformat())
        except DBDiskFullError:
            await safe_channel_delete(ch)
            return await ix.safe_modal_response(
                itx,
                "Database is full — timer could not be saved.\n"
                "The voice channel was not created. Free up disk space and try again.",
            )

        start_timer_task(str(ch.id))

        ts = int(end.timestamp())
        await ix.safe_modal_response(
            itx,
            f"Timer **{self.name_input.value}** created.\n"
            f"{ch.mention} — ends <t:{ts}:F> (<t:{ts}:R>)",
        )
        await audit_log(
            action="CREATE TIMER", guild=itx.guild, user=itx.user,
            target_channel=ch, detail=f"end=<t:{ts}:F>",
            session_id=self.session_id,
        )
        await refresh_panel(itx, self.session_id)


class UpdateTimerModal(discord.ui.Modal):
    def __init__(self, channel_id: str, session_id: str):
        super().__init__(title="Update Timer")
        self.channel_id = channel_id
        self.session_id = session_id
        self.name_input = discord.ui.InputText(label="Name", required=True)
        self.date_input = discord.ui.InputText(
            label="Date (YYYY-MM-DD, UTC)", placeholder="2026-06-01", required=True
        )
        self.time_input = discord.ui.InputText(
            label="Time (HH:MM, UTC 24h)", placeholder="18:30", required=True
        )
        self.add_item(self.name_input)
        self.add_item(self.date_input)
        self.add_item(self.time_input)

    async def callback(self, itx: discord.Interaction):
        if not validate_session(itx.guild.id, itx.user.id, self.session_id):
            return await ix.reply_session_expired(itx)
        touch_session(itx.guild.id, itx.user.id, self.session_id)

        dkey = f"update_{self.channel_id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            try:
                end = datetime.fromisoformat(
                    f"{self.date_input.value}T{self.time_input.value}:00"
                ).replace(tzinfo=timezone.utc)
            except ValueError:
                return await ix.safe_modal_response(
                    itx, "Invalid format.\nDate: `YYYY-MM-DD`   Time: `HH:MM`"
                )

            err = validate_end_time(end)
            if err:
                return await ix.safe_modal_response(itx, err)

            row = await db_get_timer(self.channel_id)
            if not row:
                return await ix.safe_modal_response(itx, "Timer no longer exists.")

            try:
                await db_update_timer_field(
                    self.channel_id, name=self.name_input.value,
                    end_time=end.isoformat(), warned=False
                )
            except DBDiskFullError:
                return await ix.safe_modal_response(
                    itx,
                    "Database is full — update could not be saved.\n"
                    "The timer was not changed. Free up disk space and try again.",
                )

            start_timer_task(self.channel_id)

            ch = itx.guild.get_channel(int(self.channel_id))
            if ch:
                await safe_channel_edit(
                    ch, name=format_timer_channel_name(self.name_input.value, end)
                )

            ts = int(end.timestamp())
            await ix.safe_modal_response(
                itx,
                f"Timer **{self.name_input.value}** updated.\n"
                f"New end: <t:{ts}:F> (<t:{ts}:R>)",
            )
            await audit_log(
                action="UPDATE TIMER", guild=itx.guild, user=itx.user,
                target_channel=ch, detail=f"new_end=<t:{ts}:F>",
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)


# ════════════════════════════════════════════════════════════════════════
# TIMER SELECT DROPDOWN  (single source of truth for selection)
# ════════════════════════════════════════════════════════════════════════

class TimerSelect(discord.ui.Select):
    def __init__(self, guild, timers: list, session_id: str):
        self.session_id = session_id
        options         = []
        for row in timers:
            ch = guild.get_channel(int(row["channel_id"]))
            if not ch:
                continue
            if row["ended"]:
                label = f"● {row['name']}  [ENDED]"
            elif row["no_delete"]:
                label = f"🏁 {ch.name}"
            else:
                label = ch.name
            options.append(discord.SelectOption(
                label=label[:100],
                value=row["channel_id"],
                description="Archived — preserved" if row["ended"] else None,
            ))
        if not options:
            options = [discord.SelectOption(label="No timers", value="none")]
        super().__init__(
            placeholder="Select a timer…",
            options=options[:25],
            custom_id="admin_timer_select",
        )

    async def callback(self, itx: discord.Interaction):
        if not validate_session(itx.guild.id, itx.user.id, self.session_id):
            return await ix.reply_session_expired(itx)
        touch_session(itx.guild.id, itx.user.id, self.session_id)

        if self.values[0] == "none":
            return await ix.safe_send_response(itx, content="No timers available.")

        cid = self.values[0]
        CURRENT_SELECTION[(itx.guild.id, itx.user.id)] = cid

        row = await db_get_timer(cid)
        if not row:
            return await ix.safe_send_response(itx, content="Timer not found.")

        v = discord.ui.DesignerView()
        c = discord.ui.Container(
            color=discord.Color.dark_gray() if row["ended"] else discord.Color.green()
        )

        if row["ended"]:
            c.add_text(f"**{row['name']}** — Selected")
            c.add_separator(divider=True)
            c.add_text("Status: ENDED (archived)\nDelete via 🗑️.")
        else:
            end = datetime.fromisoformat(row["end_time"])
            ts  = int(end.timestamp())
            c.add_text(f"**{row['name']}** — Selected")
            c.add_separator(divider=True)
            c.add_text(f"Ends: <t:{ts}:F>\nRemaining: <t:{ts}:R>")
            if row["no_delete"]:
                c.add_separator(divider=True)
                c.add_text("🏁 End Mode: ON — channel will be renamed, not deleted")

        v.add_item(c)
        await ix.safe_send_response(itx, view=v)


# ════════════════════════════════════════════════════════════════════════
# TOURNAMENT MANAGEMENT PANEL
# ════════════════════════════════════════════════════════════════════════

class TournamentPanelView(discord.ui.View):
    def __init__(self, session_id: str):
        super().__init__(timeout=300)
        self.session_id = session_id

    def _auth(self, itx: discord.Interaction) -> bool:
        ok = validate_session(itx.guild.id, itx.user.id, self.session_id)
        if ok:
            touch_session(itx.guild.id, itx.user.id, self.session_id)
        return ok

    # ── ➕ Create ───────────────────────────────────────────────────
    @discord.ui.button(emoji="➕", style=discord.ButtonStyle.secondary, custom_id="tour_create")
    async def btn_create(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)

        dkey = f"tournament_{itx.guild.id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            await ix.safe_defer(itx, ephemeral=True)
            try:
                ch, exists = await run_tournament(itx.guild)
            except DBDiskFullError:
                await ix.safe_followup(
                    itx,
                    "Database is full — tournament channel could not be registered.\n"
                    "Any created Discord channel was automatically removed.",
                )
                await refresh_panel(itx, self.session_id)
                return

            if exists:
                await ix.safe_followup(itx, f"Tournament channel already exists: {ch.mention}")
            else:
                await ix.safe_followup(itx, f"Tournament channel created: {ch.mention}")
                await audit_log(
                    action="TOURNAMENT CREATED", guild=itx.guild,
                    user=itx.user, target_channel=ch,
                    session_id=self.session_id,
                )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)

    # ── 🗑️ Delete ──────────────────────────────────────────────────
    @discord.ui.button(emoji="🗑", style=discord.ButtonStyle.secondary, custom_id="tour_delete")
    async def btn_delete(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)

        existing = await get_active_tournament_channel(itx.guild)
        if not existing:
            return await ix.safe_send_response(itx, content="No active tournament channel.")

        dkey = f"tour_delete_{itx.guild.id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            confirm_view = ConfirmView()
            await ix.safe_send_response(
                itx,
                content=f"Delete {existing.mention}? This cannot be undone.",
                view=confirm_view,
            )
            await confirm_view.wait()
            if not confirm_view.confirmed:
                return

            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired.")

            cid = str(existing.id)
            old = TOURNAMENT_TASKS.pop(cid, None)
            if old:
                old.cancel()

            try:
                await db_delete_tournament_channel(cid)
            except DBDiskFullError:
                trows = await db_all_tournament_channels()
                trow  = next((r for r in trows if r["channel_id"] == cid), None)
                if trow:
                    try:
                        msg = await existing.fetch_message(int(trow["message_id"]))
                        start_tournament_task(existing, msg)
                    except Exception:
                        pass
                return await ix.safe_followup(
                    itx,
                    "Database is full — tournament record could not be deleted.\n"
                    "The Discord channel was not deleted.",
                )

            await safe_channel_delete(existing)
            await ix.safe_followup(itx, "Tournament channel deleted.")
            await audit_log(
                action="TOURNAMENT DELETED", guild=itx.guild,
                user=itx.user, target_channel=existing,
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)

    # ── ⏭️ Skip Week ───────────────────────────────────────────────
    @discord.ui.button(emoji="⏭", style=discord.ButtonStyle.secondary, custom_id="tour_skip")
    async def btn_skip(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)

        if await db_get_skip_next():
            return await ix.safe_send_response(itx, content="Tournament is already set to skip.")

        dkey = f"skip_{itx.guild.id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            next_regions = get_regions(week_offset=1)
            region_lines = "\n".join(
                f"• **{r['name']}** — <t:{int(r['start'].timestamp())}:F>"
                for r in next_regions
            )
            confirm_view = ConfirmView()
            await ix.safe_send_response(
                itx,
                content=(
                    f"Skip this tournament cycle?\n\n"
                    f"The channel will show next week's schedule:\n{region_lines}"
                ),
                view=confirm_view,
            )
            await confirm_view.wait()
            if not confirm_view.confirmed:
                return

            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired.")

            try:
                await db_set_skip_next(True)
            except DBDiskFullError:
                return await ix.safe_followup(
                    itx, "Database is full — skip could not be saved."
                )

            existing = await get_active_tournament_channel(itx.guild)
            if existing:
                try:
                    tour_rows = await db_all_tournament_channels()
                    trow = next(
                        (r for r in tour_rows if r["channel_id"] == str(existing.id)), None
                    )
                    if trow:
                        msg = await existing.fetch_message(int(trow["message_id"]))
                        await safe_message_edit(msg, view=build_tournament_view(skipped=True))
                    await safe_channel_edit(existing, name="tournament-»-end")
                except Exception as e:
                    await log_error("TournamentPanelView.btn_skip/update_channel", e)

            await ix.safe_followup(itx, "Tournament week skipped. The schedule shows next week's dates.")
            await audit_log(
                action="TOURNAMENT SKIP WEEK", guild=itx.guild, user=itx.user,
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)

    # ── ↩️ Restore ─────────────────────────────────────────────────
    @discord.ui.button(emoji="↩", style=discord.ButtonStyle.secondary, custom_id="tour_unskip")
    async def btn_unskip(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)

        if not await db_get_skip_next():
            return await ix.safe_send_response(itx, content="No skip is currently set.")

        dkey = f"unskip_{itx.guild.id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            try:
                await db_set_skip_next(False)
            except DBDiskFullError:
                return await ix.safe_send_response(
                    itx, content="Database is full — restore could not be saved."
                )

            existing = await get_active_tournament_channel(itx.guild)
            if existing:
                try:
                    tour_rows = await db_all_tournament_channels()
                    trow = next(
                        (r for r in tour_rows if r["channel_id"] == str(existing.id)), None
                    )
                    if trow:
                        msg = await existing.fetch_message(int(trow["message_id"]))
                        await safe_message_edit(msg, view=build_tournament_view(skipped=False))
                    now     = datetime.now(timezone.utc)
                    regions = get_regions()
                    is_live = any(r["start"] <= now <= r["end"] for r in regions)
                    await safe_channel_edit(
                        existing,
                        name="tournament-»-started" if is_live else "tournament-»-end",
                    )
                except Exception as e:
                    await log_error("TournamentPanelView.btn_unskip/update_channel", e)

            await ix.safe_send_response(itx, content="Tournament restored. The schedule shows the current week.")
            await audit_log(
                action="TOURNAMENT UNSKIP WEEK", guild=itx.guild, user=itx.user,
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)


# ════════════════════════════════════════════════════════════════════════
# ADMIN PANEL BUTTONS
# ════════════════════════════════════════════════════════════════════════

class AdminPanelView(discord.ui.View):
    def __init__(self, guild, session_id: str):
        super().__init__(timeout=86400)
        self.guild      = guild
        self.session_id = session_id

    def _auth(self, itx: discord.Interaction) -> bool:
        ok = validate_session(itx.guild.id, itx.user.id, self.session_id)
        if ok:
            touch_session(itx.guild.id, itx.user.id, self.session_id)
        return ok

    def _selected(self, itx: discord.Interaction) -> str | None:
        return CURRENT_SELECTION.get((itx.guild.id, itx.user.id))

    # ── ➕ Create ────────────────────────────────────────────────────
    @discord.ui.button(emoji="➕", style=discord.ButtonStyle.secondary, custom_id="panel_create")
    async def btn_create(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        await ix.safe_send_modal(itx, CreateTimerModal(self.session_id))

    # ── ✏️ Update ────────────────────────────────────────────────────
    @discord.ui.button(emoji="✏", style=discord.ButtonStyle.secondary, custom_id="panel_update")
    async def btn_update(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        cid = self._selected(itx)
        if not cid:
            return await ix.safe_send_response(itx, content="Select a timer from the dropdown first.")
        await ix.safe_send_modal(itx, UpdateTimerModal(cid, self.session_id))

    # ── 🗑️ Delete ────────────────────────────────────────────────────
    @discord.ui.button(emoji="🗑", style=discord.ButtonStyle.secondary, custom_id="panel_delete")
    async def btn_delete(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        cid = self._selected(itx)
        if not cid:
            return await ix.safe_send_response(itx, content="Select a timer from the dropdown first.")

        row = await db_get_timer(cid)
        if not row:
            return await ix.safe_send_response(itx, content="Timer not found.")

        dkey = f"delete_{cid}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            confirm_view = ConfirmView()
            await ix.safe_send_response(
                itx,
                content=f"Delete **{row['name']}**? This cannot be undone.",
                view=confirm_view,
            )
            await confirm_view.wait()
            if not confirm_view.confirmed:
                return

            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired during confirmation.")

            ch  = itx.guild.get_channel(int(cid))
            old = TIMER_TASKS.pop(cid, None)
            if old:
                old.cancel()

            try:
                await db_delete_timer(cid)
            except DBDiskFullError:
                start_timer_task(cid)
                return await ix.safe_followup(
                    itx,
                    "Database is full — timer record could not be deleted.\n"
                    "The Discord channel was not deleted.",
                )

            stale = [k for k, v in list(CURRENT_SELECTION.items()) if v == cid]
            for k in stale:
                CURRENT_SELECTION.pop(k, None)

            if ch:
                await safe_channel_delete(ch)
                await ix.safe_followup(itx, f"**{row['name']}** deleted.")
            else:
                await ix.safe_followup(itx, "Timer removed from database (channel was already gone).")

            await audit_log(
                action="DELETE TIMER", guild=itx.guild, user=itx.user,
                target_channel=ch or cid, detail=f"name={row['name']}",
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)

    # ── ⏳ Extend ────────────────────────────────────────────────────
    @discord.ui.button(emoji="⏳", style=discord.ButtonStyle.secondary, custom_id="panel_extend")
    async def btn_extend(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        cid = self._selected(itx)
        if not cid:
            return await ix.safe_send_response(itx, content="Select a timer from the dropdown first.")
        row = await db_get_timer(cid)
        if not row:
            return await ix.safe_send_response(itx, content="Timer not found.")
        await ix.safe_send_response(
            itx,
            content=f"Extend **{row['name']}** by:",
            view=ExtendView(cid, row["name"], self.session_id),
        )

    # ── 🏁 End Mode ──────────────────────────────────────────────────
    @discord.ui.button(emoji="🏁", style=discord.ButtonStyle.secondary, custom_id="panel_endmode")
    async def btn_endmode(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        cid = self._selected(itx)
        if not cid:
            return await ix.safe_send_response(itx, content="Select a timer from the dropdown first.")
        row = await db_get_timer(cid)
        if not row:
            return await ix.safe_send_response(itx, content="Timer not found.")

        dkey = f"endmode_{cid}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            confirm_view = ConfirmView()
            await ix.safe_send_response(
                itx,
                content=(
                    f"Enable End Mode for **{row['name']}**?\n"
                    "When the timer expires, the channel will be renamed to ENDED instead of deleted."
                ),
                view=confirm_view,
            )
            await confirm_view.wait()
            if not confirm_view.confirmed:
                return
            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired.")

            await db_update_timer_field(cid, no_delete=True)
            await ix.safe_followup(
                itx,
                f"End Mode enabled for **{row['name']}**.\n"
                "The channel will be renamed to ENDED when the timer finishes.",
            )
            await audit_log(
                action="END MODE ENABLED", guild=itx.guild, user=itx.user,
                detail=f"timer={row['name']}", session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
        finally:
            _debounce_release(itx.guild.id, dkey)

    # ── 📊 Overview ──────────────────────────────────────────────────
    @discord.ui.button(emoji="📊", style=discord.ButtonStyle.secondary, custom_id="panel_view")
    async def btn_view(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        rows = await db_all_timers()
        if not rows:
            return await ix.safe_send_response(itx, content="No timers.")

        v = discord.ui.DesignerView()
        for row in rows:
            try:
                if row["ended"]:
                    c = discord.ui.Container(color=discord.Color.dark_gray())
                    c.add_text(f"**{row['name']}** — ENDED")
                    c.add_separator(divider=True)
                    c.add_text("Archived. Delete via 🗑️.")
                else:
                    end = datetime.fromisoformat(row["end_time"])
                    ts  = int(end.timestamp())
                    c   = discord.ui.Container(color=discord.Color.blurple())
                    c.add_text(f"**{row['name']}**")
                    c.add_separator(divider=True)
                    c.add_text(f"<t:{ts}:F>\n<t:{ts}:R>")
                    if row["no_delete"]:
                        c.add_separator(divider=True)
                        c.add_text("🏁 End Mode: ON")
                v.add_item(c)
            except Exception:
                continue
        await ix.safe_send_response(itx, view=v)

    # ── 🏆 Tournament ────────────────────────────────────────────────
    @discord.ui.button(emoji="🏆", style=discord.ButtonStyle.secondary, custom_id="panel_tournament")
    async def btn_tournament(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)

        skip_active = await db_get_skip_next()
        existing    = await get_active_tournament_channel(itx.guild)

        view = discord.ui.DesignerView()
        info = discord.ui.Container(color=discord.Color.gold())
        info.add_text("🏆 **Tournament**")
        info.add_separator(divider=True)

        if existing:
            info.add_text(f"Channel: {existing.mention}")
        else:
            info.add_text("No active channel.")

        info.add_text(
            "Skip active — showing next week" if skip_active else "No skip active"
        )
        info.add_separator(divider=True)

        controls = (
            "➕ Create   🗑 Delete\n"
            "⏭ Skip Week   ↩ Restore"
        )
        info.add_text(controls)
        view.add_item(info)

        tour_view = TournamentPanelView(self.session_id)
        btn_row   = discord.ui.ActionRow(*tour_view.children)
        view.add_item(btn_row)

        await ix.safe_send_response(itx, view=view)

    # ── 🌐 Timezone ──────────────────────────────────────────────────
    @discord.ui.button(emoji="🌐", style=discord.ButtonStyle.secondary, custom_id="panel_convert_tz")
    async def btn_convert_tz(self, btn, itx: discord.Interaction):
        if not self._auth(itx):
            return await ix.reply_session_expired(itx)
        await ix.safe_send_response(
            itx,
            content="Select your timezone to convert to UTC:",
            view=TimezoneSelectView(),
        )

    # ── 🔒 Logout ────────────────────────────────────────────────────
    @discord.ui.button(emoji="🔒", style=discord.ButtonStyle.danger, custom_id="panel_logout")
    async def btn_logout(self, btn, itx: discord.Interaction):
        s = get_session(itx.guild.id)
        if not s or s["user_id"] != itx.user.id:
            return await ix.safe_send_response(itx, content="You are not logged in.")
        session_logout(itx.guild.id, itx.user.id)
        stale = [
            (g, u) for (g, u) in list(CURRENT_SELECTION)
            if g == itx.guild.id and u == itx.user.id
        ]
        for k in stale:
            CURRENT_SELECTION.pop(k, None)
        await audit_log(
            action="PANEL LOGOUT", guild=itx.guild, user=itx.user,
            session_id=s["session_id"],
        )
        await ix.safe_logout_response(itx, PanelLoginView())


# ════════════════════════════════════════════════════════════════════════
# PANEL LOGIN VIEW
# ════════════════════════════════════════════════════════════════════════

class PanelLoginView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=86400)

    @discord.ui.button(label="Login", style=discord.ButtonStyle.green, custom_id="panel_login")
    async def btn_login(self, btn, itx: discord.Interaction):
        if not (itx.user.guild_permissions.administrator or itx.user.id in DAX):
            await audit_log(
                action="UNAUTHORIZED LOGIN ATTEMPT",
                guild=itx.guild, user=itx.user, result="blocked",
            )
            return await ix.safe_send_response(itx, content="Unauthorized.")

        async with _SESSION_LOGIN_LOCK:
            existing = get_session(itx.guild.id)

            if existing and existing["user_id"] != itx.user.id:
                if session_is_expired(itx.guild.id):
                    old_name = existing["user_name"]
                    del PANEL_SESSION[itx.guild.id]
                    stale = [
                        (g, u) for (g, u) in list(CURRENT_SELECTION)
                        if g == itx.guild.id and u == existing["user_id"]
                    ]
                    for k in stale:
                        CURRENT_SELECTION.pop(k, None)
                    await audit_log(
                        action="SESSION AUTO-RECLAIMED",
                        guild=itx.guild, user=itx.user, result="expired",
                        detail=f"reclaimed from idle user: {old_name}",
                    )
                else:
                    await audit_log(
                        action="PANEL ACCESS BLOCKED",
                        guild=itx.guild, user=itx.user, result="blocked",
                        detail=f"session held by {existing['user_name']}",
                    )
                    return await ix.safe_send_response(
                        itx,
                        content=(
                            f"Panel is in use by **{existing['user_name']}**.\n"
                            "They must log out before you can access it."
                        ),
                    )

            sid = session_login(itx.guild.id, itx.user.id, itx.user.display_name)

        if not sid:
            return await ix.safe_send_response(
                itx,
                content="Could not acquire session — another admin may have just logged in.",
            )

        await audit_log(
            action="PANEL LOGIN", guild=itx.guild, user=itx.user,
            detail=f"session_id={sid[:8]}…",
            session_id=sid,
        )
        panel_view = await _build_panel_view(itx.guild, sid)
        await ix.safe_components_edit(itx, panel_view)


# ════════════════════════════════════════════════════════════════════════
# PANEL BUILDER
# Redesigned: compact header, minimal text, emoji-only buttons,
# consistent container sizing, dashboard aesthetic.
# ════════════════════════════════════════════════════════════════════════

async def _build_panel_view(guild, session_id: str) -> discord.ui.DesignerView:
    view = discord.ui.DesignerView(timeout=86400)

    # ── Header ───────────────────────────────────────────────────────
    timer_rows  = await db_all_timers()
    tour_rows   = await db_all_tournament_channels()
    skip_active = await db_get_skip_next()

    active_count   = sum(1 for r in timer_rows if not r["ended"])
    archived_count = sum(1 for r in timer_rows if r["ended"])
    tour_active    = False
    for trow in tour_rows:
        if guild.get_channel(int(trow["channel_id"])):
            tour_active = True
            break

    s = get_session(guild.id)
    session_user = s["user_name"] if s else "—"

    header = discord.ui.Container(color=discord.Color.blurple())
    header.add_text("**Timer Control Panel**")
    header.add_separator(divider=True)

    # Compact status line
    status_parts = [
        f"Timers: **{active_count}** active",
    ]
    if archived_count:
        status_parts.append(f"**{archived_count}** archived")
    status_parts.append(f"Tournament: **{'active' if tour_active else 'none'}**")
    if skip_active:
        status_parts.append("⏭ skip")
    status_parts.append(f"Session: **{session_user}**")
    header.add_text("  ·  ".join(status_parts))
    header.add_separator(divider=True)

    # Controls reference — one line per button
    header.add_text(
        "➕  Create timer\n"
        "✏  Update selected\n"
        "🗑  Delete selected\n"
        "⏳  Extend selected\n"
        "🏁  End Mode selected\n"
        "📊  Overview\n"
        "🏆  Tournament\n"
        "🌐  Timezone\n"
        "🔒  Logout"
    )
    view.add_item(header)

    # ── Active timers ─────────────────────────────────────────────────
    if timer_rows:
        tlist = discord.ui.Container(color=discord.Color.dark_blue())
        tlist.add_text("**Timers**")
        tlist.add_separator(divider=True)
        for row in timer_rows[:10]:
            try:
                if row["ended"]:
                    tlist.add_text(f"● {row['name']}  —  ENDED")
                else:
                    end   = datetime.fromisoformat(row["end_time"])
                    ts    = int(end.timestamp())
                    badge = "🏁 " if row["no_delete"] else ""
                    tlist.add_text(f"{badge}{row['name']}  —  <t:{ts}:R>")
            except Exception:
                pass
        view.add_item(tlist)

    # ── Tournament status ─────────────────────────────────────────────
    if tour_rows:
        for trow in tour_rows:
            ch = guild.get_channel(int(trow["channel_id"]))
            if ch:
                tc = discord.ui.Container(color=discord.Color.gold())
                skip_note = "  ⏭" if skip_active else ""
                tc.add_text(f"🏆 {ch.mention}{skip_note}")
                view.add_item(tc)

    # ── Timer dropdown ────────────────────────────────────────────────
    dropdown_row = discord.ui.ActionRow(
        TimerSelect(guild, timer_rows, session_id)
    )
    view.add_item(dropdown_row)

    # ── Action buttons (emoji-only, 3 per row) ────────────────────────
    apv     = AdminPanelView(guild, session_id)
    buttons = apv.children   # ➕ ✏ 🗑 ⏳ 🏁 📊 🏆 🌐 🔒

    row1 = discord.ui.ActionRow(buttons[0], buttons[1], buttons[2])   # ➕ ✏ 🗑
    row2 = discord.ui.ActionRow(buttons[3], buttons[4], buttons[5])   # ⏳ 🏁 📊
    row3 = discord.ui.ActionRow(buttons[6], buttons[7], buttons[8])   # 🏆 🌐 🔒

    view.add_item(row1)
    view.add_item(row2)
    view.add_item(row3)

    return view


# ════════════════════════════════════════════════════════════════════════
# SLASH COMMAND HANDLER
# ════════════════════════════════════════════════════════════════════════

def _is_admin(ctx) -> bool:
    return ctx.author.guild_permissions.administrator or ctx.author.id in DAX


async def cmd_timerpanel_handler(ctx) -> None:
    if not _is_admin(ctx):
        await audit_log(
            action="UNAUTHORIZED /timerpanel",
            guild=ctx.guild, user=ctx.author, result="blocked",
        )
        return await ctx.respond("Unauthorized.", ephemeral=True)

    existing = get_session(ctx.guild.id)
    if existing and existing["user_id"] != ctx.author.id:
        if not session_is_expired(ctx.guild.id):
            await audit_log(
                action="PANEL ACCESS BLOCKED — /timerpanel",
                guild=ctx.guild, user=ctx.author, result="blocked",
                detail=f"session held by {existing['user_name']}",
            )
            return await ctx.respond(
                f"Panel is in use by **{existing['user_name']}**.\n"
                "They must log out before you can access it.",
                ephemeral=True,
            )

    await ctx.respond(view=PanelLoginView(), ephemeral=True)


# ════════════════════════════════════════════════════════════════════════
# STARTUP INTEGRITY CHECK
# ════════════════════════════════════════════════════════════════════════

async def startup_integrity_check() -> None:
    bot = get_bot()
    print("[Startup] Running integrity check…")

    for row in await db_all_timers():
        ch = bot.get_channel(int(row["channel_id"]))

        if row["ended"]:
            if not ch:
                print(f"[Startup] Ended timer channel gone, removing: {row['channel_id']}")
                await db_delete_timer(row["channel_id"])
            else:
                print(f"[Startup] Archived ended timer: #{ch.name}")
            continue

        if not ch:
            print(f"[Startup] Orphaned timer removed: {row['channel_id']}")
            await cleanup_timer(row["channel_id"], reason="channel missing on startup")
            continue

        try:
            end      = datetime.fromisoformat(row["end_time"])
            new_name = format_timer_channel_name(row["name"], end)
            if ch.name != new_name:
                await safe_channel_edit(ch, name=new_name)
        except Exception as e:
            print(f"[Startup] Rename error for {row['channel_id']}: {e}")

        start_timer_task(row["channel_id"])

    for trow in await db_all_tournament_channels():
        ch = bot.get_channel(int(trow["channel_id"]))
        if not ch:
            print(f"[Startup] Orphaned tournament channel removed: {trow['channel_id']}")
            await db_delete_tournament_channel(trow["channel_id"])
            continue
        try:
            msg = await ch.fetch_message(int(trow["message_id"]))
            start_tournament_task(ch, msg)
            print(f"[Startup] Resumed tournament loop for #{ch.name}")
        except discord.NotFound:
            print(f"[Startup] Tournament message missing for #{ch.name} — removing")
            await db_delete_tournament_channel(trow["channel_id"])
        except Exception as e:
            print(f"[Startup] Tournament restore error for #{ch.name}: {e}")

    print("[Startup] Integrity check complete.")
