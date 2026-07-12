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
MAX_YEARS_AHEAD       = 2
MAX_NAME_LENGTH       = 30        # maximum timer name length (characters)
SESSION_TIMEOUT_SECS  = 15 * 60   # 15 minutes of inactivity

# ── Guild whitelist ───────────────────────────────────────────────────
# Only guilds in this set may use the bot. Any other guild triggers an
# immediate leave. Add your authorized guild IDs here.
ALLOWED_GUILDS: set[int] = {
    1452099895564439682,   # replace with actual guild IDs
    1428800178848010331,
}


def is_guild_allowed(guild_id: int) -> bool:
    """Single authoritative check for guild whitelist."""
    return guild_id in ALLOWED_GUILDS


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

# Per-guild mutex preventing concurrent timer creation from the same guild
# (guards against Discord duplicate interaction delivery and double-clicks)
_TIMER_CREATION_LOCKS: dict[int, asyncio.Lock] = {}

# Idempotency set: interaction IDs that have already entered CreateTimerModal.callback
# Prevents duplicate execution if Discord re-delivers the same modal submission.
# Entries are removed after the callback completes (success or error).
_CREATE_INTERACTION_IDS: set[int] = set()

# ════════════════════════════════════════════════════════════════════════
# COMPONENT V2 BUDGET MANAGEMENT
#
# Discord rejects any DesignerView whose total component tree exceeds 40.
# The count includes every item at every nesting level:
#   Container       = 1  (plus each of its children)
#   ActionRow       = 1  (plus each of its children)
#   TextDisplay     = 1  (from container.add_text())
#   Separator       = 1  (from container.add_separator())
#   Button          = 1
#   Select          = 1
#
# Root cause of the 50035 error:
#   - btn_view (Overview): each timer added 1 TextDisplay inside containers.
#     With enough timers + archived + scheduled, the total exceeded 40.
#   - Help panel (Timer Panel category): 9 sections × 4 components = 36
#     plus 8 fixed components = 44. Always crashed.
#
# Fix: never add one component per item. Pack all items of the same
# category into one text block inside one Container. Use pagination when
# the packed list would still exceed the per-category character limit,
# not when the component count grows.
# ════════════════════════════════════════════════════════════════════════

DISCORD_COMPONENT_LIMIT = 40


def _count_components(view: discord.ui.DesignerView) -> int:
    """
    Recursively count every Component V2 object in a DesignerView.
    Uses duck-typing so it works without importing private Discord internals.
    """
    def _count(item) -> int:
        n = 1  # the item itself
        children = getattr(item, "children", None) or getattr(item, "_children", None) or []
        # Containers store children in ._children; ActionRows in .children
        # Try both attribute names defensively
        if not children:
            children = getattr(item, "_components", [])
        for child in children:
            n += _count(child)
        return n

    total = 0
    items = getattr(view, "children", []) or getattr(view, "_children", [])
    for item in items:
        total += _count(item)
    return total

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

# Tracks the last maintenance alert state to suppress duplicate Discord logs.
# Keys: "fingerprint" → tuple describing last alert sent.
_MAINT_LAST_STATE: dict = {}


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
    """
    Scheduled maintenance loop.

    Discord logging policy
    ──────────────────────
    Healthy runs produce NO Discord output — only stdout.
    A Discord log fires only when something changes:

      Warning (yellow)  — first occurrence of low disk, VACUUM skipped, or
                          a partially-failed checkpoint
      Error   (red)     — hard errors (disk full, I/O failure, checkpoint
                          failed entirely)
      Resolved (green)  — sent once when a previously-warned condition clears

    Repeating the same warning every cycle is suppressed via
    _MAINT_LAST_STATE.  A new alert fires only when the severity
    changes or the specific error text changes.
    """
    await get_bot().wait_until_ready()
    await asyncio.sleep(60)   # let integrity check complete first

    while True:
        try:
            stats = await db_maintenance()

            free_mb    = stats["free_mb"]
            before_wal = stats["before"]["wal"] / (1024 * 1024)
            after_wal  = stats["after"]["wal"]  / (1024 * 1024)
            errors     = stats["errors"]         # list[str] from db_maintenance()

            # ── Classify this run ─────────────────────────────────────
            hard_errors = [e for e in errors
                           if not e.startswith("VACUUM skipped")]
            low_disk    = 0 <= free_mb < _DISK_WARN_THRESHOLD_MB
            wal_large   = after_wal > 32   # MB
            vac_skipped = any("VACUUM skipped" in e for e in errors)

            if hard_errors:
                severity = "error"
            elif low_disk or wal_large or (vac_skipped and not stats["checkpoint"]):
                severity = "warn"
            else:
                severity = "ok"

            # Build a compact fingerprint so we only re-alert on change
            fingerprint = (
                severity,
                round(free_mb / 50) * 50 if low_disk else -1,   # bucket to ±50 MB
                bool(hard_errors),
                bool(wal_large),
            )

            prev = _MAINT_LAST_STATE.get("fingerprint")
            _MAINT_LAST_STATE["fingerprint"] = fingerprint

            # Always print to stdout for server logs
            db_mb  = stats["after"]["db"]  / (1024 * 1024)
            wal_mb = stats["after"]["wal"] / (1024 * 1024)
            print(
                f"[Maintenance] OK — DB {db_mb:.2f} MB  WAL {wal_mb:.2f} MB  "
                f"Free {free_mb:.0f} MB  "
                f"chk={'✓' if stats['checkpoint'] else '✗'}  "
                f"trunc={'✓' if stats['truncate'] else '✗'}  "
                f"vac={'✓' if stats['vacuum'] else '✗'}"
                + (f"  errors={errors}" if errors else "")
            )

            # ── Discord log only on state change ─────────────────────
            if fingerprint == prev:
                # Condition unchanged — skip Discord entirely
                pass

            elif severity == "ok" and prev is not None and prev[0] != "ok":
                # Previously had a problem — send a one-time "resolved" log
                await audit_log(
                    action="DB MAINTENANCE — RESOLVED",
                    result="ok",
                    detail=(
                        f"DB: {db_mb:.2f} MB  WAL: {wal_mb:.2f} MB  "
                        f"Free: {free_mb:.0f} MB\n"
                        "Previous condition has cleared."
                    ),
                )

            elif severity == "warn":
                lines = []
                if low_disk:
                    lines.append(f"⚠️ Low disk: **{free_mb:.0f} MB** free (threshold {_DISK_WARN_THRESHOLD_MB} MB)")
                if wal_large:
                    lines.append(f"⚠️ WAL file is large: **{after_wal:.1f} MB**")
                if vac_skipped:
                    vac_msg = next((e for e in errors if "VACUUM skipped" in e), "")
                    lines.append(f"⚠️ VACUUM skipped — {vac_msg}")
                if hard_errors:
                    lines.extend(f"⚠️ {e}" for e in hard_errors)
                lines.append(f"DB: {db_mb:.2f} MB  WAL: {wal_mb:.2f} MB  Free: {free_mb:.0f} MB")
                await audit_log(
                    action="DB MAINTENANCE — WARNING",
                    result="warn",
                    detail="\n".join(lines),
                )

            elif severity == "error":
                lines = [f"❌ {e}" for e in hard_errors]
                lines.append(f"DB: {db_mb:.2f} MB  WAL: {wal_mb:.2f} MB  Free: {free_mb:.0f} MB")
                await audit_log(
                    action="DB MAINTENANCE — ERROR",
                    result="error",
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
                channel_id   TEXT PRIMARY KEY,
                name         TEXT NOT NULL,
                end_time     TEXT NOT NULL,
                warned_1h    INTEGER NOT NULL DEFAULT 0,
                warned_12h   INTEGER NOT NULL DEFAULT 0,
                no_delete    INTEGER NOT NULL DEFAULT 0,
                ended        INTEGER NOT NULL DEFAULT 0,
                last_check   TEXT
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

            -- Deferred operations (Update / Extend / Delete queued for on-expiry execution)
            CREATE TABLE IF NOT EXISTS deferred_ops (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                channel_id   TEXT NOT NULL,
                op_type      TEXT NOT NULL,   -- 'update' | 'extend' | 'delete'
                payload      TEXT NOT NULL,   -- JSON-encoded op data
                created_at   TEXT NOT NULL,
                FOREIGN KEY (channel_id) REFERENCES timers(channel_id) ON DELETE CASCADE
            );

            -- Scheduled timer creation / update jobs
            -- op_type: 'create_timer' | 'update_timer'
            -- channel_id: NULL for create_timer, timer's channel_id for update_timer
            CREATE TABLE IF NOT EXISTS scheduled_timers (
                id              INTEGER PRIMARY KEY AUTOINCREMENT,
                guild_id        TEXT NOT NULL,
                name            TEXT NOT NULL,
                create_at       TEXT NOT NULL,   -- UTC ISO, when to execute the job
                end_time        TEXT NOT NULL,   -- UTC ISO, the timer's actual expiry
                op_type         TEXT NOT NULL DEFAULT 'create_timer',
                channel_id      TEXT,            -- NULL for create_timer; set for update_timer
                executed        INTEGER NOT NULL DEFAULT 0,
                created_at_row  TEXT NOT NULL
            );
        """)

        # ── Safe column migrations for existing databases ────────────────
        migrations = [
            ("timers",            "ended",      "INTEGER NOT NULL DEFAULT 0"),
            ("timers",            "warned_1h",  "INTEGER NOT NULL DEFAULT 0"),
            ("timers",            "warned_12h", "INTEGER NOT NULL DEFAULT 0"),
            # scheduled_timers additions (op_type + channel_id for update jobs)
            ("scheduled_timers",  "op_type",    "TEXT NOT NULL DEFAULT 'create_timer'"),
            ("scheduled_timers",  "channel_id", "TEXT"),
        ]
        for table, col, typedef in migrations:
            try:
                await db.execute(f"ALTER TABLE {table} ADD COLUMN {col} {typedef}")
            except Exception:
                pass   # column already exists

        # Migrate old `warned` → `warned_1h` (copy data, keep old column harmlessly)
        try:
            await db.execute(
                "UPDATE timers SET warned_1h = warned WHERE warned_1h = 0 AND warned = 1"
            )
        except Exception:
            pass

        await db.commit()


# ── Timer CRUD ────────────────────────────────────────────────────────

async def db_get_timer(channel_id: str):
    return await _db_one("SELECT * FROM timers WHERE channel_id = ?", (channel_id,))


async def db_all_timers() -> list:
    return await _db_all("SELECT * FROM timers")


async def db_upsert_timer(
    channel_id: str, name: str, end_time: str,
    warned_1h: bool = False, warned_12h: bool = False,
    no_delete: bool = False, ended: bool = False,
    last_check: str | None = None,
) -> None:
    try:
        await _db_exec("""
            INSERT INTO timers
                (channel_id, name, end_time, warned_1h, warned_12h, no_delete, ended, last_check)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(channel_id) DO UPDATE SET
                name=excluded.name, end_time=excluded.end_time,
                warned_1h=excluded.warned_1h, warned_12h=excluded.warned_12h,
                no_delete=excluded.no_delete, ended=excluded.ended,
                last_check=excluded.last_check
        """, (channel_id, name, end_time,
              int(warned_1h), int(warned_12h), int(no_delete), int(ended), last_check))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_upsert_timer", e, f"name={name}")
        raise
    except DBError as e:
        await log_error("db_upsert_timer", e, f"channel_id={channel_id}")
        raise


async def db_update_timer_field(channel_id: str, **kwargs) -> None:
    allowed  = {"name", "end_time", "warned_1h", "warned_12h", "no_delete", "ended", "last_check"}
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


# ── Deferred operations CRUD ──────────────────────────────────────────
# op_type values: 'update' | 'extend' | 'delete'
# payload is JSON-encoded per-op data:
#   update:  {"name": str, "end_time": ISO str}
#   extend:  {"delta_seconds": int}
#   delete:  {}

import json as _json


async def db_add_deferred_op(channel_id: str, op_type: str, payload: dict) -> None:
    try:
        await _db_exec(
            "INSERT INTO deferred_ops (channel_id, op_type, payload, created_at) VALUES (?, ?, ?, ?)",
            (channel_id, op_type, _json.dumps(payload),
             datetime.now(timezone.utc).isoformat()),
        )
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_add_deferred_op", e, f"op={op_type}")
        raise
    except DBError as e:
        await log_error("db_add_deferred_op", e)
        raise


async def db_get_deferred_ops(channel_id: str) -> list:
    return await _db_all(
        "SELECT * FROM deferred_ops WHERE channel_id = ? ORDER BY id ASC",
        (channel_id,),
    )


async def db_delete_deferred_ops(channel_id: str) -> None:
    """Delete all pending ops for a timer (e.g. when timer is deleted)."""
    try:
        await _db_exec("DELETE FROM deferred_ops WHERE channel_id = ?", (channel_id,))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_delete_deferred_ops", e, channel_id)
        raise
    except DBError as e:
        await log_error("db_delete_deferred_ops", e)
        raise


async def db_delete_deferred_op(op_id: int) -> None:
    try:
        await _db_exec("DELETE FROM deferred_ops WHERE id = ?", (op_id,))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_delete_deferred_op", e, f"id={op_id}")
        raise
    except DBError as e:
        await log_error("db_delete_deferred_op", e)
        raise


# ── Scheduled timers CRUD ─────────────────────────────────────────────

async def db_add_scheduled_timer(
    guild_id: int, name: str, create_at: str, end_time: str,
    op_type: str = "create_timer", channel_id: str | None = None,
) -> None:
    try:
        await _db_exec(
            """INSERT INTO scheduled_timers
               (guild_id, name, create_at, end_time, op_type, channel_id, executed, created_at_row)
               VALUES (?, ?, ?, ?, ?, ?, 0, ?)""",
            (str(guild_id), name, create_at, end_time, op_type, channel_id,
             datetime.now(timezone.utc).isoformat()),
        )
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_add_scheduled_timer", e, f"name={name}")
        raise
    except DBError as e:
        await log_error("db_add_scheduled_timer", e)
        raise


async def db_all_scheduled_timers() -> list:
    return await _db_all(
        "SELECT * FROM scheduled_timers WHERE executed = 0 ORDER BY create_at ASC"
    )


async def db_mark_scheduled_executed(row_id: int) -> None:
    try:
        await _db_exec(
            "UPDATE scheduled_timers SET executed = 1 WHERE id = ?", (row_id,)
        )
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_mark_scheduled_executed", e, f"id={row_id}")
        raise
    except DBError as e:
        await log_error("db_mark_scheduled_executed", e)
        raise


async def db_cancel_scheduled_updates(channel_id: str) -> None:
    """
    Mark all pending scheduled jobs for this timer as executed (cancelled).
    Uses channel_id — the timer's channel identifier — to target update_timer
    jobs that belong to this timer. Safe to call when channel_id has no
    matching rows (no-op).
    """
    try:
        await _db_exec(
            "UPDATE scheduled_timers SET executed = 1 WHERE channel_id = ? AND executed = 0",
            (channel_id,),
        )
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_cancel_scheduled_updates", e, channel_id)
        raise
    except DBError as e:
        await log_error("db_cancel_scheduled_updates", e)
        raise


async def db_delete_scheduled_timer(row_id: int) -> None:
    """Hard-delete a scheduled_timers row by its primary key."""
    try:
        await _db_exec("DELETE FROM scheduled_timers WHERE id = ?", (row_id,))
    except DBDiskFullError as e:
        await _handle_db_disk_full("db_delete_scheduled_timer", e, f"id={row_id}")
        raise
    except DBError as e:
        await log_error("db_delete_scheduled_timer", e)
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

def validate_timer_name(name: str) -> str | None:
    """Returns an error string if the name is invalid, else None."""
    if len(name) > MAX_NAME_LENGTH:
        return (
            f"Timer name is too long ({len(name)} characters).\n"
            f"Maximum length is **{MAX_NAME_LENGTH}** characters."
        )
    if not name.strip():
        return "Timer name cannot be empty."
    return None


def validate_end_time(end: datetime) -> str | None:
    now = datetime.now(timezone.utc)
    if end <= now:
        return "That time is in the past. Please enter a future date and time."
    max_end = now + timedelta(days=int(365.25 * MAX_YEARS_AHEAD))
    if end > max_end:
        return (
            f"Date too far in the future.\n"
            f"Maximum: **{max_end.strftime('%Y-%m-%d')}** ({MAX_YEARS_AHEAD}-year limit)."
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
    # deferred_ops cascade-deletes via FK, but call explicitly to be safe
    try:
        await db_delete_deferred_ops(channel_id)
    except Exception:
        pass
    # cancel any pending scheduled updates for this timer
    try:
        await db_cancel_scheduled_updates(channel_id)
    except Exception:
        pass
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


async def _execute_deferred_ops(channel_id: str, channel, guild) -> None:
    """
    Execute all pending deferred operations for a timer at expiry.
    Operations run in insertion order. Each failure is logged but does not
    stop subsequent ops.
    """
    ops = await db_get_deferred_ops(channel_id)
    if not ops:
        return

    for op in ops:
        try:
            op_type = op["op_type"]
            payload = _json.loads(op["payload"])

            if op_type == "delete":
                # Already handled in expiry flow — just mark consumed
                pass

            elif op_type == "update":
                new_name     = payload.get("name", "")
                new_end_iso  = payload.get("end_time", "")
                if new_name and new_end_iso:
                    new_end = datetime.fromisoformat(new_end_iso)
                    await db_update_timer_field(
                        channel_id, name=new_name, end_time=new_end_iso,
                        warned_1h=False, warned_12h=False,
                    )
                    if channel:
                        await safe_channel_edit(
                            channel, name=format_timer_channel_name(new_name, new_end)
                        )
                    await audit_log(
                        action="DEFERRED UPDATE — EXECUTED", guild=guild,
                        detail=f"name={new_name}  new_end=<t:{int(new_end.timestamp())}:F>",
                    )

            elif op_type == "extend":
                delta_secs = payload.get("delta_seconds", 0)
                if delta_secs > 0:
                    row = await db_get_timer(channel_id)
                    if row:
                        base_end = datetime.fromisoformat(row["end_time"])
                        new_end  = base_end + timedelta(seconds=delta_secs)
                        err = validate_end_time(new_end)
                        if not err:
                            await db_update_timer_field(
                                channel_id, end_time=new_end.isoformat(),
                                warned_1h=False, warned_12h=False,
                            )
                            if channel:
                                await safe_channel_edit(
                                    channel,
                                    name=format_timer_channel_name(row["name"], new_end),
                                )
                            start_timer_task(channel_id)
                            await audit_log(
                                action="DEFERRED EXTEND — EXECUTED", guild=guild,
                                detail=(
                                    f"delta={timedelta(seconds=delta_secs)}"
                                    f"  new_end=<t:{int(new_end.timestamp())}:F>"
                                ),
                            )
                            # After a deferred extend the timer continues — stop op processing
                            await db_delete_deferred_op(op["id"])
                            return

            await db_delete_deferred_op(op["id"])

        except Exception as e:
            await log_error("_execute_deferred_ops", e, f"op_id={op['id']} type={op['op_type']}")


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

            # Guild whitelist guard (background task)
            if not is_guild_allowed(channel.guild.id):
                TIMER_TASKS.pop(channel_id, None)
                return

            now  = datetime.now(timezone.utc)
            end  = datetime.fromisoformat(row["end_time"])
            secs = (end - now).total_seconds()

            # ── Timer ended ──────────────────────────────────────────
            if secs <= 0:
                await asyncio.sleep(3)

                # Execute deferred ops before final state change
                await _execute_deferred_ops(channel_id, channel, channel.guild)

                # Re-read row in case a deferred extend restarted the task
                row = await db_get_timer(channel_id)
                if not row:
                    TIMER_TASKS.pop(channel_id, None)
                    return
                end  = datetime.fromisoformat(row["end_time"])
                secs = (end - datetime.now(timezone.utc)).total_seconds()
                if secs > 0:
                    # A deferred extend restarted the timer — loop continues
                    continue

                # Check if there's a pending deferred delete
                ops = await db_get_deferred_ops(channel_id)
                has_deferred_delete = any(op["op_type"] == "delete" for op in ops)
                if has_deferred_delete:
                    await db_delete_deferred_ops(channel_id)
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
                    await send_timer_log("⏹️ TIMER ENDED (DEFERRED DELETE)", row["name"], end)
                    await audit_log(
                        action="TIMER ENDED — DEFERRED DELETE",
                        guild=channel.guild,
                        detail=f"name={row['name']}  channel deleted",
                    )
                    return

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

            # ── Dual reminder checkpoints ────────────────────────────
            # 12-hour reminder (only if > 1 hour remains, prevents double-fire)
            warned_12h = bool(row["warned_12h"]) if "warned_12h" in row.keys() else True
            warned_1h  = bool(row["warned_1h"])  if "warned_1h"  in row.keys() else bool(row.get("warned", False))

            if not warned_12h and 3600 < secs <= 43200:
                await send_timer_log(
                    "⏰ 12 HOURS REMAINING", row["name"], end, channel=channel
                )
                await db_update_timer_field(channel_id, warned_12h=True)
                await audit_log(
                    action="REMINDER — 12H", guild=channel.guild,
                    detail=f"name={row['name']}",
                )

            # 1-hour reminder
            if not warned_1h and 0 < secs <= 3600:
                await send_timer_log("⚠️ 1 HOUR REMAINING", row["name"], end, channel=channel)
                await db_update_timer_field(channel_id, warned_1h=True)
                await audit_log(
                    action="REMINDER — 1H", guild=channel.guild,
                    detail=f"name={row['name']}",
                )

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
            elif secs <= 43200:
                # Within 12-hour reminder window — wake up on the 12h boundary
                # if reminder hasn't fired yet, or fall through to hourly
                fresh_12h = bool(fresh["warned_12h"]) if "warned_12h" in fresh.keys() else True
                if not fresh_12h and secs > 3600:
                    # Wake up when 12h boundary is crossed
                    wake_at    = end - timedelta(hours=12)
                    sleep_secs = max(5, (wake_at - now).total_seconds())
                    sleep_secs = min(sleep_secs, 3600)
                else:
                    next_update = now.replace(minute=end.minute, second=end.second, microsecond=0)
                    if next_update <= now:
                        next_update += timedelta(hours=1)
                    sleep_secs = (next_update - now).total_seconds()
                    if sleep_secs < 2:
                        sleep_secs += 3600
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
# SCHEDULED TIMER CREATION LOOP
# Polls the scheduled_timers table every 30 s, executes jobs whose
# create_at time has passed, prevents duplicate execution via the
# `executed` flag set before the channel is created.
# ════════════════════════════════════════════════════════════════════════

async def scheduled_timer_loop() -> None:
    await get_bot().wait_until_ready()
    await asyncio.sleep(10)   # let integrity check finish first

    while True:
        try:
            now  = datetime.now(timezone.utc)
            jobs = await db_all_scheduled_timers()

            for job in jobs:
                guild_id  = int(job["guild_id"])
                op_type   = job["op_type"] if "op_type" in job.keys() else "create_timer"
                create_at = datetime.fromisoformat(job["create_at"])

                if create_at > now:
                    continue   # not yet

                if not is_guild_allowed(guild_id):
                    await db_mark_scheduled_executed(job["id"])
                    continue

                end_time = datetime.fromisoformat(job["end_time"])
                err      = validate_end_time(end_time)

                # Mark executed first to prevent duplicate runs after restart
                try:
                    await db_mark_scheduled_executed(job["id"])
                except DBDiskFullError:
                    continue   # skip this cycle, retry next poll

                if err:
                    await audit_log(
                        action=f"SCHEDULED {op_type.upper()} — SKIPPED (end in past)",
                        result="warn",
                        detail=f"name={job['name']}  end_time={job['end_time']}",
                    )
                    continue

                guild = get_bot().get_guild(guild_id)
                if not guild:
                    await audit_log(
                        action=f"SCHEDULED {op_type.upper()} — SKIPPED (guild not found)",
                        result="warn",
                        detail=f"guild_id={guild_id}  name={job['name']}",
                    )
                    continue

                # ── Dispatch by op_type ───────────────────────────────
                if op_type == "update_timer":
                    await _execute_scheduled_update(job, guild, end_time)
                else:
                    await _execute_scheduled_create(job, guild, end_time)

        except asyncio.CancelledError:
            return
        except Exception as e:
            await log_error("scheduled_timer_loop", e)

        await asyncio.sleep(30)


async def _execute_scheduled_create(job, guild, end_time: datetime) -> None:
    """Create a voice channel timer from a scheduled_timers job."""
    channel_name = format_timer_channel_name(job["name"], end_time)
    overwrites   = {
        guild.default_role: discord.PermissionOverwrite(
            view_channel=True, connect=False
        ),
        guild.me: discord.PermissionOverwrite(view_channel=True, connect=True),
    }
    try:
        ch = await guild.create_voice_channel(
            name=channel_name, overwrites=overwrites
        )
    except Exception as e:
        await log_error("_execute_scheduled_create/create_channel", e,
                        f"name={job['name']}")
        return

    try:
        await db_upsert_timer(str(ch.id), job["name"], job["end_time"])
    except DBDiskFullError:
        await safe_channel_delete(ch)
        await audit_log(
            action="SCHEDULED CREATE — DB FULL",
            result="error",
            detail=f"name={job['name']}  channel rolled back",
        )
        return

    start_timer_task(str(ch.id))
    ts = int(end_time.timestamp())
    await audit_log(
        action="SCHEDULED TIMER — CREATED",
        guild=guild,
        target_channel=ch,
        detail=f"name={job['name']}  end=<t:{ts}:F>",
    )
    await send_timer_log(
        "📅 SCHEDULED TIMER CREATED", job["name"], end_time, channel=ch
    )


async def _execute_scheduled_update(job, guild, end_time: datetime) -> None:
    """Apply a scheduled update to an existing timer."""
    channel_id = job["channel_id"] if "channel_id" in job.keys() else None
    if not channel_id:
        await audit_log(
            action="SCHEDULED UPDATE — SKIPPED (no channel_id)",
            result="warn",
            detail=f"name={job['name']}",
        )
        return

    row = await db_get_timer(channel_id)
    if not row:
        # Timer was deleted before the scheduled update fired — silently discard
        await audit_log(
            action="SCHEDULED UPDATE — CANCELLED (timer deleted)",
            result="warn",
            detail=f"name={job['name']}  channel_id={channel_id}",
        )
        return

    try:
        await db_update_timer_field(
            channel_id, name=job["name"], end_time=job["end_time"],
            warned_1h=False, warned_12h=False,
        )
    except DBDiskFullError:
        await audit_log(
            action="SCHEDULED UPDATE — DB FULL",
            result="error",
            detail=f"name={job['name']}  channel_id={channel_id}",
        )
        return

    ch = guild.get_channel(int(channel_id))
    if ch:
        await safe_channel_edit(ch, name=format_timer_channel_name(job["name"], end_time))

    start_timer_task(channel_id)
    ts = int(end_time.timestamp())
    await audit_log(
        action="SCHEDULED UPDATE — APPLIED",
        guild=guild,
        target_channel=ch,
        detail=f"name={job['name']}  end=<t:{ts}:F>",
    )
    await send_timer_log(
        "📅 SCHEDULED UPDATE APPLIED", job["name"], end_time, channel=ch
    )


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
            label, delta = EXTEND_OPTIONS[int(self.values[0])]
            row = await db_get_timer(self.channel_id)
            if not row:
                return await ix.safe_send_response(itx, content="Timer not found.")

            new_end = datetime.fromisoformat(row["end_time"]) + delta
            err     = validate_end_time(new_end)
            if err:
                return await ix.safe_send_response(itx, content=err)

            ts = int(new_end.timestamp())

            # ── Defer choice ─────────────────────────────────────────
            defer_view = DeferChoiceView()
            await ix.safe_send_response(
                itx,
                content=(
                    f"Extend **{self.timer_name}** by **{label}**?\n"
                    f"New end: <t:{ts}:F> (<t:{ts}:R>)\n\nWhen should this apply?"
                ),
                view=defer_view,
            )
            await defer_view.wait()
            if defer_view.choice is None:
                return

            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired.")

            # ── Confirm ──────────────────────────────────────────────
            confirm_view = ConfirmView()
            mode_label   = "immediately" if defer_view.choice == "immediate" else "when timer ends"
            await ix.safe_followup(
                itx,
                content=f"Confirm extend **{self.timer_name}** by **{label}** — {mode_label}?",
                view=confirm_view,
            )
            await confirm_view.wait()
            if not confirm_view.confirmed:
                return

            if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                return await ix.safe_followup(itx, "Session expired during confirmation.")

            if defer_view.choice == "immediate":
                try:
                    await db_update_timer_field(
                        self.channel_id, end_time=new_end.isoformat(),
                        warned_1h=False, warned_12h=False,
                    )
                except DBDiskFullError:
                    return await ix.safe_followup(
                        itx,
                        "Database is full — extension could not be saved.\n"
                        "The timer was not changed.",
                    )
                ch = itx.guild.get_channel(int(self.channel_id))
                if ch:
                    await safe_channel_edit(
                        ch, name=format_timer_channel_name(self.timer_name, new_end)
                    )
                start_timer_task(self.channel_id)
                await ix.safe_followup(
                    itx,
                    f"**{self.timer_name}** extended by **{label}**.\n"
                    f"New end: <t:{ts}:F> (<t:{ts}:R>)",
                )
                await audit_log(
                    action="EXTEND TIMER", guild=itx.guild, user=itx.user,
                    target_channel=itx.guild.get_channel(int(self.channel_id)),
                    detail=f"by {label}  new_end=<t:{ts}:F>",
                    session_id=self.session_id,
                )
            else:
                try:
                    await db_add_deferred_op(
                        self.channel_id, "extend",
                        {"delta_seconds": int(delta.total_seconds())},
                    )
                except DBDiskFullError:
                    return await ix.safe_followup(
                        itx, "Database is full — deferred extend could not be queued."
                    )
                await ix.safe_followup(
                    itx,
                    f"Extension of **{label}** queued for **{self.timer_name}**.\n"
                    "Will apply when the timer expires.",
                )
                await audit_log(
                    action="EXTEND TIMER — DEFERRED", guild=itx.guild, user=itx.user,
                    detail=f"by {label}  new_end would be <t:{ts}:F>",
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
# DEFERRED CHOICE VIEW
# Shown before the confirm dialog for Update / Extend / Delete.
# ════════════════════════════════════════════════════════════════════════

class DeferChoiceView(discord.ui.View):
    """
    Two-button prompt: ⚡ Apply Immediately  |  ⏳ Apply When Timer Ends
    Sets `self.choice` to "immediate" | "deferred" | None (timeout/cancel).
    """
    def __init__(self):
        super().__init__(timeout=60)
        self.choice: str | None = None

    @discord.ui.button(label="⚡ Apply Immediately", style=discord.ButtonStyle.primary,
                        custom_id="defer_immediate")
    async def btn_immediate(self, btn, itx: discord.Interaction):
        self.choice = "immediate"
        self.stop()
        await ix.safe_defer(itx, ephemeral=True, silent=True)

    @discord.ui.button(label="⏳ Apply When Timer Ends", style=discord.ButtonStyle.secondary,
                        custom_id="defer_deferred")
    async def btn_deferred(self, btn, itx: discord.Interaction):
        self.choice = "deferred"
        self.stop()
        await ix.safe_defer(itx, ephemeral=True, silent=True)


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
    """
    Creates a timer immediately, or schedules its creation for later.

    Fields:
      - Name           (required)
      - End Date       (required, UTC)
      - End Time       (required, UTC)
      - Schedule Date  (optional, UTC) — if provided, defer creation to this time
      - Schedule Time  (optional, UTC)

    If schedule fields are blank → create immediately (existing behaviour).
    If schedule fields are filled → store in scheduled_timers, create later.
    """
    def __init__(self, session_id: str):
        super().__init__(title="Create Timer")
        self.session_id    = session_id
        self.name_input    = discord.ui.InputText(
            label=f"Name (max {MAX_NAME_LENGTH} chars)",
            placeholder="e.g. Season 3",
            max_length=MAX_NAME_LENGTH,
            required=True,
        )
        self.edate_input   = discord.ui.InputText(
            label="End Date (YYYY-MM-DD, UTC)", placeholder="2026-06-01", required=True
        )
        self.etime_input   = discord.ui.InputText(
            label="End Time (HH:MM, UTC 24h)", placeholder="18:30", required=True
        )
        self.sdate_input   = discord.ui.InputText(
            label="Schedule Date (YYYY-MM-DD, optional)", placeholder="Leave blank to create now",
            required=False,
        )
        self.stime_input   = discord.ui.InputText(
            label="Schedule Time (HH:MM, optional)", placeholder="Leave blank to create now",
            required=False,
        )
        self.add_item(self.name_input)
        self.add_item(self.edate_input)
        self.add_item(self.etime_input)
        self.add_item(self.sdate_input)
        self.add_item(self.stime_input)

    async def callback(self, itx: discord.Interaction):
        # ── Idempotency guard — block duplicate interaction delivery ──────
        # Discord occasionally re-delivers the same modal submission (same
        # interaction ID) under high latency. Reject any re-entrant call for
        # the same interaction ID before doing any work.
        iid = itx.id
        if iid in _CREATE_INTERACTION_IDS:
            print(
                f"[CREATE][DUPLICATE BLOCKED] itx_id={iid} "
                f"user={itx.user.id} guild={itx.guild.id} "
                f"ts={datetime.now(timezone.utc).isoformat()}"
            )
            return
        _CREATE_INTERACTION_IDS.add(iid)

        print(
            f"[CREATE][ENTER] itx_id={iid} "
            f"user={itx.user.id} guild={itx.guild.id} "
            f"ts={datetime.now(timezone.utc).isoformat()}"
        )

        # ── Per-guild creation mutex — serialise concurrent creates ───────
        guild_lock = _TIMER_CREATION_LOCKS.setdefault(itx.guild.id, asyncio.Lock())

        try:
            async with guild_lock:
                await self._run(itx)
        finally:
            _CREATE_INTERACTION_IDS.discard(iid)
            print(
                f"[CREATE][EXIT] itx_id={iid} "
                f"user={itx.user.id} guild={itx.guild.id} "
                f"ts={datetime.now(timezone.utc).isoformat()}"
            )

    async def _run(self, itx: discord.Interaction):
        """Inner callback body — always runs under the per-guild creation mutex."""
        if not validate_session(itx.guild.id, itx.user.id, self.session_id):
            return await ix.reply_session_expired(itx)
        touch_session(itx.guild.id, itx.user.id, self.session_id)

        # ── Name validation ───────────────────────────────────────────
        name_err = validate_timer_name(self.name_input.value)
        if name_err:
            return await ix.safe_modal_response(itx, name_err)

        # ── End time ──────────────────────────────────────────────────
        try:
            end = datetime.fromisoformat(
                f"{self.edate_input.value}T{self.etime_input.value}:00"
            ).replace(tzinfo=timezone.utc)
        except ValueError:
            return await ix.safe_modal_response(
                itx, "Invalid end date/time.\nDate: `YYYY-MM-DD`   Time: `HH:MM`"
            )

        end_err = validate_end_time(end)
        if end_err:
            return await ix.safe_modal_response(itx, end_err)

        # ── Optional schedule time ─────────────────────────────────────
        sdate = self.sdate_input.value.strip()
        stime = self.stime_input.value.strip()
        has_schedule = bool(sdate or stime)

        if has_schedule:
            if not sdate or not stime:
                return await ix.safe_modal_response(
                    itx,
                    "Both **Schedule Date** and **Schedule Time** must be provided together.\n"
                    "Leave both blank to create immediately.",
                )
            try:
                create_at = datetime.fromisoformat(
                    f"{sdate}T{stime}:00"
                ).replace(tzinfo=timezone.utc)
            except ValueError:
                return await ix.safe_modal_response(
                    itx, "Invalid schedule date/time.\nDate: `YYYY-MM-DD`   Time: `HH:MM`"
                )

            now = datetime.now(timezone.utc)
            if create_at <= now:
                return await ix.safe_modal_response(
                    itx, "The schedule time is in the past. Please enter a future time."
                )
            if create_at >= end:
                return await ix.safe_modal_response(
                    itx, "The schedule time must be **before** the timer end time."
                )

            # Scheduled path
            try:
                await db_add_scheduled_timer(
                    itx.guild.id, self.name_input.value,
                    create_at.isoformat(), end.isoformat(),
                    op_type="create_timer",
                )
            except DBDiskFullError:
                return await ix.safe_modal_response(
                    itx,
                    "Database is full — schedule could not be saved.\n"
                    "Free up disk space and try again.",
                )

            cts = int(create_at.timestamp())
            ets = int(end.timestamp())
            await ix.safe_modal_response(
                itx,
                f"Timer **{self.name_input.value}** scheduled.\n"
                f"Creates: <t:{cts}:F> (<t:{cts}:R>)\n"
                f"Expires: <t:{ets}:F>",
            )
            await audit_log(
                action="CREATE TIMER — SCHEDULED", guild=itx.guild, user=itx.user,
                detail=(
                    f"name={self.name_input.value}"
                    f"  create=<t:{cts}:F>"
                    f"  end=<t:{ets}:F>"
                ),
                session_id=self.session_id,
            )
            await refresh_panel(itx, self.session_id)
            return

        # ── Immediate path ────────────────────────────────────────────
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
    """
    Updates a timer immediately, or schedules the update for a specific time.

    Fields:
      - Name           (required)
      - End Date       (required, UTC)
      - End Time       (required, UTC)
      - Schedule Date  (optional, UTC) — if provided, defer update to this time
      - Schedule Time  (optional, UTC)

    If schedule fields are blank → apply immediately.
    If schedule fields are filled → store as a scheduled update_timer job.
    Multiple pending updates for the same timer execute in chronological order.
    """
    def __init__(self, channel_id: str, session_id: str):
        super().__init__(title="Update Timer")
        self.channel_id    = channel_id
        self.session_id    = session_id
        self.name_input    = discord.ui.InputText(
            label=f"Name (max {MAX_NAME_LENGTH} chars)",
            max_length=MAX_NAME_LENGTH,
            required=True,
        )
        self.edate_input   = discord.ui.InputText(
            label="End Date (YYYY-MM-DD, UTC)", placeholder="2026-06-01", required=True
        )
        self.etime_input   = discord.ui.InputText(
            label="End Time (HH:MM, UTC 24h)", placeholder="18:30", required=True
        )
        self.sdate_input   = discord.ui.InputText(
            label="Schedule Date (YYYY-MM-DD, optional)", placeholder="Leave blank to apply now",
            required=False,
        )
        self.stime_input   = discord.ui.InputText(
            label="Schedule Time (HH:MM, optional)", placeholder="Leave blank to apply now",
            required=False,
        )
        self.add_item(self.name_input)
        self.add_item(self.edate_input)
        self.add_item(self.etime_input)
        self.add_item(self.sdate_input)
        self.add_item(self.stime_input)

    async def callback(self, itx: discord.Interaction):
        if not validate_session(itx.guild.id, itx.user.id, self.session_id):
            return await ix.reply_session_expired(itx)
        touch_session(itx.guild.id, itx.user.id, self.session_id)

        dkey = f"update_{self.channel_id}"
        if not _debounce_acquire(itx.guild.id, dkey):
            return await ix.reply_debounce(itx)

        try:
            # ── Name validation ───────────────────────────────────────
            name_err = validate_timer_name(self.name_input.value)
            if name_err:
                return await ix.safe_modal_response(itx, name_err)

            # ── End time ──────────────────────────────────────────────
            try:
                end = datetime.fromisoformat(
                    f"{self.edate_input.value}T{self.etime_input.value}:00"
                ).replace(tzinfo=timezone.utc)
            except ValueError:
                return await ix.safe_modal_response(
                    itx, "Invalid end date/time.\nDate: `YYYY-MM-DD`   Time: `HH:MM`"
                )

            end_err = validate_end_time(end)
            if end_err:
                return await ix.safe_modal_response(itx, end_err)

            row = await db_get_timer(self.channel_id)
            if not row:
                return await ix.safe_modal_response(itx, "Timer no longer exists.")

            # ── Optional schedule time ────────────────────────────────
            sdate = self.sdate_input.value.strip()
            stime = self.stime_input.value.strip()
            has_schedule = bool(sdate or stime)

            if has_schedule:
                if not sdate or not stime:
                    return await ix.safe_modal_response(
                        itx,
                        "Both **Schedule Date** and **Schedule Time** must be provided together.\n"
                        "Leave both blank to apply immediately.",
                    )
                try:
                    schedule_at = datetime.fromisoformat(
                        f"{sdate}T{stime}:00"
                    ).replace(tzinfo=timezone.utc)
                except ValueError:
                    return await ix.safe_modal_response(
                        itx, "Invalid schedule date/time.\nDate: `YYYY-MM-DD`   Time: `HH:MM`"
                    )

                now = datetime.now(timezone.utc)
                if schedule_at <= now:
                    return await ix.safe_modal_response(
                        itx, "The schedule time is in the past. Please enter a future time."
                    )
                if schedule_at >= end:
                    return await ix.safe_modal_response(
                        itx, "The schedule time must be **before** the new timer end time."
                    )

                # Confirm before scheduling
                confirm_view = ConfirmView()
                ts = int(end.timestamp())
                sts = int(schedule_at.timestamp())
                await ix.safe_modal_response(
                    itx,
                    content=(
                        f"Schedule update for **{row['name']}**?\n"
                        f"New name: **{self.name_input.value}**\n"
                        f"New end: <t:{ts}:F>\n"
                        f"Applies at: <t:{sts}:F> (<t:{sts}:R>)"
                    ),
                    view=confirm_view,
                )
                await confirm_view.wait()
                if not confirm_view.confirmed:
                    return
                if not validate_session(itx.guild.id, itx.user.id, self.session_id):
                    return await ix.safe_followup(itx, "Session expired during confirmation.")

                try:
                    await db_add_scheduled_timer(
                        itx.guild.id, self.name_input.value,
                        schedule_at.isoformat(), end.isoformat(),
                        op_type="update_timer",
                        channel_id=self.channel_id,
                    )
                except DBDiskFullError:
                    return await ix.safe_followup(
                        itx, "Database is full — scheduled update could not be saved."
                    )

                await ix.safe_followup(
                    itx,
                    f"Update scheduled for **{row['name']}**.\n"
                    f"Will apply at <t:{sts}:F> (<t:{sts}:R>).",
                )
                await audit_log(
                    action="UPDATE TIMER — SCHEDULED", guild=itx.guild, user=itx.user,
                    detail=(
                        f"new_name={self.name_input.value}"
                        f"  new_end=<t:{ts}:F>"
                        f"  schedule=<t:{sts}:F>"
                    ),
                    session_id=self.session_id,
                )
                await refresh_panel(itx, self.session_id)
                return

            # ── Immediate path ────────────────────────────────────────
            ts = int(end.timestamp())
            confirm_view = ConfirmView()
            await ix.safe_modal_response(
                itx,
                content=(
                    f"Update **{row['name']}** → **{self.name_input.value}**\n"
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
                    self.channel_id, name=self.name_input.value,
                    end_time=end.isoformat(), warned_1h=False, warned_12h=False,
                )
            except DBDiskFullError:
                return await ix.safe_followup(
                    itx,
                    "Database is full — update could not be saved.\n"
                    "The timer was not changed.",
                )
            start_timer_task(self.channel_id)
            ch = itx.guild.get_channel(int(self.channel_id))
            if ch:
                await safe_channel_edit(
                    ch, name=format_timer_channel_name(self.name_input.value, end)
                )
            await ix.safe_followup(
                itx,
                f"Timer **{self.name_input.value}** updated.\nNew end: <t:{ts}:F> (<t:{ts}:R>)",
            )
            await audit_log(
                action="UPDATE TIMER", guild=itx.guild, user=itx.user,
                target_channel=itx.guild.get_channel(int(self.channel_id)),
                detail=f"new_end=<t:{ts}:F>",
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

# ════════════════════════════════════════════════════════════════════════
# OVERVIEW BUILDER
#
# Component budget analysis (worst case):
#   1 header container  = 1 + 3 text/sep children = 4
#   1 active  container = 1 + 1 header + 1 sep + 1 packed-text = 4
#   1 endmode container = 4
#   1 archived container= 4
#   1 scheduled container=4
#   1 tournament container=4
#   1 db container      = 4
#   1 pagination ActionRow = 1 + 2 buttons = 3
#   ─────────────────────────────────────────
#   TOTAL MAX            = 31   (well within 40)
#
# Timers are packed into a single multi-line text block per category.
# No matter how many timers exist, each category consumes exactly 4
# components. Pagination only affects which page of text is shown,
# never the component count.
# ════════════════════════════════════════════════════════════════════════

# Items per page for the active-timers text list inside the overview
_OVERVIEW_PAGE_SIZE = 10


class OverviewPageView(discord.ui.View):
    """
    Pagination controls for the Overview panel.
    Renders Prev / Next buttons only when there are multiple pages.
    The view itself only carries the buttons; the DesignerView that
    wraps it is built by _build_overview_view().
    """
    def __init__(self, guild, page: int, total_pages: int, session_id: str | None = None):
        super().__init__(timeout=300)
        self.guild       = guild
        self.page        = page
        self.total_pages = total_pages
        self.session_id  = session_id

        if page > 0:
            self.add_item(self._prev_button())
        if page < total_pages - 1:
            self.add_item(self._next_button())

    def _prev_button(self):
        btn = discord.ui.Button(
            label=f"◀  Page {self.page}",
            style=discord.ButtonStyle.secondary,
            custom_id=f"overview_prev_{self.page}",
        )
        btn.callback = self._go_prev
        return btn

    def _next_button(self):
        btn = discord.ui.Button(
            label=f"Page {self.page + 2}  ▶",
            style=discord.ButtonStyle.secondary,
            custom_id=f"overview_next_{self.page}",
        )
        btn.callback = self._go_next
        return btn

    async def _go_prev(self, itx: discord.Interaction):
        new_view = await _build_overview_view(self.guild, page=self.page - 1)
        await ix.safe_components_edit(itx, new_view)

    async def _go_next(self, itx: discord.Interaction):
        new_view = await _build_overview_view(self.guild, page=self.page + 1)
        await ix.safe_components_edit(itx, new_view)


async def _build_overview_view(guild, page: int = 0) -> discord.ui.DesignerView:
    """
    Build the Overview DesignerView.

    Component budget: always ≤ 31 components regardless of data volume.
    Each timer category is packed into ONE text block inside ONE container.
    Pagination changes which slice of the active-timer list is shown,
    not the number of components.
    """
    timer_rows  = await db_all_timers()
    tour_rows   = await db_all_tournament_channels()
    skip_active = await db_get_skip_next()
    scheduled   = await db_all_scheduled_timers()
    sizes       = _db_file_sizes()
    free_mb     = _free_disk_mb()

    active  = [r for r in timer_rows if not r["ended"] and not r["no_delete"]]
    endmode = [r for r in timer_rows if not r["ended"] and r["no_delete"]]
    ended   = [r for r in timer_rows if r["ended"]]

    # ── Pagination on active timers only ─────────────────────────────
    total_active   = len(active)
    total_pages    = max(1, -(-total_active // _OVERVIEW_PAGE_SIZE))  # ceil div
    page           = max(0, min(page, total_pages - 1))
    active_page    = active[page * _OVERVIEW_PAGE_SIZE:(page + 1) * _OVERVIEW_PAGE_SIZE]

    view = discord.ui.DesignerView(timeout=300)

    # ── Header ────────────────────────────────────────────────────────
    # Component cost: 1 container + 1 text + 1 sep + 1 text = 4
    h = discord.ui.Container(color=discord.Color.blurple())
    h.add_text("**Overview**")
    h.add_separator(divider=True)
    summary_parts = []
    if active:
        summary_parts.append(f"{len(active)} active")
    if endmode:
        summary_parts.append(f"{len(endmode)} end-mode")
    if ended:
        summary_parts.append(f"{len(ended)} archived")
    if scheduled:
        summary_parts.append(f"{len(scheduled)} scheduled")
    h.add_text("  ·  ".join(summary_parts) if summary_parts else "No timers")
    view.add_item(h)

    # ── Active timers ─────────────────────────────────────────────────
    # Component cost: 1 container + 1 text + 1 sep + 1 text = 4 ALWAYS
    c_active = discord.ui.Container(color=discord.Color.blurple())
    page_label = f"  (page {page + 1}/{total_pages})" if total_pages > 1 else ""
    c_active.add_text(f"**Active Timers{page_label}**")
    c_active.add_separator(divider=True)
    if active_page:
        lines = []
        for row in active_page:
            try:
                end    = datetime.fromisoformat(row["end_time"])
                ts     = int(end.timestamp())
                ops    = await db_get_deferred_ops(row["channel_id"])
                badge  = " ⏳" if ops else ""
                lines.append(f"**{row['name']}**{badge}  —  <t:{ts}:R>")
            except Exception:
                lines.append(f"**{row['name']}**  —  (error reading time)")
        c_active.add_text("\n".join(lines))
    else:
        c_active.add_text("No active timers.")
    view.add_item(c_active)

    # ── End Mode timers ───────────────────────────────────────────────
    # Component cost: 4 ALWAYS (only added when non-empty)
    if endmode:
        c_em = discord.ui.Container(color=discord.Color.orange())
        c_em.add_text("**End Mode**")
        c_em.add_separator(divider=True)
        lines = []
        for row in endmode:
            try:
                end = datetime.fromisoformat(row["end_time"])
                ts  = int(end.timestamp())
                lines.append(f"🏁 **{row['name']}**  —  <t:{ts}:R>")
            except Exception:
                lines.append(f"🏁 **{row['name']}**")
        c_em.add_text("\n".join(lines))
        view.add_item(c_em)

    # ── Archived timers ───────────────────────────────────────────────
    # Component cost: 4 ALWAYS (only added when non-empty)
    if ended:
        c_ar = discord.ui.Container(color=discord.Color.dark_gray())
        c_ar.add_text("**Archived**")
        c_ar.add_separator(divider=True)
        c_ar.add_text("\n".join(f"● {r['name']}" for r in ended))
        view.add_item(c_ar)

    # ── Scheduled jobs ────────────────────────────────────────────────
    # Component cost: 4 ALWAYS (only added when non-empty)
    if scheduled:
        c_sc = discord.ui.Container(color=discord.Color.teal())
        c_sc.add_text("**Scheduled Jobs**")
        c_sc.add_separator(divider=True)
        lines = []
        for job in scheduled:
            try:
                op   = job["op_type"] if "op_type" in job.keys() else "create_timer"
                cts  = int(datetime.fromisoformat(job["create_at"]).timestamp())
                icon = "✏" if op == "update_timer" else "📅"
                lines.append(f"{icon} **{job['name']}**  —  <t:{cts}:R>")
            except Exception:
                lines.append(f"📅 **{job['name']}**")
        c_sc.add_text("\n".join(lines))
        view.add_item(c_sc)

    # ── Tournament ────────────────────────────────────────────────────
    # Component cost: 4 ALWAYS
    c_t = discord.ui.Container(color=discord.Color.gold())
    c_t.add_text("**Tournament**")
    c_t.add_separator(divider=True)
    tour_lines = []
    for trow in tour_rows:
        ch = guild.get_channel(int(trow["channel_id"]))
        if ch:
            tour_lines.append(f"Channel: {ch.mention}")
    if not tour_lines:
        tour_lines.append("No active channel.")
    if skip_active:
        tour_lines.append("Skip: active — next week shown")
    c_t.add_text("\n".join(tour_lines))
    view.add_item(c_t)

    # ── Database ──────────────────────────────────────────────────────
    # Component cost: 4 ALWAYS
    db_mb  = sizes["db"]  / (1024 * 1024)
    wal_mb = sizes["wal"] / (1024 * 1024)
    c_db   = discord.ui.Container(
        color=discord.Color.yellow() if (0 <= free_mb < 200) else discord.Color.dark_gray()
    )
    c_db.add_text("**Database**")
    c_db.add_separator(divider=True)
    disk_line = (f"⚠️ Low disk: {free_mb:.0f} MB free"
                 if 0 <= free_mb < 200 else f"Free: {free_mb:.0f} MB")
    c_db.add_text(f"DB: {db_mb:.2f} MB  ·  WAL: {wal_mb:.2f} MB\n{disk_line}")
    view.add_item(c_db)

    # ── Pagination buttons ────────────────────────────────────────────
    # Component cost: 0 (no pages) or 3 (1 ActionRow + 1-2 buttons)
    if total_pages > 1:
        page_view = OverviewPageView(guild, page, total_pages)
        if page_view.children:
            view.add_item(discord.ui.ActionRow(*page_view.children))

    # ── Final safety assertion ────────────────────────────────────────
    # This should never fire in production; it's a development safeguard.
    count = _count_components(view)
    if count > DISCORD_COMPONENT_LIMIT:
        print(
            f"[OVERVIEW] BUG: component count {count} exceeds {DISCORD_COMPONENT_LIMIT}. "
            f"page={page} active={len(active)} endmode={len(endmode)} "
            f"archived={len(ended)} scheduled={len(scheduled)}"
        )

    return view


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
                await db_delete_deferred_ops(cid)
                await db_cancel_scheduled_updates(cid)
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
                await ix.safe_followup(
                    itx, "Timer removed from database (channel was already gone)."
                )
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
        await ix.safe_send_response(
            itx,
            view=await _build_overview_view(itx.guild, page=0),
        )

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
        if not is_guild_allowed(itx.guild.id):
            return await ix.safe_send_response(itx, content="This guild is not authorized.")

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

    # ── Header only (no live data containers) ────────────────────────
    s            = get_session(guild.id)
    session_user = s["user_name"] if s else "—"

    header = discord.ui.Container(color=discord.Color.blurple())
    header.add_text("**Timer Control Panel**")
    header.add_separator(divider=True)
    header.add_text(f"Session: **{session_user}**")
    header.add_separator(divider=True)

    # Controls reference — one line per button
    header.add_text(
        "➕  Create timer (or schedule)\n"
        "✏  Update selected (or schedule)\n"
        "🗑  Delete selected\n"
        "⏳  Extend selected\n"
        "🏁  End Mode selected\n"
        "📊  Overview\n"
        "🏆  Tournament\n"
        "🌐  Timezone\n"
        "🔒  Logout"
    )
    view.add_item(header)

    # ── Timer dropdown ────────────────────────────────────────────────
    timer_rows   = await db_all_timers()
    dropdown_row = discord.ui.ActionRow(
        TimerSelect(guild, timer_rows, session_id)
    )
    view.add_item(dropdown_row)

    # ── Action buttons (emoji-only)
    # Row layout: ➕ ✏ 🗑  |  ⏳ 🏁 📊  |  🏆 🌐 🔒
    apv     = AdminPanelView(guild, session_id)
    buttons = apv.children
    # buttons order defined by @discord.ui.button declarations:
    # 0=➕  1=✏  2=🗑  3=⏳  4=🏁  5=📊  6=🏆  7=🌐  8=🔒

    row1 = discord.ui.ActionRow(buttons[0], buttons[1], buttons[2])   # ➕ ✏ 🗑
    row2 = discord.ui.ActionRow(buttons[3], buttons[4], buttons[5])   # ⏳ 🏁 📊
    row3 = discord.ui.ActionRow(buttons[6], buttons[7], buttons[8])   # 🏆 🌐 🔒

    view.add_item(row1)
    view.add_item(row2)
    view.add_item(row3)

    return view


# ════════════════════════════════════════════════════════════════════════
# HELP SYSTEM
# Interactive documentation panel with category dropdown.
# Each category renders as a DesignerView with structured containers.
# ════════════════════════════════════════════════════════════════════════

# ── Category definitions ──────────────────────────────────────────────
# Each entry: (dropdown_label, emoji, short_description, content_key)
_HELP_CATEGORIES: list[tuple[str, str, str]] = [
    ("Timer Panel",       "🎛",  "All control panel buttons explained"),
    ("Timer System",      "⏱",  "Reminders, End Mode, naming, limits"),
    ("Schedule System",   "📅",  "Scheduling creation and updates"),
    ("Tournament",        "🏆",  "Tournament channel management"),
    ("Timezone Converter","🌐",  "Converting local times to UTC"),
    ("Security",          "🔒",  "Sessions, whitelist, protection"),
    ("FAQ",               "❓",  "Common questions and answers"),
]

# ── Help content ──────────────────────────────────────────────────────
# Each value is a list of (title, body) section tuples rendered as
# separate containers inside the DesignerView.
_HELP_CONTENT: dict[str, list[tuple[str, str]]] = {

    "Timer Panel": [
        ("➕  Create Timer", (
            "Opens a 5-field modal to create a new timer.\n\n"
            "**Required fields**\n"
            "— **Name** (max 30 characters)\n"
            "— **End Date** — `YYYY-MM-DD` in UTC\n"
            "— **End Time** — `HH:MM` in 24-hour UTC\n\n"
            "**Optional fields** (leave blank to create immediately)\n"
            "— **Schedule Date** — UTC date to create the voice channel\n"
            "— **Schedule Time** — UTC time to create the voice channel\n\n"
            "**Immediate creation** — both schedule fields blank:\n"
            "A voice channel is created now and the countdown begins.\n\n"
            "**Scheduled creation** — schedule fields filled:\n"
            "No channel is created yet. The bot stores the job and "
            "automatically creates the channel when the scheduled time arrives. "
            "The channel then runs exactly like a manually created timer.\n\n"
            "**Validation**\n"
            "— End time must be in the future\n"
            "— End time cannot exceed 2 years from now\n"
            "— Schedule time must be before end time\n"
            "— Schedule time must be in the future"
        )),
        ("✏  Update Timer", (
            "Updates the name or end time of the selected timer.\n\n"
            "Select a timer from the dropdown first, then press ✏.\n\n"
            "**Fields** — same layout as Create Timer.\n\n"
            "**Immediate update** — schedule fields blank:\n"
            "Changes apply now. The countdown restarts. "
            "Both reminder flags reset so the updated timer triggers fresh reminders.\n\n"
            "**Scheduled update** — schedule fields filled:\n"
            "The update is stored and applied automatically at the scheduled time. "
            "The existing timer continues running unchanged until then. "
            "Multiple scheduled updates for the same timer are safe and execute in "
            "chronological order. If the timer is deleted before the update fires, "
            "the queued update is automatically cancelled."
        )),
        ("🗑  Delete Timer", (
            "Deletes the selected timer immediately.\n\n"
            "Select a timer from the dropdown, then press 🗑.\n\n"
            "A confirmation dialog appears showing the timer name. "
            "Confirming deletes the database record, cancels the background task, "
            "and deletes the Discord voice channel.\n\n"
            "**Archived timers** (End Mode) can also be deleted this way. "
            "The renamed ENDED channel will be permanently removed.\n\n"
            "**Pending scheduled updates** for the timer are automatically "
            "cancelled when the timer is deleted."
        )),
        ("⏳  Extend Timer", (
            "Adds time to the selected timer.\n\n"
            "Select a timer, press ⏳, then choose a duration:\n"
            "— 1 Hour\n"
            "— 1 Day\n"
            "— 1 Week\n"
            "— 1 Month (30 days)\n\n"
            "**Apply Immediately** — the timer end time is extended right now. "
            "Both reminder flags reset so warnings fire again at the new 12h and 1h marks.\n\n"
            "**Apply When Timer Ends** — the extension is queued. "
            "When the timer reaches zero, the extension is applied before deletion, "
            "restarting the countdown from the new end time. "
            "This effectively chains a new timer onto the end of the current one."
        )),
        ("🏁  End Mode", (
            "Marks the selected timer to be archived instead of deleted when it expires.\n\n"
            "**Normal behaviour** — when a timer reaches zero, the voice channel is deleted.\n\n"
            "**End Mode** — when a timer reaches zero, the voice channel is renamed to "
            "`⏲️ Name » ENDED` and preserved indefinitely. "
            "The timer record is marked as ended in the database.\n\n"
            "Archived timers remain visible in the server and in the Overview panel. "
            "Delete them manually via 🗑 when no longer needed.\n\n"
            "End Mode is a one-way toggle — once enabled it cannot be disabled. "
            "Create a fresh timer if you need normal deletion behaviour."
        )),
        ("📊  Overview", (
            "Opens a full dashboard showing the current state of all timers "
            "and the tournament system.\n\n"
            "**Sections shown**\n"
            "— Active Timers — running timers with remaining time\n"
            "— End Mode Timers — timers set to archive on expiry\n"
            "— Archived Timers — timers that have ended and been preserved\n"
            "— Scheduled Jobs — pending scheduled creations and updates\n"
            "— Tournament — active channel and skip status\n"
            "— Database — file sizes and free disk space\n\n"
            "Active timers with a pending deferred extend show a ⏳ badge. "
            "The Overview is ephemeral and only visible to you."
        )),
        ("🏆  Tournament", (
            "Opens the tournament management sub-panel.\n\n"
            "**➕ Create** — creates a new tournament channel with live schedule cards. "
            "Only one tournament channel can exist per server at a time.\n\n"
            "**🗑 Delete** — removes the active tournament channel and its database record. "
            "Requires confirmation.\n\n"
            "**⏭ Skip Week** — sets the tournament to display next week's schedule instead. "
            "Use this when a tournament cycle is cancelled. "
            "Requires confirmation. The channel is renamed to `tournament-»-end`.\n\n"
            "**↩ Restore** — cancels an active skip and returns to the current week's schedule.\n\n"
            "The tournament channel updates automatically every few minutes to show "
            "live, upcoming, and ended region status."
        )),
        ("🌐  Timezone Converter", (
            "Converts a local time to UTC so you can enter it accurately in Create or Update.\n\n"
            "1. Press 🌐 and select your timezone from the dropdown.\n"
            "2. Enter the local date and time in the modal.\n"
            "3. The bot responds with the equivalent UTC time and a Discord timestamp.\n\n"
            "Use the UTC values shown in the response as input for Create Timer or Update Timer.\n\n"
            "Supported regions include Europe, Africa, Asia, Oceania, and the Americas. "
            "See the Timezone Converter category for the full list."
        )),
        ("🔒  Logout", (
            "Releases your active session so another administrator can use the panel.\n\n"
            "The panel reverts to the login screen. "
            "Your timer selection is cleared.\n\n"
            "Sessions expire automatically after **15 minutes of inactivity** — "
            "you do not need to log out manually unless handing control to another admin.\n\n"
            "If an idle session is blocking access, a new admin can reclaim it by pressing "
            "Login — the bot will automatically evict the expired session and grant access."
        )),
    ],

    "Timer System": [
        ("Voice Channel Naming", (
            "Each active timer owns a Discord voice channel. "
            "The channel name is updated automatically by the background task.\n\n"
            "Format while running:\n"
            "`⏲️ Name » Xd Yh`  or  `⏲️ Name » ZM` (under 1 hour)\n\n"
            "Format when ended (End Mode):\n"
            "`⏲️ Name » ENDED`\n\n"
            "**Name length limit** — timer names are capped at 30 characters. "
            "Discord voice channel names have their own limit; the bot formats the "
            "full channel name automatically within that limit."
        )),
        ("Reminder System", (
            "Every timer automatically sends two reminder notifications to the log channel.\n\n"
            "**12-hour reminder** — sent when fewer than 12 hours remain and the "
            "timer has not already been warned at this checkpoint.\n\n"
            "**1-hour reminder** — sent when fewer than 1 hour remains.\n\n"
            "Both reminders are persisted in the database and survive bot restarts. "
            "Each fires at most once per timer per lifecycle. "
            "Extending or updating a timer resets both flags, so a fresh set of "
            "reminders will fire on the new schedule.\n\n"
            "If a timer is created with less than 12 hours remaining, only the "
            "applicable reminder(s) fire — the 12-hour check is skipped if the "
            "window has already passed."
        )),
        ("Automatic Deletion vs End Mode", (
            "**Default** — when a timer expires, the voice channel is deleted "
            "and the database record is removed.\n\n"
            "**End Mode** — when enabled via 🏁, the channel is renamed to "
            "`⏲️ Name » ENDED` instead. The record is preserved with `ended = 1`. "
            "The channel remains in the server until you delete it manually via 🗑.\n\n"
            "End Mode is useful for tournaments or events where the channel should "
            "remain visible as a historical marker after the timer finishes."
        )),
        ("Duration Limits", (
            "**Maximum duration** — 2 years from the current date.\n"
            "Attempting to create or update a timer beyond this limit shows a "
            "validation error with the exact cutoff date.\n\n"
            "This limit applies to:\n"
            "— Create Timer\n"
            "— Update Timer\n"
            "— Extend Timer\n"
            "— Scheduled creations and updates\n\n"
            "**Name length** — 30 characters maximum. "
            "Exceeded names are rejected with a clear error; names are never silently truncated."
        )),
    ],

    "Schedule System": [
        ("How Scheduling Works", (
            "Scheduling is built into the Create and Update modals — "
            "there is no separate Schedule button.\n\n"
            "Both modals have two optional fields at the bottom:\n"
            "— **Schedule Date** (`YYYY-MM-DD`)\n"
            "— **Schedule Time** (`HH:MM` UTC)\n\n"
            "Leave both blank → executes immediately (default behaviour).\n"
            "Fill both → stores the job and executes at the given time.\n\n"
            "The scheduled job worker polls every 30 seconds. "
            "Jobs are persisted in a dedicated database table and survive bot restarts."
        )),
        ("Scheduled Timer Creation", (
            "When Create Timer is used with schedule fields filled:\n\n"
            "1. No voice channel is created yet.\n"
            "2. A `create_timer` job is stored with the creation time and end time.\n"
            "3. When the scheduled time arrives, the bot creates the voice channel, "
            "registers the timer in the database, and starts the background countdown task.\n"
            "4. From that point the timer behaves identically to one created manually.\n\n"
            "Scheduled creations appear in the Overview panel (📊) under **Scheduled Jobs** "
            "until they execute."
        )),
        ("Scheduled Timer Updates", (
            "When Update Timer is used with schedule fields filled:\n\n"
            "1. The existing timer continues running unchanged.\n"
            "2. An `update_timer` job is stored linked to the timer's channel.\n"
            "3. When the scheduled time arrives, the bot applies the new name and end time, "
            "resets reminder flags, and restarts the countdown.\n\n"
            "**Multiple scheduled updates** for the same timer are safe. "
            "They execute in chronological order.\n\n"
            "**Automatic cancellation** — if the timer is deleted before the scheduled "
            "update fires, the pending job is automatically marked as cancelled.\n\n"
            "Pending updates appear in the Overview panel under **Scheduled Jobs**."
        )),
        ("Deferred Extend (Apply When Timer Ends)", (
            "Extend Timer (⏳) offers a second option: **Apply When Timer Ends**.\n\n"
            "This is different from scheduling — it does not fire at a fixed clock time. "
            "Instead, the extension is queued and fires the moment the timer reaches zero.\n\n"
            "Sequence of events:\n"
            "1. Timer runs normally.\n"
            "2. At expiry, the queued extension is applied first.\n"
            "3. The end time is pushed forward by the chosen duration.\n"
            "4. The countdown task restarts with the new end time.\n"
            "5. The channel is not deleted.\n\n"
            "This is useful for chaining timer cycles without needing to be online at expiry."
        )),
    ],

    "Tournament": [
        ("Tournament Channel Overview", (
            "The tournament system maintains a single live-updating channel in the server. "
            "It displays three regional tournament schedules:\n\n"
            "— 🌏 Asia & Middle East\n"
            "— 🌍 Africa & Europe\n"
            "— 🌎 America\n\n"
            "Each region shows its start and end times and a live/upcoming/ended status. "
            "The channel name updates automatically to reflect whether a tournament is running."
        )),
        ("Create and Delete", (
            "**Create (➕)** — creates the tournament channel and pins the live schedule. "
            "Only one channel can exist per server at a time. "
            "Attempting to create a second one returns the existing channel.\n\n"
            "**Delete (🗑)** — removes the active channel and its database record. "
            "A confirmation dialog appears before deletion. "
            "The background update task is stopped automatically."
        )),
        ("Skip Week and Restore", (
            "**Skip Week (⏭)** — marks the current cycle as cancelled. "
            "The channel displays next week's schedule instead of the current one. "
            "The channel is renamed to `tournament-»-end`.\n\n"
            "Use this when a scheduled tournament round is not happening.\n\n"
            "**Restore (↩)** — cancels an active skip and returns to the current week. "
            "The channel reverts to the appropriate name based on live status.\n\n"
            "The skip state is persisted in the database and survives restarts."
        )),
    ],

    "Timezone Converter": [
        ("Supported Timezones", (
            "The converter supports 15 preset regions:\n\n"
            "🇬🇧 London (GMT/BST) · 🇪🇺 Central Europe (CET) · 🇷🇺 Moscow (MSK)\n"
            "🌍 East Africa (EAT) · 🌍 West Africa (WAT) · 🇸🇦 Gulf/Arabia (AST)\n"
            "🇮🇳 India (IST) · 🇸🇬 Singapore (SGT) · 🇯🇵 Japan (JST)\n"
            "🇦🇺 Australia/Sydney (AEST) · 🇧🇷 Brazil (BRT)\n"
            "🇺🇸 US Eastern (ET) · 🇺🇸 US Central (CT) · "
            "🇺🇸 US Mountain (MT) · 🇺🇸 US Pacific (PT)\n\n"
            "All daylight saving transitions are handled automatically."
        )),
        ("How to Use", (
            "1. Press 🌐 from the timer panel.\n"
            "2. Select your local timezone from the dropdown.\n"
            "3. Enter the local date (`YYYY-MM-DD`) and time (`HH:MM`, 24h).\n"
            "4. The bot returns:\n"
            "   — The equivalent UTC date and time\n"
            "   — A Discord formatted timestamp\n"
            "   — The exact values to paste into Create or Update Timer\n\n"
            "**Example**\n"
            "Input: `2026-09-01` at `20:00` in US Eastern (ET)\n"
            "Output: UTC `2026-09-02 00:00` → End Date `2026-09-02`, End Time `00:00`"
        )),
    ],

    "Security": [
        ("Administrator Requirement", (
            "Every interaction with the timer panel requires Discord **Administrator** permission "
            "in the server. This is checked on every button press and modal submission — "
            "not just at login.\n\n"
            "A small set of override user IDs (`DAX`) can also access the panel "
            "regardless of server role, for bot developers."
        )),
        ("Server Whitelist", (
            "The bot maintains a hardcoded whitelist of authorized server IDs (`ALLOWED_GUILDS`). "
            "If the bot is added to any server not on the list:\n\n"
            "— It immediately leaves the server.\n"
            "— The event is logged to the audit channel.\n"
            "— No commands, timers, or database entries are created.\n\n"
            "Every slash command and background task also validates guild authorization "
            "before performing any work."
        )),
        ("Session Locking", (
            "Only one administrator can use the panel per server at a time.\n\n"
            "**Login** — pressing Login acquires an exclusive session. "
            "Other admins see a 'Panel in use by...' message until the session ends.\n\n"
            "**Automatic timeout** — sessions expire after 15 minutes of inactivity. "
            "An idle session can be reclaimed by any other admin pressing Login.\n\n"
            "**Logout** — releases the session immediately. "
            "Always log out when handing the panel to another admin."
        )),
        ("Duplicate Interaction Prevention", (
            "Discord can re-deliver the same modal submission under high latency. "
            "The bot uses two guards to prevent duplicate timer creation:\n\n"
            "**Idempotency set** — interaction IDs are tracked. "
            "Any re-delivery of the same interaction ID is rejected before any work is done.\n\n"
            "**Per-guild creation mutex** — only one Create Timer callback can run at a time "
            "per server. Concurrent submissions are serialised, not duplicated."
        )),
        ("Database Safety", (
            "**Disk-full protection** — if a write fails because the disk is full, "
            "the bot attempts an emergency WAL checkpoint to reclaim space, then retries once. "
            "If the write still fails, the Discord-side action (channel creation, deletion, etc.) "
            "is aborted entirely so the database and Discord remain in sync.\n\n"
            "**Deferred ops and cascade cleanup** — when a timer is deleted, "
            "all pending deferred operations and scheduled updates are automatically cancelled.\n\n"
            "**Startup recovery** — on restart, the bot reconciles the database against "
            "Discord's actual channel list. Orphaned records are removed. "
            "All background tasks resume."
        )),
    ],

    "FAQ": [
        ("Why didn't my timer create?", (
            "Check the following:\n\n"
            "1. **Name too long** — timer names must be 30 characters or fewer.\n"
            "2. **Date in the past** — end time must be in the future.\n"
            "3. **Beyond 2-year limit** — the end date cannot exceed 2 years from now.\n"
            "4. **Schedule time in the past** — if using scheduling, the schedule time "
            "must also be in the future.\n"
            "5. **Partial schedule fields** — both Schedule Date and Schedule Time must "
            "be filled or both must be blank. Providing only one is rejected.\n"
            "6. **Bot missing permissions** — the bot needs Manage Channels permission "
            "to create voice channels."
        )),
        ("Why can't another admin use the panel?", (
            "The panel is session-locked — only one administrator can be logged in per server. "
            "The current session holder must log out (🔒) before another admin can log in.\n\n"
            "If the current session holder is idle, their session expires automatically "
            "after 15 minutes. After that, any admin pressing Login will reclaim the session "
            "and gain access immediately."
        )),
        ("What is the difference between End Mode and normal deletion?", (
            "**Normal deletion** — the voice channel is permanently deleted when the timer "
            "reaches zero. Nothing remains in the server.\n\n"
            "**End Mode** — the channel is renamed to `⏲️ Name » ENDED` and preserved. "
            "It stays in the server indefinitely as a visible marker that the timer finished. "
            "Delete it manually via 🗑 when you no longer need it."
        )),
        ("Why is the 2-year limit in place?", (
            "Creating a timer far in the future would hold a voice channel open indefinitely. "
            "The 2-year cap prevents accidental or malicious creation of extremely "
            "long-lived channels while still supporting all realistic tournament and "
            "event scheduling needs."
        )),
        ("Why did my scheduled timer wait instead of creating immediately?", (
            "If you filled in the Schedule Date and Schedule Time fields, the bot treats "
            "that as a future creation request. The timer will be created at the exact "
            "time you specified, not when you submitted the modal.\n\n"
            "Leave both schedule fields completely blank to create the timer immediately."
        )),
        ("Why didn't a deleted timer disappear from the server?", (
            "If a timer is in **End Mode**, deleting it via 🗑 removes the database record "
            "and the voice channel. However, if the channel was already renamed to ENDED "
            "before you pressed delete, Discord may briefly show a cached state.\n\n"
            "If a channel persists after deletion, it was likely deleted successfully — "
            "refresh your Discord client. If it genuinely remains, the bot may have lacked "
            "the Manage Channels permission at the moment of deletion."
        )),
        ("Why did my 12-hour reminder not fire?", (
            "The 12-hour reminder only fires if the timer had more than 1 hour remaining "
            "when the 12-hour window was crossed. Possible reasons it was skipped:\n\n"
            "1. The timer was created with less than 12 hours remaining.\n"
            "2. The bot was offline when the 12-hour mark passed (the reminder is "
            "suppressed rather than sent late to avoid stale notifications).\n"
            "3. The timer was extended or updated — this resets reminder flags, "
            "so the 12h reminder will re-fire at the appropriate time."
        )),
    ],
}


def _build_help_category_view(category: str) -> discord.ui.DesignerView:
    """Build a DesignerView for a given help category key — page 0."""
    return _build_help_index_view(selected=category, page=0)


class HelpCategorySelect(discord.ui.Select):
    """Dropdown that rebuilds the help panel when a category is selected."""

    def __init__(self):
        options = [
            discord.SelectOption(
                label=label,
                emoji=emoji,
                description=desc[:100],
                value=label,
            )
            for label, emoji, desc in _HELP_CATEGORIES
        ]
        super().__init__(
            placeholder="Select a category…",
            options=options,
            custom_id="help_category_select",
        )

    async def callback(self, itx: discord.Interaction):
        category = self.values[0]
        new_view = _build_help_index_view(selected=category, page=0)
        await ix.safe_components_edit(itx, new_view)


# ── Help panel component budget ───────────────────────────────────────
# Fixed structure per page:
#   master header container  = 1 + 1 text + 1 sep + 1 text   = 4
#   dropdown ActionRow       = 1 + 1 select                   = 2
#   category header container= 1 + 1 text                     = 2
#   N section containers     = N × (1 + 1 text + 1 sep + 1 text) = N × 4
#   pagination ActionRow     = 1 + 1-2 buttons                = 2-3
#   ─────────────────────────────────────────────────────────────────
#   Total = 8 + N×4 + 3(max pagination) = 11 + N×4
#
# Solving for N: 11 + N×4 ≤ 40  →  N ≤ 7.25  →  N_max = 7
#
# Timer Panel has 9 sections: split into page 1 (5 sections, cost = 31)
# and page 2 (4 sections, cost = 27). All other categories fit in 1 page.
_HELP_MAX_SECTIONS_PER_PAGE = 7


def _build_help_index_view(
    selected: str | None = None,
    page: int = 0,
) -> discord.ui.DesignerView:
    """
    Build the full help panel: master header + dropdown + (if selected)
    paginated category content.

    Component budget: never exceeds 40 regardless of category size.
    Max components: 4 + 2 + 2 + 7×4 + 3 = 39 (at max 7 sections + pagination).
    """
    view = discord.ui.DesignerView(timeout=None)

    # ── Master header (cost: 4) ───────────────────────────────────────
    header = discord.ui.Container(color=discord.Color.blurple())
    header.add_text("**Timer Bot — Help**")
    header.add_separator(divider=True)
    header.add_text(
        "Select a category from the dropdown below to read the documentation.\n"
        "Use `/timerpanel` to open the admin control panel."
    )
    view.add_item(header)

    # ── Category dropdown (cost: 2) ───────────────────────────────────
    view.add_item(discord.ui.ActionRow(HelpCategorySelect()))

    # ── Category content (if selected) ───────────────────────────────
    if not (selected and selected in _HELP_CONTENT):
        return view

    sections     = _HELP_CONTENT[selected]
    total_pages  = max(1, -(-len(sections) // _HELP_MAX_SECTIONS_PER_PAGE))
    page         = max(0, min(page, total_pages - 1))
    page_sections = sections[
        page * _HELP_MAX_SECTIONS_PER_PAGE :
        (page + 1) * _HELP_MAX_SECTIONS_PER_PAGE
    ]

    emoji_map = {label: emoji for label, emoji, _ in _HELP_CATEGORIES}
    emoji     = emoji_map.get(selected, "📖")

    # Category header (cost: 2)
    cat_header = discord.ui.Container(color=discord.Color.dark_blue())
    page_label = f"  (page {page + 1}/{total_pages})" if total_pages > 1 else ""
    cat_header.add_text(f"{emoji} **{selected}**{page_label}")
    view.add_item(cat_header)

    # Section containers (cost: 4 each, max 7 = 28)
    for title, body in page_sections:
        c = discord.ui.Container(color=discord.Color.dark_gray())
        c.add_text(f"**{title}**")
        c.add_separator(divider=True)
        c.add_text(body)
        view.add_item(c)

    # Pagination buttons (cost: 3 max)
    if total_pages > 1:
        btns = []
        if page > 0:
            prev_btn = discord.ui.Button(
                label=f"◀  Page {page}",
                style=discord.ButtonStyle.secondary,
                custom_id=f"help_prev_{selected}_{page}",
            )
            # Closure trick: capture current values
            def _make_prev(cat, pg):
                async def _cb(itx: discord.Interaction):
                    await ix.safe_components_edit(
                        itx, _build_help_index_view(selected=cat, page=pg - 1)
                    )
                return _cb
            prev_btn.callback = _make_prev(selected, page)
            btns.append(prev_btn)

        if page < total_pages - 1:
            next_btn = discord.ui.Button(
                label=f"Page {page + 2}  ▶",
                style=discord.ButtonStyle.secondary,
                custom_id=f"help_next_{selected}_{page}",
            )
            def _make_next(cat, pg):
                async def _cb(itx: discord.Interaction):
                    await ix.safe_components_edit(
                        itx, _build_help_index_view(selected=cat, page=pg + 1)
                    )
                return _cb
            next_btn.callback = _make_next(selected, page)
            btns.append(next_btn)

        if btns:
            view.add_item(discord.ui.ActionRow(*btns))

    return view


async def cmd_help_handler(ctx) -> None:
    """Handler for /help — responds with the interactive documentation panel."""
    if not is_guild_allowed(ctx.guild.id):
        return await ctx.respond("This guild is not authorized.", ephemeral=True)
    await ctx.respond(view=_build_help_index_view(), ephemeral=True)


# ════════════════════════════════════════════════════════════════════════
# SLASH COMMAND HANDLER
# ════════════════════════════════════════════════════════════════════════

def _is_admin(ctx) -> bool:
    return ctx.author.guild_permissions.administrator or ctx.author.id in DAX


async def cmd_timerpanel_handler(ctx) -> None:
    if not is_guild_allowed(ctx.guild.id):
        return await ctx.respond("This guild is not authorized.", ephemeral=True)

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

        # Skip timers in non-whitelisted guilds
        if not is_guild_allowed(ch.guild.id):
            print(f"[Startup] Timer in non-whitelisted guild, skipping: {row['channel_id']}")
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
        if not is_guild_allowed(ch.guild.id):
            print(f"[Startup] Tournament in non-whitelisted guild, skipping: {trow['channel_id']}")
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

    # Scheduled jobs — evict expired and orphaned update jobs
    now = datetime.now(timezone.utc)
    for job in await db_all_scheduled_timers():
        try:
            op_type  = job["op_type"] if "op_type" in job.keys() else "create_timer"
            end_time = datetime.fromisoformat(job["end_time"])

            if end_time <= now:
                print(f"[Startup] Scheduled job expired before execution, removing: id={job['id']}")
                await db_mark_scheduled_executed(job["id"])
                continue

            if op_type == "update_timer":
                cid = job["channel_id"] if "channel_id" in job.keys() else None
                if cid:
                    row = await db_get_timer(cid)
                    if not row:
                        print(
                            f"[Startup] Scheduled update has no timer, cancelling: id={job['id']}"
                        )
                        await db_mark_scheduled_executed(job["id"])
        except Exception as e:
            print(f"[Startup] Scheduled job check error for id={job['id']}: {e}")

    print("[Startup] Integrity check complete.")