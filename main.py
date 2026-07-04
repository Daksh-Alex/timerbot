"""
main.py
════════════════════════════════════════════════════════════════════════
Bot entry point. Responsible only for:
  - Environment loading
  - Discord client creation
  - Database initialization
  - Event registration (on_ready, on_guild_join)
  - Slash command registration
  - Background task startup
  - Launching the bot

All timer system logic lives in timer.py.
"""

import asyncio
import os

import discord
from dotenv import load_dotenv

load_dotenv()

import i as ix
import timer as tm

# ── Config ────────────────────────────────────────────────────────────
TOKEN = os.getenv("TOKEN")

bot = discord.Bot(intents=discord.Intents.all())
tm.set_bot(bot)

# ── Slash commands ────────────────────────────────────────────────────

@bot.slash_command(name="timerpanel", description="Open the timer control panel")
async def cmd_timerpanel(ctx):
    await tm.cmd_timerpanel_handler(ctx)


# ── Lifecycle ─────────────────────────────────────────────────────────

@bot.event
async def on_ready():
    print(f"✅ Logged in as {bot.user}")
    ix.set_error_logger(tm.log_error)
    await tm.init_db()
    await asyncio.sleep(2)
    await tm.startup_integrity_check()
    bot.loop.create_task(tm.session_cleanup_loop())
    bot.loop.create_task(tm.db_maintenance_loop())
    bot.loop.create_task(tm.scheduled_timer_loop())
    print("✅ Ready.")


@bot.event
async def on_guild_join(guild: discord.Guild):
    """Immediately leave any guild not in the whitelist."""
    if not tm.is_guild_allowed(guild.id):
        await tm.audit_log(
            action="GUILD JOIN — UNAUTHORIZED — LEAVING",
            result="blocked",
            detail=f"guild={guild.name}  id={guild.id}",
        )
        print(f"[Security] Left unauthorized guild: {guild.name} ({guild.id})")
        try:
            await guild.leave()
        except Exception as e:
            print(f"[Security] Failed to leave guild {guild.id}: {e}")


# ── Run ───────────────────────────────────────────────────────────────

bot.run(TOKEN)