import discord
import asyncio
import json
import os
from datetime import datetime, timedelta, timezone
from dotenv import load_dotenv

load_dotenv()
adminch = 1497901879818981506 
TIMER_LOG = int(os.getenv("TIMER_LOG"))
TOKEN = os.getenv("TOKEN")
DAX = int(os.getenv("DAX"))

bot = discord.Bot(intents=discord.Intents.all())

DATA_FILE = "data.json"

# ================= DATA =================

def load_data():
    if not os.path.exists(DATA_FILE):
        return {"channels": {}, "timers": {}}

    with open(DATA_FILE, "r") as f:
        data = json.load(f)

    data.setdefault("channels", {})
    data.setdefault("timers", {})

    return data


def save_data(data):
    with open(DATA_FILE, "w") as f:
        json.dump(data, f, indent=4)


data = load_data()


async def send_timer_log(title, timer_name, end_time, channel=None, extra=None):
    log_ch = bot.get_channel(TIMER_LOG)

    if not log_ch:
        print("❌ Log channel not found")
        return

    view = discord.ui.DesignerView(timeout=None)

    container = discord.ui.Container(color=discord.Color.blurple())

    container.add_text(f"📡 **{title}**\n\n**{timer_name}**")
    container.add_separator(divider=True)

    container.add_text(
        f"🕒 **Ends:** <t:{int(end_time.timestamp())}:F>\n"
        f"⏳ **Remaining:** <t:{int(end_time.timestamp())}:R>"
    )

    if channel:
        container.add_separator(divider=True)
        container.add_text(f"📍 Channel: {channel.mention}")

    if extra:
        container.add_separator(divider=True)
        container.add_text(extra)

    view.add_item(container)

    await log_ch.send(view=view)
    
# ================= REGIONS =================

def get_regions():
    now = datetime.now(timezone.utc)

    friday = (now - timedelta(days=now.weekday() - 4)).replace(
        hour=0, minute=0, second=0, microsecond=0
    )

    def build(friday):
        return [
            {"name": "🌏 Asia & Middle East", "start": friday.replace(hour=8), "end": (friday + timedelta(days=2)).replace(hour=13)},
            {"name": "🌍 Africa & Europe", "start": friday.replace(hour=18), "end": (friday + timedelta(days=2)).replace(hour=23)},
            {"name": "🌏 America", "start": (friday + timedelta(days=1)).replace(hour=0), "end": (friday + timedelta(days=3)).replace(hour=5)},
        ]

    this_week = build(friday)
    last_end = max(r["end"] for r in this_week)
    still_running = any(r["start"] <= now <= r["end"] for r in this_week)
    if still_running or now <= last_end + timedelta(hours=12):
        return this_week
    return build(friday + timedelta(days=7))

# ================= COLORS =================

LIVE = discord.Color(0x01b201)
UPCOMING = discord.Color(0xffd800)
ENDED = discord.Color(0xd51717)

# ================= TOURNAMENT VIEW =================

def build_view():
    view = discord.ui.DesignerView()
    now = datetime.now(timezone.utc)

    for r in get_regions():
        if now < r["start"]:
            color = UPCOMING
            status = "🟡 UPCOMING"
        elif r["start"] <= now <= r["end"]:
            color = LIVE
            status = "🟢 LIVE"
        else:
            color = ENDED
            status = "🔴 ENDED"

        c = discord.ui.Container(color=color)
        c.add_text(f"**{r['name']} — {status}**")
        c.add_separator()
        c.add_text(
            f"Start: <t:{int(r['start'].timestamp())}:F>\n"
            f"End: <t:{int(r['end'].timestamp())}:F>"
        )

        view.add_item(c)

    return view

# ================= TIMER LOOP =================

async def timer_loop():
    await bot.wait_until_ready()
    print("LOOP RUNNING at", datetime.now(timezone.utc))

    while True:
        try:
            now = datetime.now(timezone.utc)
            log_ch = bot.get_channel(TIMER_LOG)

            if not log_ch:
                print("❌ TIMER_LOG channel not found")

            for cid, t in list(data.get("timers", {}).items()):
                try:
                    channel = bot.get_channel(int(cid))
                    if not channel:
                        continue

                    # ================= TIME =================
                    end = datetime.fromisoformat(t["end"])
                    diff = end - now
                    curr_diff = diff.total_seconds()

                    print(f"[CHECK] Timer {t['name']} diff:", curr_diff)

                    # ================= PREV CHECK =================
                    prev_check_str = t.get("last_check")
                    prev_diff = None

                    if prev_check_str:
                        try:
                            prev_time = datetime.fromisoformat(prev_check_str)
                            prev_diff = (end - prev_time).total_seconds()
                        except:
                            prev_diff = None

                    # ================= 1HR WARNING =================
                    if (
                        not t.get("warned", False)
                        and 0 < curr_diff <= 3600
                        and (
                            prev_diff is None or prev_diff > 3600
                        )
                    ):
                        print("SENDING ALERT FOR:", t["name"])

                        await send_timer_log(
                            title="⚠️ 1 HOUR REMAINING",
                            timer_name=t["name"],
                            end_time=end,
                            channel=channel
                        )

                        data["timers"][cid]["warned"] = True

                    # ================= ENDED =================
                    if curr_diff <= 0:
                        try:
                            await channel.edit(name=f"⏲️ {t['name']} » ENDED")
                        except:
                            pass

                        await asyncio.sleep(5)

                        try:
                            await channel.delete()
                        except:
                            pass

                        data["timers"].pop(cid, None)
                        continue

                    # ================= NAME UPDATE =================
                    elif curr_diff < 3600:
                        mins = max(0, int(curr_diff // 60))
                        new_name = f"⏲️ {t['name']} » {mins}M"
                    else:
                        d = diff.days
                        h = diff.seconds // 3600
                        new_name = f"⏲️ {t['name']} » {d}D {h}H"

                    if channel.name != new_name:
                        await channel.edit(name=new_name)

                    # ================= SAVE STATE =================
                    data["timers"][cid]["last_check"] = now.isoformat()

                except Exception as e:
                    print(f"[TIMER ITEM ERROR] {cid}:", e)

            # 🔥 save ONCE per loop (instead of many times)
            save_data(data)

            # ================= SLEEP =================
            # ===================== UTC ALIGNED 5-MIN SLEEP =====================
            now = datetime.now(timezone.utc)

            minutes = now.minute % 5
            sleep_time = (5 - minutes) * 60 - now.second

            if sleep_time <= 0:
                sleep_time += 300

            print(f"[LOOP] Sleeping {sleep_time}s")

            await asyncio.sleep(max(5, sleep_time))

        except Exception as e:
            print("[TIMER LOOP CRASH]", e)
            await asyncio.sleep(10)


bot.loop.create_task(timer_loop())

async def tournament_loop(channel, message):
    while True:
        try:
            now = datetime.now(timezone.utc)
            regions = get_regions()

            # find next event
            future_times = []
            for r in regions:
                if now < r["start"]:
                    future_times.append(r["start"])
                if now < r["end"]:
                    future_times.append(r["end"])

            if future_times:
                next_event = min(future_times)
                time_left = (next_event - now).total_seconds()
            else:
                time_left = 3600

            # 🎯 dynamic interval
            if time_left <= 900:
                sleep_time = 300     # 5 min
            elif time_left <= 3600:
                sleep_time = 600     # 10 min
            else:
                sleep_time = 60      # keep loop alive

            print(f"[LOOP] Next update in {sleep_time}s")

            # update UI
            view = build_tournament_view()
            await message.edit(view=view)

            # update channel name
            is_live = any(r["start"] <= now <= r["end"] for r in regions)
            new_name = "tournament-»-started" if is_live else "tournament-»-end"

            if channel.name != new_name:
                await channel.edit(name=new_name)

            await asyncio.sleep(sleep_time)

        except Exception as e:
            print(f"[LOOP ERROR] {e}")
            await asyncio.sleep(10)
        

# ================= COMMANDS =================

@bot.slash_command(name="tournament")
async def tournament(ctx):
    await ctx.defer(ephemeral=True)

    now = datetime.now(timezone.utc)
    state = any(r["start"] <= now <= r["end"] for r in get_regions())
    name = "tournament-»-started" if state else "tournament-»-end"

    ch = await ctx.guild.create_text_channel(
        name=name,
        overwrites={ctx.guild.default_role: discord.PermissionOverwrite(view_channel=True, send_messages=False)},
    )

    msg = await ch.send(view=build_view())
    data["channels"][str(ch.id)] = {"message": msg.id}
    save_data(data)
    bot.loop.create_task(tournament_loop(channel, message))
    await ctx.followup.send("✅ Tournament created", ephemeral=True)

    
    
# ================= ADMIN PANEL =================

class AdminPanelView(discord.ui.View):
    def __init__(self, guild):
        super().__init__(timeout=None)
        self.guild = guild
        self.selected_cid = None

        self.add_item(TimerSelect(guild, self))

    # ➕ CREATE
    @discord.ui.button(label="➕ Create", style=discord.ButtonStyle.green, row=1)
    async def create(self, btn, itx):
        await itx.response.send_modal(CreateTimerModal())

    # ✏️ UPDATE
    @discord.ui.button(label="✏️ Update", style=discord.ButtonStyle.blurple, row=1)
    async def update(self, btn, itx):
        if not self.selected_cid:
            return await itx.response.send_message("Select timer first", ephemeral=True)
        await itx.response.send_modal(UpdateTimerModal(self.selected_cid))

    # 🗑️ DELETE
    @discord.ui.button(label="🗑️ Delete", style=discord.ButtonStyle.red, row=1)
    async def delete(self, btn, itx):
        if not self.selected_cid:
            return await itx.response.send_message("Select timer first", ephemeral=True)

        ch = itx.guild.get_channel(int(self.selected_cid))
        data["timers"].pop(self.selected_cid, None)
        save_data(data)

        if ch:
            await ch.delete()

        await itx.response.send_message("🗑 Deleted", ephemeral=True)

    # ⏳ EXTEND
    @discord.ui.button(label="⏳ Extend", style=discord.ButtonStyle.green, row=2)
    async def extend(self, btn, itx):
        t = data["timers"].get(self.selected_cid)
        if not t:
            return await itx.response.send_message("Select timer first", ephemeral=True)

        end = datetime.fromisoformat(t["end"])
        t["end"] = (end + timedelta(days=7)).isoformat()
        t["warned"] = False
        t["no_delete"] = False
        save_data(data)

        await itx.response.send_message("⏳ Extended", ephemeral=True)

    # 🏁 END MODE
    @discord.ui.button(label="🏁 End Mode", style=discord.ButtonStyle.red, row=2)
    async def endmode(self, btn, itx):
        t = data["timers"].get(self.selected_cid)
        if not t:
            return await itx.response.send_message("Select timer first", ephemeral=True)

        t["no_delete"] = True
        save_data(data)

        await itx.response.send_message("🏁 End mode enabled", ephemeral=True)

    # 📊 VIEW TIMERS
    @discord.ui.button(label="📊 View", style=discord.ButtonStyle.gray, row=2)
    async def view(self, btn, itx):

        view = discord.ui.DesignerView()

        for cid, t in data.get("timers", {}).items():
            try:
                end = datetime.fromisoformat(t["end"])
                ts = int(end.timestamp())

                c = discord.ui.Container(color=discord.Color.blurple())
                c.add_text(f"**{t['name']}**")
                c.add_separator(divider=True)
                c.add_text(f"🕒 <t:{ts}:F>\n⏳ <t:{ts}:R>")

                if t.get("no_delete"):
                    c.add_separator(divider=True)
                    c.add_text("🏁 End Mode: ON")

                view.add_item(c)

            except:
                continue

        await itx.response.send_message(view=view, ephemeral=True)

    # 🏆 TOURNAMENT
    @discord.ui.button(label="🏆 Tournament", style=discord.ButtonStyle.blurple, row=3)
    async def tournament(self, btn, itx):
        await itx.response.defer(ephemeral=True)
        await create_tournament_for_guild(itx.guild)
        await itx.followup.send("🏆 Tournament created", ephemeral=True)

    # ⏭️ SKIP
    @discord.ui.button(label="⏭️ Skip", style=discord.ButtonStyle.secondary, row=3)
    async def skip(self, btn, itx):
        data.setdefault("tournament", {})
        data["tournament"]["skip_next"] = True
        save_data(data)

        await itx.response.send_message("⏭️ Next tournament skipped", ephemeral=True)
        
        
class TimerSelect(discord.ui.Select):
    def __init__(self, guild, panel=None):  # ✅ panel optional
        self.panel = panel

        options = []
        for cid in data.get("timers", {}):
            ch = guild.get_channel(int(cid))
            if ch:
                options.append(
                    discord.SelectOption(
                        label=ch.name[:100],
                        value=cid
                    )
                )

        if not options:
            options.append(
                discord.SelectOption(
                    label="No timers",
                    value="none"
                )
            )

        super().__init__(
            placeholder="Select Timer",
            options=options[:25]
        )

    async def callback(self, interaction):
        if self.values[0] == "none":
            return await interaction.response.send_message("No timers", ephemeral=True)

        # 🔥 Only set if panel exists
        if self.panel:
            self.panel.selected_cid = self.values[0]

        t = data["timers"][self.values[0]]
        end = datetime.fromisoformat(t["end"])
        ts = int(end.timestamp())

        view = discord.ui.DesignerView()

        c = discord.ui.Container(color=discord.Color.green())
        c.add_text(f"🎛️ **{t['name']} Selected**")
        c.add_separator(divider=True)
        c.add_text(f"🕒 <t:{ts}:F>\n⏳ <t:{ts}:R>")

        view.add_item(c)

        await interaction.response.send_message(view=view, ephemeral=True)
        
class CreateTimerModal(discord.ui.Modal):
    def __init__(self):
        super().__init__(title="Create Timer")

        self.name = discord.ui.InputText(label="Name")
        self.date = discord.ui.InputText(label="Date YYYY-MM-DD")
        self.time = discord.ui.InputText(label="Time HH:MM UTC")

        self.add_item(self.name)
        self.add_item(self.date)
        self.add_item(self.time)

    async def callback(self, itx):
        try:
            end = datetime.fromisoformat(f"{self.date.value}T{self.time.value}:00").replace(tzinfo=timezone.utc)
        except:
            return await itx.response.send_message("Invalid format", ephemeral=True)

        ch = await itx.guild.create_voice_channel(f"⏲️ {self.name.value}")

        data["timers"][str(ch.id)] = {
            "name": self.name.value,
            "end": end.isoformat(),
            "warned": False,
            "no_delete": False
        }

        save_data(data)

        await itx.response.send_message(f"✅ Created {ch.mention}", ephemeral=True)

class UpdateTimerModal(discord.ui.Modal):
    def __init__(self, cid):
        super().__init__(title="Update Timer")
        self.cid = cid

        t = data["timers"][cid]

        self.name = discord.ui.InputText(label="Name", value=t["name"])
        self.date = discord.ui.InputText(label="Date YYYY-MM-DD")
        self.time = discord.ui.InputText(label="Time HH:MM UTC")

        self.add_item(self.name)
        self.add_item(self.date)
        self.add_item(self.time)

    async def callback(self, itx):
        try:
            end = datetime.fromisoformat(f"{self.date.value}T{self.time.value}:00").replace(tzinfo=timezone.utc)
        except:
            return await itx.response.send_message("Invalid format", ephemeral=True)

        t = data["timers"][self.cid]
        t["name"] = self.name.value
        t["end"] = end.isoformat()

        save_data(data)

        ch = itx.guild.get_channel(int(self.cid))
        if ch:
            await ch.edit(name=f"⏲️ {self.name.value}")

        await itx.response.send_message("✏️ Updated", ephemeral=True)
        
        
# ================= CREATE TIMER =================

@bot.slash_command(
    name="createtimer",
    description="Create a countdown timer channel"
)

async def createtimer(
    ctx,
    name: discord.Option(str, description="Timer name (e.g. Season 3)"),
    date: discord.Option(str, description="End date: YYYY-MM-DD"),
    time: discord.Option(str, description="End time (UTC): HH:MM (24h)")
):
    await ctx.defer(ephemeral=True)

    # 🧠 Parse datetime
    try:
        end = datetime.fromisoformat(f"{date}T{time}:00").replace(tzinfo=timezone.utc)
    except:
        return await ctx.followup.send(
            "❌ Invalid format\n\n📅 Date: YYYY-MM-DD\n⏰ Time: HH:MM (UTC)",
            ephemeral=True
        )

    now = datetime.now(timezone.utc)
    diff = end - now

    # 🧠 Generate initial channel name
    if diff.total_seconds() <= 0:
        channel_name = f"⏲️ {name} » ENDED"
    elif diff.total_seconds() < 3600:
        mins = diff.seconds // 60
        channel_name = f"⏲️ {name} » {mins}M"
    else:
        d = diff.days
        h = diff.seconds // 3600
        channel_name = f"⏲️ {name} » {d}D {h}H"

    # 🔒 Permissions (visible but not joinable)
    overwrites = {
        ctx.guild.default_role: discord.PermissionOverwrite(
            view_channel=True,
            connect=False
        ),
        ctx.guild.me: discord.PermissionOverwrite(
            view_channel=True,
            connect=True
        )
    }

    # 📡 Create channel
    try:
        channel = await ctx.guild.create_voice_channel(
            name=channel_name,
            overwrites=overwrites
        )
    except Exception as e:
        return await ctx.followup.send(
            f"❌ Failed to create channel\n{e}",
            ephemeral=True
        )
    # 💾 Store data
    data.setdefault("timers", {})
    data["timers"][str(channel.id)] = {
        "name": name,
        "end": end.isoformat(),
        "warned": False
    }
    save_data(data)
    # ✅ Done
    await ctx.respond(
        f"✅ Timer created: {channel.mention}",
        ephemeral=True
    )

# ================= UPDATE TIMER =================


class TimerModal(discord.ui.Modal):
    def __init__(self, cid):
        super().__init__(title="Update Timer")

        self.cid = cid

        # 🧠 Pre-fill existing values
        existing = data.get("timers", {}).get(cid, {})

        self.name = discord.ui.InputText(
            label="Name",
            placeholder="e.g. Season 3",
            value=existing.get("name", ""),
            required=True
        )

        self.date = discord.ui.InputText(
            label="Date (YYYY-MM-DD)",
            placeholder="2026-04-25",
            required=True
        )

        self.time = discord.ui.InputText(
            label="Time (HH:MM UTC)",
            placeholder="18:30",
            required=True
        )

        self.add_item(self.name)
        self.add_item(self.date)
        self.add_item(self.time)

    async def callback(self, interaction: discord.Interaction):
        print(f"[MODAL] Updating timer {self.cid}")

        try:
            # 🧠 parse datetime
            end = datetime.fromisoformat(
                f"{self.date.value}T{self.time.value}:00"
            ).replace(tzinfo=timezone.utc)

        except Exception as e:
            print("[MODAL PARSE ERROR]", e)
            return await interaction.response.send_message(
                "❌ Invalid format\n\n"
                "📅 Date: YYYY-MM-DD\n"
                "⏰ Time: HH:MM (UTC)",
                ephemeral=True
            )

        try:
            # 🧠 update data
            if "timers" not in data:
                data["timers"] = {}

            if self.cid not in data["timers"]:
                return await interaction.response.send_message(
                    "⚠️ Timer not found",
                    ephemeral=True
                )

            data["timers"][self.cid]["name"] = self.name.value
            data["timers"][self.cid]["end"] = end.isoformat()
            save_data(data)

            # ⚡ update channel instantly
            channel = interaction.guild.get_channel(int(self.cid))

            if channel:
                now = datetime.now(timezone.utc)
                diff = end - now

                if diff.total_seconds() <= 0:
                    new_name = f"⏲️ {self.name.value} » ENDED"

                elif diff.total_seconds() < 3600:
                    mins = diff.seconds // 60
                    new_name = f"⏲️ {self.name.value} » {mins}M"

                else:
                    d = diff.days
                    h = diff.seconds // 3600
                    new_name = f"⏲️ {self.name.value} » {d}D {h}H"

                try:
                    if channel.name != new_name:
                        await channel.edit(name=new_name)
                except Exception as e:
                    print("[CHANNEL EDIT ERROR]", e)

            await interaction.response.send_message(
                "✅ Timer updated successfully",
                ephemeral=True
            )

        except Exception as e:
            print("[MODAL ERROR]", e)
            await interaction.response.send_message(
                "⚠️ Something went wrong while updating",
                ephemeral=True
            )

class TimerSelect(discord.ui.Select):
    def __init__(self, guild):
        options = []
        for cid in data["timers"]:
            ch = guild.get_channel(int(cid))
            if ch:
                options.append(discord.SelectOption(label=ch.name, value=cid))

        super().__init__(options=options[:25], placeholder="Select timer")

    async def callback(self, interaction):
        await interaction.response.send_modal(TimerModal(self.values[0]))


class TimerView(discord.ui.View):
    def __init__(self, guild):
        super().__init__()
        self.add_item(TimerSelect(guild))


@bot.slash_command(name="updatetimer")
async def updatetimer(ctx):
    if not data["timers"]:
        return await ctx.respond("⚠️ No timers found", ephemeral=True)

    await ctx.respond("Select timer:", view=TimerView(ctx.guild), ephemeral=True)

# ================= DELETE =================


class DeleteSelect(discord.ui.Select):
    def __init__(self, guild):
        options = []

        now = datetime.now(timezone.utc)

        # 🔹 Tournament channels
        for cid in data.get("channels", {}):
            ch = guild.get_channel(int(cid))
            if ch:
                options.append(
                    discord.SelectOption(
                        label=ch.name[:100],
                        value=f"c_{cid}",
                        description="Tournament"
                    )
                )

        # 🔹 Timer channels (WITH countdown preview)
        for cid, t in data.get("timers", {}).items():
            ch = guild.get_channel(int(cid))
            if not ch:
                continue

            try:
                end = datetime.fromisoformat(t["end"])
                diff = end - now

                if diff.total_seconds() <= 0:
                    time_str = "ENDED"

                elif diff.days == 0 and diff.seconds < 3600:
                    # 🔥 minutes mode
                    mins = diff.seconds // 60
                    time_str = f"{mins}M"

                else:
                    days = diff.days
                    hours = diff.seconds // 3600
                    time_str = f"{days}D {hours}H"

            except:
                time_str = "Invalid"

            options.append(
                discord.SelectOption(
                    label=ch.name[:100],
                    value=f"t_{cid}",
                    description=f"{time_str} remaining"
                )
            )

        # 🚨 IMPORTANT: handle empty
        if not options:
            options = [
                discord.SelectOption(
                    label="No channels available",
                    value="none",
                    description="Nothing to delete"
                )
            ]

        super().__init__(
            placeholder="Select a channel to delete...",
            min_values=1,
            max_values=1,
            options=options[:25]
        )

    async def callback(self, interaction: discord.Interaction):
        value = self.values[0]

        if value == "none":
            return await interaction.response.send_message(
                "⚠️ Nothing to delete",
                ephemeral=True
            )

        typ, cid = value.split("_")
        ch = interaction.guild.get_channel(int(cid))

        # 🧠 remove from data
        data["channels"].pop(cid, None)
        data["timers"].pop(cid, None)
        save_data(data)

        if ch:
            name = ch.name
            await ch.delete()

            await interaction.response.send_message(
                f"🗑 Deleted **{name}**",
                ephemeral=True
            )
        else:
            await interaction.response.send_message(
                "⚠️ Channel not found but removed from data",
                ephemeral=True
            )


class DeleteView(discord.ui.View):
    def __init__(self, guild):
        super().__init__(timeout=60)
        self.add_item(DeleteSelect(guild))

@bot.slash_command(name="deletetimer")
async def deletetimer(ctx):

    if not (ctx.author.guild_permissions.administrator or ctx.author.id == DAX):
        return await ctx.respond("❌ Admin only", ephemeral=True)

    # 🔥 check before building UI
    has_channels = any(ctx.guild.get_channel(int(cid)) for cid in data.get("channels", {}))
    has_timers = any(ctx.guild.get_channel(int(cid)) for cid in data.get("timers", {}))

    if not has_channels and not has_timers:
        return await ctx.respond("⚠️ No channels to delete", ephemeral=True)

    await ctx.respond(
        "Select channel:",
        view=DeleteView(ctx.guild),
        ephemeral=True
    )

@bot.event
async def on_ready():
    print(f"Logged in as {bot.user}")

    await asyncio.sleep(2)  # let cache load

    # 🔁 refresh all timers instantly on restart
    for cid, t in data.get("timers", {}).items():
        channel = bot.get_channel(int(cid))
        if not channel:
            continue

        try:
            end = datetime.fromisoformat(t["end"])
            now = datetime.now(timezone.utc)
            diff = end - now

            if diff.total_seconds() <= 0:
                new_name = f"⏲️ {t['name']} » ENDED"

            elif diff.days == 0 and diff.seconds < 3600:
                # 🔥 minutes mode
                mins = diff.seconds // 60
                new_name = f"⏲️ {t['name']} » {mins}M"

            else:
                days = diff.days
                hours = diff.seconds // 3600
                new_name = f"⏲️ {t['name']} » {days}D {hours}H"

            if channel.name != new_name:
                await channel.edit(name=new_name)

        except Exception as e:
            print(f"[Timer Restart Error] {cid}:", e)

    # ================= ADMIN PANEL START =================

    try:
        channel = bot.get_channel(adminch)

        if not channel:
            print("❌ Admin channel not found")
            return

        guild = channel.guild

        # 🔁 Register persistent panel view
        bot.add_view(AdminPanelView(guild))

        panel_data = data.get("panel")

        # 🔍 Check if panel exists
        if panel_data:
            try:
                await channel.fetch_message(panel_data["message"])
                print("✅ Admin panel already exists")
                return
            except:
                print("⚠️ Panel missing, recreating...")

        # 🆕 Create panel
        panel_view = discord.ui.DesignerView(timeout=None)

        container = discord.ui.Container(color=discord.Color.blurple())

        container.add_text("🎛️ **ADMIN CONTROL PANEL**")
        container.add_separator(divider=True)
        container.add_text("Manage all timers and tournaments from here.")

        panel_view.add_item(container)

        # 🔽 Dropdown (IMPORTANT: bind SAME panel instance)
        panel = AdminPanelView(guild)
        panel_view.add_item(panel.children[0])  # TimerSelect

        msg = await channel.send(view=panel_view)

        # 💾 Save panel
        data["panel"] = {
            "channel": channel.id,
            "message": msg.id
        }
        save_data(data)

        print("✅ Admin panel created")

    except Exception as e:
        print("[ADMIN PANEL ERROR]", e)


# ================= SAY =================

@bot.slash_command(name="say")
async def say(ctx, message: str):
    await ctx.defer(ephemeral=True)
    await ctx.channel.send(message)
    await ctx.followup.send("✅ Sent", ephemeral=True)

# ================= RUN =================

bot.run(TOKEN)
