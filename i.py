"""
i.py  (interaction_utils)
════════════════════════════════════════════════════════════════════════
Centralised Discord interaction safety middleware.

Compatible with: Pycord 2.x, discord.py 2.x
Designed for:   Components V2, DesignerViews, ephemeral admin panels,
                persistent views, modals, dropdowns, long-lived sessions.

QUICK REFERENCE
───────────────
  safe_send_response()    Primary response or automatic followup fallback
  safe_edit_response()    Edit-in-place with V2 content-collision fix
  safe_followup()         Followup after primary response, with fallback
  safe_panel_refresh()    Rebuild ephemeral panel (always content=None)
  safe_logout_response()  Transition panel → login view on logout
  safe_components_edit()  Swap one DesignerView for another in-place
  safe_send_modal()       Open a modal as primary response
  safe_defer()            Acknowledge without visible response

  reply_stale()           "Interaction expired" convenience message
  reply_session_expired() "Session expired" convenience message
  reply_unauthorized()    "Unauthorized" convenience message
  reply_debounce()        "Already in progress" convenience message

  set_error_logger(fn)    Register your structured error-log coroutine
  IxResult                Enum: OK / STALE / DOUBLE / MISSING / FAILED

WHY RAW DISCORD INTERACTION CALLS ARE DANGEROUS
────────────────────────────────────────────────
In a simple stateless bot every interaction is fresh and independent.
In a stateful bot with persistent DesignerViews, session locking,
background tasks, modals, and ephemeral admin panels the interaction
lifecycle is complex and full of edge cases:

  1. INTERACTION EXPIRY  (error 10062 Unknown Interaction)
     Discord interaction tokens expire after 15 minutes.  Persistent
     views receive interactions on tokens created much earlier.  Any
     await that crosses this boundary raises NotFound.

  2. DOUBLE-RESPONSE  (InteractionResponded)
     Calling response.send_message() twice on the same interaction
     raises InteractionResponded.  Happens from concurrent button
     presses, debounce races, or error-recovery paths.

  3. COMPONENTS V2 + CONTENT COLLISION  (error 50035 Invalid Form Body)
     Discord rejects edit payloads that include both a `content` field
     and MessageFlags.IS_COMPONENTS_V2.  Even content="" triggers it —
     you must explicitly pass content=None in every edit.

  4. EPHEMERAL STALE MESSAGES
     Ephemeral messages disappear when the user navigates away.  Editing
     them afterward raises NotFound even on a valid token.

  5. MODAL → PANEL REFRESH LIFECYCLE MISMATCH
     Modal callbacks own their own interaction object.  Calling
     edit_original_response() on a modal interaction edits the modal's
     invisible phantom message, not the ephemeral panel behind it.
     Correct approach: safe_modal_response() sends the modal result,
     then safe_panel_refresh() targets the panel via the webhook token
     the modal inherited from its originating button interaction.

  6. DEFERRED + FOLLOWUP ORDERING
     Calling defer() then response.send_message() fails because the
     response slot is already consumed by the defer ACK.

  7. CONCURRENT ASYNC TASKS
     Background timer tasks can delete channels or mutate DB state
     between when a button interaction is received and when it finishes.
     Wrappers detect and handle the resulting NotFound/HTTPException
     errors instead of crashing the task.

ERROR CLASSIFICATION
────────────────────
  STALE      10062 / token expired      → inform user, return STALE
  DOUBLE     40060 / already responded  → silent return DOUBLE
  MISSING    10008 / message gone        → return MISSING
  RATE_LIMIT 429                         → back-off sleep + retry
  COMPONENTS 50035 / V2+content clash   → strip content, retry once
  TRANSIENT  5xx                         → retry up to max_retries
  FATAL      anything else               → log_error + return FAILED

FALLBACK HIERARCHY
──────────────────
  edit_original_response()
    └─ fails → response.edit_message()
                 └─ fails → followup.send()
                              └─ fails → log_error() silently
"""

from __future__ import annotations

import asyncio
import traceback
from enum import Enum, auto
from typing import Any

import discord


# ══════════════════════════════════════════════════════════════════════
# RESULT ENUM
# ══════════════════════════════════════════════════════════════════════

class IxResult(Enum):
    OK      = auto()   # action completed successfully
    STALE   = auto()   # interaction token expired — nothing sent to user
    DOUBLE  = auto()   # response slot already consumed — nothing sent
    MISSING = auto()   # target message/channel no longer exists
    FAILED  = auto()   # non-recoverable; error has been logged


# ══════════════════════════════════════════════════════════════════════
# ERROR LOGGER REGISTRATION
# ══════════════════════════════════════════════════════════════════════

_log_error_fn: Any = None   # async (location: str, exc: Exception, extra: str) → None

def set_error_logger(fn: Any) -> None:
    """
    Register the application's structured error-logging coroutine.

    Must be called once during bot startup before any interaction wrapper
    is used.  If not registered, errors are printed to stdout only.

        import i as ix
        ix.set_error_logger(log_error)   # your existing log_error()
    """
    global _log_error_fn
    _log_error_fn = fn


async def _log(location: str, exc: Exception, extra: str = "") -> None:
    """Route errors to the registered logger or fallback to stdout."""
    print(f"[IX][{location}] {exc}\n{traceback.format_exc()[-600:]}")
    if _log_error_fn is not None:
        try:
            await _log_error_fn(location, exc, extra)
        except Exception:
            pass


# ══════════════════════════════════════════════════════════════════════
# INTERNAL HELPERS
# ══════════════════════════════════════════════════════════════════════

def _responded(itx: discord.Interaction) -> bool:
    """True if a primary response has already been sent."""
    try:
        return itx.response.is_done()
    except Exception:
        return False


def _classify(exc: discord.HTTPException) -> str:
    """Return a short error-category tag for a Discord HTTPException."""
    code   = getattr(exc, "code",   0)
    status = getattr(exc, "status", 0)
    if code == 10062:              return "STALE"
    if code in (10008, 10003):     return "MISSING"
    if code == 40060:              return "DOUBLE"
    if code == 50035:              return "COMPONENTS"
    if status == 429:              return "RATE_LIMIT"
    if 500 <= status < 600:        return "TRANSIENT"
    return "HTTP"


async def _backoff(exc: discord.RateLimited) -> None:
    """Sleep for the Discord-specified retry-after duration."""
    await asyncio.sleep(getattr(exc, "retry_after", 1.0) + 0.25)


def _maybe_strip_content(
    is_v2: bool,
    content: str | None,
) -> str | None:
    """
    Components V2 messages must never carry a content field.
    Silently strip it here so callers don't have to remember.
    """
    return None if is_v2 else content


# ══════════════════════════════════════════════════════════════════════
# safe_send_response()
# ══════════════════════════════════════════════════════════════════════

async def safe_send_response(
    itx: discord.Interaction,
    content: str | None = None,
    *,
    view: discord.ui.View | None = None,
    ephemeral: bool = True,
    max_retries: int = 2,
    silent: bool = False,
) -> IxResult:
    """
    Send a primary interaction response, or fall back to followup.send()
    if the primary slot is already consumed.

    Handles automatically:
    - Double-response detection and silent followup fallback
    - Components V2 content-field stripping (error 50035)
    - Expired interaction (10062) — returns STALE
    - Rate-limit back-off and transient retries

    Use for:  button callbacks, select callbacks, error/auth messages,
              session-expired notifications, validation errors.
    """
    is_v2    = isinstance(view, discord.ui.DesignerView)
    content  = _maybe_strip_content(is_v2, content)

    for attempt in range(max_retries + 1):
        try:
            if _responded(itx):
                # Slot consumed — send as followup instead
                kw: dict = {"ephemeral": ephemeral}
                if content is not None:
                    kw["content"] = content
                if view is not None:
                    kw["view"] = view
                await itx.followup.send(**kw)
                return IxResult.OK

            kw = {"ephemeral": ephemeral}
            if content is not None:
                kw["content"] = content
            if view is not None:
                kw["view"] = view
            await itx.response.send_message(**kw)
            return IxResult.OK

        except discord.InteractionResponded:
            # Slot was consumed between our check and the call — retry as followup
            try:
                kw = {"ephemeral": ephemeral}
                if content is not None:
                    kw["content"] = content
                if view is not None:
                    kw["view"] = view
                await itx.followup.send(**kw)
                return IxResult.OK
            except Exception:
                return IxResult.DOUBLE

        except discord.RateLimited as e:
            await _backoff(e)

        except discord.NotFound as e:
            if not silent:
                await _log("safe_send_response/NotFound", e)
            return IxResult.STALE

        except discord.HTTPException as e:
            tag = _classify(e)
            if tag in ("STALE", "DOUBLE"):
                return IxResult.STALE
            if attempt < max_retries:
                await asyncio.sleep(2 ** attempt)
            else:
                if not silent:
                    await _log("safe_send_response", e)
                return IxResult.FAILED

        except Exception as e:
            if not silent:
                await _log("safe_send_response/unexpected", e)
            return IxResult.FAILED

    return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# safe_edit_response()
# ══════════════════════════════════════════════════════════════════════

async def safe_edit_response(
    itx: discord.Interaction,
    content: str | None = None,
    *,
    view: discord.ui.View | None = None,
    max_retries: int = 2,
    silent: bool = False,
) -> IxResult:
    """
    Edit the original response for this interaction.

    Always passes content=None for DesignerViews to prevent the
    Components V2 + content collision (error 50035).

    Fallback hierarchy:
      edit_original_response() → response.edit_message() → followup.send()
    """
    is_v2   = isinstance(view, discord.ui.DesignerView)
    content = _maybe_strip_content(is_v2, content)

    for attempt in range(max_retries + 1):
        try:
            kw: dict = {}
            if content is not None:
                kw["content"] = content
            elif is_v2:
                kw["content"] = None   # explicitly clear for V2
            if view is not None:
                kw["view"] = view
            await itx.edit_original_response(**kw)
            return IxResult.OK

        except discord.RateLimited as e:
            await _backoff(e)

        except discord.NotFound as e:
            # Token expired — try response.edit_message then followup
            try:
                kw2: dict = {}
                if content is not None:
                    kw2["content"] = content
                elif is_v2:
                    kw2["content"] = None
                if view is not None:
                    kw2["view"] = view
                await itx.response.edit_message(**kw2)
                return IxResult.OK
            except Exception:
                pass
            try:
                fu_kw: dict = {"ephemeral": True}
                if view is not None:
                    fu_kw["view"] = view
                if content is not None:
                    fu_kw["content"] = content
                await itx.followup.send(**fu_kw)
                return IxResult.OK
            except Exception:
                pass
            if not silent:
                await _log("safe_edit_response/stale", e)
            return IxResult.STALE

        except discord.HTTPException as e:
            tag = _classify(e)
            if tag == "COMPONENTS":
                # Strip content and retry once more
                content = None
                if attempt < max_retries:
                    continue
                if not silent:
                    await _log("safe_edit_response/COMPONENTS", e)
                return IxResult.FAILED
            if tag in ("STALE", "DOUBLE"):
                return IxResult.STALE
            if attempt < max_retries:
                await asyncio.sleep(2 ** attempt)
            else:
                if not silent:
                    await _log("safe_edit_response", e)
                return IxResult.FAILED

        except Exception as e:
            if not silent:
                await _log("safe_edit_response/unexpected", e)
            return IxResult.FAILED

    return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# safe_followup()
# ══════════════════════════════════════════════════════════════════════

async def safe_followup(
    itx: discord.Interaction,
    content: str | None = None,
    *,
    view: discord.ui.View | None = None,
    ephemeral: bool = True,
    max_retries: int = 2,
    silent: bool = False,
) -> IxResult:
    """
    Send a followup message after a primary response has been sent.

    Automatically falls back to safe_send_response() if the primary slot
    has not yet been consumed (guards against premature followup calls).
    Handles expired tokens and rate limits.

    Use for:  post-confirm feedback, post-defer results, post-modal
              completion messages, multi-step operation results.
    """
    is_v2   = isinstance(view, discord.ui.DesignerView)
    content = _maybe_strip_content(is_v2, content)

    if not _responded(itx):
        # Primary slot not consumed — route through safe_send_response
        return await safe_send_response(
            itx, content, view=view, ephemeral=ephemeral,
            max_retries=max_retries, silent=silent,
        )

    for attempt in range(max_retries + 1):
        try:
            kw: dict = {"ephemeral": ephemeral}
            if content is not None:
                kw["content"] = content
            if view is not None:
                kw["view"] = view
            await itx.followup.send(**kw)
            return IxResult.OK

        except discord.RateLimited as e:
            await _backoff(e)

        except discord.NotFound as e:
            if not silent:
                await _log("safe_followup/NotFound", e)
            return IxResult.STALE

        except discord.HTTPException as e:
            tag = _classify(e)
            if tag == "STALE":
                return IxResult.STALE
            if attempt < max_retries:
                await asyncio.sleep(2 ** attempt)
            else:
                if not silent:
                    await _log("safe_followup", e)
                return IxResult.FAILED

        except Exception as e:
            if not silent:
                await _log("safe_followup/unexpected", e)
            return IxResult.FAILED

    return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# safe_panel_refresh()
# ══════════════════════════════════════════════════════════════════════

async def safe_panel_refresh(
    itx: discord.Interaction,
    new_view: discord.ui.DesignerView,
    *,
    silent: bool = False,
) -> IxResult:
    """
    Rebuild and replace the ephemeral admin panel message in-place.

    Always passes content=None to prevent the Components V2 + content
    field collision (error 50035) that occurs whenever a prior edit
    or send included a content string alongside a DesignerView.

    Why content=None is mandatory here:
      Once a message carries MessageFlags.IS_COMPONENTS_V2, Discord
      rejects any subsequent edit that includes a content field — even
      content="" — with error 50035.  There is no way to unset the flag,
      so every future edit of that message must omit content entirely.

    Fallback hierarchy:
      edit_original_response(content=None, view=…)
        └─ fails (stale/rate-limit) → followup.send(view=…, ephemeral=True)
                                        └─ fails → log_error silently
    """
    for attempt in range(3):
        try:
            await itx.edit_original_response(content=None, view=new_view)
            return IxResult.OK

        except discord.RateLimited as e:
            await _backoff(e)

        except discord.NotFound as e:
            # Token expired — send panel as a fresh followup instead
            try:
                await itx.followup.send(view=new_view, ephemeral=True)
                return IxResult.OK
            except Exception:
                pass
            if not silent:
                await _log(
                    "safe_panel_refresh/stale", e,
                    "Interaction token expired before panel refresh completed",
                )
            return IxResult.STALE

        except discord.HTTPException as e:
            tag = _classify(e)
            if tag == "COMPONENTS":
                # content=None should prevent this — log and give up
                if not silent:
                    await _log(
                        "safe_panel_refresh/COMPONENTS_COLLISION", e,
                        "V2+content collision despite content=None — check payload",
                    )
                return IxResult.FAILED
            if tag == "STALE":
                return IxResult.STALE
            if attempt < 2:
                await asyncio.sleep(2 ** attempt)
            else:
                if not silent:
                    await _log("safe_panel_refresh", e)
                return IxResult.FAILED

        except Exception as e:
            if not silent:
                await _log("safe_panel_refresh/unexpected", e)
            return IxResult.FAILED

    return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# safe_logout_response()
# ══════════════════════════════════════════════════════════════════════

async def safe_logout_response(
    itx: discord.Interaction,
    login_view: discord.ui.View,
    *,
    silent: bool = False,
) -> IxResult:
    """
    Transition the ephemeral panel message back to the login view.

    This is the correct way to handle the Logout button.  Raw calls to
    itx.response.edit_message(view=PanelLoginView()) fail with 10062
    on any session longer than a few minutes because the underlying
    button interaction token has expired.

    Fallback hierarchy:
      response.edit_message(content=None, view=login_view)
        └─ response.is_done / stale → edit_original_response(…)
                                        └─ fails → followup.send(…)
    """
    # Attempt 1: direct button-interaction edit
    if not _responded(itx):
        try:
            await itx.response.edit_message(content=None, view=login_view)
            return IxResult.OK
        except discord.InteractionResponded:
            pass
        except discord.RateLimited as e:
            await _backoff(e)
        except discord.NotFound:
            pass  # token expired — move to fallback
        except discord.HTTPException:
            pass
        except Exception as e:
            if not silent:
                await _log("safe_logout_response/edit_message", e)

    # Attempt 2: edit via webhook token
    try:
        await itx.edit_original_response(content=None, view=login_view)
        return IxResult.OK
    except Exception:
        pass

    # Attempt 3: send a new ephemeral message with the login view
    try:
        await itx.followup.send(view=login_view, ephemeral=True)
        return IxResult.OK
    except Exception as e:
        if not silent:
            await _log("safe_logout_response/all_fallbacks_failed", e)
        return IxResult.STALE


# ══════════════════════════════════════════════════════════════════════
# safe_components_edit()
# ══════════════════════════════════════════════════════════════════════

async def safe_components_edit(
    itx: discord.Interaction,
    new_view: discord.ui.DesignerView,
    *,
    max_retries: int = 2,
    silent: bool = False,
) -> IxResult:
    """
    Edit the current interaction message to a new DesignerView payload.

    Used for in-place view transitions such as login → full panel.
    Always passes content=None (V2 requirement).

    Prefers response.edit_message() for button callbacks (avoids consuming
    the followup webhook), then falls back to edit_original_response().
    """
    for attempt in range(max_retries + 1):
        try:
            if not _responded(itx):
                await itx.response.edit_message(content=None, view=new_view)
            else:
                await itx.edit_original_response(content=None, view=new_view)
            return IxResult.OK

        except discord.InteractionResponded:
            try:
                await itx.edit_original_response(content=None, view=new_view)
                return IxResult.OK
            except Exception:
                return IxResult.DOUBLE

        except discord.RateLimited as e:
            await _backoff(e)

        except discord.NotFound as e:
            # Token expired — send as a new ephemeral followup
            try:
                await itx.followup.send(view=new_view, ephemeral=True)
                return IxResult.OK
            except Exception:
                pass
            if not silent:
                await _log("safe_components_edit/stale", e)
            return IxResult.STALE

        except discord.HTTPException as e:
            tag = _classify(e)
            if tag == "COMPONENTS":
                if not silent:
                    await _log("safe_components_edit/COMPONENTS", e)
                return IxResult.FAILED
            if tag == "STALE":
                return IxResult.STALE
            if attempt < max_retries:
                await asyncio.sleep(2 ** attempt)
            else:
                if not silent:
                    await _log("safe_components_edit", e)
                return IxResult.FAILED

        except Exception as e:
            if not silent:
                await _log("safe_components_edit/unexpected", e)
            return IxResult.FAILED

    return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# safe_modal_response()
# ══════════════════════════════════════════════════════════════════════

async def safe_modal_response(
    itx: discord.Interaction,
    content: str | None = None,
    *,
    view: discord.ui.View | None = None,
    ephemeral: bool = True,
    silent: bool = False,
) -> IxResult:
    """
    Send a response from inside a modal callback.

    Modal interactions own their own response slot.  They must always use
    send_message (or followup), never edit_original_response — that would
    edit the modal's own invisible phantom message, not the panel below.

    After this call, refresh the panel separately via safe_panel_refresh().
    """
    return await safe_send_response(
        itx, content, view=view, ephemeral=ephemeral, silent=silent,
    )


# ══════════════════════════════════════════════════════════════════════
# safe_send_modal()
# ══════════════════════════════════════════════════════════════════════

async def safe_send_modal(
    itx: discord.Interaction,
    modal: discord.ui.Modal,
    *,
    silent: bool = False,
) -> IxResult:
    """
    Open a modal from a button or select callback.

    Modals must be sent as the PRIMARY response — they cannot be sent as
    followups.  Returns DOUBLE if the slot is already consumed; the caller
    should fall back to safe_send_response() with an error message.
    """
    if _responded(itx):
        return IxResult.DOUBLE

    try:
        await itx.response.send_modal(modal)
        return IxResult.OK

    except discord.InteractionResponded:
        return IxResult.DOUBLE

    except discord.NotFound as e:
        if not silent:
            await _log("safe_send_modal/stale", e)
        return IxResult.STALE

    except discord.HTTPException as e:
        tag = _classify(e)
        if tag == "STALE":
            return IxResult.STALE
        if not silent:
            await _log("safe_send_modal", e)
        return IxResult.FAILED

    except Exception as e:
        if not silent:
            await _log("safe_send_modal/unexpected", e)
        return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# safe_defer()
# ══════════════════════════════════════════════════════════════════════

async def safe_defer(
    itx: discord.Interaction,
    *,
    ephemeral: bool = True,
    thinking: bool = False,
    silent: bool = False,
) -> IxResult:
    """
    Acknowledge an interaction without sending visible content yet.

    Consuming the 3-second response window gives the bot up to 15 minutes
    to send the actual content via safe_followup().

    Call immediately at the start of any long-running handler.
    """
    if _responded(itx):
        return IxResult.DOUBLE

    try:
        await itx.response.defer(ephemeral=ephemeral)
        return IxResult.OK

    except discord.InteractionResponded:
        return IxResult.DOUBLE

    except discord.NotFound as e:
        if not silent:
            await _log("safe_defer/NotFound", e)
        return IxResult.STALE

    except discord.HTTPException as e:
        tag = _classify(e)
        if tag in ("STALE", "DOUBLE"):
            return IxResult.STALE
        if not silent:
            await _log("safe_defer", e)
        return IxResult.FAILED

    except Exception as e:
        if not silent:
            await _log("safe_defer/unexpected", e)
        return IxResult.FAILED


# ══════════════════════════════════════════════════════════════════════
# CONVENIENCE REPLY HELPERS
# ══════════════════════════════════════════════════════════════════════

STALE_MSG     = "Interaction expired. Please re-open `/timerpanel`."
SESSION_MSG   = "Session expired. Please re-open `/timerpanel`."
UNAUTH_MSG    = "Unauthorized. Please re-open `/timerpanel`."
DEBOUNCE_MSG  = "Operation already in progress. Please wait."


async def reply_stale(itx: discord.Interaction) -> IxResult:
    """Send a standard 'interaction expired' message."""
    return await safe_send_response(itx, STALE_MSG, ephemeral=True, silent=True)


async def reply_session_expired(itx: discord.Interaction) -> IxResult:
    """Send a standard 'session expired' message."""
    return await safe_send_response(itx, SESSION_MSG, ephemeral=True, silent=True)


async def reply_unauthorized(itx: discord.Interaction) -> IxResult:
    """Send a standard 'unauthorized' message."""
    return await safe_send_response(itx, UNAUTH_MSG, ephemeral=True, silent=True)


async def reply_debounce(itx: discord.Interaction) -> IxResult:
    """Send a standard 'already in progress' message."""
    return await safe_send_response(itx, DEBOUNCE_MSG, ephemeral=True, silent=True)
