#!/usr/bin/env bash
# PreToolUse(Agent): BLOCKING gate on subagent cost.
#
# Two independent checks, both added 2026-07-28 after a routing-eval run spent
# ~850k tokens on 28 general-purpose judges (~30k each, ~21k of which was the
# agent's own system prompt and tool schemas) for one-word answers:
#
#   1. ROUTING JUDGE TYPE. A prompt that is clearly a routing judge (a skill
#      listing + one query, asked which skill fires) must use
#      subagent_type: routing-judge -- a minimal agent with one tool -- not
#      general-purpose. Same verdicts, a fraction of the tokens.
#
#   2. FAN-OUT BURST CAP. More than MAX_BURST Agent spawns inside WINDOW seconds
#      is denied. Not because parallelism is bad, but because a fleet should be
#      a decision the user is party to: the 2026-07-28 run launched 17 at once
#      after computing -- and not surfacing -- the projected cost.
#
# Override is deliberately NOT arrangeable from inside a session: set
# CLAUDE_AGENT_GUARD_OFF=1 in the environment Claude Code was launched with, or
# toggle the hook in /hooks. A Bash call cannot mutate the parent's environment.
set -u

MAX_BURST=6
WINDOW=120

input=$(cat)

if [ "${CLAUDE_AGENT_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
dir="${TMPDIR:-/tmp}"

subtype=$(printf '%s' "$input" | jq -r '.tool_input.subagent_type // ""' 2>/dev/null) || subtype=""
prompt=$(printf '%s' "$input"  | jq -r '.tool_input.prompt // ""' 2>/dev/null) || prompt=""

deny() {
  jq -n --arg r "$1" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "deny",
      permissionDecisionReason: $r
    }
  }'
  exit 0
}

# --- Check 1: routing judges must use the routing-judge agent ---------------
lower=$(printf '%s' "$prompt" | tr '[:upper:]' '[:lower:]')
is_judge=no
case $lower in
  *"routing judge"*) is_judge=yes ;;
  *"should fire"*)
    case $lower in *skill*) is_judge=yes ;; esac ;;
esac

if [ "$is_judge" = yes ] && [ "$subtype" != "routing-judge" ]; then
  deny "BLOCKED by agent-guard: this looks like a skill-routing judge but subagent_type is '${subtype:-<unset>}'.

Use subagent_type: \"routing-judge\" (.claude/agents/routing-judge.md). A general-purpose agent costs ~30k tokens per verdict, of which ~21k is its own system prompt and full tool schemas -- paid to produce one word. routing-judge carries one tool and the mandatory TOTAL= checksum that makes a skipped listing-read detectable.

Also required by skill-routing-maintenance step 2: inline the listing in the prompt, never pass a file path (a judge that can skip the read sometimes will, and then guesses a plausible skill name)."
fi

# --- Check 2: fan-out burst cap --------------------------------------------
log="${dir}/claude-agent-spawns-${sid:-nosession}"
now=$(date +%s)
cutoff=$((now - WINDOW))

recent=0
if [ -f "$log" ]; then
  # keep only timestamps inside the window
  awk -v c="$cutoff" '$1 >= c' "$log" > "${log}.tmp" 2>/dev/null && mv "${log}.tmp" "$log" 2>/dev/null || true
  recent=$(wc -l < "$log" 2>/dev/null | tr -d ' ') || recent=0
fi
[ -z "$recent" ] && recent=0

if [ "$recent" -ge "$MAX_BURST" ]; then
  deny "BLOCKED by agent-guard: ${recent} subagents already spawned in the last ${WINDOW}s (cap ${MAX_BURST}).

A fan-out this size should be the user's call, not a default. On 2026-07-28 a 17-agent launch cost ~850k tokens after the per-agent price had been measured but not surfaced.

Do this instead: (a) state the projected cost (agents x per-agent tokens) and get a go-ahead, (b) batch several items into one agent, or (c) cut the sample -- for routing evals, migrated entries usually all test the same decision, so a couple per affected skill is as informative as all of them.

The window rolls: waiting lets it drain."
fi

printf '%s\n' "$now" >> "$log" 2>/dev/null || true
exit 0
