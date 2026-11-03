#!/usr/bin/env bash
# PostToolUse (every tool): terse context-size telemetry for a COORDINATOR.
# PLAN-context-economy Phase 1.
#
# After each tool call, reads the context size of WHICHEVER agent made it and,
# only when that agent crosses a threshold for the first time, appends ONE line
#   <ISO time> | <agent> | ctx <N>k (crossed <T>k) | calls <n> | <tool>
# to  <scratchpad_dir>/telemetry/events.log .
# A coordinator watches that file with Monitor (`tail -n0 -F .../events.log`)
# and so learns about a ballooning worker without reading the worker's output.
#
# Facts this depends on (probed 2026-11-03, see the plan):
#   - inside a subagent the hook input carries agent_id + agent_type, but
#     transcript_path is the PARENT's transcript; the agent's own transcript is
#     <dir of transcript_path>/<session_id>/subagents/agent-<agent_id>.jsonl ;
#   - scratchpad_dir is the session's scratchpad, the same for every agent;
#   - real records put "message"/"usage" BEFORE the record's own "type", so the
#     usage lookup never greps for an ordered pair.
#
# Prints NOTHING on stdout (zero context cost for the agent) and always exits 0.
# Thresholds: CLAUDE_TELEMETRY_STEPS (tokens, space-separated).
# Override:   CLAUDE_TELEMETRY_OFF=1.   Tests: context-telemetry.test.sh
set -u
[ "${CLAUDE_TELEMETRY_OFF:-}" = "1" ] && exit 0
STEPS=${CLAUDE_TELEMETRY_STEPS:-"150000 300000 450000 600000 750000"}

input=$(cat) || exit 0
# Unit separator, NOT tab: tab is IFS-whitespace, so `read` would collapse the
# empty agent_id/agent_type of a main-session call and shift every later field.
IFS=$'\x1f' read -r session tpath agent atype tool scratch < <(printf '%s' "$input" | jq -r '
  [ (.session_id // ""), (.transcript_path // ""), (.agent_id // ""),
    (.agent_type // ""), (.tool_name // "?"), (.scratchpad_dir // "") ] | join("\u001f")' 2>/dev/null) || exit 0
[ -n "${session:-}" ] && [ -n "${tpath:-}" ] || exit 0

if [ -n "${agent:-}" ]; then
  transcript="$(dirname "$tpath")/$session/subagents/agent-$agent.jsonl"
  label="${atype:-agent}:${agent:0:7}"
  key="$agent"
else
  transcript="$tpath"; label="main"; key="main"
fi
[ -r "$transcript" ] || exit 0

dir="${scratch:-/tmp/claude-telemetry-$session}/telemetry"
mkdir -p "$dir" 2>/dev/null || exit 0
state="$dir/$key.state"

calls=0; last=0
[ -r "$state" ] && read -r calls last < "$state" 2>/dev/null
calls=$(( ${calls:-0} + 1 )); last=${last:-0}

ctx=$(tac "$transcript" 2>/dev/null | grep '"usage"' | head -n 50 |
      jq -r 'select(.type=="assistant" and .message.usage != null) |
             (.message.usage.input_tokens // 0) + (.message.usage.cache_creation_input_tokens // 0)
             + (.message.usage.cache_read_input_tokens // 0)' 2>/dev/null | head -n 1)
case "${ctx:-}" in ''|*[!0-9]*) printf '%s %s\n' "$calls" "$last" > "$state" 2>/dev/null; exit 0 ;; esac

crossed=0
for s in $STEPS; do
  [ "$ctx" -ge "$s" ] && [ "$s" -gt "$last" ] && crossed=$s
done
if [ "$crossed" -gt 0 ]; then
  if [ -n "${agent:-}" ] && [ "$last" -eq 0 ]; then
    desc=$(jq -r '.description // empty' "${transcript%.jsonl}.meta.json" 2>/dev/null | head -c 60)
    [ -n "$desc" ] && label="$label \"$desc\""
  fi
  printf '%s | %s | ctx %dk (crossed %dk) | calls %d | %s\n' \
    "$(date +%Y-%m-%dT%H:%M:%S)" "$label" $(( ctx / 1000 )) $(( crossed / 1000 )) "$calls" "$tool" \
    >> "$dir/events.log" 2>/dev/null
  last=$crossed
fi
printf '%s %s\n' "$calls" "$last" > "$state" 2>/dev/null
exit 0
