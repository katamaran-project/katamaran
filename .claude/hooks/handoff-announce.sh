#!/usr/bin/env bash
# SessionStart: announce a pending phase handoff written by /handoff.
# PLAN-context-economy D11:  /handoff  ->  /clear  ->  (this hook)  ->  "go".
#
# .claude/HANDOFF holds ONE line:   <plan path> | <start line> | <date> <commit> [| NEEDS-EMIEL: <question>]
# e.g.  .claude/plans/PLAN-context-economy.md | Execute PLAN-context-economy Phase 2 | 2026-11-03 abc1234
# The optional 4th field (D13) marks a phase blocked on Emiel's answer; it is
# what stops phase-runner.sh, and here it is shown as the question to ask first.
#
# Fires on source=startup|clear only (resume/compact continue an existing
# session, which already knows). Shows the user a one-line systemMessage and
# gives the model additionalContext telling it to read ONLY the plan's handoff
# section if the user says go. Silent when there is no pointer. Never blocks;
# any error -> exit 0 silently. Override: CLAUDE_HANDOFF_ANNOUNCE_OFF=1.
# Tests: handoff-announce.test.sh
set -u
[ "${CLAUDE_HANDOFF_ANNOUNCE_OFF:-}" = "1" ] && exit 0

input=$(cat) || exit 0
source=$(printf '%s' "$input" | jq -r '.source // "startup"' 2>/dev/null) || exit 0
case "$source" in startup|clear) ;; *) exit 0 ;; esac
cwd=$(printf '%s' "$input" | jq -r '.cwd // empty' 2>/dev/null)
root=${CLAUDE_PROJECT_DIR:-${cwd:-.}}

f="$root/.claude/HANDOFF"
[ -r "$f" ] || exit 0
line=$(grep -m1 -v '^[[:space:]]*$' "$f" 2>/dev/null) || exit 0
[ -n "$line" ] || exit 0

plan=$(printf '%s' "$line" | awk -F' [|] ' '{print $1}')
start=$(printf '%s' "$line" | awk -F' [|] ' '{print $2}')
stamp=$(printf '%s' "$line" | awk -F' [|] ' '{print $3}')
need=$(printf '%s' "$line" | awk -F' [|] ' '{print $4}')
case "$need" in NEEDS-EMIEL:*) q=${need#NEEDS-EMIEL:}; q=${q# } ;; *) q= ;; esac
[ -n "$plan" ] && [ -n "$start" ] || exit 0

if [ -r "$root/$plan" ] && [ -n "$q" ]; then
  msg="Pending handoff BLOCKED on your answer: $q  ($start, $plan, $stamp)."
  ctx="PENDING HANDOFF from .claude/HANDOFF (written $stamp): \"$start\", plan $plan -- BLOCKED on a question for Emiel: \"$q\". The phase-runner stopped on it. If the user answers it or says go: read the plan's status line and Handoff section (the question's context is there), record his answer as a decision in the plan, remove the NEEDS-EMIEL field from .claude/HANDOFF, then execute the start line. If the user asks for something else, ignore this."
elif [ -r "$root/$plan" ]; then
  msg="Pending handoff: $start  ($plan, $stamp). Reply \"go\" to start it."
  ctx="PENDING HANDOFF from .claude/HANDOFF (written $stamp): \"$start\". Plan: $plan. If the user replies \"go\" (or similar), execute exactly that: read the plan's status line and its Handoff section, plus only what that section names -- not the whole plan history. If the user asks for something else, ignore this. When the phase ends, suggest /handoff to the user (it is user-invoked; you cannot run it)."
else
  msg="Stale handoff pointer: $plan not found (.claude/HANDOFF). Overwrite it with /handoff or delete it."
  ctx="STALE .claude/HANDOFF: it names $plan, which does not exist. Mention this once if relevant; do not act on it."
fi
jq -n --arg m "$msg" --arg c "$ctx" \
  '{systemMessage:$m, hookSpecificOutput:{hookEventName:"SessionStart", additionalContext:$c}}'
exit 0
