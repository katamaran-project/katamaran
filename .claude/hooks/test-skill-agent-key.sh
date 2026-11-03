#!/usr/bin/env bash
# Offline tests for the PER-AGENT skill-load key (PLAN-context-economy Phase 2,
# Emiel 2026-11-03). A subagent's hook input carries the PARENT's session_id plus
# its own agent_id; a skill loaded by one agent must satisfy the guards for that
# agent only. Markers are written by the REAL skill-load-marker.sh, not by hand,
# so writer and readers are tested against each other.
D=/home/emiel/Documents/katamaran/.claude/hooks
export TMPDIR=$(mktemp -d)
unset CLAUDE_V_GUARD_OFF CLAUDE_PHASE_GUARD_OFF CLAUDE_GIT_GUARD_OFF
pass=0; fail=0
S=sess1

load () { # $1 skill, $2 agent_id ("" = main session)
  jq -n --arg k "$1" --arg s "$S" --arg a "$2" \
    '{tool_input:{skill:$k},session_id:$s} + (if $a=="" then {} else {agent_id:$a} end)' \
    | bash "$D/skill-load-marker.sh"
}

chk () { # $1 expect, $2 hook, $3 tool_input json, $4 agent_id, $5 label
  local out got r
  out=$(jq -n --argjson ti "$3" --arg s "$S" --arg a "$4" \
    '{tool_input:$ti,session_id:$s} + (if $a=="" then {} else {agent_id:$a} end)' \
    | bash "$D/$2" 2>/dev/null)
  if printf '%s' "$out" | grep -q '"deny"'; then got=DENY; else got=ALLOW; fi
  if [ "$got" = "$1" ]; then r="ok  "; pass=$((pass+1)); else r="FAIL"; fail=$((fail+1)); fi
  printf '%s %-5s %-22s %s\n' "$r" "$got" "$2" "$5"
}

V='{"file_path":"/k/theories/ZZFoo.v","content":"x"}'
P='{"command":"./scripts/gate.sh"}'
G='{"command":"git checkout -b issue/x"}'

echo "=== marker file names ==="
load rocq-implementation ""
load rocq-implementation "w-1"
for f in "claude-skillload-rocq-implementation-$S" "claude-skillload-rocq-implementation-${S}_w-1"; do
  if [ -e "$TMPDIR/$f" ]; then echo "ok   exists $f"; pass=$((pass+1)); else echo "FAIL missing $f"; fail=$((fail+1)); fi
done
rm -f "$TMPDIR"/claude-skillload-*

echo "=== coordinator's load does NOT cover a worker ==="
load rocq-implementation ""; load phase-check ""; load branch-workflow ""
chk ALLOW skill-path-guard.sh   "$V" ""    "main, own load"
chk DENY  skill-path-guard.sh   "$V" "w-1" "worker, main loaded"
chk ALLOW phase-check-guard.sh  "$P" ""    "main, own load"
chk DENY  phase-check-guard.sh  "$P" "w-1" "worker, main loaded"
chk ALLOW git-workflow-guard.sh "$G" ""    "main, own load"
chk DENY  git-workflow-guard.sh "$G" "w-1" "worker, main loaded"
rm -f "$TMPDIR"/claude-skillload-*

echo "=== a worker's load covers that worker only ==="
load rocq-implementation "w-1"; load phase-check "w-1"; load branch-workflow "w-1"
chk ALLOW skill-path-guard.sh   "$V" "w-1" "worker, own load"
chk DENY  skill-path-guard.sh   "$V" "w-2" "other worker"
chk DENY  skill-path-guard.sh   "$V" ""    "main, worker loaded"
chk ALLOW phase-check-guard.sh  "$P" "w-1" "worker, own load"
chk DENY  phase-check-guard.sh  "$P" ""    "main, worker loaded"
chk ALLOW git-workflow-guard.sh "$G" "w-1" "worker, own load"
chk DENY  git-workflow-guard.sh "$G" ""    "main, worker loaded"

echo "=== agent_id is sanitised like session_id ==="
rm -f "$TMPDIR"/claude-skillload-*
load rocq-implementation "a/../b"
chk ALLOW skill-path-guard.sh   "$V" "a/../b" "worker with odd id"
[ -z "$(find "$TMPDIR" -mindepth 2 -name 'claude-skillload-*')" ] && { echo "ok   no marker outside TMPDIR"; pass=$((pass+1)); } || { echo "FAIL path escape"; fail=$((fail+1)); }

echo; echo "pass=$pass fail=$fail"
rm -rf "$TMPDIR"
[ "$fail" -eq 0 ]
