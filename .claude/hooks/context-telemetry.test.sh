#!/usr/bin/env bash
# Offline tests for context-telemetry.sh: fake transcripts, no API calls.
H=/home/emiel/Documents/katamaran/.claude/hooks/context-telemetry.sh
T=$(mktemp -d); unset CLAUDE_TELEMETRY_OFF CLAUDE_TELEMETRY_STEPS
pass=0; fail=0
S=sess1; P=$T/proj; SC=$T/scratch; mkdir -p "$P/$S/subagents" "$SC"
LOG=$SC/telemetry/events.log

asst () { # $1 context tokens. Real key order: message/usage BEFORE "type".
  jq -cn --argjson c "$1" '{parentUuid:"p",message:{type:"message",role:"assistant",usage:{input_tokens:2,cache_creation_input_tokens:0,cache_read_input_tokens:($c-2)}},type:"assistant",uuid:"u",timestamp:"2026-11-03T10:00:00.000Z"}'
}
setmain () { asst "$1" >> "$P/$S.jsonl"; }
setsub ()  { asst "$1" >> "$P/$S/subagents/agent-$2.jsonl"; }
call () { # $1 agent id or "", $2 tool ; captures stdout to check silence
  local j
  if [ -n "$1" ]; then
    j=$(jq -n --arg s $S --arg t "$P/$S.jsonl" --arg a "$1" --arg sc "$SC" --arg tool "$2" \
      '{session_id:$s,transcript_path:$t,agent_id:$a,agent_type:"phase-worker",tool_name:$tool,scratchpad_dir:$sc}')
  else
    j=$(jq -n --arg s $S --arg t "$P/$S.jsonl" --arg sc "$SC" --arg tool "$2" \
      '{session_id:$s,transcript_path:$t,tool_name:$tool,scratchpad_dir:$sc}')
  fi
  out=$(printf '%s' "$j" | bash "$H"); rc=$?
  [ -z "$out" ] && [ $rc -eq 0 ] || { echo "FAIL hook printed or failed: rc=$rc out=$out"; fail=$((fail+1)); }
}
lines () { [ -r "$LOG" ] && wc -l < "$LOG" || echo 0; }
check () { # $1 label, $2 expected line count, $3 optional grep on last line
  local n; n=$(lines)
  if [ "$n" -eq "$2" ] && { [ -z "${3:-}" ] || tail -1 "$LOG" | grep -q -- "$3"; }; then
    echo "ok   $1"; pass=$((pass+1)); else echo "FAIL $1 (lines=$n, last: $(tail -1 "$LOG" 2>/dev/null))"; fail=$((fail+1)); fi
}

setmain 100000; call "" Bash;                       check "main under 150k: silent" 0
setmain 160000; call "" Read;                       check "main crosses 150k: one line" 1 "main | ctx 160k (crossed 150k)"
setmain 170000; call "" Bash;                       check "main still 150-300k: no repeat" 1
setmain 470000; call "" Bash;                       check "jump over two steps: ONE line, highest step" 2 "crossed 450k"
echo '{"description":"Phase 2 of PLAN-x"}' > "$P/$S/subagents/agent-abc1234def.meta.json"
setsub 50000 abc1234def; call abc1234def mcp__rocq-mcp__rocq_check; check "subagent reads ITS OWN transcript (50k, parent 470k): silent" 2
setsub 310000 abc1234def; call abc1234def Bash;     check "subagent crosses 300k: labelled + described" 3 'phase-worker:abc1234 "Phase 2 of PLAN-x" | ctx 310k (crossed 300k) | calls 2 | Bash'
setsub 320000 abc1234def; call abc1234def Bash;     check "subagent no repeat" 3
setmain 480000; call "" Bash;                       check "main state independent of subagent" 3
call ghost Bash;                                    check "subagent without transcript: silent" 3
CLAUDE_TELEMETRY_OFF=1 bash -c "setmain() { :; }; true"; setmain 800000; CLAUDE_TELEMETRY_OFF=1 call "" Bash; check "override env: silent" 3
CLAUDE_TELEMETRY_STEPS="900000" call "" Bash;       check "custom steps respected (800k < 900k)" 3
printf 'garbage\n' >> "$P/$S.jsonl"; call "" Bash;  check "garbage last line: falls back to last real record" 4 "crossed 750k"
printf 'not json' | bash "$H"; [ $? -eq 0 ] && { echo "ok   malformed input exits 0"; pass=$((pass+1)); } || { echo "FAIL malformed input"; fail=$((fail+1)); }
echo "--- log ---"; cat "$LOG"
echo "passed $pass, failed $fail"; [ $fail -eq 0 ]
