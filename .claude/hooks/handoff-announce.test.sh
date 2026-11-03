#!/usr/bin/env bash
# Offline tests for handoff-announce.sh.
H=/home/emiel/Documents/katamaran/.claude/hooks/handoff-announce.sh
R=$(mktemp -d); mkdir -p "$R/.claude/plans"; echo '# plan' > "$R/.claude/plans/PLAN-x.md"
unset CLAUDE_HANDOFF_ANNOUNCE_OFF
export CLAUDE_PROJECT_DIR=$R
pass=0; fail=0
t () { # $1 expect ANNOUNCE|STALE|SILENT, $2 label, $3 source
  local out got r
  out=$(jq -n --arg s "$3" '{source:$s,session_id:"s"}' | bash "$H" 2>/dev/null); rc=$?
  if [ -z "$out" ]; then got=SILENT
  elif printf '%s' "$out" | jq -e '.systemMessage|startswith("Pending")' >/dev/null 2>&1; then got=ANNOUNCE
  elif printf '%s' "$out" | jq -e '.systemMessage|startswith("Stale")' >/dev/null 2>&1; then got=STALE
  else got=BADJSON; fi
  if [ "$got" = "$1" ] && [ $rc -eq 0 ]; then r="ok  "; pass=$((pass+1)); else r="FAIL"; fail=$((fail+1)); fi
  printf '%s %-8s %s\n' "$r" "$got" "$2"
}
t SILENT   "no HANDOFF file"                      clear
echo ".claude/plans/PLAN-x.md | Execute PLAN-x Phase 2 | 2026-11-03 abc1234" > "$R/.claude/HANDOFF"
t ANNOUNCE "pointer + /clear"                     clear
t ANNOUNCE "pointer + fresh startup"              startup
t SILENT   "resume: session already knows"        resume
t SILENT   "compact: session already knows"       compact
printf '\n\n.claude/plans/PLAN-x.md | Execute PLAN-x Phase 3 | d c\n' > "$R/.claude/HANDOFF"
t ANNOUNCE "leading blank lines tolerated"        clear
echo ".claude/plans/PLAN-gone.md | Execute PLAN-gone Phase 1 | d c" > "$R/.claude/HANDOFF"
t STALE    "plan file missing -> stale, not announced" clear
echo "garbage without separators" > "$R/.claude/HANDOFF"
t SILENT   "malformed pointer"                    clear
: > "$R/.claude/HANDOFF"
t SILENT   "empty pointer"                        clear
echo ".claude/plans/PLAN-x.md | Execute PLAN-x Phase 2 | d c" > "$R/.claude/HANDOFF"
CLAUDE_HANDOFF_ANNOUNCE_OFF=1 t SILENT "override env" clear
printf 'not json' | bash "$H"; [ $? -eq 0 ] && { echo "ok   malformed input exits 0"; pass=$((pass+1)); } || { echo "FAIL malformed input"; fail=$((fail+1)); }
echo "--- sample ---"; jq -n '{source:"clear"}' | bash "$H" | jq .
echo "passed $pass, failed $fail"; [ $fail -eq 0 ]
