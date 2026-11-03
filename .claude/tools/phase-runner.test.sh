#!/usr/bin/env bash
# Offline tests for phase-runner.sh: a stub `claude` plays the headless session
# and rewrites .claude/HANDOFF according to a script of per-run actions.
RUNNER=/home/emiel/Documents/katamaran/.claude/tools/phase-runner.sh
export RUNNER_NOTIFY=0   # no desktop pop-ups from the tests
pass=0; fail=0
W=$(mktemp -d)
cat > "$W/claude" <<'EOF'
#!/usr/bin/env bash
# stub: action for run k = k-th word of $STUB_ACTIONS (last one repeats)
n=$(( $(cat "$STUB_DIR/count" 2>/dev/null || echo 0) + 1 )); echo $n > "$STUB_DIR/count"
set -- $STUB_ACTIONS; a=${!n:-${!#}}
printf '%s\n' "$*" >/dev/null
echo "{\"type\":\"system\",\"subtype\":\"init\",\"session_id\":\"sid-$n\"}"
P=.claude/HANDOFF; plan=.claude/plans/PLAN-x.md
case "$a" in
  advance) echo "$plan | Execute PLAN-x Phase $((n+1)) | d c$n" > $P ;;
  same)    : ;;
  need)    echo "$plan | Execute PLAN-x Phase $n | d c$n | NEEDS-EMIEL: which option?" > $P ;;
  finish)  rm -f $P ;;
  crash)   exit 1 ;;
esac
echo '{"type":"result","result":"RUN-END"}'
EOF
chmod +x "$W/claude"

# $1 expected stop-reason substring, $2 expected number of claude runs, $3 label,
# $4 STUB_ACTIONS, $5 initial pointer ('' = none), rest = runner args
t () {
  local want=$1 runs=$2 label=$3 acts=$4 init=$5; shift 5
  local R; R=$(mktemp -d); mkdir -p "$R/.claude/plans"; echo '# plan' > "$R/.claude/plans/PLAN-x.md"
  [ -n "$init" ] && echo "$init" > "$R/.claude/HANDOFF"
  out=$(cd "$R" && RUNNER_ROOT=$R CLAUDE_BIN=$W/claude STUB_DIR=$R STUB_ACTIONS=$acts bash "$RUNNER" "$@" 2>&1); rc=$?
  got=$(cat "$R/count" 2>/dev/null || echo 0)
  if printf '%s' "$out" | grep -qF -- "$want" && [ "$got" = "$runs" ] && [ $rc -eq 0 ]; then
    echo "ok   $label"; pass=$((pass+1))
  else
    echo "FAIL $label (runs=$got want $runs, rc=$rc)"; printf '%s\n' "$out" | sed 's/^/     /'; fail=$((fail+1))
  fi
  LAST=$R
}
P2=".claude/plans/PLAN-x.md | Execute PLAN-x Phase 2 | d c"
t "no pointer"            0 "no pointer: stop before any run"             advance ""
t "empty pointer"         0 "empty pointer"                               advance " "
t "stale pointer"         0 "plan file missing"                           advance ".claude/plans/PLAN-gone.md | Execute PLAN-gone Phase 1 | d c"
t "malformed"             0 "pointer without separators"                  advance "garbage"
t "NEEDS-EMIEL: which"    0 "NEEDS-EMIEL already set: no run"             advance "$P2 | NEEDS-EMIEL: which way?"
t "not 'Execute"          0 "start line must be Execute ..."              advance ".claude/plans/PLAN-x.md | do stuff | d c"
t "no pointer"            3 "advance, advance, finish: 3 runs, stop"      "advance advance finish" "$P2"
t "NEEDS-EMIEL: which"    2 "advance then question: stop after run 2"     "advance need"   "$P2"
t "no progress"           2 "unchanged twice: N=2 guard"                  "same"           "$P2"
t "no progress"           4 "same, advance, same, same: counter resets"   "same advance same same" "$P2"
t "no progress"           2 "crashing claude counts as no progress"       "crash"          "$P2"
RUNNER_RETRIES=3 t "no progress" 3 "RUNNER_RETRIES=3"                     "same"           "$P2"
t "--once"                1 "--once: exactly one run"                     advance          "$P2" --once
t "dry run"               0 "--dry-run starts nothing"                    advance          "$P2" --dry-run
# log bookkeeping, from the 3-run case
t "no pointer"            3 "(rerun for logs)"                            "advance advance finish" "$P2"
n=$(wc -l < "$LAST/.claude/runner-logs/runs.tsv"); s=$(cut -f2 "$LAST/.claude/runner-logs/runs.tsv" | tr '\n' ' ')
[ "$n" = 3 ] && [ "$s" = "sid-1 sid-2 sid-3 " ] && { echo "ok   runs.tsv: 3 rows with session ids"; pass=$((pass+1)); } || { echo "FAIL runs.tsv ($n rows: $s)"; fail=$((fail+1)); }
# lock: a second runner is refused while the first holds the lock
R=$(mktemp -d); mkdir -p "$R/.claude/runner-logs"
( flock 9; sleep 2 ) 9>"$R/.claude/runner-logs/.lock" &
sleep 0.3
RUNNER_ROOT=$R bash "$RUNNER" >/dev/null 2>&1; rc=$?
wait
[ $rc -eq 3 ] && { echo "ok   second runner refused (lock)"; pass=$((pass+1)); } || { echo "FAIL lock (rc=$rc)"; fail=$((fail+1)); }
bash "$RUNNER" --bogus >/dev/null 2>&1; [ $? -eq 2 ] && { echo "ok   unknown arg -> 2"; pass=$((pass+1)); } || { echo "FAIL unknown arg"; fail=$((fail+1)); }
echo "passed $pass, failed $fail"; [ $fail -eq 0 ]
