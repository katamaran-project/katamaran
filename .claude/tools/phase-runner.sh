#!/usr/bin/env bash
# phase-runner.sh -- chain headless plan phases, one fresh `claude -p` session
# per run, driven by the pointer .claude/HANDOFF (PLAN-context-economy D12b, D13).
#
#   .claude/tools/phase-runner.sh [--once] [--dry-run]
#
# Pointer (written by /handoff or by a phase-worker at DONE / question-STUCK):
#   <plan path> | Execute <PLAN> Phase <N> | <date> <commit> [| NEEDS-EMIEL: <question>]
#
# Loop: read pointer -> STOP if absent, stale, or carrying NEEDS-EMIEL (D13: an
# open question or design choice is the ONLY stop rule) -> run ONE headless
# coordinator session with the start line -> re-read pointer -> repeat.
# No-progress guard (D13, Emiel): STOP when the pointer line is unchanged after
# RUNNER_RETRIES consecutive runs (default 2). No phase cap, no token budget:
# both were offered and NOT chosen. --once runs a single session (the benchmark
# mode: "benchmark ONE phase before chaining").
#
# Each run: the session runs as a COORDINATOR (system prompt
# phase-runner-coordinator.md) that drives a phase-worker subagent.
# Logs: .claude/runner-logs/<ts>.jsonl (stream-json), <ts>.err, runs.tsv
# (ts, session id, exit code, pointer before, pointer after). Measure a run
# with: python3 -I .claude/tools/transcript-usage.py <projdir> <session id>
#
# Env: CLAUDE_BIN (default claude; the tests stub it), RUNNER_RETRIES (2),
#      RUNNER_PERMISSION_MODE (auto), RUNNER_EXTRA_ARGS (word-split, appended),
#      RUNNER_NOTIFY (1 = desktop notification via notify-send on every stop).
# Tests: phase-runner.test.sh
set -u
once=0; dry=0
for a in "$@"; do
  case "$a" in
    --once) once=1 ;;
    --dry-run) dry=1 ;;
    -h|--help) sed -n '2,26p' "$0"; exit 0 ;;
    *) echo "phase-runner: unknown argument $a" >&2; exit 2 ;;
  esac
done

here=$(cd "$(dirname "$0")" && pwd)
root=${RUNNER_ROOT:-$(cd "$here/../.." && pwd)}
cd "$root" || exit 2
ptr=.claude/HANDOFF
coord="$here/phase-runner-coordinator.md"
logs=.claude/runner-logs
mkdir -p "$logs"
CLAUDE_BIN=${CLAUDE_BIN:-claude}
retries=${RUNNER_RETRIES:-2}
pmode=${RUNNER_PERMISSION_MODE:-auto}

# one runner at a time: two would race on the same working tree (D10)
exec 9>"$logs/.lock"
if ! flock -n 9; then echo "phase-runner: another runner holds $logs/.lock" >&2; exit 3; fi

stop () { # $1 reason
  local msg="phase-runner stopped: $1"
  echo "$msg"
  printf '%s\t%s\n' "$(date -Is)" "$1" >> "$logs/stops.log"
  [ "${RUNNER_NOTIFY:-1}" = 1 ] && command -v notify-send >/dev/null 2>&1 && notify-send "Claude phase runner" "$1" 2>/dev/null
  exit 0
}

read_ptr () { grep -m1 -v '^[[:space:]]*$' "$ptr" 2>/dev/null; }
field () { printf '%s' "$1" | awk -F' [|] ' -v n="$2" '{print $n}'; }

same=0
while :; do
  [ -r "$ptr" ] || stop "no pointer $ptr (plan finished, or nothing handed off)"
  line=$(read_ptr)
  [ -n "$line" ] || stop "empty pointer $ptr"
  plan=$(field "$line" 1); start=$(field "$line" 2); need=$(field "$line" 4)
  [ -n "$plan" ] && [ -n "$start" ] || stop "malformed pointer: $line"
  [ -r "$plan" ] || stop "stale pointer: $plan does not exist"
  case "$need" in NEEDS-EMIEL:*) stop "$start -- ${need}" ;; esac
  case "$start" in "Execute "*) ;; *) stop "start line is not 'Execute ...': $start" ;; esac

  ts=$(date +%Y%m%dT%H%M%S)
  echo "phase-runner: run $ts: $start"
  if [ "$dry" = 1 ]; then echo "phase-runner: dry run, not starting claude"; exit 0; fi
  # shellcheck disable=SC2086
  "$CLAUDE_BIN" -p "$start" --permission-mode "$pmode" \
      --output-format stream-json --verbose \
      --append-system-prompt "$(cat "$coord")" ${RUNNER_EXTRA_ARGS:-} \
      > "$logs/$ts.jsonl" 2> "$logs/$ts.err" < /dev/null
  rc=$?
  sid=$(head -c 200000 "$logs/$ts.jsonl" | jq -r 'select(.session_id) | .session_id' 2>/dev/null | head -1)
  after=$(read_ptr)
  printf '%s\t%s\t%s\t%s\t%s\n' "$ts" "${sid:--}" "$rc" "$line" "${after:--}" >> "$logs/runs.tsv"
  echo "phase-runner: run $ts ended rc=$rc session=${sid:--}"

  if [ "$after" = "$line" ]; then same=$((same+1)); else same=0; fi
  [ "$same" -ge "$retries" ] && stop "no progress: pointer unchanged after $same consecutive runs ($start); see $logs/runs.tsv"
  [ "$once" = 1 ] && stop "--once: single run done (rc=$rc, session ${sid:--})"
done
