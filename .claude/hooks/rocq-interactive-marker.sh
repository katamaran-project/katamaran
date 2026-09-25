#!/usr/bin/env bash
# PreToolUse(mcp__rocq-mcp__rocq_check|rocq_start|rocq_step_multi):
# records that the proof state was checked INTERACTIVELY, and when.
#
# Pure bookkeeping -- never blocks, never emits context, always exits 0. Its
# only job is to drop a timestamp that coqc-guard.sh reads, because a
# PreToolUse(Bash) hook cannot otherwise see that an MCP tool was used.
#
# WHY IT EXISTS (2026-08-16).  coqc-guard.sh originally rate-limited builds
# per rolling window.  That axis cannot see the loop it was written to stop:
# a `theories/Symbolic/Solver.v` build takes ~5-6 min, so at most 2-3 fit in
# the 15-minute window and the cap is never reached -- THE SLOWER THE FILE,
# THE MORE INVISIBLE THE LOOP.  Six consecutive full Solver.v rebuilds were
# burned that day fixing two tactic names, with the guard silent throughout.
#
# The condition that actually distinguishes a tweak loop from legitimate
# verification is not frequency but: "was the change checked interactively
# before compiling the whole file?"  This marker is what lets the guard ask
# that.  See coqc-guard.sh's SAME-TARGET rule.
#
# Pairs with .claude/hooks/coqc-guard.sh -- if you delete one, delete both,
# or the guard's same-target rule can never be satisfied and repeat builds
# become permanently blocked.
set -u

input=$(cat)

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
dir="${TMPDIR:-/tmp}"

# Timestamp, not just existence: the guard needs to know whether the check
# came BEFORE or AFTER the previous build of the same target.  NANOSECONDS,
# not seconds: a check issued in the same second as the preceding build read
# as "not after it" and produced a false denial (caught by the guard's own
# test, case 3).
# PER-TARGET (2026-09-09).  The marker used to be one file per SESSION, so a
# single interactive check -- on anything at all, even an unrelated scratch
# lemma -- satisfied the guard's same-target rule for every later build for the
# rest of the session.  Observed doing exactly that: one preamble-mode check of
# some bitvector arithmetic authorised a dozen later full compiles of an
# unrelated file.
#
# So: when the call NAMES a file (rocq_start(file=...), rocq_compile_file), the
# marker is keyed to that file and authorises only it.  Preamble-mode work and
# `rocq_check(from_state=...)` name no file -- the hook cannot know which target
# they are about -- so they write a CONSUME-ON-USE marker good for ONE build,
# which keeps preamble mode usable (it is the recommended workflow) without
# letting it unlock everything.
tgt=$(printf '%s' "$input" | jq -r '.tool_input.file // ""' 2>/dev/null) || tgt=""
tgt=${tgt#./}
now_ns=$(date +%s%N)

# CANONICAL PATH, NOT THE SPELLING (2026-09-24).  The key used to be the cksum
# of the string exactly as the tool received it, while coqc-guard.sh hashed the
# target exactly as the BUILD COMMAND spelled it.  So a check via an absolute
# path (`rocq_start(file="/home/.../X.v")`) and a build via a relative one
# (`coqc case_study/.../X.v`) produced different keys, and the check could
# never authorise the build: three false denials in a row on a file that had
# been checked twice.  Both hooks now hash `canon_path`'s output, and the two
# copies of the function MUST stay identical -- if they drift, this exact bug
# comes back silently.  A relative path is resolved against the session cwd
# first (where rocq-mcp resolves it), then the project root.
canon_path() {
  _p=$1; shift
  case $_p in
    /*) realpath -m -- "$_p" 2>/dev/null || printf '%s' "$_p"; return ;;
  esac
  for _b in "$@"; do
    [ -n "$_b" ] || continue
    if [ -e "$_b/$_p" ]; then realpath -m -- "$_b/$_p" 2>/dev/null; return; fi
  done
  realpath -m -- "${1:-$PWD}/$_p" 2>/dev/null || printf '%s' "$_p"
}
if [ -n "$tgt" ]; then
  _cwd=$(printf '%s' "$input" | jq -r '.cwd // ""' 2>/dev/null) || _cwd=""
  tgt=$(canon_path "$tgt" "$_cwd" "${CLAUDE_PROJECT_DIR:-}" "$PWD")
fi

if [ -n "$tgt" ]; then
  k=$(printf '%s' "$tgt" | cksum | cut -d' ' -f1)
  printf '%s\n' "$now_ns" > "${dir}/claude-rocq-interactive-${sid:-nosession}-${k}" 2>/dev/null || true
else
  printf '%s\n' "$now_ns" > "${dir}/claude-rocq-interactive-${sid:-nosession}-any" 2>/dev/null || true
fi

exit 0
