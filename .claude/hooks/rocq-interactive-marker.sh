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
date +%s%N > "${dir}/claude-rocq-interactive-${sid:-nosession}" 2>/dev/null || true

exit 0
