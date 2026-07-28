#!/usr/bin/env bash
# PreToolUse(Bash) ADVISORY hook: prefer rocq-mcp interactive iteration over a
# raw coqc loop.  Never blocks -- always exits 0 and never sets
# permissionDecision / continue:false.
#
# Added 2026-07-28 after a session spent three full ~5-min Symbolic/Solver.v
# compiles on two tactic errors that preamble mode found in 28 ms each.
#
# To remove: delete this file AND the PreToolUse/Bash entry in
# .claude/settings.json.  Nothing else references it.
set -u

input=$(cat)

# Cheap pure-bash prefilter: no subprocess for the vast majority of Bash calls.
case $input in
  *coqc*) ;;
  *) exit 0 ;;
esac

# Precise check on the actual command (the prefilter can match a path etc).
cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
case $cmd in
  *coqc*) ;;
  *) exit 0 ;;
esac

msg='rocq-mcp reminder (ADVISORY, not a block). Prefer interactive iteration over a raw coqc loop.

A rocq_start(theorem=...) TIMEOUT DOES NOT MEAN interactive mode is unavailable. rocq_start replays the whole file prefix, so it hits the 300s ROCQ_QUERY_TIMEOUT_CAP at deep positions in large theories/ files -- that is a property of that ONE mode, not of rocq-mcp.

Use instead: rocq_start(preamble="From Katamaran Require Import ...") + rocq_check. Imports are content-hash-cached and stay warm across iterations, so a tactic check costs ~30ms rather than ~5min.

Because the preamble carries no file context, restate the goal as a STANDALONE lemma. To get its exact shape, temporarily replace the proof with:
    match goal with |- ?G => idtac "ZZ:" G end. admit.
plus Admitted., run coqc in the BACKGROUND, and kill it as soon as ZZ: appears. Then port the verified tactic back and pay ONE full compile to confirm.

See the "Tooling gotchas" block in CLAUDE.md.

STILL LEGITIMATE uses of coqc, ignore this reminder for them: dumping a large term to a file via stdout redirect (rocq-mcp blocks Redirect), and a single final full-file confirmation compile.'

jq -n --arg m "$msg" \
  '{hookSpecificOutput:{hookEventName:"PreToolUse",additionalContext:$m}}'
exit 0
