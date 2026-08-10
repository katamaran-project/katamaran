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
# Matches raw `coqc` AND `make -f Makefile.coq` -- the latter is how this repo
# builds `Solver.v` specifically (rocq_compile_file can't; see the skill), so
# a prefilter that only caught literal `coqc` had a blind spot for exactly
# the file this hook exists to protect. Found 2026-08-07 after four ~6-minute
# `make -f Makefile.coq theories/Symbolic/Solver.vo` recompiles ran unwarned.
case $input in
  *coqc*|*Makefile.coq*) ;;
  *) exit 0 ;;
esac

# Precise check on the actual command (the prefilter can match a path etc).
cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
case $cmd in
  *coqc*|*Makefile.coq*) ;;
  *) exit 0 ;;
esac

msg='rocq-mcp reminder (ADVISORY, not a block). Prefer interactive iteration over a raw coqc/`make -f Makefile.coq` loop -- including for Symbolic/Solver.v, where `make -f Makefile.coq` (not plain coqc) is the documented way to build it, and this hook now catches that form too.

A rocq_start(theorem=...) TIMEOUT DOES NOT MEAN interactive mode is unavailable. rocq_start replays the whole file prefix, so it hits the 300s ROCQ_QUERY_TIMEOUT_CAP at deep positions in large theories/ files -- that is a property of that ONE mode, not of rocq-mcp.

Use instead: rocq_start(preamble="From Katamaran Require Import ...") + rocq_check. Imports are content-hash-cached and stay warm across iterations, so a tactic check costs ~30ms rather than ~5min.

Because the preamble carries no file context, restate the goal as a STANDALONE lemma. To get its exact shape, temporarily replace the proof with:
    match goal with |- ?G => idtac "ZZ:" G end. admit.
plus Admitted., run coqc in the BACKGROUND, and kill it as soon as ZZ: appears. Then port the verified tactic back and pay ONE full compile to confirm.

If what you are actually stuck on is NOT proof-content but a Coq MODULE-SYSTEM question (does a definition stay transparent through a functor parameter, does `cbn` fire through a class-method-then-Fixpoint dispatch chain, ...) -- that reproduces in a 10-line throwaway `Module`/`Module Type` snippet in a preamble in well under 100ms, independent of file size. Do not reach for a real-file recompile to answer a question a scratch snippet already answers faster.

Full detail: the rocq-implementation skill, section 1 ("Iterate with rocq-mcp, not with coqc").

STILL LEGITIMATE uses of a full build, ignore this reminder for them: dumping a large term to a file via stdout redirect (rocq-mcp blocks Redirect), and a single final full-file confirmation compile once the tactic script is already validated some other way.'

jq -n --arg m "$msg" \
  '{hookSpecificOutput:{hookEventName:"PreToolUse",additionalContext:$m}}'
exit 0
