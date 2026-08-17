#!/usr/bin/env bash
# PreToolUse(Write|Edit): BLOCKING gate requiring the right skill to be loaded
# before Rocq source is written.
#
# WHY THIS EXISTS. Advisory nudging does not work. `skill-nudge.sh` fired early
# in the 2026-08-17 session, was read, and the session still hand-derived
# material that `core-executor-internals` documents -- while editing the very
# file that skill covers, with the skill named in a routing table that had just
# been read. Two data points now (2026-07-28 zero-Skill-calls; 2026-08-17) both
# say the same thing: only DENY changes behaviour. Advisory hooks are decoration.
#
# Two rules, cheapest first:
#
#   1. ANY *.v write/edit            -> requires `rocq-implementation`
#      SESSION-SCOPED, so this costs exactly one denial per session that touches
#      Rocq source, and every later .v write passes. rocq-implementation is the
#      tier-1 entry point and carries the rocq-mcp preamble-mode workflow that
#      coqc-guard.sh separately enforces -- so loading it early is what makes
#      that other gate survivable.
#
#   2. The CORE executor/solver files -> ALSO requires `core-executor-internals`
#      Those are `theories/Symbolic/{Solver,Monads}.v` and
#      `theories/MicroSail/SymbolicExecutor.v`. That skill is tier-2 (listed
#      name-only, so it never competes for routing) and holds both the
#      assert-vs-path-condition machinery and the "Adding a NEW solver rule"
#      recipe. It is the specific skill that was missed on 2026-08-17.
#
# Scope notes:
#   - Only *.v. Editing .md/.sh/.json is not our business.
#   - Fires on the FIRST write only (the marker makes it self-clearing), so a
#     long editing session is not nagged.
#   - A denial names the exact Skill call to make, so the recovery is one step.
#
# Override is deliberately NOT something the assistant can arrange: set
# CLAUDE_V_GUARD_OFF=1 in the environment Claude Code itself was launched with,
# or toggle the hook off in /hooks. A Bash call from inside a session cannot
# change the parent process's environment.
set -u

input=$(cat)

# Cheap prefilter before spawning jq: bail unless a .v path is plausibly present.
case $input in
  *.v*) ;;
  *) exit 0 ;;
esac

if [ "${CLAUDE_V_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi

path=$(printf '%s' "$input" | jq -r '.tool_input.file_path // ""' 2>/dev/null) || exit 0
case $path in
  *.v) ;;
  *) exit 0 ;;
esac

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession
dir="${TMPDIR:-/tmp}"

deny() {
  jq -n --arg r "$1" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "deny",
      permissionDecisionReason: $r
    }
  }'
  exit 0
}

loaded() { [ -e "${dir}/claude-skillload-${1}-${sid}" ]; }

# ---- rule 2 first: it is the more specific requirement -----------------------
case $path in
  */theories/Symbolic/Solver.v|*/theories/Symbolic/Monads.v|*/theories/MicroSail/SymbolicExecutor.v)
    if ! loaded core-executor-internals; then
      deny "BLOCKED by v-write-guard: editing the CORE executor/solver without loading core-executor-internals.

${path}

That skill is tier-2 (listed name-only, so it never wins routing on its own) and it holds exactly what this file needs: how an \`assert\` is discharged against the path condition (solver_generic's stages, the wco walk, the wpathcondition world-extension), AND the \"Adding a NEW solver rule\" recipe -- where to hook, why returning \`error\` for \"cannot decide\" is unsoundness that does NOT fail the build, whether your rule needs a secLeakT guard, the Equations two-type-index refusal, and the iteration order that keeps you off ~6-minute rebuilds.

On 2026-08-17 a session edited this file without it, re-derived part of it from source by hand, and burned two ~6-minute builds on a trap the recipe now documents. That is why this is a deny and not a nudge.

Do this: invoke core-executor-internals (Skill tool), then retry."
    fi
    ;;
esac

# ---- rule 1: any .v at all ---------------------------------------------------
if ! loaded rocq-implementation; then
  deny "BLOCKED by v-write-guard: writing Rocq source without loading rocq-implementation first.

${path}

rocq-implementation is the tier-1 entry point for writing/repairing a proof in this repo. Load it BEFORE the first attempt, not after something fails: it carries the rocq-mcp preamble-mode workflow (which coqc-guard.sh separately enforces, so knowing it early is what makes that gate survivable), and it is the ONLY route to the tier-2 library skills -- bv-pitfalls, rocq-pitfalls, iris-proofmode, core-executor-internals, relval-model, cfgver-rsolve, cfgver-wp2 and the two -internals skills are listed WITHOUT descriptions, so nothing else will surface them.

This fires ONCE per session: after the Skill call, every later .v write passes.

Do this: invoke rocq-implementation (Skill tool), then retry.

If this is a throwaway ZZ*.v probe or a pure data/comment edit, load it anyway -- it is one call, and the traps it routes to are ones you cannot recognise from the goal alone."
fi

exit 0
