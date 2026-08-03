#!/usr/bin/env bash
# PreToolUse(Read|Grep) ADVISORY hook: load the relevant skill before
# hand-reading Katamaran source.  Never blocks -- always exits 0.
#
# Fires AT MOST ONCE PER SESSION.  A per-call reminder on every .v Read would
# become noise and get tuned out, which is how previous always-on config in
# this repo ended up removed.  The once-per-session state is a marker file in
# $TMPDIR keyed by the hook payload's session_id -- deliberately NOT inside the
# repo, so this leaves no tracked debris.
#
# Added 2026-07-28 after a skill-usage audit found a whole session that made
# ZERO Skill calls and re-derived content already written in cfgver-solve-vc,
# secret-data-walls, and bv-pitfalls.
#
# To remove: delete this file AND the PreToolUse/Read|Grep entry in
# .claude/settings.json.  Stale markers are harmless and cleaned by the OS.
set -u

input=$(cat)

# Cheap pure-bash prefilter before spawning jq.
case $input in
  *theories/*|*CFGVer/*) ;;
  *) exit 0 ;;
esac

path=$(printf '%s' "$input" | jq -r '.tool_input.file_path // .tool_input.path // ""' 2>/dev/null) || exit 0
case $path in
  *theories/*|*case_study/RiscvPmp/CFGVer/*) ;;
  *) exit 0 ;;
esac

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
# strip anything that is not filename-safe
sid=${sid//[^A-Za-z0-9_-]/}
marker="${TMPDIR:-/tmp}/claude-cfgver-skill-nudge-${sid:-nosession}"

if [ -e "$marker" ]; then
  exit 0
fi
: > "$marker" 2>/dev/null || true

msg='Skill reminder (ADVISORY, once per session). You are about to hand-read Katamaran source. Load the relevant skill FIRST -- it is usually already written.

Skills here are TWO-TIERED. Pick ONE tier-1 entry point; it routes onward. Do not
try to pick a pitfall/library skill directly -- most are listed name-only (no
description) precisely so they stop competing for this decision:

  - about to write, repair, or iterate on any Rocq PROOF SCRIPT / tactic block
      -> rocq-implementation
      (owns the rocq-mcp preamble-mode workflow, and routes to bv-pitfalls,
       rocq-pitfalls, iris-proofmode, relval-model, core-executor-internals,
       cfgver-rsolve, cfgver-wp2 and the two -internals skills)
  - verifying a new program end-to-end        -> cfgver-new-example
  - VC residuals / solve_vc / bare False      -> cfgver-solve-vc
  - NonSyncVal => False walls, relop-vs-secLeak -> secret-data-walls
  - gmap lookups that will not reduce         -> gmap-pitfalls
  - compile far slower than its own history   -> rocq-timeout-triage
  - compile silently KILLED (Terminated/143)  -> rocq-compile-oom
  - unsure, or the request spans layers       -> cfgver (hub)

Why this fires: on 2026-07-28 a full session ran start to finish with ZERO Skill calls and re-derived, by hand, facts already documented in cfgver-solve-vc (the relval_fetch_* per-fetch residual lemmas and solve_symbase_fetch), secret-data-walls (formula_relop maps NonSyncVal to False), and bv-pitfalls (the lia atom-mismatch trap). Reading source is fine -- reading it INSTEAD of the skill is the mistake.'

jq -n --arg m "$msg" \
  '{hookSpecificOutput:{hookEventName:"PreToolUse",additionalContext:$m}}'
exit 0
