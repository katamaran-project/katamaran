#!/usr/bin/env bash
# PreToolUse(Bash): BLOCKING gate requiring `branch-workflow` before the git
# operations that the merge-gate workflow governs.
#
# Gated: `git merge`, `git push`, `git checkout -b` / `git switch -c`.
# NOT gated: commit, status, log, diff, add, checkout of a path, stash --
# committing at milestones on a branch is rocq-checkpoint's business, and
# gating everyday git would be pure friction.
#
# Why these three: they are the moments the branch-workflow skill exists for --
# starting an issue on a short-lived topic branch, and landing it into a
# protected branch through scripts/gate.sh (which is wired as the
# pre-merge-commit hook and enforces the three things a green coqc does NOT:
# full build, no proof holes, axiom-clean end theorems).
#
# FALSE-POSITIVE DISCIPLINE. Matched against `.tool_input.command` ONLY, never
# the whole hook payload, and anchored on git as a command word. On 2026-08-17
# three separate guards misfired on text that merely MENTIONED their trigger --
# a case-insensitive `Error:` grep matching the printed lemma name
# `instpred_dlist_error:`, a `pgrep -f` loop matching its own command line, and
# the rocq plugin's guardrail blocking a `git ls-files` because an `echo` string
# contained the word "restore". Hence: no matching on prose, and a comment or a
# quoted string that happens to contain "git push" should not trip this. It is
# still a regex over a shell string, so it is not airtight -- prefer a false
# ALLOW to a false DENY here, since the gate protects a workflow, not soundness.
#
# Override is the user's: CLAUDE_GIT_GUARD_OFF=1 in the environment Claude Code
# was launched with.
set -u

input=$(cat)

if [ "${CLAUDE_GIT_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi

cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
[ -n "$cmd" ] || exit 0

# `git` as a command word: start of string, or after a shell separator.
gitre='(^|[;&|]|&&|\|\||^[[:space:]]*)[[:space:]]*git[[:space:]]'
op=""
if printf '%s' "$cmd" | grep -Eq "${gitre}+merge([[:space:]]|$)"; then op="git merge"; fi
if printf '%s' "$cmd" | grep -Eq "${gitre}+push([[:space:]]|$)"; then op="git push"; fi
if printf '%s' "$cmd" | grep -Eq "${gitre}+checkout[[:space:]]+(-[^[:space:]]*[[:space:]]+)*-b([[:space:]]|$)"; then op="git checkout -b"; fi
if printf '%s' "$cmd" | grep -Eq "${gitre}+switch[[:space:]]+(-[^[:space:]]*[[:space:]]+)*-c([[:space:]]|$)"; then op="git switch -c"; fi

[ -n "$op" ] || exit 0

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession
dir="${TMPDIR:-/tmp}"

[ -e "${dir}/claude-skillload-branch-workflow-${sid}" ] && exit 0

jq -n --arg r "BLOCKED by git-workflow-guard: \`${op}\` without loading branch-workflow.

Command: ${cmd}

branch-workflow carries this repo's actual landing procedure: work each issue on a short-lived topic branch, then merge into a protected branch (main / KatamaranRel) THROUGH scripts/gate.sh, which is wired as the pre-merge-commit git hook and enforces the three things a green \`coqc\` does NOT -- full build, no proof holes, and axiom-clean end theorems. It also covers how to (re)install the hook after a clone, why a merge was blocked, and how to add a new end theorem to the axiom-clean list.

Fires at most ONCE per session. Committing at milestones on a branch is NOT gated (that is rocq-checkpoint).

Do this: invoke branch-workflow (Skill tool), then retry." '{
  hookSpecificOutput: {
    hookEventName: "PreToolUse",
    permissionDecision: "deny",
    permissionDecisionReason: $r
  }
}'
exit 0
