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
#
# TWO INDEPENDENT MECHANISMS live here, in this order:
#   1. HARD DENY -- `main` is never a push or merge TARGET (2026-09-05, at the
#      user's instruction after a topic branch was pushed and the question came
#      up). This is NOT satisfiable by loading a skill, and it has its OWN
#      override (CLAUDE_ALLOW_MAIN=1) so that silencing the skill nag with
#      CLAUDE_GIT_GUARD_OFF=1 does not also unlock main. This repo's integration
#      branch is KatamaranRel; main is upstream and is never written to from
#      here.
#   2. SKILL GATE -- the pre-existing "load branch-workflow first" nag.
set -u

input=$(cat)

cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
[ -n "$cmd" ] || exit 0

# `git` as a command word: start of string, or after a shell separator.
gitre='(^|[;&|]|&&|\|\||^[[:space:]]*)[[:space:]]*git[[:space:]]'

deny () { # $1 = reason text
  jq -n --arg r "$1" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "deny",
      permissionDecisionReason: $r
    }
  }'
  exit 0
}

# ---------------------------------------------------------------------------
# 1. HARD DENY: main is never a push or merge target.
#
# Deliberately BIASED TOWARDS FALSE DENY, unlike mechanism 2 below -- a wrong
# allow here is an irreversible write to a shared upstream, a wrong deny costs
# one env var. Consequence: a branch literally named `<something>/main` reads as
# main and is refused. That is the intended trade.
# ---------------------------------------------------------------------------
if [ "${CLAUDE_ALLOW_MAIN:-}" != "1" ]; then
  head_branch=$(git symbolic-ref --quiet --short HEAD 2>/dev/null) || head_branch=""
  # `main` as a REF token: preceded by space, ':', '+' or '/', and ending the
  # token. Excludes `domain`, `main-fix`, `mainline`.
  mainre='(^|[[:space:]:+/])main([[:space:]:]|$)'
  why=""

  if printf '%s' "$cmd" | grep -Eq "${gitre}+push([[:space:]]|$)"; then
    if printf '%s' "$cmd" | grep -Eq "$mainre"; then
      why="a \`git push\` naming \`main\`"
    elif printf '%s' "$cmd" | grep -Eq '[[:space:]](--all|--mirror)([[:space:]]|$)'; then
      why="\`git push --all/--mirror\`, which would include \`main\`"
    elif [ "$head_branch" = "main" ]; then
      why="a bare \`git push\` while HEAD is \`main\`"
    fi
  fi

  if [ -z "$why" ] && printf '%s' "$cmd" | grep -Eq "${gitre}+merge([[:space:]]|$)"; then
    if [ "$head_branch" = "main" ]; then
      why="a \`git merge\` while HEAD is \`main\` -- that merges INTO main"
    fi
  fi

  if [ -n "$why" ]; then
    deny "BLOCKED by git-workflow-guard: main is never a push or merge target.

Refused: ${why}
Command: ${cmd}

This repo integrates on **KatamaranRel**, not main. main is upstream and is
never written to from here.

What to do instead:
  - landing work : merge the topic branch into KatamaranRel with --no-ff (that
                   is what fires scripts/gate.sh via the pre-merge-commit hook)
  - sharing work : push the TOPIC branch and open a PR
  - updating     : \`git merge main\` FROM a topic branch is fine and not gated

This deny cannot be satisfied by loading a skill. If it is genuinely wrong (a
branch whose name merely ends in /main, say), the user -- not a session -- can
set CLAUDE_ALLOW_MAIN=1 in the environment Claude Code is launched with."
  fi
fi

# ---------------------------------------------------------------------------
# 2. SKILL GATE (pre-existing): load branch-workflow before the gated ops.
# ---------------------------------------------------------------------------
if [ "${CLAUDE_GIT_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi
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
