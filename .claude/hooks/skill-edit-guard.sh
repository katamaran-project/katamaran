#!/usr/bin/env bash
# PreToolUse(Write|Edit): BLOCKING gate on skill authoring.
#
# CLAUDE.md's maintenance protocol requires routing through skill-creator before
# authoring a new SKILL.md, and through skill-routing-maintenance after any
# `description:` change (a description edit reshapes routing for the whole
# family). That rule was prose-only, and on 2026-07-28 it was bypassed anyway.
# This makes it enforced rather than advisory.
#
# Scope, deliberately narrow so it does not misfire:
#   - Write to a .claude/skills/**/SKILL.md        -> requires skill-creator
#   - Edit whose diff touches `description:`       -> requires skill-routing-maintenance
#   - Edit of a skill BODY only                    -> allowed, ungated (ordinary editing)
#   - anything outside .claude/skills/             -> allowed, not our business
#
# Override is deliberately NOT something the assistant can arrange: set
# CLAUDE_SKILL_GUARD_OFF=1 in the environment Claude Code itself was launched
# with, or toggle the hook off in /hooks. A Bash call from inside a session
# cannot change the parent process's environment.
set -u

input=$(cat)

# Cheap prefilter before spawning jq.
case $input in
  *.claude/skills/*) ;;
  *) exit 0 ;;
esac

if [ "${CLAUDE_SKILL_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi

path=$(printf '%s' "$input" | jq -r '.tool_input.file_path // ""' 2>/dev/null) || exit 0
case $path in
  *.claude/skills/*/SKILL.md) ;;
  *) exit 0 ;;
esac

tool=$(printf '%s' "$input" | jq -r '.tool_name // ""' 2>/dev/null) || exit 0
sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
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

if [ "$tool" = "Write" ]; then
  if [ ! -e "${dir}/claude-metaskill-creator-${sid:-nosession}" ]; then
    deny "BLOCKED by skill-edit-guard: writing a SKILL.md without consulting skill-creator first.

CLAUDE.md's maintenance protocol: authoring or splitting a skill routes through the skill-creator meta-skill FIRST, rather than hand-authoring ad-hoc. This exists because a 2026-07-20 session created, split and re-described skills directly, bypassing both meta-skills.

Do this instead: invoke skill-creator (Skill tool), then retry this Write. If you are editing an EXISTING skill's body, use Edit rather than Write -- body edits are ungated.

Path: ${path}"
  fi
  exit 0
fi

# Edit: only gate when the diff actually touches a description / frontmatter.
touches_desc=$(printf '%s' "$input" | jq -r '
  ((.tool_input.old_string // "") + "\n" + (.tool_input.new_string // ""))
  | if test("description:") then "yes" else "no" end' 2>/dev/null) || touches_desc=no

if [ "$touches_desc" = "yes" ]; then
  if [ ! -e "${dir}/claude-metaskill-routing-${sid:-nosession}" ]; then
    deny "BLOCKED by skill-edit-guard: editing a skill's \`description:\` without consulting skill-routing-maintenance.

A description change reshapes routing for the WHOLE skill family -- it can silently steal queries from, or stop competing with, a neighbouring skill. CLAUDE.md requires re-validation via skill-routing-maintenance for exactly this edit.

Do this instead: invoke skill-routing-maintenance (Skill tool) -- it carries the judge protocol, the routing-judge agent, and the cost arithmetic -- then retry this Edit.

Note: editing a skill's BODY is NOT gated. If you did not mean to touch the description, narrow your old_string/new_string to the body text.

Path: ${path}"
  fi
fi

exit 0
