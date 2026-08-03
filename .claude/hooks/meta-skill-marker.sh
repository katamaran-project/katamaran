#!/usr/bin/env bash
# PreToolUse(Skill): records that a meta-skill was consulted this session.
#
# Pure bookkeeping -- never blocks, never emits context, always exits 0. Its only
# job is to drop a marker that skill-edit-guard.sh looks for, because a hook has
# no built-in way to ask "was skill X loaded this session?".
#
# Pairs with .claude/hooks/skill-edit-guard.sh -- if you delete one, delete both,
# or skill edits become permanently blocked.
set -u

input=$(cat)

# Cheap prefilter: only two skill names matter here.
case $input in
  *skill-creator*|*skill-routing-maintenance*) ;;
  *) exit 0 ;;
esac

skill=$(printf '%s' "$input" | jq -r '.tool_input.skill // ""' 2>/dev/null) || exit 0
sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
dir="${TMPDIR:-/tmp}"

case $skill in
  *skill-creator*)
    : > "${dir}/claude-metaskill-creator-${sid:-nosession}" 2>/dev/null || true ;;
  *skill-routing-maintenance*)
    : > "${dir}/claude-metaskill-routing-${sid:-nosession}" 2>/dev/null || true ;;
esac

exit 0
