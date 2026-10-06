#!/usr/bin/env bash
# PreToolUse(Bash): closes skill-edit-guard.sh's blind spot.
#
# WHY THIS EXISTS. skill-edit-guard.sh matches Write|Edit only, so authoring a
# SKILL.md with a Bash heredoc (`cat > .../SKILL.md <<'EOF'`) walks straight
# past it. Found 2026-09-11 by doing exactly that -- while the session's own
# auto-mode reminder was actively steering file edits toward Bash, so this is
# the likely path, not an exotic one. The rule it enforces is unchanged and
# lives in CLAUDE.md's maintenance protocol; only the coverage is new.
#
# DELIBERATELY SEPARATE FILE. skill-edit-guard.sh is load-bearing -- a syntax
# error in it blocks all skill authoring. A bug in here can only affect Bash.
#
# THE HARD PART IS NOT FIRING ON READS. CLAUDE.md records four incidents of a
# guard matching text that merely MENTIONS its trigger. `cat`, `grep`, `ls`,
# `sed -n` over a SKILL.md must all sail through; only an actual WRITE whose
# TARGET is a SKILL.md may be denied. So we match write mechanisms against the
# path, never the bare path:
#     >  >>  tee  cp/mv (last arg)  sed -i  dd of=  python-with-a-write-mode
#
# KNOWN LIMIT, stated rather than papered over: a write through a shell
# variable (`f=.../SKILL.md; cat > "$f"`) is not detectable by inspection and
# is NOT caught. This raises the cost of bypassing from "accidental" to
# "deliberate", which is the honest claim; it is not airtight.
#
# Override: CLAUDE_SKILL_GUARD_OFF=1, shared with skill-edit-guard.sh on
# purpose -- one rule, one switch, settable only in Claude Code's own launch
# environment.
set -u

input=$(cat)

# Cheap prefilter: both tokens must be present before we do any real work.
case $input in
  *.claude/skills/*) ;;
  *) exit 0 ;;
esac
case $input in
  *SKILL.md*) ;;
  *) exit 0 ;;
esac

[ "${CLAUDE_SKILL_GUARD_OFF:-}" = "1" ] && exit 0

cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
[ -n "$cmd" ] || exit 0

# A path that is a SKILL.md under .claude/skills/. Kept as one fragment so the
# write-mechanism patterns below can all anchor on the same thing.
P='[^[:space:]|;&)]*\.claude/skills/[^[:space:]|;&)]*SKILL\.md'

writes=no
# redirection INTO a SKILL.md (the heredoc case, and plain `echo x > f`)
printf '%s' "$cmd" | grep -Eq ">>?[[:space:]]*[\"']?${P}"            && writes=yes
# tee
printf '%s' "$cmd" | grep -Eq "\btee\b([[:space:]]+-[^[:space:]]+)*[[:space:]]+[\"']?${P}" && writes=yes
# in-place sed / perl
printf '%s' "$cmd" | grep -Eq "\bsed\b[^|;&]*[[:space:]]-i[^[:space:]]*[^|;&]*${P}" && writes=yes
printf '%s' "$cmd" | grep -Eq "\bperl\b[^|;&]*[[:space:]]-i[^|;&]*${P}"   && writes=yes
# dd
printf '%s' "$cmd" | grep -Eq "\bof=[\"']?${P}"                      && writes=yes
# cp / mv with a SKILL.md destination (last positional arg)
printf '%s' "$cmd" | grep -Eq "\b(cp|mv|install)\b[^|;&]*[[:space:]][\"']?${P}[\"']?[[:space:]]*(\$|[|;&])" && writes=yes
# an interpreter that both names a SKILL.md and opens something for writing
if printf '%s' "$cmd" | grep -Eq "\b(python3?|perl|ruby|node)\b"; then
  if printf '%s' "$cmd" | grep -Eq "${P}" \
     && printf '%s' "$cmd" | grep -Eq "(['\"]w['\"]|\.write\(|writelines|writeFileSync|>>?[[:space:]]*open)"; then
    writes=yes
  fi
fi

[ "$writes" = "yes" ] || exit 0

# Which requirement? Mirror skill-edit-guard.sh's own split: a SKILL.md that
# does not exist yet is AUTHORING (skill-creator); one that does exist is a
# rewrite, and a rewrite that carries a `description:` reshapes routing
# (skill-routing-maintenance). A body-only rewrite stays ungated, exactly as an
# Edit of the body would be.
target=$(printf '%s' "$cmd" | grep -Eo "$P" | head -1)
sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession
dir="${TMPDIR:-/tmp}"

deny() {
  jq -n --arg r "$1" '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}'
  exit 0
}

if [ -n "$target" ] && [ ! -e "$target" ]; then
  [ -e "${dir}/claude-metaskill-creator-${sid}" ] && exit 0
  deny "BLOCKED by skill-bash-write-guard: authoring a new SKILL.md via Bash without consulting skill-creator first.

This is the same rule skill-edit-guard.sh applies to the Write tool -- CLAUDE.md's maintenance protocol routes skill authoring through skill-creator. Reaching for a heredoc instead of Write does not change the rule; it only used to evade the check.

Do this instead: invoke skill-creator (Skill tool), then retry.

Target: ${target}"
fi

if printf '%s' "$cmd" | grep -q "description:"; then
  [ -e "${dir}/claude-metaskill-routing-${sid}" ] && exit 0
  deny "BLOCKED by skill-bash-write-guard: rewriting a SKILL.md that carries a \`description:\` without consulting skill-routing-maintenance.

A description change reshapes routing for the WHOLE skill family -- it can silently steal queries from, or stop competing with, a neighbouring skill.

Do this instead: invoke skill-routing-maintenance (Skill tool), then retry. If you only meant to change the BODY, narrow the write so it does not rewrite the frontmatter -- body edits are ungated.

Target: ${target:-a SKILL.md}"
fi

exit 0
