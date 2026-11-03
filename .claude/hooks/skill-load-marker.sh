#!/usr/bin/env bash
# PreToolUse(Skill): records that ANY skill was invoked this session.
#
# Pure bookkeeping -- never blocks, never emits context, always exits 0. A hook
# has no built-in way to ask "was skill X loaded this session?", so guards read
# the markers this drops.
#
# Deliberately SEPARATE from meta-skill-marker.sh rather than widening it: that
# one is load-bearing for skill-edit-guard.sh, and breaking it would block all
# skill authoring. Two small hooks on the same matcher beat one clever one.
#
# Marker path: ${TMPDIR:-/tmp}/claude-skillload-<skill-slug>-<session-id>[_<agent-id>]
# Consumers:   skill-path-guard.sh, phase-check-guard.sh, git-workflow-guard.sh
set -u

input=$(cat)

skill=$(printf '%s' "$input" | jq -r '.tool_input.skill // ""' 2>/dev/null) || exit 0
[ -n "$skill" ] || exit 0

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession
# Per-AGENT key (PLAN-context-economy Phase 2, Emiel 2026-11-03): a subagent's
# hook input carries the PARENT's session_id, so without this a skill the
# coordinator loaded would satisfy a worker that never loaded it. Main session
# (no agent_id) keeps the plain sid. Same 3 lines in skill-load-marker.sh,
# skill-path-guard.sh, phase-check-guard.sh, git-workflow-guard.sh -- keep equal.
aid=$(printf '%s' "$input" | jq -r '.agent_id // ""' 2>/dev/null) || aid=
aid=${aid//[^A-Za-z0-9_-]/}
sid=${sid}${aid:+_$aid}

# Slugify: plugin skills arrive as `plugin:skill`, scoped ones as `dir:skill`.
slug=${skill//[^A-Za-z0-9_-]/-}

dir="${TMPDIR:-/tmp}"
: > "${dir}/claude-skillload-${slug}-${sid}" 2>/dev/null || true

exit 0
