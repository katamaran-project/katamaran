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
# Marker path: ${TMPDIR:-/tmp}/claude-skillload-<skill-slug>-<session-id>
# Consumers:   v-write-guard.sh (rocq-implementation, core-executor-internals)
set -u

input=$(cat)

skill=$(printf '%s' "$input" | jq -r '.tool_input.skill // ""' 2>/dev/null) || exit 0
[ -n "$skill" ] || exit 0

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession

# Slugify: plugin skills arrive as `plugin:skill`, scoped ones as `dir:skill`.
slug=${skill//[^A-Za-z0-9_-]/-}

dir="${TMPDIR:-/tmp}"
: > "${dir}/claude-skillload-${slug}-${sid}" 2>/dev/null || true

exit 0
