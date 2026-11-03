#!/usr/bin/env bash
# UserPromptSubmit: holds back ONE prompt sent to a big session that has been
# idle long enough for its prompt cache to expire, and explains what each way
# forward costs, so the choice between continue / /compact / /clear is made
# knowingly instead of by default.
#
# WHY. The prompt cache lives 1 h. The first request after a longer pause
# re-writes the WHOLE context into the cache at 2x the base input price. Measured
# on the October 2026 transcripts: 37 such re-writes above 100k tokens, ~10% of
# the month's weighted cost; the largest single request re-cached 901k tokens
# (a morning resume of a day-old session).
#
# Behaviour:
#   - fires only when idle > IDLE_GUARD_MIN minutes (default 60) AND the last
#     request's context > IDLE_GUARD_CTX tokens (default 150000);
#   - blocks ONCE per (session, last request): resubmitting the same prompt goes
#     through, so this can never trap anyone;
#   - never blocks a slash command (/clear, /compact, ...);
#   - any error -> exit 0 silently (allow). A wrong allow costs tokens; a crash
#     or false block costs the user's prompt.
# Override: CLAUDE_IDLE_GUARD_OFF=1 in the launch environment.
# Tests: .claude/hooks/idle-resume-guard.test.sh
set -u
[ "${CLAUDE_IDLE_GUARD_OFF:-}" = "1" ] && exit 0

IDLE_MIN=${IDLE_GUARD_MIN:-60}
CTX_MIN=${IDLE_GUARD_CTX:-150000}
FIXED=63000   # median fixed start-up context of a fresh session (Oct 2026)

input=$(cat) || exit 0
transcript=$(printf '%s' "$input" | jq -r '.transcript_path // empty' 2>/dev/null) || exit 0
session=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || exit 0
prompt=$(printf '%s' "$input" | jq -r '.prompt // ""' 2>/dev/null) || exit 0

case "${prompt#"${prompt%%[![:space:]]*}"}" in /*) exit 0 ;; esac
[ -n "$transcript" ] && [ -r "$transcript" ] || exit 0

# Last assistant record that carries usage. Key ORDER in real records is not
# fixed ("type" comes after the nested message/usage), so pre-filter cheaply on
# "usage", cap the candidates, and let jq decide what is an assistant record.
last=$(tac "$transcript" 2>/dev/null | grep '"usage"' | head -n 50 |
       jq -c 'select(.type=="assistant" and .message.usage != null)' 2>/dev/null | head -n 1) || exit 0
[ -n "$last" ] || exit 0
read -r ctx ts uuid < <(printf '%s' "$last" | jq -r '
  [ ((.message.usage.input_tokens // 0) + (.message.usage.cache_creation_input_tokens // 0)
     + (.message.usage.cache_read_input_tokens // 0)), .timestamp, (.uuid // "nouuid") ] | @tsv' 2>/dev/null) || exit 0
[ -n "${ctx:-}" ] && [ -n "${ts:-}" ] || exit 0

then_s=$(date -d "$ts" +%s 2>/dev/null) || exit 0
now_s=$(date +%s)
idle_min=$(( (now_s - then_s) / 60 ))
[ "$idle_min" -gt "$IDLE_MIN" ] || exit 0
[ "$ctx" -gt "$CTX_MIN" ] || exit 0

marker="${TMPDIR:-/tmp}/claude-idleguard-${session}-${uuid}"
[ -e "$marker" ] && exit 0
: > "$marker" 2>/dev/null || exit 0   # cannot record the hold -> never block

k () { echo "$(( ($1 + 500) / 1000 ))k"; }
warm=$(( ctx / 10 ))                    # one turn with a warm cache, input-equivalent
recache=$(( ctx * 2 ))                  # one turn re-writing the cache (1 h TTL = 2x)
extra=$(( recache - warm ))
saved_per_turn=$(( (ctx - FIXED - 10000) / 10 ))
[ "$saved_per_turn" -lt 1 ] && saved_per_turn=1
if [ "$idle_min" -ge 120 ]; then idle_txt="$(( idle_min / 60 )) h $(( idle_min % 60 )) min"; else idle_txt="$idle_min min"; fi

reason=$(cat <<EOF
Held back once (idle-resume-guard): this session has been idle $idle_txt with a context of $(k "$ctx") tokens, so its prompt cache has expired.

What each way forward costs (input-equivalent tokens):
  continue  - this prompt re-caches the whole context: ~$(k "$recache"), i.e. ~$(k "$extra") more than a normal turn (~$(( extra / (warm > 0 ? warm : 1) )) normal turns' worth). Later turns stay at ~$(k "$warm") each.
  /compact  - the summary pass reads the same expired context once (about the same one-off ~$(k "$recache")), but every later turn then costs ~$(k "$saved_per_turn") less. Pays off when more than a few turns remain and the details can live in a summary.
  /clear    - discards it: a fresh start is ~$(k "$FIXED") of fixed context plus whatever the next task re-reads. Cheapest by far IF the plan's handoff section is current.

Recommendation: if the plan/handoff is up to date -> /clear and start from it. If you are mid-step and need this conversation's detail -> /compact. Continue only for a quick finish (a turn or two).

To continue anyway, submit the same prompt again; it will not be held a second time.
EOF
)
jq -n --arg r "$reason" '{decision:"block", reason:$r}'
exit 0
