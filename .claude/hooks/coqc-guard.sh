#!/usr/bin/env bash
# PreToolUse(Bash) gate on using `make`/`coqc` as an ITERATION loop.
#
# WHAT THIS IS FOR. A real build here costs ~40 s (targeted) to several
# minutes (full rebuild). Iterating on a proof by rebuilding after each
# tactic tweak therefore costs 3 orders of magnitude more than the
# alternative: rocq_start(preamble=...) + rocq_check, where each attempt is
# ~10-30 ms once imports are warm. A 2026-08-13 session ran dozens of
# ~20-40 s rebuilds one tweak apart, on errors preamble mode located in
# milliseconds. That -- and only that -- is what this hook exists to stop.
#
# DESIGN (rewritten 2026-08-14). The previous version keyed on WHICH FILE
# was being built, via a hand-maintained path allowlist. That was the wrong
# axis and produced friction with no safety benefit:
#   - The costly pattern is a build FREQUENCY, not a build TARGET. A path
#     allowlist cannot express "don't do this twenty times in a row", which
#     is the actual rule.
#   - Every legitimate new target needed a hook edit, and this file is a
#     guard, so each edit needed the user in the loop. That happened TWICE
#     on 2026-08-14 alone, purely to let one-off builds through.
#   - It matched the raw command string, so `ps -ef | grep coqc`,
#     `grep -n 'coqc -w none' file`, and a `kill` whose process listing
#     mentioned Makefile.coq were all blocked. Pure friction: those commands
#     build nothing.
# So: gate on frequency, and only for commands that actually INVOKE a build.
#
# AMENDED 2026-08-16: frequency ALONE was not enough -- see the second rule.
#
# RULE 1 (rate limit). At most $MAX real build invocations per $WINDOW
# seconds. A one-off build, or a final check after real work, is never
# blocked. No path allowlist, so no hook edit is ever needed to build
# something new -- including theories/Bitvector.v and theories/Symbolic/
# Solver.v, which rocq_compile_file genuinely cannot build (a `Load`
# statement and a dropped `-arg "-w all"` respectively) and which previously
# needed named exemptions.
#
# RULE 2 (same target, no interactive check in between). Rule 1 has a blind
# spot that is worst exactly where the cost is highest: a ~6-minute
# Solver.v build means only 2-3 fit in the 15-minute window, so the cap is
# never reached. THE SLOWER THE FILE, THE MORE INVISIBLE THE LOOP. On
# 2026-08-16 six consecutive full Solver.v rebuilds were burned fixing two
# tactic names, with this hook silent throughout -- the very pattern it was
# written to stop, one file slower than it could see.
#
# The condition that actually separates a tweak loop from legitimate
# verification is not "how often" but "was the change checked INTERACTIVELY
# first". So a second build of the same target is denied unless a
# rocq_check / rocq_start / rocq_step_multi happened since the previous one.
# Requires .claude/hooks/rocq-interactive-marker.sh (PreToolUse on those MCP
# tools) to be registered -- if you delete one, delete both, or repeat
# builds can never be unblocked. Disable with CLAUDE_COQC_GUARD_SAMETARGET=0.
# `make X.vo` and `coqc X.v` normalise to the same target.
#
# NOT COUNTED (allowed freely):
#   - Anything that does not actually invoke make/coqc as a command (see
#     is-this-a-build detection below) -- inspection commands are not builds.
#   - `make clean`, `make -n`, `--version`, `--help`: no compilation.
#   - A single-file ZZ*.v diagnostic probe. These are throwaway measurement
#     probes, BY CONVENTION never added to _CoqProject/dune (see the
#     cfgver-scaling-diagnostics skill), so rocq_compile_file cannot see them
#     at all; and sweeping several N values back-to-back is the entire point
#     of a scaling probe, not a thrash pattern. They compile one small file
#     against existing .vo's rather than rebuilding the project.
#
# Tunable per-session via CLAUDE_COQC_GUARD_MAX / _WINDOW. Full off-switch
# is CLAUDE_COQC_GUARD_OFF=1, deliberately settable only in the environment
# Claude Code was launched with (i.e. by the user, not from a session) --
# matching skill-edit-guard.sh's policy. Note the rate limit needs no
# assistant-facing bypass anyway: waiting is itself the intended behaviour.
#
# To remove entirely: delete this file AND the PreToolUse/Bash entry in
# .claude/settings.json. Nothing else references it.
set -u

input=$(cat)

# Cheap pure-bash prefilter: no subprocess for the vast majority of Bash calls.
case $input in
  *coqc*|*make*) ;;
  *) exit 0 ;;
esac

if [ "${CLAUDE_COQC_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi

cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
[ -n "$cmd" ] || exit 0

# ---------------------------------------------------------------------------
# Is this actually a build INVOCATION, or does it merely mention one?
#
# Split the command into pipeline/list segments and check whether any segment's
# own first word is make/coqc, after stripping benign prefixes (`time`, env
# assignments, ...). `ps -ef | grep coqc` splits into `ps -ef` and `grep coqc`,
# neither of which STARTS with a build command, so it sails through -- which is
# the whole point of doing it this way rather than substring matching.
# ---------------------------------------------------------------------------
build_kind=""
while IFS= read -r seg; do
  seg=${seg#"${seg%%[![:space:]]*}"}
  while :; do
    case $seg in
      time\ *|nohup\ *|command\ *|exec\ *|builtin\ *|env\ *|sudo\ *)
        seg=${seg#* }; seg=${seg#"${seg%%[![:space:]]*}"} ;;
      [A-Za-z_][A-Za-z0-9_]*=*)
        seg=${seg#* }; seg=${seg#"${seg%%[![:space:]]*}"} ;;
      *) break ;;
    esac
  done
  first=${seg%%[[:space:]]*}
  first=${first##*/}
  case $first in
    coqc) build_kind="coqc"; break ;;
    make)
      # Only this project's coq build; an unrelated `make` is not our business.
      case $seg in *Makefile.coq*) build_kind="make"; break ;; esac
      ;;
  esac
done <<EOF
$(printf '%s' "$cmd" | sed -E 's/&&|\|\||;|\|/\n/g')
EOF

[ -n "$build_kind" ] || exit 0

# Non-compiling make modes cost nothing.
if [ "$build_kind" = "make" ]; then
  case " $cmd " in
    *" -n "*|*" --dry-run "*|*" --version "*|*" --help "*|*clean*) exit 0 ;;
  esac
fi

# Single-file ZZ*.v diagnostic probe -- see NOT COUNTED in the header.
case $cmd in
  *CFGVer/Example/ZZ*) exit 0 ;;
esac

state_dir=${XDG_RUNTIME_DIR:-/tmp}
key=$(printf '%s' "${CLAUDE_PROJECT_DIR:-$PWD}" | cksum | cut -d' ' -f1)
state="$state_dir/claude-coqc-guard-$(id -u)-$key"

# ---------------------------------------------------------------------------
# CHANGED-FILE rule (added 2026-08-16, tightened same day).
#
# Rule 1 cannot see a slow tweak loop: a ~6-minute Solver.v build never fills
# the 15-minute window, so THE SLOWER THE FILE, THE MORE INVISIBLE THE LOOP.
# Six consecutive full Solver.v rebuilds were burned that way in one session
# fixing two tactic names, with this guard silent throughout.
#
# THE RULE: always check a change interactively before compiling the whole
# file.  So a build is denied when the target's OWN source has changed since
# it was last compiled and no rocq_check / rocq_start / rocq_step_multi has
# happened since that change.
#
# "Changed" is read off the filesystem -- source mtime newer than its .vo --
# not off an edit log.  That is deliberate:
#   - it catches edits made by ANY route, including `sed -i` / `python` from
#     Bash, which an Edit/Write-tool hook would miss entirely;
#   - it is session-independent, so there is no stale-state class of false
#     denial (an earlier build-history version of this rule denied a NEW
#     session's first build of a previously-built file);
#   - a successful build refreshes the .vo, so the next build is allowed
#     again until the source is touched once more.
#
# ONLY THE TARGET'S OWN SOURCE COUNTS.  If a PREREQUISITE changed and this
# file did not, the build is allowed -- that is a dependency rebuild, not a
# tweak loop.  So `make Prelude.vo` after editing Solver.v sails through,
# while `coqc Solver.v` right after editing Solver.v does not.
#
# Deliberately NOT blocked: a build of an unmodified file, and any build
# preceded by interactive work on it.  Disable with
# CLAUDE_COQC_GUARD_SAMETARGET=0.  The marker is written by
# .claude/hooks/rocq-interactive-marker.sh -- if you delete one, delete both.
# ---------------------------------------------------------------------------
sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
marker="${TMPDIR:-/tmp}/claude-rocq-interactive-${sid:-nosession}"

# Every .v the command names.  `make X.vo` and `coqc X.v` normalise to X.v.
# Take the WHOLE whitespace-separated token -- do NOT carve it out with
# `s/.*\(...\.v\)$/\1/`: the leading `.*` is greedy, so the capture
# collapses to ".v" and every target shares one key (caught by this hook's
# own tests).
targets=$(printf '%s' "$cmd" | tr ' \t' '\n\n' \
          | sed -n -e '/\.v$/{s#^\./##;p;}' -e '/\.vo$/{s#^\./##;s#o$##;p;}')

# ns-resolution mtime; %.9Y renders as SEC<sep>NSEC, separator is locale
# dependent, so strip both.  Matches `date +%s%N` in the marker.
mtime_ns() { stat -c '%.9Y' "$1" 2>/dev/null | tr -d '.,' ; }

if [ -n "$targets" ] && [ "${CLAUDE_COQC_GUARD_SAMETARGET:-1}" = "1" ]; then
  last_check=0
  [ -f "$marker" ] && last_check=$(cat "$marker" 2>/dev/null || echo 0)
  case $last_check in ''|*[!0-9]*) last_check=0 ;; esac

  while IFS= read -r tgt; do
    [ -n "$tgt" ] || continue
    [ -f "$tgt" ] || continue
    src_mt=$(mtime_ns "$tgt"); case $src_mt in ''|*[!0-9]*) continue ;; esac
    vo_mt=0
    [ -f "${tgt}o" ] && vo_mt=$(mtime_ns "${tgt}o")
    case $vo_mt in ''|*[!0-9]*) vo_mt=0 ;; esac

    # unchanged since its last build -> not a tweak loop, allow
    [ "$src_mt" -gt "$vo_mt" ] || continue
    # checked interactively since the change -> allow
    [ "$last_check" -le "$src_mt" ] || continue

    msg="BLOCKED by coqc-guard: ${tgt} has changed since it was last compiled, and there has been no interactive check since.

The rule: ALWAYS check a change interactively before compiling the whole file. A full build here costs ~40s to several minutes; an interactive check costs ~10-30ms. On 2026-08-16 six consecutive Solver.v rebuilds were burned fixing two tactic names -- the rate limit below could not see it, because a 6-minute build never fills a 15-minute window.

  - rocq_start(preamble=\"From Katamaran Require Import ...\") + rocq_check -- imports are content-hash-cached, so attempts after the first are near-instant.
  - Cannot reach the real definitions (module functor, or rocq_start cannot index that far into a big file)? Restate the goal SHAPE over abstract Context params; tactic failures reproduce that way in ~100ms. See the rocq-implementation skill.
  - Need an exact mid-proof goal? \`match goal with |- ?G => idtac G end\`, with \`all:\` if there may be more than one goal.

Any rocq_check / rocq_start / rocq_step_multi clears this for ${tgt}. A build whose target is UNCHANGED is never blocked, so a dependency rebuild (e.g. \`make ...Prelude.vo\` after editing a file it depends on) is unaffected.

Genuinely need to compile without checking first? Ask the user; they can set CLAUDE_COQC_GUARD_SAMETARGET=0."
    jq -n --arg r "$msg" \
      '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}'
    exit 0
  done <<EOF
$targets
EOF
fi

# ---------------------------------------------------------------------------
# Rate limit.
# ---------------------------------------------------------------------------
WINDOW=${CLAUDE_COQC_GUARD_WINDOW:-900}
MAX=${CLAUDE_COQC_GUARD_MAX:-3}

now=$(date +%s)
recent=""
count=0
oldest=$now
if [ -f "$state" ]; then
  while IFS= read -r ts; do
    case $ts in ''|*[!0-9]*) continue ;; esac
    if [ $((now - ts)) -lt "$WINDOW" ]; then
      recent="${recent}${ts}
"
      count=$((count + 1))
      [ "$ts" -lt "$oldest" ] && oldest=$ts
    fi
  done < "$state"
fi

if [ "$count" -ge "$MAX" ]; then
  wait=$(( WINDOW - (now - oldest) ))
  [ "$wait" -lt 1 ] && wait=1
  printf '%s' "$recent" > "$state" 2>/dev/null || true
  msg="BLOCKED by coqc-guard: build rate limit reached (${MAX} builds per $((WINDOW / 60)) min).

That is the signature of iterating with \`make\`/\`coqc\`, which costs ~40s-several minutes per attempt. The alternative is ~10-30ms per attempt:

  - Iterating on ONE tactic/lemma: rocq_start(preamble=\"From Katamaran Require Import ...\") + rocq_check. Imports are content-hash-cached, so attempts after the first are near-instant. If the real types are unreachable from a preamble (module functor), restate the goal SHAPE over abstract Context params -- most tactic failures reproduce that way.
  - Whole-file check where the tool can do it: rocq_compile_file(file, mode=\"full\"|\"vos\").
  - Need an exact mid-proof goal? \`match goal with |- ?G => idtac G end\` -- and use \`all:\` if there is more than one goal, or you will only ever see the first.

The budget frees up in ${wait} seconds. It is a rolling window, so no action is needed to reset it -- but if you are about to wait it out and retry the same build unchanged, that is itself the pattern this is stopping: verify the fix in preamble mode first.

Genuinely need a different budget for a legitimate batch (e.g. a measurement sweep)? Ask the user; they can set CLAUDE_COQC_GUARD_MAX / CLAUDE_COQC_GUARD_WINDOW."
  jq -n --arg r "$msg" \
    '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}'
  exit 0
fi

printf '%s%s\n' "$recent" "$now" > "$state" 2>/dev/null || true

# (No per-target build record: the CHANGED-FILE rule reads mtimes instead.)

exit 0
