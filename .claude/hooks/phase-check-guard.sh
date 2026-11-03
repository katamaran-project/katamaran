#!/usr/bin/env bash
# PreToolUse(Bash): BLOCKING gate requiring `phase-check` before a FULL-closure build.
#
# Gated (each as a COMMAND, after stripping `VAR=x`, `env`, `time`, `nohup`, `(`):
#   - `make … Results.vo` (any path prefix): the gate's own closure;
#   - `make -f Makefile.coq` with NO .vo/.vos/.vok target and no `vos` target, i.e.
#     everything in _CoqProject (bare `vok` counts: it checks every proof);
#   - `scripts/gate.sh` (any path prefix, optionally run via bash/sh).
# NOT gated: builds of named files (the light check phase-check prescribes),
# `make … vos`, `make -n`, `make clean`, and anything that only MENTIONS these
# (cat/grep/less of gate.sh, an echo) -- matched on the command word, never on prose.
#
# Why: on 2026-11-03 a full Results.vo rebuild (35-40 min at -j1) was proposed as a
# mid-plan check, and Emiel decided a phase check is a representative set
# (phase-check skill). The pre-merge gate is unaffected: git runs scripts/gate.sh
# itself, not through a Bash tool call.
#
# Satisfied by loading phase-check once per session (marker from
# skill-load-marker.sh). Override: CLAUDE_PHASE_GUARD_OFF=1 in the environment
# Claude Code was launched with. Kept OUT of coqc-guard.sh on purpose: that guard
# is load-bearing for every build, and a bug here must not block builds wholesale.
# Prefer a false ALLOW to a false DENY: it protects time, not soundness.
# Tests: .claude/hooks/phase-check-guard.test.sh
set -u

[ "${CLAUDE_PHASE_GUARD_OFF:-}" = "1" ] && exit 0

input=$(cat)
cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
[ -n "$cmd" ] || exit 0

ltrim () { local s="$1"; printf '%s' "${s#"${s%%[![:space:]]*}"}"; }

hit=""
while IFS= read -r seg; do
  seg=$(ltrim "$seg")
  # strip leading wrappers: `(`, `time`, `nohup`, `env`, `VAR=value`
  while :; do
    case "$seg" in
      '('*) seg=$(ltrim "${seg#(}") ;;
      'time '*|'nohup '*|'env '*) seg=$(ltrim "${seg#* }") ;;
      *)
        w=${seg%%[[:space:]]*}
        case "$w" in
          [A-Za-z_]*=*) [ "$w" = "$seg" ] && break; seg=$(ltrim "${seg#"$w"}") ;;
          *) break ;;
        esac ;;
    esac
  done
  w1=${seg%%[[:space:]]*}
  rest=$(ltrim "${seg#"$w1"}")
  # `bash scripts/gate.sh` / `sh ./scripts/gate.sh`
  if [ "$w1" = "bash" ] || [ "$w1" = "sh" ]; then
    w1=${rest%%[[:space:]]*}; rest=$(ltrim "${rest#"$w1"}")
  fi
  case "$w1" in
    scripts/gate.sh|*/scripts/gate.sh) hit="$seg"; break ;;
    make|*/make)
      args=" $rest "
      case "$args" in *' -n '*|*' --dry-run '*|*' --just-print '*|*' clean '*|*' cleanall '*) continue ;; esac
      if printf '%s' "$args" | grep -Eq '[[:space:]/]Results\.vo[[:space:]]'; then hit="$seg"; break; fi
      if printf '%s' "$args" | grep -q 'Makefile\.coq'; then
        printf '%s' "$args" | grep -Eq '\.vo[sk]?[[:space:]]|[[:space:]]vos[[:space:]]' && continue
        hit="$seg"; break
      fi ;;
  esac
done < <(printf '%s\n' "$cmd" | sed -E 's/(&&|\|\||;|\|)/\n/g')

[ -n "$hit" ] || exit 0

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession
[ -e "${TMPDIR:-/tmp}/claude-skillload-phase-check-${sid}" ] && exit 0

jq -n --arg r "BLOCKED by phase-check-guard: a FULL-closure build without loading phase-check.

Command: ${hit}

A full Results.vo / gate.sh build is 35-40 min at -j1, and in this repo it runs ONCE, at the merge into KatamaranRel (the pre-merge hook enforces it). A mid-plan check is a representative set: the changed files, the files that use a changed name, and the sentinel set after a solver/peval/executor change, with -vos for the rest (Emiel, 2026-11-03). phase-check has the recipe and the sentinel list.

Fires at most ONCE per session. Building named files is never gated. If this really is the final pre-merge run, load the skill and retry.

Do this: invoke phase-check (Skill tool), then retry." '{
  hookSpecificOutput: {
    hookEventName: "PreToolUse",
    permissionDecision: "deny",
    permissionDecisionReason: $r
  }
}'
exit 0
