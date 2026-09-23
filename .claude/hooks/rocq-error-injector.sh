#!/usr/bin/env bash
# PostToolUse(Bash|rocq-mcp): pushes the RIGHT pitfall skill's name in front of
# the assistant when a Rocq error string that we have already diagnosed once
# appears in tool output.
#
# WHY INJECTION RATHER THAN A GATE. The pitfalls skills are symptom-keyed by
# design, and the symptom is literally a deterministic string in tool output --
# so matching a prose description against a goal is unnecessary guesswork when
# the string is right there. There is also nothing to deny: by the time the
# error exists the mistake has happened, and the only useful action is to put
# the fix in front of the reader. Unlike a gate, this needs no cooperation.
#
# NEVER blocks, NEVER fails a tool call: always exit 0, and stay silent unless a
# pattern matches. A false positive here costs two lines of context; a crash
# would cost a tool call, so the whole script is written to be unable to crash.
#
# The gmap/bv split on the SAME "Cannot find witness" string is deliberate: the
# two skills document different causes of it (bv.unsigned atom mismatch vs
# stdpp's Zify instances), and the disambiguator is whether the file in play
# imports gmap. We cannot see the file reliably from here, so both are named
# with the discriminator spelled out.
set -u

input=$(cat)

# Only look at what the tool actually produced. Keep it bounded: a 100 MB VC
# dump must not turn into a 100 MB grep.
out=$(printf '%s' "$input" | jq -r '
  [ (.tool_response.stdout // ""), (.tool_response.stderr // ""),
    (.tool_response.error // ""),  (.tool_response.content // "" | tostring) ]
  | join("\n")' 2>/dev/null) || exit 0
out=${out:0:20000}
[ -n "$out" ] || exit 0

note() {
  printf 'SKILL POINTER (rocq-error-injector): %s\n' "$1"
}

hit=""

case $out in
  *"Cannot find witness"*)
    hit="lia failed with \"Cannot find witness\". Two documented causes, different skills: bv-pitfalls (cbn unfolded bv.unsigned in the goal but bv.unsigned_bounds keeps it folded, so lia sees two unrelated atoms -- fix: 'unfold bv.unsigned in *'), and gmap-pitfalls (stdpp's Zify instances break lia on trivial linear goals in files doing 'From stdpp Require Import gmap'). Check which import the file has, then load that skill." ;;
esac

case $out in
  *"Wrong bullet"*|*"No applicable tactic"*|*"found no subterm"*)
    hit="${hit:+$hit
}Tactic-shape failure (Wrong bullet / No applicable tactic / found no subterm) -> load rocq-pitfalls. If the 'found no subterm' is on a gmap lookup (m !! k) that will not reduce, load gmap-pitfalls instead." ;;
esac

case $out in
  *iApply*|*iFrame*|*iDestruct*|*iIntros*|*iMod*)
    case $out in
      *Error*|*error*)
        hit="${hit:+$hit
}An Iris proof-mode tactic failed -> load iris-proofmode (iApply/iFrame/iMod lore, syntactic matching, persistent-vs-spatial). If the goal is inside a module functor, that skill also has the abstract-restatement recipe." ;;
    esac ;;
esac

case $out in
  *Terminated*|*"Error 143"*|*Killed*|*"signal 9"*)
    hit="${hit:+$hit
}A compile appears to have been KILLED with no Coq error -> load rocq-compile-oom (out-of-memory / orphaned-process diagnosis). Do NOT read this as a proof bug." ;;
esac

# A STALE pet process, not a broken file.  This string is deterministic and the
# fix is one flag, but the failure mode it usually shows up as is an EMPTY
# interactive state with success:true -- which reads as "interactive mode is
# unavailable here" and sends you to blind `make` cycles.  Added 2026-09-22
# after that cost four ~60s builds and a wrong conclusion about the tooling.
case $out in
  *"makes inconsistent assumptions over library"*)
    hit="${hit:+$hit
}\"makes inconsistent assumptions over library\" = something was rebuilt and something that depends on it was NOT. It is never a broken file and never a bad load path. TWO causes, and the tool that reported it tells you which: (a) from rocq-mcp -> a STALE PET holding a pre-edit .vo; the .vo timestamps on disk can be perfectly consistent, because the staleness is in pet's memory. Fix: rocq_start(..., force_restart=True). (b) from coqc/make -> a genuinely STALE .vo ON DISK, typically because you rebuilt one file directly (make X.vo) instead of the dependency closure, so a sibling branch still points at the old one. Fix: rebuild the real target (e.g. make Results.vo), not the single file. For (a) there is a disguise to know: a failed Require in a PREAMBLE is swallowed, so rocq_start returns success:true with EMPTY goals and every later check runs in an environment holding only Coq.Init.*. Smoke-test any fresh state with 'Print Libraries.' before concluding interactive mode is unavailable. See rocq-implementation section 1." ;;
esac

case $out in
  *"still running"*|*"timed out"*|*"moved to background"*)
    hit="${hit:+$hit
}Something ran far past its own history -> rocq-timeout-triage is the entry point (it triages BETWEEN causes before you wait longer or raise a timeout). Note: a tool reporting 'moved to background' is routine async behaviour, NOT a failure -- only reach for the skill if this is slower than the file's own history." ;;
esac

case $out in
  *VerificationConditionWithErasure*)
    hit="${hit:+$hit
}A VC residual survived solve_vc -> load cfgver-solve-vc (the residual-to-tactic table, DebugCFGVerifierContract, the tight-fuel False)." ;;
esac

[ -n "$hit" ] || exit 0
note "$hit"
exit 0
