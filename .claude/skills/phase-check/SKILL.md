---
name: phase-check
description: >
  How much to rebuild and re-check after a change in this Rocq repo, mid-plan: which files
  need a FULL proof check, which only need to become loadable again (-vos), the sentinel
  set to run after a solver/peval/executor change, the negative controls, and why the full
  closure / scripts/gate.sh runs only ONCE, at the merge into KatamaranRel. Use it whenever
  you are about to verify a phase, "check it's still green", "run the tests", rebuild after
  editing Solver.v / PartialEvaluation.v / Verifier.v / SpecIris.v, decide between a light
  check and the full gate, or are tempted to rebuild Results.vo or everything downstream of
  a theories/ change. Also for the RSA/arrv files that lie OUTSIDE Results.vo's closure and
  so are never built by the gate. NOT for HOW the merge gate works or how to land a branch
  (branch-workflow), and NOT for iterating on one proof (rocq-implementation).
---

# Checking a phase: a representative set, not the full gate

The full closure rebuild (`make -f Makefile.coq …/Results.vo`, or `scripts/gate.sh`) is
35–40 min at `-j1` on this 14 GB box. It runs **once**, when the topic branch merges
into KatamaranRel. The pre-merge hook enforces that one, so nothing is lost by skipping
it before then (**branch-workflow**). Between phases of a plan, do not rebuild the whole
closure as a check, and do not offer that as the default next step. Emiel's decision,
2026-11-03: "We shouldn't rerun all the tests, just a representative set." It refines
his 2026-10-02 rule "a light check per phase, one full gate at the end".

Hook: `.claude/hooks/phase-check-guard.sh` denies a full-closure build until this skill
has been loaded once in the session. Builds of individual files are not gated.

## What a phase check is

1. **Full check** (a real `.vo`, proofs run) of:
   - **every file whose source changed;**
   - **every file that USES a definition the change touched.** Find them with
     `command grep -rln '\bname\b' --include=*.v` for each renamed, removed or changed name
     (a CLem constructor, a peval helper, a lemma). Use plain `grep` and you miss them:
     here it is a ugrep wrapper that skips gitignored files;
   - **if the change touches EVERY VC** (a solver or peval rule, the executor, the
     closers in `MuladdParamClose.v`), also the **sentinel set**, one heavy
     representative per family:

     | family | sentinel |
     |---|---|
     | muladd loops (heaviest loop VC) | `Example/Muladd/MuladdParamLoopI.v` |
     | check_scalar byte-array loops | `Example/CheckScalar/CheckScalarParamLoop2.v` |
     | flat program, parametric base | `Example/Cmovznz4.v` |
     | RSA / arrv with values, header phase | `Example/Rsa/RsaCcopy.v` |
     | Iris side, end to end | one `Example/*Result.v` downstream of the change |

     Update the table when a new family appears. A sentinel should be the most
     solver-sensitive member of its family, not the cheapest.
2. **Everything else** downstream only has to become loadable again. Coq refuses to
   load a file whose dependency changed, so SOME recompilation is forced. Re-checking
   every proof is not. Compile the rest with `-vos` (statements only, proofs skipped),
   then `-vok` just the files from step 1.
   - Caveat: a file with section VARIABLES and no `Proof using` runs its proofs even
     under `-vos`, because the section's variable usage has to be read off the proof.
     Here that is `Adequacy.v` and `VerifierRel.v`'s Soundness section, so that part is
     a fixed cost (**rocq-implementation** §1).
   - The `-vos`+`-vok` route had not been timed on this closure as of 2026-11-03.
     Measure it the first time, and replace this line with the number.
3. **Negative controls** in the touched files must still fail. A `Goal … Fail solve…
   Abort.` that starts succeeding means the change made the verifier accept something
   it must refuse, so read it as a soundness alarm, not as progress.
4. **Diffs to a trusted statement** (`Noninterference.v`, `Layout.v`, the
   `Example/*Result.v` end theorems, the `*_instrs` lists) still go to Emiel for review.

Kill any file that runs past 1.5× its baseline CPU and investigate before continuing
(the compile-cutoff rule).

## Files the gate never builds

`scripts/gate.sh` builds `Results.vo`'s closure only. Files in `_CoqProject` outside it
are checked by step 1 or by nothing. As of 2026-11-01 these are `RsaMemcpy.v`,
`RsaMemset.v`, `RsaMemmove.v`, `RsaSpikeSb.v` and `RsaSpikeArrv.v` (in
`Example/Rsa/`). To refresh the list, compare `_CoqProject` with the `COQC` lines of a
full gate build log. `make -n` is no substitute: it lists only out-of-date files. When a
change touches what they use, build them explicitly.

## The accepted risk, and why it is acceptable

A solver rule changes the terms of every VC, so a file outside the sentinel set can still
break, either because a closer stops matching or because it slows past the cutoff. The
merge gate catches it, later and at a price: you are further from the change that
caused it. The sentinels exist to make that rare. For a change confined to
`Verifier.v`/`SpecIris.v` (a ghost lemma, a CLem), step 1's grep is close to exact,
since only users of the changed definition can break.

Worked case (2026-11-01, relval-rsa D-M4). Removing four arrv CLems and strengthening
`empty_elim` needed, beyond the changed files: the eight examples that used those CLems,
plus the sentinels for the two solver rules that came with it. The proposed alternative
was a 35–40 min full rebuild, and Emiel rejected it.
