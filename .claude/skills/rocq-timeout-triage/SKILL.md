---
name: rocq-timeout-triage
description: >
  How to triage a Rocq/Coq compile or proof step that is taking way longer than
  expected or has hit an actual timeout, BEFORE deciding what it means or how to
  fix it. Use whenever a `vm_compute`/`Qed`/tactic call is running far past its
  own history, `rocq_compile_file` reports "still running... moved to
  background" for something that used to be fast, or a compile is approaching
  or hitting its timeout ceiling. This is the entry point for that whole class
  of symptom — it triages BETWEEN the specific known causes rather than
  guessing: was the process actually killed (→ rocq-compile-oom, an
  out-of-memory/resource problem, NOT this skill's territory) or is it still
  running and just slow (this skill covers the general "figure out why, cheaply,
  before waiting longer or increasing the timeout" workflow, including
  recognizing the CFGVer backward-branch-loop exponential blowup — see
  cfgver-executor / core-executor-internals — as one specific, already-diagnosed
  cause). NOT for a compile that is simply still in progress and has NOT yet
  exceeded its own normal history (that's routine async behavior, no
  investigation needed) and NOT for an actual Coq error message (rocq-pitfalls
  or the specific proof-layer skill).
---

# Triaging a slow or timed-out compile

The temptation when something is "just slow" is to bump the timeout and wait
longer. Don't — first spend a little effort figuring out WHY, using the
techniques below, which are all cheaper than a second full-length wait. This
skill formalizes the process used to characterize the `key_schedule_loop2`
scaling wall (2026-07-19): timing individual steps, isolating construction
cost from proof-search cost, and bisecting the specific parameter that was
just changed — rather than re-running the whole thing with a bigger number
and hoping.

## Step 0: was it actually killed, or is it just running?

- **Silently killed** (`Terminated`, `Error 143`, no Coq diagnostic at all) →
  this is **rocq-compile-oom**'s territory (memory/swap pressure — orphaned
  processes, OR an over-parallel `make -jN` whose per-process floor × N exceeds
  RAM, common right after a git checkout/merge), not this skill. Check that first.
- **Still running, no crash, just past its own history** (e.g.
  `rocq_compile_file` returns `"reason": "timeout"` after the full timeout
  budget, or a background task has been running far longer than this exact
  file/proof ever has) → continue below. This is the case this skill covers.
- **Routine async "still running after 120s, moved to background"** on
  something that hasn't yet exceeded its own normal compile time is NOT a
  problem to investigate at all — that's expected behavior for any nontrivial
  compile.

## Step 1: find out WHICH step is slow, don't assume the whole file is

Pass `timing: true` to `rocq_compile_file`. Even on a timeout, the response's
`timing.top_slowest` and `last_completed` fields tell you exactly which
sentence was running when time ran out, and how long every OTHER completed
sentence took. Don't guess "the file" is slow — one specific `vm_compute` or
`Qed` almost always is.

## Step 1b: wall-clock is NOT a reliable comparison across runs

`timing.top_slowest` is trustworthy for finding *which sentence* dominates
inside one run. It is NOT trustworthy for comparing one run against another,
and neither is any wall time you measure around `rocq_compile_file` — on a
memory-pressured box the two runs did not see the same machine.

Multi-GB `coqc` processes evict each other's `.vo` page cache, so a file's wall
time depends on **what ran just before it**. Measured 2026-07-27 on the CFGVer
tree: `TablesRel.v` — unchanged, 100 lines, ~3 s of actual proof work —
came in at **22 s → 43 s → 32 s** on three consecutive runs. Run 1 had a warm
cache; run 2 followed `SpecIris` (4.0 GB peak) and `VerifierRel` (3.75 GB),
which had flushed it; run 3 recovered partway as it re-warmed. Nothing about
the file changed. `free -m` showed buff/cache down to 2.3 GB.

This silently poisons exactly the question people use timings for — "did my
restructuring make things faster?" Two same-sized files split out of one will
appear to cost +20 s or +30 s purely because they now run under different cache
conditions than the single file did.

So, when the question is a COMPARISON rather than "which sentence is hot":

- **Prefer peak RSS.** It is deterministic and unaffected by cache state, and
  for build-layout decisions it is usually the binding constraint anyway (it is
  what bounds `make -jN`; see rocq-compile-oom).
- **If you need time, use user CPU, not wall.** `coqc -time` reports
  `(Xu,Ys)` per sentence; summed user time is far more robust than wall clock.
- **Run the variants back-to-back** in the same session and same cache state,
  never against a number recorded on another day.
- **Treat anything under ~2x as noise** unless you have controlled for the
  above. Do not restructure code on the strength of a 10–20% wall-time delta.

The general lesson: before attributing a timing difference to your change,
re-run the *unchanged* baseline and check it still reproduces its old number.
If it doesn't, you are measuring the box, not the code.

## Step 2: isolate construction cost from proof-search cost

If the slow step is `vm_compute` followed by a tactic script (`solve_vc`, a
long `Qed` body, etc.), test the `vm_compute` ALONE first: write the same
`Lemma`, run `vm_compute.` and then `Abort.` immediately — no need to prove
anything to time the reduction itself. This tells you whether the blowup is
in building/normalizing the term (`vm_compute`) or in the subsequent tactic's
search (`solve_vc`/`eauto`/etc.), which matters because they have completely
different fixes. In the CFGVer loop investigation, timing `vm_compute` alone
(via `Abort`) showed the blowup was fully present before `solve_vc` even ran
— that ruled out "the proof search is inefficient" immediately, for a
fraction of the cost of a full attempted proof.

## Step 3: if you just changed a specific parameter (N, fuel, table size…), bisect it

Don't jump straight from "worked at 2" to "try 64" — time a few intermediate
values (e.g. 4, 5, 6, 7) with `Abort`-after-`vm_compute` and look at the
RATIO between consecutive values, not just the raw times:

- Ratio trending toward 1, or roughly constant and small (e.g. staying near
  1.1–1.5×) → polynomial-ish; a bigger timeout will probably eventually work.
- Ratio holding steady around 2× per +1 (or per doubling of the parameter,
  depending on what's varying) → exponential. No timeout will save you; the
  parameter has to be attacked structurally instead (a different proof
  strategy, not "wait longer" — see cfgver-executor's "Backward-branch
  loops"/core-executor-internals for the CFGVer-specific instance of exactly
  this pattern).

If you suspect TWO factors changed at once (e.g. both a loop trip count and a
memory/data-structure size grew), isolate them independently — hold one fixed
at its known-fast value while bumping only the other, for each factor in
turn, rather than assuming the combined symptom means both are guilty.

## Step 4: once you know the shape, hand off

- Confirmed real killed/OOM process → **rocq-compile-oom**.
- Confirmed exponential scaling with a loop's trip count, CFGVer
  specifically → **cfgver-executor**'s "Backward-branch loops" section
  (term duplication of a re-referenced register, not branch forking).
  Same shape but NOT CFGVer, or you need the underlying mechanism → **core-executor-internals**.
- Confirmed polynomial/just genuinely large → this is a real capacity
  question (bigger timeout, more fuel, or accept the current size as the
  practical ceiling and report back) — not a bug to keep digging into.
