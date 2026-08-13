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
  recognizing the CFGVer backward-branch-loop scaling blowup — see
  cfgver-executor / core-executor-internals — as one specific already-diagnosed
  cause, whose mechanism was corrected 2026-07-29). ALSO use for HOW TO MEASURE
  a Rocq performance question at all, before trusting any number: timings that
  disagree between runs of an identical file, or whose growth curve changes
  SHAPE between runs; several heavy `Time Eval vm_compute` commands in one file
  contaminating each other; one stage of a pipeline appearing slower than the
  whole pipeline over it; and designing an ablation that isolates a suspected
  cost without silently changing the proof term underneath you. NOT for a
  compile that is simply still in progress and has NOT yet
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

> **Writing the probe: `references/allocation-probes.md`.** End-to-end recipe for
> measuring `allocated_words` (OCaml GC stats — deterministic to 0.0002% where
> wall clock varied 2.3× on identical input), peak RSS and user CPU: the `coqc`
> invocation, the definitions-file + one-runner-per-N + baseline layout, how to
> write a raw-tree census (including the `Env` guard-checker workaround for term
> size), how to instrument inside the executor via the `nc_debug` channel, and
> how to fit with a held-out point. Read it before hand-rolling a cost probe.

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

## Step 1c: ONE heavy `Eval`/`vm_compute` per `coqc` process

Step 1b is about noise *between* runs. There is a second, larger effect *inside*
one run: **several heavy `Eval vm_compute in …` commands in the same file
contaminate each other's timings.** Later commands execute against an OCaml heap
that earlier ones grew, so they run under materially different GC conditions.

Measured 2026-07-29 (CFGVer, flat-loop VC probe), byte-identical computations:

| | N=1 | N=2 | N=4 |
|---|---|---|---|
| run A (3 Evals/process) | 0.68 | 3.47 | 20.77 |
| run B (3 Evals/process) | 1.09 | 6.24 | 16.18 |
| run C (3 Evals/process) | 1.13 | 5.96 | 15.86 |

Within-run growth ratios **flipped direction** between runs (5.08→5.99 in one,
5.72→2.60 in another) — so even the *shape* of the curve, not just its scale,
was an artifact. Peak RSS differed 3.30 vs 5.35 GB between arms. Consequence: a
"rising exponent" conclusion drawn from those runs did not survive clean
re-measurement (the same baseline was 2.28 then 1.51, i.e. *decelerating*).

So for any number you intend to quote or compare:

- put **one** heavy reduction in a file, and run each N / each variant as its own
  `coqc` invocation (a shared `Require`d definitions file keeps this cheap —
  `Require Export`, not `Require Import`, or downstream probes lose the
  notations);
- record peak RSS and user CPU per process (`/usr/bin/time -f "RSS=%M user=%U"`);
- A/B **within** one process only when the arms are cheap and equal-sized.

## Step 1d: force a stage with a cheap consumer, don't print it

To time one stage of a pipeline (e.g. `postprocess (CFG_VC_triple …)`), do NOT
`Eval vm_compute in` the stage itself — you will mostly measure the **printer**.
`vm_compute` is call-by-value, so wrapping the stage in a cheap consumer forces
the whole computation while leaving a tiny result:

```coq
Time Eval vm_compute in (SymProp.Statistics.size (postprocess (CFG_VC_triple …))).
```

This matters because a printed VC is easily 100 MB. A historical CFGVer note
recorded "the raw un-postprocessed VC times out >90 s at N=2" while the *full*
pipeline over it took 7.6 s — an impossibility under CBV, and entirely a
printing artifact. Sweeping the consumer across successive stages
(`raw` → `prune` → `solve_evars` → … → `postprocess`) gives per-stage cost as
the *delta* between cumulative timings, and the consumer's own output doubles as
a size metric.

Caveat: `SymProp.Statistics.size` scores `error` and `block` nodes as 0 and
counts nodes only, never the terms embedded in them — fine when terms are O(1)
by construction, misleading otherwise.

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

## Step 3b: ablating to find the cause — control the intervention

Once bisection says "something grows per step", the next move is to perturb one
candidate and re-time. Two traps make an ablation lie, and both bit for real in
the 2026-07-29 CFGVer investigation:

- **A weakening ablation can change the tree instead of just its cost.** Nulling
  the solver's fact list (`assumption_pathcondition ctx.nil …`) looked like the
  clean way to isolate the path-condition walk. It would have been confounded:
  the raw tree turned out to contain ~410 solver-killed forks per loop trip
  (every `block` node was a binary node's child), so removing the solver's
  refutation power would have let them all live — path explosion, mistaken for
  the walk being cheap.
- **A removal can truncate execution and read as a speedup.** Dropping a
  postcondition conjunct can make a downstream assert fail, ending that path at
  an `error` leaf. Prefer **additive** interventions: a postcondition is only
  *produced* at call sites, so adding to it adds assumes and no asserts, and
  cannot truncate. Extra facts also cannot disable pruning that already worked.

So: **census the structure, not just the clock.** Count node kinds over the raw
tree (binary nodes, `block`, `block`-as-binary-child, `error`, `assertk`,
`assumek`, `angelicv`, `demonicv`, `assert_vareq`, `assume_vareq`, `debug`) and
require every counter *except the one you intended to move* to stay identical.
That is what separated a confounded two-variable arm from a clean one-variable
arm, and it is cheap — the census walk costs nothing next to building the tree.

Corollary worth knowing: collecting `demonicv` binding **names** and diffing the
multiset against the names eliminated by `assume_vareq` identifies variables that
are never unified away — i.e. it names the thing that grows, rather than merely
confirming that something does.

## Step 4: once you know the shape, hand off

- Confirmed real killed/OOM process → **rocq-compile-oom**.
- Confirmed superlinear scaling with a loop's trip count, CFGVer
  specifically → **cfgver-executor**'s "Backward-branch loops" section.
  Read that section's own caveat first: term duplication of a re-referenced
  register is a real mechanism but was measured (2026-07-29) **not** to be the
  dominant cost at practical trip counts — a loop whose every term stays O(1)
  by construction is just as slow. The measured driver is the **live
  logic-variable context**: two demonic variables per instruction step are
  introduced and never unified away, so `|wctx|` grows linearly in steps and
  per-emission cost grows with it. Same shape but NOT CFGVer, or you need the
  underlying mechanism → **core-executor-internals**.
- Confirmed polynomial/just genuinely large → this is a real capacity
  question (bigger timeout, more fuel, or accept the current size as the
  practical ceiling and report back) — not a bug to keep digging into.
- Writing the finding up as a durable record (not just enough to get
  unblocked right now), or the symptom involves more than one candidate
  driver that need separating cleanly → **cfgver-scaling-diagnostics**, the
  fuller treatment of this section's Step 3 one-factor-at-a-time principle,
  plus the `diagnostics/` file convention and the known cost-driver catalog.
