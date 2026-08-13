---
name: cfgver-scaling-diagnostics
description: >
  How to run and WRITE UP a CFGVer cost/scaling investigation — pinning down
  which mechanism makes a symbolic-execution example's cost blow up with
  trip count N, distinct from fixing it. Use this when asked to "diagnose",
  "investigate", "figure out the driver", "isolate the cause", or "write up"
  a cost/performance finding for a CFGVer loop or example, or before
  proposing a fix for a scaling wall so the fix targets the right mechanism.
  Covers the catalog of known cost-driver mechanisms (declared-chunk-count
  scaling with N, self-referential symbolic term growth, per-step
  instruction/term density, historically leaked duplicable chunks), the
  `diagnostics/` file convention (a completed causal record, distinct from a
  phased `plans/` document), and — the step most often skipped — how to
  design an ablation that isolates ONE candidate driver at a time instead of
  attributing a compound effect to a single cause. NOT for in-the-moment
  "why is this hanging right now" triage or the exact `allocated_words`
  measurement recipe — both live in `rocq-timeout-triage` (its Step 3
  already states the one-factor-at-a-time principle in miniature; this
  skill is the fuller treatment for when the output is a durable written
  record, not a quick unblock).
---

# CFGVer scaling diagnostics

A scaling *diagnostic* answers "which mechanism is responsible, and by how
much" for a specific example. A `plans/` document answers "what are we going
to build." They're different documents with different shelf lives — a
diagnostic's conclusion outlives whatever fix eventually gets chosen, so it
belongs in its own place: `case_study/RiscvPmp/CFGVer/diagnostics/`, sibling
to `plans/`. See `case_study/RiscvPmp/CFGVer/diagnostics/
key-schedule-loop2-cost-drivers.md` for a complete worked example of
everything below.

## The core discipline: one axis at a time

The single most common way a cost diagnostic goes wrong is comparing two
variants that differ along **more than one** candidate mechanism, then
attributing the whole gap to the one you happen to be focused on. This
happens easily because it's natural to build a "fixed" version and an
"original" version and just diff them — but if the fixed version changed
two things, the measured gap is a *mix*, not a clean reading of either one.

The fix is procedural, not just a warning to be careful:

1. **Name every candidate mechanism as an explicit axis before measuring
   anything.** If you suspect both "N declared resources" and "a
   self-referential recurrence" might matter, that's two axes, not one
   investigation. Write them down as axes (`chunk-usage: 1 | N`,
   `term-growth: flat | growing`) before building variants.
2. **Design each variant to move exactly one axis relative to some other
   variant you already have.** Before trusting a comparison, list every way
   the two variants differ and confirm it's exactly the one axis you mean
   to be reading. A variant that silently differs in a second way isn't
   useless — it just isn't evidence about the axis you think it is.
3. **Name variants by their full axis-state, not an arbitrary label.**
   `N-used + growing-term` self-documents which axes it represents;
   `DISTINCT`/`SHARED`/`PADDED`-style names don't, and that's exactly the
   condition under which a two-axis comparison slips through unnoticed —
   an arbitrary name gives no reminder to check. This is worth doing even
   when you're confident there's only one axis in play, because a second
   one hiding is precisely what you can't see from inside the arbitrary
   name.
4. **Once every axis has an isolated reading, compositions are informative
   on their own.** If axis A alone gives a 2× effect and axis B alone gives
   a 4× effect, a variant with both should land near 8×, and if it doesn't,
   that mismatch is itself a finding (an interaction between the axes, not
   just two independent multipliers) — but you only notice a mismatch like
   that if you've actually got the two clean single-axis readings to
   compare it against.

`rocq-timeout-triage`'s Step 3 states the same idea in one sentence ("if
you suspect two factors changed at once... isolate them independently");
this is the fuller version, worth applying deliberately whenever the
answer is going into a written record, not just whatever gets you
unblocked right now.

## Known cost-driver mechanisms

These are the named mechanisms found so far, each pluggable into the
general executor cost law `heap_size × (α·S + β·S²)` (`S` = steps executed;
full history in `cfgver-executor`'s description) as a specific way one of
those terms grows with the trip count `N`:

- **Declared-chunk-count scaling with N.** The precondition's resource list
  (`reg_specs`/`mem_specs`) is asserted once, up front, for the whole run —
  `gen_contract_rel` does not prune unused entries and does not grow the
  list incrementally as the loop executes. If a program's real data
  structure has `N` cells (e.g. a table being built one entry per trip),
  `heap_size` is `N` for the entire run, not amortized. Isolate this axis
  by holding the instruction body fixed and varying only whether the
  precondition/addressing genuinely touches `N` distinct chunks or 1.
- **Self-referential symbolic term growth.** A register whose new value is
  computed from its *own* previous value every iteration (`H := f(H)`, not
  merely read twice within one iteration's formula) accumulates a nested
  symbolic term — roughly one extra node per iteration — so the term at
  step `k` is `O(k)`-sized, and processing an `O(k)` term at each of `N`
  steps sums to `O(N²)`, independent of chunk count. Isolate this axis by
  rerouting the self-referencing operand to a genuine constant (something
  that does not itself change across iterations) while changing nothing
  else about the instruction sequence.
- **Per-step instruction/term density.** Independent of both axes above: a
  loop body with many chained operations over largely-unconstrained
  (`PVExist`) operands can be expensive per iteration even at a small,
  fixed trip count, simply because each step's own symbolic term is large.
  Distinguish this from the self-reference axis above — a dense body can be
  expensive without any value feeding into its own next iteration at all.
- **Leaked duplicable chunks (historical, now fixed).** `encodes_instr`
  (`Sig.v`) was marked `is_duplicable := true`, and `heap_extractions` keeps
  duplicable chunks on consume rather than removing them — so a fresh
  existential minted every fetch never got cleared, growing the heap by
  exactly one chunk per instruction *step* (not per trip). Fixed by the
  landed chunk-GC (`plans/PLAN-chunk-gc.md`). Worth naming as a category:
  any predicate marked `is_duplicable` in `Sig.v` is a structural candidate
  for the same failure mode if it's ever produced fresh on a per-step,
  rather than per-address, basis — `grep is_duplicable` there before ruling
  it out on a new example.

A caution on terminology: this project has, at different times, tested a
*different* pattern under a similar-sounding name — a register read **twice
within one formula** (e.g. `c |= -EQ0(c) & CMP(...)`, `c` appearing twice in
one expression) — and found it not dominant for that specific reproducer
(see `cfgver-executor`'s description). That is not the same mechanism as
the self-referential-across-iterations pattern above (one read per
iteration, but nesting the *previous iteration's* value) — don't assume a
"term duplication isn't dominant" finding for one shape transfers to the
other without checking which shape you actually have.

## Reliable measurements

`allocated_words` (OCaml's own GC allocation counter) is the default — see
`rocq-timeout-triage`'s `references/allocation-probes.md` for the exact
recipe (`OCAMLRUNPARAM='v=0x400'`, subtracting an imports-only baseline, one
heavy proof/Eval per process, gating on `Finished transaction`). Don't
re-derive that mechanics here; read it before hand-rolling a probe.

Two things not yet in that reference, learned since: wall-clock is
unreliable not just from cache/scheduling noise but can be **actively
contaminated** by something as simple as the conversation itself pausing
mid-run (a process idling for an unrelated reason reads as enormous elapsed
time against negligible CPU-seconds — check the `u`/`s` split, not the
total, if a number looks absurd). And OS-reported peak RSS (`/usr/bin/time`)
can point the **wrong direction** entirely between two variants — prefer
OCaml's own `top_heap_words` (also in the GC stats dump) for a peak-footprint
question; it answers a different question from `allocated_words` (peak
simultaneous resident heap vs. total work ever done) and the two can
disagree in informative ways.

## Common mistakes checklist

- Trusting wall-clock, or OS RSS, across separate `coqc` processes.
- Not gating on `Finished transaction` appearing in the log before trusting
  a number — a variant that fails to compile reports only its baseline-level
  allocation, which reads as "this variant is free."
- Forgetting to subtract the imports-only baseline (it can be a large
  fraction of a small-N figure).
- More than one heavy `Eval`/proof per `coqc` process (later ones inherit
  an OCaml heap the earlier ones already grew).
- Concluding a growth law from one doubling, or a fit that stops too early —
  this project has more than once mistaken a small-N plateau for "it's
  flattening out" when a later crossover was just still ahead. Fit on two
  points and check a third you didn't use before calling something linear
  or quadratic.
- Comparing two variants without first listing every way they differ (the
  core discipline above).

## Writing the diagnostic file

Location: `case_study/RiscvPmp/CFGVer/diagnostics/<short-name>.md`. Structure
that's worked well:

1. **One-sentence finding** at the top — the causal claim, in one sentence,
   before any setup.
2. **The experiment** — the axes, named explicitly, and a table mapping
   each variant's short name to exactly what it changed and which file
   implements it.
3. **Results** — the raw measurements, plus doubling ratios and any
   held-out-point fit checks.
4. **Reading the axes apart** — same-N, one-knob-changed ratios for each
   axis, isolated. This is the section that actually answers "which driver,
   how much," not the raw table.
5. **What this means** — tie the finding to a concrete next step (a fix
   candidate, a plan document, an open question), not just a restatement of
   the numbers.
6. **Files / reproduction** — throwaway probe files (not in `_CoqProject`,
   matching every other `ZZ*.v` probe convention) and the exact commands to
   rerun them.

Keep it information-dense rather than narrating the investigation's
history — the reader wants the causal picture and how to reproduce it, not
a blow-by-blow of what was tried in what order.
