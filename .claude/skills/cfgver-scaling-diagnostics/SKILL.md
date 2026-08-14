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

## Read these before measuring anything

Half of a new investigation is often already on disk. Check here first —
re-deriving a conclusion someone already established is the most expensive
possible way to start, and a *recurrence* of a known driver looks identical
to a fresh one until you compare.

| file (all in `diagnostics/`) | what it concluded |
|---|---|
| `key-schedule-loop2-cost-drivers.md` | TWO independent axes — declared-chunk **usage** (1 vs N genuinely-touched cells) and self-referential term growth — which is why any single-variant comparison here is a mix. As of the 2026-08-14 re-measurement the term axis is **closed** (`bop.mulx`, 0.98×) and declared-chunk count is the sole remaining driver (2.72× at N=16). The worked example for this whole skill, and for retraction discipline. |
| `check-scalar-loop1-cost-drivers.md` | loop 1's accumulator is **cleared**: <1.4% at N=32, because `z` is read only ONCE per iteration so its term grows linearly. |
| `check-scalar-loop2-cost-drivers.md` | loop 2's `c` accumulation also small (~3.2% at N=16) — but NOT because double-referenced accumulators are safe in general (`key_schedule_loop2`'s identically-shaped `H` genuinely is exponential). Per-iteration density is the primary driver here. |
| `check-scalar-combined-cost-drivers.md` | re-concluded 2026-08-14: combining two loops costs **5.5–18.6×** the sum of the parts, splitting into a **symbolic-base amplification of 2.8–7.2×** (a concrete base removes it) and a residual **1.6–2.6× that is chunk-inventory cost**, dominated by instruction chunks. Also the worked example for the PROTOCOL trap: a `Qed`+`solve_symbase_fetch` denominator against an `Admitted` numerator invalidated two tables. The old "~8–12%" is a pinned-sweep lower bound, superseded. |

Note what the two `check-scalar-loop*` records have in common: a mechanism
that is genuinely dominant in one example was measured near-zero in
another with the *same shape*. Cost-driver names transfer between examples;
their magnitudes do not.

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

### Reading goal state during a diagnostic

Half of diagnosing a cost driver is dumping intermediate state, and Rocq's
goal-selection defaults quietly lie to you when there is more than one goal.
Each of these has produced a confidently WRONG reported result in this
project:

- **A period-terminated tactic acts on the FIRST goal only.** `tac1. tac2.`
  is not `tac1; tac2`. A `Show`/`idtac` dump written with periods inspects
  goal #1 and silently ignores the other fourteen — which on 2026-08-14 was
  read as "these are the goals my tactic failed on" when they were simply
  the untouched raw output, sending the session down a dead end. Same trap
  recorded earlier for `solve_vc. solve_symbase_fetch.`, which made an
  example look like it had a permanent discharge gap it did not have.
  Use `all:` when you mean all goals.
- **`all: idtac "X"` prints exactly ONCE regardless of goal count, including
  at zero goals.** It tells you the tactic ran, nothing more; as a goal
  counter it is pure noise and has manufactured a fictitious "1 residual
  goal at every N". For a count use
  `all: (let n := numgoals in idtac "count:" n)` — and note a BARE
  `numgoals` sentence reports 1 whatever the truth, because a plain tactic
  focuses one goal. For per-goal dumps,
  `all: (match goal with |- ?G => idtac G end)` does iterate correctly.
- **`Time (all: tac)` is a syntax error** — `all:` is sentence-level and an
  `Ltac` body cannot contain one. Time `(t1; t2)` jointly, or take a stage
  cost as a residual against the wall clock.

Corollary worth internalising: if a dump shows N goals and your tactic
"fails", confirm which goals it was actually applied to before theorising
about why. Cheapest check is `all: try tac.` followed by a per-goal dump of
whatever survives.

## Before proposing a fix

Finding the dominant mechanism does NOT establish that fixing it is worth
building. Close that loop explicitly, because this project has twice paid
for a correct diagnosis that led to a fix which barely moved anything:

- **`select_last_k` (July 2026)** — an accumulator fold, algebraically
  correct, genuinely killed the `3^N` term-size wall it targeted. It bought
  **~12% at N=8**, and N=16 still did not finish, because the dominant cost
  at those N was a *separate* `O(steps²)` driver (a leaked duplicable heap
  chunk). Real proof engineering was spent, then reverted. **Sequel worth
  knowing (2026-08-14):** once that quadratic was fixed, the same wall *was*
  worth removing — a different rule (`bop.mulx`) took the term axis from
  3.7–4.7× to 0.98×, i.e. no measurable cost. So the lesson is about
  ORDERING, not about the diagnosis or the fix being wrong: fix the dominant
  driver first, then re-measure before funding the secondary one. Note also
  that the axis only read as fully closed once the *control* variants were
  re-measured on the same footing — a fix compared against its own stale
  pre-fix row could show "now linear" while the truth was "now free."
- **The world-GC** — reported as "2.24× → 10.67×, and the speedup GROWS
  with N". That growth was an artifact of dividing by a steeply superlinear
  baseline; measured on equal footing its real edge was a **constant**
  ~1.85× at N=8, shrinking as N fell.

So before writing a plan, state three things:

1. **Predicted end-to-end speedup**, from the fitted model, at the N you
   actually care about — not the N that was convenient to measure.
2. **Constant factor or exponent change?** A constant factor moves the wall;
   only an exponent change removes it. Say which, in those words. If a
   fix's own arm is only measured against a superlinear baseline, a "growing
   speedup" says nothing — compare arms on equal footing.
3. **Is this mechanism still dominant after the fix?** If it accounts for
   40% of cost, the ceiling is a 1.7× win and the other 60% becomes the new
   wall. Amdahl applies and is routinely forgotten.

If the honest answer is "a constant factor on a mechanism that is not
dominant", that is a legitimate result and belongs in the diagnostic — it
saves the next person the same detour. It is not a reason to inflate the
finding.

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
- **Comparing across TACTIC PROTOCOLS.** `Proof. … vm_compute; solve_vc;
  solve_symbase_fetch. Qed.` and `Proof. … Time vm_compute. Time solve_vc.
  Admitted.` do not measure the same thing — a real `Qed` re-runs the whole
  executor through the VM cast (≈ a second `vm_compute`, see
  `cfgver-executor`), and `solve_symbase_fetch` is extra work. On 2026-08-14
  a sum-of-parts denominator taken from pre-existing `Qed` probes against an
  `Admitted` numerator invalidated two published tables and *understated* a
  superadditivity by ~1.4×. Copy an existing probe's `Proof.` line verbatim,
  and state the protocol in the write-up.
- **Trusting `top_heap_words` at the low end.** It is the high-water mark of
  heap SIZE, quantized to OCaml's ~15% growth steps, and the multi-GB import
  closure means anything whose live set fits in the existing slack reads as
  byte-identical to the floor. That produced a confident "this variant is
  free at every N" for a variant whose allocation demonstrably grew 3×. Use
  `allocated_words` for cost; reserve peak footprint metrics for feasibility.
- **Trusting OS peak RSS for a ratio.** It saturates near the machine
  ceiling, compressing exactly the largest effects — it reported 3.5× where
  `allocated_words` reported 18.6× on the same pair.
- **Assuming an added EXIT prunes execution.** The exit/execute choice is
  `angelic_binary`, so an extra exit only grants permission to stop; the
  execute branch is still constructed and `vm_compute` still pays for it. An
  "exit early to skip the second half" probe measured 92–96% of the
  unmodified cost. To shorten a loop, minimise its trip count instead.

## Writing the diagnostic file

Location: `case_study/RiscvPmp/CFGVer/diagnostics/<short-name>.md`. Structure
that's worked well:

1. **One-sentence finding** at the top — the causal claim, in one sentence,
   before any setup.
2. **The experiment** — the axes, named explicitly, and a table mapping
   each variant's short name to exactly what it changed and which file
   implements it.
3. **Results** — the raw measurements, plus doubling ratios and the
   held-out-point fit check. Not optional: fit on the points you have minus
   one, then report the prediction error at the point you withheld. A fit
   quoted without one is a curve drawn through its own data.
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

### When a later measurement overturns an earlier one

It will. Several headline figures in this project's record have been
refuted by a subsequent, better-controlled run — "the curve bends /
exponent 1.05" (an artifact of stopping the series at N=8), and "heap size
is measured NOT to be a driver (0.95×)", which was wrong and had already
been used once to dismiss the leak that turned out to BE the driver.

**Mark the old claim retracted in place; never silently delete or edit it.**
A reader who remembers the old number needs to find out it was wrong, and a
figure that merely vanishes looks like it is still true somewhere else. In
practice:

- Leave the original text, prefixed `RETRACTED <date>:`, with one line on
  *what specifically* was wrong — the N range, the confound, the baseline.
  Distinguish "the numbers were real but the conclusion doesn't follow"
  from "the measurement itself was bad"; they have different lessons.
- If a figure is quotable-but-wrong, say **"never requote"** explicitly.
  This is what stops it being cited from the old section by a future
  session that skimmed.
- Retract the *conclusion*, keep the *measurements* — later work often
  reuses the raw numbers on a corrected footing.
- Correct the memory note and any `plans/` doc that cites the figure in the
  same commit, per this repo's "docs travel with code" rule. A retraction
  that lives in only one of three places is how the bad figure survives.
