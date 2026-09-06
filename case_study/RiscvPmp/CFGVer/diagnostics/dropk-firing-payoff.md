# dropk: it FIRES, and it buys ~nothing on the current examples

**Finding, in one sentence.** With `drop_fuel = 8` the dead-logical-variable
drop fires on every live example tried — 1, 7 and 4 `dropk` nodes on Countdown,
Cmovznz4 and KeyScheduleLoop — but **peak `|Σ|` moves by at most 1** (17 → 16 on
Cmovznz4, unchanged on the other two), because the variables it finds dead are
not the ones sitting on the peak-`|Σ|` path.

This is a negative result about the PAYOFF, not about the mechanism: the drop is
correct, it is gate-green, `solve_vc` discharges the `dropk` nodes, and the knob
works. It just has nothing worth eating on the programs currently verified.

## Why `SymProp` size is the WRONG instrument (recorded because I used it first)

The first run measured `SymProp.Statistics.size` and read as a REGRESSION:
236 → 237 on Countdown, 3613 → 3620 on Cmovznz4 — up by **exactly** the dropk
count, down by nothing.

That is the expected behaviour, not a regression. A drop removes a **binder from
the context**, not nodes from the tree: the `demonicv` that minted the variable
is still there, and `dropk` adds one node after it. Tree size cannot see the
drop's payoff at all. The payoff is in `|Σ|`, whose lookup cost is quadratic
(`lvar-lookup-cost-drivers.md` §5.3).

**Corollary for anyone measuring a `|Σ|` fix: node count is not a proxy.**
`word-slicing-payoff.md` is the contrasting case — there `|Σ|` 17 → 4 came *with*
the node count dropping by exactly the 13 removed `demonicv` nodes, because
slicing removes the mints themselves. `dropk` does not remove mints; it retires
variables after the fact.

## The experiment

One axis, `drop_fuel`, at two states. Nothing else differs — same commit, same
sources, the constant is the only edit (`Verifier.v:934`).

| axis | states |
|---|---|
| `drop_fuel` | `0` (drop is `SHeapSpec.pure tt`, byte-identical tree) &#124; `8` |

8 is a probe value, not a tuned one. It is an upper bound on drops **per
executor step**; the counts below are totals over the whole tree, so nothing
here shows 8 was binding — most likely 1–2 would give the same counts at lower
scan cost. Not measured.

Metric: `peak_sigma`, the maximum live binder count over every root-to-leaf
path, computed structurally by `vm_compute` on the VC term. Structural counts
are deterministic — this is the same class of metric as
`lvar-lookup-cost-drivers.md`'s binder counts, not a timing.

## Results

**Protocol: raw VC via `cfg_map … CFG_VC_triple`, no `postprocess`, no `Qed` —
identical on both arms.** (Protocol column per this directory's rule; a figure
recorded without its protocol is not a measurement.)

| example | fuel | `dropk` | peak `\|Σ\|` | raw size |
|---|---|---|---|---|
| Countdown | 0 | 0 | 8 | 236 |
| Countdown | 8 | **1** | **8** | 237 |
| Cmovznz4 | 0 | 0 | 17 | 3613 |
| Cmovznz4 | 8 | **7** | **16** | 3620 |
| KeyScheduleLoop | 0 | 0 | 12 | 2914 |
| KeyScheduleLoop | 8 | **4** | **12** | 2918 |

Twelve drops across three programs; peak `|Σ|` improves by 1, on one of them.

No fit, no doubling series, no held-out check — deliberately. There is no curve
here to fit: the effect is at or below one binder on every arm, so a growth law
would be fitting noise. If a vehicle is found where the drop bites, THAT is when
a series over trip count is worth running.

### Cost side — WEAK EVIDENCE, do not quote as a measurement

KeyScheduleLoop rebuild, `user` time: **8.18 s** at fuel 8 (one run) vs
**8.44 / 8.51 s** at fuel 0 (two runs). Reads as "the scan cost is below noise",
and that is the honest summary — but this directory's own rule is that
wall/user clock across separate `coqc` processes is unreliable, and this was not
run with `allocated_words`. **Treat as an absence of an alarming signal, not as
a cost measurement.** It was not pursued further because with the payoff at ~0
the cost question does not change any decision.

## Reading it apart: why does it fire but not help?

`var_dead` (`Verifier.v`) requires a variable to be absent from **all** of the
path condition, heap, `trans`, `apc`, `anp`, table and exits. Two consequences:

1. **Anything the solver has constrained is live**, because it appears in `wco`.
   The solver already eliminates the overwhelming majority of mints — peak `|Σ|`
   is 25 out of 1293 on the KSL rig (`lvar-lookup-cost-drivers.md`) — so by the
   time a variable is *droppable* it is usually one the solver was going to
   handle anyway.
2. **The drops are off the peak path.** Countdown drops one variable and its
   peak is unchanged, which pins this down: the drop happened somewhere the
   context was already below its maximum. Peak `|Σ|` is set by the widest point,
   and retiring a variable elsewhere does not narrow it.

**The population the drop was BUILT for is absent from every live example.**
`havoc-abstraction-payoff.md` measures `havoc_regs` leaving **+7 dead lvars per
trip** on `br_divrem` — that is the target. No example under
`case_study/RiscvPmp/CFGVer/Example/` calls `havoc_regs` (checked by grep); that
work lives only in the diagnostics probes. So this study measured the drop on
programs that never generate the garbage it was designed to collect.

## What this means

- **Leave `drop_fuel` at `0`.** Turning it on changes every VC in the project
  and requires a full gate re-run, in exchange for one binder on one example.
  The knob is live and documented; flipping it is a one-line edit when there is
  a reason.
- **The next measurement is a `havoc_regs` vehicle, not a higher fuel.** Raising
  fuel cannot help: the counts above are totals, and nothing suggests the
  per-step bound of 8 was reached. What is missing is dead variables, not
  permission to drop more of them.
- **Amdahl, stated explicitly** (this directory's "before proposing a fix"
  rule): even a drop that worked perfectly on these examples has a ceiling of
  17 → 16, i.e. ~6% of one program's peak `|Σ|`. On the current example set this
  mechanism is **not dominant and cannot become so**. Any claim that dropk is
  worth its ~1500 lines has to be made on `br_divrem`-shaped code, where the
  havoc lemma is what makes the loop tractable in the first place and the +7
  dead lvars/trip are the price it charges.
- **Open, and NOT answered here:** whether the drop clears those +7/trip. That
  is the question the whole framework exists for and it is still unmeasured.

## Files / reproduction

Probe: `Example/ZZDropFire.v` (throwaway, gitignored, not in `_CoqProject`).
It defines `dropk_count` and `peak_sigma` over `SymProp`, and `vm_compute`s both
for each contract's raw VC.

```bash
# arm A (baseline)
sed -i 's/drop_fuel : nat := 8/drop_fuel : nat := 0/' case_study/RiscvPmp/CFGVer/Verifier.v
make -f Makefile.coq case_study/RiscvPmp/CFGVer/Example/{Countdown,Cmovznz4,KeyScheduleLoop}.vo
coqc -w all -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
     case_study/RiscvPmp/CFGVer/Example/ZZDropFire.v

# arm B — same two commands with := 8
```

Every dependent of `Verifier.v` must be rebuilt between arms; a stale
`KeyScheduleLoop.vo` surfaces as `makes inconsistent assumptions over library
… Prelude`, not as a wrong number. (Hit once during this study.)

---

# Part 2 — on the vehicle it was built for, the drop makes `|Σ|` FLAT (2026-08-31)

**Finding, one sentence.** On br_divrem with a seven-register `havoc_regs` at the
loop head, `drop_fuel = 8` takes peak `|Σ|` from **`19 + 7n` to a constant 21** —
slope 7/trip to **0/trip** — and costs **4.05× less allocation at n=8**. This is
an **exponent change, not a constant factor**: the ratio grows without bound in
`n`, because the drop removes the linear-in-`n` growth of `|Σ|` and `|Σ|` cost is
quadratic.

Part 1's negative result stands exactly as written and is not retracted. It
measured the drop on programs that generate no dead variables. This measures it
on the program that does.

## The vehicle

`havoc-abstraction-payoff.md` §9.4 predicted this and named the configuration:
a **seven**-register havoc leaves all 7 of 7 fresh variables droppable per trip,
while the **three**-register arm leaves only 1 of 3, because the un-havoced temps
carry the previous trip's variables forward. The seven-register set is used here
for exactly that reason. §9.5's warning applies and is now load-bearing: §8's
"havoc three registers" recommendation was tuned with no drop available, and
**inverts** once a drop exists.

Rig: `ZZPin7_3.v`'s (itself `ZZDivremNCommon`'s), copied verbatim, with the ghost
list `[havoc zz_all]` planted at index 8, the loop head.

## Results

**Protocol: raw VC (`tree_raw`, no `postprocess`), no `Qed`, structural
`vm_compute` — identical on both arms. Allocation rows: `OCAMLRUNPARAM=v=0x400`,
one heavy `Eval` per process, imports-only baseline subtracted.**

| n | 1 | 2 | 3 | 4 | 8 |
|---|---|---|---|---|---|
| peak `\|Σ\|`, `drop_fuel = 0` | 26 | 33 | 40 | 47 | 75 |
| peak `\|Σ\|`, `drop_fuel = 8` | 21 | 21 | 21 | **21** | **21** |
| `dropk` nodes | 15 | 22 | 29 | 36 | 64 |

Fits, with held-out checks (n=4 and n=8 withheld from both):

| quantity | fit on n=1,2,3 | predicted n=4 / n=8 | actual | error |
|---|---|---|---|---|
| peak `\|Σ\|` @ fuel 0 | `19 + 7n` | 47 / 75 | 47 / 75 | **0% / 0%** |
| peak `\|Σ\|` @ fuel 8 | `21` | 21 / 21 | 21 / 21 | **0% / 0%** |
| `dropk` | `7n + 8` | 36 / 64 | 36 / 64 | **0% / 0%** |

Exact at every held-out point, at up to 2.7× beyond the fitted range. These are
structural integer counts, so exactness is expected rather than impressive — but
it does mean the flatness is not a small-`n` plateau of the kind this directory
has been fooled by before.

### Cost, measured properly

| arm | baseline | with `Eval` | net | ratio |
|---|---|---|---|---|
| `drop_fuel = 0` | 610,499,159 | 7,609,766,834 | 6,999,267,675 | — |
| `drop_fuel = 8` | 610,500,970 | 2,336,826,618 | 1,726,325,648 | **4.054×** |

The two baselines agree to **1,811 words in 610 M (0.0003%)**, which is the
check that the import closures cost the same and the ratio is clean.

(Wall clock at n=8 was 41.4 s → 21.1 s, i.e. 1.96×. Recorded only to note it
points the same way; per this directory's rules it is not the measurement, and
it understates the allocation ratio by half.)

## Reading it

- **`|Σ|` slope 7 → 0 is the whole story.** The 7 dropped per trip are exactly
  the 7 the havoc mints; `dropk = 7n + 8` says so directly, the constant 8 being
  one-off drops in the prologue. Mint 7, retire 7, net zero — §9.4's "mint 7,
  retire 7" prediction, confirmed mechanically.
- **Exponent, not constant.** `|Σ|` cost is quadratic
  (`lvar-lookup-cost-drivers.md`), so removing a linear-in-`n` term from `|Σ|`
  removes a quadratic-in-`n` term from cost. 4.05× at n=8 is a point on a
  diverging curve, **not** a factor to quote at other `n`. Do not extrapolate it
  as a constant; re-measure at the `n` you care about.
- **Amdahl, honestly.** 4.05× at n=8 means the `|Σ|` term was ~75% of cost there.
  The remaining 25% is now the wall and this mechanism cannot touch it. What that
  residual is has not been identified here.
- **br_divrem's real 31 trips.** §8 measured those at 41.25 G words with the
  three-register havoc and no drop. Nothing here licenses a prediction for n=31 —
  the arms differ in register set as well as fuel, and the curve is diverging.
  It is the obvious next measurement.

## What this means

- **The drop is worth its ~1500 lines, on havoc-shaped code.** That question was
  open at the end of Part 1 and is now answered.
- **`drop_fuel` is still `0` in the tree**, because no example under `Example/`
  uses `havoc_regs`, and Part 1 showed flipping it buys those examples ~nothing
  while requiring a full gate re-run. The flip becomes correct the moment a
  havoc-using example lands — at which point it is a one-line edit plus a gate
  run.
- **`havoc-abstraction-payoff.md` §8's register-set advice is now formally
  superseded for any configuration with the drop enabled**, per its own §9.5.
  Three registers is optimal without a drop; seven is optimal with one. Both are
  measured; neither is universal.

## Files / reproduction

`Example/ZZDropHavoc_n{1,2,3,4,8}.v` (structural counts),
`Example/ZZDropHavocAlloc_{BASE,n8}.v` (allocation, one `Eval` each).
All throwaway, gitignored, not in `_CoqProject`.

```bash
# per arm: set drop_fuel, rebuild the light chain, then run the probes
sed -i 's/drop_fuel : nat := [08]/drop_fuel : nat := 8/' case_study/RiscvPmp/CFGVer/Verifier.v
make -f Makefile.coq case_study/RiscvPmp/CFGVer/Example/Prelude.vo
coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
     case_study/RiscvPmp/CFGVer/Example/ZZDropHavoc_n8.v
OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
     -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/ZZDropHavocAlloc_n8.v \
     2>&1 | grep allocated_words
```

`Example/Prelude.vo` MUST be rebuilt between arms — a stale one surfaces as
`makes inconsistent assumptions over library … Prelude`, not as a wrong number.
Note also that `ZZPin*.v` and the other pre-dropk probes no longer compile at
all: their `count_*` fixpoints predate the `dropk` constructor and are now
non-exhaustive.

---

# Part 3 — at br_divrem's REAL trip count, the drop makes cost EXACTLY AFFINE (2026-09-01)

**Finding, one sentence.** At n = 32 trips, `drop_fuel = 8` on the seven-register
havoc holds peak `|Σ|` at a constant **21** (against `19 + 7n` = 243) and makes
total allocation **exactly affine in the trip count** — `262.2 M + 183.0 M·n`,
fitted on n = 4,8 and predicting BOTH held-out points to **+0.00006% / +0.0002%**,
below the metric's own 0.0008% noise floor — where the same rig without the drop
has a local exponent of **2.029** and rising. br_divrem's real trip count now
costs **6.119 G words in 91 s**.

Part 2 called this "the obvious next measurement" and explicitly declined to
predict it. This is that measurement. Nothing in Part 1 or Part 2 is retracted.

## Why n = 32, when §8 measured n = 31

BearSSL's `br_divrem` loop runs **31** times (fixed by the division algorithm,
one trip per bit of a 31-bit word); the rig's `li A5, n+1` immediate sets it.
This study was run at **32**, i.e. one trip MORE than the real program, so any
comparison against §8's n = 31 figures is conservative in the drop's disfavour.
For the real count exactly, the affine law gives n = 31 → **5.936 G words**.

## The experiment

| axis | states | what moves it |
|---|---|---|
| `drop_fuel` | `0` (drop is `SHeapSpec.pure tt`, byte-identical tree) &#124; `8` | `Verifier.v:856`, one constant |
| `havoc-breadth` | 3 (`A0 A1 A4`) &#124; 7 (`T0 T1 T2 T3 A0 A1 A4`) | the `regs` list in the ghost, nothing else |
| `trip-count` | n = 4, 8, 16, 32 | the `li A5, n+1` immediate; program LENGTH is constant in n |

The R3 and R7 probe files differ from each other in **exactly one line** (the
register list); the n-variants differ in **exactly one token** (`zz_n`). Both
checked by `diff` before running, per this directory's single-axis rule.

**Protocol, identical on every cell: raw VC via `cfg_map … CFG_VC_triple`
(`tree_raw`), NO `postprocess`, NO `Qed`, one heavy `Eval` per `coqc` process,
`OCAMLRUNPARAM='v=0x400'`, imports-only baseline subtracted and RE-MEASURED on
each arm.** This is Part 2's protocol and NOT §8's (which is postprocessed) — see
the cross-protocol section before mixing them.

Baselines: **610,502,973** and **610,505,052** (`drop_fuel = 8`, two separate
rebuilds) and **610,504,516** (`drop_fuel = 0`). Total spread **2,079 words in
610 M = 0.0003%**, which is the check that the import closures cost the same and
the ratios below are clean. All three are within 0.0006% of Part 2's, so Part 2's
n = 8 rows are directly comparable and are reused rather than re-run.

## Results

### Structural counts

| n | peak `\|Σ\|` @ fuel 0 | peak `\|Σ\|` @ fuel 8 | `dropk` @ fuel 8 |
|---|---|---|---|
| 8 | 75 | 21 | 64 |
| 16 | **131** | **21** | **120** |
| 32 | *not run — see below* | **21** | **232** |

### Allocation, net G words

| n | R7, fuel 0 (no drop) | R7, fuel 8 (drop) | ratio | protocol |
|---|---|---|---|---|
| 4 | — | **0.9943** | — | raw, no Qed, one Eval |
| 8 | 6.9993 | 1.7263 | 4.054× | ″ |
| 16 | **28.5725** | **3.1904** | **8.956×** | ″ |
| 32 | *not run* (≥116.6 G projected) | **6.1186** | *≥19.1× projected* | ″ |

### Held-out fits — fitted LOW, held out HIGH

| quantity | fit on | held-out point | predicted | actual | error |
|---|---|---|---|---|---|
| alloc @ fuel 8 | n = 4,8 → `262,235,088 + 183,011,320·n` | n = 16 | 3,190,416,208 | 3,190,418,257 | **+0.00006%** |
| ″ | ″ | n = 32 | 6,118,597,328 | 6,118,609,830 | **+0.0002%** |
| peak `\|Σ\|` @ fuel 8 | Part 2's `21` (n=1..4) | n = 16, 32 | 21 | 21 | **0%** |
| `dropk` @ fuel 8 | Part 2's `7n + 8` (n=1..4) | n = 16, 32 | 120 / 232 | 120 / 232 | **0%** |
| peak `\|Σ\|` @ fuel 0 | Part 2's `19 + 7n` (n=1..4) | n = 16 | 131 | 131 | **0%** |

The `|Σ|` and `dropk` laws are now confirmed at **8× beyond** the range they were
fitted on. They are structural integer counts, so exactness is expected rather
than impressive — but it does rule out the small-n plateau this directory has
been fooled by before, which was Part 2's stated residual doubt.

**The allocation law is the new result.** The fit is taken on the two LOWEST
points and predicts both higher ones, so it extrapolates 4× beyond its range
rather than interpolating; the errors are **below the metric's own
reproducibility** (0.0008%, measured 2026-08-19). Cost per trip is a constant
**183.0 M words**, and the **262.2 M** intercept is the n-independent prologue,
epilogue and contract setup.

That intercept is worth naming: it is exactly the "large n-independent overhead"
that `havoc-abstraction-payoff.md` §10 identified as the thing which broke §9.6's
extrapolation and forced its retraction. Here it is *measured directly* rather
than inferred from a misbehaving fit.

### The no-drop arm at n = 32 was DELIBERATELY NOT RUN

It was started and killed after ~15 minutes. This is not a failed measurement and
should not be recorded as one — the arm is *known* infeasible and re-establishing
that has no value. The evidence, all measured here:

- at n = 16 it already allocates 28.57 G and peaks at **1.694 G words ≈ 13.5 GB**,
  i.e. the entire RAM of the box (which reproduces §8.4's 1.693 G to 0.06%);
- its local exponent 8→16 is **2.029**, so n = 32 projects to **≥116.6 G words**
  and a peak of roughly 27 GB — reachable only through deep swap;
- while running it sat in uninterruptible sleep with 0 GB available.

**≥19.1× is therefore a FLOOR on the drop's payoff at n = 32, not a measurement**,
and this directory's own rule (quadratic fits here underpredict by ~13%) says the
true figure is higher. Do not quote 19.1× as a result.

## Cross-protocol validation (new, and it licenses a comparison Part 2 could not)

The same R7/no-drop configuration, raw here vs postprocessed in §8:

| n | raw (this study) | postprocessed (§8) | raw/post |
|---|---|---|---|
| 8 | 6.9993 | 7.0788 | 0.9888 |
| 16 | 28.5725 | 28.9014 | 0.9886 |

Two independent n agreeing on the correction factor to **0.02%**. The raw
protocol is a uniform **1.14% cheaper** on this rig, so §8's series may be
compared with these numbers *with that correction stated*. Independently, the
local exponent 8→16 measured here is **2.029** against §8's **2.030** — a
cross-protocol reproduction of the no-drop exponent to 0.05%.

**This is not a general license to mix protocols.** It is one measured
equivalence, on one rig, for a tree whose `postprocess` happens to do little.
`check-scalar-combined-cost-drivers.md` prices a protocol mismatch at 1.81×.

## Reading the axes apart

### The `drop_fuel` axis: an exponent, seen from three sides

- **The payoff is not a constant: 4.05× at n=8, 8.96× at n=16.** It doubles as n
  doubles, which is what an exponent change looks like from the ratio side, and
  it is why Part 2's "do not extrapolate 4.05× as a constant" was correct.
- **Why *exactly* affine, mechanically.** `|Σ|` is flat at 21, so every trip runs
  against a context of the same size and costs the same 183.0 M words. The
  no-drop arm's quadratic is `|Σ|`-lookup cost against a `|Σ|` that grows linearly
  in n (`lvar-lookup-cost-drivers.md`: `|Σ|` cost is quadratic). Remove the
  linear-in-n growth of `|Σ|` and the quadratic term goes with it, leaving work
  proportional to trip count and nothing else.
- **Amdahl, at the n that matters.** At n=16 the ratio 8.96× means the `|Σ|` term
  was **88.8%** of the no-drop cost there, up from 75% at n=8. What remains is
  now perfectly linear, so on this rig there is no second superlinear driver
  hiding behind the one just removed — which is the outcome
  `havoc-abstraction-payoff.md` §8.5 explicitly could not promise.

### The `havoc-breadth` axis: the drop COLLAPSES it (and §9.4's forecast is refuted)

Both at n = 32, `drop_fuel = 8`, differing only in the register list:

| arm | peak `\|Σ\|` | `dropk` | net G words | vs R7 |
|---|---|---|---|---|
| R7 (`T0 T1 T2 T3 A0 A1 A4`) | 21 | 232 = `7n + 8` | **6.1186** | — |
| R3 (`A0 A1 A4`) | **19** | **104 = `3n + 8`** | 6.1486 | 1.0049× |

Three things here, two of them corrections:

1. **The register-set axis is worth 0.5%, having been worth 2.66× without the
   drop** (§8.3, R3/R7 at n=16 = 0.377×). The drop does not merely change which
   register set wins — it makes the choice nearly irrelevant. 0.5% is real (it is
   600× the noise floor) but it is not a design consideration.
2. **§9.5's predicted INVERSION is confirmed in direction and refuted in
   magnitude.** R7 does now beat R3, as §9.5 said it would — by 0.5%, not by
   anything resembling the 2.66× it was reversing. Anyone reading §9.5 should
   take "seven registers is now optimal" as true and "the register set matters"
   as false.
3. **§9.4's "1 of 3 droppable per trip" for R3 is REFUTED — never requote it.**
   It predicted R3 under a perfect drop would retain a `|Σ|` slope of 2/trip.
   Measured: `dropk = 3n + 8`, i.e. **3 of 3** are retired every trip, and peak
   `|Σ|` is flat at 19 — *lower* than R7's 21, where 2/trip would have given 83.
   The cause is a method limitation, and it is the transferable lesson:
   **§9.4 took a deadness census at ONE program point (the loop head).** A
   variable live at the loop head can die later in the same trip, and the drop
   runs at *every executor step*, so it collects garbage the loop-head snapshot
   cannot see. A single-point census systematically UNDER-predicts a per-step
   drop. (§9.4's own scope note called its counts an upper bound on droppability;
   the measurement went the other way.)

The mechanism behind the 0.5%: R7 havocs the temps, so their terms stay tiny but
it carries 7 binders per trip; R3 lets the temps be recomputed as real terms each
trip but carries only 3. Under the drop both are flat, and the two effects very
nearly cancel.

## What this means

- **br_divrem's loop is no longer a scaling wall.** It is affine, 183 M words per
  trip, and its real trip count builds in 91 seconds. `PLAN-muladd-full.md` Phase 3
  was blocked on exactly this loop (67.5 s for *two* trips when first isolated;
  31 trips unreachable). That blocker is lifted, and the whole-function question
  becomes total step count rather than this loop's blowup.
- **The drop is the load-bearing half, not the havoc.** The havoc alone removed
  the term recurrence but left exponent 2.03 (`havoc-abstraction-payoff.md` §8.3);
  the drop removes what the havoc left. Neither is sufficient alone, and the
  ~1500 lines are now justified on the program they were written for.
- **`drop_fuel` is still `0` in the tree, and this study does not change that.**
  Part 1's reasoning is unchanged: no example under `Example/` calls `havoc_regs`,
  so flipping it rewrites every VC and needs a full gate run in exchange for ~one
  binder on one example. The flip becomes correct the moment a havoc-using
  example lands — this is the evidence for making it then, not now.
- **What this does NOT establish.** Every number here is raw-VC *construction*
  cost, with no `Qed` and no `solve_vc`. A real end-to-end example adds the `Qed`
  (priced at 1.81× on a different rig) and the VC discharge. **Linearity of the
  construction is not linearity of the proof**, and the proof side is unmeasured.
  That is the next measurement, and it needs a havoc-using example to exist first.

## Files / reproduction

`Example/ZZDropHavoc_n{16,32}.v`, `ZZDropHavocR3_n32.v` (structural counts);
`ZZDropHavocAlloc_{BASE,n4,n16,n32}.v`, `ZZDropHavocAllocR3_n32.v` (allocation,
one `Eval` each). Generated from Part 2's n=8 files by `sed` on a single token, so
nothing but the intended axis can differ. All throwaway, gitignored, not in
`_CoqProject`.

```bash
# per arm: set drop_fuel, rebuild the light chain, then run the probes
sed -i 's/drop_fuel : nat := [08]\./drop_fuel : nat := 8./' case_study/RiscvPmp/CFGVer/Verifier.v
make -f Makefile.coq case_study/RiscvPmp/CFGVer/Example/Prelude.vo
coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
     case_study/RiscvPmp/CFGVer/Example/ZZDropHavoc_n32.v
OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
     -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/ZZDropHavocAlloc_n32.v \
     2>&1 | grep -E 'allocated_words|top_heap_words'
```

`Example/Prelude.vo` MUST be rebuilt between arms (Part 2's note; a stale one
surfaces as `makes inconsistent assumptions over library … Prelude`).

**Box caveat, for wall-clock and peak-footprint figures only.** These runs shared
a 14 GB box with an unrelated 4.4 GB process, and the no-drop arm at n ≥ 16
exceeds RAM and runs in swap. `allocated_words` is deterministic and unaffected —
it reproduced to 0.0003% across three independent baseline runs here — but **no
wall-clock or `top_heap_words` figure in this section is a clean measurement**,
per this directory's standing rule.


---

# ADDENDUM 2026-09-03 — the scan was 22.7x too expensive, and fixing it inverts the verdict ON HAVOC-SHAPED CODE

**This does NOT retract anything above.** Everything in this record is about the
nine live examples, where the drop finds at most one binder worth retiring and
the recommendation to leave `drop_fuel = 0` stands unchanged. What follows is the
measurement this record named as the missing next step -- *"the next measurement
is a `havoc_regs` vehicle, not a higher fuel"* -- run on the muladd probe rig
(`Example/ZZDS<K>.v`, dense per-instruction `havoc` annotations), plus a cost bug
found on the way that had been hiding the answer.

## The bug: `var_dead` re-walked the whole program for every candidate

Two facts about `find_dead`/`var_dead` (`Verifier.v`), each harmless alone:

1. **`oc_ok` does not test, it REBUILDS.** `occurs_check` has type
   `x ∈ Σ -> T Σ -> option (T (Σ - x))` -- it constructs a complete copy of the
   structure at the smaller context, and `oc_ok` discards that copy to keep one
   bit.
2. **`&&` does not short-circuit under `vm_compute`.** `&&` is `andb`, a plain
   FUNCTION, so call-by-value evaluates both arguments. Measured on a closed
   standalone probe: `andb cheap_false slow` **1.416 s**,
   `if cheap_false then slow else false` **0.000 s**.

`var_dead` is an eight-conjunct `&&` whose roots include the O(K) instruction
table, and `itableW_free` is `List.forallb`, itself `f a && forallb f l'`.
Together: **for every logical variable, at every drop attempt, at every step,
the entire instruction table plus path condition plus heap were reconstructed
and thrown away** -- even when the variable had already been found in the first
root. Cost `O(K^2 * |Sigma| * fuel)`, all of it copy-and-discard, which is
exactly what `allocated_words` measures.

## The fix (~40 lines, `Verifier.v`)

- `forallb_sc`, a short-circuiting `forallb`, with
  `forallb_sc_spec : forallb_sc f l = List.forallb f l`.
- `itableW_free` / `etable_free` use it; each keeps a bridge lemma back to the
  `List.forallb` form.
- `var_dead` respelled as nested `if`s and **reordered cheapest-first**:
  `apc`, `anp`, `wd`, `trans`, `h`, `wco`, `exits`, instruction table **LAST**.
  The variables the drop asks about are havoced registers, whose occurrence is
  in the heap -- so for them the table is now never walked at all.
- `var_dead_andb` proves the new definition **equals** the old `&&`-chain in the
  original order (256 subgoals, all `reflexivity`, 122 ms). Behaviour identity
  is therefore a THEOREM, not a measurement, and `VerifierRel.v`'s `wb_bundle`
  needed one line changed (`unfold var_dead` -> `rewrite var_dead_andb in H`).

## Results -- muladd rig, K=206, protocol ALLOC, net of the `ZZDSB` baseline (656,267,200)

| arm | net allocated words | |
|---|---|---|
| `drop_fuel=8`, pre-fix | 44.233 G | the 12.17x penalty in `footprint-vs-throughput.md` §4 |
| `drop_fuel=8`, **post-fix** | **1.947 G** | **22.72x cheaper** |
| `drop_fuel=0` | 3.636 G | |

**So the drop is now 1.87x CHEAPER than not dropping.** The 12.17x penalty is
gone and inverted. Peak `|Sigma|` is unchanged at 33 (fuel 8) and 135 (fuel 0),
as it must be given `var_dead_andb`.

**Control, because the 44.233 G figure is from a different session.** Re-ran
`drop_fuel=0` post-fix: net **3,636,172,368** against the recorded
**3,635,767,677**, i.e. **+0.0111%**; and against the same-file `ZZHP0` arm
(4,292,457,760 gross vs 4,292,439,568 today) **-0.0004%**. The rig is identical
to the study that produced 44.233 G, so both ratios stand. Gate green: build
clean, no holes, 14 end theorems axiom-clean.

## What this changes, and what it does not

- **Not dominant on the live examples -- unchanged.** The Amdahl argument above
  still holds there: `|Sigma|` 17 -> 16 is a ~6% ceiling on one program.
  `drop_fuel` stays at `0` in the committed tree.
- **On havoc-shaped code the verdict inverts.** `|Sigma|` 135 -> 33 was always
  worth a large factor; it was buried under ~42 G words of copy-and-discard.
  This record's own diagnosis that dropk "buys ~nothing" was a statement about
  the example set, but `footprint-vs-throughput.md` §4's *cost* figures were
  measuring the scan bug, not the mechanism.
- **`|Sigma|` = 33 is now free**, which puts it below the ~100-variable region
  where the verifier is reported to degrade. Any cost model built at
  `drop_fuel=0` (i.e. `|Sigma|`=135) -- including `base-k-hunt.md`'s exponent
  work -- describes a configuration that may no longer be the one to run.
- **Open, and NOT measured:** whether `drop_fuel` should become the default.
  It changes every VC in the project, so it needs its own gate run and a
  re-measurement of the `|Sigma|` picture. Also unmeasured: whether 1-2 fuel
  gives the same drops at lower cost (this record's earlier note that 8 was
  never shown to be binding still applies).

## Method lessons

1. **A `&&` in a hot loop is a cost bug under `vm_compute`, not a style choice.**
   This generalises past dropk: any boolean conjunction of expensive tests in
   executor-side code pays for every conjunct. Grep for `&&` and `List.forallb`
   in anything that runs per-step.
2. **`oc_ok`-style "run the constructive version and look at the constructor"
   wrappers are a silent allocation multiplier.** The `option` return says the
   work was done; only the caller knows it is being thrown away.
3. **Two fixes proposed on code-reading alone were wrong, and measurement killed
   both.** Hoisting `all_ins` out of `find_dead`'s fold: it is the fold's LIST
   ARGUMENT, already evaluated once per call, and the world changes each drop so
   there is nothing to hoist -- ~0.1% of cost. And a non-allocating `occurs`
   class across `OccursCheck.v`/`Formulas.v`/`Chunks.v` with ten soundness
   lemmas: after the reordering its ceiling is a fraction of 1.947 G, so it was
   dropped unbuilt. Bound the candidate before building the fix.

## ADDENDUM PART 2 (same day) — the K sweep at CONSTANT `|Sigma|`, and a footprint win that is bigger than the throughput one

The ADDENDUM's open question was whether the REMAINING scan cost justifies a
non-allocating `occurs` (the "Fix 1" declined above). Because `drop_fuel=8` pins
peak `|Sigma|` at **33 regardless of K**, a K sweep at fuel 8 is the first
measurement in this directory that moves program length with `|Sigma|` HELD
FIXED — which answers that question and several others.

Protocol ALLOC + peak RSS, net of a freshly-measured `ZZDSB`
(656,599,455 words / 4,080,536 KB). `|Sigma|` printed **33 at all four K**, and
`ZZDS206` reproduced the ADDENDUM's figure **to the byte** (2,603,120,486).

| K | net alloc (M words) | delta per 22 instrs | net peak RSS (GB) |
|---|---|---|---|
| 140 | 452.4 | — | 0.3016 |
| 162 | 1101.5 | **649.0** | 0.6394 |
| 184 | 1398.5 | **297.1** | 0.8172 |
| 206 | 1946.5 | **548.0** | 1.0818 |

### 1. "Fix 1" is CLOSED — the scan is not the dominant term

A dominant `O(K^2 * |Sigma| * fuel)` scan requires the marginal cost per
instruction to RISE monotonically with K. It does not: over three windows of
identical width (22 instructions) it goes **649 -> 297 -> 548**, falling by more
than half and then rising. So the residual copy-and-discard is the ~6-12% the
ADDENDUM estimated bottom-up, not the ~93% that extrapolating a `|Sigma|^2.4`
law had suggested. **A non-allocating `occurs` class buys ~1.1x. Do not build
it.** (The competing extrapolation is itself refuted: `|Sigma|`^2.4 does not
hold down to 33.)

### 2. TWO-POINT EXPONENTS ON THIS RIG ARE WORTHLESS — including my own

Adjacent windows of EQUAL WIDTH differ by **2.2x** in marginal cost, so the
muladd prefix is structurally heterogeneous and any exponent depends on which
two points were picked:

| interval | fuel | exponent in K |
|---|---|---|
| 140 -> 206 | 8 | **3.78** |
| 162 -> 206 | 8 | **2.37** |
| 162 -> 206 | 0 | **3.44** (recorded) |

**RETRACTED, as laws:** the "total exponent 3.44" and the two-variable fit
`footprint ~ K^2.22 * |Sigma|^0.83` derived from it (this session, unpublished
outside these notes). Both were fitted on two points of a program whose
per-instruction cost swings 2.2x between adjacent windows. Quote a marginal cost
(mean **22.6 M words/instruction** at `|Sigma|`=33, range 13.5-29.5) rather than
an exponent, and never fit an exponent here on fewer than four points.

### 3. The FOOTPRINT win, which matters more than the throughput one

`mlen=2` dies on memory, not time, and this is where the fix lands hardest.

| arm | net peak RSS at K=206 |
|---|---|
| `drop_fuel=0` (today) | **2.8759 GB** — reproduces the recorded 2.876 to **-0.01%** |
| `drop_fuel=8`, pre-fix | 2.045 GB (recorded) |
| `drop_fuel=8`, **post-fix** | **1.0818 GB** |

- **The fix is worth 1.89x in PEAK MEMORY**, not only 22.7x in allocation —
  the discarded copies were real GC pressure. This was not predicted; the fix
  was aimed at throughput.
- **dropk's footprint benefit is now 2.66x, not the 1.41x** recorded in
  `footprint-vs-throughput.md` §3. That figure is superseded: it was measured
  with the scan bug inflating the fuel=8 arm.
- The `drop_fuel=0` reproduction at -0.01% is what licenses comparing today's
  numbers against that study's baseline.

### 4. The drop's benefit GROWS with K

| K | fuel=0 | fuel=8 post-fix | ratio |
|---|---|---|---|
| 162 | 1.593 G | 1.101 G | **1.45x** |
| 206 | 3.636 G | 1.947 G | **1.87x** |

Because fuel=0's `|Sigma|` grows with K (96 -> 135) while fuel=8 pins it at 33,
the gap widens with program length — so it extrapolates FAVOURABLY toward the
full K=292. **This is the strongest argument yet for making `drop_fuel = 8` the
default**: 1.87x throughput and 2.66x footprint at K=206, both still growing.
Still requires its own gate run (it changes every VC), and 8 is still not shown
to be binding.
