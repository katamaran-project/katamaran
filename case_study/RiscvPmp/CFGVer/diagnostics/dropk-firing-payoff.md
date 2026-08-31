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
sources, the constant is the only edit (`Verifier.v:852`).

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
