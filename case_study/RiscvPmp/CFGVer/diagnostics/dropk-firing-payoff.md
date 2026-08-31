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
