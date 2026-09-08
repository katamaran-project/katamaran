# How much of `diagnostics/` measures the EXECUTOR and how much measures `solve_vc`

**Date:** 2026-09-08. **Provoked by:** the user asking "I thought you were only
measuring vm_compute time before."  The answer is no, and it matters.

## The problem with the instrument

Every cost figure in this directory is whole-process `allocated_words` for a
`coqc` run whose proof body is some spelling of

```coq
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
```

So `solve_vc` -- and, in `Qed` arms, the kernel -- have always been INSIDE the
number, while the prose has consistently narrated it as executor behaviour
(`persist_itableW`, `|Σ|`, chunk carrying, term growth).  Nothing separated the
symbolic executor from the tactic until 2026-09-08.  Most rigs do carry
`Time vm_compute. Time solve_vc.`, so per-stage WALL CLOCK was always available;
it was simply never read, and `allocated_words` was never split at all.

## Method

Two independent instruments, which agree:

1. **Allocation staging.** Recompile an arm with the proof truncated at each
   stage and `Admitted`: `intros; vm_compute.` / `+ solve_vc.` /
   `+ solve_symbase_fetch.` / the real `Qed`.  Differences attribute
   `allocated_words` to stages.
2. **Wall clock.** Read the `Time vm_compute` / `Time solve_vc` lines the rigs
   already print.

## Result: the split is RIG-DEPENDENT, and only one family is tactic-bound

`solve_vc` share of wall clock, `Admitted` arms, one `coqc` each:

| rig | record it backs | vm (s) | solve_vc (s) | **solve_vc %** |
|---|---|---:|---:|---:|
| `ZZKslCD_N16` | key-schedule-loop2 (distinct chunks) | 8.430 | 0.000 | **0%** |
| `ZZKslCLS_N16` | classed existentials | 4.922 | 0.001 | **0%** |
| `ZZKslCS_N16` | key-schedule-loop2 (shared) | 3.245 | 0.000 | **0%** |
| `ZZKHC_t4_P1` | prefix-length / branch-refutation | 0.612 | 0.000 | **0%** |
| `ZZKHC_t4_P64` | prefix-length / branch-refutation | 1.437 | 0.000 | **0%** |
| `ZZComb_M4_N16` | check-scalar combined | 15.186 | 0.430 | 2.8% |
| `ZZByteLoop2N16` | check-scalar loop2 | 9.954 | 0.352 | 3.4% |
| `ZZComb_M16_N4` | check-scalar combined | 4.061 | 0.316 | 7.2% |
| `ZZByteLoop1N16` | check-scalar loop1 | 1.085 | 0.097 | 8.2% |
| **`ZZSegTrimP`** | **table-entry cost (K=15)** | 0.528 | 0.263 | **33.2%** |
| **`ZZK_75`** | **table-entry cost (K=75)** | 0.536 | 0.720 | **57.3%** |
| **`ZZSeg2P`** | **table-entry cost (K=282)** | 0.886 | 3.152 | **78.1%** |

**Everything except the muladd cut-segment family is executor-dominated.** Those
conclusions stand as statements about the symbolic executor.

**The muladd cut-segment family is tactic-dominated, and its tactic share GROWS
with table size** (33% → 57% → 78%).  That is the family
`table-entry-cost.md` and `table-entry-sigma-axis.md` are built on.

## The table-size scaling is 95% tactic

Allocation staging on the canonical `ZZK_15` / `ZZK_75` arms -- the exact files
the original seven-point sweep used:

| stage | K=15 (M) | K=75 (M) | per entry | share |
|---|---:|---:|---:|---:|
| `vm_compute` (the executor) | 94.618 | 97.467 | **0.0475** | **1.6%** |
| `solve_vc` | +162.500 | +335.498 | **2.8833** | **95.3%** |
| `solve_symbase_fetch` | +0.002 | +0.004 | 0.00003 | 0.0% |
| kernel at `Qed` | +82.192 | +87.908 | 0.0953 | 3.1% |
| **total** | **339.312** | **520.877** | **3.0261** | |

The per-entry column sums to 3.0261, reproducing the independently known
K-slope exactly, so the decomposition is sound.  Wall clock agrees: the K-growth
is +0.029 s of `vm_compute` against +0.455 s of `solve_vc`, i.e. **94%**.

**The symbolic executor is responsible for 1.6% of the table-size scaling.**

## And inside `solve_vc` it is one `cbn`

`solve_vc` (`Contracts.v:453`) is
`vm_compute; constructor; cbn; intros; repeat split; try solve_bv; ...; auto`.
Bisecting it against a dead logic variable of width X (a binder mentioned
nowhere, so it moves only total bit-width in Σ):

| tactic prefix | X=32 (M) | X=3840 (M) | M per bit |
|---|---:|---:|---:|
| `… constructor` | 99.853 | 110.608 | 0.0028 |
| `… constructor; cbn` | 267.645 | 609.600 | **0.0898** |
| `+ intros; repeat split` | 267.735 | 609.691 | +0.0000 |
| `+ try solve_bv` | 267.738 | 609.694 | +0.0000 |

One `cbn` is 100% of it; every later step adds nothing.  This is the blanket-`cbn`
trap already in **bv-pitfalls** (`cbn` unfolding a bv width index into unary
Peano), showing up as a COST driver rather than as a matching failure.

Removing that one `cbn`, everything else identical, real `Qed`:

| K | with `cbn` | without | ratio |
|---:|---:|---:|---:|
| 15 | 339.550 | 192.830 | 1.76x |
| 75 | 520.065 | 212.798 | 2.44x |
| 227 | 976.888 | 263.203 | **3.71x** |
| per-entry (15→75) | 3.0086 | 0.3328 | |
| per-entry (75→227) | 3.0054 | 0.3316 | **9.06x** |

Both arms linear (0.36% between the two slope estimates) and both reach `Qed`.
NOT YET LANDED: it is a shared tactic and only this one program has been
checked.

## Why the muladd rig differs -- NOT base concreteness

The obvious hypothesis is that symbolic-base contracts leave fetch-bound
residuals for `cbn` to chew.  **It is wrong:** `ZZKslChunkDistinctCommon` uses
`gen_contract_rel`, i.e. it is symbolic-base too, and its `solve_vc` share is
0%.  What actually distinguishes the muladd cut segment is not established.
Do not predict the split from the contract builder -- **measure it per rig**,
which costs one `Admitted` arm.

## What this does and does not retract

- **Nothing is retracted as a MEASUREMENT.** Every ratio and held-out fit in
  this directory is a valid measurement of what it costs to compile that arm.
- **The ATTRIBUTION is wrong wherever the rig is tactic-bound.** For the
  muladd cut-segment family that is 95% of the table-size scaling, so
  `table-entry-cost.md`'s "carrying cost" and `table-entry-sigma-axis.md`'s
  "`persist_itableW` lookup" name executor mechanisms for a cost that is 1.6%
  executor.  Both records carry a correction banner as of today.
- Unmeasured and therefore unknown: `muladd-full-cost-drivers.md`,
  `composition-payoff.md`, `subtable`-related figures, `base-k-hunt.md`,
  `word-slicing-payoff.md`, `ctx-fresh-cost.md`, `lvar-lookup-cost-drivers.md`
  (its rig's commons did not rebuild in time).  `base-k-hunt.md` is the most
  interesting of these: it concluded the finished VC is <=2.6% of peak heap and
  the cost is "transient construction state" -- which is consistent with the
  cost being in a TACTIC rather than in the executor at all.

## Method lesson

**Name the stage, not just the number.** An `allocated_words` figure for a
`coqc` run is the cost of a PIPELINE -- elaboration, `vm_compute`, the tactic,
and the kernel.  Attributing it to any one of them requires a staged arm, which
costs one extra 10-second compile.  Ten months of records did not pay that
10 seconds, and the result was a fix (base+offsets) built against a mechanism
worth 0.58%.

## Arms

`Example/ZZSg_{A_VM,B_SVC,C_ALL}_K{15,75}.v` (allocation staging),
`Example/ZZSg_{S1..S4}_{32,3840}.v` (inside `solve_vc`),
`Example/ZZSg_WX{32,480,1920,3840}.v` (width axis),
`Example/ZZSg_{NOCBN,CBN}_K{15,75,227}.v` (the fix),
`Example/ZZSg_TIME_K{15,75}.v`, `Example/ZZSg_T_ZZ*.v` (wall-clock split).
Script: `split.sh`, `sgsweep.sh` in the session tmp dir.
