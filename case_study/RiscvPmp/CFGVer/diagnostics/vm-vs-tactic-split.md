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

One `cbn` is 100% of it; every later step adds nothing.

### The constant is `Erasure.inst_symprop`, and the mechanism is its valuation accumulator

`Propositions.v:2297`:

```coq
| edemonicv b k => forall v : RelVal (type b),
                     inst_symprop (cons (existT (type b) v) ι) k
```

Each unfolding step builds `existT (type b) v` -- a dependent pair carrying the
binder's TYPE as a runtime value -- conses it onto the accumulated valuation,
and recurses.  The goal `cbn` sees is TINY (~7 KB, dumped: a chain of ~22
`edemonicv` nodes under one `inst_symprop`), but one of those binders is the
instruction-word variable at `ty.bvec (32*K)` -- `ty.bvec 7264` at K=227 -- and
`nat` is UNARY.  So that width is rebuilt and carried at every subsequent binder
level: **O(binders x width)**, exactly the law measured from outside (linear in
width at 0.0916 M/bit with 0.13% spread, linear in `|Σ|`).

Confirmed by whitelisting delta to that one constant:

| variant | X=32 (M) | X=3840 (M) | M/bit | share |
|---|---:|---:|---:|---:|
| `cbn beta iota zeta` (no delta) | 100.325 | 111.638 | 0.00297 | — |
| `cbn [Erasure.inst_symprop]` | 215.511 | 473.693 | 0.0678 | **75%** |
| plain `cbn` | 267.645 | 609.600 | 0.0898 | 100% |
| **`cbn -[Erasure.inst_symprop]`** | **100.354** | **111.667** | **0.00297** | **0%** |

Blocking that ONE constant is exactly as cheap as disabling delta entirely,
while leaving every other constant unfoldable -- it is the gateway, so the rest
of the delta cost only exists inside what it produces.

**Eliminated, do not re-test:** `ty.Val`, `bv.is_wf`, `bv.at_most` (all
indistinguishable from plain `cbn` under `-[...]`), and `safeE`, `inst`,
`bv.bin` (all indistinguishable from no-delta under `[...]`).  A minimal
`forall v : bv.bv 3840, v = v` costs `cbn` **0.000 s**, so this does not
reproduce outside the real goal -- the bv type is not the problem, the erasure
layer's valuation accumulator dragging it around is.

Removing that one `cbn`, everything else identical, real `Qed`:

| K | with `cbn` | without | ratio |
|---:|---:|---:|---:|
| 15 | 339.550 | 192.830 | 1.76x |
| 75 | 520.065 | 212.798 | 2.44x |
| 227 | 976.888 | 263.203 | **3.71x** |
| per-entry (15→75) | 3.0086 | 0.3328 | |
| per-entry (75→227) | 3.0054 | 0.3316 | **9.06x** |

Both arms linear (0.36% between the two slope estimates) and both reach `Qed`.

**LANDED 2026-09-08** as `cbn -[Erasure.inst_symprop]` (the surgical form, not
deletion): all 16 real examples build, and **`./scripts/gate.sh` PASSED** --
build clean, no holes, 18 end theorems axiom-clean.

### Payoff on real examples is SMALL -- do not quote the 9x as a project speedup

| example | `cbn` | fixed | change |
|---|---:|---:|---:|
| Cmovznz4 | 915.4 M | 847.7 M | -7.4% |
| BearSSLModpowFull | 1917.8 M | 1809.9 M | -5.6% |
| BearSSLCheckScalarLoop1 | 1345.4 M | 1320.9 M | -1.8% |
| KeyScheduleLoop | 687.1 M | 687.1 M | **0.0%** |
| BearSSLCheckScalar | 671.9 M | 671.9 M | **0.0%** |

The two zeros are byte-identical, which is exactly what the rig split above
predicts (both were measured at 0% `solve_vc` share).  This is a tax that
scales with INSTRUCTION-TABLE SIZE: large on segment contracts carrying a big
table, ~nil on the current suite.

### It re-prices EVERY SUB-TABLE payoff -- matched old-vs-new A/B

Completed 2026-09-08.  Each pair was run twice in the same file: once with
today's `solve_vc`, once with the pre-fix tactic **inlined verbatim as
`solve_vc_old`** (bare `cbn`, everything else identical), so this is a matched
A/B and not a comparison against the published record.  Baselines `ZZSegBase`
606.649 M / `ZZM_base` 606.323 M, net M words, strictly serial.

| pair | OLD full | OLD trim | OLD x | NEW full | NEW trim | **NEW x** | published |
|---|---:|---:|---:|---:|---:|---:|---:|
| countdown synthetic (`pbody 64`/`pseg 256`) | 7.572 | 5.663 | 1.337 | 7.512 | 5.602 | **1.341** | 1.36 |
| muladd seg1, decidable (282/56) | 1055.403 | 354.884 | 2.974 | 172.929 | 90.416 | **1.913** | 3.025 |
| muladd cut @220, `T0` pinned (282/15) | 1164.651 | 339.316 | 3.432 | 311.578 | 194.629 | **1.601** | 3.63 |
| muladd cut @220, `T0` havoc'd (282/15) | 43503.287 | 456.400 | 95.318 | 213.345 | 130.227 | **1.638** | 95.33 |

**Every OLD column reproduces its published figure** -- 1.337 vs 1.36, 2.974 vs
3.025, 95.318 vs **95.33**, and the havoc'd full arm at 43503.287 M against a
published 43503 M, i.e. **0.0007%**.  (The pinned row's OLD is the post-`7e5ceffe`
1164.651/339.316 = 3.432, not the pre-exit-fix 3.63.)  So the rigs are unchanged
and the whole delta is the one `cbn`.

Both havoc'd arms fail to close -- they always have (`table-entry-cost.md`
§Files: *"`ZZSegTrim` is the havoc'd arm and legitimately fails to close (bare
`False`) -- its allocation was read from the failure log"*), and the pre-fix
tactic fails at exactly the same point, so the failure is not new.  Re-run as a
matched `Admitted` pair the ratio is **1.655x** against the failure-log arms'
1.638x, so nothing rests on reading a failed arm.

Per-arm, what the `cbn` was worth:

| arm | old | new | ratio |
|---|---:|---:|---:|
| `ZZSeg2` (havoc'd, 282) | 43503.287 | 213.345 | **203.9x** |
| `ZZTrimF` (decidable, 282) | 1055.403 | 172.929 | 6.10x |
| `ZZSegTrim` (havoc'd, 15) | 456.400 | 130.227 | 3.50x |
| `ZZTrimT` (decidable, 56) | 354.884 | 90.416 | 3.93x |
| `ZZM_b64` / `ZZM_seg256` (countdown) | 7.572 / 5.663 | 7.512 / 5.602 | **1.01x** |

### This CLOSES the 48x undecidable-branch multiplier

`table-entry-cost.md` ended on *"Still unexplained: the 48x undecidable-branch
multiplier (161.2 vs 3.35 M/entry, same program/cut/table)"*.  Reading the same
four arms as a marginal cost per table entry (267 entries between 282 and 15):

| | OLD (M/entry) | NEW (M/entry) |
|---|---:|---:|
| havoc'd `T0` | **161.224** | **0.3113** |
| pinned `T0` | 3.091 | 0.4380 |
| **havoc / pinned** | **52.2x** | **0.71x** |

161.224 is the published 161.2 to four digits, and 3.091 the published 3.09.
**The multiplier is not merely reduced, it is gone** -- an undecidable branch now
makes a table entry very slightly CHEAPER than a decidable one.  So the "48x"
was never an executor property of undecidable branches: an undecidable branch
leaves more `edemonicv` binders standing in the erased VC, and the old `cbn`
charged O(binders x width) for each of them.  It was a `cbn` multiplier the
whole time.

**Consequence for the sub-table machinery.** Its largest advertised payoff,
95.3x, is now **1.638x**, and that was the one number arguing that trimming is
"the only lever currently known to work on" the undecidable-branch regime.  That
regime no longer exists as a distinct cost class.  The machinery is landed,
gate-clean and still worth **1.6-1.9x** on real muladd segments, so this is a
RE-PRICING, not a reason to remove it -- but it is no longer a headline result,
and `prefix-length-cost.md`'s implied *"per-segment trimming is worth (K/k)^2"*
is now doubly superseded (first by `cfdcc92f`, now by this).

## Why the muladd rig differs -- the LEADING BINDER CHAIN (answered 2026-09-08)

The obvious hypothesis is that symbolic-base contracts leave fetch-bound
residuals for `cbn` to chew.  **Wrong:** `ZZKslChunkDistinctCommon` uses
`gen_contract_rel`, i.e. is symbolic-base too, and its `solve_vc` share is 0%.

The second obvious hypothesis is instruction-table SIZE, since the cost is
O(binders x width) and width is `32*K`.  **Also wrong on its own**, and the
counterexample is sharp: `ZZByteLoop1N16` has K=**4** and is 8.2% tactic, while
`ZZKslCD_N16` has K=**14** and is **0%**, and `ZZSegTrimP` has K=**15** and is
33.2%.  Table size alone predicts nothing.

The factor that was missing is the other half of the product.  `inst_symprop`'s
only expensive case is `edemonicv`, so what matters is how long a chain of
`demonicv`/`angelicv` nodes the POSTPROCESSED VC leads with.  Counted directly
(`Example/ZZBind_*.v`, a `count_binders` walk over
`postprocess (CFG_VC_triple ...)`):

| rig | leading binders | K | width `32K` | binders x width | `solve_vc` share |
|---|---:|---:|---:|---:|---:|
| `ZZKslCD_N16` | **0** | 14 | 448 | **0** | **0%** |
| `ZZByteLoop1N16` | 5 | 4 | 128 | 640 | 8.2% |
| `ZZSegTrimP` | 27 | 15 | 480 | 12,960 | 33.2% |
| `ZZSeg2P` | 27 | 282 | 9,024 | 243,648 | 78.1% |

**The zero is the decisive one.** With no leading binders the `edemonicv` case
never fires at all, so the `cbn` is free no matter how big the table is -- which
is exactly why `KeyScheduleLoop` and `BearSSLCheckScalar` came out
BYTE-IDENTICAL before and after the fix.  The product orders all four rigs
correctly, and within the muladd family (binders fixed at 27) the share rises
with K alone, 33% -> 57% -> 78%.

**Do not read the product as a fitted law** -- four points, and the record's own
lesson is that a handful of points will fit anything.  What is established is
the GATE (zero binders ⇒ zero cost, measured) and the two factors' identity
(from `Propositions.v:2297`, not from a fit).  `ZZK_75`'s binder count was not
measured; it is assumed to share `ZZSegTrimP`'s contract shape.

Practical consequence: **to predict whether a rig is tactic-bound, count the
leading binder chain of its postprocessed VC** -- one `Eval vm_compute`, no
proof, seconds.  That is cheaper than the staged `Admitted` arm and answers the
question before you schedule anything.

## What this does and does not retract

- **Nothing is retracted as a MEASUREMENT.** Every ratio and held-out fit in
  this directory is a valid measurement of what it costs to compile that arm.
- **The ATTRIBUTION is wrong wherever the rig is tactic-bound.** For the
  muladd cut-segment family that is 95% of the table-size scaling, so
  `table-entry-cost.md`'s "carrying cost" and `table-entry-sigma-axis.md`'s
  "`persist_itableW` lookup" name executor mechanisms for a cost that is 1.6%
  executor.  Both records carry a correction banner as of today.
- **The rest of the catalog is now split too -- see the next section. Every
  remaining record is executor-dominated; the muladd cut-segment family stays
  the only tactic-bound rig in `diagnostics/`.**

## The catalog split, COMPLETED 2026-09-08

The six records left open above are now classified.  Two classification methods,
in decreasing order of cost:

**(a) STRUCTURAL -- the arm contains no tactic at all.**  Four records (and half
of a fifth) are measured with a bare `Eval vm_compute in ...` at file top level:
no `Lemma`, no `Proof`, no `Qed`, no `solve_vc` anywhere in the file.  For these
the split is **0% tactic by construction** and needs no run:

| record | arms | checked |
|---|---|---|
| `muladd-full-cost-drivers.md` | 13 x `ZZDS*`, `ZZMuladd{Prefix,PrefixHavoc,HavocAll,Dense,DenseAll,Dump}` | 0 of 13 contain `solve_vc` |
| `base-k-hunt.md` | 4 x `ZZDSI*` | 0 of 4 |
| `word-slicing-payoff.md` | 8 x `ZZWsFlat*` | 0 of 8 |
| `ctx-fresh-cost.md` | 6 x `ZZFreshBench*` (+ `ZZDSI206`) | 0 of 6 |
| `lvar-lookup-cost-drivers.md`, INSTR half | 15 x `ZZLvI_*` | 0 of 15 |

`muladd-full-cost-drivers.md` **already said this in its own §1** -- *"the raw-VC
kill is the load-bearing one: it localises the wall to CONSTRUCTION.  `solve_vc`
and the `Qed` are never reached"* -- and it was listed as unmeasured above only
because that line was not re-read.  Check the arm before scheduling a run.

**This REFUTES the speculation above about `base-k-hunt.md`.**  That record's
"the finished VC is <=2.6% of peak heap, so the cost is transient construction
state" was flagged here as *"consistent with the cost being in a TACTIC"*.  It is
not: its rig never runs one.  The transient state is `vm_compute`'s own, and
`base-k-hunt.md`'s conclusion -- including that `Base(K)` needs OCaml heap
profiling rather than any Coq-level traversal -- stands unmodified.

**(b) MEASURED -- one `coqc` per arm, reading `Time vm_compute` / `Time solve_vc`.**
The two remaining rigs both have real tactics.  What matters is not the tactic's
share of the TOTAL but its share of the EFFECT the record attributes to a
mechanism, so each axis is differenced:

### `lvar-lookup-cost-drivers.md` COST grid -- 91-100% executor

13 arms, `intros. Time vm_compute. Time solve_vc. Admitted.`  Baseline
`ZZLvDBase` = 606.3 M.  `solve_vc` share of TOTAL runs 4.8-10.5%.  Per axis:

| axis | dvm (s) | dsolve_vc (s) | tactic share OF THE EFFECT |
|---|---:|---:|---:|
| chunk count pw 0->16, at K0 | +0.519 | **-0.008** | **-1.6%** |
| chunk count pw 0->16, at F64 | +0.427 | **-0.010** | **-2.4%** |
| chunk count pw 0->16, at L64 | +1.836 | +0.037 | **2.0%** |
| pure DEPTH (F64->L64) @ pw0 | +0.484 | **-0.021** | **-4.5%** |
| pure DEPTH (F64->L64) @ pw8 | +1.337 | +0.005 | **0.4%** |
| pure DEPTH (F64->L64) @ pw16 | +1.893 | +0.026 | **1.4%** |
| variable COUNT K0->F64 @ pw0 | +6.525 | +0.673 | **9.3%** |
| variable COUNT F16->F64 @ pw8 | +5.515 | +0.549 | **9.1%** |

Chunk count and lookup depth move `solve_vc` by *nothing* (three of six readings
are negative, i.e. inside noise).  Variable count moves it by 9%, and even there
the shape is the record's, not the tactic's: over the doublings F16->F32->F64,
`solve_vc` grows **2.005x then 1.882x** -- flat, i.e. LINEAR in the count --
while `vm_compute` grows **1.658x then 2.239x**, rising.  **So the |Sigma|
quadratic is entirely an EXECUTOR quadratic**, which is the one claim in that
record a tactic could have counterfeited, and it did not.

*Incidental, and NOT a matched A/B:* the rig's absolute magnitudes have moved a
lot since 2026-08-19.  The published depth surcharge (chunk marginal at L64 vs
at K0) was **16.1x**; today it is **4.71x** (3.581 -> 16.881 M/pw).  Pure depth
L64/F64 was **1.16-1.47x**; today **1.09-1.27x**.  Directions and orderings all
hold.  Several fixes have landed in between (branch refutation, the exit
short-circuit, dropk, this cbn) and the probe itself had to be repaired to
compile at all -- so treat these as "the mechanism is still there and smaller",
not as a measurement of any one commit.

### `composition-payoff.md` -- 0.0% tactic on every arm

| family | arms | `solve_vc` (s) | share |
|---|---|---:|---:|
| prefix axis | `ZZU5_K{0,8,16,32}` | 0.000 | **0.0%** |
| flat trip count | `ZZFlat_N{2,4,8,16}` | 0.000 | **0.0%** |
| composed / pinned | `ZZCmp{Body,Final,BodyPin}` | 0.000 | **0.0%** |

This rig REPRODUCES its published numbers, unlike the lvar one: net M words
7.2 / 7.4 / 7.7 / 8.3 against the published 7.223 / 7.471 / 7.747 / 8.343, and a
flat slope of 1.55 M/trip against the published 1.528.  So the composition
verdict -- including the 2026-09-05 reversal (composition 0.56x the flat VC,
break-even ~4.65 trips/cut) -- is an executor result and is untouched.

**One live discrepancy found while doing this, and it is NOT the cbn change.**
`ZZCmpBody.v` and `ZZCmpFinal.v` carry three residual-closing tactics after
`solve_vc`; today both fail with *"Error: No such goal"*, i.e. `solve_vc` closes
those VCs outright.  Tested directly by re-running each arm against an inlined
copy of the PRE-FIX tactic (bare `cbn`) in the same file:

| arm | new `solve_vc` | old tactic inlined | delta |
|---|---:|---:|---:|
| `ZZCmpBody` | 616.0 M | 616.1 M | 0.016% |
| `ZZCmpFinal` | 614.4 M | 614.5 M | 0.016% |

Both spellings close the goal and cost the same, so the dead tactics predate
2026-09-08 -- most likely `cfdcc92f` (branch refutation) or `7e5ceffe` (the exit
short-circuit).  `composition-payoff.md` §0's note that those two arms "carry
three extra residual-closing tactics" is stale.

### Summary of the whole catalog

| tactic-bound | executor-bound |
|---|---|
| muladd cut-segment family ONLY (`table-entry-cost.md`, `table-entry-sigma-axis.md`) -- 33% at K=15 rising to 78% at K=282 | everything else: key-schedule-loop2, classed existentials, prefix-length, branch-refutation, check-scalar loop1/loop2/combined, muladd-full, base-k-hunt, word-slicing, ctx-fresh, lvar-lookup, composition |

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
Catalog split (2026-09-08): `Example/ZZLvD_*.v` (12 arms, the lvar COST grid,
after repairing `ZZPadShrCommon.v`/`ZZLvarDepthCommon.v` with `asn_no_post`),
`Example/ZZ{U5_K*,Flat_N*,Cmp*}_T.v` (`Time`-instrumented composition arms).
Sub-table re-pricing: `Example/ZZ{Seg2,SegTrim,TrimF,TrimT,M_b64,M_seg256}.v` for
the NEW arm and `..._O.v` for the OLD (the pre-fix tactic inlined as a local
`Ltac solve_vc_old`), plus `ZZ{Seg2,SegTrim}_A.v` for the matched `Admitted`
cross-check; baselines `ZZSegBase.v` / `ZZM_base.v`.
Binder census: `Example/ZZBind_{ksl,bl1,mulTrimP,mul2P}.v`.
Scripts: `split.sh`, `sgsweep.sh`, `subtable.sh`, `rebuild_commons.sh` in the
session tmp dir.

**Reusable method: to A/B a tactic change, inline the old tactic as a local
`Ltac` in the probe file.** No rebuild of `Contracts.v`, no scratch tree, ~10 s
per arm, and both spellings run against byte-identical everything else. It
validated itself three times here by reproducing published figures (456.36 M to
0.009%, 43503 M to 0.0007%, 161.2/3.09 M per entry to four digits).
