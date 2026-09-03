# The payoff of contract composition — measured, and it is NEGATIVE at the sizes we have

Status: **Diagnostic record, 2026-09-04.** This is `plans/PLAN-loop-invariant.md`
U5, finally run, plus the direct flat-vs-composed comparison the landed loop cut
(U9) made possible.

## One-sentence finding

Composition's throughput payoff comes almost entirely from a mechanism we do NOT
have — **a fixed segment costs only 1.155× more with 32 unexecuted instructions
in front of it** — while the composed loop proof costs a flat **178 M words**
against a flat unrolled VC that is **exactly linear at 1.528 M words/trip**, so
for the countdown loop **composition does not pay until ~114 trips**, and the
reason is a single isolated axis: **a segment contract whose counter is
symbolically unknown costs 9.19× one whose counter is pinned**, everything else
held equal.

## 0. Protocol

| tag | protocol |
|---|---|
| **ALLOC** | `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc` process, `allocated_words` net of an imports-only baseline **re-measured on this commit**, `/usr/bin/time` for RSS |

**Proof protocol is `vm_compute. solve_vc. Qed.` in every arm** — `Qed`
throughout, since the `Qed`/`Admitted` gap is 1.81× and would swamp everything
here. Two arms (`ZZCmpBody`, `ZZCmpFinal`) carry three extra residual-closing
tactics before `Qed`; the skill prices that class of difference at 0.004%, so it
is not corrected for.

Baselines re-measured per family and agree to **3,277 words in 6.06e8
(0.0005%)**: 605,858,503 / 605,860,597 / 605,849,525 / 605,851,998 / 605,852,802.
That agreement is what licenses comparing across the families below.

**`top_heap_words` is USELESS on this rig** — byte-identical (553,738,752 or
554,344,448) across every arm, and peak RSS moves by at most 1.6%. The live sets
all fit in the import closure's existing slack. So **this record says nothing
about footprint**; it is a throughput measurement only.

## 1. Axes

| axis | states | rig |
|---|---|---|
| **prefix length K** | 0 / 8 / 16 / 32 unexecuted instructions before a fixed segment | `ZZU5_K{0,8,16,32}` |
| **trip count N**, flat VC | 2 / 4 / 8 / 16 | `ZZFlat_N{2,4,8,16}` |
| **proof structure** | flat unrolled VC vs composed (two segment contracts) | `ZZFlat_N16` vs `CountdownComposed` |
| **counter knownness** | symbolic `k` vs `k` pinned to 5 by the path condition | `ZZCmpBody` vs `ZZCmpBodyPin` |

The last one is the isolating arm: **same `|Σ|`** (the variable `"k"` exists in
both), same chunks, same instructions, same fuel, same executed steps. Only the
path condition gains `k = 5`.

## 2. Results

### 2.1 U5 as originally specified — prefix length is nearly free

A fixed 3-instruction segment, entry pc set past `K` never-executed filler
instructions. Net M words:

| K | net | vs K=0 | marginal / prefix instr |
|---|---|---|---|
| 0 | 7.223 | 1.000× | — |
| 8 | 7.471 | 1.034× | 0.0310 |
| 16 | 7.747 | 1.073× | 0.0345 |
| 32 | 8.343 | **1.155×** | 0.0373 |

Held-out linear fit on K ∈ {0,8,16}, predicting K=32: **−0.87%**. Marginal cost
per prefix instruction rises 0.0310 → 0.0373 (+20% across the range), so it is
very slightly superlinear, but a 4-point series over a 1.15× total effect cannot
distinguish linear from quadratic and **no exponent should be quoted**.

**Reading:** the answer to U5's question — *"does a fixed segment cost more as
the tail of a longer program?"* — is **yes, but barely**. Removing a
32-instruction prefix from a segment's table is worth 13%. This is the axis
composition attacks by giving each segment its own table, and it is small.

### 2.2 The flat unrolled countdown VC is EXACTLY linear in trip count

`X1` pinned to `N` (public), fuel `2N+3`, so exactly `N` trips execute:

| N | net M words | marginal / trip |
|---|---|---|
| 2 | 6.466 | — |
| 4 | 9.520 | 1.5273 |
| 8 | 15.632 | 1.5280 |
| 16 | 27.862 | 1.5287 |

Held-out linear fit on N ∈ {2,4,8}, predicting N=16: **+0.025%**. So
`cost_flat(N) = 3.410 + 1.5278·N` M words, **linear, not superlinear**.

This is the arm the loop cut is supposed to beat, and it is cheap **because the
trip count is concrete**: every branch is decided by computation, never by the
solver.

### 2.3 The composed proof costs 178 M words — 6.4× the flat VC at N=16

| arm | net M words |
|---|---|
| `CountdownComposed` (both segment VCs) | **177.96** |
| — `cdBody` alone | 97.95 |
| — `cdFinal` alone | 83.44 |
| flat VC at N=16 | 27.86 |

The two halves sum to 181.39 against 177.96 measured together (+1.93%, shared
elaboration), which is the consistency check that they are being read correctly.

**Crossover:** `3.410 + 1.5278·N = 177.96` gives **N ≈ 114 trips.** Below that,
the flat unrolled VC is cheaper than the composed proof. ONE symbolic loop-body
VC costs **64× one concrete trip** of the flat arm.

### 2.4 Reading the axes apart — it is the UNKNOWN COUNTER, 9.19×

Same contract, same `|Σ|`, same chunks, same steps; only `k = 5` added to the
path condition:

| arm | net M words | ratio |
|---|---|---|
| `ZZCmpBody` (symbolic `k`) | 97.95 | **9.19×** |
| `ZZCmpBodyPin` (`k` pinned to 5) | 10.66 | 1.00 |

**That is the whole story.** The expense of a segment contract is not its size,
its table, or its chunk inventory — it is that the executor must reason about a
value it does not know. Pinning the counter recovers a cost (10.66 M) within 7×
of the flat arm's *entire* 16-trip VC, from a contract that still carries the
logic variable.

## 3. What this means

- **U5's original question is answered and the answer is "small".** Prefix
  length costs 1.155× over 32 instructions. Composition's table-shrinking
  benefit is a modest constant, not an exponent fix.
- **For the loop cut specifically, composition currently LOSES**, by 6.4× at
  N=16, and only breaks even near N=114. The published loop-cut result (U9) is
  a correctness and expressiveness result, **not** a performance result, and
  `plans/PLAN-loop-invariant.md` U9's "does not measure the payoff" caveat is
  now discharged in the unfavourable direction.
- **The mechanism to attack is symbolic-value cost, not program length.** The
  9.19× pinning effect is the largest single factor measured here, and it is
  intrinsic to what a loop invariant IS: an invariant must hold for an unknown
  counter, or it is not an invariant. **This is a real tension in the whole
  approach, not an implementation defect** — you cannot get the flat arm's
  concreteness and the invariant's generality at once.
- **Scope limit, stated loudly:** countdown is a 2-instruction loop whose flat
  VC is *linear*. The programs the invariant work was motivated by
  (`muladd` at `mlen=2`, `check_scalar`) have flat arms that are superlinear and
  **do not finish at all**. A comparison against a flat arm that does not
  terminate has no crossover, and composition wins by default there. **Nothing
  in this record contradicts that**, and nothing in it supports it either — the
  measurement was not run, because the flat arm cannot be run.
- **Amdahl, stated per this directory's own rule:** even a perfect fix to the
  prefix axis (§2.1) buys 13% on a segment. The dominant term is §2.4's.

## 4. Files / reproduction

Throwaway, gitignored, none in `_CoqProject`:

| purpose | files |
|---|---|
| prefix axis | `Example/ZZU5Common.v`, `ZZU5_K{0,8,16,32}.v`, baseline `ZZU5Base.v` |
| flat trip-count axis | `Example/ZZFlatCommon.v`, `ZZFlat_N{2,4,8,16}.v`, baseline `ZZFlatBase.v` |
| composed arm, split | `Example/ZZCmpBody.v`, `ZZCmpFinal.v`, baseline `ZZCmpBase.v` |
| counter-knownness ablation | `Example/ZZCmpBodyPin.v` |

```bash
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "RSS %M KB WALL %e s" \
  coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/<probe>.v 2>&1 \
  | grep -E 'allocated_words|top_heap_words|RSS|Error'
```

Two traps hit while building this:

- **A `Common` file must `Require Export`, not `Require Import`**, or the arms
  that require it cannot see `Prelude`'s contents and fail with *"The reference
  ValidCFGVerifierContract was not found"* — which reads like a load-path bug.
- **Pinning the counter changes the RESIDUALS**: `solve_vc` then closes the VC
  outright and the unpinned arm's residual-closing tactics fail with *"No such
  goal"*. The pinned arm therefore ends `solve_vc. Qed.` while the unpinned one
  has three extra tactics before `Qed`. Both are `Qed`, which is the factor that
  actually matters.
