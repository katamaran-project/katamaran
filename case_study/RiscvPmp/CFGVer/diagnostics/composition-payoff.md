# The payoff of contract composition — measured, and it is NEGATIVE at the sizes we have

Status: **Diagnostic record, 2026-09-04.** This is `plans/PLAN-loop-invariant.md`
U5, finally run, plus the direct flat-vs-composed comparison the landed loop cut
(U9) made possible.

> **VERDICT REVERSED 2026-09-05 — see the ADDENDUM at the end of this file.**
> After `cfdcc92f` (branch refutation) a cut costs **7.10 M words, not ~108 M**,
> composition is **0.56×** the flat VC where it was 6.4–7.3×, break-even falls
> from ~71 trips per cut to **~4.65**, and §2.4's "the expense is the unknown
> counter, 9.19×" is now **1.006×**. Everything below remains a correct record
> of the pre-fix executor and its flat arms still reproduce exactly — but do
> **not** quote 6.4×, 7.30×, ~90 M per contract, 9.19×, or "cut sparingly".

## One-sentence finding

Composition's throughput payoff comes almost entirely from a mechanism we do NOT
have — **a fixed segment costs only 1.155× more with 32 unexecuted instructions
in front of it** (**SCOPED 2026-09-04: true of the STRAIGHT-LINE segment measured
here, false of a loop-body contract, which is quadratic in prefix length —
`prefix-length-cost.md`**) — while the composed loop proof costs a flat **178 M words**
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
about footprint**; it is a throughput measurement only. (True of these
arms. The PREFIX axis, re-run on the loop-body contract, *does* move footprint —
41 MB → 1318 MB net RSS over P=0→64, with `top_heap_words` stepping off its
floor: `prefix-length-cost.md` §2.5.)

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

> **SCOPE LIMIT added 2026-09-04 — do not generalise this row.** Re-run on the
> LOOP-BODY segment contract instead of these 3 MVs, the same axis is an exact
> quadratic: `93.81 + 4.05·P + 0.531·P²` M words, **26.93× over 64 filler
> instructions** (held-out +0.0024%), and it needs the unknown counter — pinning
> it returns 1.42×. The trigger is a branch condition the solver cannot decide
> by computation, which this straight-line rig lacks even though it does carry
> three symbolic register values. **`prefix-length-cost.md`.** The row above is
> correct as a measurement and wrong as a general claim about segment contracts;
> consequently "composition's table-shrinking benefit is a modest constant, not
> an exponent fix" (§3, first bullet) is **RETRACTED** — for a loop-body contract
> it IS an exponent fix, worth (K/k)².

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

> **Two corrections to this ratio, 2026-09-04 (`prefix-length-cost.md`).**
> (a) **9.19× is not a constant** — it is the value at a 2-instruction program,
> and it grows linearly in program length, reaching **307×** at 64 filler
> instructions. (b) The pinned arm's cost depends on **conjunct order**: pinning
> BEFORE the guard rather than after is 1.74× cheaper (5.79 M vs 10.06 M on a
> matched rig), so a pinning ratio quoted without the ordering is ambiguous by
> that factor. `ZZCmpBodyPin` re-runs at exactly 10.660 M on the 2026-09-04
> commit, so nothing here has drifted.
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

---

# ADDENDUM 2026-09-04 — the TWO-LOOP payoff, and the superadditivity that isn't

`plans/PLAN-loop-invariant.md` U11 predicted composition would win on two loops,
on the grounds that combining two loops was measured **5.5–18.6× superadditive**
(`check-scalar-combined-cost-drivers.md`). **That prediction is wrong for this
program, and the reason is instructive.**

## One-sentence finding

The flat two-loop VC is **exactly linear in total trips** (`3.427 + 1.5811·T`,
held-out −0.036%) and combining the two loops is **0.970× the cost of verifying
them separately — SUBadditive** — so there is no superadditivity for composition
to recover, and the composed proof loses by **7.30×**, worse than the 6.4× it
lost by on a single loop.

## Results

Same program as `Example/TwoLoopsComposed.v`, both counters pinned concrete at
`nA = nB = N`, fuel `2nA+2nB+3`. `T = nA+nB` total trips. Baseline 605,870,094.

| N | T | net M words |
|---|---|---|
| 2 | 4 | 9.751 |
| 4 | 8 | 16.075 |
| 8 | 16 | 28.725 |
| 16 | 32 | 54.042 |

Marginal per trip: **1.581 / 1.581 / 1.582** — constant to four significant
figures. Held-out linear fit on T ∈ {4,8,16} predicting T=32: **−0.036%**.

| arm | net M words |
|---|---|
| flat two-loop, T=32 | 54.04 |
| **composed (4 contracts)** | **394.61** |

**Composed / flat at T=32 = 7.30×. Crossover at T ≈ 247 total trips (124 per
loop).**

## Reading the axes apart

**1. There is no superadditivity here.** Against U10's single-loop law
(`3.410 + 1.5278·N`), two separate single-loop VCs at N=16 each would cost
**55.71 M**; the combined two-loop program costs **54.04 M**. Ratio **0.970** —
combining is very slightly CHEAPER than separating, because the ~3.4 M fixed
intercept is paid once instead of twice.

**Why `check_scalar`'s 5.5–18.6× does not reproduce:** that figure decomposes
into a **symbolic-base amplification of 2.8–7.2×** and a **chunk-inventory
residual of 1.6–2.6×** (`check-scalar-combined-cost-drivers.md` §5.5, §6). This
program has a **concrete base** and a **two-register inventory**, so both
mechanisms are absent. The superadditivity was never a property of "two loops";
it was a property of symbolic bases and large declared inventories that happened
to be measured on a two-loop program. **Do not treat "combining loops is
superadditive" as a general law — it is contingent on those two mechanisms.**

**2. A symbolic segment contract costs ~83–99 M words almost regardless of what
it contains.** Across every segment contract measured:

| contract | net M words |
|---|---|
| `cdBody` (single loop, body) | 97.95 |
| `cdFinal` (single loop, exit) | 83.44 |
| two-loop, mean of 4 contracts | 98.65 |

That flatness is the real cost law of composition: **you pay ~90 M per segment
contract, and the flat arm buys ~60 trips for that same money.**

> **SCOPED 2026-09-04:** ~90 M is the value at a 2–4 instruction table, which is
> what every contract in this table has. The same contract in a 66-instruction
> program costs **2.53 G**, because the per-segment cost is quadratic in the
> surrounding program's length (`prefix-length-cost.md` §2.1). The law is flat in
> the segment's OWN content and quadratic in the program around it, so the
> break-even is not ~60 trips per cut but ~60 at K=2 and ~970 at K=66. Adding a second
loop doubled the contract count (2 → 4) and doubled the composed cost
(177.96 → 394.61, 2.22×), exactly as that model predicts.

## What this means

- **U11's prediction is RETRACTED** (marked in place in the plan). Composition
  loses on two loops by 7.30×, *more* than on one.
- **The mechanism is unchanged from §2.4**: it is the unknown counter (9.19×),
  and it is paid once per segment contract. Adding structure to the program adds
  contracts, so composition's cost scales with the number of CUTS while the flat
  arm's scales with TRIPS. Composition wins only when trips ≫ cuts, by roughly
  60 trips per cut on this rig.
- **The case that remains genuinely open is the one where the flat arm does not
  terminate** (`muladd` mlen=2, `check_scalar` — symbolic base, large
  inventories, i.e. exactly the two mechanisms absent here). There, "flat cost"
  is ∞ and any finite composed cost wins. **That is now the ONLY remaining
  argument for this technique on performance grounds**, and it has not been
  measured because the flat arm cannot be run.
- Corollary for design: **cut sparingly.** Every cut costs ~90 M. A loop
  invariant that replaces 250+ trips pays; a cut that replaces 10 does not.

## Files

`Example/ZZF2Common.v`, `ZZF2_N{2,4,8,16}.v`, baseline `ZZF2Base.v`; composed arm
is `Example/TwoLoopsComposed.v` against baseline `ZZCmpBase.v`. Same protocol as
the main record (`vm_compute. solve_vc. Qed.` throughout; the composed arm's four
proofs carry residual-closing tactics before `Qed`, priced at ~0.004%).

---

# ADDENDUM 2026-09-05 — RE-MEASURED after branch refutation: the verdict REVERSES

Everything above is a correct record of the pre-`cfdcc92f` executor. On code at
or after that commit (`diagnostics/branch-refutation-payoff.md`) the numbers move
by an order of magnitude and **the conclusion flips sign**: composition now WINS
at every size we actually build.

## One-sentence finding

A segment contract costs **7.10 M words per cut** instead of ~108 M, so the
composed proof is **0.56× the flat unrolled VC** where it was 6.4–7.3×, the
break-even falls from **~71 trips per cut to ~4.65**, and §2.4's central
mechanism — "the expense is the unknown counter, 9.19×" — is now **1.006×**.

## Calibration

The flat arms cannot be affected by the fix (trip count concrete, every branch
decided by computation), so they are the control that the rig and tree are the
same objects the original record measured:

| arm | published | now | delta |
|---|---:|---:|---:|
| flat 1-loop, N=8 | 15.632 | 15.632 | **+0.00%** |
| flat 1-loop, N=16 | 27.862 | 27.862 | **−0.00%** |
| flat 2-loop, T=32 | 54.042 | 54.041 | **−0.00%** |

Exact to the last published digit. Baselines: 606,197,695 (`ZZCmpBase`),
606,210,788 (`ZZFlatBase`), 606,211,196 (`ZZF2Base`); `ZZFlatCommon.vo` /
`ZZF2Common.vo` rebuilt first (the stale-`Common` trap this file documents).

## Results

| arm | published | now | change |
|---|---:|---:|---:|
| `cdBody` (segment contract) | 97.95 | **10.879** | −88.9% |
| `cdFinal` (segment contract) | 83.44 | **8.137** | −90.3% |
| composed, 1 loop (2 contracts) | 177.96 | **15.653** | −91.2% |
| composed, 2 loops (4 contracts) | 394.61 | **29.857** | −92.4% |
| `ZZCmpBodyPin` (pinned ablation) | 10.66 | 10.811 | +1.42% |

| | before | after |
|---|---:|---:|
| composed / flat, 1 loop at N=16 | 6.39× | **0.562×** |
| composed / flat, 2 loops at T=32 | 7.30× | **0.552×** |
| crossover, 1 loop | N ≈ 114 | **N ≈ 8.0** |
| crossover, 2 loops | T ≈ 247 | **T ≈ 16.7** |
| marginal cost of one extra cut | 108.33 M | **7.102 M** (15.3× cheaper) |
| break-even trips per cut | ~71 | **~4.65** |

The marginal figure is the clean one: it is
`(2-loop composed − 1-loop composed)/2`, i.e. two extra segment contracts on the
same rig, so every shared cost cancels.

## §2.4 is RETRACTED: the unknown counter is no longer the story

§2.4 concluded, in bold, *"That is the whole story. The expense of a segment
contract is not its size, its table, or its chunk inventory — it is that the
executor must reason about a value it does not know,"* on a measured 9.19× gap
between a symbolic and a pinned counter.

| | before | after |
|---|---:|---:|
| `cdBody` (symbolic `k`) / `ZZCmpBodyPin` (`k` = 5) | **9.19×** | **1.006×** |

Post-fix a symbolic counter costs **0.6%** more than a pinned one on this rig
(1.16× on `prefix-length-cost.md`'s `pbody`/`pbodyPin` rig). The 9.19× was never
the cost of *not knowing* the counter — it was the cost of the infeasible branch
that not knowing it left live, and the solver now refutes that branch against the
path condition directly. Pinning was one way to kill the branch; refuting it is
another, and it does not require knowing the value.

## What this means

- **"Cut sparingly — every cut costs ~90 M" is RETRACTED.** A cut costs ~7 M and
  pays for itself after ~5 trips. Cut where it makes the proof clearer.
- **Composition is no longer a loss at the sizes we build.** It wins from ~8
  trips (one loop) / ~17 total trips (two loops); `CountdownComposed` at N=16 is
  now 0.56× the flat VC rather than 6.4×.
- **U11's two-loop retraction stands on its own facts but not on its numbers.**
  There is still no superadditivity to recover here (§ADDENDUM 2026-09-04's
  0.970× is a property of the flat arms, which have not moved). What changed is
  that composition no longer needs superadditivity to be worth doing.
- **The break-even is now nearly K-independent.** The old scoping note said
  break-even was ~60 trips at K=2 but ~970 at K=66, because the per-segment cost
  was quadratic in surrounding program length. That quadratic is 3544× smaller
  now, so a K=66 segment costs ~1.36× a K=2 one and the break-even goes ~4.65 →
  ~6.3 trips. (Estimate: it combines this rig's marginal cut cost with
  `branch-refutation-payoff.md`'s P-law, not a single measurement.)
- **Still open, unchanged:** the case where the flat arm does not terminate
  (`muladd` mlen=2, `check_scalar` — symbolic base, large inventories). That
  argument for the technique was always independent of these numbers and is
  now joined by a positive one.

## Caveats

- The "before" column is this file's published record, not a same-session BASE
  re-run. The three flat arms reproducing to ≤0.01% is what licenses that.
- **The split-vs-together consistency check changed shape** and should not be
  reused as a proxy: `cdBody + cdFinal` was +1.93% over the composed measurement
  and is now **+21.49%**, because each contract's own cost fell ~10× while the
  shared elaboration did not. Use the marginal (7.102 M/cut), not the sum.
- `ZZCmpBodyPin` moved **+1.42%** (151k words) on an arm the refutation rule
  cannot help — an order of magnitude more than the 10,228-word tax measured on
  `pbodyPin`. Most likely the `formula_eqb` `formula_propeq` clause landing in
  the same commit, which changes which formulas discharge. Small, and in the
  costs-slightly-more direction; not chased.
- All arms here have 2–4 instruction tables.

## Files

Arms: `ZZM_cdbody.v` / `ZZM_cdfinal.v` (copies of `ZZCmpBody`/`ZZCmpFinal` with
the now-dead residual closers stripped — post-fix `solve_vc` closes those VCs
outright), `ZZM_cmp1.v` / `ZZM_cmp2.v` (copies of `Example/CountdownComposed.v`
and `Example/TwoLoopsComposed.v`), plus the unmodified `ZZFlat_N*`, `ZZF2_N16`,
`ZZCmpBodyPin` and the three baselines.

