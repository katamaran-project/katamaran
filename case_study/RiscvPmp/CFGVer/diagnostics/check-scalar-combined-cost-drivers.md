# check_scalar combined (loop1 + loop2) cost drivers

Status: **Diagnostic record. Originally 2026-08-13; substantially re-measured
and re-concluded 2026-08-14.** The 2026-08-13 reading is kept, marked
superseded, at the bottom.

**One-sentence finding (2026-08-15, ROOT-CAUSED; FIXED 2026-08-16):**
combining check_scalar's two loops into one flat VC cost **5.5–18.6× the sum
of the two loops measured separately**, and the dominant part was a specific,
fixable defect — **the solver did not refute `bvadd c₁ p = bvadd c₂ p` for
distinct literals `c₁ ≠ c₂` on the `formula_propeq` path**, so a
base-relative pointer-compare loop exit left one provably-dead fall-through
path per trip and **everything sequenced after the loop was re-verified under
every one of them**. The residual-goal count obeyed exactly
`A_first + A_second × T_first` (verified to the goal on three
configurations). **Fixed** by adding cancellation to that path: 92 → 29
goals, up to 9.8× cheaper, superadditivity 18.60× → 1.90×, gate green. What
remains is the independent **1.5–1.9× chunk-inventory** effect of §6, which
is what a concrete base leaves too.

**Prior framing, superseded 2026-08-15:** the 2026-08-14 version of this line
attributed the dominant factor to a diffuse "symbolic-base amplification of
2.8–7.2×" and asserted it was "not more residual goals". The magnitudes were
right; the causal claim was wrong on both counts — it *is* more residual
goals, multiplicatively so, and it has a single named cause.

---

## 0. Read this first: the protocol trap that invalidated two tables

**Every cost comparison here must hold the tactic protocol fixed.** The
pre-existing standalone probes (`ZZByteLoop{1,2}N*.v`) end

```coq
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
```

while every probe written for this investigation ends

```coq
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
```

The difference is not cosmetic: `solve_symbase_fetch` is extra work, and a
real `Qed` **re-runs the whole executor** through the VM cast (≈ a second
`vm_compute`, see `cfgver-executor`). Comparing a combined-program numerator
measured one way against a sum-of-parts denominator measured the other way
inflates the denominator and *understates* the superadditivity. This happened
twice during this session before it was caught; §7 records both retractions.
When adding a probe here, copy an existing probe's `Proof.` line verbatim.

Three further metric hazards, all hit live:

- **`top_heap_words` is quantized and floor-limited.** Across 12 runs it took
  only seven distinct values with ~15% gaps, and the ~4.8 GB import closure
  means anything whose live set fits in the existing heap reads as *identical
  to the floor*. This produced a confident "loop 1 is free at every N", which
  is false — loop 1's allocation grows 0.8 → 2.7 G over N=4→16. Use
  `allocated_words` (deterministic, no floor) for cost, and OS peak RSS only
  for feasibility.
- **Peak RSS saturates near the machine ceiling**, compressing exactly the
  largest effects: at M16/N4 it reported 3.49× superadditivity where
  allocation reported 18.60×.
- **Peak RSS also PLATEAUS with N, so it must not be extrapolated to project
  feasibility.** On the m=n diagonal it is 9.51 GB at N=16 and 9.50 GB at
  N=32 — flat — while allocation grows 3.8×. Every "N is infeasible, it would
  need X GB" claim in this file's history came from extrapolating RSS, and
  each was wrong: `m=n=16` was called infeasible and now runs, and `m=n=32`
  was projected over the ceiling and runs at 9.50 GB. Project from
  allocation and time; quote RSS only for configurations actually run.
- **A failed compile reports ~baseline allocation, i.e. reads as nearly
  free.** A mis-set `cd` in a backgrounded subshell produced six such
  "measurements" at 1,447,863 words. Gate on `Error` as well as on
  `Finished transaction`.

Baseline (imports only): `allocated_words` **593,774,593**, peak RSS
**4.02 GB**. All allocation figures below are net of that baseline, in G
words.

## 1. The rig, and what it does NOT model

`ZZCombinedCommon.v`: check_scalar's real loop 1 (4 instructions) followed by
real loop 2 (13 instructions) in one 17-instruction list, parametric on the
two trip counts `m`, `n` **independently** (the real function has `m = n =
klen`). Chunk inventory: 17 instruction chunks, 11 register chunks, and
`m + 2n` byte cells (`k1` gives `m`, `k2` gives `n`, `n2` gives `n`; each
byte-spec word entry yields four `ptstomem 1` chunks). Steps `S = 4m + 13n`.

**Two deliberate departures from the real function, both still untested:**

1. **Loop 2 reads its own `k2[]`, not loop 1's `k[]`.** The real function's
   loop 2 re-reads the array loop 1 just walked, so real `H_data = m + n`
   with cells consumed and re-produced by *both* loops. The rig's header
   states this was done "to avoid address-aliasing complexity that isn't
   needed to answer the cost question" — that assumption is exactly what is
   unverified. If the interaction lives in aliasing, this rig cannot see it.
2. **The whole-function figures this file was originally written against are
   not comparable to it.** `PLAN-check-scalar-full.md` §5's "2.81×/3.78×" are
   **user CPU time, with a real `Qed`, on the real 35-instruction function, at
   N=2→4→8**. The rig's numbers are `allocated_words`, `Admitted`, on a
   synthetic 17-instruction composition, at N=4→8→16. Different metric,
   different N range, different program — and since the ratios rise with N,
   comparing a 2→4 ratio against a 4→8 one compares different parts of the
   curve. Do not quote a gap between those two families as a finding.

## 2. The grid (parametric base, `Admitted` protocol)

| m | n | steps | allocation | `vm_compute` | `solve_vc` | peak RSS |
|---|---|---|---|---|---|---|
| 4 | 4 | 68 | 19.092 | 32.5 s | 31.6 s | 7.70 GB |
| 8 | 4 | 84 | 40.757 | 75.0 s | 62.7 s | 8.31 GB |
| 4 | 8 | 120 | 35.632 | 91.7 s | 45.4 s | 8.46 GB |
| 8 | 8 | 136 | 76.445 | 222.8 s | 95.4 s | 9.68 GB |
| 16 | 4 | 116 | 92.300 | 190.0 s | 134.6 s | 9.85 GB |
| 4 | 16 | 224 | 85.024 | 361.5 s | 82.1 s | 10.29 GB |

`m = n = 16` was not attempted AT THE TIME: `m = n = 8` already peaked at
~11 GB (`top_heap`) on a 14 GB box. **Superseded 2026-08-16** — after the
§5.5 fix both run comfortably; see §5.6. Every pre-existing point reproduced its
2026-08-13 value to ≤0.0004%, so `bop.mulx` does not touch check_scalar and
the old grid figures remain valid on their own footing.

**The diagonal, which 2026-08-13 left as its open item.** Predicting
`m=n=8` additively from the three cheaper points gives 57.30; measured
**76.45, +33%**. So the interaction is real and larger than the ~8–12% the
pinned single-axis sweeps suggested — as that record itself warned, those
sweeps could only bound it by inference.

**`solve_vc` is a scaling term here**, 25–40% of time and rising 31.6 → 134.6 s.
Everywhere else in this project it is a flat toll (`cfgver-executor`:
"7.90/6.42/10.50 — FLAT, a fixed toll, never a scaling term"). §5 explains it.

**Allocation and time disagree in direction** on which lopsided arm is worse:
allocation says `m16/n4` (92.3 vs 85.0), time says `m4/n16` (443.6 vs 324.6).
`vm_compute` tracks steps (1.64 vs 1.61 s/step, step ratio 1.93× ≈ cost ratio
1.90×) while `solve_vc` tracks loop-1 trips (8.58 vs 4.21 s/trip) — two stages
with opposite sensitivities, which is why a fit to the *total* is meaningless
(§7, retraction 3).

## 3. Order swap: position is the driver, not the loop

`ZZCombSwapCommon.v` reverses the two instruction blocks — loop 2 first, then
loop 1. Legitimate as a one-knob change because both loops' branch offsets are
self-relative and the two loops use disjoint registers (loop 1: A0–A3; loop 2:
A7/T0–T5), each initialised from the precondition. Same 17 instructions, same
inventory, same fuel, same data layout.

| config | loop 1 first | loop 2 first | swapping gains |
|---|---|---|---|
| m4 n4 | 19.1 G / 64 s | 9.9 G / 33 s | 1.92× alloc, 1.96× time |
| m16 n4 | 92.3 G / 325 s | 25.9 G / 95 s | **3.56× alloc, 3.40× time** |
| m4 n16 | 85.0 G / 444 s | 54.0 G / 249 s | 1.57× alloc, 1.78× time |

Within each order, the **first** loop's trip count is always the steeper axis:

| order | m 4→16 | n 4→16 | steeper axis |
|---|---|---|---|
| loop 1 first | **4.83×** | 4.45× | m — the first loop |
| loop 2 first | 2.61× | **5.44×** | n — the first loop |

So "loop 1's trips are intrinsically expensive" is **refuted**: what makes a
loop's trips expensive is running *before* another loop.

> **Superseded twice.** (1) 2026-08-15: this section originally closed with
> "no simple functional form fits — position-dependence is solid; the law is
> not." There IS an exact law; it is on *residual goals*, not allocation,
> which is why fitting allocation missed it (§5.5).
>
> (2) **OBSOLETE as of the 2026-08-16 fix — the effect itself is gone, not
> just its explanation.** Position-dependence WAS the dead-path
> multiplication, so removing that removes it. Re-measured post-fix:
>
> | config | loop 1 first | loop 2 first | swap gain |
> |---|---|---|---|
> | m16 n4 | 9.42 G | 9.45 G | **1.00×** (was 3.56×) |
> | m4 n16 | 21.61 G | 20.72 G | **1.04×** (was 1.57×) |
>
> Loop order no longer affects cost. The tables below are kept because they
> are what identified the mechanism, and because the ratio going to 1.00× is
> the cleanest available confirmation that the diagnosis was right — but
> **never quote 1.92×/3.56×/1.57× as current behaviour.**

Note the *feasibility* gain is much smaller than the throughput gain: at
m16/n4 swapping wins 3.56× in allocation but only 1.42× in peak RSS.
Reordering would not make `m=n=16` fit. (And the real function's order is
fixed by the algorithm, so this is a diagnostic, not a lever.)

## 4. Concrete base: the dominant factor, 18–59×

No concrete byte-granular generator exists (`gen_contract` is word-granular;
only `gen_contract_rel_bytes` is byte-granular) — as `PLAN-check-scalar-full.md`
§5 predicted, the contract can be hand-assembled from `gen_pre` +
`gen_mem_pre_bytes` + `asn_init_pc` + `exits_of_offs` +
`MkCFGVerifierContract` without touching `GenContract.v`
(`ZZCombConcCommon.v`, `ZZLoopsConcCommon.v`). One-knob discipline: the spec
lists are the existing `_rel` lists pushed through `concretize_reg` /
`concretize_mem`, so only the base changes.

| config | base | allocation | `vm_compute` | `solve_vc` | RSS above floor |
|---|---|---|---|---|---|
| m4 n4 | parametric | 19.09 | 32.5 s | 31.57 s | 3.68 GB |
| | **concrete** | **0.80** | 3.8 s | **0.21 s** | **0.29 GB** |
| m16 n4 | parametric | 92.30 | 190.0 s | 134.62 s | 5.83 GB |
| | **concrete** | **1.57** | 7.5 s | **0.38 s** | **0.54 GB** |
| m4 n16 | parametric | 85.02 | 361.5 s | 82.08 s | 6.27 GB |
| | **concrete** | **4.74** | 30.2 s | **0.66 s** | 1.80 GB |

18–59× less allocation, 14–41× less time, and `solve_vc` collapses by
125–358× to a fraction of a second. Peak RSS above floor drops 3.5–12.6×, so
**`m=n=16` is very likely feasible at a concrete base** — untested, and worth
testing before being believed, because `cfgver-executor` records a concrete
base as having a *steeper* exponent (1.63) on a different reproducer. Do not
extrapolate the three points here.

The owner has explicitly chosen to keep the parametric base
(`PLAN-check-scalar-full.md` §5), so this is a diagnostic about where the cost
lives, not a sanctioned fix.

## 5. Splitting the penalty: symbolic base vs. chunk inventory

Matched protocol on both bases (`Admitted`, no `solve_symbase_fetch`):

| config | base | loop 1 | loop 2 | sum | combined | multiplier |
|---|---|---|---|---|---|---|
| m4 n4 | parametric | 0.580 | 2.924 | 3.504 | 19.092 | **5.45×** |
| | concrete | 0.041 | 0.370 | 0.411 | 0.796 | 1.94× |
| m16 n4 | parametric | 2.039 | 2.924 | 4.963 | 92.300 | **18.60×** |
| | concrete | 0.238 | 0.370 | 0.607 | 1.569 | 2.58× |
| m4 n16 | parametric | 0.580 | 13.726 | 14.306 | 85.024 | **5.94×** |
| | concrete | 0.041 | 2.856 | 2.897 | 4.739 | 1.64× |

So the symbolic base contributes an amplification of **2.8× / 7.2× / 3.6×**
on top of a residual **1.6–2.6×**. The amplification is worst where loop 1 is
large, which fits: loop 1 introduces one new byte address every 4
instructions against loop 2's two per 13 — the highest new-address density
per step — and symbolic-base bounds are per-address.

**It is not mainly deferred residual goals.** Splitting the superadditivity by
stage: `vm_compute` **26.4×** parametric vs 2.84× concrete; `solve_vc` 11.4×
vs 2.0×. The *executor* is the more superadditive stage. Corroborated
independently in §6: dead declarations add `vm_compute` cost and **zero**
`solve_vc` cost.

## 5.5. ROOT CAUSE: an unrefuted pointer equality multiplies the VC

Dumping the residual goals themselves (`ZZVCDump_*.v`) turns the whole
symbolic-base story from a magnitude into a mechanism.

**Every residual has one shape** — an access upper bound
`0 ≤ 1024 − (K + unsigned (offset ⊕ v))`, `K=4` for a 4-byte instruction
fetch, `K=1` for an `LBU`. Nothing else survives `solve_vc`. A concrete base
never produces them (`unsigned` of a literal just computes), which is why
`solve_vc` measures 0.000 s there.

**One loop: exactly one goal per distinct address.**

| | residual goals | distinct (K, offset) | addresses touched |
|---|---|---|---|
| loop 1 alone, N=4 | 8 | 8 | 4 instr + 4 bytes |
| loop 2 alone, N=4 | 21 | 21 | 13 instr + 8 bytes |

No duplicates. Note this is per *address*, not per step: loop 1 executes 16
steps but its 4 instruction addresses recur across trips and collapse.

**Two loops: the second loop's whole block, duplicated `T_first` times.**

| | goals | distinct | structure |
|---|---|---|---|
| combined m4/n4 | **92** | 29 | 8 (loop 1, 1×) + **4 × 21** (loop 2) |
| combined m8/n4 | **180** | 33 | 12 (loop 1, 1×) + **8 × 21** (loop 2) |
| swapped m4/n4 | **53** | 29 | 21 (loop 2, 1×) + **4 × 8** (loop 1) |

The copies sit at stride 21 (goals 9, 30, 51, 72) — four consecutive complete
copies of loop 2's block. The law is

```
residual goals  =  A_first  +  A_second × T_first
```

with `A` the addresses a loop owns and `T_first` the FIRST loop's trip count.
Zero fitted parameters, exact on all three configurations, including the
swapped rig where the multiplied group is the one that moved to the end.

**Why.** Loop 1 walks `A0` from `p+0x44` to `A1 = p+0x48` and exits on
`BNE A0 A1`. At the end of *every* trip the executor forks, and the
fall-through arm assumes a pointer equality. Diffing the four copies'
contexts (they are otherwise identical) shows exactly one extra hypothesis
each:

| copy | assumed on that path | true? |
|---|---|---|
| goal 9 | *(none)* | the real exit, after trip 4 |
| goal 30 | `p+0x47 = p+0x48` | **impossible** |
| goal 51 | `p+0x46 = p+0x48` | **impossible** |
| goal 72 | `p+0x45 = p+0x48` | **impossible** |

Three of the four are `bvadd c₁ p = bvadd c₂ p` with `c₁ ≠ c₂` — decidable
arithmetic, provably false. **The solver does not refute them**, so instead of
collapsing to `SymProp.block` (as `cfgver-executor` describes for a refuted
fork) each dead branch stays live and the entire remainder of the program is
symbolically executed and verified underneath it.

Four consequences worth stating plainly:

- **It is linear, not exponential.** Each trip contributes one dead path and
  they do not compound: `T_first` paths, not `2^T_first`. The blow-up is
  multiplicative only on what *follows* the loop.
- **It is positional by construction**, which is what §3's order swap was
  seeing: swapping decides which loop gets multiplied by the other's trip
  count. Predicted goal ratio at m16/n4 is 336/80 = 4.2 against the measured
  3.56× allocation saving.
- **A single loop hides it.** Loop 1 alone shows no duplication *in the goal
  count* because its dead paths reach the program end immediately — but they
  are still built, which is part of why even a single loop pays a 4.4–14.2×
  parametric penalty (§5).
- **It explains why the base penalty is program-dependent** (§4's 18–59× for
  check_scalar vs §"KSL" 3.4–4.9%). check_scalar's loops exit on
  *base-relative pointer compares*, so they duplicate. `key_schedule_loop2`
  exits on a **public pinned counter** (`A4, true, PVConst`), which folds to
  a literal and IS decided in place — so it has no duplication at all, and
  its symbolic-base cost is only the per-address bounds.

### Exactly why it is not refuted: the WRONG FORMULA CONSTRUCTOR

Localised 2026-08-16. Three facts, in order:

1. **A cancellation rule exists and is correct.** `try_bvadd_cancel`
   (`Solver.v:2550`) is wired into `simplify_relop`'s `eq` and `neq` arms
   (2577/2584), and `bvadd_cancel_pair` (2525) matches exactly
   `bvadd (val v₁) s` vs `bvadd (val v₂) s`. It is gated on `secLeakT s`
   (2559).
2. **That gate is NOT the blocker.** Adding `secLeakvar "p"` to the
   precondition — so the base is explicitly leakable — changes the residual
   count by **nothing**: 92 → 92 at m4/n4 and 180 → 180 at m8/n4, allocation
   within 0.006% (`ZZLeakBaseCommon.v`, `ZZLeakBase_M{4,8}_N4.v`). A
   plausible-looking hypothesis, measured dead. Don't re-run it.
3. **The loop exit produces a DIFFERENT formula constructor.** `Formula`
   (`Formulas.v:62-71`) has both `formula_relop` and `formula_propeq`, with
   different interpretations (`Formulas.v:138`):

   | constructor | `instprop` |
   |---|---|
   | `formula_relop op t1 t2` | `match eval_relop_relprop … with SyncVal p => p \| NonSyncVal _ _ => False end` |
   | `formula_propeq t1 t2` | `inst t1 ι = inst t2 ι` — a bare Coq equality on RelVals |

   The dumped hypothesis is the **bare** form
   (`bvadd (SyncVal [bv 0x47]) v = bvadd (SyncVal [bv 0x48]) v`), so the exit
   emits `formula_propeq`. Its simplifier arm (`Solver.v:2784`) is
   `simplify_propeq Term_eqb …`, which does syntactic comparison and
   structural decomposition and **never calls `try_bvadd_cancel`**. The rule
   is fine; it is simply not on this path. (Note `formula_eq` is *notation*
   for `formula_relop bop.eq`, `Formulas.v:409` — easy to mistake for the
   propositional one.)

### The fix — LANDED 2026-08-16, gate green

`try_bvadd_cancel_propeq` + `try_bvadd_cancel_propeq_spec` (`Solver.v`,
next to the relop original), wired into `simplify_formula`'s
`formula_propeq` arm ahead of `simplify_propeq`. Closed `Qed`, no new
axioms.

**Residual goals — exactly the predicted collapse:**

| | before | after |
|---|---|---|
| loop 1 alone N=4 | 8 | 8 (unchanged) |
| loop 2 alone N=4 | 21 | 21 (unchanged) |
| combined m4/n4 | **92** | **29** = 8+21 |
| combined m8/n4 | **180** | **33** = 12+21 |

The `A_second × T_first` term is gone and the single-loop counts are
untouched, so the rule fires only where it should.

**Cost, parametric base:**

| config | allocation | time | peak RSS | superadditivity |
|---|---|---|---|---|
| m4 n4 | 19.09 → 5.32 G (3.6×) | 64 → 19 s | 7.70 → 5.12 GB | 5.45× → **1.52×** |
| m16 n4 | 92.30 → 9.42 G (**9.8×**) | 325 → 36 s (8.9×) | 9.85 → 5.87 GB | 18.60× → **1.90×** |
| m4 n16 | 85.02 → 21.61 G (3.9×) | 444 → 111 s | 10.29 → 8.39 GB | 5.94× → **1.51×** |

The gain scales with the multiplier removed — largest where `T_first` was
largest — exactly as the law predicts. What remains (~1.5–1.9×) is the
chunk-inventory effect of §6, i.e. the parametric base now costs
essentially nothing extra *for composition*. `m16/n4` at 5.87 GB is well
under the ceiling that made larger configurations infeasible.

`./scripts/gate.sh` passes: build clean, no holes, 14 end theorems
axiom-clean. That run was also the first full rebuild of the heavy Iris
branch since `bop.mulx`, so both changes are covered.

**Why it needs no guard.** For this constructor cancellation is sound
**unconditionally**, in both directions — no `secLeakT`:

`inst (bvadd (val c) s) ι = liftBinOp bvadd (SyncVal c) (inst s ι)`, so

| `⟦s⟧ ι` | the two sides | equal iff |
|---|---|---|
| `SyncVal sv` | `SyncVal (c₁+sv)` vs `SyncVal (c₂+sv)` | `c₁ = c₂` (bv cancellation) |
| `NonSyncVal sl sr` | `NonSyncVal (c₁+sl) (c₁+sr)` vs `NonSyncVal (c₂+sl) (c₂+sr)` | `c₁ = c₂` (constructor injectivity, then cancellation componentwise) |

The `secLeakT` guard on `try_bvadd_cancel` exists only because
`formula_relop`'s interpretation has the `NonSyncVal ⇒ False` wall, which
makes the *hold* direction unsound for a secret operand — and even there the
*refute* direction needs no guard. `formula_propeq` has no wall, so both
directions are unconditional. `liftBinOpRV` (`TypeDecl.v:268`) is what pins
this down: it returns `SyncVal` only when both inputs are sync and never
collapses `NonSyncVal b b`.

Keep the `op ∈ {eq, neq}` restriction on the *relop* rule: cancellation is
genuinely unsound for the ordering relops because bv addition wraps
(`Solver.v:2543`).

**Not verified:** that the real `check_scalar` — whose loop 2 re-reads loop
1's array, the aliasing this rig removes (§1.1) — duplicates the same way.

### 5.6. The diagonal m = n — the barrier is gone (2026-08-16)

`m = n` is the real function's coupling (`m = n = klen`) and the case that
could not be run at all before: `m=n=8` peaked ~11 GB and `m=n=16` was
projected 15–17 GB total. Post-fix, both bases:

| N | base | allocation | time | peak RSS | ×prev N |
|---|---|---|---|---|---|
| 4 | parametric | 5.32 G | 18.9 s | 5.12 GB | — |
| 4 | concrete | 0.80 G | 3.9 s | 4.32 GB | — |
| 8 | parametric | 11.10 G | 45.2 s | 6.19 GB | 2.09× |
| 8 | concrete | 2.05 G | 11.6 s | 4.80 GB | 2.57× |
| 16 | parametric | 30.87 G | 159 s | 9.51 GB | 2.78× |
| 16 | concrete | 6.67 G | 43.9 s | 6.30 GB | 3.25× |
| **32** | **parametric** | **116.21 G** | **948 s** | **9.50 GB** | 3.76× |
| **32** | **concrete** | **28.82 G** | **268 s** | **9.00 GB** | 4.32× |

**`m=n=32` completes at the PARAMETRIC base** — the real function's own
`klen`, on the base the project wants to keep. Before the fix `m=n=8` was the
ceiling and `m=n=16` was projected infeasible.

Two things to carry forward rather than over-read:

- **Growth is superlinear and still accelerating at every doubling** —
  parametric 2.09 → 2.78 → 3.76×, concrete 2.57 → 3.25 → 4.32×. There is no
  settled exponent to quote. This is the `H·S` chunk-inventory law of §6
  (on the diagonal BOTH factors grow with N), now unmasked by the removal of
  the goal multiplication: the fix moved the wall out ~three doublings
  without removing it.
- **PEAK RSS PLATEAUS — and this invalidates how feasibility was projected
  here.** Parametric RSS is 9.51 GB at N=16 and **9.50 GB at N=32**, flat,
  while allocation grew 3.8×. Peak *live set* is not what scales; the run
  churns rather than accumulates, which is also why N=32 survived with the
  machine fully committed. Every earlier "N is infeasible because it needs
  11–13 GB above floor" projection in this file extrapolated the wrong
  quantity. Project feasibility from allocation and time; treat RSS as a
  measured fact about a configuration that has actually been run.
- **The base penalty SHRINKS with N**: parametric/concrete is 6.7× / 5.4× /
  4.6× / 4.0× at N=4/8/16/32. The concrete base has the steeper exponent, as
  `cfgver-executor` records for a different reproducer, so a concrete-base
  measurement flatters itself most at small N. Extrapolating the trend the
  two converge somewhere past N=128 — worth knowing before trading the
  parametric base away for speed.
- **The projections in this section's earlier revision were wrong in the
  usual direction.** N=32 was projected at ~22 G / ~2.4 min (concrete) and
  ~90 G / ~8 min / over-ceiling (parametric); measured 28.8 G / 5.2 min and
  116.2 G / 21.8 min / comfortably under. Allocation +31%/+29%, time 2.2×/
  2.7×, and the feasibility call outright wrong. Four of this session's own
  projections erred optimistically; assume the same of the next one.

### 5.7. WHICH NUMBERS IN THIS FILE ARE POST-FIX — read before quoting any

The 2026-08-16 solver fix (§5.5) changed the cost model, and **the file was
NOT re-measured wholesale.** Status of every measurement block:

| section | measured | post-fix? |
|---|---|---|
| §5.5 goal counts (92→29, 180→33) | 2026-08-16 | **yes** |
| §5.6 the m=n diagonal, N=4..32, both bases | 2026-08-16/17 | **yes** |
| §5.8 the three-arm bound-VC ablation (P/A/C) | 2026-08-17 | **yes** — arms P and C at m4n4/m8n4/m4n8/m8n8 re-measured from scratch that day; the m16n16 and m32n32 P/C values are §5.6's, reused after reproducing three of them to ≤0.1% |
| §5.5 cost table (m4n4, m16n4, m4n16) | 2026-08-16 | **yes** |
| §3 order swap | 2026-08-14 | **OBSOLETE** — effect measured gone (1.00×) |
| §2 the 6-point grid | 2026-08-14 | **no** — pre-fix; m4n4/m16n4/m4n16 superseded by §5.5's table |
| §4 concrete-vs-parametric (18–59×) | 2026-08-14 | **no** — pre-fix, and it conflated the goal multiplication with the base; §5.6's 4.0–6.7× is the post-fix figure |
| §5 the two-factor split (5.45/18.60/5.94×) | 2026-08-16 | pre-fix *by construction* — it is what the fix was measured against |
| §6 chunk-inventory probes (padding, inventory swap, H·S) | 2026-08-14 | **no** — but these were taken at a CONCRETE base, where no dead paths existed, so the fix should not move them. Argued, not measured. |

Sibling diagnostics **not** revisited after the fix:
`check-scalar-loop1-cost-drivers.md` and `check-scalar-loop2-cost-drivers.md`
(both single loops with base-relative pointer-compare exits, so their dead
paths existed but died at the program end — the fix plausibly makes them
cheaper, unmeasured), and `key-schedule-loop2-cost-drivers.md` (exits on a
public pinned counter, so it never had dead paths; unaffected by argument,
not by measurement).

### 5.8. Splitting the symbolic base itself: the per-address bound VCs are 76–90% of it (2026-08-17)

`PLAN-fetch-bound-vcs.md` Phase 1. §5.6 leaves the symbolic base as a 4.0–6.7×
constant factor without saying *what inside it* costs. Two candidate
mechanisms, and they need different fixes:

- **bound obligations** — one `0 ≤ lenAddr − (K + unsigned (off ⊕ p))` per
  distinct address touched, emitted by `Spec.v`'s `sep_contract_fetch_instr`
  (upper bound, `K = 4`), `sep_contract_mem_read` and
  `sep_contract_checked_mem_read` (`K = bytes`). Removable in principle by
  discharging them in the solver against the precondition's single base bound.
- **symbolic address terms** — every address is `bvadd (val off) p` rather than
  a literal, everywhere, all the way through. NOT removable by any VC work.

**Three arms, one knob each.** The discriminator is an ABLATION, not the
`PVConst`-pinned base the plan originally sketched: a `PVConst` base *is* a
concrete base, so it moves both axes at once and merely reproduces arm C.
Instead the three upper-bound conjuncts were deleted from `Spec.v` (arm A),
leaving every address term symbolic and byte-identical while the obligations
are never emitted:

| arm | base | bound obligations | reads as |
|---|---|---|---|
| **P** | symbolic | emitted | today's parametric cost |
| **A** | symbolic | **deleted at source** | ceiling of the proposed fix |
| **C** | concrete | never emitted (`unsigned` of a literal computes) | §5.6's concrete arm |

Arm A is deliberately **unsound** — it also forces `valid_checked_mem_read` to
`Admitted`, since the body can no longer justify the access. It is a cost
probe, nothing else; the tree was reverted and rebuilt after measuring.

**Control, and it is the reason to believe the ablation is on-target:**
residual goals go **29 → 0** at m4n4 and **37 → 0** at m4n8. Exactly the
obligations disappeared and nothing else was left behind.

**Allocation, G words net of baseline** (P/C at m4n4, m8n4, m4n8, m8n8
measured 2026-08-17; P/C at m16n16 and m32n32 are §5.6's, which this session
reproduced at m4n4 to 0.03%, m8n8 to 0.04% and C-m8n8 to 0.1%):

| shape | S | addrs | **P** | **A** | **C** | P/A = ceiling | (P−A)/(P−C) | A/C |
|---|---|---|---|---|---|---|---|---|
| m4 n4 | 68 | 29 | 5.325 | 1.229 | 0.798 | 4.33× | **90.5%** | 1.54× |
| m8 n4 | 84 | 33 | 6.541 | 1.609 | 1.025 | 4.07× | 89.4% | 1.57× |
| m4 n8 | 120 | 37 | 9.407 | 2.732 | 1.721 | 3.44× | 86.8% | 1.59× |
| m8 n8 | 136 | 41 | 11.105 | 3.308 | 2.048 | 3.36× | 86.1% | 1.62× |
| m16 n16 | 272 | 65 | 30.87 | 11.274 | 6.67 | 2.74× | 81.0% | 1.69× |
| **m32 n32** | 544 | 113 | **116.21** | **49.758** | **28.82** | **2.34×** | **76.0%** | 1.73× |

**The `vm_compute` stage is where this had to be settled**, because roughly
half the parametric penalty is spent before `solve_vc` starts, so a faster
*tactic* could never recover it. User CPU:

| shape | `vm_compute` P → A → C | obligation share of the vm gap | `solve_vc` P → A → C |
|---|---|---|---|
| m4 n4 | 10.09 → 5.37 → 3.86 s | 75.8% | 9.91 → 0.31 → 0.23 s |
| m8 n4 | 13.28 → 7.07 → 5.17 s | 76.6% | 12.32 → 0.34 → 0.28 s |
| m8 n8 | 32.46 → 16.44 → 11.52 s | 76.5% | 13.98 → 0.50 → 0.49 s |

So **~76% of the parametric `vm_compute` penalty is obligation cost**, stable
to ±0.4 points across three shapes, and `solve_vc` collapses to the concrete
arm's value (97%+ of it was obligations). The mechanism is real and it is the
dominant part of the base penalty at every size measured.

**But the share DECAYS with N, and that is the finding that matters.**
90.5 → 86.1 → 81.0 → 76.0% on the diagonal, ≈ −4.8 points per doubling, so
the achievable ceiling falls 4.33× → **2.34× at the real `klen = 32`**. The
obligations are per-ADDRESS (`17 + m + 2n`, §5.5) while total cost is
`H^(1+ε)·S` (§6.5) — addresses grow linearly, cost grows superlinearly, so
this mechanism is a *shrinking* fraction of the whole by construction. Any
figure quoted for it must name its N.

**Held-out fit check** (required by `cfgver-scaling-diagnostics`, and this
file's history is mostly of projections erring optimistically): fitting the
share linearly in `log₂N` on the diagonal N=4 and N=8 ONLY predicts 81.7% at
N=16 (measured 81.0, **error 0.7 pts**) and 77.3% at N=32 (measured 76.0,
**error 1.3 pts**), i.e. a ceiling of 2.39× against the measured 2.34×. Two
doublings out, 2% optimistic on the ceiling — the smallest projection error
recorded in this file, and still in the usual direction.

**What the ceiling is worth, stated as headroom rather than a ratio.**
Diagonal cost grows 3.76× per doubling at N=16→32, so a 2.34× saving buys
`ln 2.34 / ln 3.76` = **0.64 of a doubling** in reachable N. The real fix
lands strictly below that ceiling: the ablation removes the obligation's
*construction* too, whereas a solver rule still builds `unsigned (off ⊕ p)`
before simplifying it away, and pays a recognizer on every formula it sees.

**Peak RSS, for feasibility only** (P / A / C): m4n4 5.12 / 4.35 / 4.32 GB;
m8n8 6.19 / 4.88 / 4.80; m16n16 9.51 / 6.54 / 6.30; m32n32 9.50 / **9.07** /
9.00. The N=32 plateau of §5.6 shows up in arm A as well, so the ablation is
not a feasibility lever either — it buys throughput, not headroom on this box.

**Third shape for the §5.5 residual law, while the rig was up.** Both
previously-measured points held n=4, so only the `m` coefficient of
`residuals = A_first + A_second` had ever been exercised. Moving `n` instead:

| shape | predicted `17 + m + 2n` | measured |
|---|---|---|
| m4 n4 | 29 | 29 (re-measured 2026-08-17) |
| m8 n4 | 33 | 33 (2026-08-16) |
| **m4 n8** | **37** | **37** |

Still zero fitted parameters, now with both coefficients tested.

## 6. The residual 1.6–2.6× is chunk inventory

**Padding probe** (`ZZPadVCCommon.v`) — loop 2 alone at *fixed* n=4, with `P`
extra byte cells declared past all code and live data, never read or written:

| dead cells | allocation | vs unpadded | marginal per word entry |
|---|---|---|---|
| 0 | 0.370 | 1.00× | — |
| 4 | 0.409 | 1.11× | 0.039 |
| 16 | 0.540 | 1.46× | 0.044 |
| 32 | 0.744 | 2.01× | 0.051 |
| 64 | **1.256** | **3.40×** | **0.064** |

Declaring 64 untouched cells triples the cost of a loop whose executed work
never changes, and the marginal cost per entry *grows* — superlinear in
declared size, consistent with the `subst_list`-transports-the-whole-heap
mechanism (`key-schedule-loop2-cost-drivers.md`). On a parametric base the
same 16 dead cells cost +0.611 G versus +0.170 G concrete (3.6× worse), and
`solve_vc` stays flat (6.68 → 6.60 s): **declared-but-unused resources cost at
execution time, not at discharge time.**

**Inventory-swap probe** (`ZZSkipCommon.v`) — the decisive one. Run **only
loop 2**, but with the entire combined inventory declared (entry pc set to
offset 16, past loop 1, whose four instructions stay resident and unreached):

| config | loop 2 alone | full inventory, same steps | cost of the extra chunks |
|---|---|---|---|
| m4 n4 | 0.370 | 0.644 | **1.74×** |
| m16 n4 | 0.370 | 0.796 | **2.15×** |
| m4 n16 | 2.856 | 4.439 | **1.55×** |

Identical executed work in each pair. **1.55–2.15× accounts for essentially
all of the 1.64–2.58× concrete-base residual.** Cleanest single point: within
this probe, m4/n4 → m16/n4 costs 0.644 → 0.796 (+24%) purely from 12 extra
declared byte cells, with loop 1 never executing in either run.

**Which chunks.** At m16/n4 loop 1's steps go from 24 to 52 resident chunks:
**+13 instruction**, +7 register, +8 byte. The padding probe varied only the
smallest of the three, which is why it explained just 18% of the excess; the
full inventory swap explains ~all of it. So the dominant term is **program
length** — `cfgver-executor` already states it: "program length L enters BOTH
— the heap holds one `ptstoinstr` chunk per instruction and S = L·N — so long
programs hurt worse than trip counts."

**Structural check, zero fitted parameters.** With `H` and `S` read straight
off the spec lists, `H·S` predicts the concrete-base residual as
1.65 / 2.02 / 1.30 against measured 1.94 / 2.58 / 1.64 — under by a
consistent ~1.2–1.3×, but right in magnitude and ordering. The cross term is
superadditive by construction: each loop's steps transport the other loop's
chunks.

**Failed probe, recorded so it is not repeated.** The intended twin — skip
loop 2 by adding an exit at loop 1's fall-through (offset 16) — **does not
skip anything**: it measured 92–96% of the full combined cost. The exit/execute
choice at each pc is **angelic** (`angelic_binary`), so an extra exit grants
permission to stop without preventing the execute branch from being built, and
`vm_compute` pays for constructing both. **Adding an exit is never a way to
prune construction cost in this executor.** Consequence: loop 1's steps under
the full inventory were never isolated, so the `combined − skip_l1` residual
(3.3–7.4× loop 1's standalone cost) still mixes inventory cost with any
genuine both-loops-executed interaction. To fix it, *minimise* loop 2 rather
than skip it — set `T0 = T1` at entry so it falls through after one trip,
keeping the full inventory resident.

## 6.5. The cost law, decomposed (2026-08-17)

With the goal multiplication gone, what remains was tested against the
`H · S` law directly. Three readings, and the answer is "mostly `H·S`, with a
superlinear chunk exponent":

**`cost / (H·S)` is flat across the mid-range, then drifts.** Post-fix
parametric, with `H = m + 2n + 28` and `S = 4m + 13n`:

| config | H | S | `cost/(H·S)` ×1e-4 |
|---|---|---|---|
| m4 n4 | 40 | 68 | 19.56 |
| m16 n4 | 52 | 116 | 15.62 |
| m8 n8 | 52 | 136 | 15.70 |
| m4 n16 | 64 | 224 | 15.07 |
| m16 n16 | 76 | 272 | 14.93 |
| m32 n32 | 124 | 544 | **17.23** |

Flat to ±3% over a 1.5× range of `H` and 2.3× of `S` — a genuinely good
account — with the small point high (constant overhead) and **m32n32 +15%**.
Same on the concrete arm, more sharply: 2.94 / 2.90 / 3.23 / **4.27**, flat to
N=8 then +47% by N=32.

**Chunks and steps are BOTH live factors.** Pin chunks at one cell (the KSL
`1-used` rows, pointer never advancing) and cost is *exactly* linear in steps
— held-out fit **+0.00%** at N=16. So halving executed steps halves cost
independently of chunk count. Chunks are what make it superlinear; steps are
what make it grow at all. On the diagonal both scale with N, hence the
apparent quadratic.

**The chunk dependence is SUPERLINEAR** — the padding probe is the clean test,
since it moves `H` at constant `S` (loop 2 alone, n=4 fixed, `P` dead cells,
`H = 28+P`, `S = 52`):

| H | cost | marginal per chunk |
|---|---|---|
| 28 | 0.370 | — |
| 44 | 0.540 | 0.0109 |
| 60 | 0.744 | 0.0127 |
| 92 | 1.256 | **0.0160** |

**+64% marginal cost per chunk** as `H` grows 3.3× at fixed `S`. Each added
chunk raises the cost of carrying every other one — exactly what `subst_list`
re-transporting the whole heap per world extension predicts. So the law is
nearer `H^(1+ε)·S`, which is why both arms under-account at N=32 and why the
diagonal's local exponent climbs past 2 instead of settling there.

**Failed attempt, recorded so it is not repeated:** fitting `c·H^a·S^b` on the
three corner points (m4n4, m16n4, m4n16) returns **a = −1.09**, physically
impossible. Those points are nearly collinear in log-space, so `a` and `b` are
not separable there. Separating them needs a point that moves `H` a lot at
fixed `S` *on the two-loop rig* — pad the combined rig at fixed m,n. The
single-loop padding probe above does it for one loop only.

### Ranking, as of 2026-08-17

| driver | status |
|---|---|
| **chunks × steps**, superlinear in chunks | the ONLY thing making cost grow with N |
| **symbolic base** | 4.0–6.7× constant factor, shrinking with N; not a scaling term. Largest remaining multiplier. **Decomposed 2026-08-17 (§5.8):** 76–90% of it is the per-address bound VCs (removable in principle, ceiling **2.34× at N=32** and falling with N), the rest is symbolic address terms (not removable). |
| access count | negligible — measured three ways (§5.5, §6) |
| term growth | closed by `peval` RECOGNIZERS (`mulx`/`coalesce`/`expand`); `ZZTermSim2.v` shows the unrecognized shape is `3^n`, so a new idiom reopens it |
| dead-path VC multiplication | closed by the `formula_propeq` cancellation (§5.5) |

Note the asymmetry in how the two closed items are closed: the dead-path fix
is structural (a sound rule, applies to any program), whereas term growth is
closed only for the SHAPES a recognizer matches. The latter is the one a new
example is most likely to reopen.

## 7. What this means

Ranked, for `check_scalar`'s whole-function target:

1. ~~Fix the unrefuted pointer equality (§5.5).~~ **DONE** — this was the
   dominant cost and, unlike everything else here, a *defect* rather than a
   design trade-off: three of four paths through a 4-trip loop were provably
   dead and fully verified anyway. Cancellation on the `formula_propeq` path
   turned `A_second × T_first` into `A_second`, worth up to 9.8×, with no
   change to the parametric base.
2. **The residual composition penalty is chunk inventory, ~1.6–2.6×**, driven
   by total resident chunks × steps, dominated by instruction chunks. Same
   mechanism as `key-schedule-loop2-cost-drivers.md`'s driver, so
   `plans/PLAN-loop-invariant.md`'s per-iteration contract addresses both:
   it would stop each loop's steps from carrying the other loop's chunks at
   all. This is what remains after (1), and it is a design change, not a bug
   fix.
3. **No cross-loop semantic interaction exists.** §5.5 gives an exact law for
   the goal multiplication and §6 accounts for the concrete-base residual
   with inventory alone. The two loops do not interact; the first one
   multiplies the second.

**A design rule that falls out of this**, worth applying to any future
example: **prefer a public pinned counter over a base-relative pointer
compare as a loop exit.** The counter folds to a literal and the branch is
decided in place; the pointer compare is not refuted and leaks one dead path
per trip into everything downstream. `key_schedule_loop2` uses a counter and
pays no duplication; both check_scalar loops use pointer compares and pay it.
That single difference is why the symbolic-base penalty is 3.4–4.9× on one
and 18–59× on the other.

### Retractions from the 2026-08-14 session

Measurements were sound in every case; the inferences were not.

- **RETRACTED: parametric additivity multipliers 3.91× / 13.55× / 3.64×.**
  Mixed protocol (§0) — parts included `solve_symbase_fetch` + `Qed`,
  combined did not. Replaced by 5.45× / 18.60× / 5.94× on matched protocol.
  The retracted figures are *understatements*; never requote them.
- **RETRACTED: RSS-based composition multipliers 3.04× / 3.49× / 1.40×.** Same
  protocol contamination, plus RSS saturation near the memory ceiling. Never
  requote.
- **RETRACTED: "cost is best modelled as linear in total trips (18% held-out
  error), and all product forms fit worse."** An artifact of fitting the
  *total*, which sums two stages with opposite sensitivities (§2). The
  per-stage reading supersedes it.
- **RETRACTED: "loop 1 is free — 0.00 GB above floor at every N."** A
  `top_heap_words` resolution artifact (§0). Loop 1 costs 0.26 / 0.33 / 0.72 /
  1.91 GB above floor at N=4/8/16/32.

## 8. Files (throwaway, not in `_CoqProject`)

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran <Common>.v
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "maxrss %M" \
  env coqc <same flags> <Runner>.v 2>&1 | grep -E 'allocated_words|maxrss|Error'
```

Subtract 593,774,593. One heavy proof per process; run sequentially.

| probe | files |
|---|---|
| grid, parametric | `ZZCombinedCommon.v` + `ZZComb_M{4,8,16}_N{4,8,16}.v` |
| order swap | `ZZCombSwapCommon.v` + `ZZCombSwap_M{4,16}_N{4,16}.v` |
| concrete base, combined | `ZZCombConcCommon.v` + `ZZCombConc_M{4,16}_N{4,16}.v` |
| concrete base, each loop alone | `ZZLoopsConcCommon.v` + `ZZL1Conc_N{4,16}.v`, `ZZL2Conc_N{4,16}.v` |
| parametric, each loop alone, matched protocol | `ZZL1ParamA_N{4,16}.v`, `ZZL2ParamA_N{4,16}.v` |
| dead-declaration padding | `ZZPadVCCommon.v` + `ZZPadC_PW{0,1,4,8,16}.v`, `ZZPadP_PW{0,4}.v` |
| inventory swap / failed skip | `ZZSkipCommon.v` + `ZZSkipL1_*.v` (works), `ZZSkipL2_*.v` (does not skip) |
| residual-goal dumps (§5.5) | `ZZVCDump_L1.v`, `ZZVCDump_L2.v`, `ZZVCDump_Comb.v`, `ZZVCDump_Comb84.v`, `ZZVCDump_Swap.v`, `ZZVCDump_Ctx.v` |
| bound-VC ablation (§5.8) | baselines `ZZFbBase.v` / `ZZFbBaseC.v`; residual counts `ZZFbCount_M4_N{4,8}.v`; arms P and A both reuse `ZZComb_M*_N*.v` (the ablation lives in `Spec.v`, not in the probe); arm C adds `ZZCombConc_M{8_N4,4_N8}.v`. **Arm A requires editing `Spec.v`** — comment out the upper-bound conjunct in `sep_contract_fetch_instr`, `sep_contract_checked_mem_read` and `sep_contract_mem_read`, `Admitted` the then-unprovable `valid_checked_mem_read`, rebuild `Spec → Verifier → Tables → Contracts → GenContract → Example/Prelude → ZZCombinedCommon`, and **revert plus rebuild afterwards** so no ablated `.vo` is left in the tree. |

Goal-inspection idioms used in the dumps, each of which silently lies if got
wrong (see `cfgver-scaling-diagnostics`): count with
`all: (let k := numgoals in idtac "n:" k)` — a BARE `numgoals` reports 1
whatever the truth, and `all: idtac "x"` prints exactly ONCE regardless of
goal count; dump per goal with
`all: (match goal with |- ?G => idtac "GOAL||" G end)`; and inspect one goal's
full context with the VERNACULAR `Show n.` — `n: Show.` does not parse, since
a goal selector takes a tactic and `Show` is a command.

**Not done, in priority order:**

0. ~~Add `bvadd` cancellation to the `formula_propeq` path.~~ **DONE
   2026-08-16, gate green** — see §5.5. 92 → 29 goals, 9.8× at m16/n4,
   superadditivity 18.60× → 1.90×.
1. ~~Concrete base at `m=n=8` and `m=n=16`~~ **DONE 2026-08-16** — §5.6. Both
   bases now reach `m=n=16`; the concrete exponent does steepen (its
   held-out linear fit misses by +46.5% vs parametric's +36%). Next rung is
   **N=32**, where the extrapolations disagree about feasibility
   (parametric likely over this box's ceiling, concrete likely reachable) —
   worth measuring rather than projecting, since this file's own history is
   mostly of projections being wrong.
2. **The aliasing question** (§1.1): the rig gives loop 2 a private `k2[]`
   where the real function re-reads loop 1's `k[]`. Untested; could be an
   additional driver the rig is blind to by construction.
3. **Isolate loop 1's steps under the full inventory** by minimising loop 2
   (§6), completing the decomposition that the failed `skip_l2` left open.
4. **Instruction-chunk padding** — dead instructions kept out of the executed
   path, to confirm directly that the +13 instruction chunks dominate the
   +7/+8 register/byte ones, rather than inferring it from the inventory swap.

---

## Superseded: the 2026-08-13 reading

Kept per this project's retraction discipline. **The measurements are real and
correctly taken; they are on the pre-`bop.mulx` baseline 434,833,198 and were
reproduced to ≤0.0004% on 2026-08-14 — it is the conclusion that no longer
holds.**

> **One-sentence finding:** holding either loop's size fixed and growing only
> the other shows a modest (~8-12%) superadditive penalty over that loop's own
> standalone doubling rate — much smaller than the dramatic 2.81×/3.78×
> superadditivity `PLAN-check-scalar-full.md` measured when **both** loops grow
> together, which means the bulk of the real superadditivity comes from an
> interaction between the two loops' sizes growing *simultaneously*.
>
> | m | n | minus baseline |
> |---|---|---|
> | 4 | 4 | 19,092,120,420 |
> | 8 | 4 | 40,757,145,526 |
> | 16 | 4 | 92,299,646,314 |
> | 4 | 8 | 35,632,243,366 |
> | 4 | 16 | 85,024,015,368 |
>
> Sweep A (loop 1 marginal, n=4): 2.13×, 2.26×. Sweep B (loop 2 marginal,
> m=4): 1.87×, 2.39×. Loop 2's doubling rate is 8-12% steeper inside the
> combined function than alone.

**What changed.** The ~8-12% figure is a *lower bound artifact of pinning one
loop at 4*, as that record correctly flagged; measured on the diagonal the
interaction is +33% over additive at `m=n=8`, and against the sum of parts the
penalty is 5.5–18.6×. The suspected mechanism — "loop 1's ambient heap
footprint still resident while loop 2 executes" — is **confirmed in substance**
(§6: chunk inventory is the residual driver) but was **not the bulk of the
cost**: the symbolic base was, and that was invisible to a single-base
experiment. The 2.81×/3.78× comparison the finding was framed against is
itself not commensurable with this rig (§1.2).
