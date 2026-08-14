# check_scalar combined (loop1 + loop2) cost drivers

Status: **Diagnostic record. Originally 2026-08-13; substantially re-measured
and re-concluded 2026-08-14.** The 2026-08-13 reading is kept, marked
superseded, at the bottom.

**One-sentence finding (2026-08-14):** combining check_scalar's two loops into
one flat VC costs **5.5–18.6× the sum of the two loops measured separately**,
and that penalty decomposes into two independent factors — a **symbolic-base
amplification of 2.8–7.2×**, which a concrete base removes entirely, and a
residual **1.6–2.6× that is chunk-inventory cost**: each loop's steps must
transport the *other* loop's resident chunks at every world extension, an
effect dominated by instruction and register chunks rather than data cells.
Neither factor is a cross-loop *semantic* interaction, and neither is
"more residual goals".

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

`m = n = 16` was not attempted: `m = n = 8` already peaks at ~11 GB
(`top_heap`) on a 14 GB box. Every pre-existing point reproduced its
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
loop's trips expensive is running *before* another loop. No simple functional
form fits, though — `(first-loop trips) × (second-loop steps)` predicts a
uniform 3.25× gain from swapping, against measured 1.92 / 3.56 / 1.57.
Position-dependence is solid; the law is not.

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

## 7. What this means

Ranked, for `check_scalar`'s whole-function target:

1. **The symbolic base is the dominant cost**, 2.8–7.2× amplification of the
   combination penalty and 18–59× of absolute allocation, acting mainly
   through `vm_compute`. Anything that reduces it (a concrete-base rung, or
   cheaper per-address fetch bounds) dwarfs every other lever measured here.
2. **The residual composition penalty is chunk inventory, ~1.6–2.6×**, driven
   by total resident chunks × steps, dominated by instruction chunks. This is
   the same mechanism as `key-schedule-loop2-cost-drivers.md`'s driver, so
   `plans/PLAN-loop-invariant.md`'s per-iteration contract addresses both:
   it would stop each loop's steps from carrying the other loop's chunks at
   all.
3. **No cross-loop semantic interaction has been demonstrated.** Order matters
   (§3) and that is unexplained by any fitted law, but §6 shows inventory
   alone accounts for the concrete-base residual, so there may be nothing
   left to explain once the base and the inventory are accounted for.

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

**Not done, in priority order:**

1. **Concrete base at `m=n=8` and `m=n=16`** — the payoff test. `m16/n4`
   concrete runs in ~8 s, so this is cheap, and it settles both whether the
   original "cannot run at all" barrier is gone and whether the concrete
   base's exponent really steepens.
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
