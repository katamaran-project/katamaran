# The instruction table's per-entry cost is variable LOOKUP — isolated

**Date:** 2026-09-07. **Rig:** the muladd cut segment (`ZZK_*` / `ZZSg_*`,
15 executed instructions at offset 220, fuel 20, symbolic base `term_var "p"`).
**Protocol:** `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc`,
`allocated_words` net of an imports-only baseline (`ZZSegBase.v`) re-measured
per run, strictly serial, every arm gated on a real `Qed`.

## What this answers

`table-entry-cost.md` §3 established that 89% of the per-table-entry cost is
*carrying* cost: 3.03 M words per entry, producing **zero** VC nodes (structural
counts byte-identical at K=20, 75, 282). §3b then guessed the mechanism was
`|Σ|`-quadratic, from a two-rig fit. This is the isolation that §3b said it
needed and did not have.

**Conclusion: the per-entry cost is `env.lookup` on the table's own two
variables, and it is EXACTLY LINEAR in their depth.** That identifies
`persist_itableW` as the site and refutes §3b's quadratic.

## Method — one axis, verified structurally

`dead_exists D` (`exists x1..xD, True`, verbatim from `ZZLvarDepthCommon.v`) is
prepended to the precondition. It is safe on this branch because
`Verifier.v`'s `drop_fuel` is **0**, so `drop_dead 0` is the identity and the
pads are not collected before they can be paid for.

Placing the pads at the **front** matters: `produce (a1 ∗ a2)` produces `a1`
first, so every *real* variable keeps its baseline distance-from-top, while the
two variables the table is built from — the base `"p"` (in `Σ0`) and the wide
word variable (minted by `sexec_triple_addr`'s `demonic_ctx`, before `produce`)
— sit `D` binders deeper. So the **K-slope reads the table's own lookup cost and
nothing else.**

That the pad moves one axis is not asserted, it is measured
(`ZZSgStat_D{0,64}.v`, `zz_stats_raw`):

| | D=0 | D=64 | Δ |
|---|---:|---:|---:|
| `lv_binders` | 371 | 435 | **+64** |
| `lv_maxsig` (peak \|Σ\|) | **32** | 96 | **+64** |
| `lv_vareqs` | 345 | 345 | 0 |
| `lv_occ` | 159 | 159 | 0 |
| `lv_nodes` | 2342 | 2406 | +64 |

Exactly `D` binders, zero occurrences, zero equations, no other structure.
Chunks, steps, instructions, term shapes and fuel are identical across the whole
grid. Peak `|Σ|` at baseline is **32**.

## The grid — net allocated words (M)

| pads `D` | K=15 | K=45 | K=75 | **slope (M/entry)** |
|---|---:|---:|---:|---:|
| 0  | 339.699 | 430.299 | 521.267 | **3.0261** |
| 16 | 613.315 | 743.223 | 873.495 | **4.3363** |
| 32 | 979.969 | 1149.151 | 1318.765 | **5.6466** |
| 48 | 1434.377 | 1642.932 | 1851.785 | **6.9568** |
| 64 | 1976.926 | 2224.767 | 2472.930 | **8.2667** |

## Result 1 — the K-slope is exactly linear in |Σ|

Fit the two endpoints (D=0, D=64), hold out the three interior rows:

| D | predicted M/entry | measured | error |
|---|---:|---:|---:|
| 16 | 4.336285 | 4.336333 | **+0.0011%** |
| 32 | 5.646437 | 5.646606 | **+0.0030%** |
| 48 | 6.956589 | 6.956800 | **+0.0030%** |

and the four consecutive differences are 81887.5 / 81892.1 / 81887.1 /
81871.3 words per entry per binder — a spread of 0.03%. So

> **per-entry cost = 3.0261 + 0.08188·D M words**, linear to 6 parts in 100,000
> on three held-out points.

A cost that is *linear in the number of binders between a variable and the top
of the context* is a de Bruijn walk. `env.lookup` is that walk
(`Environment.v`), `persist__term t θ = subst t (sub_acc θ)` performs it at
every `term_var` leaf, and `persist_itableW` maps it over all K entries at every
world extension. Nothing else in the per-step path is depth-sensitive.

## Result 2 — the |Σ| QUADRATIC is not a table cost

Read the same grid down the other axis. At fixed K, fit `c + p·D + q·D²` on
D=0/32/64 and hold out D=16/48:

| K | c (M) | p (M/binder) | q (M/binder²) | held-out D=16 | D=48 |
|---|---:|---:|---:|---:|---:|
| 15 | 339.699 | 14.4352 | 0.174164 | −0.314% | +0.036% |
| 45 | 430.299 | 16.8896 | 0.174202 | −0.256% | +0.035% |
| 75 | 521.267 | 19.3489 | 0.174154 | −0.221% | +0.028% |

So total cost **is** quadratic in `|Σ|` — confirming the catalog — but

> **`q` is independent of table size: 0.174164 vs 0.174154 at K=15 vs K=75,
> a difference of 0.006%.**

The table contributes a strictly **linear** `|Σ|` term. The quadratic lives
elsewhere (`sub_comp`'s `O(|Σ|²)` per world extension is the standing candidate,
`base-k-hunt.md`), and no amount of table shrinking will touch it.

**Internal consistency check.** `dp/dK` from the D-direction fits is
`(19.3489 − 14.4352)/60 = 81895.1` words/entry/binder; `b` from the K-slopes is
`81884.5`. The same coefficient recovered from two orthogonal directions of the
grid, **0.013% apart**. The two-variable law on this rig is

```
cost(K,D) = A + 3.0261·K + (P0 + 0.08189·K)·D + 0.17416·D²      [M words]
```

## How much of the 3.026 M/entry is lookup?

`b·d0`, with `d0` the run-mean depth of the table's variables. Peak `|Σ|` is 32
and `"p"` is the outermost binder, so `d0 ≤ 31`; the precondition mints ~24
variables before the first step, so `d0 ≳ 25`. Hence

| `d0` | lookup | share | `|Σ|`-blind residue |
|---|---:|---:|---:|
| 31 (peak, upper bound) | 2.5384 M/entry | **83.9%** | 0.4877 M/entry |
| 25 (post-precondition, lower bound) | 2.0471 M/entry | **67.6%** | 0.9790 M/entry |

So **68–84% of the per-entry cost is the lookup walk.** The residue is the
`|Σ|`-blind work: `lookup_instr`'s `Term_eqb`/`peval` `List.find`, the
occurs-check walk in `itableW_free`, and `persist__term`'s own term traversal.

## Consequence for base+offsets

`base+offsets` — one base term, one wide word term, and a world-independent
`list (N * AnnotInstr)` — removes the entire per-entry cost, not merely the
lookup share: a list of `N`s is not persisted at all, is not occurs-checked as
terms, and is dispatched by one `peval` plus a numeric lookup. On `ZZSeg2P`
(K=282, 1164.651 M post-exit-fix) the table share is `282 × 3.0261 = 853.4 M`,
**73.3%**, i.e. a predicted ~3.7× on that arm.

Stated honestly: the *mechanism* is now measured, the *ceiling* is an
extrapolation of a measured slope to K=282 (the slope is flat over K=15..75 and
was flat to K=282 in §3's own sweep, so this is interpolation of a verified
linearity rather than a new hypothesis).

## RETRACTION — §3b of `table-entry-cost.md`

§3b inferred an `|Σ|` **quadratic** for the per-entry coefficient from a
28× per-entry-per-step gap between the pad rig (`|Σ|`≈7) and muladd (`|Σ|`≈32),
a 4.6× `|Σ|` ratio. That inference is **wrong twice over**:

1. The per-entry law is **linear** in `|Σ|`, measured above to 0.003%. A linear
   law cannot produce 28× from a 4.6× ratio, so the gap was never evidence of
   an exponent.
2. The two rigs are not comparable on this axis at all. `ZZPadShrCommon.v` is
   `@MkCFGVerifierContract [ctx] ia` with `term_val ty_xlenbits (bv.of_N ia)` —
   a **concrete base and an empty `Σ0`**. After `peval` its table keys are bare
   `term_val`s containing **no variable**, so the pad rig has no lookup cost to
   measure. It was measuring the residue, against a rig measuring residue plus
   lookup.

This is the fifth two-point/two-rig mechanism fit to fail on this question
(`feedback_check_the_record_first`). The 5×3 grid with three held-out points is
what the claim needed, and it cost 15 arms at 10–18 s each.

Note also that the matched concrete-base comparison could **not** be run:
`ZZSeg2C.v` (concrete-base muladd segment) does not compile — it burns 43.8 G
words and leaves open goals after `solve_vc`, which is why it never had a `.vo`.
It was abandoned, not measured, and any statement resting on it should be
treated as unsupported.

## Arms

`Example/ZZSg_D{0,16,32,48,64}_K{15,45,75}.v` (15 arms, all `Qed`),
`Example/ZZSgStat_D{0,64}.v` (structural counters),
`Example/ZZSg_C_K{15,45,75}.v` (concrete-base attempt, all FAILED — see above).
Scripts: `sgsweep.sh`, `gensig.py`, `sganal.py` in the session tmp dir.
