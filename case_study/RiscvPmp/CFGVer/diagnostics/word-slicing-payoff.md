# Word slicing, measured without the term-explosion confound

> **STAGE SPLIT, 2026-09-08 — 0% tactic.**  All eight `ZZWsFlat*` arms are bare
> `Eval vm_compute` probes (no `Lemma`/`Proof`/`Qed`, no `solve_vc`), so the
> 2.77x-2.86x slicing payoff is a pure symbolic-executor measurement.
> See `vm-vs-tactic-split.md`.

**Finding (2026-08-24).** On a rig whose term shape is pinned flat, replacing
the per-address instruction-word logic variables with slices of ONE wide
variable is a **2.77x–2.86x reduction in allocated words**, a pure CONSTANT
FACTOR (both arms are exactly linear in trip count), asymptoting to **2.862x**
at the margin. That is substantially *larger* than the 1.61x/1.72x wall-clock
figure published in `plans/PLAN-encoded-instr.md` §12-SEQUEL, which was measured
on br_divrem — a rig whose terms grow 10.54x/trip, so a large share of its cost
sits in a component slicing cannot touch. Amdahl, not a measurement error: the
`|Sigma|` REDUCTION FACTOR is essentially the same on both rigs (4.25x here,
4.2x on br_divrem); what differs is how much of the total cost `|Sigma|` was
driving.

## The experiment

**One axis, and only one:** `CFGVer/Verifier.v` at `71c3172c` (one demonic word
variable per instruction ADDRESS) vs at `2001202f` (one wide `bv (word*n)`
variable, each address's word a `bvtake`/`bvdrop` SLICE of it). Every other
input is byte-identical — same probe file, same `theories/` `.vo`s, same
`Prelude` closure, same protocol.

The pre-slicing arm was built in a scratch COPY of `case_study/RiscvPmp`
(`-Q <copy> Katamaran.RiscvPmp -R theories Katamaran`), so the working tree was
never modified and the two arms cannot contaminate each other's artifacts.

| variant | `Verifier.v` at | what moves |
|---|---|---|
| `per-address-words` | `71c3172c` | 14 word variables (one per instruction) |
| `sliced-words` | `2001202f` (HEAD) | 1 wide variable + 14 slices |

**The rig is `ZZKslHeapCommon`'s, copied verbatim** — chosen because it pins
every other known cost driver:

- **term shape FLAT**: the mask bit and `H` both come from `A3`, a constant,
  never from `A0`, so nothing is self-referential across trips;
- **heap inventory STATIC**: `A3` is a no-op `addi`, the pointer never advances,
  every trip stores to the same `p+56`;
- **declared cells fixed** at `P = 1`, via `gen_contract_rel_classed`.

Confirmed empirically rather than assumed: **both arms are exactly linear in
trip count** (fit below). A rig with term growth could not be.

**PROTOCOL (identical on both arms): tree construction only.** The measured
expression is `postprocess (CFG_VC_triple ...)` consumed by a node/binder
census — no VC proof, no `solve_vc`, no `Qed`. See "Scope limits" below.

## Results

`allocated_words`, `OCAMLRUNPARAM='v=0x400'`, one heavy `Eval` per `coqc`
process, each arm minus ITS OWN no-`Eval` baseline of the same file (so the
subtraction removes imports *and* definition-elaboration cost).

Baselines: sliced **607,036,630**, per-address **607,038,071** — they agree to
1,441 words in 607 M (0.0002%), which is the metric's noise floor and confirms
the two arms' import closures cost the same.

| trips | protocol | `per-address-words` (net) | `sliced-words` (net) | ratio |
|---|---|---|---|---|
| 2  | tree only | 178,304,672   | 64,333,868  | **2.772x** |
| 4  | tree only | 354,799,719   | 126,015,296 | **2.816x** |
| 8  | tree only | 707,784,196   | 249,369,139 | **2.838x** |
| 16 | tree only | 1,413,758,344 | 496,081,639 | **2.850x** |
| 32 | tree only | 2,825,698,550 | 989,497,433 | **2.856x** |

Wall clock on the same runs, for scale only (never quote it as the result):
0.801/1.656/3.669/8.473/22.349 s vs 0.408/0.783/1.684/3.918/9.005 s.

### Held-out fit

Both arms fitted linear on t = 4 and 16 only, then predicting the three points
NOT used:

| arm | slope (words/trip) | intercept | t=2 err | t=8 err | t=32 err |
|---|---|---|---|---|---|
| `per-address-words` | 88,246,552 | 1,813,511 | +0.0011% | +0.0002% | +0.00016% |
| `sliced-words`      | 30,838,862 | 2,659,848 | +0.0015% | +0.0006% | +0.0006%  |

Linear to within the noise floor on both arms. **Marginal per-trip ratio =
88,246,552 / 30,838,862 = 2.862x**, which is what the table's ratios are
climbing towards as the fixed intercept washes out.

## Reading the axis apart

The cost ratio is not explained by the tree getting smaller. Same rig, t=2,
census of the RAW (un-`postprocess`ed) tree:

| arm | leading binders (`|Sigma|`) | total nodes |
|---|---|---|
| `per-address-words` | 17 | 4,619 |
| `sliced-words`      | **4** | 4,606 |

14 instructions, so 14 word binders collapse into 1: 17 - 14 + 1 = 4, exactly.
The node count moves by the same 13 — i.e. **only the removed `demonicv` nodes
themselves**. The tree is otherwise structurally identical, and the 2.86x is
therefore entirely the cost of CARRYING and LOOKING THROUGH those variables,
which is what `diagnostics/lvar-lookup-cost-drivers.md` predicts (`env.lookup`
is a linear walk, and `persist` re-looks-up every occurrence at every world
extension).

## Why this is bigger than the published br_divrem number

| rig | `|Sigma|` before -> after | reduction | measured payoff |
|---|---|---|---|
| br_divrem (`ZZDivremDebugProbe`) | 63 -> 15 | 4.20x | 1.61x / 1.72x (wall clock) |
| this rig (`ZZWsFlat*`)           | 17 -> 4  | 4.25x | **2.86x** (allocated words) |

Same reduction factor, different payoff — so the difference is in the
DENOMINATOR, not in what slicing does. br_divrem carries 10.54x/trip term
growth in six loop-carried registers; that cost is untouched by slicing and
dilutes the ratio. Here it is absent, so the `|Sigma|` effect shows in full.

Two corollaries worth keeping:

1. **The payoff is NOT simply proportional to program length.** This rig is
   *shorter* than br_divrem (14 words vs 49) and pays off *more*. What sets the
   ratio is the share of total cost that `|Sigma|` was driving.
2. **It is a constant factor, not an exponent change.** Both arms are linear in
   t with the same shape; slicing moves the wall, it does not remove it. On a
   program whose real blocker is term growth (muladd / br_divrem), expect the
   1.6-1.7x end of the range, and the Phase 4 abstraction lemma is still the
   thing that matters there.

## Scope limits

- **Tree construction only.** No `Qed`, no `solve_vc`. Cross-protocol
  comparison is worth 1.81x on its own (see the skill's checklist), so this
  number must not be compared against any `Qed`-protocol figure elsewhere. Both
  arms here share one protocol, so the RATIO is sound; the absolutes are not
  comparable to VC-discharge measurements.
- **One rig, one program length.** The 2.86x is this rig's number. The general
  claim it supports is the mechanism (`|Sigma|` carrying/lookup cost), not the
  constant.
- The postprocessed VC collapses to `SymProp.block` on this rig at every t —
  the solver discharges it entirely. That is why the cost table's census reads
  `(1, 0)`; the executor still did all the work, and the raw-tree census above
  is where the structure was read.

## Files / reproduction

Throwaway probes, not in `_CoqProject` (`ZZ*` convention):

- `Example/ZZWsFlat.tmpl`-generated `Example/ZZWsFlatT{2,4,8,16,32}.v` — one
  heavy `Eval` each, trip count is the only difference.
- `Example/ZZWsFlatBase.v` — the same file with the `Eval` line deleted.
- `Example/ZZWsFlatRaw.v` — t=2, `postprocess` removed, for the binder census.

Sliced arm (HEAD), from the repo root:

```bash
OCAMLRUNPARAM='v=0x400' coqc -w none \
  -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/ZZWsFlatT32.v
```

Pre-slicing arm — build a scratch copy so the working tree is never touched:

```bash
OFF=/tmp/off && mkdir -p $OFF && cp -r case_study/RiscvPmp $OFF/RiscvPmp
git show 71c3172c:case_study/RiscvPmp/CFGVer/Verifier.v > $OFF/RiscvPmp/CFGVer/Verifier.v
for f in Verifier Noninterference Tables Contracts GenContract Example/Prelude; do
  coqc -w none -Q $OFF/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
    $OFF/RiscvPmp/CFGVer/$f.v
done   # ~52 s total
OCAMLRUNPARAM='v=0x400' coqc -w none \
  -Q $OFF/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  $OFF/RiscvPmp/CFGVer/Example/ZZWsFlatT32.v
```

Note `Noninterference.v` also requires `Verifier`, so it must be rebuilt in the
scratch copy too or its `.vo` mismatches.
