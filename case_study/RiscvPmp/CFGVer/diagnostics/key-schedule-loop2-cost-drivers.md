# key_schedule_loop2 cost drivers — heap size vs. term growth

Status: **Diagnostic record, 2026-08-13.** Not a phased plan — a completed
causal investigation. Lives in `diagnostics/`, not `plans/`.

**One-sentence finding:** `key_schedule_loop2`'s cost blows up along two
*independent* axes that must be varied one at a time to be measured
honestly — declared-chunk **usage** (1 vs. N genuinely-touched memory cells)
and the masking step's self-referential **term growth**
(`H := (H>>1) ^ mask(H)`) — and once properly isolated, term growth is the
dominant axis (~3.7–4.7× at N=8) while chunk usage is real but secondary
(~1.7–2.2× at N=8).

---

## The experiment

All variants reuse `KeyScheduleLoop.v`'s committed 14-instruction body
(masking step + table store + backward branch). **This body is already a
simplified stand-in, not the true Botan algorithm**: `KeyScheduleLoop.v`
deliberately reuses `Precompute.v`'s 32-bit masking step instead of the real
64-bit `H0`/`H1` register-pair masking, specifically to sidestep the
separate, still-open `sltu`-on-secret-borrow-chain gap (`TODO.md`'s "Botan
CT::Mask / 64-bit-subtraction gap") — an expressiveness problem, unrelated
to cost. The true 64-bit masking step needs *more* instructions per
iteration than this stand-in, so if anything every number below understates
the real function's cost.

Two independent knobs, five variants (one cell intentionally left
unexplored — see below):

- **Chunk-usage axis**: `1-used` (table pointer never advances, `addi
  a3,a3,0`, all N iterations hit the same address) / `N-used` (pointer
  genuinely advances, `addi a3,a3,4`, N distinct addresses) / `N-declared-
  1-used` (N addresses declared in the precondition, but the pointer never
  advances, so N−1 of them are dead weight, never read or written).
- **Term-growth axis**: `growing-term` (`H`'s two reads are `andi a1,a0,1` /
  `srli a0,a0,1` — `H` feeds into its own previous value, as written) /
  `flat-term` (those two reads are rerouted to `A3` instead of `A0` — `H` is
  recomputed from a value that does not itself accumulate across
  iterations).

| short name | chunks used | chunks declared | term | file |
|---|---|---|---|---|
| 1-used + growing-term | 1 | 1 | growing | `ZZKslChunkSharedCommon.v` |
| N-used + growing-term | N | N | growing | `ZZKslChunkDistinctCommon.v` |
| 1-used + flat-term | 1 | 1 | flat | `ZZKslChunkSharedNoFbCommon.v` |
| N-used + flat-term | N | N | flat | `ZZKslNUsedFlatCommon.v` |
| N-declared-1-used + flat-term | 1 | N | flat | `ZZKslChunkPaddedCommon.v` |

(The `N-declared-1-used + growing-term` cell — pad the precondition while
`H` still feeds into itself — was never built; nothing so far suggests it
would show anything other than the growing-term cost plus the same mild
declared-but-unused surcharge measured on the flat-term side.)

Each was measured at N=4/8/16 via **`allocated_words`** (OCaml's own GC
allocation counter, deterministic to ~0.0002% on this box — both wall-clock
and OS-reported peak RSS gave misleading numbers earlier in this
investigation and were abandoned in favor of this metric).

## Results

`allocated_words`, minus a shared imports-only baseline (434,833,198):

| N | 1-used, growing | N-used, growing | 1-used, flat | N-used, flat | N-decl-1-used, flat |
|---|---|---|---|---|---|
| 4 | 2,136,783,054 | 2,775,733,250 | 2,090,805,329 | 2,696,079,703 | 2,354,454,405 |
| 8 | 10,480,969,207 | 23,087,289,792 | 2,837,247,223 | 4,914,660,883 | 3,839,101,444 |
| 16 | not run | killed, >8 min, never finished | 4,330,048,822 | 12,219,708,553 | 8,402,593,577 |

**Doubling ratios (N4→8):** N-used+growing **8.32×** (cubic-ish) —
1-used+growing **4.91×** (quadratic) — N-used+flat **1.82×**, then **2.49×**
at N8→16 — N-decl-1-used+flat **1.63×**, then **2.19×** — 1-used+flat
**1.36×**, then **1.53×** (climbing toward 2×, the signature of a plain
linear law).

**Held-out linearity check, 1-used+flat only:** fit `a+b·N` on N=4/8,
predict N=16 → 4,330,131,011. Measured: 4,330,048,822. **0.0019% off** —
genuinely linear. The other three multi-chunk rows all miss a linear fit by
19–23% (quadratic fits put their `N²` coefficients at roughly 17–30M,
smaller than the growing-term rows' but real) — so 1-used+flat is the only
variant here that's actually linear; everything else has some superlinear
component.

## Reading the two axes apart (same N, one knob changed)

At **N=8**:

- **Term-growth axis, chunks held at 1**: `1-used+growing` / `1-used+flat`
  = 10,480,969,207 / 2,837,247,223 = **3.69×**.
- **Term-growth axis, chunks held at N**: `N-used+growing` /
  `N-used+flat` = 23,087,289,792 / 4,914,660,883 = **4.70×**.
- **Chunk-usage axis, term held flat**: `N-used+flat` / `1-used+flat` =
  4,914,660,883 / 2,837,247,223 = **1.73×**.
- **Chunk-usage axis, term held growing**: `N-used+growing` /
  `1-used+growing` = 23,087,289,792 / 10,480,969,207 = **2.20×**.
- **Declared-but-unused sub-effect, term held flat**: `N-decl-1-used+flat` /
  `1-used+flat` = 3,839,101,444 / 2,837,247,223 = **1.35×**.

At **N=4** the same comparisons give 1.02×/1.03× (term axis — barely
visible yet) and 1.29×/1.30×/1.13× (chunk axes) — the term-growth axis
compounds much faster with N than the chunk-usage axis does.

Genuinely using N chunks vs. merely declaring N−1 dead ones costs **1.73×
vs. 1.35×** at N=8 — both real, same order of magnitude, not a qualitative
gap. Neither is close to the ~3.7–4.7× the term-growth axis contributes.

## What this means

`KeyScheduleLoop.v`'s own body — already the cheaper 32-bit stand-in — sits
at `N-used + growing-term`, the worst cell measured: both axes fire at
once, and their axis-isolated multipliers roughly compose
(`2.20× × 4.70× ≈ 10.3×`, in the ballpark of the directly-measured 4.91× →
23.09× jump from `1-used+flat` through the two single-axis intermediates).
That compounding is why it's stuck at a feasibility spike of N=2 rather
than the real N=128 — and since the true 64-bit masking step would need
more instructions per iteration than this 32-bit stand-in, the real
function's cost is plausibly worse than what's measured here, not better.

This still gives concrete backing for `plans/PLAN-loop-invariant.md` as the
fix, but now with the right emphasis: term growth is the bigger lever, not
chunk count. Chunk-GC-style fixes only remove *leaked* chunks, not
genuinely-needed ones, so they were never going to touch either axis here.
A per-iteration contract kills both: it mentions only the O(1) resource one
iteration touches (chunk-usage axis gone), and an inductive step relates
just one iteration's before/after `H` via the recurrence instead of
carrying the whole unrolled term forward (term-growth axis gone, and this
is the one worth prioritizing if only one gets fixed first).

## Files (throwaway, not in `_CoqProject`)

`ZZKslBaseline.v` (baseline) ·
`ZZKslChunkSharedCommon.v` + `ZZKslCS_N{4,8,16}.v` (1-used+growing) ·
`ZZKslChunkDistinctCommon.v` + `ZZKslCD_N{4,8,16}.v` (N-used+growing) ·
`ZZKslChunkSharedNoFbCommon.v` + `ZZKslCSNF_N{4,8,16}.v` (1-used+flat) ·
`ZZKslNUsedFlatCommon.v` + `ZZKslNUF_N{4,8,16}.v` (N-used+flat) ·
`ZZKslChunkPaddedCommon.v` + `ZZKslCP_N{4,8,16}.v` (N-declared-1-used+flat).

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran <Common>.v
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran <Runner>.v 2>&1 | grep allocated_words
```

Subtract `ZZKslBaseline.v`'s figure from every runner before comparing.

**Not done this session:** `ZZKslCS_N16.v` (1-used+growing at N=16, for a
third point on its own quadratic fit), the `N-declared-1-used+growing-term`
cell noted above, and the same flat-vs-growing ablation applied to
`br_divrem`'s loop (a structurally similar self-referential accumulator,
flagged but untested).
