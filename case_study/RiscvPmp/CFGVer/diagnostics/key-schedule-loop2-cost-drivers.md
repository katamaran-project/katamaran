# key_schedule_loop2 cost drivers — heap size vs. term growth

Status: **Diagnostic record, 2026-08-13.** Not a phased plan — a completed
causal investigation. Lives in `diagnostics/`, not `plans/`.

**One-sentence finding:** `key_schedule_loop2`'s cost blows up along two
*independent* axes that must be varied one at a time to be measured
honestly — declared-chunk **usage** (1 vs. N genuinely-touched memory cells)
and the masking step's self-referential **term growth**
(`H := (H>>1) ^ mask(H)`) — and once properly isolated, term growth is the
dominant axis (~3.7–4.7× at N=8) while chunk usage is real but secondary
(~1.7–2.2× at N=8). A direct term-level simulation confirms WHY: `H` is
referenced twice per iteration in a shape no existing `peval` rule
collapses, so its raw term size is genuinely exponential (`2^n`, confirmed
by construction, not inferred) — meaning the 3.7–4.7× at N=8 is likely an
early, understated reading, not the eventual ratio.

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

## The mechanism behind the term-growth axis, confirmed by direct simulation

The ablation above shows THAT growing-term costs 3.7-4.7×; a follow-up
simulation (`ZZTermSim.v`, built while investigating why `check_scalar`
loop 1's structurally-similar `z |= k[u]` recurrence costs nothing —
see `check-scalar-loop1-cost-drivers.md`) establishes WHY, by directly
applying the real `peval_binop`/`peval_unop` smart-constructors to both
recurrences and measuring the resulting term's raw node count:

| n | `z`'s term size | `H`'s term size |
|---|---|---|
| 1 | 3 | 8 |
| 2 | 5 | 22 |
| 4 | 9 | 106 |
| 8 | 17 | 1,786 |
| 16 | 33 | 458,746 |

`z` (referenced once per iteration, as `or`'s left operand) grows exactly
linearly (`2n+1`). `H` (referenced **twice** per iteration — `andi
a1,a0,1` and `srli a0,a0,1`, both feeding the same `xor` that produces the
next `H`) roughly **doubles every iteration** — genuinely `O(2^n)`, not
`O(n)` or `O(n²)`. Coq's term representation is a tree, not a DAG with
sharing: embedding `H`'s current value into two different sub-expressions
of the same new expression creates two full independent copies of its
entire prior structure, and that duplication compounds. `peval` has a
specific rule for exactly this shape when it's dressed as `bvor(bvand(mask,
S), C)` (`bop.coalesce`, landed via the earlier mask-algebra work,
`plans/PLAN-coalesce.md`) — but `H`'s recurrence is `bvxor(shiftr(H,1),
negate(bvand(H,1)))`, top-level `bvxor` with a *shift* of `H` as one
operand, which `bvcoalesce_try`'s pattern (`theories/Symbolic/
PartialEvaluation.v:948-968`, requires top-level `bvor` splitting into
`bvand(mask,S)` against a zero-test) structurally cannot match. So `H`
falls straight through to the naive, duplicating construction.

**This means the 3.7-4.7× measured at N=8 likely understates the real
severity.** A term whose raw size is genuinely exponential should, once
whatever absorbs the early constant-factor overhead runs out, show a ratio
climbing well past a fixed multiplier — exactly the "early exponent looks
mild, hides a worse crossover" trap this project has been burned by more
than once (see the common-mistakes checklist in `cfgver-scaling-
diagnostics`). The `1-used+growing`/`N-used+growing` `allocated_words`
figures only go up to N=8; whether the ratio is still climbing toward
something matching `2^N` at N=16 is untested (see below).

## Correction: this exact mechanism was already diagnosed and a fix already built

This is not a new finding — an earlier session (2026-07-19 to 2026-07-24,
`project_key_schedule_loop_scaling` memory) found the identical mechanism
and built a fix for it, which this diagnostic failed to cross-reference
before now. A targeted `peval` fold (`select_last_k`, wired into
`peval_binop`'s `bvxor` case at commit `a13da1b3`) recognizes
`key_schedule_loop2`'s exact masking-chain shape — including the `AND`
against the GHASH constant `R = 0xE1000000` (that's what `lui a2,921600`
in the real instructions loads: `921600 << 12 = 0xE1000000`), which the
simulation above simplified away — and rewrites it to an `O(1)`-growth
accumulator form. Its correctness was confirmed directly from the raw VC
term at N=3/4 in that session: *"the 3^N blowup is killed."* (That
session's own reproducer measured a base closer to 3 than this diagnostic's
clean asymptotic 2×/iteration; likely a difference in exactly which part of
the real bit-trick chain was modeled — same mechanism, not necessarily the
identical constant — not something to over-read.)

**It was reverted (commit `027d7c27`, 2026-07-24) not because it failed,
but because a *different*, then-undiagnosed driver dominated at the
time**: fixing the term-duplication wall alone only bought ~12% wall-clock
at N=8 and didn't even finish `vm_compute` at N=16, because the real
bottleneck then was the leaked `encodes_instr` heap chunk (a separate
`O(steps²)` driver, unrelated to term size). **That driver has since been
fixed** — the landed chunk-GC, `plans/PLAN-chunk-gc.md`, 2026-08-03. The
thing that was masking `select_last_k`'s benefit when it was last measured
is gone.

**This makes reviving `select_last_k` the most concrete, promising next
step for this file's own scaling problem** — more so than
`plans/PLAN-loop-invariant.md`'s per-iteration contract, which is a larger,
from-scratch undertaking, not something already built and measurement-
confirmed once. Recovery point: commit `a13da1b3` (the "confirmed correct
from the raw VC term, soundness deliberately `Admitted`" state — a
measurement-first pass, exactly the same rigor level as this session's own
`allocated_words`/`ZZTermSim.v` work). The commits after that
(`select_last_k_bump` soundness-proof attempts) went through several
add/revert cycles and don't appear to have landed cleanly, so `a13da1b3`
is the right starting point to re-measure from, not the later attempts.

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
Given the confirmed exponential mechanism above, "plausibly worse" may be
a significant understatement past N=8.

`plans/PLAN-loop-invariant.md`'s per-iteration contract would still fix
both axes at once (it mentions only the O(1) resource one iteration
touches, and relates one step's before/after `H` inductively rather than
carrying the whole unrolled term forward) — but per the correction above,
it's no longer the *only*, or even the most immediate, lever for the
term-growth axis specifically: `select_last_k` already does that alone,
already built, already measurement-confirmed once, and just needs
re-testing now that chunk-GC removed what was masking it. The sensible
order is: revive and re-measure `select_last_k` first (cheap, since it's
recovering existing work, not building new); if the chunk-usage axis is
still a problem afterward, `PLAN-loop-invariant.md` (or region chunks) is
what's left to address that one.

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

Also: `ZZTermSim.v` (the term-simulation probe backing the mechanism
section above).

**Not done this session, in priority order:**

1. **Revive `select_last_k` from commit `a13da1b3` and re-measure** now
   that chunk-GC has landed — see "Correction" above. This is the single
   highest-value next step: a fix that's already built and was already
   confirmed to kill this exact wall, just never re-tested since the
   driver that was masking its benefit got fixed.
2. `ZZKslCS_N16.v` (1-used+growing at N=16 — would show directly whether
   the ratio is still climbing toward `2^N` or has started to level off),
   useful regardless of (1) as an independent confirmation of the
   mechanism's real-world severity.
3. The `N-declared-1-used+growing-term` cell noted above.
4. The same term-simulation check applied to `br_divrem`'s loop (muladd) —
   a bit-serial division algorithm almost certainly updates its own state
   from multiple self-references per step, structurally similar to `H`,
   flagged as a plausible-but-untested candidate for this exact mechanism.
