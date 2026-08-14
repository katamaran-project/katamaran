# check_scalar combined (loop1 + loop2) cost drivers

Status: **Diagnostic record, 2026-08-13.**

**One-sentence finding:** holding either loop's size fixed and growing only
the other shows a modest (~8-12%) superadditive penalty over that loop's
own standalone doubling rate — much smaller than the dramatic 2.81×/3.78×
superadditivity `plans/PLAN-check-scalar-full.md` measured when **both**
loops grow together (matching the real function's `M = N = klen`), which
means the bulk of the real superadditivity comes from an interaction
between the two loops' sizes growing *simultaneously*, not from either
loop paying a fixed penalty for the other's mere presence.

Neither loop's own recurrence is the driver of this — see
`check-scalar-loop1-cost-drivers.md` and `check-scalar-loop2-cost-drivers.md`,
both of which independently clear self-reference as a meaningful cost
source for either loop in isolation.

## The experiment

A synthetic composition: check_scalar's real loop 1 (4 instructions)
immediately followed by real loop 2 (13 instructions) in one instruction
list — loop 1 runs to completion, then loop 2 runs, exactly the real
function's control flow. Loop 2 reads its own `k2[]`/`n2[]` arrays rather
than aliasing loop 1's `k[]`, to avoid address-aliasing complexity that
isn't needed to answer the cost question; loop 2's registers are renamed
off `A0-A6` onto `A7`/`T0-T5` so no re-initialization code is needed
between the loops. Parametric on loop 1's trip count `M` and loop 2's trip
count `N` **independently** (the real function always has `M = N = klen`;
decoupling them is the point — it's what lets each loop's marginal
contribution be read off on its own).

Two sweeps, each holding one loop's size at a small constant and varying
the other:

- **Sweep A** — `N = 4` fixed, `M ∈ {4, 8, 16}` (loop 1's marginal cost).
- **Sweep B** — `M = 4` fixed, `N ∈ {4, 8, 16}` (loop 2's marginal cost).

Measured via `allocated_words`, minus the same 434,833,198 baseline used
throughout.

## Results

| M | N | allocated_words | minus baseline |
|---|---|---|---|
| 4 | 4 | 19,526,953,618 | 19,092,120,420 |
| 8 | 4 | 41,191,978,724 | 40,757,145,526 |
| 16 | 4 | 92,734,479,512 | 92,299,646,314 |
| 4 | 8 | 36,067,076,564 | 35,632,243,366 |
| 4 | 16 | 85,458,848,566 | 85,024,015,368 |

**Sweep A (loop 1's marginal doubling, N=4 fixed):** M4→8 = **2.13×**,
M8→16 = **2.26×**.

**Sweep B (loop 2's marginal doubling, M=4 fixed):** N4→8 = **1.87×**,
N8→16 = **2.39×**.

## Reading the axes apart — combined-context doubling vs. each loop's own standalone doubling

Loop 2's sweep lands at exactly the same N-ranges (`4→8`, `8→16`) already
measured standalone in `plans/PLAN-check-scalar-full.md` (loop 2 alone:
1.67×, 2.21× at those same two doublings), so this is a clean, matched
comparison:

| doubling | loop 2 alone | loop 2 in combined (M=4 fixed) | combined/alone |
|---|---|---|---|
| N4→8 | 1.67× | 1.87× | **1.12×** |
| N8→16 | 2.21× | 2.39× | **1.08×** |

So loop 2's own marginal doubling rate is **8-12% steeper** inside the
combined function than it is alone, even with loop 1 held at a small,
constant `M=4`. That's a real, measurable superadditive effect — but it's
far short of explaining a jump from ~2.2-3.3× (loop 2 alone, per-doubling)
to the 2.81×/3.78× the real (`M=N`-scaled) whole-function measurement
showed.

Loop 1's sweep doesn't have an exactly matching-range standalone
comparison (loop 1 was only measured standalone at N16→32 in the
self-reference diagnostic, not at M4→8/M8→16), so this read is softer: its
combined-context doublings (2.13×, 2.26×) sit close to its own
standalone N16→32 doubling (2.35×) — no strong sign of a matching
superadditive penalty, but the ranges aren't identical, so this shouldn't
be over-read the way loop 2's matched comparison can be.

## What this means

**The bulk of the real superadditivity is an interaction term, not a fixed
surcharge.** Holding one loop small (`=4`) and growing only the other shows
at most a ~10% penalty over that loop's own rate — nowhere near enough to
explain the original whole-function finding. That finding scaled **both**
loops together (`M=N`), which is exactly the condition under which the
`heap_size × steps²` law's cross-terms should show up: loop 1's own
ambient heap footprint (its `k1[]` bytes, still resident while loop 2
executes) is itself only `O(M)` — cheap when `M=4` is held fixed, but it
grows right along with `N` when the real function's `M=N=klen` coupling is
respected, and `heap_size` multiplying a *growing* `steps²` term is a much
bigger effect than a small constant `heap_size` doing the same. This is
consistent with (though not yet a direct confirmation of) the general
"declared-chunk-count scaling with N" mechanism from
`key-schedule-loop2-cost-drivers.md`, here showing up as a cross-loop
interaction rather than a single loop's own chunk count.

**Not yet done**: a sweep with both `M` and `N` growing together
(`M=N ∈ {4,8,16}`) to directly measure the interaction term itself, rather
than inferring its size from the gap between the held-fixed sweeps above
and the old whole-function numbers. That would be the natural next
diagnostic if this needs to be pinned down further — e.g. before deciding
whether `PLAN-loop-invariant.md`'s per-iteration contract approach (which
would eliminate the ambient-heap coupling entirely, since each loop's proof
step would only ever mention its own iteration's O(1) footprint) is worth
prioritizing here specifically.

## Files (throwaway, not in `_CoqProject`)

`ZZCombinedCommon.v` (new, parametric on `m n`) +
`ZZComb_M4_N4.v` / `ZZComb_M8_N4.v` / `ZZComb_M16_N4.v` (Sweep A) /
`ZZComb_M4_N8.v` / `ZZComb_M4_N16.v` (Sweep B, `M4_N4` shared with Sweep A).

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran ZZCombinedCommon.v
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran <Runner>.v 2>&1 | grep allocated_words
```

See also: `check-scalar-loop1-cost-drivers.md`, `check-scalar-loop2-cost-drivers.md`.
