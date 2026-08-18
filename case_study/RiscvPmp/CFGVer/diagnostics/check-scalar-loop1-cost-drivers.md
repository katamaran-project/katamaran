# check_scalar loop 1 cost drivers — self-reference tested and cleared

Status: **Diagnostic record, 2026-08-13.**

**Follow-on (2026-08-18).** Unaffected. The `|Σ|` (logic-variable) driver named
in the sibling `check-scalar-combined-cost-drivers.md` now has a landed fix
(`gen_contract_rel_classed`, `plans/PLAN-classed-existentials.md`), but it applies
only to the base-relative word-granular `gen_contract_rel` family — not to this
example's byte specs. This record's conclusion about the accumulator is about a
different axis entirely and is untouched either way.

**One-sentence finding:** loop 1's accumulator (`z |= k[u]`, i.e. `or
a2,a2,a3` reading its own previous value every iteration) contributes
essentially nothing to cost (<1.4% at N=32) because `z` is referenced only
**once** per iteration, so its symbolic term grows linearly — confirmed by
direct simulation, after three other hypotheses (peval flattening,
double-touch, memory-store) were tried and ruled out first (see "Ruled-out
drivers" below, then "The confirmed mechanism").

## The experiment

Real loop 1 body, from BearSSL `check_scalar` (`src/ec/ec_p256_m62.c:1610`):

```
lbu  a3, 0(a0)    ; a3 := k[u]
addi a0, a0, 1    ; advance pointer
or   a2, a2, a3   ; z := z | a3        <-- a2 read AND written
bne  a0, a1, back
```

Two variants, one axis (term-growth: flat vs. growing), chunk count held
fixed at N genuinely-read bytes in both:

- **baseline** — unchanged, `ZZByteLoop1Common.v` (`or a2,a2,a3`).
- **no-feedback** — `ZZByteLoop1NoFbCommon.v`: `or a2,a2,a3` rerouted to
  `or a2,a1,a3` (A1 is the fixed end-pointer, never written in this loop,
  so the new `a2` no longer nests the previous one). Nothing else changed.

Measured via `allocated_words` at N=16 and N=32 (minus the 434,833,198
imports-only baseline, same figure re-used from the `key_schedule_loop2`
investigation — same `Prelude` chain, deterministic, unaffected by which
example references it).

## Results

| N | baseline | no-feedback | ratio (baseline/no-feedback) |
|---|---|---|---|
| 16 | 2,473,518,969 | 2,464,062,561 | 1.0038× |
| 32 | 5,818,238,424 | 5,740,237,602 | 1.0136× |

Doubling ratios (N16→32): baseline **2.352×**, no-feedback **2.330×** —
statistically the same curve.

## Reading the axis

Self-reference costs **0.4% at N=16 and 1.4% at N=32** — both well within
noise of the two curves being identical. Contrast this directly with
`key_schedule_loop2`'s `H` recurrence, which cost **3.69×** at N=8 for the
same kind of ablation (`diagnostics/key-schedule-loop2-cost-drivers.md`),
and with loop 2's own accumulator (see the companion diagnostic), which
shows a small but non-trivial effect at N=16. Three data points on the same
mechanism, three different magnitudes — self-reference is not a fixed
tax, its cost depends on what the recurrence actually computes.

## Ruled-out drivers

Two follow-up hypotheses for *why* `z`'s recurrence is cheap while `H`'s is
expensive, both tested directly and both negative:

**Hypothesis: `peval` flattens the OR-chain into an associative/idempotent
normal form.** Checked against the actual code
(`theories/Symbolic/PartialEvaluation.v`) rather than assumed. `bop.bvor` is
dispatched to `peval_bvor_mask` (line 977), which only special-cases operands
recognizable as `uop.expand`/`bop.coalesce` mask patterns — `z`'s plain
byte-OR chain matches neither, so it falls through to `peval_bvor_coalesce`
→ `peval_binop'` (line 854), whose *only* simplification is folding two
concrete (`term_val`) operands together; with any symbolic operand present
it just constructs a fresh, unsimplified `term_binop` node. **`z`'s raw term
nests exactly the same way `H`'s does — this hypothesis is wrong.**

**Hypothesis: touching `z` a second time per iteration matters** (mirroring
`H` feeding both `H&1` and `H>>1`). Tested with `ZZLoop1DoubleReadCommon.v`
— same 4-instruction body plus one inert extra read of `z` into an unused
scratch register. **Hypothesis: writing `z` to memory every iteration
matters** (mirroring `H`'s `sw a0,0(a3)`). Tested with
`ZZLoop1MemStoreCommon.v` — same 4-instruction body plus a store of `z` to a
fixed (chunk-count=1) address every iteration. Both add a 5th instruction,
so a **neutral control** (`ZZLoop1NeutralCommon.v` — a 5th instruction that
touches neither `z` nor anything growing) is needed to separate "one more
step" overhead from anything `z`-specific:

| N | baseline (4 instr) | neutral (+1 instr, no `z`) | double-read | mem-store | double-read vs. neutral | mem-store vs. neutral |
|---|---|---|---|---|---|---|
| 16 | 2,473,518,969 | 2,973,701,709 | 2,930,526,589 | 3,039,649,340 | **−1.5%** | **+2.2%** |
| 32 | 5,818,238,424 | 7,103,652,331 | 7,089,441,454 | 7,255,111,536 | **−0.2%** | **+2.1%** |

The generic "one more instruction" tax is ~20-22% at both N — far bigger
than either candidate mechanism. Against that proper baseline: double-read
costs *nothing* extra (negative at both N, i.e. noise), and mem-store costs
a small, real, but flat ~2.1-2.2% at both N — not accelerating, and nowhere
near `key_schedule_loop2`'s 3.7-4.7× for the equivalent ablation. **Both
hypotheses are ruled out** as the explanation for the `H`-vs-`z` gap.

## The confirmed mechanism

All three ruled-out hypotheses were indirect — testing a guessed mechanism
through `allocated_words` rather than looking at the constructed term
itself. `ZZTermSim.v` does that directly: it applies the real
`peval_binop`/`peval_unop` smart-constructors to both recurrences (`z`'s
and `H`'s) in isolation and measures the resulting term's raw node count.

| n | `z`'s term size | `H`'s term size |
|---|---|---|
| 1 | 3 | 8 |
| 2 | 5 | 22 |
| 4 | 9 | 106 |
| 8 | 17 | 1,786 |
| 16 | 33 | 458,746 |

`z` grows exactly linearly (`2n+1`) — it's referenced once per iteration
(the `or`'s left operand), so nothing duplicates. `H` roughly **doubles
every iteration** (genuinely `O(2^n)`): it's referenced **twice** per
iteration (`andi a1,a0,1` and `srli a0,a0,1`, both feeding the same `xor`
that produces the next `H`), and Coq's term representation is a tree, not
a DAG with sharing — embedding the same current value into two different
sub-expressions of the next one creates two full copies of its entire
prior structure, and that compounds. `peval` has a rule that would collapse
exactly this kind of double-reference when it's shaped as `bvor(bvand(mask,
S), C)` (`bop.coalesce` — see `check-scalar-loop2-cost-drivers.md`, where
this is exactly what protects `check_scalar`'s own `c` accumulator, which
has the *same* double-reference shape as `H` but doesn't blow up). `H`'s
shape (`bvxor` of a *shift* and a masked-AND) doesn't match `bop.coalesce`'s
pattern — but a *different*, `H`-specific rule (`select_last_k`) was
already built for exactly this shape in an earlier session, confirmed
correct, then reverted for reasons unrelated to whether it worked (see
"Correction" in `key-schedule-loop2-cost-drivers.md` — currently it isn't
in the tree, but it isn't true that nothing was ever built for this).
Full writeup of the mechanism, applied to `H` directly:
`key-schedule-loop2-cost-drivers.md`.

**So the full answer**: `z` is cheap because single-reference recurrences
can't duplicate regardless of what `peval` does; double-reference
recurrences are only cheap if their specific shape happens to be one of the
patterns `peval` recognizes (as `check_scalar`'s `c` is) — otherwise, as
with `H`, they're genuinely exponential.

For check_scalar's own scaling story: loop 1 is not a source of the
combined function's superadditive cost (see
`check-scalar-combined-cost-drivers.md`) — whatever drives the combination
being worse than loop1+loop2 separately, it isn't loop 1's own recurrence.

## Files (throwaway, not in `_CoqProject`)

`ZZByteLoop1Common.v` (existing, baseline) + `ZZByteLoop1BL_N{16,32}.v` ·
`ZZByteLoop1NoFbCommon.v` + `ZZByteLoop1NF_N{16,32}.v` ·
`ZZLoop1NeutralCommon.v` + `ZZL1N_N{16,32}.v` ·
`ZZLoop1DoubleReadCommon.v` + `ZZL1DR_N{16,32}.v` ·
`ZZLoop1MemStoreCommon.v` + `ZZL1MS_N{16,32}.v` ·
`ZZTermSim.v` (the direct term-construction simulation).

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran <Common>.v
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran <Runner>.v 2>&1 | grep allocated_words
```
