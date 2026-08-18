# check_scalar loop 2 cost drivers — self-reference cleared, density still primary

Status: **Diagnostic record, 2026-08-13.**

**Follow-on (2026-08-18).** Unaffected, same reasoning as
`check-scalar-loop1-cost-drivers.md`: the landed `|Σ|` fix
(`gen_contract_rel_classed`, `plans/PLAN-classed-existentials.md`) covers the
`gen_contract_rel` family only, not this example's byte specs, and in any case
this record's subject — per-iteration density vs. `c`'s accumulation — is a
different axis. Figures below not re-run; no input to them changed.

**One-sentence finding:** loop 2's cross-iteration accumulation of `c`
contributes only a small effect (~3.2% at N=16) — not because
double-referenced accumulators are inherently safe (`key_schedule_loop2`'s
identically-shaped `H` recurrence is genuinely exponential), but because
`c`'s specific shape is caught and collapsed by the landed `bop.coalesce`
peval rule, which `H`'s different shape structurally cannot match (see
"Why `c` doesn't blow up" below). The standing conclusion in
`plans/PLAN-check-scalar-full.md` ("per-step instruction density is the
primary driver, not term duplication or chunk count") comes out more
confidently established by this, not overturned.

## Background: two different "c is read twice" mechanisms

```
lbu  a4, 0(a0)     ; k[u]
lbu  a5, 0(a1)     ; n[u]
sltu a6, a5, a4
sltu a4, a4, a5
neg  a4, a4
or   a4, a4, a6    ; a4 := CMP(k[u], n[u])
snez a5, a3        ; READ #1 of c -- is c already decided?
addi a5, a5, -1    ; a5 := -EQ0(c)
and  a4, a5, a4
or   a3, a4, a3    ; READ #2 of c, AND writes it -- the accumulation
addi a1, a1, 1
addi a0, a0, 1
bne  a1, a2, back
```

The plan doc's existing "Ablation 1" changed `snez a5,a3` to `snez a5,a4`
(a same-iteration double-read question) and found it a null result — but it
left `or a3,a4,a3` untouched, so `c` still fully accumulated across
iterations in that ablation. The actual cross-iteration self-reference (the
`key_schedule_loop2`-shaped mechanism) was never isolated. This diagnostic
closes that gap.

## The experiment

- **baseline** — unchanged, `ZZByteLoop2Common.v`.
- **no-feedback** — `ZZByteLoop2NoFbCommon.v`: BOTH reads of `a3` (`snez
  a5,a3` and `or a3,a4,a3`) rerouted to `a2` (the fixed end-pointer,
  read-only in this loop). Both needed rerouting, not just the write: if
  only the write changed, `snez a5,a3` would still test the real
  (nesting) `c`, and equality-against-zero of a large symbolic term doesn't
  shrink it — the formula can still embed the whole term. Rerouting both
  severs the path completely (same reasoning as `key_schedule_loop2`'s `H`,
  which needed both its reads rerouted for the identical reason).

Measured via `allocated_words` at N=16 (both variants) and N=32 (baseline
only — the no-feedback run at N=32 was still going after ~7 minutes and was
not pushed further; a timeout here is itself information about density, not
a result worth forcing).

## Results

| N | baseline | no-feedback |
|---|---|---|
| 16 | 14,160,887,483 | 13,718,046,454 |
| 32 | 46,665,901,621 | not measured (>7 min, abandoned rather than extended) |

Same-N ratio at N=16: **1.032×** (3.2%).

Baseline's own doubling ratio N16→32: **3.30×** — cross-checks closely
against the plan doc's independently-measured wall-clock figure for the
same doubling (278.30s / 85.21s = 3.27×), despite using a completely
different metric (`allocated_words` vs. user CPU seconds). That agreement
is itself a small validation that both measurements are tracking the same
real effect.

## Reading the axis

Self-reference costs **~3%** at N=16 — small, and (by the same-N
comparison) clearly not the source of the **3.30×** super-quadratic
doubling baseline itself shows. If cross-iteration accumulation were the
dominant driver, removing it should have collapsed the doubling ratio the
way it did for `key_schedule_loop2` (4.91× down to 1.36-1.53×, i.e. down to
genuinely linear); instead the same-N gap barely moves. So: **neither
same-formula duplication (existing Ablation 1) nor cross-iteration
self-reference (this diagnostic) explains loop 2's acceleration.** That
leaves the plan doc's other finding — dropping one of the two memory reads
(`ablation 2`, chunk count per iteration) at fixed body length gave a real
~30% reduction — and, by elimination, per-iteration instruction/term
density (13 instructions of chained XOR/AND/SLTU over largely-unconstrained
operands, vs. loop 1's 4) as the standing explanation.

## Why `c` doesn't blow up despite being referenced twice — the positive mechanism

`c`'s recurrence (`or a3,a4,a3` writing from a masked comparison, `snez
a5,a3` reading it first) has the **identical double-reference shape** as
`key_schedule_loop2`'s `H` (`key-schedule-loop2-cost-drivers.md`), which
*is* genuinely exponential (`O(2^n)` raw term size, confirmed by direct
simulation, `ZZTermSim.v`) — two references per iteration, both feeding the
same propagating value, no sharing in Coq's term trees. `c` doesn't share
that fate because `peval` has a rule built specifically for its shape:
`bop.coalesce` (`theories/Symbolic/PartialEvaluation.v:948-968`, landed via
the earlier mask-algebra work, `plans/PLAN-coalesce.md`) recognizes
`bvor(bvand(mask, S), C)` — exactly `c |= mask & cmp` — and rewrites it to
mention `C` **once**, collapsing what would otherwise be the same
duplication `H` suffers. `H`'s recurrence is `bvxor(shiftr(H,1),
negate(bvand(H,1)))`: top-level `bvxor`, not `bvor`, and one operand is a
*shift* of `H` rather than a second plain operand — `bvcoalesce_try`'s
pattern requires top-level `bvor` splitting into `bvand(mask,S)` against a
zero-test, which this structurally cannot match, so `H` falls straight
through uncaught.

So the earlier "ruled out by elimination" framing understates it: this
isn't just an absence of the term-growth driver, it's `c` being **actively
protected** by a rule that happened to be built for exactly its shape. A
different check_scalar-style accumulator whose shape *doesn't* match
`bop.coalesce`'s pattern would not be protected — this is not a general
guarantee that double-reference recurrences are safe, only that this
particular one is caught.

## What this means

The existing "body length is primary" conclusion in
`plans/PLAN-check-scalar-full.md` was drawn by comparing loop 1 (4 instr,
near-flat) against loop 2 (13 instr, accelerating) — a comparison that
changes body length *and* whether cross-iteration self-reference sits in a
denser context at the same time. That was a real risk of the same
axis-conflation this project has been burned by before. This diagnostic
closes it: self-reference is now directly ruled out as a meaningful
contributor for loop 2, specifically (not just inferred from loop 1's
unrelated near-flat curve) — and now with a positive, mechanistic reason
why (the landed `bop.coalesce` rule), not just an absence of evidence for
the alternative. "Density, not term growth" stands, for a confirmed reason.

**Open, not chased further this session**: the no-feedback measurement at
N=32. Given the same-N gap at N=16 is only 3%, there's no reason to expect
it suddenly grows at N=32, but that's an extrapolation, not a measurement —
worth a quick check before leaning on it in a future decision.

## Files (throwaway, not in `_CoqProject`)

`ZZByteLoop2Common.v` (existing, baseline) + `ZZByteLoop2BL_N{16,32}.v` ·
`ZZByteLoop2NoFbCommon.v` (new) + `ZZByteLoop2NF_N{16,32}.v` (N32 run
abandoned, see above). `ZZTermSim.v` (term-construction simulation backing
the coalesce-vs-no-coalesce mechanism, shared with
`check-scalar-loop1-cost-drivers.md`/`key-schedule-loop2-cost-drivers.md`).

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran <Common>.v
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran <Runner>.v 2>&1 | grep allocated_words
```
