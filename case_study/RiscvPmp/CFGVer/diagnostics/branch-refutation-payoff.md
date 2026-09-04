# Refuting an infeasible branch against `wco` removes the prefix-length quadratic

Status: **Diagnostic record, 2026-09-04.** Two-commit A/B of `cfdcc92f`
("the solver could DISCHARGE a formula but never REFUTE one") against its
parent. Prompted by "now measure the cost impact", after the fix had landed
with the commit message honestly saying cost was not measured.

## One-sentence finding

Refuting the loop's infeasible fall-through branch against a single path-condition
entry takes the loop-body segment contract from
**93.809 + 4.0506·P + 0.530681·P²** to **6.7197 + 0.029083·P + 0.00014974·P²**
M words in the prefix length `P` — a **3544× smaller quadratic coefficient**,
**275× at P=64** and **~722× at P=128** — and the surviving P-dependence is
*coefficient-identical* to the same contract with its counter PINNED, i.e. the
branch-specific prefix cost is gone entirely and only the generic table cost
every contract pays remains.

## 0. Protocol

| tag | protocol |
|---|---|
| **ALLOC** | `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc` process, `allocated_words` net of an imports-only baseline **re-measured per side**, arms run strictly serially |

Rig is `Example/ZZPadCommon.v` (the `prefix-length-cost.md` rig), unchanged.
Arms are generated `ZZM_*.v` files, `Qed` throughout, proof body
`vm_compute. solve_vc.` — plus, on the BASE side only, the three residual-closing
tactics the pre-fix code requires for the guarded arms (priced at ~0.004% by
`prefix-length-cost.md`, and the FIXED side needs none of them because the VC
closes outright).

**Two baselines, one per side, and the difference between them is REAL, not
noise:** BASE 605,973,425 / FIXED 606,230,828 (mean of two runs, spread 1,830).
The 251k-word gap is the cost of loading a slightly larger `Solver.vo` and is
why every net below is taken against its own side's baseline. Within a side the
baseline is deterministic: three consecutive BASE runs returned
605,973,538 / 605,973,538 / 605,973,538 — **identical to the word**, so the
noise floor is ~0 and the few-thousand-word tax figures in §3 are real.

`ZZPadCommon.vo` was rebuilt on each side before measuring (the documented
stale-`.vo`-after-`Prelude`-rebuild trap), nothing else was compiling during any
arm, and every arm was checked for `Error` and a nonzero return code.

## 1. The rig reproduces the published law before it reproduces anything else

Calibration first, because a 275× claim is worthless if the rig is not measuring
what the earlier record measured. Against `prefix-length-cost.md`'s fit
`93.809 + 4.0506·P + 0.530681·P²`:

| check | published | this BASE run | delta |
|---|---|---|---|
| `pbody` P=0 | 93.809 (fit constant) | 93.797 | **−0.0133%** |
| `pbody` P=64 | 2526.717 (fit) | 2526.677 | **−0.0016%** |
| `pflat 0 8` | 15.632 | 15.632 | **0.000%** |

## 2. The payoff

Guarded loop-body segment contract `pbody P`, M words net:

| P | before | after | speedup | "before" source |
|---:|---:|---:|---:|---|
| 0 | 93.797 | 6.7197 | **14.0×** | measured |
| 16 | 294.473 | 7.2281 | 40.7× | published fit |
| 32 | 766.846 | 7.8071 | 98.2× | published fit |
| 64 | 2526.677 | 9.1943 | **274.8×** | measured |
| 128 | 9306.963 | 12.8956 | 721.7× | published fit |

Only P=0 and P=64 were measured on the BASE side; the other three "before"
values are the published fit, which §1 validates at both measured points to
≤0.013%. They are interpolation, not measurement — do not quote them as data.

Post-fix law, fitted through P = 0, 64, 128:

```
after :  6.7197 + 0.029083·P + 0.000149736·P²      held out: P=16 −0.066%, P=32 −0.043%
before:  93.809 + 4.0506·P   + 0.530681·P²         (prefix-length-cost.md)
ratio :  14.0×      139×          3544×
```

**The quadratic is not eliminated — it is reduced 3544×.** At P=1000 the
surviving `c·P²` term would still be ~150 M words. Saying "the quadratic is
gone" would be wrong; saying "the branch-driven quadratic is gone" is right, and
§2.1 is why.

### 2.1 What remains is the generic table cost, not a branch cost

The pinned control `pbodyPin P` — same program, same table, same `|Σ|`, same
chunks, same fuel, same executed steps, differing only in that the path
condition also pins `k = 5` so the branch is decided by *computation* — is
untouched by the fix (it never had a live infeasible branch to refute). Fitting
it the same way:

```
guarded, after :  6.7197 + 0.029083·P + 0.000149736·P²
pinned,  after :  5.7852 + 0.029046·P + 0.000150074·P²
agreement      :            +0.13%        −0.23%
```

The two P-coefficients agree to **0.13% and 0.23%**. So after the fix the
guarded contract's response to prefix length is the *same function* as the
pinned contract's, offset by a constant 0.93 M (16.2%). The ratio of the two
arms at P=64 went from **306.3× to 1.113×**.

That is the strongest form the result can take: it is not "the branch got
cheaper", it is "the branch stopped having a prefix-length cost at all".

## 3. What it costs the contracts it cannot help

The rule runs on every formula against every `wco` entry, so the tax has to be
priced on contracts where it fires on nothing. Same arm, both sides:

| arm | before | after | tax | % |
|---|---:|---:|---:|---:|
| `pbodyPin 0` | 5.775 M | 5.785 M | +10,228 words | +0.177% |
| `pbodyPin 64` | 8.249 M | 8.259 M | **+10,228 words** | +0.124% |
| `pflat 0 8` | 15.632 M | 15.635 M | +2,320 words | +0.015% |
| `pflat 0 32` | 52.309 M | 52.311 M | +2,520 words | +0.005% |

The pinned tax is **the same 10,228 words at P=0 and at P=64** — bit-identical,
not merely close. So the tax is a fixed per-contract overhead, independent of
table size, and its *share* falls as the contract grows (0.18% → 0.005% across
this range). It scales with `|wco|` a little (the pinned arms carry two extra
conjuncts and pay 4× the flat arms' tax) and with nothing else.

There is no scaling penalty. This includes the `formula_eqb` `formula_propeq`
clause added in the same commit, which makes propeq-vs-propeq comparisons do a
real `Term_eqb` walk where they previously returned `false` instantly.

## 4. RETRACTION: "branch resolution cannot be the scaling cause"

Stated earlier the same day, in this session, before the fix was measured:

> the K-dependent cost is identical to 0.7% with no guard at all and split counts
> are invariant in P … the K² needs a register to hold a **symbolic value**, not
> an **unresolved branch**.

**That is refuted.** The counter `k` is still fully symbolic in every FIXED arm
above — nothing was pinned — and the quadratic died anyway.

The reasoning error is worth naming because it is easy to repeat. The evidence
was the `pbodyNG` arm: delete the `dec k ≠ 0` conjunct and the K-dependence does
not move. That correctly shows *the guard's presence is not what creates the
cost*. It was then read as *the branch is not what creates the cost* — but
deleting the guard makes the branch **genuinely undecidable**, so both successors
stay live and the cost must stay. Only *refuting* the branch removes a successor.
Deleting the reason something is decidable and deciding it are opposite
interventions, and the ablation only ruled out the first.

The correct statement: **the K² was driven by the live infeasible branch.**
Pinning the counter killed the quadratic because it let the solver kill that
branch by computation; that was one route to it, not evidence about symbolic
values.

## 5. Consequence for `prefix-length-cost.md` and for sub-table contracts

`prefix-length-cost.md`'s headline — "program length is a quadratic cost driver
for a symbolic segment contract, 26.93× at P=64" — is **superseded for code at
or after `cfdcc92f`**. Measured on the same rig, the same arm is now **1.368× at
P=64**. Its numbers remain correct as a record of the pre-fix executor, and its
cost law is what §1 calibrates against, so do not delete it — but never quote
26.93× as current.

Sub-table segment contracts (`project_subtable_contracts.md`, landed earlier the
same day) were motivated by exactly this quadratic. They remain sound and remain
the right thing for a contract to carry only its own instructions, and the
`(K/k)²` payoff never transferred to real muladd anyway (3.03×). But the
headline motivation is now largely gone: at P=64 the thing they were built to
avoid costs 1.37×, not 26.9×. **Re-measure the sub-table payoff before investing
further in it.**

## 6. Files

- Rig: `Example/ZZPadCommon.v` (unchanged, from `prefix-length-cost.md`)
- Arms: generated `Example/ZZM_*.v` (throwaway, not in `_CoqProject`)
- Fix under test: `cfdcc92f`, `theories/Symbolic/Solver.v` —
  `formula_refuted_by` + `assumption_formula`, and the `formula_propeq` clause
  added to `formula_eqb`
