# Byte-granular classed data block — measured payoff

Status: **Diagnostic record, 2026-08-19.** Measures the block added by
`plans/PLAN-unify-generators.md` stage 2, and re-runs the `check_scalar_loop1`
diagnostics it invalidates (that plan's G4).

## Finding, in one sentence

Grouping a byte-granular data block's cells into **one logic variable per
publicness class** instead of one per cell makes `check_scalar_loop1`'s VC
**1.10× cheaper at 2 declared cells, 1.32× at 4, and 1.77× at 8** — so it is
more than a constant factor, and it lowers the local growth exponent (1.462 →
1.198 over N=8→16), but **no exponent law may be quoted**: a fit on the two
smaller points under-predicts the third by 14–23% on both arms, so both curves
are still steepening and this range does not settle a law.

Two secondary findings, both about the records this re-run touched:

- The **`check_scalar_loop1` / `check_scalar_loop2` self-reference conclusions
  are CONFIRMED** (≈4–6%, matched-protocol), **but the evidence behind them was
  not sound** — their no-feedback rigs are `Admitted` and omit
  `solve_symbase_fetch` while their baseline rigs are full `Qed`. See
  §Protocol defect. This is a fresh instance of the trap
  `check-scalar-combined-cost-drivers.md` already documents.
- The **imports-only baseline moved from 434,833,198 to 604,283,692** (+39%).
  Re-using the recorded figure, as those records instruct, now corrupts every
  derived number by ~170M.

## The experiment

One axis: **how many logic variables the byte data block mints.**

| variant | byte block | variables minted | file |
|---|---|---|---|
| `uncl` | `gen_mem_pre_rel_bytes` | one per cell (N/4) | `Example/ZZAttrBaseUncl{,8,16}.v` |
| `cls` | `gen_mem_pre_rel_bytes_classed` | one per class (1) | `Example/ZZAttrBaseCls{,8,16}.v` |

Everything else is held fixed: same `loop1_instrs`, same
`loop1_reg_specs_rel n`, same `loop1_byte_specs_rel n` (which has **N/4**
entries, all `(false, PVExist)`, hence exactly one private class), same
`bound = 16+n`, same `fuel = 4n+8`, same `pcOutOfInstrs_exitCond`, same empty
word block. Both arms are **hand-built via `MkCFGVerifierContract`** rather than
through a generator, because after stage 2 no builder produces the unclassed
byte block any more (`gen_contract_u` and `gen_contract_rel_bytes` both class
it), so the control arm has no generator to call. Hand-building both preserves
the one-token property.

**Protocol, stated explicitly** (see §Protocol defect for why this matters):
both arms use `Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.`
— a real `Qed`, and `solve_symbase_fetch` included, on **both** sides.

## Results

`allocated_words`, one process per point, minus the **re-measured**
imports-only baseline of **604,283,692** (`Example/ZZImportsBase.v`).

| N | declared cells | `uncl` | `cls` | ratio |
|---|---|---|---|---|
| 8  | 2 | 263,462,071 | 240,151,632 | 1.097× |
| 16 | 4 | 725,805,940 | 551,053,032 | 1.317× |
| 32 | 8 | 2,586,832,030 | 1,465,402,340 | **1.765×** |

Doubling ratios:

| arm | N=8→16 | N=16→32 |
|---|---|---|
| `uncl` | 2.755× | 3.564× |
| `cls`  | 2.295× | 2.659× |

**Held-out fit check** (fit a power law on N=8 and 16, predict N=32):

| arm | exponent (8→16) | predicted N=32 | actual | error |
|---|---|---|---|---|
| `uncl` | 1.462 | 1,999,507,028 | 2,586,832,030 | **−22.7%** |
| `cls`  | 1.198 | 1,264,448,805 | 1,465,402,340 | **−13.7%** |

Both under-predict badly, so **neither arm is a power law over this range** and
no exponent may be quoted from it. What survives the check is weaker and
directional: the classed arm's local exponent is lower at *both* intervals
(1.198 vs 1.462 over 8→16; 1.410 vs 1.833 over 16→32).

## Reading the axis

The ratio grows monotonically with declared cell count — 1.097× at 2 cells,
1.317× at 4, 1.765× at 8 — which is what a *constant factor* would not do. So
this is not merely a level shift; the removed cost scales with the cell count,
consistent with the `|Σ|`-quadratic mechanism in
`check-scalar-combined-cost-drivers.md` §6.6 (one variable costs ~30–46× one
chunk, and makes every other transport more expensive because `env.lookup` is a
linear walk).

The variable count itself is confirmed directly rather than inferred
(`Example/ZZG3Count.v`): over `check_scalar_loop1`'s own 8-entry spec list the
unclassed block emits **8** binders (all named `"mw"`) and the classed block
emits **1** (`"mwprivb"`), with `mem_class_width` computing the grouped width as
**256** = 32×8. All 8 keys — `[16;20;24;28;32;36;40;44]` — land in the single
private class, because they are uniformly `(false, PVExist)`.

Cross-check on a second configuration: `check_scalar_loop1`'s *committed*
contract (8 cells, via the generator rather than hand-built) measures **1.54×**
(`Example/ZZVCB1{Cls,Base}.v`), against 1.765× for the hand-built rig at the
same cell count. The two differ in instruction body and in generator-vs-handbuilt
construction, so 1.54–1.77× is the honest range at 8 cells rather than a single
figure.

`PLAN-unify-generators.md` predicted **~1.1× at 8 cells**, extrapolating the
*word*-granular cell-count curve (1.00× at 1 cell, 1.02× at 2, 1.20× at 12,
1.41× at 16). That extrapolation **understates the byte case substantially** —
1.765× at 8 cells exceeds even the word curve's 16-cell value. A plausible
mechanism, offered as hypothesis and **not measured**: each byte cell emits four
chunks that each project from the minted variable through a `vector_subrange`,
where a word cell emits one, so eliminating N−1 variables strips ~4× more
variable-referencing structure. Isolating that would need a probe varying
granularity at fixed cell count.

## Protocol defect in the check_scalar loop records

**RETRACTED 2026-08-19 — the EVIDENCE, not the conclusion.**
`check-scalar-loop1-cost-drivers.md` and `check-scalar-loop2-cost-drivers.md`
each compare a baseline arm against a no-feedback arm to price the
self-reference axis. Those two arms **do not run the same tactic protocol**:

| rig | protocol |
|---|---|
| `ZZByteLoop1N16` / `N32`, `ZZByteLoop2N16` / `N32` | `vm_compute; solve_vc; solve_symbase_fetch.` **`Qed`** |
| `ZZByteLoop1NF_N16` / `NF_N32`, `ZZByteLoop2NF_N16` / `NF_N32` | `Time vm_compute. Time solve_vc.` **`Admitted`** |

The no-feedback arm therefore does strictly less work — it skips
`solve_symbase_fetch` and never pays the `Qed` VM cast, which re-runs the
executor. This is exactly the trap
`check-scalar-combined-cost-drivers.md` records ("a `Qed`+`solve_symbase_fetch`
denominator against an `Admitted` numerator invalidated two tables"), recurring
in two more records.

**The conclusions survive.** Measured on a properly matched pair at one commit
(both arms `Qed` + `solve_symbase_fetch`, N=32):

| arm pair | same-N ratio (baseline / no-feedback) |
|---|---|
| unclassed | 1.0613× |
| classed | 1.0411× |

So self-reference costs ~4–6% here, in the same "negligible" territory the
records concluded (0.4–1.4% at 2026-08-13), and stage 2 does not change that.
**Never requote the cross-protocol numbers as evidence** — and note that reading
the rigs as-is at the current commit yields a spurious **2.098×** for this axis,
which is the protocol gap, not a regression.

## What this means

- Stage 2's block is worth using wherever a byte-granular block has more than a
  couple of declared cells, and the benefit grows with that count. At
  `check_scalar_loop1`'s own 8 cells it is ~1.5–1.8×.
- **It is not established to be an exponent fix.** The held-out check fails on
  both arms; whatever is still steepening both curves is unidentified, and that
  sweep was not run. Do not describe this as removing a wall.
- The `|Σ|` axis is now closed for *declared cells* in both granularities —
  word (`gen_contract_rel_classed`, 2026-08-18) and byte
  (`gen_mem_pre_rel_bytes_classed`, here). The remaining `|Σ|` source named in
  the catalog, **per-step demonic variables**, is untouched.
- Both check_scalar loop records need their no-feedback rigs re-run under the
  baseline protocol before their self-reference tables can be cited as
  measurements. The conclusions do not need revisiting.

## Files / reproduction

Probes (throwaway, not in `_CoqProject`, `ZZ*` convention):
`ZZAttrBaseCls{8,16,}.v`, `ZZAttrBaseUncl{8,16,}.v` (the three-point pair),
`ZZAttrNfU2.v` / `ZZAttrNfC2.v` (no-feedback arm, matched protocol),
`ZZVCB1{Cls,Base}.v` (committed-contract cross-check),
`ZZG3Count.v` (binder count), `ZZImportsBase.v` (baseline).

```
# rebuild the Common .vo chain first -- stale ones fail with
# "makes inconsistent assumptions over library"
for f in ZZByteLoop1Common ZZByteLoop1NoFbCommon; do
  coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
    case_study/RiscvPmp/CFGVer/Example/$f.v
done
# one process per point
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/<Probe>.v 2>&1 \
  | grep -E 'allocated_words|Finished transaction|Error'
```

Note these probes carry no `Time`, so `Finished transaction` never appears;
completion was gated on absence of `Error` **plus** the `.vo` artifact being
produced. That is weaker than the two-marker gate and worth fixing by adding
`Time` if these are re-run.

**Two tooling traps hit while measuring**, both about the `coqc-guard` hook's
`ZZ*` exemption, which matches the literal command text `*CFGVer/Example/ZZ*`:
running `coqc` from *inside* `Example/` (bare filename) defeats it, and so does
routing the path through a shell variable (`$E/ZZ...`). Use literal full paths.
