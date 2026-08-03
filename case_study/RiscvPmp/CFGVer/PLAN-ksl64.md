# PLAN-ksl64 — `key_schedule_loop` at N=64: restore the solver fold, prove it, land it

Status: DRAFT, **NOT THE ACTIVE CAMPAIGN** (2026-08-03). Written, then parked
the same day in favour of whole-function BearSSL verification — the first of
which (`modpow_win_full`, 28 instrs, nested loops, 16 data words) landed
axiom-clean that afternoon without needing anything in this plan.

**Why parked, and what would un-park it.** §3's two-driver analysis is the
reusable part and it survives: driver 1 (term explosion) is narrow — the fold
buys exactly the GHASH `mulx` idiom and nothing else in the corpus — while
driver 2 (`cells × steps`) is generic to every array-loop program. The decisive
observation is that **`key_schedule_loop` is the outlier, not the template**:
its array size IS its trip count (it builds a 256-entry table by construction),
so it cannot be scaled down. Every other target has array size independent of
loop structure, so a complete function verifies at a reduced word count — which
is what `modpow_win_full` did, comfortably, at 12 resident cells and 122 steps.
Un-park this plan if `key_schedule_loop` at N≥32 becomes a goal in its own
right, or if a second GHASH-shaped idiom appears. §1's recovery instructions
were verified against HEAD and should still apply; re-check the `git apply -R`
before trusting them.

Successor campaign to `PLAN-chunk-gc.md` (LANDED same day). Recovers and
completes the work removed in `027d7c27`.

Prior record, all still accurate and worth reading before starting:
`PLAN-term-sharing.md` (Plan A refuted), `PLAN-havoc-secrets.md` (refuted),
`PLAN-solver-fold.md` (**deleted in `027d7c27`; Phase A restores it**),
`PLAN-chunk-gc.md` §12/§13, memory notes `project-key-schedule-loop-scaling`
and `project-chunk-gc-landed`.

---

## §0. Why now

The solver fold was removed on 2026-07-24 with the verdict *"didn't fix the
real bottleneck"*: it was **algebraically correct and did kill the 3^N term
wall**, but bought only ~12% wall-clock at N=8 because a *separate*
`O(steps²)` driver dominated everything.

**That driver is now gone.** The chunk-GC landed 2026-08-03: the leaked
`encodes_instr` chunk is dropped every step, the allocation model's quadratic
coefficient went 6.75M → ≈0, and the isolated `zzf` reproducer is affine to
0.0001% from N=8 through N=64 (`PLAN-chunk-gc.md` §13).

So the removal verdict is **obsolete, not wrong**: it measured the fold under a
regime where a quadratic swamped it. The fold's own contribution — collapsing
the register value term from 3^N to O(N) — is exactly what should dominate once
the quadratic is subtracted, and it has never been measured in that regime.
This plan re-measures it first and only then funds the proof.

**Acceptance target** (unchanged since `PLAN-term-sharing.md`): the
`key_schedule_loop` 32-bit analogue verified **end-to-end noninterferent at
N=64**, axiom-clean, gate green. Rungs on the way: N=4, 8, 16, 32.

---

## §1. What exists to recover — verified, not remembered

Everything removed by `027d7c27` (*"Remove select_last_k solver-fold
infrastructure"*) still applies **cleanly in reverse** against today's HEAD:

```
$ git show 027d7c27 | git apply -R --check -
FULL REVERSE PATCH APPLIES CLEANLY (all 13 files)
```

Per-file drift audit since `027d7c27`:

| file | drift | restore route |
|---|---|---|
| `theories/Syntax/UnOps.v` | **none** | exact checkout |
| `theories/Syntax/Terms.v` | **none** | exact checkout |
| `theories/Symbolic/PartialEvaluation.v` | **none** | exact checkout |
| `theories/Symbolic/Solver.v` | 3 commits | reverse patch, **verified clean** |
| probe files (`ZZProbeKSL*`, `ProbeFoldAlgebra.v`) | n/a | see §4 — do **not** blanket-restore |
| `PLAN-solver-fold.md` | n/a | restore verbatim (historical record) |

What the restore brings back:

- **`uop.select_last_k (k : nat) : UnOp (bvec 32) (bvec 32)`** (`UnOps.v`) — a
  new `UnOp` constructor whose `eval` is `select_last_k_eval`, the exact replay
  of `mulx`'s per-round update. `R = 0xE1000000` is hardcoded in `eval`
  (deliberate: for any other constant the op is not a "select"). `k` is plain
  metadata, no type-level role.
- **the `peval_bvxor` graft** (`PartialEvaluation.v`) — `peval_bvxor {n}`
  dispatches at `n = 32` to `peval_bvxor_fold32`, falls through to
  `peval_binop' bop.bvxor` at every other width; wired into `peval_binop`'s
  `bop.bvxor` case (which had **no** simplification before this work). The
  recognizer is `bvxor_fold_try_split` / `_try_match_select_last_k` /
  `_try_match_shiftr_amt` / `_try_match_folded` + `bvxor_fold_mask_chain`.
- **5 opaque-default clauses** across `Solver.v` and `Terms.v` for the new
  constructor.
- The **already-fixed selector bug**: `select_last_k_eval_rec`'s per-step
  selector is `bit_k(V) xor bit0(Correction_k)`, not `bit_k(V)` alone. The
  naive version is invisible for `k < 24` (R's 24 trailing zeros) and silently
  wrong from k≈25 — i.e. **exactly in the N=32/64 range this plan targets**.
  It was found by hand-deriving the proof, never by any test. Do not "simplify"
  it back.
- `ProbeFoldAlgebra.v`'s **proven, axiom-free `bv 32` algebra**: `mulx_spec`
  (the 8-op mask chain = `(A>>1) ^ (bit0(A)?R:0)`), `mulx_linear`,
  `mulx_incremental`, plus `bit_lxor`, `bit_shiftr`, `shiftr_lxor`,
  `lxor_assoc`/`comm`/`nilpotent`, `shiftr_zero`, `sel_spec`, `mulx_sel`,
  `mulx_step`. This is most of §6's supporting-lemma bill, already `Qed`'d.

---

## §2. What is **not** proven — read this before trusting the skeleton

Exactly one hole was introduced by the original work: **`peval_bvxor_sound`
is `Admitted`** (in the `Hint Resolve` list feeding `peval_binop_sound`, which
keeps its own `Qed` because `auto` picks up the admitted hint).

`peval_bvxor_fold32_sound` carries a **partial** proof script with two
`admit`s. **Its skeleton is not merely incomplete — it is set up wrongly**, and
Phase C must not build on it as-is:

```coq
generalize (bvxor_fold_try_match_shiftr_amt 1 t2); intro match_shiftr.
destruct match_shiftr as [Z | ].
```

`generalize` **discards the equation linking `Z` to `t2`**, so the `Some Z`
branch has no hypothesis that `t2 = shiftr Z 1` and is unprovable as posed.
The `None`/`false` leaves close by `reflexivity` (they return the term
verbatim) which is why the script looked healthy. Redo with
`destruct … eqn:E` plus the inversion lemmas of §6 step 3.

Treat the "structure and dispatch are complete" comment in the restored file
as covering steps 2.1–2.2 only.

---

## §3. The two remaining drivers — and only one of them is the fold's

**Driver 1 — term explosion (what the fold fixes).** The masking body rebuilds
the secret `A0` from 3 copies of its own previous value per round, so the
register term grows ~3^N. Measured pre-fold: N=8 → 0.42 s just to `Term_eqb`
the term against itself, N=12 → 19.8 s, N=16 → ~1300 s extrapolated. With the
fold the accumulator is the O(N) shape, confirmed by dumping the raw VC at
N=3/N=4 (`v` occurs exactly N+1 times, constants correctly aged one `mulx` per
round).

**Driver 2 — the memory-cell quadratic (NOT the fold's, and it hits us).**
`PLAN-chunk-gc.md` §13 found that `zzn_contract n` balloons post-fix because it
declares `n` memory cells that sit in the heap for the whole run and are
**never touched by `chunk_gc`** (which filters only `is_encodes_instr`). `n`
persistent chunks across `14n` steps is its own `O(n²)`. `zzn 32` was killed at
8.55 GB; the cell-pinned `zzf 32` completed at 4.86 GB.

**`key_schedule_loop` has exactly the `zzn` shape**: instruction 11 is
`sw a0, 0(a3)` with `a3` advancing by 4 each trip, and
`key_schedule_loop2_mem_specs` declares one cell per trip. At N=64 that is 64
persistent cells across 896 steps. **This is the single biggest risk to the
N=64 target and it is independent of everything the fold does.** Phase B
measures both arms so we learn which driver we are actually fighting before
committing to Phase C or Phase D.

---

## §4. PHASE A — mechanical restore  [HAIKU]

Work on a topic branch (`solver-fold-restore`), per `branch-workflow`. **Do not
merge to `KatamaranRel` before Phase C closes the `Admitted`** — see the Gate A
note on why the gate *does* catch it, but only via check (3).

**A1.** Restore the four `theories/` files and the plan doc:

```
git checkout 027d7c27^ -- theories/Syntax/UnOps.v theories/Syntax/Terms.v \
                          theories/Symbolic/PartialEvaluation.v \
                          case_study/RiscvPmp/CFGVer/PLAN-solver-fold.md
git show 027d7c27 -- theories/Symbolic/Solver.v | git apply -R
```

`Solver.v` is the only drifted file and the reverse patch is verified to apply;
if that ever stops being true, the five sites are `simplify_eq_unop_val`,
`simplify_eq_unop`, `simplify_propeq_unop` (direct `match op with`) and the two
`Term_bvec_case` positional argument lists in `simplify_eq_binop_bvapp'` /
`bvcons'`. All five treat the constructor as opaque/default, exactly like
`uop.negate` beside them.

**A2.** Restore `ProbeFoldAlgebra.v` as a **`theories/`-side scratch file only**
(e.g. keep it out of `_CoqProject`, or park it under
`case_study/RiscvPmp/CFGVer/Example/`). It is source material for Phase C, not
a build target. It is `Admitted`-free (checked), so it will not trip the gate's
hole scan — but see A4.

**A3.** Do **not** restore `ZZProbeKSL*.v` / `ZZProbeKeyScheduleTiming.v`.
They were written against the pre-`nextpc-param`, pre-chunk-GC executor and a
`mem_full_spec` shape that has since changed; recreating the sweep fresh in the
current `ZZProveRunZf*` convention (§5) is cheaper than repairing them.

**A4.** Full-tree recompile: `make -f Makefile.coq` (or the gate's build), not
just CFGVer. `peval_bvxor` fires at **every 32-bit xor in every case study**
(`xlenbits = 32`), including MinimalCaps and the three BearSSL examples. The
recognizer is constant-specific so it should be a no-op everywhere else, but
that is a claim to verify, not assume.

### GATE A — mechanical, no judgement
1. Whole tree compiles.
2. `grep -rn 'Admitted\.' theories/` reports **exactly one** hit:
   `peval_bvxor_sound`. (`peval_bvxor_fold32_sound` is also `Admitted` in the
   restored file — expect **two** if the partial skeleton is kept; either is
   fine, just record which.)
3. All 12 existing `_param` end theorems still build.
4. `Print Assumptions` on one existing end theorem now shows
   `peval_bvxor_sound` — **this is expected and is the reason Phase A/B must
   not be merged.** The gate's hole scan (`SCOPE_DIRS=case_study/RiscvPmp/CFGVer`)
   does **not** cover `theories/`, so the `Admitted` is caught by check (3)
   axiom-cleanliness, not check (2). Do not "fix" this by editing the gate.

---

## §5. PHASE B — the measurement gate  [HAIKU runs, SONNET/owner interprets]

**This gate decides whether Phase C is funded at all.** The whole reason this
work was dropped once is that its payoff was measured against a confound; do
not skip or shortcut it.

Build an N-parameterized contract family in the current probe convention
(`ZZDiagCommon.v` / `ZZProveRunZf*.v` are the models — one file per rung, one
`Time`d goal each, never several heavy `vm_compute`s in one file; see
`rocq-timeout-triage` on measurement hygiene). Three arms, N ∈ {4, 8, 16, 32, 64}:

| arm | trip count | mem cells | isolates |
|---|---|---|---|
| **B-fold** | N | 1 (pinned store address) | driver 1 alone, fold ON |
| **B-nofold** | N | 1 (pinned store address) | driver 1 alone, fold OFF (baseline) |
| **B-real** | N | N (advancing pointer, the real program) | drivers 1 + 2 together |

"Fold OFF" = stash the `peval_binop` `bop.bvxor` wiring only; everything else
identical. Pinning the store address is a *diagnostic* change to the program,
not a candidate deliverable — it exists to separate the drivers, mirroring
exactly why `zzf_contract` exists beside `zzn_contract`.

**Scale all four knobs together every time**: loop-counter register (`A4`),
`cfg_fuel` (`14·N + slack`), the **mem spec list**, and the exit-condition
address. Under-scaling the mem specs produces a spurious
`∀v, secLeak v → False` residual that looks identical at every N and cost about
an hour of misdiagnosis last time.

**Metric: `allocated_words`, not wall clock.** Wall time on this box swings
with page-cache state (an unchanged file measured 22/43/32 s on three
consecutive runs) and `Qed` re-runs the executor. Report wall time as
secondary.

### GATE B — the decision point
- **B-fold vs B-nofold must show the fold collapsing the curve** (nofold should
  be unable to reach N=16 at all; fold should be affine-ish through N=32).
  If the fold fires and the curve still does not collapse, **stop** — that means
  a *third* driver beyond term size, binder count and heap size, and more
  probing beats more building. Report back rather than pushing on.
- **B-real vs B-fold sizes driver 2.** If B-real reaches N=64 within the memory
  envelope (~8 GB peak RSS is where this box starts dying), Phase D is not
  needed. If B-real dies at N=32 the way `zzn` did, Phase D becomes required
  work and its scope needs its own decision.
- Verify the fold actually *fires* on today's executor output before trusting
  any number: dump `DebugCFGVerifierContract` at N=3 and grep the final
  `chunk_ptsreg x10` entry for the `select_last_k` shape (the N=3 expected term
  is recorded verbatim in the restored `PLAN-solver-fold.md` Phase 1 update).
  The `encoded_instr` word column and the chunk GC both landed after the
  recognizer was written; the ALU-chain term shape *should* be untouched, but
  that is the cheapest possible thing to check first.

---

## §6. PHASE C — close `peval_bvxor_sound`  [SONNET]

Only start once Gate B is green. The restored `PLAN-solver-fold.md` §2.1–2.7 is
the detailed script and remains valid; the deltas below are what this plan adds.

**C1 — where the `bv` lemmas must live.** `peval_bvxor_sound` is in
`theories/Symbolic/PartialEvaluation.v`, *upstream* of `case_study/`. So
`ProbeFoldAlgebra.v`'s lemmas **cannot** be cited from where they sit — migrate
the load-bearing ones into `theories/Bitvector.v` (which today has essentially
no `shiftr`/`lxor` algebra: `shiftr`/`lxor` are bare definitions, ~6 mentions
total). Keep them `bv 32`-specific if that is what is already proven;
`select_last_k` is 32-fixed, so genericity buys nothing here.

**C2 — the one genuinely new mathematical fact**, `select_last_k_bump`:

```coq
Lemma select_last_k_bump (V : bv 32) (k : nat) :
  mulx (bv.shiftr V (bv.of_N (N.of_nat k) : bv 6) `bv.lxor` select_last_k_eval k V)
  = bv.shiftr V (bv.of_N (N.of_nat (S k)) : bv 6) `bv.lxor` select_last_k_eval (S k) V.
```

It is **known true** — hand-derived, and `select_last_k_eval` was corrected
specifically to make it hold unconditionally for every `k`. Given the three
supporting facts (shift composition `shiftr (shiftr V k) 1 = shiftr V (S k)`
generic in `k`; `shiftr` distributes over `lxor`; bit-of-xor and
bit-after-shift), it unfolds to `reflexivity` on `select_last_k_eval_rec`'s own
`S k'` clause — **no induction on `k`**. `ProbeFoldAlgebra.v` already proves the
distribution and bit lemmas and the `k=1` instance of composition; the generic-`k`
composition is the one genuinely missing piece.

**Prove it standalone in a throwaway `bv`-only file before touching
`PartialEvaluation.v`** — same cheapest-failure-point discipline as every other
phase gate in this project.

**C3 — redo the skeleton.** Per §2: `destruct … eqn:` + inversion lemmas for
the three `Equations`-defined recognizers (`funelim`/`simp` apply to those;
`peval_bvxor_fold32` itself is a plain `Definition`, so `funelim` does **not**),
and `Term_eqb_spec` for the `mask_chain` comparison.

**C4 — the `Term`-level mask-chain fact.** `⟦bvxor_fold_mask_chain Z⟧ ι =
if bit0(⟦Z⟧ ι) then R else 0` — this is `mulx_spec` lifted to a valuation.
The lift is free (`mask_chain` is pure `bv` arithmetic, no `relop`, no `bool`),
per `relval-rewrite-over-secrets`. Check first whether a `Term`-level version
already exists from the k=2-fold era before re-deriving.

**C5 — soundness risk to keep in view.** The recognizer must check the
*embedded constants* (the specific `R`, the specific shift amounts), not just
the constructor skeleton; an under-constrained recognizer that fires on a
same-shaped chain with a different constant would be silently unsound. Verify
this holds in the restored recognizer as part of the proof, not by inspection.

### GATE C
1. Zero `Admitted`/`admit`/`Axiom` in `theories/` attributable to this work.
2. `Print Assumptions` on all 12 existing `_param` end theorems is back to the
   pre-existing allowlist (`Machine.pure_decode`, `Base.mmioenv`).
3. Full gate green (`scripts/gate.sh`, bound `-j` by RAM).

---

## §7. PHASE D — the memory-cell quadratic  [CONDITIONAL on Gate B]

Only if B-real cannot reach N=64. Do **not** pre-build this.

The cost is heap-size × step-count with N separately-owned `ptstomem` chunks
resident throughout. Candidate directions, cheapest first — this needs its own
plan and its own decision checkpoint before any code:

- **(a) Accept and re-scope.** Land N=32 with N cells, and N=64 only in the
  cell-pinned form. Honest, cheap, and arguably still the interesting result
  (the loop shape and the masking algebra are what the example is about).
- **(b) Aggregate representation.** Replace N per-word chunks with one
  gmap-valued memory chunk, mirroring what the instruction store already did
  (list+base-offset → finite map, see `project_cfgver_gmap_pivot`). Structural,
  invasive, touches the trusted assertion vocabulary and every `_with_mem`
  example.
- **(c) A second GC arm.** Drop *written-and-never-reread* cells the way
  `chunk_gc` drops `encodes_instr`. Note the affinity argument that made
  `chunk_gc` sound (drop is fine in an affine BI, only completeness is at
  stake) applies here too, but the census argument would have to be redone —
  and unlike `encodes_instr`, these chunks are named in the postcondition.

**Do not attempt (b) or (c) on the strength of this paragraph.** It exists so
Gate B's negative branch has somewhere to land, not as approved work.

---

## §8. PHASE E — land the example  [SONNET, then OWNER]

1. Add the N-parameterized program to the trusted surface:
   `Example/KeyScheduleLoop.v` gains the N=64 instruction list / reg specs /
   mem specs (statement-relevant — `Results.v` references them by name), plus
   the `_param` contract and `valid_*_param` VC.
2. `Example/KeyScheduleLoopResult.v` gains the end theorem via
   `gen_contract_noninterferent_rel`; add it to `Results.v` and to
   `scripts/gate.sh`'s axiom-clean list.
3. Keep `Example/Prelude.v` free of `EndToEnd`, keep the example file free of
   Iris — the light/heavy split is worth ~1.2 GB per example and is easy to
   undo by accident (`CFGVer/CLAUDE.md`).
4. Regression: all 12 existing `_param` theorems unchanged and axiom-clean.
5. Full gate green.
6. **Docs in the same commit as the code** (`CLAUDE.md` hygiene rule):
   - `cfgver-executor` — the new `peval` rule, its fragility (syntactic, not
     semantic: any rewording of the masking idiom silently stops benefiting,
     with no error and no speedup), and the fact that the term-explosion wall
     is now addressed for *this idiom only*.
   - `core-executor-internals` — `select_last_k` and the `peval_bvxor` dispatch.
   - `rocq-implementation` / `bv-pitfalls` — whatever the C2 proof teaches.
   - Route any skill *description* edit through `skill-routing-maintenance`
     (hook-enforced).
   - Update `.claude/TODO.md`'s "full real `GHASH::key_schedule` loop" item and
     the memory notes `project-key-schedule-loop-scaling` (which currently
     records the fold as removed) and `project-chunk-gc-landed`.

---

## §9. Traps checklist — every one of these has already cost this project time

1. **Scale all four knobs together** (counter, fuel, mem specs, exit address).
   Under-scaled mem specs → a spurious `∀v, secLeak v → False` residual,
   identical at every N.
2. **`zzn` vs `zzf`**: a reproducer whose parameter conflates trip count with
   cell count makes a fix look like it failed. Always have a cell-pinned arm.
3. **Trust `allocated_words`, not wall clock**; `Qed` re-runs the executor.
4. **One heavy `Time Eval vm_compute` per file** — several in one file
   contaminate each other.
5. **The selector bug** (`bit0(Correction_k)` in the `select_last_k_eval`
   recursion) is invisible below k≈24 and fatal at exactly the N this plan
   targets. Do not simplify the recursion.
6. **`generalize` in the restored soundness skeleton discards the recognizer
   equation** (§2).
7. **The gate's hole scan does not cover `theories/`** — an `Admitted` there is
   caught only by the axiom-cleanliness check on the listed end theorems.
8. **`peval_bvxor` fires at every 32-bit xor tree-wide**, not just in
   `key_schedule_loop`. Full-tree recompile is part of Phase A, not an
   afterthought.
9. **GADT matching**: any raw match on `Term Σ σ` must keep the width a genuine
   bound variable, use `Equations` (not vanilla `match`), and put the
   "return the scrutinee unchanged" fallback in an outer `option` match. The
   restored code already embodies this; the full write-up is in
   `PLAN-solver-fold.md` Phase 1.

---

## §10. Open decisions for the owner

1. **Deliverable shape if driver 2 bites** — real advancing-pointer store with
   N cells (Botan-faithful, may not reach N=64) vs. accepting a cell-pinned
   N=64 alongside a real N=32. §7(a).
2. **Is the measurement gate mandatory** (recommended: yes — Phase C is the
   expensive half and its payoff has never been measured post-chunk-GC), or
   should Phase C start in parallel on the strength of the algebra already
   being proven?
3. **Where the recovered `bv` algebra lands** — a new section in
   `theories/Bitvector.v` (recommended) vs. a dedicated
   `theories/BitvectorMasking.v`.
