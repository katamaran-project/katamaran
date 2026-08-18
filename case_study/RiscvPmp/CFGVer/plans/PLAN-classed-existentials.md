# PLAN-classed-existentials — one existential per publicness class

Status: **ALL FIVE PHASES COMPLETE (2026-08-18).** Gate PASSED twice — on Phase 3
alone and again after the Phase 4 migration. `gen_contract_rel_classed` exists,
its `ImplPre` bridge is proved with real `Qed`s, and the four committed contracts
that CAN use it do (see Phase 4 for why it is four, not nine).
`gen_contract_rel` and `gen_contract_noninterferent_rel(_simple)` are kept — they
remain correct for a mixed-publicness data block. No `Admitted` anywhere, and no
end theorem's statement changed.

## Why

`gen_mem_pre_rel` emits one `asn.exist` per `PVExist` entry, so `|Σ|` grows with
the declared data-cell count. Three independent rigs now agree that this — not
chunk count — is the dominant cost driver:

- `diagnostics/check-scalar-combined-cost-drivers.md` §6.6: chunk count is
  EXACTLY linear (held-out 0.00%); `|Σ|` is quadratic; one variable costs
  ~30–46× one chunk.
- `key-schedule-loop2-cost-drivers.md` (final sections): 82% → 86.4% of the
  declared-resource penalty is `|Σ|`, share rising with N. Total penalty over
  the 1-cell floor reaches 5.771× at N=32.
- `PLAN-byte-memory.md` §10 driver (C): the same factor from the other side,
  turning a VC doubling-slope of 1.39 into 1.02.

And the win needs **no weakening**: N independent words are in bijection with one
N-word vector, so one grouped existential is *equivalent* to N separate ones —
measured within 0.16% of the (weaker) shared-variable arm. `PVConst`-pinning is
therefore strictly dominated and should not be pursued.

## Phase 1 — the generator (LANDED)

`GenContract.v` gains, all additive:

| name | role |
|---|---|
| `mem_class_width {K} : list K -> nat` | `xlenbits * length`, structurally |
| `gen_mem_cells_class {Σ} {K}` | cells of one class, peeling `xlenbits` bits per entry |
| `mem_spec_is_exist` / `mem_spec_is_pub` | classification on `mem_spec_rel` |
| `mem_full_is_exist` / `mem_full_is_pub` | ditto on `mem_full_spec`, for the bridge |
| `mem_rel_keys` / `mem_full_keys` | key projections |
| `gen_mem_pub_class_rel` / `gen_mem_priv_class_rel` | one existential per class; empty class emits nothing |
| `gen_mem_pre_rel_classed` | pinned entries (unchanged) ∗ public class ∗ private class |
| `gen_contract_rel_classed` | `gen_contract_rel` with that final conjunct swapped |

**Three implementation facts, each of which cost time to find:**

1. **Use `uop.bvtake`/`bvdrop`, NOT `uop.vector_subrange`.** The latter carries
   an implicit `IsTrue (s + l <=? n)` that `Prelude.v:297`'s Hint Extern
   discharges only for LITERAL offsets, so it cannot be used under a fold over a
   runtime list at all. `bvtake`/`bvdrop` are typed on `m + n` with no side
   condition, and `mem_class_width (cons k r)` is DEFINITIONALLY
   `xlenbits + mem_class_width r`, so the slices typecheck with zero proof
   obligations. This also makes the bridge easier — see Phase 3.
2. **Index the width by the KEY LIST, not by a list of address TERMS.**
   `length (map f L) = length L` is only propositional.
3. **No concrete (`mem_full_spec`) classed builder.** Mirroring
   `gen_mem_pre_rel_concretize` would require
   `mem_class_width (mem_rel_keys L)` and
   `mem_class_width (mem_full_keys (map (concretize_mem ia) L))` to agree
   definitionally; they agree only propositionally, so it would need a dependent
   transport across a type index (the width-index trap,
   `core-executor-internals` §6).

**Heap order changes** — pinned, then public, then private, rather than spec
order. Sound (`∗` is commutative) but it moves consume-scan positions and hence
residual shapes, which is a migration risk (Phase 4).

## Phase 2 — feasibility (MEASURED)

Rig: `Example/ZZKslClassCommon.v` + `ZZKslCLS_N{32,64,128}.v`, on
`key_schedule_loop`'s REAL shape (pointer advances, one declared cell per trip),
byte-identical to `zzkcd_cfg_contract_param` except the generator call.

| N | unpinned `gen_contract_rel` | classed | win |
|---|---|---|---|
| 32 | 15.526 G words | **4.689 G** | **3.31×** |
| 64 | did not finish in 10 min | **14.205 G, completes** (399 s `vm_compute`) | — |
| 128 | — | **NOT MEASURED** | — |

**N=64 now completes where it previously did not.** Two honest caveats:

- The baseline at N=64 was given 10 minutes and did not finish; a longer run was
  started and **killed before completing**, so "infeasible" is evidenced by that
  plus the extrapolated ~70 G words / ~30 GB peak, NOT by a completed
  measurement. Re-run it in the background if the claim needs to be firm.
- This box has **40 GB of swap** and the classed N=64 run reported a 17.9 GB peak
  heap, so it was swapping. "Feasible" here means "completes via swap", not "fits
  in RAM", and its wall-clock is therefore not a performance figure.
- N=128 was queued behind the killed baseline run and never started.

## Phase 3 — the `ImplPre` bridge (COMPLETE)

**Every lemma is in `EndToEnd.v` with a real `Qed`**, from the bv cells core up
to `gen_contract_noninterferent_rel_classed`. The sections below are in the order
they were developed; the estimate that the bv half was the easy half held.

### How it was developed, and why a separate harness was needed

`ZZClassBridge.v` is a throwaway file carrying `EndToEnd.v`'s import block
verbatim plus `Require Import EndToEnd`. Reasons, all load-bearing:

- An in-progress `Admitted` inside `EndToEnd.v` would put an axiom in the
  trusted chain and fail the gate. Develop outside, move in when proved.
- **`pet` OOMs replaying `EndToEnd.v` in position mode** (RSS > 7.6 GB), so
  `rocq_start(file=EndToEnd.v, theorem=…)` is not available. Iterating against
  this small file instead costs ~11–900 ms per `rocq_check`.
- The import block must be copied through **line 94**, not 90. Stopping early
  leaves `memGS2` / `PredicateDef` instances unresolved and *every* statement
  fails with `UNDEFINED EVARS`. `Import IrisModelBinary.RiscvPmpIrisBase2` is
  the one that matters.

### The proof, and the two statement choices that make it work

```coq
Lemma gen_mem_cells_class_intro `{sailGS2 Σ}
    (ks : list N) {Σ0} (ι : Valuation Σ0)
    (pterm : Term Σ0 ty_xlenbits) (pv : Val ty_xlenbits)
    (mwt : Term Σ0 (ty.bvec (mem_class_width ks))) (μ1 μ2 : Memory)
    (Hp : inst pterm ι = SyncVal pv)
    (Hmw : inst mwt ι = (NonSyncVal (words_app μ1 pv ks) (words_app μ2 pv ks)
                         : RelVal (ty.bvec (mem_class_width ks)))) :
  ([∗ list] k ∈ ks, interp_ptstomem (width := 4) …) ⊢ asn.interpret (gen_mem_cells_class ks … mwt) ι.
```

- **`mwt` must be a PARAMETER, not `term_var "mw"`.** `gen_mem_cells_class`'s
  cons branch applies itself to `term_unop (uop.bvdrop xlenbits) mwt` — a
  non-variable term at the *same* logical context. A statement that fixed the
  third argument to a variable puts the IH at a different context and it will
  not apply. This was the one real design insight.
- `pterm` is a parameter too (cf. `byte_addr_rel`), so one lemma serves the
  base-relative and concrete address forms.
- The `: RelVal (ty.bvec …)` ascription on `Hmw` is REQUIRED: without it
  elaboration reads the RHS as `RV (bv _)` and fails with
  `Could not find an instance for "Inst ?T (RV (bv …))"`.
- `words_app` (the concatenation of a class's cell values) is the witness and
  must be defined before the lemma can be stated.

Proof shape, for reference: `generalize dependent mwt; induction ks`, then in
the cons case `rewrite big_sepL_cons`, `cbn [gen_mem_cells_class asn.interpret]`,
`iSplitL`; head closes with
`unfold bop.evalRel, uop.evalRel; cbn; rewrite !bv.take_app; iApply "Hhead"`,
tail with an `assert` discharged by `rewrite !bv.drop_app` then `iApply (IH _ Hd)`.
Note plain `cbn` is what exposes the `evalRel` form — `cbn [inst inst_env]`
leaves `luser` folded, and `rewrite !bv.take_app` then finds no subterm.

### Steps 1–2 DONE (2026-08-18, commit `e802bd3b`)

All four lemmas are now **in `EndToEnd.v`, proved with real `Qed`s**, no
`Admitted` anywhere in the file, and `KeyScheduleLoopResult.vo` rebuilds green:

| lemma | role |
|---|---|
| `words_app` | the concatenation witness |
| `gen_mem_cells_class_intro` | core bridge, `NonSyncVal` (private class) |
| `gen_mem_cells_class_intro_sync` | `SyncVal` twin (public class) |
| `gen_mem_priv_class_ks_intro` | class wrapper, supplies the `iExists` |
| `gen_mem_pub_class_ks_intro` | ditto, plus discharges `secLeakvar` |

Two structural findings from doing it:

- **`GenContract.v` now splits `gen_mem_{pub,priv}_class_ks` out at the KEYS
  level**, with the specs-level definitions as thin wrappers. Required, not
  cosmetic: the wrapper proofs must `destruct` the key list to handle the empty
  class, and `destruct (mem_rel_keys specs)` fails with *"Conclusion depends on
  the bodies of ..."* because the existential's type mentions
  `mem_class_width` of it. With keys as a plain variable the destruct is trivial.
- **The public class genuinely needs its own `SyncVal` cells lemma.** `secLeak`
  matches on the CONSTRUCTOR (`Formulas.v:117`), so `secLeak (NonSyncVal v v)`
  is `False` however equal the sides are — a `NonSyncVal` witness makes
  `secLeakvar` on the grouped variable unprovable. The proof script is otherwise
  character-identical between the two.

Third mechanical trap, on top of the two above: the `secLeak` goal arrives as
`instprop (formula_secLeak …) ι`, so a bare `exact I` fails with *"The term I has
type True while it is expected to have type instprop …"* — `cbn` first.

`ZZClassBridge.v` is trimmed to its import block only, so it cannot shadow the
real lemmas; it is kept as the iteration harness for any further work here.

### The partition obstacle: SOLVED (2026-08-18, commit `53569cff`)

Five lines, once the right existing lemma was found. Three lemmas, all in
`EndToEnd.v` with real `Qed`s:

| lemma | role |
|---|---|
| `three_way_perm` | `l` is a permutation of its three-way filter partition |
| `big_sepL_three_way` | generic: split a `big_sepL` three ways by two booleans |
| `interp_mem_partition` | the instance for `interp_mem_with_public_memory` |

**Why it is provable at all:** Iris's `big_opL_permutation` applies to bodies of
the form `λ _ : nat, f` — index-INDEPENDENT ones — and
`interp_mem_with_public_memory`'s body ignores the index. So the resource list can
be re-associated into `pinned ++ public ++ private` even though the classed
precondition groups by publicness while the resources arrive in spec order.

Two things not to re-derive:

- **`rewrite Permutation_middle` matches an UNINTENDED instance** in the partition
  proof and leaves an unprovable goal. `Permutation_cons_app` is the exact shape:
  `l ≡ₚ l1 ++ l2 → a :: l ≡ₚ l1 ++ a :: l2`.
- **Use `big_sepL_fmap` to move the `map` INSIDE**, so the filters stay on the
  original spec list. The other order additionally requires filter/map
  commutation.

### Phase 3 steps 0–3: DONE (2026-08-18)

All in `EndToEnd.v`, real `Qed`s, file compiles green. Nine further lemmas:

| lemma | role |
|---|---|
| `concretize_mem_is_exist` / `_is_pub` | the two classifications agree under `concretize_mem` |
| `filter_map_concretize_mem` | filter/map commutation, generic in the predicate pair |
| `filter_{pinned,pub,priv}_concretize` | its three instances |
| `gen_init_mem_filter_pinned` | restricting to the pinned class leaves `gen_init_mem` unchanged |
| `interp_mem_group_{priv,pub}` | per-group resource conversion |
| `interp_mem_partition_rel` | `interp_mem_partition` with the filters at the `mem_spec_rel` level |
| `gen_implpre_mem_class` | the classed memory `ImplPre` |
| `gen_contract_noninterferent_rel_classed` | the end bridge |

The scoping estimate held — nothing here needed more than one attempt. Four
things worth not re-deriving:

- **The per-group lemmas need only the `is_pub` hypothesis, not `is_exist`.**
  `interp_mem_with_public_memory` branches on the publicness bit and ignores the
  value slot entirely, so the group conversion never has to know the group is
  `PVExist`. The plan above expected both hypotheses; one suffices, and dropping
  the other removes the only place `filter_In` would have needed two projections.
- **`gen_init_mem_filter_pinned` is why the caller's unfiltered
  `declare_init_memory` hypotheses are enough.** `gen_init_mem` is an `omap` that
  already drops `None` entries and `concretize_mem` sends exactly the non-pinned
  entries to `None`, so filtering to the pinned class is a no-op on it. Its proof
  needs `unfold gen_init_mem in *` — unfolding only in the goal leaves the IH
  folded and `rewrite IH` finds no subterm.
- **`μ1`/`μ2` are strict-implicit in `gen_implpre_mem_class`** (they occur in
  `HInitMem1`'s type), and this differs from the same statement at a file's top
  level. A positional call reports `"μ1 has type Memory while RelVal
  ty_xlenbits was expected"`, which reads like a statement bug. The call site
  uses named arguments.
- Two parser traps in this file's notation environment, both pure noise but both
  cost a round trip: `rewrite A, B` (comma form) is a **syntax error** — use two
  `rewrite`s; and a one-element delta flag `cbn [map]` is a syntax error
  (`[smart_global] expected after '['`) while `cbn [map List.filter]` parses —
  qualify it as `cbn [List.map]`.

## Phase 3 — original scoping notes (kept)

Target:

```coq
Lemma gen_implpre_mem_class `{sailGS2 Σ}
    (specs : list mem_spec_rel) (ia : N) (μ1 μ2 : Memory) {Σ0} (ι : ...) :
  interp_mem_with_public_memory μ1 μ2
    (map mem_full_to_spec (map (concretize_mem ia) specs)) ⊢
  asn.interpret (gen_mem_pre_rel_classed specs) ι
```

**The bv side is the EASY half, and easier than `PLAN-byte-memory.md` §10
feared.** §10's warning was about proving `subrange i w = appView-peel i w`.
Because Phase 1 used `bvtake`/`bvdrop` instead, the needed lemmas are
`bv.take_app` and `bv.drop_app` (`Bitvector.v:947,974`) applied directly — the
induction peels one word per step with no bridging lemma. The existential witness
is the CONCATENATION of the cell values (`NonSyncVal (w1_0 ++ w1_1 ++ …)
(w2_0 ++ …)` for a private class), built up by the same induction.

**The actual obstacle, identified but not attacked: a `big_sepL`
partition/permutation.** `interp_mem_with_public_memory` is a `big_opL` over the
resource list in SPEC ORDER, while `gen_mem_pre_rel_classed` groups by class. So
the proof must first re-associate the resource list into
`pinned ++ public ++ private`. `∗` is commutative so this is true; it needs
either a `big_sepL` permutation lemma or a partition-and-recombine argument, and
it is where the work is. Do not start by writing the bv slicing — that part is
short.

Also needed: `secLeakvar "mwpub"` on the grouped variable must be discharged from
the N per-cell public facts. Composition direction only (`SyncVal` is closed
under construction), and `simplify_secLeak` already decomposes `secLeak` through
unops down to variable leaves, so the symbolic side is fine; this is the Iris
side.

### Phase 3 smoke test — the classed path EXERCISED (2026-08-18)

Nothing in the tree used `gen_contract_rel_classed`, so the end bridge was
unexercised. `Example/ZZClassSmoke.v` (throwaway) reuses **Cmovznz4's instrs and
specs verbatim** — 12 declared cells, all `PVExist`, all private, the largest
declared-cell count among the nine committed examples — changing only the
generator call. `Example/ZZClassBase.v` is the same file with
`gen_contract_rel`, as a matched baseline. Both compile clean.

| | classed | unclassed baseline |
|---|---|---|
| `vm_compute; solve_vc; solve_symbase_fetch` | 10.14 s | 11.38 s |
| its `Qed.` | 2.70 s | 3.95 s |
| **VC total** | **12.84 s** | **15.33 s** (→ **1.19×**) |
| peak RSS (whole file) | 7.43 GB | 7.48 GB |
| `Print Assumptions` on the end theorem | `pure_decode`, `mmioenv` | *identical* |

Three things this settles:

1. **The heap-order change did NOT move cmovznz4's residuals.** The VC closes
   with the *byte-identical* tactic line. That was the headline Phase 4 risk, and
   on the hardest of the nine examples it did not materialise. It is evidence, not
   a proof, for the other eight.
2. **The classed chain is axiom-clean** — the same two framework parameters as
   the baseline, no new assumptions.
3. **The win at 12 cells is 1.19×.** Do NOT generalise this to the migration as
   a whole — this plan did, wrongly, until the per-example sweep below was run.

## Phase 4 — migrate the examples (DONE 2026-08-18)

Requested explicitly, re-confirmed with the user after Phase 3's smoke test put
numbers on it. Recorded risk, stated at the time: the committed examples declare
FEW cells (`key_schedule_loop` has 2), so they save little, while the heap-order
change may move VC residual shapes. All-or-nothing behind a green gate.
(The "save little" half turned out to be right for the 1- and 2-cell examples and
WRONG for the 16-cell one — see the per-example sweep below.)

### The scope was 4 contracts, not 9

`gen_contract_rel_classed` is the classed counterpart of `gen_contract_rel`, and
only four committed contracts use that builder:

| contract | declared cells |
|---|---|
| `modpow_win_full_cfg_contract_param` | 16, all private `PVExist` |
| `cmovznz4_cfg_contract_param` | 12, all private `PVExist` |
| `key_schedule_loop2_cfg_contract_param` | 2 |
| `countdown_mem_cfg_contract_param` | 1 |

The other ten committed contracts are **not migratable and have nothing to
gain**: eight use `gen_contract_param` (concrete `mem_full_spec`), for which a
classed builder cannot be written at all — the width-index trap documented at
`GenContract.v:536` — and seven of those eight pass `[]` for memory, so there are
no cells to group. One (`BearSSLCheckScalarLoop1`) uses
`gen_contract_rel_bytes`, whose data block already groups per word.

### The heap-order risk did NOT materialise — on any of the four

This was the whole reason the phase was expected to be per-example debugging
rather than a sweep. **Every one of the four VCs closed with its tactic line
completely unchanged**, first try:

| example | VC file rebuild |
|---|---|
| `Countdown.v` | 10.15 s / 4.33 GB |
| `KeyScheduleLoop.v` | 15.14 s / 4.40 GB |
| `Cmovznz4.v` | 19.45 s / 4.64 GB |
| `BearSSLModpowFull.v` | 42.97 s / 6.27 GB |

Why the fear was overstated, in hindsight: `consume` is order-sensitive, but all
four examples' data blocks are *homogeneous* — every cell is private `PVExist`
(or, for the 1- and 2-cell cases, too small for order to matter). The pinned and
public classes are empty, so `gen_mem_pre_rel_classed`'s reordering is the
identity on these lists. **Expect the risk to be real only for an example that
mixes pinned/public/private cells**, which none of the committed nine do.

### Per-example cost sweep (2026-08-18) — measured, all four

The single cmovznz4 number was being quoted as if it characterised the migration.
It does not. Rigs `Example/ZZVC{Cd,Ksl,Cmv,Mpf}{Cls,Base}.v`: contract + VC only
(deliberately NO `EndToEnd` require, so this measures the VC and not the Iris
load), ONE heavy sentence per `coqc` process so they cannot contaminate each
other, and the two files of a pair differ in exactly one token — the generator
call. User CPU from `-time`, peak RSS from `/usr/bin/time`.

| example | cells | classed VC+`Qed` | unclassed | win | peak RSS cls/base |
|---|---|---|---|---|---|
| `countdown_mem` | 1 | 1.509 + 0.06 = **1.569 s** | 1.516 + 0.06 = 1.576 s | **1.004×** | 4.332 / 4.333 GB |
| `key_schedule_loop2` | 2 | 3.473 + 3.523 = **6.996 s** | 3.579 + 3.541 = 7.120 s | **1.018×** | 4.406 / 4.417 GB |
| `cmovznz4` | 12 | 8.540 + 2.403 = **10.943 s** | 9.702 + 3.405 = 13.107 s | **1.198×** | 4.629 / 4.732 GB |
| `modpow_win_full` | 16 | 19.985 + 14.325 = **34.310 s** | 26.974 + 21.301 = 48.275 s | **1.407×** | 6.275 / 6.916 GB |

Reading it:

- **1 → 2 → 12 → 16 cells gives 1.00 → 1.02 → 1.20 → 1.41**, a coherent
  superlinear curve consistent with the `|Σ|` cost the diagnostics identified, and
  extrapolating sensibly toward the 3.31× at 32 cells. Four points, one curve.
- **At 1–2 cells the win is nil** (inside noise). At 1 cell it *must* be — one cell
  is one existential under either builder — so that row doubles as a check that the
  two arms really are matched; it comes out as the identity to 0.4%.
- **At 16 cells it is 1.41×**, appreciably better than the ~1.1–1.2× this plan
  previously asserted for the whole 2–16 range.
- These numbers are NOT comparable to the `ZZClassSmoke`/`ZZClassBase` pair above,
  which loaded `EndToEnd`. But cmovznz4's 1.198× here independently replicates that
  rig's 1.19×, which is a useful cross-check on both.

Whole sweep is ~4 min to re-run.

### What the migration touched

One new lemma plus eight one-line swaps — and the **trusted statement surface did
not move**: every `*_noninterferent_param` conclusion is byte-identical, only the
contract the VC is taken over changed.

- `EndToEnd.v`: `gen_contract_noninterferent_rel_classed_simple` added, the
  classed twin of `_rel_simple`, so a Result file changes by one identifier.
- 4 × `Example/<Prog>.v`: `gen_contract_rel` → `gen_contract_rel_classed`.
- 4 × `Example/<Prog>Result.v`: `gen_contract_noninterferent_rel_simple` →
  `..._rel_classed_simple`.
- Stale prose references to the old builder fixed in the same commit.

`gen_contract_rel` and `gen_contract_noninterferent_rel(_simple)` are all KEPT —
they are still the right builders for a mixed-publicness data block, and
`gen_contract_rel_bytes` has no classed variant.

**But note the consequence: those three now have ZERO callers in the tree.** They
are still *proved* (they are `Lemma`s with `Qed`s in `EndToEnd.v`, so the gate
keeps validating them), but no VC reduces through them any more, so the
combination — a real symbolic VC taken over `gen_contract_rel` — is no longer
exercised by anything. If you later need that path (a mixed-publicness block),
expect to be its first user since 2026-08-18 and budget accordingly.
`Example/ZZClassBase.v` is the cheapest way to smoke-test it. By contrast
`gen_mem_pre_rel` IS still load-bearing — `gen_mem_pre_rel_classed` uses it for
the pinned group (`GenContract.v:530`).

## Phase 5 — gate (DONE 2026-08-18, PASSED TWICE)

`GATE_JOBS=1 ./scripts/gate.sh` on this 14 GB box, run twice: once on Phase 3
alone (pre-migration baseline) and once after the Phase 4 migration. Both:

```
✓ GATE PASSED — build clean, no holes, 14 end theorems axiom-clean
  (only: Machine.pure_decode Base.mmioenv).
```

So the classed builder introduces **no new assumptions** — that pair is the
project's accepted baseline, and it is exactly what the Phase 3 smoke test
reported, which retroactively validates that reading.

One operational note: the axiom probe chose batches of 8 and peaked at ~8 GB,
which on this box means swapping (0 GB available at the peak) and a noticeably
slower second batch. It completed. If it ever gets OOM-killed instead, that
arrives as a bare exit 143 — set `GATE_PROBE_BATCH=4`.

## Files

Generator: `GenContract.v`. Bridge + end theorem: `EndToEnd.v`. Migrated
contracts: `Example/{Cmovznz4,Countdown,KeyScheduleLoop,BearSSLModpowFull}.v`
and their four `*Result.v` files.

Rigs (throwaway, not in `_CoqProject`, so they are NOT kept green by the gate —
expect them to rot):
- `Example/ZZVC{Cd,Ksl,Cmv,Mpf}{Cls,Base}.v` — the per-example matched cost sweep
  (8 files, ~4 min for the whole set). The right rig to re-run if the classed
  builder or the `|Σ|` cost model changes; better isolated than
  ZZClassSmoke/ZZClassBase because they omit `EndToEnd`.
- `Example/ZZClassBridge.v` — Phase 3 iteration harness (import block only).
- `Example/ZZClassSmoke.v` / `ZZClassBase.v` — the Phase 3 smoke test and its
  matched unclassed baseline, on Cmovznz4's specs. Rebuild these two if you ever
  need to re-measure the classed-vs-unclassed delta at a given cell count; they
  are the cheapest matched comparison available (~30–45 s each).
- Phase 2 feasibility: `Example/ZZKslClassCommon.v`, `ZZKslCLS_N{32,64,128}.v`,
  `ZZKslClassBase.v`.
- Earlier measurement rigs: `ZZKslShrCommon.v`, `ZZKslBigCommon.v`,
  `ZZKslPinCommon.v`, `ZZPadShrCommon.v` and their runners.

---

## Hand-off notes (2026-08-18)

### Environment traps that will cost hours if rediscovered

These are not about the proofs; they are about being able to iterate at all.

1. **`pet` OOMs replaying `EndToEnd.v` in position mode** (>7.6 GB), so
   `rocq_start(file=EndToEnd.v, theorem=…)` is unavailable. Iterate against
   `Example/ZZClassBridge.v` instead — it carries `EndToEnd.v`'s import block and
   `Require Import EndToEnd`, giving all Iris names at ~11–900 ms per
   `rocq_check`. It deliberately defines nothing.
2. **That import block must be copied through line 94, not 90.** Stopping early
   leaves `memGS2` / `PredicateDef` unresolved and *every* statement fails with
   `UNDEFINED EVARS`. `Import IrisModelBinary.RiscvPmpIrisBase2` is the one that
   matters.
3. **`rocq_compile_file` defaults to `keep_vo=false` and DELETES the `.vo`.** A
   `mode="vos"` check on `EndToEnd.v` silently removed `EndToEnd.vo`, after which
   sibling files failed with "Cannot find a physical path bound to logical path".
   Pass `keep_vo=true` whenever anything downstream will require the result.
4. **Hooks will block builds**, by design: `coqc-guard.sh` denies a build whose
   target changed with no interactive check since (any `rocq_check` clears it),
   and rate-limits to 3 builds / 15 min. `rocq_compile_file` is the sanctioned
   alternative. `skill-path-guard.sh` denies edits to `GenContract.v` /
   `EndToEnd.v` without the matching skill loaded once per session.
4b. **`rocq_compile_file` reported SUCCESS on an `EndToEnd.v` that `coqc`
   rejects** (2026-08-18) — a hard `Wrong argument name` error, and the `.vo` it
   left behind lacked the new lemmas entirely (`strings EndToEnd.vo | grep
   <lemma>` → 0) while the source's mtime came out *newer* than the `.vo` it had
   supposedly just produced. Two consequences: **treat `make -f Makefile.coq
   <file>.vo` as the authority for this file**, and after any `rocq_compile_file`
   on it, verify with `strings … | grep` that the names you added are actually
   in the artifact. A commit was made on the strength of the false green.
5. A `git checkout` of a file changes its mtime and trips the build guard even
   though the content is identical.

### Proof idioms specific to this work

- Plain `cbn` is what exposes the `evalRel` form; `cbn [inst inst_env]` leaves
  `luser` folded and a subsequent `rewrite bv.take_app` finds no subterm.
- Any `inst mwt ι = NonSyncVal …` hypothesis needs the
  `: RelVal (ty.bvec …)` ascription or elaboration fails to find
  `Inst ?T (RV (bv …))`.
- `secLeak` goals arrive as `instprop (formula_secLeak …) ι`; `cbn` before
  `exact I`.
- Dependent-width traps have bitten three times (concrete builder, `remember`
  in the wrappers, term-list indexing). The reflex: keep ONE width index, derive
  it from the list you are inducting on, and never state an equation whose two
  sides carry different-but-equal-length index expressions.

### Phase 4 turned out NOT to be the risky one — what the fear was, and why it missed

This section predicted that migrating the committed examples would need
per-example debugging, because `gen_mem_pre_rel_classed` changes the HEAP ORDER
(pinned, then public, then private, rather than spec order) and `consume` is
order-sensitive (`core-executor-internals`), so a residual shape could move and a
`solve_vc`/`solve_symbase_fetch` line could stop closing.

**It did not happen — all four VCs closed with unchanged tactic lines, first
try.** The reasoning was sound but the premise was not checked: reordering by
class is the IDENTITY on a homogeneous data block, and every committed example's
block is all-private `PVExist`. The lesson generalises — before budgeting for a
reordering risk, check whether the reordering is even non-trivial on the actual
data.

The two rules written for that phase were followed and remain right for any
future migration:

- **All-or-nothing behind a green `./scripts/gate.sh`** (`GATE_JOBS=1` on a
  ≤16 GB box).
- **Never "fix" a failing VC by weakening a spec entry or admitting a lemma.**
  The gate's `Print Assumptions` on end theorems is the only thing that catches
  it, and it runs last. If an example will not close, leave it unmigrated and say
  so — but note the benefit is strongly cell-count dependent: nil at 1–2 cells,
  1.20× at 12, 1.41× at 16 (measured; see the per-example sweep).

The cost/benefit of Phase 4 was genuinely poor and was flagged before it was
requested; it was re-confirmed with the user, with the smoke-test numbers in
hand, before being carried out.
