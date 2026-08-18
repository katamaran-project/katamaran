# PLAN-classed-existentials — one existential per publicness class

Status: **Phase 1 LANDED green (`bfdf7ec2`, `3eefda6f`). Phase 2 measured.
Phase 3: core + wrappers + THE PARTITION OBSTACLE all PROVED and in
`EndToEnd.v` (`e802bd3b`, `53569cff`); what is left is routine plumbing, no
unknowns. Phases 4–5 NOT STARTED.** Additive throughout — every
existing example and `gen_contract_rel` itself are untouched, no `Admitted`
anywhere, and the tree is green (`KeyScheduleLoopResult.vo` rebuilt).

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

## Phase 3 — the `ImplPre` bridge (ALL HARD PARTS PROVED)

**The core lemma and both class wrappers are PROVED with real `Qed`s and now
live in `EndToEnd.v`** (see "Steps 1–2 DONE" below). The bv half of the bridge is
done, and the estimate below — which called it the easy half — held.

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

`ZZClassBridge.v` is now trimmed to its import block only, so it cannot shadow
the real lemmas; it is kept purely as the iteration harness for step 3.

### What remains in Phase 3

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

### What remains in Phase 3 — routine, no unknowns

1. **Per-group resource conversion.** For each class, turn
   `interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec (filter … specs))`
   into the `[∗ list] k ∈ mem_rel_keys …` form the wrappers consume. Two
   ingredients: the filter's `In` facts (via `filter_In`) pick the `if pub`
   branch, and `bv.of_N_add` relates `concretize_mem`'s `of_N (ia + k)` to the
   wrappers' `bv.add (of_N ia) (of_N k)` — the same rewrite
   `gen_mem_pre_rel_concretize` already uses.
2. **`gen_implpre_mem_class`** assembling `interp_mem_partition` + (1) + the two
   class wrappers + the existing `gen_implpre_mem` for the pinned group.
3. **`gen_contract_noninterferent_rel_classed`**, mirroring the `_rel` bridge.

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

## Phase 4 — migrate the 9 examples (NOT STARTED, gated on Phase 3)

Requested explicitly. Recorded risk, stated at the time: the committed examples
declare FEW cells (`key_schedule_loop` has 2), so they save almost nothing, while
the migration touches the trusted statement surface and the heap-order change may
move VC residual shapes. Must be all-or-nothing behind a green gate — do NOT land
a partial migration.

## Phase 5 — gate (NOT STARTED)

`./scripts/gate.sh` with `GATE_JOBS=1` on this ≤16 GB box. The only check that
catches an unsound `empty` in the new builder, via `Print Assumptions` on the end
theorems.

## Files

Generator: `GenContract.v`. Rigs (throwaway, not in `_CoqProject`):
`Example/ZZKslClassCommon.v`, `ZZKslCLS_N{32,64,128}.v`, `ZZKslClassBase.v`;
plus the earlier measurement rigs `ZZKslShrCommon.v`, `ZZKslBigCommon.v`,
`ZZKslPinCommon.v`, `ZZPadShrCommon.v` and their runners.
