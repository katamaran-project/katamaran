# PLAN-classed-existentials — one existential per publicness class

Status: **Phase 1 LANDED and green (2026-08-18, commits `bfdf7ec2`, `3eefda6f`).
Phase 2 measured. Phases 3–5 NOT STARTED.** Additive throughout so far — every
existing example and `gen_contract_rel` itself are untouched, and the tree is
green.

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

## Phase 3 — the `ImplPre` bridge (NOT STARTED)

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
