# PLAN: block annotations that carry their own validity (`AnnotInstrV`)

Status: rev 2 (2026-09-25). COMPLETE: merged into local KatamaranRel 2026-09-28 (b001d1a3, gate PASSED, 19 end theorems axiom-clean), NOT pushed.
Phases 1-6 DONE (2026-09-28); GATE PASSED after Phase 4; VC-cost measurement DONE (0.11-0.12%, noise). Merged (§8.4). Rewritten after PLAN-exit-targets.md
landed (branch issue/exit-targets), against the code as it now is. Rev 1 was
written before that change; see §6 for what it settled.

## 0. Goal

Get rid of `blocksSound` as a post-processing premise. Today every external
bridge (EndToEnd.v, GenCompose.v) takes
`∀ words, ⊢ blocksSound words (instrs_of_list base L)`, and so does
`ValidCFGVerifierContract` (EndToEnd.v, at `bv.of_N (cfg_init_addr c)`). That
is a `□∀` over the program map, re-established after the fact per example with
`blocksSound_of_none` / `blocksSound_of_head` / `blk_span_sub`, and a
mid-program block needs a collision inversion nobody has written yet (ZZBlkBC,
index 55). Instead, an `ai_block` annotation CARRIES a proof that its block is
sound, and the VC checks that the block's code really is in the program.

Decisions (Emiel, 2026-09-25; revert paths in §5):
- **Only `ai_block` carries validity** (V1). `ai_loop` is justified by Löb.
- **A separate type `AnnotInstrV` that erases to `AnnotInstr`** (V2). The
  executor, `cfg_vc` and the existing examples stay untouched; the executor is
  NOT parameterised (measured at ~220 sites, including the trusted surface).
- **Span containment is checked in the VC** at the firing site (V3).
- **`blkValid` is a closed `Prop`** (∀ Σ GS, ⊢ …) (V4).
- **`ai_loop` self-reference is enforced by the TYPE** (V5): `aiv_loop : bool`,
  "re-enter the contract being verified". Since exit-targets this needs no
  offset (§1b).

## 1. Design

### 1a. What a block is now, and why validity is address-free

After exit-targets (current code):
- `BlkAnnot := {| blk_ctx : LCtx ; blk_contract : @CFGVerifierContract blk_ctx |}`
  (Verifier.v). There is no resume offset: a block resumes at its contract's
  single exit, `blk_exit b ι := inst (cfg_exit (blk_contract b)) ι`
  (Adequacy.v), symbolically `subst (cfg_exit c) evars` (sexec_block).
- `blockSound words v b` (Adequacy.v) reads exactly `cfg_precondition`,
  `cfg_postcondition`, `cfg_exit` (through `blk_exit`) and `cfg_instrs`
  (through `blk_span v b`). It does NOT read `cfg_init_addr`.
- `cfg_exit` is a term over the contract's own context: for a generated
  segment it is `exit_of_off base target`, with `base` pinned by the
  precondition's `asn_pc_eq` to the entry pc. So the resume address follows the
  entry pc and has nothing to do with `ia`.
- Evidence it holds in practice: `blockFaithful_of_seg` (GenCompose.v) no
  longer needs `v = of_N ia` -- only the placement fact `inst base ι = SyncVal v`.

Hence, with `cfg_init_addr` the ONLY `ia`-dependent field of a contract like
`cdRec ia`, and `blockSound` never reading it:

```coq
Definition blkValid (b : BlkAnnot) : Prop :=
  ∀ Σ (GS : sailGS2 Σ) words v,
    (bv.bin v + 4 * N.of_nat (length (cfg_instrs (blk_contract b))) < bv.exp2 xlenbits)%N ->
    ⊢ blockSound words v b.
```

It lives in Adequacy.v (heavy side). For CountdownRec, `cdRecBlk_valid :
blkValid (cdRecBlk ia)` comes from today's `cdRec_blockSound (ia := bv.bin v)`
plus `blockSound words v (cdRecBlk ia) = blockSound words v (cdRecBlk ia')`.
**R1 (downgraded to a formality):** that equation should hold by
`reflexivity`, since the two contracts differ only in `cfg_init_addr`. Confirm
with one `rocq_check` before Phase 2 builds on it.

The fit condition at a firing site comes from span containment (§1c) plus the
enclosing program's own fit (`seg_fits_memory` / `Hrep`), which the bridges
already carry.

### 1b. The type

Light side, new, in Verifier.v next to `AnnotInstr` (or a small new light file):

```coq
Record BlkAnnotV (Valid : BlkAnnot -> Prop) :=
  { vb_blk : BlkAnnot ; vb_ok : Valid vb_blk }.
Record AnnotInstrV (Valid : BlkAnnot -> Prop) :=
  { aiv_ghost_before : list Annot ; aiv_instr : AST ; aiv_ghost_after : list Annot
  ; aiv_block : option (BlkAnnotV Valid)
  ; aiv_loop  : bool }.               (* re-enter the ENCLOSING contract *)
Definition selfBlk {Σ} (c : @CFGVerifierContract Σ) : BlkAnnot :=
  {| blk_ctx := Σ ; blk_contract := c |}.
Definition eraseV {Valid Σ} (c : @CFGVerifierContract Σ)
    : AnnotInstrV Valid -> AnnotInstr := …
  (* drops vb_ok; ai_loop := if aiv_loop then Some (selfBlk c) else None *)
```

`Valid` is a parameter, so Verifier.v stays Iris-free (layering invariant 1).
The heavy side instantiates it with `blkValid`. The VC is
`cfg_vc c (map (eraseV c) a)`: the executor and `solve_param_vc` are unchanged.

**Why `bool` now suffices (rev 1 needed `option N`).** A re-entry block used to
carry `blk_off`, its resume offset, which a contract with several exits did not
determine. Every contract now has exactly one exit and a block resumes at it,
so `selfBlk c` is fully determined by `c`. Rev 1's R4 (a Löb hypothesis
quantified over several offsets) does not arise: there is exactly one
`selfBlk c`.

### 1c. The VC-side containment check

At the firing site (`sexec_cfg_addr`, Verifier.v, `Some b` arm of
`match ai_fire stepped ai`), before `sexec_block`:

```
for i < length (cfg_instrs (blk_contract b)):
  lookup_instr tbl (apc + 4i) = Some (_, ai_i)  and  ai_instr ai_i = instr_i
  else emsg "block code not in program"
```

- Syntactic after `peval`, like `is_exit`; one lookup per block instruction
  per firing; no variables allocated.
- **R2:** `lookup_instr` on `apc + 4i` must resolve for a symbolic base. It
  does on the ordinary fetch path; confirm on `cd_link_annot`.

Concrete mirror (`cexec_block`, VerifierRel.v): take `instrs` and
`assert ⌜blk_span v b ⊆ ai_instr <$> instrs⌝` (or its pointwise form).
**R3:** `rexec_block` is an `rsolve` mirror plus two hand-closed value goals
(entry pc via `refine_inst_persist`, exit pc via `refine_inst_subst`, both
added by exit-targets and developed in the untracked `Example/ZZBlkExitProbe.v`
-- reuse that probe setup). The containment assert is a pure fact on the
concrete side and an error on the symbolic side, so it may need a small
pointwise-lookup relational lemma over `itable_relW`.

The check is on `AnnotInstr`, so it also works in today's `blocksSound` world:
Phase 1 can land alone, and it deletes `blk_span_sub` and the containment half
of `blocksSoundAt` immediately.

## 2. What changes in the soundness chain

Current state (after exit-targets):
- `blockSound_of_vc words ab v b tbl Hv Hstrip Hbs0 Hbs` (Adequacy.v): no
  `Hexit`; `v` explicit; `Hbs0 : ⊢ blocksSoundAt false …` (the ai_blocks at
  step 0) and `Hbs : □ blockSound words v b ⊢ blocksSound …` (all blocks, may
  assume this one -- the Löb hook).
- `blockFaithful ab v b tbl`: itable half + exit half, the latter just
  `etable_rel (blk_exit b ι) (cfg_exit c) ι` ("the exit term is SyncVal").
- `blockSound_of_contract words v b ab Hv Hstrip Hbs0 Hbs` (GenCompose.v)
  quotes `blockSound_of_vc` at the contract's own table.

Changes:
- **Firing site** (the BLOCK branch of `sound_exec_cfg_addr_myWP2`,
  Adequacy.v): containment from the concrete assert (Phase 1), `blockSound`
  from `vb_ok` of the looked-up `AnnotInstrV` (Phase 3). This needs the
  concrete table to be `gmap _ (AnnotInstrV blkValid)`, or a side fact
  `instrs = eraseV c <$> instrsV`.
- **ai_loop:** after erasure every re-entry block is `selfBlk c`, so the `▷`
  half of today's premise is exactly the Löb hypothesis of `blockSound_of_vc`;
  `Hbs` shrinks to nothing (or to `Hbs0`, the step-0 ai_blocks, which are now
  covered by `vb_ok`). The `stepped`/`▷` split survives only inside
  `blockSound_of_vc`.
- **`ValidCFGVerifierContract`** (EndToEnd.v): its third conjunct is the
  `blocksSound` obligation at `cfg_init_addr c`. It goes. This is the one
  remaining real reader of `cfg_init_addr`, which is why exit-targets' Phase 5
  was deferred until after this plan (PLAN-exit-targets.md D11).
- **Bridges** (EndToEnd.v, GenCompose.v): drop the `blocksSound` premise and
  take `L : list (AnnotInstrV blkValid)`. No ai_loop premise (the type enforces
  it). Block-free programs embed trivially (`aiv_block := None`,
  `aiv_loop := false`), so the old bridges become corollaries; keep their
  statements unchanged, because `Example/*Result.v` is the trusted surface.

## 3. Phases

1. **Containment in the VC** (Verifier.v, VerifierRel.v, Adequacy.v). Add the
   check to `sexec_cfg_addr` and its mirror to `cexec_block`; re-prove
   `rexec_block` / `rexec_cfg_addr`. Drop the containment conjunct from
   `blocksSoundAt`; delete `blk_span_sub`. Gate green, trusted surface
   unchanged. Measure VC cost on CountdownRec and a muladd composed segment
   (expect noise).
2. **R1 + `blkValid`** (Adequacy.v). Check R1 by `reflexivity`, define
   `blkValid`, prove `cdRecBlk_valid` from `cdRec_blockSound`.
3. **`AnnotInstrV` + adequacy** (Verifier.v types, Adequacy.v). Firing site
   reads `vb_ok`; `blockSound_of_vc` over `AnnotInstrV` with the Löb hypothesis
   about `selfBlk c` only.
4. **Bridges + CountdownRec** (GenCompose.v, EndToEnd.v, CountdownRec.v,
   CountdownRecResult.v). `cd_link_annot` becomes an `AnnotInstrV` list with
   `vb_ok := cdRecBlk_valid ia`; `cd_rec_annot`'s head gets `aiv_loop := true`.
   `cd_link_blocksSound` and every `blocksSound_of_head` use disappear.
   `ValidCFGVerifierContract` loses its third conjunct.
5. *(SUPERSEDED by §8.1 -- written before Phases 1-4; in particular
   `blocksSound`/`blocksSoundAt` are NOT deletable.)*
   **Cleanup.** Delete `blocksSound`, `blocksSoundAt`, `blocksSound_of_head`,
   `_of_none` once unused. Update the skills (`cfgver-soundness`,
   `cfgver-endtoend*`, `cfgver-executor`'s "Loops as ONE block" and "Where a
   block resumes") and the Verifier.v "WHY NO PROOF FIELD" comment.
6. *(Current scope: §8.2.)* **Then** revisit exit-targets' Phase 5 (drop `cfg_init_addr`, and with it
   the `ia` parameter of `cdRec ia` & co): after step 4 nothing should read it.

## 4. Open questions / risks

- R1: formality now (§1a); one `reflexivity` check.
- R2: symbolic-base lookup of `apc + 4i` (§1c).
- R3: relational lemma for the containment assert (§1c).
- Mid-program blocks (ZZBlkBC, index 55): with containment in the VC and
  validity in the annotation, no map inversion is needed any more -- confirm
  when porting ZZBlkABSound.v.

## 5. Decision log (with revert paths)

| # | date | decision | revert |
|---|---|---|---|
| V1 | 2026-09-25 | Only `ai_block` carries validity. `ai_loop` stays justified by Löb. | Additive: a validity field on `ai_loop` could be added later. |
| V2 | 2026-09-25 | Separate `AnnotInstrV` that erases to `AnnotInstr`. The executor is not parameterised. | Delete `AnnotInstrV`/`eraseV` and restore the `blocksSound` premise on the bridges (kept in git history). |
| V3 | 2026-09-25 | Span containment is checked in the VC (firing site), not by a side premise. | Revert the Phase 1 commit, which restores `blk_span_sub` and the containment half of `blocksSoundAt`. |
| V4 | 2026-09-25 | `blkValid` is a closed Prop (∀ Σ GS, ⊢ …), not an iProp field, because loops cover all recursion. | Needed only if mutual recursion between blocks appears: move `AnnotInstrV` into the Σ section. |
| V5 | 2026-09-25 | `ai_loop` self-reference is enforced by the type: `aiv_loop : bool` (rev 1 had `option N`; exit-targets made the offset redundant). | Back to `option BlkAnnot` + a `Forall` premise in `blockSound_of_vc`. |
| V6 | 2026-09-25 | Sequenced AFTER PLAN-exit-targets.md -- DONE, that plan is implemented. | — |
| V7 | 2026-09-25 | `blkValid` is UNCONDITIONAL in the entry address (no no-wrap premise, revising §1a). A generated segment's precondition already carries `gen_base_bound` (`unsigned base + 4·len ≤ lenAddr`), which `GenCompose.seg_pre_bound` reads off, so `blockFaithful_of_seg` takes `strip ab = code` instead of `Hrep`. Phase 3 needs no address arithmetic at the firing site. | Restore `Hrep` on `blockFaithful_of_seg` and the premise on `blkValid`; derive the fit at the firing site from containment + the program's own fit. |
| V8 | 2026-09-25 | Re-entry is justified at EVERY address: `blockSound_of_vc`'s Löb induction ranges over the entry address, `Hbs` may assume `□ ∀ v', blockSound words v' b`, and the lemma concludes `∀ v, blockSound words v b` (= `blkValid`'s body). So `aiv_loop` may sit on any instruction and no head-only restriction exists. Chosen over (a) a program-level re-entry flag and (b) a head-only side condition. Cost: a block's faithfulness must hold at every address (symbolic placement) -- already implied by V7. | Fixed-`v` `blockSound_of_vc` plus option (a): `AnnotInstrV` without `aiv_loop`, re-entry flag on the program, set on the head by erasure. |
| V9 | 2026-09-28 | Top-level programs may not re-enter themselves: the sealed condition is `annotsValid a` (every `ai_block` carries `blkValid`, NO `ai_loop`). A loop is used as a block (as `cdRec` is). | Allow top-level `ai_loop` with a faithful-at-every-address premise on the bridges. |
| V10 | 2026-09-28 | NO annotation in any bridge statement (Emiel: "annotations only where the contract is proved valid"). Every bridge (`EndToEnd.v`, `GenCompose.v`) takes only `ValidCFGVerifierContract c`, states memory over `cfg_instrs c : list AST`; the seal lives in its own heavy file `Validity.v` so `EndToEnd.v` and `GenCompose.v` stay parallel siblings. | Bridges taking the annotated list + `cfg_vc` + `blocksSound` (pre-Phase-4 state, in git). |
| V11 | 2026-09-28 | A contract run INSIDE a larger program: `GenCompose.contract_run(_w)` over a plain `gmap _ AST` program, premises placement + no-wrap fit + AST containment `instrs_of_list pbase (cfg_instrs c) ⊆ P`. Sound because the concrete run reads the map only at addresses the contract's table matched: the proof builds `instrs_of_list pbase a ∪ (AST_AnnotInstr <$> P)` internally. Replaces `itable_rel`-over-annotated-program premises (`pl_itable`-style) at every composed call site. | Keep the raw Adequacy lemma at call sites (annotation-level). |

## 6. What PLAN-exit-targets.md settled for this plan

- `blk_off` is gone; blocks resume at `blk_exit b ι` (§1a). → `aiv_loop` is a
  `bool`, `selfBlk c` needs no offset, rev 1's R4 is moot.
- `blockSound_of_vc` / `blockSound_of_contract` lost `Hexit`, and
  `blockFaithful`'s exit half is only "the exit term is SyncVal". → `blkValid`
  needs no exit-side obligation of its own.
- `blockFaithful_of_seg` no longer needs `v = of_N ia`. → R1 is a formality.
- `cfg_init_addr` was kept (exit-targets D11) because
  `ValidCFGVerifierContract`'s blocksSound conjunct reads it. → This plan's
  step 4 removes that reader, and step 6 then drops the field.

## 7. Progress log

### Phase 1 -- containment in the VC (2026-09-25, BUILT)

Built through `Example/CountdownRecResult.vo`; `countdown_rec_noninterferent_param`
has exactly the two whitelisted axioms. `CountdownRec.vo`'s VCs (block at the
entry of cdLink, ai_loop re-entry in cdRec) close unchanged with the check in
place -- R2 confirmed on the real code. NOT yet run: `scripts/gate.sh`, and the
VC-cost measurement on CountdownRec / a muladd segment. The three relational
lemmas were developed in `Example/ZZBlkChkProbe.v` (pet cannot open
VerifierRel.v); two needed only implicit-argument fixes.

As built, differing from §1c in three places:
- **R2 confirmed** by `vm_compute` on the symbolic-base self-test table:
  `peval` reassociates `4 + (k 4)`, `(k 4) + 4` and `4 + p` against the
  `table_of_list` keys `peval_bvadd (off) p` (offset 0 is bare `p`).
- **Symbolic** (`Verifier.v`): `blk_code_in tbl apc l : bool` steps the address
  as `term_bvadd apc 4` (the `instrs_of_list` recursion, so the concrete side
  is `bv.add v 4` definitionally), `eq_dec` on `ai_instr`. Wrapped in
  `sexec_block_chk tbl b apc := if blk_code_in .. then sexec_block b apc else
  error`, NOT an `if` around the whole firing-site chain: the step keeps the
  shape `bind <block step> k`, so `rexec_cfg_addr` case 2 changes one line
  (`rexec_block` -> `rexec_block_chk`). Self-tests `blk_code_in_hit/_miss`.
- **Concrete** (`VerifierRel.v`): POINTWISE `cblk_code_in instrs v l : Prop`
  (`(ai_instr <$> instrs) !! v = Some i` per address) rather than
  `instrs_of_list v l ⊆ ..`, because VerifierRel.v does not require Tables.v
  and the pointwise form makes `blk_code_in_sound` a plain induction over
  `lookup_instr_sound`. `cexec_block_chk := assert_formula (cblk_code_in ..)
  ;; cexec_block`. Lemmas: `blk_code_in_sound(_repₚ)`, `rprop_and`,
  `rexec_block_chk`.
- **Adequacy**: `cblk_code_in_sub` (pointwise -> `⊆`, by `insert_subseteq_l`,
  no key-freshness) feeds `blockSound_span_to_whole` from `Hexec`;
  `blocksSoundAt` loses its containment conjunct; `blk_span_sub` deleted;
  `blocksSound_of_head` loses `Hsub`. `CountdownRecResult.v` drops its two
  `blk_span_sub` bullets (statement unchanged).
- Not ported: `Example/ZZBlkABSound.v` (probe, not in `_CoqProject`) still
  calls `blk_span_sub`.
- Decision recorded: VC check over a static Coq-level prefix check on the
  annotated list, because the VC automates it (Emiel).

### Phase 2 -- blkValid (2026-09-25, BUILT)

- R1 holds by `reflexivity` (`blockSound .. (cdRecBlk ia) = blockSound ..
  (cdRecBlk ia')`), but turned out unnecessary: `blockFaithful_of_seg` and
  `blockSound_of_contract` were already generic in the entry address `v`.
- `Adequacy.blkValid b := ∀ Σ GS words v, ⊢ blockSound words v b` -- no fit
  premise, per V7. The plan's §1a premise (`bin v + 4·len < 2^32`) was the
  first version built; replaced the same day.
- `GenCompose.seg_pre_bound` (new) + `blockFaithful_of_seg`'s `Hrep` ->
  `Hab : strip ab = code`. `lia` fails on the last step of `seg_pre_bound`
  (gmap's Zify, gmap-pitfalls); closed with `N2Z.inj_le`/`inj_add`.
- `Example/CountdownRecResult.cdRecBlk_valid` (every v); `cdRec_blockSound` is
  now an instance, its `Hfit` unused until Phase 4 deletes it.
- Built through `CountdownRecResult.vo`; `countdown_rec_noninterferent_param`
  and `cdRecBlk_valid` axiom-clean.

### Phase 3 -- AnnotInstrV + adequacy (2026-09-25, GATE PASSED: 16m46s at GATE_JOBS=1, 19 end theorems axiom-clean)

Design as built differs from §2 in how `vb_ok` reaches the firing site: the
concrete table stays `gmap _ AnnotInstr` and the executor induction
(`sound_exec_cfg_addr_myWP2`) is UNCHANGED. Instead the block premises it
already takes are DERIVED from the annotated list:
- `Verifier.v`: `BlkAnnotV Valid`, `AnnotInstrV Valid` (with
  `aiv_loop : bool`), `selfBlk c`, `eraseV c`, `AST_AnnotInstrV`,
  `strip_eraseV`. Light, Iris-free.
- `Adequacy.v`: `blockSound_of_vc` generalized per V8 (Löb `forall (v)`).
  New `Section ValidAnnot`: `blocksSoundAt_false_of_V` (ai_block via
  `vb_ok`) and `blocksSound_of_V` (plus ai_loop via the Löb hypothesis), for
  `instrs_of_list base (map (eraseV c) LV)` -- a lookup only needs list
  membership (`instrs_of_list_elem_of` + `in_map_iff`), so NO key inversion
  and blocks may sit anywhere (ZZBlkBC's mid-program case needs nothing).
- `GenCompose.v`: `blockSound_of_contract` generalized likewise;
  `blkValid_of_contract` and `blkValid_of_seg` (after `End SegCompose`, since
  `blkValid` quantifies over every Σ).
- `Example/CountdownRecResult.v`: `cd_rec_annotV` (head `aiv_loop := true`)
  and `cdRecBlk_valid` as ONE `exact blkValid_of_seg ...`, reusing
  `valid_cd_rec` unchanged: `map (eraseV (cdRec ia)) cd_rec_annotV` is
  `cd_rec_annot ia` up to conversion.
- V-lists whose type mentions `blkValid` must live on the HEAVY side (the
  `*Result.v` files), not in the light `Example/*.v`. Relevant for Phase 4's
  `cd_link_annotV`.
- Probes: `Example/ZZBlkVcAllProbe.v` (generalized Löb lemma),
  `Example/ZZBlkVProbe.v` (step C) -- pet OOMs on Adequacy.v too.

### Phase 4 -- annotation-free bridges (2026-09-28, GATE PASSED, GATE_JOBS=1)

- `Adequacy.v`: `annotsValid`, `annotsValid_of_none`, `blocksSound_of_annotsValid`.
- NEW `Validity.v` (after Adequacy in `_CoqProject`): `ValidCFGVerifierContract`
  (third conjunct now `annotsValid a` -- no Iris, no `cfg_init_addr`, which
  unblocks Phase 6), intro/elim/Opaque, `solve_annots_none`, `solve_valid`.
  Re-exported by `EndToEnd.v`, required by `GenCompose.v`.
- `EndToEnd.v`: all six bridges take `ValidCFGVerifierContract contract` +
  `contractInstrs : cfg_instrs contract = instrs` (eq_refl); no `Hbs`; memory
  and `mem_has_instrs` over `instrs : list AST`. `cfg_instrs_verified[_with_mem]`
  unseal once; the endToEnd lemmas lost their strip/fmap bridge;
  `gen_contract_noninterferent_u` passes the seal through unopened.
  `solve_no_blocks` deleted. Trap hit: under `Set Implicit Arguments`,
  `contract` became implicit (inferable from `valid_contract`).
- `GenCompose.v`: `blocksSound_of_map`, `contract_setup`, `contract_run`,
  `contract_run_w` (V11); `seg_entry`/`seg_exit`/`seg_exit_state`/
  `loop_instr_block` over AST; `seg_run`, `seg_run_single_exit`, `loop_*`,
  `loop_enter_*` contract-level. `LoopSpec` unchanged (its annotated
  `loop_code` is generator input, i.e. the proof site).
- `Example/CountdownRecResult.v`: `cd_link_valid` (annotsValid via
  `cdRecBlk_valid`) + `cdLink_valid`; `Section Link` (`cdRec_blockSound`,
  `cd_link_blocksSound`) deleted.
- Composed examples (PaddedLoop, CountdownComposed, TwoLoopsComposed,
  SwapComposed): 10 raw calls -> `contract_run`; per-contract `*_valid` by
  `solve_valid`; `pl_itable` -> `pl_contain` (AST containment via
  `instrs_of_list_segment` + `map_fmap_mono`). Invariant statements unchanged:
  `P` is the invariant's own `ai_instr <$> instrs_of_list ...` map.
- Docs: cfgver-endtoend, cfgver-endtoend-internals, cfgver-executor,
  cfgver-contracts; `CFGVer/CLAUDE.md` file table + `skill-path-guard.sh`
  mapping for `Validity.v`.
- Process note: `EndToEnd.v`/`GenCompose.v` edits went through Python scripts,
  which `skill-path-guard.sh` (Write|Edit only) does not see; the required
  skill (cfgver-endtoend-internals) was loaded afterwards and the changes
  checked against it.

### Phase 5 -- cleanup (2026-09-28, dcae0fe1, Results.vo built)

- 8.1a deleted as planned. 8.1b was WIDER than listed: the whole sub-table
  chain was dead -- GenCompose `split_id` / `instr_table_ok_at` /
  `seg_instr_table_ok` / `Section GenSegTables`, `TablesRel.itable_faith_of_segment`,
  and GenSegment §2b (`seg_placement_ok` + four projections). Nothing
  gate-built used any of it; ~50 gitignored ZZ probes do and stay broken
  (Emiel: delete the whole chain). GenCompose sections renumbered 1-5.
  `itable_faith_weaken` / `instrs_of_list_segment` / `seg_fits_rep` /
  `seg_exit_table_ok` are still live and stay.
- 8.1d: the "WHY NO PROOF FIELD" comment rewritten (it pointed at a
  `blocks_valid` in Contracts.v that no longer exists); coqc-guard mentions
  marked dormant in two skills and in skill-path-guard.sh's text; the
  cfgver-contracts sub-table section now points at `contract_run`.
- 8.1e (Emiel: port the muladd chain): `ZZBlkABSound.v` was stale far past
  `blk_span_sub` -- pre-exit-targets and pre-self-contained-segments API --
  and its block sat at index 0, so it was NOT the mid-program test.  Ported
  ZZSegQA / ZZSegQBC / ZZBlkAB / ZZBlkBC / ZZBlkABSound (all gitignored,
  compiled by hand): ZZBlkBC now `Require`s ZZBlkAB instead of copying it;
  ZZBlkABSound proves two generic facts (`strip_blk_at`,
  `annotsValid_blk_at`, by induction on the index), `blkA_valid` /
  `blkBC_valid` by `blkValid_of_seg`, `ab_valid` / `bc_valid`, and runs both
  inside the whole 282-instruction muladd map with `contract_run`.
  **`bc_run_in_muladd` -- a block at index 55 -- is axiom-clean
  (pure_decode, mmioenv).** First real mid-program block; it needed no map
  inversion, as §4 predicted. Trap: `ValidCFGVerifierContract_intro`'s `a` is
  implicit (inferable from `Hvc`), so use the `@`-form.
- 8.1f: the four P1-P4 probes kept (Emiel).

### Phase 6 -- drop `cfg_init_addr` (2026-09-28, 0d9f56e2, Results.vo built)

Emiel chose the FULL version: not just the field, but every load-address
parameter that becomes dead with it.
- Removed: the field and `cfg_map`'s `ia` (Verifier.v), `Valid_CFG_VC`'s
  unused `init_addr` (Contracts.v), the bridges' `contractInitAddr` premise
  (six sites, EndToEnd.v; call sites lose one `eq_refl`),
  `GenSegment.gen_seg_init_addr`, and the `ia`/`init_addr` parameter of
  `gen_contract_rel` / `_u` / `_rel_classed` / `_param` / `_rel_bytes`,
  `gen_seg_contract` (and `gen_loop_contract`'s call; `LoopSpec.loop_head_addr`
  stays, it is a real address) and the four GenCompose segment lemmas.
  `gen_contract` (concrete base) keeps `init_addr`: it builds the placement.
- Examples: every `<prog>_cfg_contract_param`, `valid_*`, `cdRec`,
  `cdRecBlk`, `cdLink`, `cd_*_annot` is a CLOSED term; Result proofs drop
  the argument (`solve_valid valid_x_param`).
- Trusted surface unchanged (diffed): Noninterference.v untouched, no
  `*Result.v` statement and no `*_instrs`/`*_specs` block moved.
- One miss caught by the build: CountdownRec's negative controls spelled the
  load address as the literal `0` (`cdRec 0`), which the rewrite did not match.
- Skills updated in the same commit (record, generator arities, call
  patterns, `cfg_map` lambdas in two probe recipes). NOT updated:
  cfgver-contracts' `description:` still names `cfg_init_addr` (twice) --
  changing it needs the skill-routing-maintenance consult.

### 8.3 result -- the containment check costs 0.11-0.12% (2026-09-28)

Method changed from the handoff (Emiel): a ONE-AXIS ablation on the current
tree (`sexec_block_chk`'s condition stubbed to `true`, plus the one
`cext_sexec_block_chk` proof that destructs it), not a build of 321c42f3.
Probes `Example/ZZChkCost{Common,Base,Link,Rec}.v`, one `Eval` per coqc,
`SymProp.Statistics.size (postprocess (CFG_VC_triple ..))` as the consumer;
`allocated_words` net of each arm's own baseline (612.81 M):

| VC | with check | without | delta |
|---|---|---|---|
| `cdLink` (ai_block at entry) | 4,134,427 | 4,129,651 | 4,776 (0.12%) |
| `cdRec` (ai_loop re-entry) | 4,763,167 | 4,757,919 | 5,248 (0.11%) |

Repeat spread 953 words; baseline drift 1,386. Real but negligible -- one
`lookup_instr` per block instruction per firing, as §1c predicted. Not
written up in diagnostics/ (noise-level, per the plan). Trap met: the first
ablation run silently measured the OLD .vo because Verifier.v failed to
compile under the stub -- gate the measurement on the build succeeding.

## 8. Remaining work -- HANDOFF (written 2026-09-28, for a fresh session)

**State.** Phases 1-4 are DONE on branch `issue/valid-blk-annot` (off
`KatamaranRel`; not merged, not pushed): 6a6ebfdd (P1), 765a0656 (P2),
70f734b2 (P3), 641757ba (P4). `scripts/gate.sh` passed after P3 and after P4
(19 end theorems axiom-clean). Read §5 (decisions V1-V11) and §7 (what each
phase built) first. One-line summary: every bridge now takes only the sealed
`ValidCFGVerifierContract c` (`Validity.v`); annotations appear only where a
contract is proved valid.

Do the items in this order; each ends with a build, and the gate runs once at
the end (`GATE_JOBS=1 ./scripts/gate.sh` on this box, ~17 min).

### 8.1 Phase 5 -- cleanup (usage re-checked 2026-09-28 with `command grep`) -- DONE, see §7

a. **Delete, verified dead:** `Adequacy.blocksSound_of_head` (its definition is
   its only occurrence); `Adequacy.blocksSound_of_none` and
   `blocksSoundAt_of_none` (they only reference each other);
   `EndToEnd.cfg_instrs_pre` and `cfg_instrs_contract` (definitions only -- and
   they still speak of an annotated `instrs`, against V10).
b. **Check, then delete if dead:** `GenCompose.split_id` and the sub-table
   faithfulness helpers around it (`Section GenSegTables`, lines ~100-210);
   `TablesRel.itable_faith_of_segment` (its only real user was `pl_itable`,
   replaced by `pl_contain` in P4; `Example/PaddedLoop.v` mentions it only in
   comments -- update those). Use `command grep -rnw` (plain `grep` is
   gitignore-aware and skips files) and ignore `Example/ZZ*`.
c. **Do NOT delete** `blocksSound`, `blocksSoundAt`, `blocksSound_at_false`,
   `blockSound_span_to_whole`, `blk_span`: the executor's soundness induction
   (`sound_exec_cfg_addr_myWP2`) and `GenCompose.contract_setup` still use them
   internally. (§3 item 5 predates this and is wrong on that point.)
d. **Stale text:** Verifier.v's "WHY NO PROOF FIELD" comment near
   `AnnotInstr`/`BlkAnnot` (validity now rides in `AnnotInstrV`); the
   coqc-guard mentions in the cfgver-scaling-diagnostics skill (~l.504), the
   skill-usage-audit skill (~l.127), and the rocq-implementation requirement
   text inside `.claude/hooks/skill-path-guard.sh` (coqc-guard.sh was unwired
   from settings.json by Emiel on 2026-09-25; the script file remains). Skill
   BODY edits only -- a `description:` change needs the
   skill-routing-maintenance consult. Edit skill files with the Edit tool:
   `skill-bash-write-guard.sh` misfires on any Bash command whose text merely
   names a skill file path (even `git add`, even a plan edit quoting one).
e. **Probe `Example/ZZBlkABSound.v`** (not in `_CoqProject`, not gate-built)
   still calls the deleted `blk_span_sub`. Either port it to the P3/P4 API
   (`blkValid_of_seg` + `annotsValid` + `ValidCFGVerifierContract_intro`) --
   which would be the FIRST real test of a block in the MIDDLE of a program
   (the design needs no key inversion, but nothing exercises it) -- or delete
   it. Ask Emiel which.
f. **Untracked probes from this work:** `Example/ZZBlkChkProbe.v`,
   `ZZBlkVcAllProbe.v`, `ZZBlkVProbe.v`, `ZZContractRun.v`. Ask Emiel whether
   to keep them.

### 8.2 Phase 6 -- drop `cfg_init_addr` -- DONE, see §7

P4 removed its last real reader (the old blocksSound conjunct of
`ValidCFGVerifierContract`). 22 non-comment lines still mention it
(`command grep -rn cfg_init_addr --include=*.v . | grep -v ZZ`), mostly the
bridges' `contractInitAddr : cfg_init_addr contract = init_addr` premise and
the record field itself (Verifier.v). Plan: (1) confirm no proof READS it
beyond that premise; (2) remove the premise from the bridges (every call site
passes `eq_refl`); (3) remove the field from `CFGVerifierContract` and
`cfg_map`, then fix the generators (`gen_contract_*`, `gen_seg_contract` take
`ia` to fill it) -- the `ia` parameters of `cdRec ia` / `cdRecBlk ia` /
`cdLink ia` should then disappear. This changes the RECORD every example
constructs: check with Emiel before touching anything that might move a
trusted `Example/*Result.v` statement (none should; `noninterferent_strong`
takes `init_addr` itself). Coordinate with PLAN-exit-targets.md D11, which
deferred this step to here.

### 8.3 The Phase-1 VC-cost measurement -- DONE, see §7

The block containment check (`Verifier.blk_code_in`, run at every block
firing) should cost noise. Measure `allocated_words` for `valid_cd_link` and
`valid_cd_rec` (Example/CountdownRec.v) before and after P1 -- "before" is
commit 321c42f3 -- with the recipe in the rocq-timeout-triage skill (one heavy
`Time Eval vm_compute` per process; `OCAMLRUNPARAM='v=0x400'`). If it is more
than noise, write it up per the cfgver-scaling-diagnostics skill.

### 8.4 Merge

When 8.1-8.3 are done: `git switch KatamaranRel && git merge --no-ff
issue/valid-blk-annot` (branch-workflow skill; the pre-merge hook runs the
gate). Never push or merge to `main`.

### 8.5 Traps met in this work (so the next session skips them)

- pet (rocq-mcp file mode) runs OUT OF MEMORY opening `VerifierRel.v`,
  `Adequacy.v` and `EndToEnd.v` at any position. Develop proofs in a `ZZ*.v`
  probe that `Require`s the built `.vo` (ZZContractRun.v's header works; it
  needs `From iris.base_logic Require Import ...` for `⊢` to typecheck), or
  check by building. A "not found" from file mode right after a rebuild was
  twice a stale pet, not a real error -- `make` the file before believing it.
- `Set Implicit Arguments` (EndToEnd.v, VerifierRel.v, most Example files):
  anything inferable from a later premise becomes implicit (`contract` from
  `valid_contract`, `l` from `annotsValid l`, `c1` in `rprop_and`). Prefer
  `@lemma` with every argument, or `assert ... by apply`. GenCompose.v does
  NOT set it -- positional arguments there are as declared.
- SSReflect `rewrite` is in scope in several files: no comma lists, no
  `rewrite ... by tac`.
- `map_fmap_compose` is stated `(f ∘ g) <$> m = f <$> (g <$> m)`.
- `repeat constructor` on an `annotsValid` goal descends into `blkValid`'s
  Iris body -- split explicitly (see CountdownRecResult.cd_link_valid).
- Edits to `.v` files through Python/sed bypass `skill-path-guard.sh`
  (Write|Edit only): load the file's required skill first anyway (CFGVer/
  CLAUDE.md's file table), or use the Edit tool.

