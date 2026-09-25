# PLAN: block annotations that carry their own validity (`AnnotInstrV`)

Status: rev 2 (2026-09-25), IN PROGRESS on branch `issue/valid-blk-annot`.
Phases 1-2 DONE, built and axiom-clean; gate deferred until after Phase 3 (Emiel); VC-cost measurement not yet run (§7). Rewritten after PLAN-exit-targets.md
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
5. **Cleanup.** Delete `blocksSound`, `blocksSoundAt`, `blocksSound_of_head`,
   `_of_none` once unused. Update the skills (`cfgver-soundness`,
   `cfgver-endtoend*`, `cfgver-executor`'s "Loops as ONE block" and "Where a
   block resumes") and the Verifier.v "WHY NO PROOF FIELD" comment.
6. **Then** revisit exit-targets' Phase 5 (drop `cfg_init_addr`, and with it
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

