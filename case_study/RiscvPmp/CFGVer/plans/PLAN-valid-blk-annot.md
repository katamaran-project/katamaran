# PLAN: block annotations that carry their own validity (`AnnotInstrV`)

Status: DRAFT 2026-09-25. Nothing implemented.

## 0. Goal

Get rid of `blocksSound` as a post-processing premise. Today every external
bridge (EndToEnd.v ×19, GenCompose.v ×10) takes
`∀ words, ⊢ blocksSound words (instrs_of_list base L)`. That is a `□∀` over the
program map, re-established after the fact per example with
`blocksSound_of_none` / `blocksSound_of_head` / `blk_span_sub`, and a
mid-program block needs a collision inversion that nobody has written yet (ZZBlkBC,
index 55). Instead, an `ai_block` annotation CARRIES a proof that its
block is sound, and the VC checks that the block's code really is in
the program. After that the type system and the VC between them cover
everything `blocksSound` does today.

Decisions already taken (Emiel, 2026-09-25):
- **Only `ai_block` carries validity.** `ai_loop` stays a bare `BlkAnnot`,
  because its block is the enclosing contract and Löb justifies it.
- **A separate type `AnnotInstrV` that erases to `AnnotInstr`.** The executor,
  `cfg_vc` and every existing example stay untouched. We do NOT parameterise the
  executor: the Verifier.v comment above `CFGVerifierContract` measured that at
  ~220 sites, including the trusted surface.
- **Span containment moves into the VC** as a syntactic check at the firing site.
  It is not kept as a side premise.
- **`blkValid` is a closed `Prop`** (∀ Σ GS, ⊢ …), not an iProp field.
  Loops cover all intended recursion, so the annotation never needs to carry a
  validity that holds only under a Löb hypothesis (was Q1).
- **`ai_loop` self-reference is enforced by the TYPE** (was Q2): in
  `AnnotInstrV` the field is `aiv_loop : option N`, meaning "re-enter the
  contract being verified, resuming at this offset". The block is not written
  down, so a wrong one cannot be written, and no `Forall` premise is needed.
  Chosen because most future examples involve loops.

## 1. Design

### 1a. Validity is address-free

`blockSound words v b` (Adequacy.v:1299) reads only `cfg_precondition`,
`cfg_postcondition`, `blk_off` and `blk_span v b` (= `cfg_instrs` at `v`). It
does NOT read `cfg_init_addr` or `cfg_exitCond`, which are the only
`ia`-dependent fields of e.g. `cdRec ia`. So:

```coq
Definition blkValid (b : BlkAnnot) : Prop :=
  ∀ Σ (GS : sailGS2 Σ) words v,
    (bv.bin v + 4 * length (cfg_instrs (blk_contract b)) < bv.exp2 xlenbits)%N ->
    ⊢ blockSound words v b.
```

This lives in Adequacy.v, on the heavy side. For CountdownRec it is proved from
`∀ ia, … blockSound … (cdRecBlk ia)` (today's `cdRec_blockSound`) by
instantiating `ia := bv.bin v`. That step needs a lemma saying `blockSound` is
invariant under changing `cfg_init_addr` / `cfg_exitCond`. The lemma is either
definitional, or holds by `blockSound` depending on `b` only through those four
fields. **Risk R1: check this first**, with a 2 ms `rocq_check` of
`blockSound words v (cdRecBlk ia) = blockSound words v (cdRecBlk ia')` by
`reflexivity`.

The fit condition at a firing site comes from span containment (1c) plus the
enclosing program's own fit (`seg_fits_memory` / `Hrep`), which the bridges
already carry.

### 1b. The type

Light side, new, in Verifier.v next to `AnnotInstr` or in a small new light file:

```coq
Record BlkAnnotV (Valid : BlkAnnot -> Prop) :=
  { vb_blk : BlkAnnot ; vb_ok : Valid vb_blk }.
Record AnnotInstrV (Valid : BlkAnnot -> Prop) :=
  { aiv_ghost_before : list Annot ; aiv_instr : AST ; aiv_ghost_after : list Annot
  ; aiv_block : option (BlkAnnotV Valid)
  ; aiv_loop  : option N }.       (* re-enter the ENCLOSING contract at +off *)
Definition selfBlk {Σ} (c : @CFGVerifierContract Σ) (off : N) : BlkAnnot :=
  {| blk_off := off ; blk_ctx := Σ ; blk_contract := c |}.
Definition eraseV {Valid Σ} (c : @CFGVerifierContract Σ)
    : AnnotInstrV Valid -> AnnotInstr := …
  (* drops vb_ok; ai_loop := option_map (selfBlk c) aiv_loop *)
```

`Valid` is a parameter, so Verifier.v stays Iris-free (layering invariant 1).
The heavy side instantiates it with `blkValid`. The VC is
`cfg_vc c (map (eraseV c) a)`, so the executor and `solve_param_vc` are
unchanged. `c` appears twice, which is fine: it is the same term.

**Why `option N` and not `bool`.** `blk_off` is the resume point, and a
contract with several exits does not determine it (`cdRecBlk` has
`blk_off := 8`, its single exit). Whether `blk_off` should instead be DERIVED
from the contract's exits, and checked in the VC, is left for later.

**R4 (new, from Q2).** `eraseV c` rebuilds `selfBlk c off` inside the VC's own
argument, so the Löb hypothesis in `blockSound_of_vc` must be about
`selfBlk c off` for every `off` used in `a`. If the code has two different
resume offsets, the Löb hypothesis becomes a conjunction over them. That is
harmless, but `blockSound_of_vc`'s statement has to quantify over it.

### 1c. The VC-side containment check

At the firing site (`sexec_cfg_addr`, Verifier.v:1356, `Some b` arm), before
`sexec_block`:

```
for i < length (cfg_instrs (blk_contract b)):
  lookup_instr tbl (apc + 4i) = Some (_, ai_i)  and  ai_instr ai_i = instr_i
  else emsg "block code not in program"
```

- The check is syntactic after `peval`, like `is_exit`. It costs one lookup per
  block instruction per firing and allocates no variables.
- **R2:** `lookup_instr` on `apc + 4i` terms must resolve for a symbolic base.
  It does for the ordinary fetch path (fetch-bound solver rule), but confirm it
  on `cd_link_annot`.

Concrete mirror (`cexec_block`, VerifierRel.v:270): take `instrs` and
`assert ⌜blk_span v b ⊆ ai_instr <$> instrs⌝`, or the pointwise form if that is
easier for `rexec_block`. The refinement goes through `itable_rel`'s lookup
faithfulness. **R3:** `rexec_block` is currently a pure `rsolve` mirror, so a
new pointwise-lookup relational lemma may be needed.

Note that the check is on `AnnotInstr`, so it is also in force for today's
`blocksSound` world. It can land first and on its own (Phase 1), and it deletes
`blk_span_sub` and the containment half of `blocksSoundAt` immediately.

## 2. What changes in the soundness chain

- The firing site in adequacy (Adequacy.v ~1576–1590) currently gets
  containment and `blockSound` from `blocksSoundAt stepped`. After the change:
  containment comes from the concrete assert (Phase 1), and `blockSound` comes
  from `vb_ok` of the looked-up `AnnotInstrV` (Phase 3). That needs the
  concrete table to be `gmap _ (AnnotInstrV blkValid)`, or a side fact
  `instrs = eraseV <$> instrsV`.
- `ai_loop` blocks: after erasure every re-entry block is `selfBlk c off`, by
  construction. So the `▷` half of today's premise is exactly the Löb
  hypothesis of `blockSound_of_vc`, and no `loopsSound` predicate needs to be
  exposed. The `stepped`/`▷` split survives only inside `blockSound_of_vc`.
- Bridges (EndToEnd.v, GenCompose.v): drop the `blocksSound` premise and take
  `L : list (AnnotInstrV blkValid)`. There is no ai_loop premise, because the
  type enforces it. Old `list AnnotInstr` programs with no blocks embed
  trivially (`aiv_block := None`), so the old bridges become corollaries. Keep
  their statements unchanged, because `Example/*Result.v` is the trusted
  surface.

## 3. Phases

1. **Containment in the VC** (Verifier.v, VerifierRel.v, Adequacy.v). Add the
   check to `sexec_cfg_addr` and its mirror to `cexec_block`, then re-prove
   `rexec_block` / `rexec_cfg_addr`. Drop the containment conjunct from
   `blocksSoundAt` and delete `blk_span_sub`. Gate green, and the trusted
   surface is unchanged. Measure VC cost on muladd composed and CountdownRec
   (expect noise).
2. **R1 + `blkValid`** (Adequacy.v). Prove the `ia`-invariance lemma, define
   `blkValid`, and prove `cdRecBlk_valid : blkValid (cdRecBlk ia)` from
   `cdRec_blockSound`.
3. **`AnnotInstrV` + adequacy** (Verifier.v types, Adequacy.v). Add the firing
   site reading `vb_ok`, `loopsSound`, and `blockSound_of_vc` over
   `AnnotInstrV`.
4. **Bridges + CountdownRec** (GenCompose.v, EndToEnd.v,
   CountdownRecResult.v). Port `cd_link_annot` to `AnnotInstrV` with
   `vb_ok := cdRecBlk_valid ia`. `blocksSound_of_head` usage disappears.
   Then ZZBlkABSound.v.
5. **Cleanup.** Delete `blocksSound`, `blocksSound_of_head`, `_of_none` and
   `blocksSoundAt` once nothing uses them. Grep the skills (`cfgver-soundness`,
   `cfgver-endtoend*`, `cfgver-executor`) and the Verifier.v "WHY NO PROOF
   FIELD" comment for stale references.

## 4. Open questions

None blocking. Q1 and Q2 were decided 2026-09-25 (see §0). Deferred: deriving
`blk_off` from the contract's exits (§1b).

**UPDATE 2026-09-25: PLAN-exit-targets.md is IMPLEMENTED** (branch
issue/exit-targets).  Consequences for this plan, now facts rather than
predictions: `BlkAnnot` is `(blk_ctx, blk_contract)` (no blk_off); a block
resumes at `blk_exit b ι = inst (cfg_exit c) ι`; `blockSound_of_vc` has no
Hexit; `blockFaithful`'s exit half is only "the exit term is SyncVal"; and
`blockFaithful_of_seg` no longer needs `v = of_N ia`, so R1 (blockSound
independent of the load address) is essentially answered -- only
cfg_init_addr remains, and blockSound never reads it.  `aiv_loop` can be a
`bool`, and R4 is moot.  Re-draft §1a/§1b against this before Phase 2.

**Sequencing (decided 2026-09-25): PLAN-exit-targets.md goes FIRST.** It
removes `cfg_exitCond` and `blk_off` (one target, and a block resumes at it), so
after it: `BlkAnnot` = (ctx, contract), R1/R4 are moot, `aiv_loop : bool`, and
`blkValid` needs no exit side. Re-draft §1a/§1b against that before starting
Phase 2. Phase 1 (containment in the VC) is independent and may land earlier.

## 5. Decision log (with revert paths)

| # | date | decision | revert |
|---|---|---|---|
| V1 | 2026-09-25 | Only `ai_block` carries validity. `ai_loop` stays justified by Löb. | Additive: a validity field on `ai_loop` could be added later. |
| V2 | 2026-09-25 | Separate `AnnotInstrV` that erases to `AnnotInstr`. The executor is not parameterised. | Delete `AnnotInstrV`/`eraseV` and restore the `blocksSound` premise on the bridges (kept in git history). |
| V3 | 2026-09-25 | Span containment is checked in the VC (firing site), not by a side premise. | Revert the Phase 1 commit, which restores `blk_span_sub` and the containment half of `blocksSoundAt`. |
| V4 | 2026-09-25 | `blkValid` is a closed Prop (∀ Σ GS, ⊢ …), not an iProp field, because loops cover all recursion. | Needed only if mutual recursion between blocks appears: move `AnnotInstrV` into the Σ section. |
| V5 | 2026-09-25 | `ai_loop` self-reference is enforced by the type (`aiv_loop`). After PLAN-exit-targets it becomes a `bool`; before it, `option N`. | Back to `option BlkAnnot` + a `Forall` premise in `blockSound_of_vc`. |
| V6 | 2026-09-25 | Sequenced AFTER PLAN-exit-targets.md. | Reorder. Only §1a/§1b depend on it. |
