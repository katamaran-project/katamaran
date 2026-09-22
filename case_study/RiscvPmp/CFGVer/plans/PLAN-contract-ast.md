# PLAN-contract-ast — `cfg_instrs : list AST`, and the annotation as tool input

Status: **NOT STARTED, and no longer blocked.** Written 2026-09-22, at Emiel's
diagnosis. The solver work it was waiting on landed the same day and is
gate-green: `bc4adb1d` (try_bvadd_cancel_val_propeq) and `3223f7a5` (peval in
simplify_formula's propeq/secLeak arms).

Audience: a later session executing one phase at a time. Each phase ends in an
explicit GATE — reach it, report, commit, stop.

---

## §0. The bet, in five lines

`CFGVerifierContract` carries `cfg_instrs : list AnnotInstr`. Annotations are
TOOL INPUT — ghost hints and block contracts — not part of what a contract
asserts. Carrying them in the specification record forces `strip` at every
trusted boundary, makes `AnnotInstr` and `CFGVerifierContract` mutually
recursive (so a block contract cannot BE a contract), and requires a coercion
plus an elaboration hack so that ordinary programs still typecheck. Change the
field to `list AST` and pass the annotated list as an argument to the
VERIFICATION, and all four go away at once.

## §1. The diagnosis, with the evidence already in the tree

`EndToEnd.v` applies `strip` at **ten** sites, and the comment at
`EndToEnd.v:1514` says outright that some premises are over `strip instrs'`
("the trusted ones") and others over `instrs'`. That is the smell: **the
contract you read is not the program you trust.** `strip` exists to undo, at
every boundary, a decision made in the record.

The circularity is the same fact wearing a different hat:

```
AnnotInstr  --ai_block-->  <a contract>  --cfg_instrs-->  list AnnotInstr
```

and it is not merely a type-theory nuisance — `Contracts.v` REQUIRES
`Verifier.v` (line 54), so the dependency already runs contract -> annotation.
Reusing `CFGVerifierContract` inside `ai_block` would mean inverting that, i.e.
merging the trusted `Contracts.v` into `Verifier.v`. `SBlk` (`Verifier.v:126`)
exists ONLY to dodge this: it is `CFGVerifierContract`'s data minus
`cfg_instrs` and `cfg_init_addr`, plus `sblk_off`.

## §2. The design

**`cfg_instrs : list AST` alone does not work** and the plan must not pretend
otherwise: a program that USES a block has to carry that block somewhere, and
with an AST-only field there is no such place. The annotated list has to enter
the verification. It enters as an ARGUMENT, not a field:

```coq
Record CFGVerifierContract {Σ} := { …; cfg_instrs : list AST; … }   (* spec only *)

Definition ValidCFGVerifierContractA {Σ} (c : @CFGVerifierContract Σ)
    (a : list AnnotInstr) (Ha : strip a = cfg_instrs c) : Prop := …
```

The contract says what program and what it promises; `a` is the proof hint;
`Ha` says the hints do not change the program. That is exactly the discipline
`strip` already enforces — moved from ten boundary sites to one entry point,
checked once.

**THE RESULTING PROPOSITION MUST NOT MENTION THE ANNOTATIONS EITHER (Emiel,
2026-09-22).** The form above is the PROVING form. Validity is a property of
the CONTRACT, not of the hints used to establish it: with `a` in the statement,
two proofs using different hints are different propositions, and everything
downstream that quotes validity drags hints along — which is precisely what
stops a verified contract from being dropped into an `ai_block`. So the hints
are EXISTENTIALLY QUANTIFIED in the stating form, and that is the only one
anything downstream sees:

```coq
Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
  exists a (Ha : strip a = cfg_instrs c), ValidCFGVerifierContractA c a Ha.
```

Annotations are then what they should be: needed to PROVE a contract, invisible
in STATING it.

**THE HOLE THIS OPENS, AND IT IS A REAL ONE.** `blocksSound` is indexed by the
ANNOTATED program (`blocksSound words (instrs_of_list base a)`). If the
statement hides `a` behind the `∃` while the block premise is discharged for a
DIFFERENT `a'`, the two can disagree: pick an `a` carrying a block annotation
with a FALSE contract (`strip a = cfg_instrs c` still holds — only ghosts and
blocks are free), let the block assume anything so `VC(a)` is trivial, then
discharge `blocksSound` for an annotation-free `a'` via `blocksSound_of_none`.
Two different programs, one theorem. Close it one of two ways, and say which:

1. **Universally quantify the premise** —
   `∀ a, strip a = cfg_instrs c → ∀ words, ⊢ blocksSound words (instrs_of_list base a)`.
   Strictly stronger than picking one `a`, so it cannot be dodged. Simplest.
2. **Bundle** — have the Iris bridge destruct the `∃` and demand `blocksSound`
   for THAT `a`. More faithful, but carries an existential across the
   Prop/iProp boundary.

**For a BLOCK this is a non-issue, which is a good consistency check on the
design.** A block's own VC runs against the CLEARED program
(`clear_blk <$> instrs`), so its `blocksSound` premise is discharged internally
by `blocksSound_clear_blk` and never reaches a caller — the `∃`-form is
unconditionally safe there. Only the top-level entry points
(`cfg_instrs_endToEnd`, `gen_contract_noninterferent*`) need the care above.

**The unary form is KEPT, and this is what bounds the blast radius.** Measured
2026-09-22: **no tracked example carries any annotation** — every `_instrs`
block is a plain `list AST` riding the coercion. So

```coq
Lemma strip_of_AST (l : list AST) : strip (list_AST_AnnotInstr l) = l.
Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
  ValidCFGVerifierContractA c (list_AST_AnnotInstr (cfg_instrs c)) (strip_of_AST _).
```

keeps `Lemma valid_X : ValidCFGVerifierContract X_contract` spelled exactly as
it is today in all ~16 examples. `strip_of_AST` is `map_map` + `map_id`, a real
lemma rather than `reflexivity`, so it also holds for a symbolic `l`.

**The block annotation then IS a contract:**

```coq
Record BlkAnnot := MkBlkAnnot
  { blk_off      : N                                  (* resume at pc + off *)
  ; blk_ctx      : LCtx
  ; blk_contract : @CFGVerifierContract blk_ctx }.

… ai_block : option BlkAnnot
```

Well-founded, because `CFGVerifierContract` no longer mentions `AnnotInstr`.

**Bonus the current design cannot express.** A block's `cfg_instrs` is then a
`list AST` naming the code the block stands for. Blocks are verified against
the ENCLOSING program, so it is not needed for soundness — but it makes
"does this block actually sit over that code?" a checkable proposition instead
of an unstated convention. `SBlk` has no field that can say this.

## §2b. POSITION-INDEPENDENCE — the SPLIT IS RETRACTED (2026-09-22)

An earlier revision of this section proposed splitting `CFGVerifierContract`
into a position-independent "core" and a top-level "wrapper" holding
`cfg_init_addr`/`cfg_exitCond`, so that a block could hold only the core.
**Emiel rejected that and was right. Do not reintroduce it.** Those two fields
are already PARAMETERIZED: a segment contract is written as a FUNCTION of its
address (`sgA_q_contract (iq : N)`), and `valid_sgA_q : forall iq, …` is ONE
`Qed` applied at each call site. Instantiating a contract at `ia + 220` is
application, not duplication, and a second record would be pure duplication.

Two specific claims made in support of the split are WRONG and are retracted:

- *"`seg_exitCond` forces a copy of the contract per address."* False. See
  above: one universally-quantified lemma, applied.
- *"`gen_seg_contract`'s `base + of_N 0` placement breaks the evar."* False.
  `peval` folds `t + 0` to `t` (verified: `peval (a + 0) = term_var "a"`). The
  real cause was that `simplify_formula`'s `propeq` arm fell through to
  `simplify_propeq` on UN-peval'd terms; fixed in `3223f7a5`. There is
  therefore NO reason to add a block builder that places at the bare base.

**What survives, and it is the useful half.** The VC is ALREADY
position-independent: `Valid_CFG_VC` takes eight arguments and passes SIX to
`CFG_VC_triple` — `init_addr` and `ec` are dropped on the floor
(`Contracts.v:135-147`, "unused by the symbolic VC … kept in the signature so
Valid_CFG_VC remains a direct cfg_map target"). Every assertion is written
against `term_var "q"`, which `sexec_block` instantiates angelically to
whatever pc it stands at. So a block's contract needs instantiating at the
address the block sits at, and nothing more — and `blk_at` can do that AT
ATTACHMENT TIME (it already knows the base and the index), so the author never
writes an offset by hand.

**The one thing genuinely not recoverable from the record: the resume point.**
`cfg_exits` holds it inside a term and `cfg_exitCond` inside a function;
extracting an `N` from either means pattern-matching a term, which is fragile.
Hence `blk_off` in §2's `BlkAnnot`.

*Optional, second-order, do NOT bundle it with the main refactor:* have
`sexec_block` resume at the block's sole EXIT TERM, substituted by the angelic
evars it already holds, instead of computing `apc + of_N off`. That removes
`blk_off` entirely (so `ai_block : option (sigT CFGVerifierContract)`, zero
added fields) and generalises to an exit that is not a constant offset. It
needs a singleton `cfg_exits`, or a demonic choice over the list — which is the
honest shape for a block with two successors, and is how segments H and L would
eventually want it.

**`gen_base_bound` is NO LONGER an open question.** This section previously
recorded a per-call-site tax: a block asserting its own extent
(`unsigned q + 16 <= lenAddr`) inside a program bounded at 336. As of
`3223f7a5` both block probes close with plain `solve_param_vc` and no
arithmetic step, so it does not surface. The likely closer is `try_fetch_bound`
discharging the narrower bound against the enclosing one in `wco` once the
angelic is substituted — MECHANISM INFERRED, NOT VERIFIED; if it reappears,
check there first.

## §3. What collapses

| goes away | why |
|---|---|
| `SBlk` (8 fields) | becomes `BlkAnnot` (3), of which 2 are the contract |
| `sblk_place` | **already dead** — occurs only in its own declaration and in three comment lines in `Adequacy.v` |
| `sblk_exits` / `sblk_exitCond` / `sblk_fuel` | read off `blk_contract` instead of being copied into a second record |
| `sblk_of_contract` (probe) | nothing to convert |
| ten `strip` sites in `EndToEnd.v` | the two lists are now NAMED (`cfg_instrs c` for memory, `a` for the table) instead of one being derived from the other |
| `strip_length` | no longer needed at a boundary |
| `AST_AnnotInstr`, `list_AST_AnnotInstr`, `Local Arguments List.cons {_} & _ _.` | exist ONLY so `[MV X3 X2; …]` typechecks as `list AnnotInstr`. With an AST field, examples need no coercion. **Check before deleting** — the coercion may still be wanted for the `ValidCFGVerifierContract` default above |

**What does NOT change:** `AnnotInstr` stays the executor's payload,
`instrs_of_list` stays `AnnotInstr`-valued, `itable_rel` and `table_of_list`
are untouched. This removes annotations from the STATEMENT, not from the tool.

## §4. Phases

### Phase 1 — the record and the two Valid forms
`Contracts.v` only: flip the field, add `ValidCFGVerifierContractA` (proving
form), the `∃`-quantified `ValidCFGVerifierContract` (stating form, §2), plus
`strip_of_AST` and the unary default. `cfg_map`/`Valid_CFG_VC` gain the
annotated list. Nothing else edited yet.

GATE 1: `Contracts.vo` compiles; `ValidCFGVerifierContract c` still has its
current type from an example's point of view.

### Phase 2 — the generators
`GenContract.v`, `GenSegment.v` (3 `cfg_instrs` refs), `GenCompose.v` (11).
**`gen_seg_contract`'s `prog` argument is the landmine — see §5.**

GATE 2: every `Example/*.v` compiles UNCHANGED. If any example needs editing,
the unary default is wrong; fix the default, not the example.

### Phase 3 — EndToEnd
`EndToEnd.v` (33 `cfg_instrs` refs, 10 `strip` sites). The memory side takes
`cfg_instrs c`; the table side takes `a`. Expect this file to get shorter and
the `strip`-vs-no-`strip` comment at :1514 to be deleted.

GATE 3: `make Results.vo` green; `./scripts/gate.sh` at `GATE_JOBS=1` green.
**Plus: check the `∃`/`blocksSound` hole of §2 is actually closed** — every
top-level entry point must quantify its block premise over all `a` consistent
with `c` (option 1), or destruct the existential itself (option 2). A gate pass
does NOT catch this: the cheat compiles.
**Diff `Noninterference.v` + the `*_instrs`/`*_specs` blocks and every
`Example/*Result.v` statement — this phase touches the trusted surface and the
whole point is that those statements should now be SIMPLER, never different.**

### Phase 4 — blocks on the new shape
Delete `SBlk`, introduce `BlkAnnot` (`off` + the packed contract, §2), have
`blk_at` instantiate the contract at the attachment address so the author never
writes an offset, and re-point `sexec_block`/`cexec_block`/`rexec_block`/
`blockSound`/`blockSound_of_vc`/`blockFaithful`. Re-do the
`ZZBlkAB` probe on the new shape rather than porting it.

GATE 4: `ZZBlkAB` green again, `make Results.vo` green.

### Phase 5 — the cleanup this unblocks
- delete the dead `sexec_blocks` / `sexec_triple_addr_blk` / `_blks` /
  `scfg_verification_condition_blk` / `_blks` cluster (`Verifier.v`), referenced
  only by the untracked `ZZBlkSpike`/`ZZBlkChain` probes;
- `blockSound_of_loop` (PLAN: blocks over loops without unrolling) — cheaper to
  write once on the final shape.

## §5. Landmines

1. **`gen_seg_contract`'s `prog : list AnnotInstr` is deliberate and documented
   (`GenSegment.v:409-415`).** With `list AST` there, the coercion lands OUTSIDE
   the slicing — `list_AST_AnnotInstr (firstn take (skipn skip prog))` — and can
   never unify with `GenCompose.instr_table_ok_at`'s
   `firstn take (skipn skip L)` for `L : list AnnotInstr`. After this refactor
   there are genuinely TWO lists (AST for the statement, AnnotInstr for the
   table) and the segment machinery must slice BOTH consistently. Decide this
   explicitly in Phase 2; do not let the coercion float.
2. **`Set Implicit Arguments` + the new `Ha` argument.** Coq's `(name := v)`
   syntax accepts implicit names only, and several call sites already use
   positional/numeric selectors (`4: exact …` in `JumpsResult.v`). Adding an
   argument reorders goals. Put `Ha` LAST, as `HBS` was.
3. **`strip a = cfg_instrs c` must be `reflexivity`-cheap.** For a concrete
   literal it computes; for a `firstn/skipn` slice of a named program it may
   not. If it does not, the side condition becomes real work at every segment.
4. **The gate is the only check that matters here.** A wrong `strip` bridge
   would let a contract be proved about one program and applied to another —
   and it would still compile.

## §6. Do NOT

- **Do not change `cfg_instrs` to `list AST` without adding the annotated
  argument.** It looks like it works until the first program that carries a
  block, and then there is nowhere to put it.
- **Do not edit an example to make Phase 2 pass.** The unary default exists so
  that examples are untouched; an example needing a change means the default is
  wrong.
- **Do not remove `AnnotInstr` from `instrs_of_list` / `table_of_list`.** The
  executor reads `ai_ghost_*` and `ai_block` off the table payload. This plan
  removes annotations from the statement only.
- **Do not fold this together with the solver change.** Land that first.

## §7. Related

- `plans/PLAN-annotinstr.md` — the migration that introduced `AnnotInstr`, and
  the PRODUCT-vs-SUM history. Read before touching the record.
- `plans/PLAN-executor-composition.md` — the block hook this unblocks.
- `.claude/skills/cfgver-executor` — "Ghost annotations (AnnotInstr)", including
  why the coercions are not `Local` and why the payload is not split.
- `.claude/skills/cfgver-contracts`, `cfgver-endtoend-internals` — the two
  skills whose documented shapes this plan changes; update them IN THE SAME
  COMMIT as the code (CLAUDE.md hygiene rule).
