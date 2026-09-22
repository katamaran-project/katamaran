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
VERIFICATION, and all four go away at once. **One qualification, established in
§2.4:** this breaks the circularity for the RECORD, so a block annotation can
carry a real contract — it does NOT break it for VALIDITY, which is defined by
running the executor that reads the annotation. Validity therefore stays a side
premise (`blocksSound`), and `SBlk`'s existence was never a pure dodge.

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
exists to dodge this: it is `CFGVerifierContract`'s data minus `cfg_instrs` and
`cfg_init_addr`, plus `sblk_off`. **But only the DATA half of the dodge is
removable — see §2.4.**

## §2. The design

**`cfg_instrs : list AST` alone does not work** and the plan must not pretend
otherwise: a program that USES a block has to carry that block somewhere, and
with an AST-only field there is no such place. The annotated list has to enter
the verification. It enters as an ARGUMENT, not a field.

### §2.1 Three definitions, settled 2026-09-22

| | mentions `a` | kind | layer | who states it |
|---|---|---|---|---|
| `CFGVerifierContract` — the record, `cfg_instrs : list AST` | — | `Type` | light, `Contracts.v:148` | authors |
| `cfg_vc c a` — the VERIFICATION CONDITION | **yes** | `Prop` | light, `Contracts.v` | `Example/*.v`, via `vm_compute; solve_vc` |
| `ValidCFGVerifierContract c words base` — VALIDITY | **no** | `iProp` | Iris, with `blockSound` | `Example/*Result.v`; what a block premise quotes, what nests |

```coq
Record CFGVerifierContract {Σ} := { …; cfg_instrs : list AST; … }

(* light: today's ValidCFGVerifierContract, renamed, + the annotated list *)
Definition cfg_vc {Σ} (c : @CFGVerifierContract Σ) (a : list AnnotInstr) : Prop := …

(* Iris: blockSound re-indexed off SBlk and onto a contract *)
Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ)
    (words : bv xlenbits -> bv word) (base : bv xlenbits) : iProp Σ := …
```

`cfg_vc` is deliberately named as PLUMBING, next to `cfg_map`, not as another
`Valid…` variant: it is the helper you discharge, and `Valid…` now means valid.

**Retracted on the way here (all 2026-09-22, none ever in a `.v`):**
`ValidCFGVerifierContractA` (78fe8548), `ValidCFGVerifierContractVC`
(549d83e1), `CFGVerifierContractVC` (b6b09ee6), and the revision at 68a101fe
that put `ValidCFGVerifierContract` back on the VC. That last one was wrong for
the reason §2.4 gives: `ai_block`'s premise has to quote an annotation-free
proposition, and `cfg_instrs_contract` cannot be it.

### §2.2 THE DERIVATION MUST NOT REDO THE WORK — and it does not

Emiel's acceptance criterion, 2026-09-22: `ValidCFGVerifierContract c` must be
derivable from the annotated proof **without redoing the work**.

```coq
Lemma valid_mv : ⊢ ValidCFGVerifierContract mv_ex words base.
Proof. eapply blockSound_of_contract; [reflexivity | exact vc_mv | solve_no_blocks]. Qed.
```

The executor is not re-run, the VC is not re-proved, nothing is re-`vm_compute`d.

```coq
Lemma blockSound_of_contract {Σ} (c : @CFGVerifierContract Σ)
    (a : list AnnotInstr) (words : bv xlenbits -> bv word) (base : bv xlenbits) :
  strip a = cfg_instrs c ->
  cfg_vc c a ->
  (⊢ blocksSound words (instrs_of_list base a)) ->
  ⊢ ValidCFGVerifierContract c words base.
```

proved ONCE, generically in `c` and `a` — it is today's `blockSound_of_vc` with
its `SBlk` swapped for a contract. Per contract the derivation is an `eapply`, a
`reflexivity` and the block premise. That premise is `solve_no_blocks` (one
line) for a program without blocks; for one WITH blocks it is the block's own
validity, which is work you cannot avoid, because it is exactly what the block's
assumption stood in for.

**This criterion is what rules out the obvious alternative.** Defining
`ValidCFGVerifierContract c` as the UN-ANNOTATED VC, `cfg_vc c (cfg_instrs c)`,
would make the derivation re-execute all 33 of muladd's instructions instead of
the 4 the annotated run touched — and it may simply fail, on fuel alone. An
annotation only ever makes the VC EASIER, so `cfg_vc c a → cfg_vc c (cfg_instrs c)`
is false for every hint that does any work.

### §2.3 Why validity is Iris-level: the trilemma

Three properties, at most two at once:

1. **annotation-free** — the statement does not mention `a`;
2. **light syntactic `Prop`** — `Example/*.v` can state it and `solve_vc`
   proves it directly;
3. **no `∃` over the annotation**.

- Drop **1** → today's definition (`Contracts.v:172`, a `Prop` — and it DOES
  mention annotations today, because `cfg_instrs : list AnnotInstr`). Rejected:
  it is the whole point of the plan.
- Drop **3** → `∃ a, strip a = cfg_instrs c ∧ cfg_vc c a`. Rejected, see below.
- Drop **2** → the semantic form. **CHOSEN.** Note it is still a `Prop` where it
  is used (an Iris entailment `⊢ …` is a `Prop`); it is the BODY that is an
  `iProp`, so only the heavy branch can state it.

The forcing step: no purely syntactic annotation-free statement is implied by
the annotated VC (previous section), and there is nothing else syntactic to aim
at.

**Why the `∃` loses, and it is NOT on the work criterion.** Deriving it is
trivially cheap — `exists a; split; [reflexivity | exact H]` — so it passes
§2.2. It fails on a hole with no patch at the light layer:

- `blocksSound` must be demanded for the SAME `a` the `∃` hid, so the Iris side
  has to destruct the existential and ask for that `a` — putting the annotation
  back inside the Iris statement, which is what the `∃` was for avoiding;
- the escape would be to quantify the premise:
  `∀ a, strip a = cfg_instrs c → ⊢ blocksSound …`;
- **that is not dischargeable, even for an annotation-free program.**
  `blocksSound_of_none` needs `ai_block ai = None` everywhere, which
  `ai_block_none_of_AST` (`Verifier.v:244`) gives for the COERCED list and not
  for an arbitrary `a` that merely strips correctly. A lying block strips
  correctly — which is the same false-block attack, now unpatchable rather than
  merely awkward.

### §2.4 `ai_block` CANNOT CARRY VALIDITY — it carries the contract as data

The constraint that decides §2.1, and it is structural rather than a matter of
taste. Validity is DEFINED BY RUNNING THE EXECUTOR, and the executor READS
`ai_block`:

```
Verifier.v:186    ai_block : option SBlk
Verifier.v:1233   match ai_block ai with            <- sexec_cfg_addr reads it
Verifier.v:1678   scfg_verification_condition       <- built from sexec_cfg_addr
Contracts.v:172   ValidCFGVerifierContract := … scfg_verification_condition …
```

so `ai_block → validity → scfg_verification_condition → sexec_cfg_addr →
ai_block` is a circular DEFINITION, not a file-ordering nuisance. Flipping
`cfg_instrs` to `list AST` breaks the cycle for the **record** — the data no
longer mentions `AnnotInstr`, which is what lets a block annotation carry a real
`CFGVerifierContract` instead of a cloned `SBlk` — and does **not** break it for
**validity**. (The semantic form cannot be a field either, for the independent
reason that `AnnotInstr` is a light record with no Iris in scope.)

**So `ai_block` holds the contract as DATA and validity stays a side premise —
which is what `blocksSound` already is, and why it cannot be deleted.** "The
valid contract can be used as an `ai_block`" holds in the form that matters: the
annotation carries the contract, and the premise you discharge is stated as
`ValidCFGVerifierContract` — annotation-free — instead of in terms of annotated
internals. That is also what makes NESTING work: the premise quotes a
proposition that says nothing about hints, so the next level up neither sees nor
cares about them.

**And it is why `cfg_instrs_contract` is not the answer**, despite already
existing and already being annotation-free:

```coq
EndToEnd.v:112   Definition cfg_instrs_contract `{sailGS2 Σ} exitCond instrs γ1 γ2 :=
                   (cfg_instrs_pre instrs γ1 γ2 -∗ exitCond_WP2_loop exitCond)%I.
```

It is ENTRY-POINT shaped — whole program, fixed start, no resumption — so it
cannot describe a block, which needs pre/post plus "resume at `pc + off`". It is
the right shape for the top-level theorem and the wrong shape for composition.
Two notes while in the area: it is DEAD (`git grep` finds only the definition;
`cfg_instrs_verified` spells the same statement inline), and its instruction
frame is already `ai_instr <$> …` — annotation-freeness at the Iris layer was
never in doubt, because MEMORY HOLDS INSTRUCTIONS, NOT ANNOTATIONS. Flipping the
field makes the statement layer agree with what the Iris layer always said.

### §2.5 No `Ha` argument: `cfg_vc` does not read `cfg_instrs c`

An earlier revision gave the VC a dependent third argument
`(Ha : strip a = cfg_instrs c)`. Unnecessary. What `Valid_CFG_VC` uses today
(`Contracts.v:137`):

```coq
Valid_CFG_VC ia p exits P i ec fl Q := safeE (postprocess (CFG_VC_triple p exits P i fl Q))
```

`i` is the only instruction-ish input and the list the table is built from —
**`Valid_CFG_VC` has always been parameterised by the instruction list.** With
the field flipped to `list AST`, `cfg_vc`'s instruction input is `a` and
`cfg_instrs c` plays no role in it. So `strip a = cfg_instrs c` is not needed to
STATE the VC; it is needed by the bridge, and that is where §2.2 puts it.

Consequences: an un-annotated example states `cfg_vc mv_ex mv_instrs`, its own
`list AST` riding the existing coercion; an annotated one states
`cfg_vc mv_ex mv_annot`; no `strip_of_AST _` at any statement site (the lemma is
still needed — `strip (list_AST_AnnotInstr l) = l`, `map_map` + `map_id`, so it
holds for a symbolic `l` — but is discharged once, inside the bridge); and
`cfg_map` keeps its arity, with Phase 1 deciding whether `Valid_CFG_VC` keeps an
unused `cfg_instrs` parameter or drops it (`init_addr` and `ec` are already kept
unused there, `Contracts.v:135-147`).

**What this gives up, plainly:** `cfg_vc c a` no longer forces `a` to be a
version of `c`'s program, so a VC can be discharged for an unrelated `a`.
Harmless — it proves nothing, because the bridge will not accept it — and it is
the same freedom `Valid_CFG_VC` already has with `init_addr`.

### §2.6 Blast radius

Counted 2026-09-22: 64 occurrences of `ValidCFGVerifierContract` in 26 tracked
files. Position decides what each becomes.

| site | count | position | becomes |
|---|---|---|---|
| `Contracts.v` (the definition) | 1 | — | `cfg_vc c a` |
| `Verifier.v:270` (a comment) | 1 | — | reword |
| light `Example/*.v` (18 files) | 30 | **statement** | `cfg_vc c <its own _instrs>`, Phase 2 |
| `EndToEnd.v` | 13 | **premise** | `∀ a, strip a = … → cfg_vc c a → …`, Phase 3 |
| `GenCompose.v` | 10 | **premise** | same, Phase 2 |
| `Example/*Result.v` (4 files) | 9 | **application** | pass what was proved — but see §2.8, three of them also carry a faithfulness hypothesis that names `cfg_instrs c` |

**A PREMISE MUST QUANTIFY `a`, NOT PIN IT TO THE UN-ANNOTATED PROGRAM.**
Checked 2026-09-22: every `EndToEnd.v`/`GenCompose.v` occurrence is a hypothesis
(`(Hv : ValidCFGVerifierContract c)`, `(valid_contract : … contract)`,
`ValidCFGVerifierContract c ->`), and every light `Example/*.v` occurrence is
the goal of a `vm_compute; solve_vc` lemma. A premise pinned to the un-annotated
program says *"the contract you hand me must have been proved with NO hints"* —
so a generated loop segment could never be discharged with a block annotation
inside it, which is precisely the composition PLAN-muladd-composed needs.

Do each substitution in the phase that already edits that file — NOT as one
tree-wide sed up front, or Phase 2's gate loses its meaning.

**This rename is the real cost of the design and should not be buried.** It is
30 example statements plus 23 premises. It is unavoidable once
`ValidCFGVerifierContract` is annotation-free, because the light files cannot
state an annotation-free form (§2.3) and therefore cannot keep the name.

### §2.8 THE SECOND RENAME, AND IT IS THE BIGGER ONE: classifying every `cfg_instrs c`

`ValidCFGVerifierContract`'s 64 sites are the *visible* half. The real work is
the **61 occurrences of `cfg_instrs` in 9 tracked files** — `EndToEnd.v` 33,
`GenCompose.v` 11, `Example/*Result.v` 14, `GenSegment.v` 3, `Contracts.v` 2,
`Verifier.v` 1, `Example/PaddedLoop.v` 1 — because after the flip **each one
means one of two different things** and only a human reading can tell which:

| the use means | becomes | why |
|---|---|---|
| "the program that sits in MEMORY" | stays `cfg_instrs c`, now `list AST` | memory holds instructions; this is the trusted side |
| "the list the SYMBOLIC TABLE is built from" | becomes `a` | the executor needs the annotations |

Getting one wrong in the second direction is a type error and the build catches
it. **Getting one wrong in the first direction is not**, because
`list_AST_AnnotInstr` will coerce — the file compiles and the contract silently
becomes a claim about the un-annotated program.

**The seven sites that are certainly the TABLE side** (`table_of_list … 0
(cfg_instrs c)`), found 2026-09-22:

```
GenCompose.v                      4   (seg_run's Hif, and three siblings)
Example/CountdownComposedResult.v 2
Example/SwapComposedResult.v      1
```

These are `itable_rel` faithfulness hypotheses, so three of them sit in
`*Result.v` files that §2.6 classifies as pure "application" sites. **They are
not.** `seg_run`'s shape shows why the confusion is easy:

```coq
Lemma seg_run {R} (c : @CFGVerifierContract R) … (L : list AnnotInstr) …
  (Hv  : ValidCFGVerifierContract c)
  (Hif : itable_rel (instrs_of_list cbase L)
                    (table_of_list (cfg_placement c) 0 (cfg_instrs c)) iota)
  (Hbs : ∀ wds, ⊢ blocksSound wds (instrs_of_list cbase L))
  … : Pre -∗ myWP2_loop Post.
```

`GenCompose` **already** carries two instruction lists — `L`, the enclosing
program, and `cfg_instrs c`, the segment's slice — tied by `Hif`. After the flip
there are THREE: `L` (annotated, enclosing), `a` (annotated, this segment's
table) and `cfg_instrs c` (AST, the statement). `Hif` takes `a`; the new
`strip a = cfg_instrs c` connects `a` back to the statement.

**Two things this reveals about the plan's other claims, both corrections:**

- §3's "`itable_rel` and `table_of_list` are untouched" is true of their
  DEFINITIONS and misleading about their USE SITES, which is where the work is.
- `seg_run`'s conclusion is `Pre -∗ myWP2_loop Post` — **already the semantic
  shape §2.1 wants**, with `seg_entry`/`seg_exit` already packaging the pre/post.
  So `ValidCFGVerifierContract` has TWO existing models to be derived from, not
  one: `blockSound` (§2.4) and `seg_run`'s conclusion. Check whether they can be
  the same definition before writing a third; if they can, Phase 4 shrinks and
  `seg_run` becomes an instance rather than a parallel path.

**Method note for whoever executes this:** do the classification as an explicit
pass with the list above in hand, file by file, and write the verdict next to
each site in the commit message. Do NOT let the coercion decide it for you.

### §2.7 The block annotation then IS a contract

```coq
Record BlkAnnot := MkBlkAnnot
  { blk_off      : N                                  (* resume at pc + off *)
  ; blk_ctx      : LCtx
  ; blk_contract : @CFGVerifierContract blk_ctx }.

… ai_block : option BlkAnnot
```

Data only, per §2.4. Well-founded, because `CFGVerifierContract` no longer
mentions `AnnotInstr`.

**Bonus the current design cannot express.** A block's `cfg_instrs` is then a
`list AST` naming the code the block stands for. Blocks are verified against the
ENCLOSING program, so it is not needed for soundness — but it makes "does this
block actually sit over that code?" a checkable proposition instead of an
unstated convention. `SBlk` has no field that can say this.

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
## §2c. FAITHFULNESS IS AST-LEVEL; REFINEMENT KEEPS ANNOTATIONS (Emiel, 2026-09-22 — DECIDED)

`itable_rel` (`VerifierRel.v:474`) is payload-EXACT today:

```coq
exists v, inst (fst p) ι = ty.SyncVal v /\ instrs !! v = Some (snd p)
```

It is doing two different jobs at once, and they should be separated:

| job | between | annotations? |
|---|---|---|
| **REFINEMENT** — `sexec` and `cexec` take the same branch | the symbolic table and the concrete gmap OF THE SAME VERIFICATION | **YES, exact.** `cexec_cfg_addr` dispatches on `ai_block` from the gmap and `sexec_cfg_addr` on the table payload; if they disagree `rexec_cfg_addr` is false |
| **FAITHFULNESS** — "this code really is there" | a block's span and the ENCLOSING program | **NO — project to `ai_instr`** |

**Consequence: a block's VC is a SELF-CONTAINED verification.** It runs against
its own annotated list `a_b`: table `table_of_list place 0 a_b`, gmap
`instrs_of_list base a_b`. Their payload-exact agreement is then internal and
provable by the existing whole-list faith lemma — no enclosing program appears,
so the refinement obligation is discharged where it belongs.

The bridge to the enclosing program is AST-level containment plus a
SEPARATION-LOGIC SPLIT of the instruction memory: the block owns
`ptsto_instrs` for its own span, the rest is framed across the block step and
reassembled after. That is the "only reason about what is visible in the block"
philosophy, and it is the point of the design rather than a cost to be
minimised.

**What this kills, all of it good:**

- **`clear_blk` is not needed at all.** It existed because the enclosing gmap
  carries the block's own annotation at `v` while the block's table does not —
  a disagreement that only arises because the two came from different artifacts.
  Under §2c they never do. (Keep `clear_blk` itself if something else wants it;
  the `clear_blk <$> instrs` in `blockSound_of_vc` goes.)
- **The stratified `blocksSound` goes.** An earlier revision of this plan
  proposed a global annotated program with per-entry clearing and an induction
  over a set `S` of already-proven blocks. Not needed: block F's proof never
  mentions the enclosing program, so F-needs-L is an ordinary premise, not a
  fixpoint over one shared artifact.
- **NESTING IS FREE, and it is the whole point.** `a_F` may annotate the loop
  head L, so a function-level block's VC skips the loop instead of unrolling it.
  Without this, blocks compose only over straight-line code and the layer above
  loops is unreachable — i.e. PLAN-muladd-composed cannot be finished.

**THE NARROW FIX DOES NOT WORK — CHECKED 2026-09-22, AND THIS IS WHY §2c IS
LOAD-BEARING RATHER THAN A NICETY.**

An earlier round of this discussion concluded that the defect in
`clear_blk <$> instrs` was *narrow*: it clears EVERY address when only the
block's own entry, `<[v := clear_blk ai]> instrs`, needed clearing — so
single-entry clearing would hide a block from itself while leaving nested
annotations intact, and nesting would work. The supporting lemma is true and was
proved in 1.2 s:

```coq
Lemma blocksSound_insert_clear words instrs v ai :
  instrs !! v = Some ai ->
  blocksSound words instrs ⊢ blocksSound words (<[v := clear_blk ai]> instrs).
```

**But it does not buy nesting, because it RELOCATES the circularity instead of
removing it.** `blockSound_of_vc` currently discharges its block premise
VACUOUSLY (`blocksSound_clear_blk`, every `ai_block` is `None` after a
whole-map clear). With single-entry clearing that premise is no longer vacuous:
the cleared program still carries every OTHER block, so `blockSound_of_vc` would
have to take the enclosing `blocksSound words instrs` as a HYPOTHESIS. And
`blocksSound` is *defined* as a `□ ∀` over `blockSound` — so at the use site you
need `blocksSound` in order to prove `blockSound`, i.e. in order to prove
`blocksSound`. Circular.

§2c is what breaks it, and the mechanism is the SELF-CONTAINMENT, not the
clearing: a block's VC runs against its OWN annotated list `a_b`, so its block
premise is `blocksSound words (instrs_of_list base a_b)` over a STRICTLY SMALLER
artifact, and the recursion is well-founded on nesting depth. The enclosing
program never appears, so there is nothing to clear and no fixpoint to stratify.

**Consequence for whoever executes Phase 4: you cannot get nesting cheaply.**
The span split is the feature, not an optimisation of it. Keep
`blocksSound_insert_clear` out of the tree unless something else wants it —
it is a true lemma with no user.

**THE LOAD-BEARING QUESTION — ANSWERED 2026-09-22, THE ANSWER IS YES.**
`blockSound` currently holds `ptsto_instrs_w words (ai_instr <$> instrs)` for
the WHOLE program, unchanged, across the block step. Under §2c it holds only
the block's span and the remainder must be framed through a `myWP2_loop`. That
frame rule does not exist but is DERIVABLE IN FOUR LINES from the two lemmas
already in `Adequacy.v` -- `exitCondImpliesMyWP2_loop` (:149, the UNIT,
`ExitCond ⊢ myWP2_loop ExitCond`) and `myWP2_loop_bind` (:183, the BIND):

```coq
Lemma myWP2_loop_frame (Fr E : iProp Σ) : Fr ∗ myWP2_loop E ⊢ myWP2_loop (Fr ∗ E).
Proof.
  iIntros "[HFr H]".
  iApply (myWP2_loop_bind E (Fr ∗ E) with "[HFr] H").
  iIntros "HE". iApply exitCondImpliesMyWP2_loop. iFrame.
Qed.
```

Verified in preamble mode over an abstract `bi` with `loop`/`unit`/`bind` as
parameters (pet OOMs opening `Adequacy.v` at any position, so the real file
cannot be spiked in place -- restate the SHAPE, per the rocq-implementation
skill). The derivation uses NOTHING but unit and bind, and the real statements
match the abstract ones on the nose, so it transfers. `Fr` sits in the linear
wand handed to `bind`, which is legitimate: `myWP2_loop_bind`'s own Löb proof
either uses that wand or passes it on, never both.

So §2c is not gated on new Iris machinery. Proceed.

### §2c-STATUS (2026-09-23): BOTH IRIS RISKS SETTLED, AND THE SHAPE IS VERIFIED

Phase 4a landed the record swap (`fab97c31`). For 4b, the three things §2c left
open have now been checked interactively against the real `Adequacy.v`
environment rather than argued:

| §2c open item | status |
|---|---|
| `myWP2_loop_frame` | derivable in 4 lines from `myWP2_loop_bind` + `exitCondImpliesMyWP2_loop` (verified over an abstract `bi`, 2026-09-22) |
| `ptsto_instrs` split/reassembly | **DONE** — `ptsto_instrs_w_split` (`VerifierRel.v`), three tactics, a BI-ENTAILMENT so one lemma does split and rejoin |
| the block's span is expressible | **YES, with no new machinery** — `instrs_of_list` is polymorphic (`∀ A, bv xlenbits → list A → gmap _ A`), so `instrs_of_list v (cfg_instrs (blk_contract b))` is a `gmap _ AST` directly, exactly `ptsto_instrs_w`'s argument type. No coercion, no fmap |

**And the self-contained `blockSound` TYPECHECKS** (45 ms). The shape, with the
one property that matters — it does NOT mention the enclosing `instrs`:

```coq
Definition blockSound (words : bv xlenbits -> bv word)
    (v : bv xlenbits) (b : BlkAnnot) : iProp Σ :=
  (∀ ι ExitCond,
     interp (cfg_precondition (blk_contract b)) (ι.["a" ↦ SyncVal v]) ∗
     pc ↦ᵣ SyncVal v ∗ (∃ x, nextpc ↦ᵣ x) ∗
     ptsto_instrs_w words (instrs_of_list v (cfg_instrs (blk_contract b))) -∗
     (interp (cfg_postcondition (blk_contract b)) … ∗ pc ↦ᵣ … ∗ (∃ x, nextpc ↦ᵣ x) ∗
      ptsto_instrs_w words (instrs_of_list v (cfg_instrs (blk_contract b))) -∗ ExitCond) -∗
     myWP2_loop ExitCond)%I.
```

**Dropping the `instrs` parameter is the whole point**, and it is what §2.7's
"bonus the current design cannot express" buys: `cfg_instrs (blk_contract b)`
names the block's own code, so the span is derivable from the annotation alone.
`SBlk` had no field that could say this, which is why the old `blockSound` had
to take the enclosing program and hence why it needed `clear_blk`.

**THE ADAPTER IS PROVED, AND IT RETIRES §2c's "LOAD-BEARING QUESTION"
(2026-09-23).** The step everything else rests on — recover the OLD
whole-program interface from the NEW span-only one, given AST-level containment
— is six tactics:

```coq
Lemma blockSound_span_to_whole words instrs v b ι ExitCond :
  instrs_of_list v (cfg_instrs (blk_contract b)) ⊆ ai_instr <$> instrs ->
  blockSound words v b -∗
  (pre … ∗ pc ↦ᵣ … ∗ (∃ x, nextpc ↦ᵣ x) ∗ ptsto_instrs_w words (ai_instr <$> instrs)) -∗
  (post … ∗ pc ↦ᵣ … ∗ (∃ x, nextpc ↦ᵣ x) ∗ ptsto_instrs_w words (ai_instr <$> instrs) -∗ ExitCond) -∗
  myWP2_loop ExitCond.
Proof.
  intros Hsub. iIntros "Hb (Hpre & Hpc & Hnpc & Hinstrs) Hk".
  rewrite (ptsto_instrs_w_split words Hsub).
  iDestruct "Hinstrs" as "[Hspan Hrest]".
  iApply ("Hb" $! ι ExitCond with "[$Hpre $Hpc $Hnpc $Hspan]").
  iIntros "(Hpost & Hpc' & Hnpc' & Hspan')". iApply "Hk". iFrame.
Qed.
```

**`myWP2_loop_frame` IS NOT NEEDED, and §2c's claim that it was the load-bearing
question is RETRACTED.** Look at the last line: `Hrest` is discharged by a plain
`iFrame`. The caller's continuation is an ordinary wand, so it CLOSES OVER the
remainder from the caller's own spatial context — the remainder never has to
travel through `myWP2_loop` at all, and there is nothing to frame across it.
The frame rule is still derivable in four lines and may be wanted elsewhere; it
is simply not what this design needs. §2c spent its risk budget on the wrong
question.

**WHAT REMAINS IN 4b, in order, with no unknown risks left:**

1. swap `blockSound` to the shape above and re-shape `blocksSound` (its body
   stops mentioning `instrs`; the map survives only in the lookup premise);
2. `blockFaithful` becomes AST-level CONTAINMENT — the span is a submap of
   `ai_instr <$> instrs` — replacing the `itable_rel` over `clear_blk <$> instrs`;
3. the block branch of `sound_exec_cfg_addr_myWP2`: split with
   `ptsto_instrs_w_split`, hand the span over, rejoin from the block's post.
   **This is the only real proof work left**;
4. `blockSound_of_vc` → `blockSound_of_contract`: the block's VC runs against
   its OWN table and its OWN gmap, so its block premise is
   `blocksSound words (instrs_of_list v a_b)` — a strictly smaller artifact,
   which is what makes nesting well-founded (see the retraction above);
5. re-do `ZZBlkAB` on the new shape; GATE 4.

Secondary, expected to be easy but unverified:
- `ptsto_instrs` splitting/reassembly — it is a `big_sepM`, so
  `big_sepM_union`/`_subseteq` should do it, given the span is a submap.
- the block's execution never fetches outside its span: true by construction,
  since a lookup outside its own table is an `error`, but say so explicitly.


## §3. What collapses

| goes away | why |
|---|---|
| `SBlk` (8 fields) | becomes `BlkAnnot` (3), of which 2 are the contract |
| `sblk_place` | **already dead** — occurs only in its own declaration and in three comment lines in `Adequacy.v` |
| `sblk_exits` / `sblk_exitCond` / `sblk_fuel` | read off `blk_contract` instead of being copied into a second record |
| `sblk_of_contract` (probe) | nothing to convert |
| ten `strip` sites in `EndToEnd.v` | the two lists are now NAMED (`cfg_instrs c` for memory, `a` for the table) instead of one being derived from the other. **One `strip` survives**, as a hypothesis of the bridge (§2.2) — that is the point, not a leftover |
| `strip_length` | no longer needed at a boundary |
| `AST_AnnotInstr`, `list_AST_AnnotInstr`, `Local Arguments List.cons {_} & _ _.` | exist ONLY so `[MV X3 X2; …]` typechecks as `list AnnotInstr`. With an AST field, examples need no coercion. **Check before deleting** — the coercion is still wanted: §2.5 has an un-annotated example write `cfg_vc c c_instrs` with `c_instrs : list AST` riding it |

**What does NOT change:** `AnnotInstr` stays the executor's payload,
`instrs_of_list` stays `AnnotInstr`-valued, and `itable_rel`/`table_of_list`
keep their DEFINITIONS — but seven of their USE SITES change which list they are
fed (§2.8), which is the bulk of the refactor. This removes annotations from the STATEMENT, not from the tool.

## §4. Phases

### Phase 1 — the record, and the VC renamed to `cfg_vc`
`Contracts.v` only: flip the field to `list AST`, rename
`ValidCFGVerifierContract` to `cfg_vc` and give it the annotated list `a` as a
second argument, and add `strip_of_AST`. **No `Ha` argument** (§2.5). Decide
here whether `Valid_CFG_VC` keeps an unused `cfg_instrs` parameter or drops it.
**The Iris-level `ValidCFGVerifierContract` is NOT part of this phase** — it
lands with Phase 4; Phase 1 must not put an Iris require into a light file (root
CLAUDE.md, ~1.2 GB across seven examples). Until Phase 4 the name
`ValidCFGVerifierContract` is simply unused, which is the cleanest way to be
sure nothing still reads it as the VC.

GATE 1: `Contracts.vo` compiles, and `cfg_vc c (cfg_instrs c)` is definitionally
the proposition `ValidCFGVerifierContract c` denotes today — check by
`reflexivity` against an inlined copy of the old body, not by eye.

### Phase 2 — the generators
`GenContract.v`, `GenSegment.v` (3 `cfg_instrs` refs), `GenCompose.v` (11).
**`gen_seg_contract`'s `prog` argument is the landmine — see §5.**
`GenCompose.v`'s 10 validity hypotheses quantify `a` — see §2.4 — and its four
`table_of_list … (cfg_instrs c)` sites take `a` instead (§2.8). Pinning them
to the un-annotated program is what would stop a generated segment being
discharged with a block annotation inside it.

GATE 2: every light `Example/*.v` compiles after rewriting its statement to
`cfg_vc c <its own _instrs>` and NO other edit — no changed `_instrs` block, no
changed tactic. If an example needs more than that, something upstream is
wrong; fix that, not the example.

**ONE EXEMPTION, found by the gate itself on 2026-09-22 — a hand-written
contract LITERAL whose `cfg_instrs` is deliberately a `list AnnotInstr`.**
`Example/PaddedLoop.v` is the tree's only one (it is also the only example with
a sub-table contract): `plBody`/`plFinal` set `cfg_instrs := pl_seg` with
`pl_seg : list AnnotInstr := cd_instrs`, and no upstream default can fix that —
the field's type genuinely changed, and this example was exercising exactly the
distinction the plan introduces. The fix is the §2.8 classification applied by
hand: the FIELD takes the AST list `cd_instrs`, and `cfg_vc` is applied to
`pl_seg` — which is already the list `PaddedLoopResult.v:91` builds the table
from, so the example gets MORE coherent, not less. Do not read this exemption
more widely: a GENERATED contract needing an edit still means the generator is
wrong.

### Phase 3 — EndToEnd
`EndToEnd.v` (33 `cfg_instrs` refs, 10 `strip` sites) **plus the three
`table_of_list … (cfg_instrs c)` sites in `Example/*Result.v`** (§2.8). The
memory side takes `cfg_instrs c`; the table side takes `a`; classify every one
explicitly — the coercion will hide a mistake in the memory direction.

**GOOD NEWS, surveyed 2026-09-22: this is SIX hypotheses, not 33 sites.**
`EndToEnd.v` already routes the whole question through one named equation,
repeated once per top-level lemma (`:119`, `:193`, `:233`, `:312`, `:1481`,
`:1580`):

```coq
(contractInstrs : cfg_instrs contract = instrs')
```

`instrs'` is THE program: everything else in those lemmas — `instrs_of_list`,
`ptsto_instrs`, `blocksSound`, `mem_has_instrs` — is stated over it, not over
`cfg_instrs contract`. So the flip is

```coq
(contractInstrs : strip instrs' = cfg_instrs contract)
```

with `instrs' : list AnnotInstr` unchanged everywhere else, and the ten `strip`
sites in the bodies collapse because `strip instrs'` now HAS a name. Phase 3
should start by making exactly that change to the six and reading the errors,
not by walking the 33 occurrences. Expect this file to get shorter and
the `strip`-vs-no-`strip` comment at :1514 to be deleted.

GATE 3: `make Results.vo` green; `./scripts/gate.sh` at `GATE_JOBS=1` green.

**STATUS 2026-09-22 — Phase 3 landed at `f95f32c0`, GATE 3 is 2 OF 3.**

| step | result |
|---|---|
| 1. build target closure | **pass** (`Results.vo`, `GenCompose.vo`) |
| 2. proof-hole scan | **pass** — the only `Admitted`/`admit`/`Axiom` hits are two COMMENTS, `Verifier.v:500` and `VerifierRel.v:2602` |
| 3. axiom hygiene, 18 theorems | **BLOCKED, NOT FAILED** — killed twice for memory |

Step 3 needs ~7 GB in ONE process; with ~5 GB held by the desktop on this 14 GB
box it trips the low-memory monitor. **`GATE_PROBE_BATCH` does not help in
either direction** — the ~7 GB is per-process (see `project-compile-cost`), so a
smaller batch multiplies the count instead of shrinking the peak. Re-run it when
the box is quiet; nothing in Phase 4 depends on it.

**So this is the one thing Phase 3 has NOT established:** whether the 18 end
theorems are still axiom-clean (expected: only `Machine.pure_decode` and
`Base.mmioenv`). Everything structural IS established — the whole tree builds,
and the trusted statements are unchanged, because the bridges' conclusions lost
only the `strip` that each `Result` file was immediately undoing with
`rewrite <- Hstrip` / `rewrite <- strip_id_X`.
**Plus: read through the `blocksSound` premises** — with the parameterised
form, each entry point's VC premise and its `blocksSound` premise must name the
SAME `a`. That is what closes the §2 false-block hole, and under this design it
holds by construction, so this is a read-through and not a proof obligation.

### Phase 4 — blocks on the new shape, and the contract-indexed semantic form
Delete `SBlk`, introduce `BlkAnnot` (`off` + the packed contract, §2), have
`blk_at` instantiate the contract at the attachment address so the author never
writes an offset, and re-point `sexec_block`/`cexec_block`/`rexec_block`/
`blockSound`/`blockSound_of_vc`/`blockFaithful`.

**This is where `ValidCFGVerifierContract` itself lands** (§2.1) — `blockSound`
re-indexed off `SBlk` and onto a `CFGVerifierContract`, so that a block's
premise quotes an annotation-free proposition and the next level up neither sees
nor cares about hints. The ENTRY-POINT form needs nothing new:
`cfg_instrs_contract` (`EndToEnd.v:112`) already exists and is already
annotation-free — it is simply the wrong SHAPE for a block, per §2.4.

The bridge is `blockSound_of_contract` — today's `blockSound_of_vc` with the VC
premise now `cfg_vc c a`, the `strip` equation as an ordinary hypothesis, and
the `blocksSound` premise naming that same `a`. Once it exists,
a verified contract plugs into an `ai_block` with no annotation in sight, and
nesting is just iterating it — which is what Emiel asked for and what loops
need.

**Restructure per §2c while doing it, not afterwards:** faithfulness projects
to `ai_instr`, each block's VC runs against its own annotated program, and
`blockSound` owns only its span with the rest framed. The `myWP2_loop` frame
rule §2c needs is already shown derivable, so this phase is not gated on new
Iris machinery. Do NOT fall back to `clear_blk <$> instrs`: it forecloses
nesting and therefore PLAN-muladd-composed. Re-do the
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
2. **`Set Implicit Arguments` + the new `a` argument.** Coq's `(name := v)`
   syntax accepts implicit names only, and several call sites already use
   positional/numeric selectors (`4: exact …` in `JumpsResult.v`). Adding an
   argument reorders goals. There is no `Ha` (§2.5 retracted it), but `cfg_vc`
   gains `a` and the Phase 3 premises gain a quantifier — check those selectors.
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
- **Do not edit an example BEYOND its statement line in Phase 2.** Examples do
  change — the statement becomes `cfg_vc c <its own _instrs>` (§2.6) — but that
  is the whole edit. A changed `_instrs` block, a changed tactic, or an added
  hypothesis means something upstream is wrong; fix that, not the example.
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
