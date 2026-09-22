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
the verification. It enters as an ARGUMENT, not a field.

### §2.1 Two names, and only two

| name | layer | reads | says |
|---|---|---|---|
| `CFGVerifierContractVC c a` | light, `Contracts.v`, `Prop` | `c`'s pre/post/exits/fuel/placement **and `a`** | "the symbolic VC of `c`'s spec against the annotated program `a`" — what `vm_compute; solve_vc` discharges |
| `ValidCFGVerifierContract c` | Iris, `iProp` | `c`, **`cfg_instrs c : list AST` included** | "`c` holds" — the conclusion, annotation-free, what composes |

```coq
Record CFGVerifierContract {Σ} := { …; cfg_instrs : list AST; … }   (* spec only *)

Definition CFGVerifierContractVC {Σ} (c : @CFGVerifierContract Σ)
    (a : list AnnotInstr) : Prop := …
```

**`Valid` now means VALID, and a verification condition is not valid — it is
DISCHARGED.** So the syntactic form drops the word. (An earlier revision of
this section, 78fe8548–5c636a66, called the two forms
`ValidCFGVerifierContractA` and `ValidCFGVerifierContractVC`. Both names were
invented in this plan on 2026-09-22 and have never appeared in a `.v` file —
`git log -S` over all of history confirms it — so nothing is owed to them.
`ValidCFGVerifierContractVC` in particular read "valid verification condition",
a category error, and Emiel rejected it on sight.)

### §2.2 `CFGVerifierContractVC` does NOT read `cfg_instrs c`, and that is what removes the third name

The earlier revision gave the VC a third, DEPENDENT argument
`(Ha : strip a = cfg_instrs c)`, and then needed a named abbreviation for the
no-hints case just to hide `(strip_of_AST _)` at ~30 example statement sites.
All of that is unnecessary. Check what `Valid_CFG_VC` actually uses today
(`Contracts.v:137`):

```coq
Valid_CFG_VC ia p exits P i ec fl Q := safeE (postprocess (CFG_VC_triple p exits P i fl Q))
```

`i` is the ONLY instruction-ish input, and it is the list the table is built
from. With the field flipped to `list AST`, the VC's instruction input is `a`
and **`cfg_instrs c` plays no role in it whatsoever**. So `strip a =
cfg_instrs c` is not needed to STATE the VC — it is a well-formed proposition
without it. It is needed by the BRIDGE, and that is exactly where it should
sit: an ordinary hypothesis of the lemma that uses it, not a dependent argument
of the thing that does not.

Consequences, all of them simplifications:

- **No third name.** An un-annotated example states
  `CFGVerifierContractVC mv_ex mv_instrs` — the `list AST` rides the existing
  coercion, and the line reads "verified with the program itself as the
  annotated list", i.e. no hints. An annotated one states
  `CFGVerifierContractVC mv_ex mv_annot`. Same shape, one argument.
- **No `strip_of_AST _` noise** at any statement site. The lemma stays
  `Lemma strip_of_AST (l : list AST) : strip (list_AST_AnnotInstr l) = l`
  (`map_map` + `map_id`, so it holds for a symbolic `l` too), but it is now
  discharged once inside the bridge instead of written out thirty times.
- **`cfg_map` keeps its arity.** It still projects all eight fields; the VC
  simply ignores the instruction one. Decide at Phase 1 whether to drop
  `cfg_instrs` from `Valid_CFG_VC`'s signature or keep it unused, the way
  `init_addr` and `ec` are already kept unused there (`Contracts.v:135-147`).

**The one thing this gives up, stated plainly:** `CFGVerifierContractVC c a` no
longer forces `a` to be a version of `c`'s program, so it is possible to
discharge a VC for an unrelated `a`. That is harmless — it just proves nothing
useful, because the bridge below will not accept it — and it is the same
freedom `Valid_CFG_VC` already has with `init_addr`.

### §2.3 The stating form, and why it is semantic

```
  CFGVerifierContractVC c a       PROVING form — hints visible, solve_vc's job
        |
        |   + strip a = cfg_instrs c
        |   + the block premises for THAT SAME a
        v
  ValidCFGVerifierContract c      STATING form — mentions only cfg_instrs c : list AST
```

**THE ∃-QUANTIFIED STATING FORM IS RETRACTED (Emiel, 2026-09-22).** An earlier
revision defined the stating form as `∃ a Ha, <the VC>`. Two things are wrong
with it. (i) It is still *definitionally about hints* — the `∃` quantifies them
rather than removing them, so every consumer has to destruct it, and a block
consumer would carry an existential across the Prop/iProp boundary. (ii) It
opened the false-block hole that this section used to spend twenty lines
patching. A parameterised form plus an implication gives the "hints invisible
downstream" property with neither cost.

**WHAT THE STATING FORM CANNOT BE — and this decides where it lives.** It
cannot be the VC at the trivial annotation, `CFGVerifierContractVC c
(cfg_instrs c)`. The implication would run the WRONG WAY: an annotation only
ever makes the VC *easier*. Measured this session — a block annotation replaced
29 of muladd's 33 executed instructions with one consume/produce, and the
un-annotated VC has to execute all 33 and can fail on fuel alone. So
`VC(c,a) → VC(c, cfg_instrs c)` is false for every hint that does any work, and
the stating form is **not a syntactic VC at all**. It therefore cannot live in
the light layer (`Contracts.v` is Iris-free by the layering invariant in the
root CLAUDE.md).

**IT IS THE SEMANTIC STATEMENT — AND THE TREE ALREADY CONTAINS IT UNDER ANOTHER
NAME.** `blockSound` (`Adequacy.v:1283`) is exactly "this code, entered at this
address satisfying pre, reaches `pc + off` satisfying post, inside
`myWP2_loop`", and its instruction frame is
`ptsto_instrs_w words (ai_instr <$> instrs)` — **already annotation-free**.
Under §2c a block's obligation is a self-contained verification over its own
span. Put those two together:

> **the annotation-free stating form and `blockSound` are the same
> proposition**, one indexed by an `SBlk` and the other by a
> `CFGVerifierContract`.

That is the answer to "I would expect `blocksSound` not to be needed any more
if we can supply a valid contract instead": it is not removed, it is
**re-indexed** — off `SBlk` and onto `CFGVerifierContract` — and promoted from
an internal Iris premise to the thing a user proves and hands around. Shape,
not final text:

```coq
Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ)
    (words : bv xlenbits -> bv word) (base : bv xlenbits) : iProp Σ :=
  (∀ ι ExitCond,
     interp (cfg_precondition c) … ∗ pc ↦ᵣ … ∗ <span of cfg_instrs c at base> -∗
     (interp (cfg_postcondition c) … ∗ … -∗ ExitCond) -∗
     myWP2_loop ExitCond)%I.
```

and the bridge is `blockSound_of_vc` with its `SBlk` swapped for a contract —
note `strip` appears here, once, and nowhere else:

```coq
Lemma ValidCFGVerifierContract_of_VC {Σ} (c : @CFGVerifierContract Σ)
    (a : list AnnotInstr) (words : bv xlenbits -> bv word) (base : bv xlenbits) :
  strip a = cfg_instrs c ->
  CFGVerifierContractVC c a ->
  (⊢ blocksSound words (instrs_of_list base a)) ->
  ⊢ ValidCFGVerifierContract c words base.
```

**THE FALSE-BLOCK HOLE IS CLOSED BY CONSTRUCTION, not patched.** The `∃`-form
admitted this attack: prove the VC with a block annotation carrying a FALSE
contract (`strip a = cfg_instrs c` still holds — only ghosts and blocks are
free), then discharge `blocksSound` for a DIFFERENT, annotation-free `a'` via
`blocksSound_of_none`; two different programs, one theorem. In the bridge above
**all three premises name the same `a`**, so the attack is not expressible.
Neither of the two fixes the `∃`-form needed — universally quantifying the
premise over all `a`, or bundling the `∃` into the Iris statement — is
required. This is the main reason the parameterised form is better and not
merely tidier.

### §2.4 Rename blast radius

Counted 2026-09-22: **64 occurrences of `ValidCFGVerifierContract` in 26
tracked files**, and the POSITION of each decides what it becomes.

| site | count | position | becomes |
|---|---|---|---|
| `Contracts.v` (the definition) | 1 | — | `CFGVerifierContractVC c a` |
| `Verifier.v:270` (a comment) | 1 | — | reword |
| light `Example/*.v` (18 files) | 30 | **statement** | `CFGVerifierContractVC c <its own instrs>`, Phase 2 |
| `EndToEnd.v` | 13 | **premise** | `∀ a, strip a = … → CFGVerifierContractVC c a → …`, Phase 3 |
| `GenCompose.v` | 10 | **premise** | same, Phase 2 |
| `Example/*Result.v` (4 files) | 9 | **application** | pass what was proved |

**A PREMISE MUST NOT BE FIXED AT THE NO-HINTS CASE — an earlier revision of
this table did exactly that and it was WRONG.** Checked 2026-09-22: every
`EndToEnd.v`/`GenCompose.v` occurrence is a hypothesis
(`(Hv : ValidCFGVerifierContract c)`, `(valid_contract : … contract)`,
`ValidCFGVerifierContract c ->`), and every light `Example/*.v` occurrence is
the goal of a `vm_compute; solve_vc` lemma. A premise pinned to the
un-annotated program says *"the contract you hand me must have been proved with
NO hints"* — so a generated loop segment could never be discharged with a block
annotation inside it, which is precisely the composition PLAN-muladd-composed
needs. Premises quantify `a`.

Do each substitution in the phase that already edits that file — NOT as one
tree-wide sed up front, or Phase 2's gate loses its meaning.

The `*Result.v` sites are the ones to watch later: they are end-to-end entry
points, so once Phase 4 exists some of them may want the semantic
`ValidCFGVerifierContract` rather than what they pass now. Phase 5 question,
not a Phase 3 one.

### §2.5 The block annotation then IS a contract

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
| ten `strip` sites in `EndToEnd.v` | the two lists are now NAMED (`cfg_instrs c` for memory, `a` for the table) instead of one being derived from the other |
| `strip_length` | no longer needed at a boundary |
| `AST_AnnotInstr`, `list_AST_AnnotInstr`, `Local Arguments List.cons {_} & _ _.` | exist ONLY so `[MV X3 X2; …]` typechecks as `list AnnotInstr`. With an AST field, examples need no coercion. **Check before deleting** — the coercion is still wanted — §2.2 has an un-annotated example write `CFGVerifierContractVC c c_instrs` with `c_instrs : list AST` riding it |

**What does NOT change:** `AnnotInstr` stays the executor's payload,
`instrs_of_list` stays `AnnotInstr`-valued, `itable_rel` and `table_of_list`
are untouched. This removes annotations from the STATEMENT, not from the tool.

## §4. Phases

### Phase 1 — the record and the two light Valid forms
`Contracts.v` only: flip the field to `list AST`, rename
`ValidCFGVerifierContract` to `CFGVerifierContractVC` and give it the annotated
list `a` as its second argument, and add `strip_of_AST`. **No third form and no
`Ha` argument** (§2.2). Decide here whether `Valid_CFG_VC` keeps an unused
`cfg_instrs` parameter or drops it. **The SEMANTIC stating form is NOT part of
this phase** — it is Iris-level and lands with Phase 4; Phase 1 must not put an
Iris require into a light file (root CLAUDE.md, ~1.2 GB across seven
examples).

GATE 1: `Contracts.vo` compiles, and `CFGVerifierContractVC c (cfg_instrs c)`
is definitionally the proposition the name `ValidCFGVerifierContract` denoted
BEFORE this plan — check by `reflexivity` against an inlined copy of the old
body or the pre-change `.vo`, not by eye. (The name is being reused for the
semantic form, so "same name, same meaning" is exactly the check that stops
being available.)

### Phase 2 — the generators
`GenContract.v`, `GenSegment.v` (3 `cfg_instrs` refs), `GenCompose.v` (11).
**`gen_seg_contract`'s `prog` argument is the landmine — see §5.**
`GenCompose.v`'s 10 validity hypotheses quantify `a` — see §2.4. Pinning them
to the un-annotated program is what would stop a generated segment being
discharged with a block annotation inside it.

GATE 2: every light `Example/*.v` compiles after the mechanical rewrite of its
statement to `CFGVerifierContractVC c <its own instrs>` and NO other edit — no
changed `_instrs` block, no changed tactic. If an example needs more than that,
something upstream is wrong; fix that, not the example.

### Phase 3 — EndToEnd
`EndToEnd.v` (33 `cfg_instrs` refs, 10 `strip` sites). The memory side takes
`cfg_instrs c`; the table side takes `a`. Expect this file to get shorter and
the `strip`-vs-no-`strip` comment at :1514 to be deleted.

GATE 3: `make Results.vo` green; `./scripts/gate.sh` at `GATE_JOBS=1` green.
**Plus: read through the `blocksSound` premises** — with the parameterised
form, each entry point's VC premise and its `blocksSound` premise must name the
SAME `a`. That is what closes the §2 false-block hole, and under this design it
holds by construction, so this is a read-through and not a proof obligation.

### Phase 4 — blocks on the new shape, and the SEMANTIC stating form
Delete `SBlk`, introduce `BlkAnnot` (`off` + the packed contract, §2), have
`blk_at` instantiate the contract at the attachment address so the author never
writes an offset, and re-point `sexec_block`/`cexec_block`/`rexec_block`/
`blockSound`/`blockSound_of_vc`/`blockFaithful`.

**This is also where the annotation-free stating form lands**, because §2's
finding is that it IS `blockSound` re-indexed by a `CFGVerifierContract`. So
the phase does not add a definition so much as rename one, plus the bridge
`ValidCFGVerifierContract_of_VC` (= today's `blockSound_of_vc`, with the VC
premise now `CFGVerifierContractVC c a`, the `strip` equation as an ordinary
hypothesis, and the `blocksSound` premise naming that same `a`). Once it exists, a verified contract
plugs into an `ai_block` with no annotation in sight, and nesting is just
iterating that — which is what Emiel asked for and what loops need.

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
- **Do not edit an example to make Phase 2 pass.** The statement rewrite exists so
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
