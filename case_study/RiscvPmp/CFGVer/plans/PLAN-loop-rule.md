# PLAN — loops by an invariant rule: no `stepped`, no self-block (2026-10-14)

Status: **DRAFT for Emiel's review.** Design decided by Emiel in a VibeWise
session (2026-10-14, `.vibe-wise/progress.md`); nothing implemented. Spike
declined by Emiel ("Don't bother with the spikes, just draft the plan"), so
the risks in §5 are carried into the phases instead of settled up front.
Branch: `issue/loop-rule` off `KatamaranRel`. Supersedes the executor half of
PLAN-rec-loop-block.md (the `ai_loop` re-entry design, 286fd1bd).

## 0. Goal (Emiel's words)

"I only care about clarity: How is someone reading the code going to
understand? How many things do we need to juggle at once? What is the
simplest abstraction?" — and: "I don't support the stepped concept, I
understand the need for first when verifying blocks that loop around."

The system works today; this is a readability redesign. It must not change
any trusted statement (Noninterference.v, Layout.v, `*Result.v` statements,
`*_instrs`).

## 1. Vocabulary (defined before use)

- **loop contract** — a `CFGVerifierContract` describing a whole loop, from
  its head to its exit. Used at its call sites as an ordinary block.
- **head** — the loop's first instruction; the loop contract's entry. Its
  address term is the loop table's offset-0 key (`cfg_placement` + 0).
- **parameter** — a logic variable of the loop contract (`blk_ctx`) that does
  NOT change across trips (code base `q`, end address `e`, a `total`).
- **invariant (Inv)** — the loop contract's precondition. Every variable that
  changes across trips is existentially quantified INSIDE it.
- **post** — the loop contract's postcondition; mentions parameters only (plus
  its own existentials).
- **back edge / fall-through** — the two ways one run of the body ends:
  returning to the head, or reaching the loop's exit.
- **head test** — new executor check: not the entry step, and the pc term
  equals the head term → consume Inv, end the path.
- **exit test** — existing check (`is_exit`): not the entry step, and the pc
  term equals the exit term → stop (the post is consumed by the triple).
- **loop VC** — the verification condition of a loop contract: one run of the
  body from Inv with BOTH tests live. Entry point `cfg_vc_loop` (new; §3b).
  Ordinary contracts keep `cfg_vc` with the exit test only.
- **step-first** — `myWP2_step E` (new, §3d): "at least one machine step is
  taken, then `myWP2_loop E`". The non-exit disjunct of `myWP2_loop_fix`
  (Adequacy.v:112–124) with `myWP2_loop E` after the step.

## 2. Decisions (Emiel, 2026-10-14)

- **L1** The writer supplies an invariant and an explicit post. **No
  measure**: partial correctness, which is all the end theorems need (they
  quantify over runs that reach the exit). Generated exit-state posts are
  deferred ("to avoid having to worry about this for now").
- **L2** Parameters are exactly the unchanging things; they may be values
  from before the loop (`total`). Every changing variable is fresh (∃ in
  Inv). The post mentions parameters only. ⇒ no stability obligation, no
  ghost entry values.
- **L3** The tool runs the body ONCE from Inv; head test and exit test, both
  off on the entry step (`first`).
- **L4** The induction lives only in the meta-level loop rule, which receives
  "the body preserves Inv" and "the fall-through path gives the post". The
  executor never uses an induction hypothesis: no self-block, no `stepped`.
- **L5** Blocks earn a step (option ii): `blockSound` promises ≥1 machine
  step, so a block — e.g. a separately verified body segment — may sit at the
  loop head. Emiel's reason: "Preprocessing the loop body separately if
  needed." Rejected alternative (i): forbid a block at a loop's head.
- **L6** Accepted additions (Claude-proposed, confirmed at the design
  checkpoint): a loop-specific VC entry; use sites unchanged (`ai_block`);
  head detection by the comparison `lookup_instr` already uses; scratch
  registers ∃ in Inv and post; every loop context changes shape (changing
  variables leave `blk_ctx`).

## 3. Design

### 3a. What the author writes (check_scalar loop 1, illustrative)

Today (`Example/CheckScalar/CheckScalarParamLoop1.v:22–65`): context
`q e n d kE`; `l1_inv` over `n d`; `l1_post` re-binds a count `c` and states
done = `d + n`. Under L2:

```
parameters: q, e, kE, total
Inv  := ∃ n d. l1_state n d e kE ∗ n ≠ 0 ∗ d + n = total ∗ bounds ∗ scratch
post := ∃ d.   l1_state 0 d e kE ∗ d = total ∗ scratch
```

Whether `total` is the right extra parameter for each loop is decided per
loop in Phase 5 (R3).

### 3b. Executor (Verifier.v, Contracts.v)

- `sexec_cfg_addr fuel first` — `stepped` is gone. Block dispatch reads
  `ai_block ai` directly; `ai_fire` is gone.
- A loop VC passes the head assertion: proposed as a parameter
  `head : option (Assertion (Σ0 ▻ "a"∷ty_xlenbits))` (None for ordinary
  contracts). Head test, placed beside the exit test:
  `if negb first && is_head … then consume (extend_to_minimal_pre Inv)
  trans.["a" ↦ apc] ;; <end path>`. The consume uses the existing `trans`
  substitution, so parameters stay fixed and only Inv's ∃ are chosen
  (angelically) — L2.
- Head detection: `Term_eqb (peval apc) (peval head_key)`, i.e. exactly the
  comparison `lookup_instr` (Verifier.v:1095–1098) already performs to find
  the head's instruction at today's back edge. Low risk (R6).
- `cfg_vc_loop c a` (Contracts.v): like `cfg_vc`, with `head := Some
  (cfg_precondition c)`.

### 3c. Concrete mirror + refinement (VerifierRel.v)

- `cexec_cfg_addr` drops `stepped` and gains `first`: the concrete side must
  also refuse to stop at the entry step, or step-first (§3d) is unprovable.
- Head test mirrored the way the exit is today: the concrete side may keep an
  angelic choice; the symbolic side being more decisive is the sound
  direction (same argument as `is_exit_sound`).
- `rexec_cfg_addr` and its block/head lemmas re-proved; 29 `stepped`
  occurrences today.

### 3d. Soundness (Adequacy.v, GenCompose.v)

- **`myWP2_step E`** (§1) with `myWP2_step E ⊢ myWP2_loop E` and a bind
  lemma `myWP2_step E1 ∗ (E1 -∗ myWP2_loop E2) ⊢ myWP2_step E2`.
- **`blockSound` concludes `myWP2_step`** (L5). Its definition
  (Adequacy.v:1439–1453) changes; every producer goes through
  `blockSound_of_vc` (R1).
- **Executor lemma** (`sound_exec_cfg_addr_myWP2`): at `first = true`
  concludes `myWP2_step` — the entry step is an instruction (one machine step)
  or an `ai_block` (step-first by the new `blockSound`); at `first = false`
  concludes `myWP2_loop` as now. Block premise: ONE `blocksSound` (all
  `ai_block`s, needed now). `blocksSoundAt`, the `▷ blocksSound` premise and
  the `Hbs0`/`Hbs` split are gone.
- **`blockSound_of_vc`** for ordinary contracts: no `iLöb`, no self premise.
- **Loop rule** (new): from a loop VC,
  `∀ ι, Inv ι -∗ myWP2_step ((head ∗ ∃ ι', Inv ι') ∨ (exit ∗ post))`
  gives `Inv ι -∗ myWP2_step (exit ∗ post)`. Proved once, by `iLöb` on
  `myWP2_loop` (the meta-logic's induction over the run; the step-first form
  is what makes the IH usable after the head is reached again). L4: this is
  the only place the induction happens.
- **`blkValid_of_loop`** (GenCompose.v, new): a loop contract with a
  discharged `cfg_vc_loop` is a valid block — what the 8 loops' Result files
  call instead of `blkValid_of_seg` + `aiv_loop := true`.

### 3e. Annotation types + seal (Verifier.v, Validity.v, Adequacy.v)

- `AnnotInstr` loses `ai_loop`; `AnnotInstrV` loses `aiv_loop`; `selfBlk` and
  `eraseV`'s contract argument go (it existed only for `aiv_loop`).
- `ValidCFGVerifierContract` loses its `aiv_loop = false` conjunct;
  `annotsValid` loses its top-level ban (V9) — there is nothing left to ban.

### 3f. Removed (census 2026-10-14, non-ZZ `.v` files)

`ai_loop` (18 files), `ai_fire` (Adequacy, GenCompose, Verifier,
VerifierRel), `stepped` (Adequacy, Verifier, VerifierRel), `aiv_loop`
(Adequacy, Validity, Verifier, CountdownRecResult), `selfBlk`, `eraseV`'s
argument (+ 3 Result files), `blocksSoundAt`, `Hbs0`. Each removal is checked
by build, not assumed.

## 4. Phases

Light check per phase (compile the phase's files and their direct users,
`keep_vo`); ONE full gate at the end (feedback-light-gates). VibeWise paused
during proof phases; resume if a design question comes up.

1. **Executor** (Verifier.v, Contracts.v): drop `stepped`/`ai_fire`, add the
   head test and `cfg_vc_loop`. Witness: `CountdownRec.v` migrated —
   `valid_cd_rec` as a `cfg_vc_loop` under L2, plus BOTH negative controls
   (unannotated / non-preserved `k ≠ 1` invariant) still `Fail`. Also record
   the cost of today's `valid_cd_rec` / `valid_l1` before the change (the only
   baseline we will have, R4).
2. **Concrete mirror + refinement** (VerifierRel.v).
3. **Soundness** (Adequacy.v): `myWP2_step`, `blockSound` step-first,
   executor lemma, `blockSound_of_vc` without Löb, loop rule.
4. **Types + seal** (Verifier.v annotations, Validity.v, GenCompose.v):
   §3e; `blkValid_of_loop`.
5. **Migrate the loops** to L2 + `cfg_vc_loop`: CountdownRec(+Result);
   CheckScalarParamLoop1/2 (+CheckScalarParamResult); Muladd LoopD, D0, DAng,
   G, N (+MuladdParamResult). Record-literal sites that only set
   `ai_loop := None`: MuladdParam.v:122, MuladdParamTail.v:156,
   CheckScalarParam.v:55, PaddedLoop.v:42; `eraseV` in CheckScalarPtrResult.
   Use sites that consume a loop's pre verbatim (`cd_link_extra`,
   `pl_extra`, `dLink`) follow the new Inv shape.
6. **Docs travel with code**: skills `cfgver-executor`, `cfgver-contracts`
   (the only two naming these symbols), `CFGVer/CLAUDE.md`; file headers;
   a "superseded" note at the top of PLAN-rec-loop-block.md. Grep the skills
   for every removed name before committing.
7. **Full gate**, statement diff (`scripts/stmtdiff.py`: expected EMPTY on
   the trusted surface), comprehension check with Emiel, merge.

## 5. Risks / open (not spiked — Emiel's call)

- **R1** Step-first threading: `blockSound` → executor lemma → loop rule.
  Believed local (all producers go through `blockSound_of_vc`), untested;
  ZZ probes and any hand-written `blockSound` proof not checked.
- **R2** "End the path" after the head consume: which `SHeapSpec` primitive
  succeeds without continuing (to verify by name in Monads.v).
- **R3** Do muladd D/D0/G fit L2? `d_inv` keeps `c` and `k` separate and
  matches its done array angelically; not checked. If one does not fit,
  decide per loop with Emiel, not silently.
- **R4** VC cost of the new loop VC: predicted equal or lower (the back edge
  does strictly less work), unmeasured; Phase 1 records the only baseline.
- **R5** Concrete head test direction (§3c): mirror of the exit argument,
  unproved.
- **R6** Head detection: low risk, same comparison as `lookup_instr`.
- **R7** Out of scope, unchanged: the LoopSpec machinery (GenSegment.v §4,
  `myWP2_loop_induction`) used by the muladd composed segments.

## 6. Decision log

| # | Date | Decision | Revert path |
|---|---|---|---|
| L1 | 2026-10-14 | invariant + explicit post, no measure | add a measure term + trip-count rule |
| L2 | 2026-10-14 | changing vars ∃ in Inv; post over parameters | today's context-vars + relative post |
| L3 | 2026-10-14 | one body run, `first`-gated head + exit tests | today's self-block at the back edge |
| L4 | 2026-10-14 | induction only in the meta loop rule | — |
| L5 | 2026-10-14 | blocks earn a step (ii), not (i) | (i): forbid a block at a loop head |
| L6 | 2026-10-14 | accepted additions (§2) | — |
