# PLAN — a loop as a SELF-REFERENTIAL block (Löb), 2026-09-24

## Goal (user's words)

"Only the induction should happen in the meta-logic, but you should try to get
all the framing and stuff to happen in the symbolic executor where the solver
can help."

The LoopSpec route (`ZZBlkLoop.v`, `loop_runs` + `blockSound_of_loop`) works
but leaves ~45 lines of per-loop Iris glue (`cd_entry`, the `HOut` bullet):
the block contract and the LoopSpec are two descriptions of one loop, and the
glue reconciles them by hand.

## Design

A loop is ONE block contract whose precondition is the invariant, verified by
ONE VC run over the loop's own code **with the loop head annotated with that
same block**:

- run the body once from the head;
- back edge → the executor finds `ai_block = Some b` at the head, CONSUMES the
  invariant (solver proves it from the branch condition), PRODUCES the post,
  resumes at the exit offset;
- fall-through → consume the post.

All framing is consume/produce, discharged by the solver.  The only
meta-logic is one generic lemma, proved once, by **Löb induction**:
`cfg_vc_rec (blk_contract b) ab → ⊢ blockSound words v b`, where the IH is
`▷ blockSound b` and every use of b inside its own VC is after ≥1 executed
instruction, i.e. under that ▷.  No LoopSpec, valuation family, trip count,
latch, back-edge obligation or variant.

**Why the VC is not trivially circular:** its FIRST step executes the entry
instruction and never consults `ai_block` — otherwise it would apply b to
itself at step 0.  Done by a new entry point, NOT a flag in `sexec_cfg_addr`
(`ZZBlkAB`'s outer contract starts AT an annotated instruction and needs the
block to fire at step 1, so the ordinary entry must keep its behaviour).

**Partial correctness only** (Löb).  Believed sufficient: the end theorems
quantify over executions that REACH the exit in n steps, and `myWP2_loop` is a
contractive safety fixpoint (Adequacy.v:125).  Confirm against
`cfg_instrs_safe` before relying on it (phase 4).

## Phases

- **0. SPIKE — the Löb/▷ question. DONE 2026-09-24.**
  `Example/ZZRecStep.v`: `cexec_first_step` (concrete first step) and
  `sound_first_step`, i.e. the first step is sound given only
  `▷ blocksSound`; after the step `iModIntro` strips the later and the
  EXISTING `sound_exec_cfg_addr_myWP2` finishes unchanged.  coqc-green.
  (`sound_exec_cfg_addr_myWP2` already takes blocksSound as a persistent
  Iris hypothesis — only `sound_cexec_triple_addr_myWP2_w` lifts it from ⊢.)
- **1. `Verifier.v` + `Contracts.v`. DONE 2026-09-24.** `sexec_first_step`,
  `sexec_triple_addr_rec`, `scfg_verification_condition_rec`,
  `CFG_VC_triple_rec`, `cfg_vc_rec`; `sexec_cfg_addr` unchanged; make-green.
  **Empirical result (`Example/ZZCdRec.v`, coqc-green): countdown as ONE
  self-referential contract discharges by `solve_param_vc` in 22 ms** — the
  solver does the back-edge framing.  Negative controls: unannotated code
  fails; an invariant not preserved by the body (`k ≠ 1`) fails.  Two
  findings: dropping `k ≠ 0` still verifies, correctly (partial correctness:
  from 0 the counter wraps and the loop exits); and the ORDINARY `cfg_vc` on
  self-annotated code proves trivially (useless, not unsound — its bridge
  needs `blocksSound` for that program).  Debt: `sexec_triple_addr_rec` is a
  verbatim copy of `sexec_triple_addr`.
- **2. `VerifierRel.v`. DONE 2026-09-24.** `cexec_first_step`,
  `rexec_first_step` (stated exactly like `rexec_cfg_addr` minus `first`; the
  proof is `rexFS`'s case 3 minus drop/GC, handing off to `rexec_cfg_addr`),
  `cexec_triple_addr_rec`, `rexec_triple_addr_rec`,
  `ccfg_verification_condition_rec`, `rcfg_verification_condition_rec`.
  Developed in a probe (pet cannot open this file — it also OOMs on any probe
  requiring it; `coqc` peaks at 6.76 GB), compiled first try, ported
  verbatim, `make`-green.
- **3 + 4. `GenCompose.v` (not Adequacy.v — it already holds the other
  blockSound doors and has `Local Unset Implicit Arguments`, so the probe
  proofs port verbatim). DONE 2026-09-24.** Section `RecLoop`:
  `sound_first_step`, `sound_cexec_triple_addr_rec_myWP2_w` (block premise an
  Iris hypothesis under ▷), `sound_scfg_verification_condition_rec_myWP2_w`,
  `blocksSound_of_head_iris` (`□ blockSound ⊢ blocksSound`), and
  **`blockSound_of_rec_vc`** — `iLöb`; the IH `▷ blockSound b` supplies
  `▷ blocksSound` for the loop's own program.  Plus `rec_vc_of`.
- **5. Example. DONE 2026-09-24.** `Example/ZZCdRec.v` (the loop as ONE
  contract, 22 ms) + `ZZCdRecLinkSpec.v` (outer VC, 15 ms) +
  `ZZCdRecLink.v`: `cdRec_blockSound` is one `iApply` of the Löb lemma plus
  where-the-code-sits arithmetic; `valid_rlink_contract :
  ValidCFGVerifierContract rlink`, axiom-clean.  The spikes ZZRecStep /
  ZZRecRefine / ZZRecSound were retired once ported.

- **6. ONE CHAIN, via a RE-ENTRY annotation, 2026-09-24.** The `_rec` chain
  was a verbatim copy of the ordinary one with the entry step swapped.  A
  first attempt (525be59f) made EVERY entry skip blocks, which deleted the
  copies but stopped a contract from starting at a block -- rejected.  The
  fix is in the annotation instead: `AnnotInstr.ai_loop`, a block that fires
  only once an instruction of the run has executed, next to `ai_block`, which
  fires always.  Both executors dispatch on `ai_fire stepped ai`;
  `sexec_cfg_addr` carries `first` (exit test) and `stepped` (re-entry),
  `cexec_cfg_addr` carries `stepped`.  Gone: `sexec/cexec/rexec_first_step`,
  `sound_first_step`, every `_rec` definition and lemma, `rec_vc_of`,
  `blockSound_of_rec_vc`.  `Adequacy.blockSound_of_vc` does the `iLöb` itself,
  with premises `Hbs0 : ⊢ blocksSoundAt false …` (entry blocks, needed now)
  and `Hbs : □ blockSound b ⊢ blocksSound …` (all blocks, under the later);
  `blocksSound = blocksSoundAt true`, so no external bridge changed.  The
  LoopSpec-to-block door (`blockSound_of_induction` / `blockSound_of_loop`,
  `blk_pre` / `blk_post`) was deleted as subsumed.

- **7. Tracked + end-to-end, 2026-09-24.** The probes became
  `Example/CountdownRec.v` (`valid_cd_rec`, `valid_cd_link`, the negative
  controls; `rlink` renamed `cdLink`) and `Example/CountdownRecResult.v`
  (`cdRec_blockSound`, `cd_link_blocksSound`, and
  **`countdown_rec_noninterferent`**, `noninterferent_strong` through
  `cfg_instrs_endToEnd`), in `_CoqProject`, `Results.v` and the gate's
  `AXIOM_CLEAN_THMS`; axiom-clean.  Two forced choices in the statement:
  base 0 (the block is justified at base 0), and X1 pinned to 2 (reg_specs
  cannot express `k ≠ 0`).  `valid_rlink_contract` (the sealed
  `ValidCFGVerifierContract`) was dropped: `cfg_instrs_endToEnd` takes the
  VC and the block obligation directly, so nothing consumed it.

## Open

- A loop block at index > 0 still needs the index-n `blocksSound_of_head`.

## Out of scope

LoopSpec / `loop_runs` stay: they serve segment composition (muladd), not
only loops-as-blocks.
