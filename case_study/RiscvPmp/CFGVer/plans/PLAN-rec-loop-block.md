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
- **2. `VerifierRel.v`** (THE RISK): concrete mirror (`cexec_first_step`,
  `cexec_triple_addr_rec`) and refinement.  `step_after_drop`'s refinement is
  INLINED in `rexec_cfg_addr` (~l.1309-1416, 1699), not a lemma — extract it
  (`rstep_after_drop`) or reproduce it.  pet cannot open `VerifierRel.v`;
  develop in a probe (cf. `ZZGhostRefineProbe.v`).
- **3. `Adequacy.v`**: move `sound_first_step` in; triple-level
  `sound_cexec_triple_addr_rec_myWP2` taking `▷ blocksSound` as an Iris
  hypothesis; `sound_scfg_verification_condition_rec_myWP2`.
- **4. `GenCompose.v`**: `blockSound_of_rec_vc` by `iLöb`; `□▷ blockSound b ⊢
  ▷ blocksSound` for the loop's program (b at the head, nothing else, or
  others from a premise).
- **5. Example**: countdown as ONE rec contract; relink `ZZCdLinkSpec`/
  `ZZCdLink` through it; delete the LoopSpec-route glue if it's subsumed.

## Out of scope

LoopSpec / `loop_runs` stay: they serve segment composition (muladd), not
only loops-as-blocks.
