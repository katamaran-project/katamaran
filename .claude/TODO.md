# Next session briefing

CLAUDE.md and the `/katamaran` skill are auto-loaded — read them for full context.
This file tracks the approved task list and current starting point.

---

## Current state (after TS revert)

Examples.v is restored to the state at commit `8762d44c` ("add countdown_mem
endToEnd"), with one addition: `exitCond_WP2_loop` now uses the SyncVal form
`∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝` (cleaner than the old disjunctive form).

Kept from the TS branch (independent of TS goal):
- `reg_valid_nd` in `theories/Iris/Resources.v`
- `reg_valid2_nd` in `theories/Iris/BinaryResources.v`
- `adequacy_gen_n` refactoring in `theories/Iris/BinaryAdequacy.v`
- Documentation comments in `Spec.v` and `Verifier.v`

---

## Abandoned approach: termination-sensitive end-to-end (reverted)

**What was tried** (commits `41514a00`–`5b8c2df1`):

A `semWP2_preservation_fwd'` lemma was added to bridge from world-1's n-step
execution to world-2's execution while threading a PC-sync guarantee through
each step. The idea: if both PCs start equal (`Hpc`), after each synchronized
step they remain equal, so at exit the exit condition fires in both worlds
simultaneously. This would strengthen `adequacy_gen_RiscVNStepsExitCond_strong`
to only require a single-world NSteps hypothesis (world-2 steps are existential).

**Why it was abandoned:**

The S n case of `semWP2_preservation_fwd'` requires deriving
`read_register γ1mid pc = read_register γ2mid pc` after `semWP2_step`. After
the step, we hold `regs_inv2 γ1mid γ2mid` (the AUTH part of ghost state) but
NO `reg_pointsTo2 pc` fragment. `regs_inv2` is defined as two separate
`regs_inv`, one per world — it carries no cross-world PC relationship. Multiple
repair strategies were considered (ghost invariant, semantic argument, specialized
postcondition Q) and all ran into the same obstacle. The statement may be
provable but requires additional semantic lemmas about `RiscVStep` or a structural
change to the ghost resources.

---

## TODO list (from TODOS.txt + session notes)

**Priority 1 (termination-sensitive noninterference — try from scratch):**
- The goal: prove that if world-1 terminates in n steps, world-2 also terminates
  in n steps (same count, same exit condition). The obstacle is PC-sync after
  `semWP2_step` without a `reg_pointsTo2 pc` fragment.
- `reg_valid2_nd` is available and returns resources without consuming them.
  The remaining question: WHERE does the `reg_pointsTo2 pc` fragment come from
  during the loop body?

**Priority 2:**
- Make a `Definition` for non-interference such that `Examples.v` becomes
  readable — callers should state "this program is non-interfering" without
  reading the full adequacy chain.

**Priority 3 (end-to-end automation):**
- A lemma that works for *any* `gen_contract`-generated contract without
  per-program boilerplate.

**Cleanup / refactoring:**
- Consolidate everything in CFGVer, so BlockVer can be deleted.
- Rename everything in CFGVer to remove mentions to BlockVer.
- Remove `sound_sblock_verification_condition` in favor of
  `sound_sblock_verification_condition_myWP2_loop`.
- Remove duplicate `gen_contract` infrastructure.
- `Examples.v` is too large; split into: logic lemmas, examples, memory helpers.

**Modularity (longer term, discuss with Dominique):**
- Move from lists of instructions to maps from addresses to instructions.
- Change hardcoded start PC at 0 (needed for modularity).
- Add exit resources (resources required when reaching the exit condition).
  Subtle: execution must stop *first time* exit condition is reached.
- Ask Dominique or Sander whether `AnnotInstr` is worth looking at.

**Known remaining Admits (expected):**
- `valid_jmp_fwd` (BlockVer): BlockVer cannot handle JAL. Intentional.
- `instrsAndDataMemory`: proof admitted; statement correct.

---

## Potential next tasks (not yet approved)

- Prove `jmp_bwd` (backward jump / loop) as a second CFGVer example.
- Close the general `semTripleCFG → myWP2_loop` bridge.
