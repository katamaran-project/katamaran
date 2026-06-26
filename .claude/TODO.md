# Next session briefing

CLAUDE.md and the `/katamaran` skill are auto-loaded — read them for full context.
This file tracks the approved task list and current starting point.

---

## Current state: adequacy_gen_RiscVNStepsExitCond_strong

`adequacy_gen_RiscVNStepsExitCond_strong` and `cfg_instrs_endToEnd_strong` now
**compile** with `pc_step_sync` as a hypothesis. This was a workaround —
see the open design question below.

---

## Open design question: pc_step_sync and where to get it

`pc_step_sync` says: if both worlds' PCs agree before a step, they agree after.
This is needed in the strong (one-sided) adequacy to derive `nEC2` at each step
and to pass PC-sync through to the IH.

**Why we needed it here but not in the two-sided adequacy:**
In `adequacy_gen_RiscVNStepsExitCond` (two-sided), `Heval2` is given as input.
`nEC2` comes directly from inverting `Heval2` — the world-2 trace carries it.
No derivation from world-1 needed.

In the strong (one-sided) version, we only have `Heval1`. We derive world-2's
step existentially via `semWP2_preservation_fwd'`. The output is
`∃ γ22mid μ22mid, Steps ...` as a pure Coq existential. At that point:
- `Hregs_new : regs_inv2 γ1mid γ22mid` IS in the Iris context and encodes
  PC synchronization (both worlds fetch the same instruction from the same PC),
  but `read_register γ1mid pc = read_register γ22mid pc` is never extracted.

**The right fix (not yet done):** Strengthen `semWP2_preservation_fwd'` to
also return `⌜read_register γ12 pc = read_register γ22 pc⌝` as part of its
output. This eliminates `pc_step_sync` as an external hypothesis entirely — it
is a consequence of the semWP2 lock-step property, not an assumption.

Alternatively, add a lemma extracting PC-sync from `regs_inv2`:
```coq
Lemma regs_inv2_pc_sync γ1 γ2 :
  regs_inv2 γ1 γ2 ⊢ ⌜read_register γ1 pc = read_register γ2 pc⌝.
```
and use it inside `adequacy_gen_RiscVNStepsExitCond_strong` instead.

---

## TODO list (from TODOS.txt + session notes)

**Priority 1:**
- Make a `Definition` for non-interference such that `Examples.v` becomes
  readable — callers should state "this program is non-interfering" without
  reading the full adequacy chain.

**Priority 2 (pc_step_sync is a strong hypothesis):**
- Strengthen `semWP2_preservation_fwd'` to return PC-sync as a pure output,
  OR prove `regs_inv2_pc_sync` to extract it from `regs_inv2`.
  This eliminates `pc_step_sync` from `cfg_instrs_endToEnd_strong` and
  `adequacy_gen_RiscVNStepsExitCond_strong`. Must be done before
  `jmp_fwd_endToEnd_strong` can be proved cleanly.

**Priority 3 (end-to-end automation):**
- `cfg_instrs_endToEnd_strong` currently still requires manual work. Goal:
  a lemma that works for *any* `gen_contract`-generated contract without
  per-program boilerplate.
- Remove `semWP2_preservation'` duplicate (replace with `semWP2_preservation_fwd'`
  where applicable, or prove the two-sided version from the one-sided one).

**Cleanup / refactoring:**
- Consolidate everything in CFGVer, so BlockVer can be deleted.
- Rename everything in CFGVer to remove mentions to BlockVer.
- Remove `sound_sblock_verification_condition` in favor of
  `sound_sblock_verification_condition_myWP2_loop`.
- Remove duplicate `gen_contract` infrastructure.
- `Examples.v` is too large; split into: logic lemmas, examples, memory helpers.
- Clean up proof of `semWP2_preservation_fwd'` (currently Admitted).

**Modularity (longer term, discuss with Dominique):**
- Move from lists of instructions to maps from addresses to instructions.
- Change hardcoded start PC at 0 (needed for modularity).
- Add exit resources (resources required when reaching the exit condition).
  Subtle: execution must stop *first time* exit condition is reached.
- Ask Dominique or Sander whether `AnnotInstr` is worth looking at.

**Known remaining Admits (expected):**
- `valid_jmp_fwd` (BlockVer): BlockVer cannot handle JAL. Intentional.
- `semWP2_preservation_fwd'`: proof admitted; statement believed correct.
- `pc_step_sync` in callers of `cfg_instrs_endToEnd_strong`: currently
  `Admitted` — provable by `vm_compute` for concrete programs; should be
  eliminated by strengthening `semWP2_preservation_fwd'` instead.

---

## Potential next tasks (not yet approved)

- Prove `jmp_bwd` (backward jump / loop) as a second CFGVer example.
- Close the general `semTripleCFG → myWP2_loop` bridge.
- Prove `regs_inv2_pc_sync` and use it to remove `pc_step_sync`.
