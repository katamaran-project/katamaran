---
name: cfgver-new-example
description: >
  The step-by-step recipe for verifying a NEW example program end-to-end in
  Katamaran CFGVer — the most common CFGVer task. Covers BOTH translating real
  compiled assembly into a list AST via asm_to_ast.py AND hand-authoring a
  synthetic program/loop from scratch when there's no real source to translate
  (e.g. a small-N feasibility spike toward a bigger not-yet-attempted example,
  such as a loop a real compiler would just fully unroll at that trip count) —
  choosing exitCond / fuel / extra_exit_offs, building the contract with
  gen_contract, discharging the VC, and the gen_contract_noninterferent end
  lemma. Trigger on "verify this program", "add a new example", "prove X
  noninterferent", "write/design a small-N or synthetic version of X first",
  "add a loop that does Y" — including terse follow-ups that refer back to code
  discussed/compiled earlier in the conversation rather than restating it
  ("prove non-interference for this version"), even when bundled with an
  unrelated side-task (e.g. "...and update the TODO"). NOT for the individual
  layers' details (each step links its skill) and NOT for merely inspecting an
  already-proven lemma (e.g. running Print Assumptions on it — no skill needed).
---

# Recipe: verifying a new example program end-to-end

Every existing example (`swap`, `countdown_mem`, `cmovznz4`, …) follows this shape —
**copy the closest analogue** in `Example/*.v` + `Results.v` rather than starting
from scratch. A new example gets its own `Example/<Prog>.v` (instrs + specs +
contract + `valid_*` VC), is added to `_CoqProject` before `Results.v`, and its
end theorem goes in `Results.v` (plus the gate's `AXIOM_CLEAN_THMS` list in
`scripts/gate.sh`).

1. **Instructions.** Translate the RV32I assembly (e.g. Compiler Explorer output of
   `clang -O2 -march=rv32i`) into a `list AST` with
   `case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` — it tags each entry with its
   source line for auditability. Don't hand-transcribe real compiled code.
   **Hand-authoring a synthetic program/loop instead** (no real source to
   translate — e.g. a small-N feasibility spike like `countdown`/
   `countdown_mem`/`key_schedule_loop2`, where a real compiler would just fully
   unroll a small trip count): the script's automatic label resolution is
   exactly what's missing, so this needs manual care — AST constructor field
   order, register aliases, and (the sharpest edge, wrong exactly once already)
   the backward-branch-immediate convention are all in
   **`cfgver/references/asm-vocabulary.md`**.
2. **Exit condition + fuel.** Typically `pcOutOfInstrs_exitCond init_addr instrs`;
   fuel must exceed the number of instruction steps actually executed, **with
   slack** (tight fuel shows up as a bare `False` deep in the VC —
   → **cfgver-solve-vc**). If control flow can exit other than by falling off the
   end (e.g. a forward branch past the program), collect those offsets as
   `extra_exit_offs`. **Scaling an EXISTING backward-branch loop example to a
   bigger trip count is NOT just a fuel-tuning exercise**: `vm_compute` itself
   can blow up exponentially in trip count (confirmed on `key_schedule_loop2`,
   N=2→8 already unfinished after minutes) — see **cfgver-executor**'s
   "Backward-branch loops" section before assuming more fuel/timeout will
   eventually get there.
3. **Contract.** `gen_contract init_addr reg_specs mem_specs instrs extra_exit_offs
   ec fl` — spec-triple formats and public/private/pinned semantics in
   **cfgver-gen-contract**. (Hand-written contracts instead: **cfgver-contracts**.)
4. **VC.** `Lemma valid_<prog>_cfg_contract : ValidCFGVerifierContract ….
   Proof. vm_compute. solve_vc. Qed.` Residuals and debugging:
   **cfgver-solve-vc**.
5. **End lemma.** `<prog>_noninterferent : noninterferent_strong …` by
   `eapply gen_contract_noninterferent;` discharging its **five** premises (NoDup,
   `HDataAddrs`, length bound, `HexitOffs`, the VC) — the premise-by-premise table
   is in **cfgver-gen-contract**. Gotcha: `HDataAddrs` needs a case split on
   *every* index of `mem_specs`, not just index 0.
6. **Axiom hygiene.** `Print Assumptions <prog>_noninterferent.` must show only
   `pure_decode` and `mmioenv` (the model's inherent parameters). Anything else —
   especially `functional_extensionality` — means a proof took a shortcut; fix it.

**If the program uses data memory:** addresses must be hardcoded contiguously right
after the code (the `countdown_mem` pattern); real pointer arguments are an open
TODO. Data-memory proof plumbing: **cfgver-memory**.
