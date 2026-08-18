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
  gen_contract, discharging the VC, and the gen_contract_noninterferent_param end
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
**copy the closest analogue** in `Example/<Prog>.v` + `Example/<Prog>Result.v`
rather than starting from scratch. A new example gets **two** files:

| File | Holds | Requires |
|---|---|---|
| `Example/<Prog>.v` | instrs + specs (statement-relevant), parametric contract, `valid_<prog>_cfg_contract_param` VC | just `Example.Prelude` |
| `Example/<Prog>Result.v` | the end theorem(s) `<prog>_noninterferent[_param]` | `Example.Prelude` + `EndToEnd` + `Example.<Prog>` |

Both go in `_CoqProject` before `Results.v`, the `Result` file is added to
`Results.v`'s re-export list, and the end theorem names are added to the gate's
`AXIOM_CLEAN_THMS` list in `scripts/gate.sh`.

**Do not put the end theorem in `Example/<Prog>.v`.** It would drag `EndToEnd`
(and so `Adequacy`) into the example, serializing that ~85 s chain ahead of every
example instead of letting it build in their parallel shadow — ~40 s of wall time
per -j2 gate build. Only write a `_param` contract/VC; the concrete-base result
is a corollary (`gen_contract_noninterferent_*_simple` / `ni_rel_corollary`), so
a concrete-base VC is dead compile time.

1. **Instructions.** Translate the RV32I assembly (e.g. Compiler Explorer output of
   `clang -O2 -march=rv32i`) into a `list AST` with
   `case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` — it tags each entry with its
   source line for auditability. Don't hand-transcribe real compiled code.
   **Label resolution works only since 2026-08-03** (`modpow_win_full`, the first
   example translated from real compiled control flow): the directive regex was
   tested before the label regex, so every clang local label (`.LBB0_2:`) was
   eaten as a directive and every branch failed with "undefined label". If a
   listing's last label sits on the dropped `ret`, translate WITHOUT `--drop-ret`
   (so the label still resolves, to one-past-the-end) and delete the trailing
   `RISCV_JALR` entry by hand — a branch to one-past-the-end is covered by
   `pcOutOfInstrs_exitCond` with no `extra_exit_offs`.
   **Watch for full unrolling:** clang unrolls a loop whose bounds are
   compile-time constants, so a program compiled with its sizes baked in
   verifies nothing about loop control flow. Keep the bounds as runtime
   parameters (as the real source has them) and pin them to public constants in
   the CONTRACT instead.
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
   Proof. vm_compute. solve_vc. Qed.` — for a PARAMETRIC-base contract
   (`gen_contract_param`/`_rel`, the usual choice for a new example) add the
   symbolic-base fetch-residual closer:
   `Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.` Residuals
   and debugging: **cfgver-solve-vc**.
5. **End lemma.** `<prog>_noninterferent : noninterferent_strong …`. Common case
   (register-only or straight-line, standard `pcOutOfInstrs` exit): use the
   specialised bridge **`gen_contract_noninterferent_param_simple`** (or
   `_rel_classed_simple` when there is data memory — see step 3's note on
   `gen_contract_rel_classed`, which is the default builder there) — it bakes in the mechanical
   premises AND removes the ordering hazard below, leaving only NoDup +
   length-bound (+ `HDataAddrs`/`Hbound` for `_rel`) + the VC. Only reach for
   the general `eapply gen_contract_noninterferent_param` / `_rel*` (its **five**
   premises: NoDup, `HDataAddrs`, length bound, `HexitOffs`, the VC — and the
   "discharge the VC FIRST" gotcha) when there are extra exit offsets
   (`jump_if_zero`) so `_simple` does not apply. Premise-by-premise table +
   both patterns: **cfgver-gen-contract**. Gotcha: `HDataAddrs` needs a case
   split on *every* index of `mem_specs`, not just index 0.
6. **Axiom hygiene.** `Print Assumptions <prog>_noninterferent.` must show only
   `pure_decode` and `mmioenv` (the model's inherent parameters). Anything else —
   especially `functional_extensionality` — means a proof took a shortcut; fix it.

**If the program uses data memory:** addresses must be hardcoded contiguously right
after the code (the `countdown_mem` pattern); real pointer arguments are an open
TODO. Data-memory proof plumbing: **cfgver-memory**.
