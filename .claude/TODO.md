# Next session briefing

CLAUDE.md is auto-loaded; the detailed CFGVer reference lives in the modular
`.claude/skills/cfgver*` skills (see CLAUDE.md header for the map).
This file tracks the approved task list and current starting point.

---

## Current state

All CFGVer noninterference proofs are one-liners via `gen_contract_noninterferent`.
All contracts are defined using `gen_contract`. See commit history for details.

First realistic example (from the "Breaking Bad" paper discussion) is done:
`cmovznz4` (HACL*'s constant-time conditional move), hand-translated from
`clang -O2 -march=rv32i` output into a `list AST`, proved noninterferent
end-to-end (`cmovznz4_noninterferent` in `CFGVer/Examples.v`).

**MILESTONE (2026-07-04): genuine LOAD-of-secret verified.** `cin`, scratch
registers, AND the `x`/`y` data are now all **private** (`r` private too);
only addresses (hardcoded right after the code, see Priority 1) are public.
The secret words loaded from memory flow through `fun_extend_value`'s union
match `KMemValue (pat_var "result")` with NO `secLeak` on the loaded word —
this is the payoff of the method-Y pattern-match rework (see "Pattern-match
secLeak — RESOLVED" below). `Print Assumptions cmovznz4_noninterferent` shows
only the two standard framework model parameters (`Machine.pure_decode`,
`Base.mmioenv`); the non-interference statement, operational semantics, and
step relation were verified unchanged. Commits `f90a607e` (TCB rule),
`03582316` (`read_ram_sound` fix), `88c947bb` (secret x/y).

A script at `case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` mechanically
translates RV32I assembly (as pasted from Compiler Explorer) into the `list
AST` Coq literal, tagging each entry with its source line for auditability —
use it for future examples instead of hand-transcribing.

---

## TODO list

**Priority 1 (hardcoded start PC):**
- `init_addr = 0` is hardcoded throughout CFGVer. This needs to be a parameter
  so that programs can be placed at arbitrary addresses.
- Note: we will NOT move from instruction lists to address maps; lists are fine.
- Concrete motivating case from `cmovznz4`: real pointer-argument functions
  (x/y/r passed in registers, addresses only known at call time) can't be
  verified as such yet -- `gen_mem_asn`/`gen_contract` only support memory at
  a *literal* address fixed at contract-authoring time. Current workaround is
  to hardcode the pointer registers to concrete addresses right after the
  code (`countdown_mem`'s pattern), which sidesteps needing arbitrary-start
  support but doesn't reflect real calling-convention pointer arguments.
  Revisit once init_addr is parameterized; may also need a genuinely new
  "pointer-relative" memory-ownership generator (symbolic base register +
  literal offset) plus a matching two-world memory-extraction lemma for
  `gen_contract_noninterferent` -- sketched and then abandoned as out of
  scope for `cmovznz4` (see commit history), still open for a future example
  that actually needs real pointer arguments.

**Cleanup / refactoring:**
- **[DONE 2026-07-17, NOT YET COMPILED] Removed dead code from `CFGVer/Verifier.v`:**
  grepped the whole tree first to confirm each was unused outside `Verifier.v`
  itself, then removed: `instrAligned` (+ the stale `bv.uleb : simpl never`
  comment that only existed to justify it, itself unused elsewhere); the whole
  dead WP2-based (as opposed to `myWP2_loop`-based) soundness chain —
  `semTripleCFG`, `sound_stm_aux`, `sound_exec_cfg_addr`,
  `sound_cexec_triple_addr`, `sound_ccfg_verification_condition`,
  `sound_scfg_verification_condition` — none of which anything outside
  `Verifier.v` referenced; Adequacy.v has its own complete parallel chain
  (`sound_exec_cfg_addr_myWP2`, `sound_cexec_triple_addr_myWP2`,
  `sound_scfg_verification_condition_myWP2`, ...) targeting `myWP2_loop`
  instead, and only reuses `ptsto_instrs`, `ptsto_instrs_lookup`, and
  `sound_exec_instruction` from `Verifier.v` — all three kept. This also
  satisfies the separate "remove `sound_scfg_verification_condition`" bullet
  below (folded in, bullet removed). Reworded the section-header/file-header
  comments that described the removed chain. Covered by the same pending
  full-chain compile as the item below (not yet compiled).
- **[IN PROGRESS 2026-07-17] Consolidate everything in CFGVer, so BlockVer can
  be deleted / rename everything in CFGVer to remove mentions of BlockVer —
  broadened to remove mentions of "Block" generally, since CFGVer covers full
  CFGs now, not just straight-line blocks.**
  Turned out `RiscvPmp.BlockVer.Spec` was a REAL load-bearing dependency (not
  a leftover) — `CFGVer/Spec.v` existed as an orphaned, ~93%-identical, never-
  `Require`d copy (nothing in the repo required it), and it didn't even
  compile (an abandoned method-Y rewrite of `read_ram_sound` failed under
  `mode=full`). Fixes applied so far (mechanical, via `sed` — see below for
  verification status):
  - Overwrote `CFGVer/Spec.v` with `BlockVer/Spec.v`'s (working) content
    verbatim, discarding the broken rewrite.
  - Switched all 13 CFGVer files (8 core + 5 `Example/*.v`) from
    `Require Import RiscvPmp.BlockVer.Spec` (+ the empirically-unused
    `RiscvPmp.BlockVer.Verifier`) to `Require Import RiscvPmp.CFGVer.Spec`;
    dropped one genuinely-dead definition this surfaced
    (`filter_AnnotInstr_AST` in `Noninterference.v`, copy-pasted from
    `BlockVer/Examples.v`/`FemtoKernel.v`, never called in CFGVer).
  - Switched the bare `Require RiscvPmp.CFGVer.Verifier` (qualified-only, to
    dodge the old BlockVer-name clash) to a full `Require Import` now that
    the clash source is gone.
  - Renamed the `RiscvPmpBlockVerif{Spec,ShalExecutor,Executor}` modules and
    `{foreignSem,lemSem,TforeignSem}BlockVerif` lemmas to
    `RiscvPmpCFGVerif{Spec,ShalExecutor,Executor}` /
    `{foreignSem,lemSem,TforeignSem}CFGVerif` (13 files).
  - Renamed `Section BlockVerificationDerived` → `CFGVerificationDerived` in
    `Verifier.v`; dropped its now-satisfied "despite the name" caveat and the
    now-stale "Import policy" comment block above it (nobody keeps
    `CFGVer.Verifier` bare-required anymore, so there's no more clash to
    document).
  - Renamed the `*block_verification_condition*`/`*block_vc*` identifier
    family (symbolic/concrete/relational VC + `refine_compat_*`/`sound_*`
    variants) to `*cfg_verification_condition*`/`*cfg_vc*`, matching the
    `CFG_VC_triple`/`Valid_CFG_VC` naming already used in `Contracts.v`.
  - Renamed the `block`/`valid_block`/`blockInitAddr`/`blockInstrs`/
    `blockExitCond`/`blockPlacement` local binders in `EndToEnd.v` (6 repeated
    lemma signatures) to `contract`/`valid_contract`/`contractInitAddr`/etc.
  - Reworded prose across `Tables.v`, `GenContract.v`, `Noninterference.v`,
    `Contracts.v`, `Example/Jumps.v`, `Example/Cmovznz4.v` that described
    CFGVer's own program as "a block"/"the block" → "a program"/"the
    program" (kept the handful of comments in `Verifier.v` that factually
    reference the real, still-existing `BlockVer/Verifier.v` file/module —
    those aren't a naming-legacy issue).
  - Updated the 9 skills docs that named the old identifiers
    (`cfgver`, `cfgver-executor`, `cfgver-refinement`, `cfgver-soundness`,
    `cfgver-solve-vc`, `cfgver-gen-contract`, `cfgver-endtoend`,
    `cfgver-endtoend-internals`, `cfgver-new-example`) to match.
  - Fixed one incidental bug the sed introduced: a `Contracts.v` comment
    comparing to BlockVer's own (differently-named) contract type read
    circularly after the blind rename; reworded by hand.
  **FULLY VERIFIED BY COMPILE (2026-07-17): the entire chain, `Spec.v` through**
  **`Results.v`, is full-compile clean.** (`Spec.v`'s `.vo` had briefly gone
  stale relative to its own source and needed a refresh first — a `Require`d
  `.vo` is loaded as-is, not rebuilt-on-demand.) This covers the
  `*block_verification_condition*`/`*block_vc*` family rename, the `Section`
  rename, `forgetting_RVal`'s removal, all of `Verifier.v`'s comment
  rewording, AND the item-3 dead-code deletion below (which additionally
  touched `Adequacy.v`).
  Next: revisit whether `RiscvPmp/BlockVer/` itself can finally be deleted
  (still used by `FemtoKernel.v` directly — check that first).

**From `Verifier.v` inline TODOs (2026-07-17), in the order I'd tackle them
(duplicate mentions of the same issue at different call sites are merged):**
1. **[DONE 2026-07-17]** Quick, independent doc fixes — no proof risk:
   - Stale-comment sweep: the import-policy note at the top of the file
     (`Examples.v` renamed to the actual post-split file list); the
     "apc must be concrete" + `sexec_cfg_addr` description paragraphs
     (consolidated into one accurate gmap-based description); the
     `rexec_cfg_addr` intro comment (`nth_error` → gmap-lookup);
     `lookup_instr`/`is_exit`'s "plan §0" reference (dropped);
     the Phase-1-plan paragraph before `SITable` (rewritten present-tense,
     points at this TODO.md instead of PLAN-symbolic-base.md phases);
     the "Option B" jargon in the relational-layer overview (dropped).
   - Added an inline explainer to `cexec_triple_addr_tbl`.
   - `peval_eqb_inst` relocation: left as-is for now (an actual file move,
     not a comment fix — folds into step 4 below instead).
   - Verified `case_study/RiscvPmp/CFGVer/Verifier.v` still compiles
     (`rocq_compile_file`, mode=vos) after the edits.
2. **[DONE 2026-07-17, NOT YET COMPILED]** Checked all three dedupe questions
   before touching step 3, so it doesn't rename code that should just be
   deleted:
   - `forgetting_RVal` — genuine duplicate. `theories/Symbolic/UnifLogic.v`'s
     `refine_inst_persist` (generic over any `RInst AT A`, proved via
     `forgetting_repₚ`) is exactly `forgetting_RVal` specialized to
     `RVal σ = RInst (Term Σ σ) (RelVal σ)`. Deleted `forgetting_RVal`;
     rewired its one call site (`rexec_triple_addr_tbl`) to
     `refine_inst_persist`.
   - `refine_guard` — NOT a duplicate. Checked `Solver.v` and
     `Refinement/Monads.v`: the closest existing lemma is
     `refine_assume_formula`, which assumes on *both* sides, whereas
     `refine_guard` assumes only on the concrete side (the symbolic side is
     untouched) — a different, one-sided combinator with no existing
     equivalent. It's generic enough to promote to `Refinement/Monads.v` if a
     second use site ever appears, but that's a core-theories change out of
     scope for this CFGVer-only pass; left in place with an updated comment
     recording the finding.
   - `itable_rel_of_faith_forget` vs `forgetting_itable_rel` — NOT a
     duplicate, despite similar proof shape. `forgetting_itable_rel` commutes
     `forgetting`/`persist_itable` given an *existing* `itable_rel` hypothesis
     (`SITable` on both sides); `itable_rel_of_faith_forget` instead *derives*
     `itable_rel` from the Prop-level `itable_faith` fact via a substitution
     `ζ`, over the raw-list table representation. Both are genuinely used
     together at the single `rexec_triple_addr_tbl` call site. Kept both;
     updated the stale comment.
3. Main consolidation refactor (the biggest cluster — most inline TODOs point
   here). Split into a done part and a deferred part (2026-07-17):
   - **[DONE 2026-07-17, VERIFIED BY COMPILE]** Deleted the old non-table
     chain, confirmed dead by grepping the whole tree both directions before
     removing anything: symbolic `sexec_cfg_addr`/`sexec_triple_addr`/
     `scfg_verification_condition`; shallow `cexec_triple_addr`/
     `ccfg_verification_condition` (NOT `cexec_cfg_addr` itself — it's the
     still-live concrete executor, called directly by `Adequacy.v`'s
     `sound_exec_cfg_addr_myWP2`, which both the tbl and non-tbl bridges
     route through); relational `rexec_cfg_addr`/`rexec_triple_addr`/
     `rcfg_verification_condition` + their 3 `RefineCompat` instances. This
     surfaced two more dead lemmas in `Adequacy.v` (not just `Verifier.v`):
     `sound_cexec_triple_addr_myWP2` / `sound_scfg_verification_condition_myWP2`
     had zero callers — `Results.v`/`EndToEnd.v` only ever call the `_tbl`
     bridge — so those were removed too. Confirms `Contracts.v`'s
     `CFG_VC_triple` already exclusively builds the `_tbl` VC: it's what
     every example runs on today, not just the parametric-base ones.
     Reworded `sexec_cfg_addr_tbl`'s doc comment positively (what it does,
     not what it doesn't) while in there. Full chain (`Spec.v` → `Results.v`)
     recompiled clean afterward — see "Consolidate everything in CFGVer"
     entry above.
   - **Deferred to a follow-up pass** (wider blast radius — spans
     `GenContract.v`/`Contracts.v`/`EndToEnd.v`/`Results.v`, not just
     `Verifier.v`): rename the `_tbl` versions to canonical names and drop
     all remaining `tbl`/`Tbl` references. Bundle in while touching this
     region:
     - ~~Rename `Section BlockVerificationDerived`~~ — already done as part
       of the Block→CFG rename above (now `CFGVerificationDerived`).
     - Give `SITable`/`SETable` clearer names (flagged as unclear on first
       read).
     - Type `subst_itable`'s and `sexec_triple_addr_tbl`'s `tbl`/`exits`
       parameters as `SITable`/`SETable` instead of raw lists (flagged twice).
     - Rename the `Phase1SelfTests` section to drop the process reference,
       keep the lemmas/tests themselves.
     - Dedupe `itable_faith` vs `itable_rel` (flagged as near-duplicate, one
       over a raw list where the other is over `SITable`).
4. Once consolidated: split the `SITable`/gmap/`SETable` machinery out into
   its own section, module, or file (explicitly flagged as deserving one).
5. Proof engineering (standalone, can happen last): `rexec_cfg_addr_tbl` was
   not written in rsolve style and is suspected to be missing `RefineCompat`
   instances for tables — investigate the gap, then use it as a golf target;
   same root cause is flagged at the `itable_rel_of_faith_forget` call site
   inside the `rexec_cfg_addr_tbl_2`-ish proof.
   - (The `instrAligned`-outdated note reinforces the already-approved
     2026-07-16 dead-code removal above — no new action needed.)

**Modularity (longer term, discuss with Dominique):**
- Parameterize hardcoded start PC at 0 (see Priority 1).
- Add exit resources (resources required when reaching the exit condition).
  Subtle: execution must stop *first time* exit condition is reached.
- Ask Dominique or Sander whether `AnnotInstr` is worth looking at.

**Known remaining Admits (expected):**
- `valid_jmp_fwd` (BlockVer): BlockVer cannot handle JAL. Intentional.

## Pattern-match `secLeak` — RESOLVED (2026-07-04, method Y)

**Status: DONE.** Pattern matching used to demand full `secLeak` (both worlds
fully synchronized, `SyncVal`) on the scrutinee, which for `LOAD` forced the
loaded value to be public — the blocker for `cmovznz4` with secret `x`/`y`.
This is now fixed end-to-end via **method Y** and `cmovznz4` verifies with
secret loads (see MILESTONE above). No admits; only the two standard framework
model axioms remain.

**Root cause (for reference).** `secLeak` = fully synchronized, but a pattern
match only needs both worlds to select the *same case* (same constructor); the
payload it binds is a `RelVal` that may legitimately be `NonSyncVal` (differ per
world). `semWP2_pattern_match` already computes the two worlds' cases
independently, so soundness only needs case-agreement, not value sync. The
driving case: every `LOAD` runs `fun_extend_value` (`RiscvPmp/Machine.v:528`),
which matches the `KMemValue (pat_var "result")` union; the secret loaded word
is bound by that inner `pat_var`, and the union constructor is statically known,
so it is safe but the old rule rejected it.

**What method Y did (the axis is UNIQUE-REVERSIBILITY, not control flow):**
`pattern_match_relval` is RAW (`ty.nonsyncNamedEnv`): same-branch `NonSyncVal ⇒
Some (existT pc (nonsyncNamedEnv δ1 δ2))`, different branch ⇒ `None`. The
shallow + symbolic executors fast-path the uniquely-reversible patterns with raw
payloads and **no `secLeak`** (`pat_var`, `pat_unit`, statically-known-`K`
`pat_union` — the cmovznz4-critical one, recursing into its sub-pattern), and
keep `secLeak` as a conservative fallback for the rest (`pat_pair`/`pat_tuple`/
`pat_record` — a coinciding leaf makes `reverse` non-unique — and the genuinely
branching `pat_bool`/`pat_enum`/`pat_sum`/`pat_list`). This is symbolic
*incompleteness* on the fallback shapes, never unsoundness. Files touched:
`Syntax/Patterns.v`, `Shallow/Monads.v`, `Symbolic/Monads.v`,
`Refinement/Monads.v`, `MicroSail/ShallowExecutor.v`, `ShallowSoundness.v`.

**TCB rule also weakened (this session).** `Sep/Hoare.v` `rule_stm_pattern_match`
premise went from `⌜secLeak rv⌝` to `⌜is_Some (pattern_match_relval pat rv)⌝`,
and the continuation now carries the original `rv` + an equality hypothesis
(NOT a reversed payload — `reverse` is not a left inverse on the empty-context
`NonSyncVal v v` contamination case). New projection lemmas
`pattern_match_relval_projLeft/projRight` (`Patterns.v`) let
`iris_rule_stm_pattern_match` (`Iris/BinaryWeakestPre.v`) reduce the two
per-world matches; `sound_stm` (`Iris/BinaryInstance.v`) bridges the `Triple`
constructor's `->` to the rule's `bi_impl`. The one downstream TCB proof that
broke — `read_ram_sound` (`BlockVer/Spec.v`, whose `read_ram` contract uses
`asn.match_bool inv`) — was fixed by destructing the `pattern_match_relval`
result rather than `inv` itself. Full details in the
`project-pmr-canonicalization` memory note.

**METHOD X (DEFERRED, not needed) — uniform canonicalization.** The principled,
case-split-free alternative (canonicalize `pattern_match_relval` so `secLeak`
becomes *exact*). Doesn't localize: it cascades down to canonicalizing the
concrete RelVal algebra (`liftBinOp`/`liftUnOp`/`evalRel`/`inst_term`) — a
foundational trusted-base change, "scope with Dominique." The canon machinery
(`canonNamedEnv`, `canonRelVal`, `canonMatchResultRel`, `canonRelVal_idem`, …)
is left in `Patterns.v` as the base X would build on. Revisit only if we want to
remove the per-pattern case-split and make `secLeak` precise. Full X writeup:
git history around commit `95e2fd54` and the `project-pmr-canonicalization`
memory note.

**Gotchas found while proving `cmovznz4_noninterferent`:**
- `fuel` must exceed the raw instruction count, and it's not obvious by how
  much. Every existing example already had slack (jmp_fwd: 2 instrs/fuel 5,
  swap: 3/5, countdown_mem: 4/10); `cmovznz4` initially used `fuel = 29`
  (exactly the instruction count) and got stuck on a bare `False` VC goal
  deep in the proof that looked like a missing `secLeak` fact but wasn't --
  bumping to `fuel = 35` made it disappear entirely. No documented rule yet
  for how much slack is actually required; worth deriving one (or exposing a
  clearer error) instead of trial-and-error next time.
- `gen_contract_noninterferent`'s `HDataAddrs` proof obligation must case-split
  on *every* index in `mem_specs`, not just index 0 -- the pattern in
  `countdown_mem_noninterferent` (`intros [|i] ...`) only works because that
  example has exactly one memory entry. Copy-pasting it for a longer
  `mem_specs` list silently breaks (`discriminate` fails on real, in-bounds
  entries): destructure `i` through every concrete index instead, e.g.
  `intros [|[|[|...[|i]...]]] spec H; cbn in H; try (inversion H; subst;
  vm_compute; done); discriminate.` for N entries.

---

## Potential next tasks (not yet approved)

- Prove `jmp_bwd` (backward jump / loop) as a second CFGVer example.
- Continue with more "Breaking Bad"-style realistic examples now that
  `cmovznz4` established the pattern (register/memory reg_specs split into
  public/private, `asm_to_ast.py` for translation). Next ones will likely
  want real pointer arguments -- see the Priority 1 note above.
