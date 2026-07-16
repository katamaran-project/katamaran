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
- **[approved 2026-07-16, own session] Remove dead code from `CFGVer/Verifier.v`:**
  `semTripleCFG`, `instrAligned`, and the dead WP2-based `sound_*` lemmas (the
  skills already describe them as "pending cleanup"). Grep for usages first,
  then recompile `Verifier.v` (keep_vo) + full `Examples.v` to confirm.
- Consolidate everything in CFGVer, so BlockVer can be deleted.
- Rename everything in CFGVer to remove mentions to BlockVer.
- Remove `sound_sblock_verification_condition` in favor of
  `sound_sblock_verification_condition_myWP2_loop`.
- `Examples.v` is too large; split into: logic lemmas, examples, memory helpers.

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
