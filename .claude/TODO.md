# Next session briefing

CLAUDE.md and the `/katamaran` skill are auto-loaded — read them for full context.
This file tracks the approved task list and current starting point.

---

## Current state

All CFGVer noninterference proofs are one-liners via `gen_contract_noninterferent`.
All contracts are defined using `gen_contract`. See commit history for details.

First realistic example (from the "Breaking Bad" paper discussion) is done:
`cmovznz4` (HACL*'s constant-time conditional move), hand-translated from
`clang -O2 -march=rv32i` output into a `list AST`, proved noninterferent
end-to-end (`cmovznz4_noninterferent` in `CFGVer/Examples.v`). `cin` and
scratch registers private, `x`/`y` data public, `r` private, addresses
hardcoded right after the code (see Priority 1 below re: why). A script at
`case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` mechanically translates
RV32I assembly (as pasted from Compiler Explorer) into the `list AST` Coq
literal, tagging each entry with its source line for auditability — use it
for future examples instead of hand-transcribing.

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

**ROOT-CAUSED: pattern matching demands full `secLeak` on the scrutinee,
which for LOAD forces the loaded value to be public.**

*Symptom.* `cmovznz4_noninterferent` needs `x`/`y` public (see
`cmovznz4_mem_specs`). A/B-isolated to: a single `LOAD` with the loaded
memory word PRIVATE fails; with it PUBLIC it succeeds -- independent of the
destination register, the address, or any `RTYPE`. So specifically "the
value read from memory by LOAD must be `secLeak`."

*Mechanism (full chain, confirmed by reading the code):*
1. Every `LOAD` runs `extend_value` (Machine.v:528), which does
   `match: value in union (memory_op_result bytes)`, where `value` is the
   loaded word wrapped `KMemValue cmem_val`.
2. The symbolic executor lowers `stm_pattern_match` (SymbolicExecutor.v:475)
   to `demonic_pattern_match`.
3. `demonic_pattern_match'` (Monads.v:551) opens with
   `assertSecLeak … t` on the scrutinee `t`, i.e.
   `assert_formula (formula_secLeak t)` (Monads.v:436). (The message string
   "Pattern matched term is not secLeak" at SymbolicExecutor.v:461 is the
   same check surfaced in `stm_assertk`.)
4. `formula_secLeak` on a union reduces (Solver.v:2232,
   `simplify_secLeak (term_union U K tl) => dlist_secLeak tl`) to `secLeak`
   of the *payload*. So `secLeak (KMemValue cmem_val)` becomes
   `secLeak cmem_val` -- exactly the residual `secLeak (bv 32)` goal.
5. It is baked into the *shallow spec too*, not just the optimizer:
   ShallowExecutor.v:251 `demonic_pattern_match pat v <-> secLeak v /\
   demonic_pattern_match' pat v`. So the requirement lives at every layer
   (shallow spec -> symbolic mirror -> refinement -> erasure), which is why
   re-enabling the commented-out constructor fast-path in Monads.v alone
   would NOT help -- it would break refinement against this shallow spec.

*Why it is over-conservative.* `secLeak` = fully synchronized (`SyncVal`,
same value in both worlds). But a pattern match only needs both worlds to
select the *same case* (same constructor); the payload variables it binds
are `RelVal` and may legitimately be `NonSyncVal` (differ per world). The
semantics already allow this: `semWP2_pattern_match` (BinaryWeakestPre.v:770)
computes `pc1`, `pc2` for the two worlds *independently* and requires the
continuation for the actual `(pc1,pc2)`; the symbolic executor collapses to
one `pc`, so soundness only needs `pc1 = pc2` (case-sync), NOT full value
sync. Confirms this is a tooling limitation, not a property of the program:
real CT crypto LOADs secret values (HACL* `cmovznz4` selects between secret
bignums/points in the Montgomery ladder; `Hacl.Spec.Bignum.Base.mask_select`
has a generic `limb_t` signature -- see the "Breaking Bad" paper).

*Fix plan: weaken the pattern-match precondition from `secLeak v`
(full sync) to `secLeakCase pat v` (both worlds select the same
`PatternCase`).* In dependency order:
  1. `Syntax/Formulas.v`: add concrete `secLeakCase pat rv` (both
     projections of `rv` hit the same `PatternCase`) and a symbolic
     `formula_secLeakCase pat t` constructor + subst/inst/occurs_check
     boilerplate.
  2. `MicroSail/ShallowExecutor.v`: change `demonic/angelic_pattern_match`
     (+ the `_unfold` lemmas) to use `secLeakCase` instead of `secLeak`.
  3. `MicroSail/ShallowSoundness.v`: re-prove pattern-match soundness w.r.t.
     `semWP2_pattern_match` under the weaker precondition. **This is the
     crux/risk** -- but the WP already handles `pc1`/`pc2` independently, so
     case-sync (`pc1=pc2`) is exactly what collapsing to one `pc` needs; the
     bound payload becomes `NonSyncVal (world1 payload) (world2 payload)`.
  4. `Symbolic/Monads.v`: `assertSecLeak` -> `assertSecLeakCase` in
     `demonic/angelic_pattern_match'`.
  5. `Symbolic/Solver.v`: simplify `formula_secLeakCase pat (term_union K tl)`
     -> `True` (constructor statically known). This is what discharges LOAD
     automatically; also handle other term shapes conservatively.
  6. `Symbolic/UnifLogic.v`: update `refine_*_pattern_match*` + add a
     `RefineCompat` instance for the new formula so `rsolve` still closes.
  7. `Symbolic/Propositions.v`: handle the new formula in the Erasure
     (`erase_formula`/`inst_eformula`) so `safeE`/`postprocess`/
     `VerificationConditionWithErasure` (CFGVer's `Valid_CFG_VC`) still work.

*Blast radius.* ~6-7 core theory files, in the metatheory shared by ALL
case studies (RiscvPmp *and* MinimalCaps); every case study must still
compile. The risk is concentrated in the ShallowSoundness re-proof (3) and
in threading the new formula through Solver (5) + Erasure (7) without
breaking existing proofs. Definitely a "scope with Dominique" change.

*Recommended de-risking spike before committing to the full proof:* wire
through steps 1,2,4,5,6,7 but leave the ShallowSoundness lemma (3) `Admitted`,
then check that (a) `cmovznz4` with `x`/`y` PRIVATE now closes and (b) all
existing case studies still compile. If both hold, the fix is "correct in
shape" and only the honest soundness re-proof remains.

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
