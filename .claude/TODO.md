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
