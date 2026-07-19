---
name: cfgver
description: >
  Index/hub for the Katamaran RISC-V PMP CFG verifier (case_study/RiscvPmp/CFGVer/).
  Use when starting CFGVer work, when the request spans multiple layers, or when no
  focused sub-skill clearly matches. Routes to: cfgver-new-example (the recipe for
  verifying a new program), cfgver-executor (symbolic executor + VC),
  cfgver-refinement (concrete mirror + relational lemmas), cfgver-rsolve (the rsolve
  tactic), cfgver-soundness (the chain), cfgver-wp2 (semWP2 mechanics),
  cfgver-contracts (the contract record, hand-written contracts), cfgver-gen-contract
  (the generator user guide), cfgver-gen-contract-internals, cfgver-solve-vc (VC
  discharge), cfgver-endtoend (wiring user guide), cfgver-endtoend-internals, and
  cfgver-memory (data memory). If the request clearly matches one of those, use it
  directly instead. Katamaran-specific; generic Rocq/Coq → the rocq skill.
---

# CFGVer — reference hub

Entry point for the CFG verifier (`case_study/RiscvPmp/CFGVer/`). The reference is
split into focused skills so only the relevant one loads.

File layout (post 2026-07-17 split of the old monolithic `Examples.v`) and
compilation order: `Spec.v` → `Verifier.v` → {`Noninterference.v`, `Tables.v`}
→ `Contracts.v` → `GenContract.v` → `Adequacy.v` → `EndToEnd.v` →
`Example/{MvSwap,Jumps,Countdown,SetX2,Cmovznz4,Precompute}.v` (mutually independent) →
`Results.v` (aggregator: the concrete `*_noninterferent` theorems the merge
gate checks). `Noninterference.v` is the trusted statement layer (step
relations, `declare_*`, `noninterferent_strong`, spec types) and deliberately
does not depend on the verifier. When modifying a file, recompile it with
`keep_vo=True` before compiling files downstream of it.

| File | Contents | Matching skill |
|------|----------|----------------|
| `Noninterference.v` | trusted statement defs | cfgver-endtoend |
| `Tables.v` | reg aliases, `instrs_of_list`, `table_of_list`/`exits_of_*`, faith lemmas | cfgver-executor |
| `Contracts.v` | `CFGVerifierContract`, `minimal_pre`, `↦ᵣ`/`↦ₘ`, `solve_vc` | cfgver-contracts, cfgver-solve-vc |
| `GenContract.v` | `gen_contract(_param/_rel)`, `param_val`, concretize maps | cfgver-gen-contract(-internals) |
| `Adequacy.v` | `myWP2_loop`, `create_resources`, `semWP2_*`, `sound_*_myWP2` | cfgver-soundness, cfgver-wp2 |
| `EndToEnd.v` | `cfg_instrs_*`, `gen_implpre*`, `gen_contract_noninterferent*` | cfgver-endtoend(-internals), cfgver-memory |
| `Example/*.v` | per-program instrs+specs (statement-relevant), contract, `valid_*` VC | cfgver-new-example |
| `Results.v` | concrete end-to-end theorems | cfgver-endtoend |
For generic Rocq workflow (compile-first iteration, lemma search, proof repair)
use the **rocq** plugin skill; generic pitfalls live in **rocq-pitfalls**,
**bv-pitfalls**, **gmap-pitfalls**, **iris-proofmode**.

## Module map — which skill to read

| Skill | Covers | Read when |
|-------|--------|-----------|
| **cfgver-new-example** | the 6-step recipe: asm → contract → VC → end lemma → axiom check | verifying/adding a new program (most common task) |
| **cfgver-executor** | symbolic executor `sexec_cfg_addr`, term-table instruction store, `ptsto_instrs`, `scfg_verification_condition` | how the verifier decides/executes; VC construction; symbolic-pc errors |
| **cfgver-refinement** | concrete mirror `cexec_cfg_addr`, the mirroring discipline, `RefineCompat`, `rexec_cfg_addr` | reading/extending the relational layer; proving a new relational (ℛ⟦⟧) lemma |
| **cfgver-rsolve** | driving `rsolve`: debug workflow, instance template, divergence/OOM, manual bind pairing | an `rsolve` failure/hang/OOM; writing a `RefineCompat` instance |
| **cfgver-soundness** | the VC → `myWP2_loop` → leakage chain; `WP2_loop` vs `myWP2_loop` | understanding/extending the theorem architecture |
| **cfgver-wp2** | binary WP2 proof mechanics: `semWP2_unfold`, `stm_to_val`, `IVal`, `Result2` (library skill) | a semWP2/adequacy proof is stuck |
| **cfgver-contracts** | the `CFGVerifierContract` record, field semantics, Σ choice, hand-written contracts, `Valid`/`Debug` | what a contract IS; writing one without the generator |
| **cfgver-gen-contract** | the generator user guide: spec triples, `extra_exit_offs`, the 5 premises | declaring public/private/pinned registers or memory via `gen_contract` |
| **cfgver-gen-contract-internals** | `gen_reg_asn`/`gen_pre` builders, `gen_implpre` (library skill) | modifying/extending the generator machinery itself |
| **cfgver-solve-vc** | `vm_compute. solve_vc.`, residual patterns, `DebugCFGVerifierContract`, tight-fuel `False`, vm_compute divergence | discharging or debugging a VC |
| **cfgver-endtoend** | `cfg_instrs_endToEnd`, its call pattern, the `ImplPre` obligation | wiring a hand-written contract; debugging `ImplPre` |
| **cfgver-endtoend-internals** | proof bodies of the wiring lemmas, `_with_mem` proof patterns (library skill) | modifying/extending the wiring lemmas themselves |
| **cfgver-memory** | data-memory infra: `interp_mem_with_*`, `instrsAndDataMemory`, `_with_mem` variants | the program reads/writes data memory |

Dependency order: `executor ← refinement ← soundness ← contracts ← endtoend ← memory`,
with `gen-contract` on top of `contracts` and `new-example` orchestrating all of them.
Library skills (loaded from parents, rarely self-firing): `cfgver-rsolve`,
`cfgver-wp2`, `cfgver-gen-contract-internals`, `cfgver-endtoend-internals`.
References files (zero listing cost, reachable only via parent bodies):
`cfgver/references/registers.md` (two-world register machinery, from
cfgver-gen-contract-internals/cfgver-endtoend-internals); `cfgver/references/
asm-vocabulary.md` (AST constructor field order, register aliases, and the
backward-branch-immediate convention for hand-authored programs, from
cfgver-new-example).

## Importing CFGVer.Verifier downstream

```coq
(* At top level, after the main Require Import block: *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
```

Then use qualified names (`Katamaran.RiscvPmp.CFGVer.Verifier.foo`). Do NOT
`Require Import` — it clashes with BlockVer's identically-named definitions.
The other CFGVer files (`Noninterference`, `Tables`, `Contracts`, …) are safe
to plain `Require Import`.

> **BlockVer-contingent.** This idiom exists only because BlockVer shares names
> with CFGVer. Once BlockVer is consolidated away (see TODO.md cleanup items),
> switch the downstream files to a plain `Require Import` and delete this note.

## Example status (2026-07-19)

All CFGVer examples compile with **zero `Admitted`**, each with a
`valid_<prog>_cfg_contract` VC and a `<prog>_noninterferent` end lemma, axiom-clean
(`pure_decode` + `mmioenv` only): `swap`, `jumpIfZero`, `jmp_fwd`, `countdown`,
`countdown_mem`, `set_X2_to_42`, `cmovznz4`, `precompute`, `key_schedule_loop2`.

**All nine now have a parametric-base (∀ `init_addr`) headline**
(`<prog>_noninterferent_param`, via `gen_contract_param` for base-independent
specs or `gen_contract_rel` for base-relative ones — see **cfgver-gen-contract**);
every concrete `<prog>_noninterferent` is a free corollary of its `_param`
version (no per-address `vm_compute`). `cmovznz4` additionally has a genuinely
nonzero-base corollary (`cmovznz4_noninterferent_at_start`, base 256).
`countdown_mem`'s instruction stream was changed (`X0` → a dedicated `X2` holding
the base) to make its data word base-relative — see **cfgver-gen-contract**'s
"register choice for base-relative memory addressing" note; the backward branch
in `countdown`/`countdown_mem` (a previously untested case for the parametric-
base machinery) turned out to need zero special handling.
`valid_jmp_fwd` (BlockVer) stays `Admitted` — BlockVer cannot handle JAL;
intentional.

`precompute` (second "Breaking Bad" example, a 32-bit-word analogue of
Botan's real, currently-shipping `GHASH::key_schedule` masking step) is the
first example whose real (`uint64_t`) form does NOT verify with today's
executor: comparisons (`sltu`, from 64-bit-subtraction-on-32-bit borrow
detection) used as a pure VALUE on private data need `secLeak` on their
operand, which `solve_vc` has no way to discharge when the operand is
genuinely secret — see `TODO.md`'s "Botan CT::Mask / 64-bit-subtraction gap"
for the full trace and the open executor-extension task.

`key_schedule_loop2` (small-N=2 feasibility spike toward the full Botan
`GHASH::key_schedule` loop — the real function loops 128 times, wrapping
`precompute`'s masking step in a table-building backward branch; see
`TODO.md`) confirms that combination — secret arithmetic re-executed across
loop iterations, plus a per-iteration STORE to an advancing base-relative
table address, inside a genuine backward branch — needs no new `solve_vc`
machinery: the existing `countdown_mem`-style bridge and boilerplate `_param`
tail close it unchanged. Hand-authored (not `asm_to_ast.py`-translated, since
a real compiler would just fully unroll a 2-trip loop) — see
**cfgver-new-example**'s hand-authoring note and
`cfgver/references/asm-vocabulary.md` for the backward-branch-immediate
convention a first draft of this example got wrong. Bumping toward the real
trip count (128, in two nested 64-iteration passes per the actual source) is
a separate, not-yet-attempted step.
