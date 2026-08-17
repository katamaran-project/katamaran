# Core framework — file map

One-line orientation for the most structurally central files in `theories/`
(ranked by how many other files import them), so an agent can tell what a
file is for without opening it. Each file itself carries a fuller header
comment (right after its copyright block) — read that when the one-liner
here isn't enough; only open the actual code once you need the details the
header doesn't cover. Where an existing skill already documents a file's
mechanics in depth, that's noted — read the skill for that, not this index.

Layering, roughly bottom-up: `Prelude` → `Bitvector`/`Context`/`Environment`
→ `Syntax/TypeDecl` → `Base` → `Program`/`Specification`/`Signature` →
`Semantics` → `Sep/Hoare` → `Iris/Base` → `Iris/Instance` →
`MicroSail/{Shallow,Symbolic,Refine}Executor` → `Symbolic/{Worlds,
Propositions,Solver}`. A case study (e.g. `case_study/RiscvPmp/`)
instantiates the module types at each layer.

| File | What it's for |
|---|---|
| `Bitvector.v` | the `bv n` sized-bitvector type and its operation library (arithmetic, logical, shifts, slicing) |
| `Notations.v` | precedence-level cheatsheet for the framework's custom notations |
| `Prelude.v` | foundational, language-agnostic utilities (`EqDec`/`Finite`/`Countable`, `IsTrue`, the `option` weakest-precondition monad, shared notation scopes) |
| `Specification.v` | module-type interface for supplying a case study's contracts (`CEnv`/`CEnvEx`/`LEnv`) |
| `Semantics.v` | packages the generic small-step operational semantics of the statement language |
| `Base.v` | module-type interface fixing a case study's object language and machine model (`Types <+ RegDeclKit <+ OperationalModel <+ BaseMixin`) |
| `Environment.v` | heterogeneous, context-indexed environments (`Env`) — `CStore`/`Valuation`/`SStore`/`Sub` are all instances |
| `Sep/Hoare.v` | the language-generic axiomatic Hoare-triple layer (`Triple`/`CTriple`/`LTriple`), proof-theoretic only |
| `Iris/Instance.v` | generic Iris model layer proving `Sep/Hoare.v`'s triples sound against `semWP` |
| `Program.v` | module type supplying a case study's function declarations/definitions + the call-graph/termination machinery |
| `Iris/Base.v` | the `IrisBase` module type — abstract ghost-state/resource requirements + `semWP`/`semTWP` |
| `Signature.v` | combined module type (`PredicateKit <+ WorldsMixin <+ SolverKit <+ SignatureMixin`) a case study instantiates once |
| `Context.v` | the `Ctx B` snoc-list context structure (typed variable contexts, e.g. `LCtx`) |
| `MicroSail/ShallowExecutor.v` | the concrete, directly-executable reference semantics (correctness baseline for the symbolic executor) |
| `Symbolic/Worlds.v` | the `World` record and logic-variable-world extension operators underlying symbolic execution; also declares the `SolverKit` module type |
| `Symbolic/Solver.v` | formula/path-condition simplification (`solver_generic`, `combined_solver`) — see **secret-data-walls** for its `secLeak` logic, and **core-executor-internals** for both how an `assert` is discharged and the recipe for adding a new rule (read it BEFORE the first edit; see the box below) |
| `Syntax/Predicates.v` | abstract separation-logic predicate vocabulary (`PurePredicateKit`/`HeapPredicateKit`) a case study instantiates |
| `MicroSail/SymbolicExecutor.v` | the generic symbolic executor for `Stm` — see **core-executor-internals** for the choice-combinator mechanics |
| `Symbolic/Propositions.v` | the `SymProp` verification-condition language and its postprocessing (`prune`/`solve_evars`/`solve_uvars`) |
| `Syntax/TypeDecl.v` | core `Ty`/`Val`/`RelVal` type-denotation machinery — see **relval-model** for `SyncVal`/`NonSyncVal` semantics |
| `MicroSail/RefineExecutor.v` | refinement/soundness proof connecting the symbolic executor to the shallow one (`symbolic_vcgen_soundness`) |

---

## Editing `Symbolic/Solver.v` — four facts that bound every iteration

Read **core-executor-internals** ("Adding a NEW solver rule") before the first
edit; these four are here because they apply to *any* change to that file.

1. **`rocq_compile_file` cannot build it.** It drops `_CoqProject`'s
   `-arg "-w all"`, under which the pre-existing `#[export] Notation` at
   ~`Solver.v:2230` is a hard error pointing at code you did not touch. Use
   `make -f Makefile.coq theories/Symbolic/Solver.vo` — budget **~5m45s**, and
   it invalidates every downstream `.vo` (i.e. the whole case study).
2. **Its definitions cannot be checked interactively.** They sit in
   `Module Import GenericSolver` inside `Module Type GenericSolverOn`, so that
   inner `Import` does not escape: from a position-mode `rocq_start` even
   *pre-existing* siblings are unreachable, and past ~line 2400 the replay
   exceeds the 300 s cap anyway. Externally the names are
   `RiscvPmpSignature.GenericSolver.<name>`.
3. **So prove the semantics in preamble mode first.** `Bitvector` and
   `Syntax.TypeDecl` load standalone, and `ty.liftBinOpRV`/`liftUnOpRV` are what
   `bop.evalRel`/`uop.evalRel` reduce to — the real RelVal argument restates
   there in ~100 ms. `RiscvPmp.Sig` does **not** load in a preamble.
4. **A wrong rule does not fail loudly.** A rule that discharges to `empty`
   claims a formula holds; only `./scripts/gate.sh`'s `Print Assumptions` pass
   catches it, via the end theorems. Run the gate at **`GATE_JOBS=1`** on a
   ≤16 GB box — the default `-j3` runs three ~3 GB `coqc` processes at once.

---

## Compile-cost floor — measured, and there is no hot spot

Every `coqc` process in a case study pays ~1.96 GB of peak RSS before any of its
own content. Bisected 2026-07-27 (bare-`Require` probes; peak RSS, which is
deterministic — wall times on a memory-pressured box are not, see the
**rocq-timeout-triage** skill):

| layer | GB | |
|---|---|---|
| `coqc` startup | 0.06 | |
| stdpp + Iris (via a case study's `Base`) | 0.37 | 19% |
| `Base` itself | 0.18 | |
| `Syntax/Statements.v` (the `Stm`/`Exp` AST) | 0.10 | |
| `Program.v` (adds `Syntax/FunDecl`, `Syntax/FunDef`) | 0.20 | |
| `Semantics.v` | 0.17 | |
| `Syntax/Chunks.v` + `Syntax/Predicates.v` | **0.41** | **21%** |
| `Symbolic/Worlds.v` + `Syntax/Assertions.v` | 0.09 | |
| `Symbolic/UnifLogic` + `Propositions` + `Shallow/Monads` | 0.15 | |
| `Symbolic/Solver` + `Symbolic/Monads` + `Refinement/Monads` | 0.20 | |

**Ten layers at 0.1–0.4 GB each — no single pathology.** That is why no
restructuring has ever reduced it; there is breadth, not a hot spot. The largest
single entry, and the only lead not yet probed, is `Chunks`+`Predicates` (0.41).

Things already measured and found NOT to be the cause — don't re-derive these:

- **A case study's own content is ~free.** A copy of `RiscvPmp/Machine.v` with all
  58 `fun_*` `Stm` ASTs deleted and `FunDef` stubbed to `stm_fail` measures
  *identically* to the real thing; so does a file holding only `Machine.v`'s
  header with zero content. The cost is the `Require` closure.
- **`.vo` size does not predict RAM.** `Machine.vo` is 0.77 MB and `Base.vo` is
  10.6 MB, yet `Machine`'s layer costs 2.7x `Base`'s. Ratios like "600x
  expansion" are an attribution error — RAM tracks the transitive closure.
- **`Equations` and stdpp `decidable`/`finite` are free** (+0.00 GB each).
- **OCaml GC tuning is a dead end.** `OCAMLRUNPARAM=o=80` cuts a small probe
  1.96 → 1.77 GB but a real heavy file only 3.26 → 3.22 (1.2%), at +33% time.
  It is live heap, not GC headroom.
- **Splitting `Symbolic/Solver` out of `Signature.v`** buys 0.20 GB, not the
  ~0.9 GB once hoped — see the FRAMEWORK entry in `TODOS.txt`.
