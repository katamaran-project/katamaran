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
| `Symbolic/Solver.v` | formula/path-condition simplification (`solver_generic`, `combined_solver`) — see **secret-data-walls** for its `secLeak` logic |
| `Syntax/Predicates.v` | abstract separation-logic predicate vocabulary (`PurePredicateKit`/`HeapPredicateKit`) a case study instantiates |
| `MicroSail/SymbolicExecutor.v` | the generic symbolic executor for `Stm` — see **core-executor-internals** for the choice-combinator mechanics |
| `Symbolic/Propositions.v` | the `SymProp` verification-condition language and its postprocessing (`prune`/`solve_evars`/`solve_uvars`) |
| `Syntax/TypeDecl.v` | core `Ty`/`Val`/`RelVal` type-denotation machinery — see **relval-model** for `SyncVal`/`NonSyncVal` semantics |
| `MicroSail/RefineExecutor.v` | refinement/soundness proof connecting the symbolic executor to the shallow one (`symbolic_vcgen_soundness`) |
