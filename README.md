Deeply embedded MicroSail in Coq
================================

[Sail](https://github.com/rems-project/sail) is a domain-specific language for
specification of instruction set architectures (ISAs) of processors. The
accompanying Sail tool type-checks Sail code and has multiple back ends for both
executable emulators and theorem provers. All theorem prover back ends output a
shallow embedding of desugared Sail.

This repository contains the development of MicroSail, a deep embedding of Sail
in Coq which we hope to develop into a full Sail backend. It requires Coq 8.8 or
later.

Motivation
----------
The deep embedding allows us to develop different proof methods and automation
techniques. Specifically we develop a weakest (liberal) precondition (WP)
calculus for the embedded language. The WP allows us to perform axiomatic
verification of specifications, which we nevertheless prove sound with respect
to an operational model.

We believe that our approach yields easier proof goals and is more amenable to
proof automation than the current back end's reasoning against a computational
monad. Furthermore, direct access to the syntax and specifically the types of a
specification enables us to carry out logical-relation based poofs like for
instance recent work on reasoning about capability safety:
[1](https://ieeexplore.ieee.org/abstract/document/7467352/)
[2](https://dl.acm.org/citation.cfm?id=3133913)
[3](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_17).

Road map
--------

We aim to derive the full pipeline, including a Sail backend, for a bare bones
version of the language first and then to iteratively scale this up. We envision
that the Sail tool can desugar some language features using rewrites and for
other unsupported features we will simply bail out. The different *parts* of the
pipeline are:

1. A (small-step) operational semantics of the embedded language including a
   type-safety proof.
2. A weakest-precondition based VC generator that is proven sound with respect
   to the operational semantics.
3. A Sail backend that compiles desugared Sail to our deeply embedded language.
4. A tactic library to automatically discharge VCs potentially with help from
   SMT solvers via [SMTCoq](https://smtcoq.github.io/).
5. Some example programs and proofs which we want to scale up to [RISC-V
   cheri_lite](https://github.com/rems-project/sail-riscv/tree/cheri_lite).

### Iteration 1
- Support int, bool, bit, unit, strings, pairs, lists, (and sums) as base types.
- Multi-parameter functions.
- Only local mutable variables as side-effectul feature.

### Iteration 2
- More type constructors: tuples, enums, unions and records. Restrict unions
  and records to kind Set.
- Global register state-

### Later iteration
- Refinement types: Add bool and nat kinded type variables and potentially also
  type kinded variables. Otherwise rely on monomorphisation. It's still unclear
  if nat and bool kinded variables can be added intrinsically or if we go back
  to define them extrinsically or if we not at them at all and compile
  refinement types to refinement contracts of functions.
- More type constructors: vectors, reals, bitfields and higher-kinded type
  constructors.
- More effects: non-local control flow via return, exceptions,
  non-determinism.


### Unplanned features
- We have no plans on adding polymorphism on vector order and always rely on
  monomorphisation.
- Bidirectional mappings. Rely on desugaring.
- Rich lvalue assignment. We only allow assignments on registers and mutable
  variables.
- Bi-directional typing or type inference. We always expect type-signatures for
  every function, let-bound variable and some other places
- Scattered definitions for unions, enums and functions.

Comparison
----------

### MiniSail
MiniSail is another development to study a core calculus of Sail. There are
notable differences:
- MiniSail uses bi-directional typing like Sail. We are not interested in the
  study of type inference for Sail and hence implement a common typing relation.
- Our stratification into values, expressions and statements differs from
  MiniSail. MiniSail enforces ANF while MicroSail does not. Our development
  includes:
  + Literals are values which are not variables. We do not have values as a
    separate syntactic sort. We use the term "literals" to not clash with
    existing Sail/MiniSail terminology.
  + Expressions are control-flow free and side-effect free terms. However we
    allow read access of mutable variables inside expressions and might allow
    reading from registers in the future. Anything that has unobservable effects
    during evaluation goes in here.
  + Statements contain the remainder.
  
License
-------
The MicroSail implementation is distributed under the 2-clause BSD license.
