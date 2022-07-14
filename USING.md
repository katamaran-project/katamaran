# Using Katamaran

This file described how the framework can be used for a new development, i.e. a new instruction set architecture, and provides information on more general usage concerns like variable binding etc.
To understand the library structure, we recommend reading this file in conjunction with the linked list toy example that can be found in [test/LinkedList.v](test/LinkedList.v).
It instantiates the complete library, including a user-defined solver and the Iris model.
In addition, it shows the definition of many user-defined modules and the application of the library's module functors.

For new developments, you can also adapt one of the existing case studies, e.g. [MinimalCaps](https://github.com/katamaran-project/katamaran/tree/main/case_study/MinimalCaps) or [RISC-V PMP](https://github.com/katamaran-project/katamaran/tree/main/case_study/RiscvPmp).

## Variable binding
In the development, two kinds of variables are explicitly represented:
- *program variables* which are variables that stand for a mutable entry in a (local) program variable store, and which are used to represent function paramaters, and are used in program statements and expressions.
- *logic variables* which are variables that stand for a value and are used in contracts and symbolic propositions.

Both kinds of variables share a lot of code in the implementation, and both are represented using an intrinsically-typed de Bruijn representation, but tries to hide that fact for the user. Specifically, the user can write his programs and contracts using names (strings) instead and the library provides some typeclass-based machinery to perform name resolution and fill in de Bruijn indices automatically.
The de Bruijn indices are the ground source of truth for all purposes, but the names are also kept around as "decoration".
Logic variable names are also refreshed during computations ([`Definition fresh`](theories/Context.v)) and we try to preserve user-given names as much as possible, but we currently do not prove that logic variable names are sufficiently fresh and that no shadowing occurs.
Program variable names are allowed to use shadowing.

The file [Context.v](theories/Context.v) provides most of the variable binding-related definitions.
An (ordered) context [`Inductive Ctx`](theories/Context.v) is a list of bindings that represent a set of variables in scope.
This datatype is parameterized over a type of bindings `B`, and is thus a bit more general because it is also used in the representation of tuples and records, heap predicates etc..
For variable bindings the `B` parameter is always instantited to [`Record Binding`](theories/Context.v) that consists of a name and a type for a variable.
This instantiation is then used to represent program variable contexts ([`Notation PCtx`](theories/Base.v)) and logic variable contexts ([`Notation LCtx`](theories/Base.v)).

Variables are represented using context containment proofs ([`Class In (b : B) (Γ : Ctx B)`](theories/Context.v)) that consist of a witness (de Bruijn index) and a proof that the binding `(b : B)` is the binding at that position in the context `(Γ : Ctx B)`.
A hook into the typeclass instance resolution (in [`Module resolution`](theories/Context.v)) provides a computationally reflective procedure to resolve the last context entry with a given name and constructs the context containment witness ([`Fixpoint resolve_mk_in`](theories/Context.v)).
Such a technique was independently developed in the Koika language and described in: [Pit-Claudel and Bourgeat. "An experience report on writing usable DSLs in Coq." CoqPL’21](https://people.csail.mit.edu/bthom/coqpl21.pdf).

Environments ([`Inductive Env`](theories/Environment.v)) map variables to different kinds of data.
A program variable store is a mapping of program variables to values ([`Notation CStore`](theories/Base.v)) or to symbolic terms ([`Definition SStore`](theories/Syntax/Terms.v)).
Mappings of logic variables to values are valuations ([`Notation Valuation`](theories/Base.v)) and mappings of logic variables to symbolic terms (in another context) are substitutions ([`Definition Sub`](theories/Syntax/Terms.v)).

## Programs and specifications
The framework uses modules and module functors, i.e. modules parameterized by other modules.
To instantiate the library, the user has to define his own modules of certain signatures.
For some of these modules a default implementation is available, in case the use does not want to define custom functionality, e.g. custom datatypes etc.
We describe these user-provided modules on a high level and give pointers to the codebase where the signatures of the modules can be found with more detailed documentation for each one.

- The *base module* ([`Module Type Base`](theories/Base.v)) consists of the definitions of user-specified types, i.e. unions, records and enums, for the development, and the names and types of registers of the machine.
  These are defined as ordinary Coq types and the library is provided with one-level folding (construction) and unfolding (pattern-matching) of their values.
  This is a prerequisite to use the syntax of statements ([`Inductive Stm`](theories/Syntax/Statements.v)) and expressions ([`Inductive Exp`](theories/Syntax/Expressions.v)) to define functions.
- With the types in place, the *program module* ([`Module Type Program`](theories/Program.v)) contains the declaration (type signatures) and definition of the μSail and foreign functions, and the definition of the underlying type of memory, to which the foreign functions have access.
  The program module also includes the type signature declaration of lemmas, that can be used in lemma ghost statements.
- The *program logic signature module* ([`Module Type ProgramLogicSignature`](theories/Specification.v)) declares user-defined abstract pure and special predicates.
  These are the necessary parameters for the assertion language ([`Inductive Assertion`](theories/Syntax/Assertions.v)) used in pre- and postconditions.
- The *specification module* ([`Module Type Specification`](theories/Specification.v)) contains the definitions of contracts for the functions of the program.
- Finally, the *solver module* ([`Module Type SolverKit`](theories/Specification.v)) provides user-defined heuristics for solving pure proof obligations.

The base and program modules together contain the necessary details to instantiate μSail's operational semantics ([`Module MakeSemantics`](theories/Semantics.v)).
The signature, specification and solver modules together instantiate the shallow ([`Module MakeShallowExecutor`](theories/Shallow/Executor.v)) and symbolic ([`Module MakeExecutor`](theories/Symbolic/Executor.v)) verification condition generators, the axiomatic program logic ([`Module Type ProgramLogicOn`](theories/Sep/Hoare.v)) and the shallow ([`Module Soundness`](theories/Shallow/Soundness.v)) and symbolic ([`Module Soundness`](theories/Symbolic/Soundness.v)) soundness lemmas.


## Iris program logic model

The Iris model ([`Module Type IrisInstance`](theories/Iris/Model.v)) for the axiomatic program logic is instantiated similarly by defining modules.

- The *iris parameters* ([`Module Type IrisParameters`](theories/Iris/Model.v)) define the ghost state for memory.
  Together with the program module this is sufficient to define the operational model.
- The *iris predicates* ([`Module Type IrisPredicates`](theories/Iris/Model.v)) contains the user-defined interpretation of the abstract spatial predicates as Iris propositions.

The lemma statements and the contracts of foreign functions have to be verified directly in the iris instance, e.g. by using Iris Proof Mode.
The soundness of the lemmas, the soundness of the foreign functions and validity of the verification conditions can be combined into full soundness ([`Lemma sound`](theories/Iris/Model.v)) and adequacy ([`Lemma adequacy`](theories/Iris/Model.v)) statements.


## Debugging verification failures

There are essentially two types of failed verifications, either when consuming a spatial chunk, or when an asserted pure proposition does not hold.
Sometimes, i.e. when using the angelic version of chunk consumption (`chunk_angelic`), the former may be disguised as the latter.
To investigate failures of contract verification the output of the symbolic executor can be instrumented with debug information to locate the cause.
This debug information is already provided by default for asserts and consumes in the verification condition, and you can request additional debug nodes to be created by using the `stm_debug` ghost statement in your programs or the `asn_debug` ghost assertion in your contracts.
The verification condition will always resemble the control flow structure of your program, i.e. it has the structure of a symbolic execution tree rather than being a random formula.
The debug information will always provide you with the state (store, heap) and path constraints at that point in the execution.

Note: we previously described how to *step* through the symbolic executor by selectively evaluating functions or by making functions opaque.
This is not practical because the interactive handling in proof mode of the intermediate states is very slow.
The only viable solution is to fully execute (via `compute`, `vm_compute` or `native_compute`) the verification condition generation and inspect the resulting tree.

### Failed chunk consumption

A failed consumption of a heap chunk will provide you with a value of
[`Record DebugConsumeChunk`](theories/Symbolic/Executor.v):

```
error
 ("p"∷ptr. "q"∷ty.sum ptr ty.unit. "xs"∷ty.list ptr. "ys"∷
  ty.list ptr. "xs.1"∷ty.sum ptr ty.unit. "x"∷ptr. "p.1"∷ptr.
  {| debug_consume_chunk_program_context := ["p"∷ptr; "q"∷ty.sum ptr ty.unit];
     debug_consume_chunk_pathcondition := []%list;
     debug_consume_chunk_localstore := [env].["p"∷ptr ↦ "p"].["q"∷ty.sum ptr ty.unit ↦ "q"];
     debug_consume_chunk_heap := [ chunk_user ptstolist ["q"; "ys"];
                                   chunk_user ptstolist [term_inl "p"; "xs"]
                                 ]%list;
     debug_consume_chunk_chunk := chunk_user ptstocons ["p"; "x"; "xs.1"]
  |})
```

The record value is wrapped in an `error` node of the symbolic propositions with
some number of quantified variables. The interesting parts of the record are the
contents of the heap `debug_consume_chunk_heap` and the chunk to be consumed
`debug_consume_chunk_chunk`. In the above example, the user-defined predicate
`chunk_user ptstocons ["p"; "x"; "xs.1"]` is to be consumed, but the heap does
not contain any chunk of the `ptstocons` predicate.

### Debug statements

To request the creation of debug nodes in the execution tree you can use the
`stm_debug s` statement. For every execution branch that executes this statement
a value of the [`Record DebugStm`](theories/Symbolic/Executor.v) is produced.

```
{| debug_stm_program_context :=
     ["xs"∷list int; "y"∷int; "ys"∷list int; "sml"∷prod (prod int int) int;
     "sm"∷prod int int; "l"∷int; "s"∷int; "m"∷int;
     "m'"∷int];
   debug_stm_statement_type := prod (prod int int) int;
   debug_stm_statement :=
     stm_exp
       (exp_binop bop.pair
          (exp_binop bop.pair (exp_binop bop.plus (exp_var "s") (exp_var "y"))
             (exp_var "m'")) (exp_binop bop.plus (exp_var "l") (exp_int 1)));
   debug_stm_pathcondition :=
     (("m" >= "y") :: (0 <= "l") :: ("s" <= "m" * "l") :: nil)%list;
   debug_stm_localstore := [env]
     .["xs"∷list int ↦ term_binop bop.cons "y" "ys"].[
     "y"∷int ↦ "y"].["ys"∷list int ↦ "ys"]
     .["sml"∷prod (prod int int) int ↦ term_binop bop.pair
                                         (term_binop bop.pair "s" "m") "l"]
     .["sm"∷prod int int ↦ term_binop bop.pair "s" "m"].[
     "l"∷int ↦ "l"].["s"∷int ↦ "s"].["m"∷int ↦ "m"].[
     "m'"∷int ↦ "m"];
   debug_stm_heap := nil
|}
```

It includes information about the wrapped statement `s` that is replicated in
the `debug_stm_statement` field, and the state of the execution
(`debug_stm_heap`, `debug_stm_localstore`) and the path constraints at the point
of execution `debug_stm_pathcondition`.
