# ICFP 2022 Artifact

Name: Verified Symbolic Execution with Kripke Specification Monads (and no Meta-Programming)

## Artifact Instructions

The artifact mainly consists of Katamaran, our mechanized separation logic
verifier for the Sail language, the MinimalCaps case study and the
summaxlen/linked-list toy examples presented in the paper. The papers aims to
provide a generic methodology for the construction of mechanized verifiers,
which we extracted from Katamaran, but Katamaran contains extensions,
optimizations and makes other design choices which are orthogonal to the story
of the paper.

Some of the bigger differences include:
- Katamaran only implements a shallow and symbolic executor for separation logic
  (Section 4), not for predicate logic based program logics such as Section 2
  and 3 suggest.
- The code is parameterized by user-defined enum, record and union types and
  also contains support for more types than discussed in the paper, e.g. tuples
  and bit-vectors.
- The syntax of programs is stratified in to statements and expressions.
- The complete codebase uses an intrinsically-typed representation for all
  pieces of data such as input programs, variable stores, heaps, substitutions,
  valuations etc.

Nevertheless, our implementation provides evidence for the main claims of the
paper and we tried to make the presentation in the code and in the paper
consistent. We documented differences when necessary either as part of this
readme or as comments in the code.

### Requirements

To compile our code and verify our claims, we assume that reviewers either have
Coq installed on their own system or are using the provided Debian QEMU image,
which is derived from the base image. The code has the following dependencies
with the specified lower bounds:
```
coq            >= 8.14
coq-equations  >= 1.3
coq-iris       >= 3.5
coq-stdpp      >= 1.6
```

but also works with the most recent releases, i.e. Coq 8.15.1 and Iris 3.6. For
benchmarking the running time, you will need the `ts` command of the
[moreutils](https://joeyh.name/code/moreutils/) package that is available as
part of most Linux distributions. For the QEMU image, generic install and run
instructions are provided at the end of this file. To check our claims, we
require you to run make commands, inspect the output and also read the
statements of key definitions and lemmas. All of the commands in this file
should be run from the main `katamaran` folder, which is
`/home/artifact/katamaran` in the VM image.

### Claimed badges
For our artifact we claim the available, functional and reusable badges. We lay
out how we support the claim of each badge in its own section.

## Available badge
We will make the artifact available in a long-term, publicly accessible archive
upon acceptance of the paper for which we will use Zenodo as recommended by the
evaluation guidelines. Furthermore, we will also cut out a release on GitHub
and submit it to Coq's opam archive.

## Functional badge

To verify our functional claims, we ask you to browse the code and compare it to
the definitions of the paper, and to check that our proofs are assumption free,
i.e. they don't use any axioms or rely on unproven facts. For browsing the code
and finding referenced definitions, we recommend that you open the files in a
code editor on your machine outside of the QEMU VM.

The assumptions of a definition can be printed with the Coq command [`Print
Assumptions`](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions).
The expected output of this command is `Closed under the global context` for
assumption free definitions. We have already added these commands to the code
for key lemmas and will point you to the location in the code, and how to see
the result of that command in the compilation output.

You can compile the codebase using `make` in the main folder. Furthermore, there
are certain make targets which will selectively force recompilation of some of
the files. We recommend that you run these once and redirect the output to a
text file
```
make summaxlen > summaxlen.txt
make linkedlist > linkedlist.txt
make minimalcaps > minimalcaps.txt
```
that you can browse later, e.g. via `less summaxlen.txt`.


### Functional Claim 1: Shallow verification condition generation
As demonstrated in Section 2, shallow VCGs can be defined by implementing
monadic interpreters in shallow specification monads. Most of the definition can
be found in the `theories/Shallow/Monads.v` file. Of interest are the
following definitions:

- The pure predicate transformer monad `CPureSpec` corresponds to the
  definition 𝑊pure from Section 2.
- The symbolic heap and store predicate transformer monad `CHeapSpec`
  corresponds to 𝑊heap from Section 4.
- The names of the definitions in `Monads.v` for the primitives from Fig 2.
  are `angelic`, `demonic`, `angelic_binary`, `demonic_binary`, `assert_formula`
  and `assume_formula` which are defined for both `CPureSpec` and `CHeapSpec`.
- The propositional implementation of control flow from Fig 3. are the
  `angelic_pattern_match` and `demonic_pattern_match` functions.

The shallow executor, which uses the shallow specification monads, can be
found in the `theories/MicroSail/Executor.v` file:

- The main interpreter function that recurses over program statements is
  implemented in `cexec` and `exec_aux`.
- The main verification condition generation is implemented `exec_contract`,
  `vcgen` and `ValidContract`.

### Functional Claim 2: Shallow VCG soundness
The proof of the soundness of the shallow VCG can be found in the file
`theories/MicroSail/ShallowSoundness.v`. Lemma 2.1 of the paper is verified by `Lemma
exec_aux_sound` and `Lemma sound_cexec` in the code, with the statement given by
`Definition SoundExec`. Corollary 2.2 of the paper corresponds to `Lemma
vcgen_sound` and `Lemma shallow_vcgen_soundness`.

The definition of the underlying program logic, and what a valid contract
corresponds to in terms of the program logic, can be found in
`theories/Sep/Hoare.v`.

Printing the assumptions of `shallow_vcgen_soundness` in
`theories/MicroSail/ShallowSoundness.v` would print all the module parameters as
assumptions, which are considered user inputs by the code. Instead we added a
`Print Assumptions shallow_vcgen_soundness` command to `test/SumMaxLen.v` where
the modules are instantiated for one of the toy examples. Search for
`shallow_vcgen_soundness` at the end of `summaxlen.txt`.

### Functional Claim 3: Symbolic verification condition generation
Section 3 discusses the generation of symbolic VCs via symbolic specification
monads. Symbolic propositions 𝕊 are defined by `Inductive SymProp` in file
`theories/Symbolic/Propositions.v`. The definition of the worlds (`Record
World`) and accessibility (`Inductive Acc`) of the Kripke frame reside in
`theories/Symbolic/Worlds.v`. This file also defines the notation used for
Kripke-indexed types and basic constructions like the box operator `Definition
Box`, the S4 axioms, and a type class for persistent types `Class Persistent`
and some of its instances.

The symbolic specification monads, found in `theories/Symbolic/Monads.v`,
come again in two flavours: `SPureSpec` for
𝑆pure from Section 3 and `SHeapSpec` for 𝑆ℎ𝑒𝑎𝑝 from Section 4 of the paper. You
will find the symbolic definition of a demonic pattern match in
`Definition demonic_pattern_match`. The `theories/MicroSail/SymbolicExecutor.v`
file contains the executor function `sexec` and `exec_aux`, which are
the symbolic equivalents to the shallow one you already encountered, and the
overall VCG is defined by `Definition vcgen` which is wrapped and combined with
the postprocessing phase in `Definition ValidContract`.

### Functional Claim 4: Symbolic VCG soundness
The reduction of the soundness of the symbolic VCG to soundness of the shallow
VCG is implemented in file `theories/MicroSail/RefineExecutor.v`. The definition of
the logical relation from Fig. 18 of the paper is implemented as `Class Refine`
and its instances. The file contains an explanation why it's implemented using
typeclasses. The example relatedness proof of the paper is implemented in `Lemma
refine_demonic` for which we provide the goal state after key steps in comments.

The key relatedness lemmas in the file are the ones for symbolically executing
program statements `Lemma refine_exec_aux` and `Lemma refine_exec`, and the one
for the complete verification condition generator `Lemma refine_vcgen` from
which the main soundness lemma `Lemma symbolic_vcgen_soundness` is derived. This
implements the proof of Lemma 5.1 from the paper. You can again find the output
of the `Print Assumption` command for `symbolic_vcgen_soundness` at the end of
`summaxlen.txt`

### Functional Claim 5: Evaluation of the implementation
This claim concerns the evaluation of Katamaran in Section 6 with the summaxlen
and linked-lists toy examples, which you can find in `test/SumMaxLen.v` and
`test/LinkedList.v`, and the MinimalCaps case study which is located in the
`case_study/MinimalCaps` folder. You will find that the source files randomly
open goals that are aborted. Their purpose is to print information on the command
line, so that you do not have to step through the file yourself.

For summaxlen you will find the definition of the function body `Definition
fun_summaxlen` and of the contract `Definition sep_contract_summaxlen` and the
proof of the verification condition `Lemma valid_contract_summaxlen`. This is a
non-trivial verification condition that is solved by a small proof script. In
the output file `summaxlen.txt` you can find the generated shallow and symbolic
verification conditions which correspond to the ones given in Section 3 of the
paper. Furthermore, there is an alternative definition of summaxlen with a debug
ghost statement for which you can also find an output of the complete
verification condition in `summaxlen.txt`, and an output that only shows the
second debug node. This reflects the case that is discussed at the end of
Section 3.7 in the paper. The adequacy statement of Section 6.1 for summaxlen
is the `Corollary summaxlen_adequacy`.

For the linked-lists examples the verification condition become trivial after
simplification and therefore all the `valid_contract_*` lemmas are solved by the
`reflexivity` tactic. In the `ExampleModel` submodule, you can find the
verification of the soundness of the foreign functions (`mkcons`, etc.) and of
the lemmas (`open_cons` etc.) provided to the symbolic executor. These proofs
are performed in Iris Proof Mode. As discussed in Section 4.1, an omission of a
lemma ghost statement (see `Definition fun_appendloop_broken`) results in a
verification failure for which the `linkedlist.txt` files contains the generated
output.

For the MinimalCaps case study, all verification conditions are solved
simultaneously in `Lemma ValidContracts` in
`case_study/MinimalCaps/Contracts/Verification.v`, which also became trivial after
simplification.

The branching statistics of Table. 1 can be found in the `summaxlen.txt` and
`linkedlist.txt` files. The details of counting the nodes can be found in the
`Module Statistics` in both `theories/MicroSail/ShallowExecutor.v` and
`theories/MicroSail/SymbolicExecutor.v`. For MinimalCaps, computing the nodes of the
large combined shallow VC (~96k lines) is intractable in Ltac, therefore an
alternative command line-based solution is provided. It prints the entire VC to
standard out and counts the number of textual occurrences of the leaf
propositions that correspond to finished and pruned execution paths. You can
find the results in `mininmalcaps.txt`.

The running times shown in Table. 1, and of the MinimalCaps case study, can be
produced with `make timings` for which the `moreutils` packages needs to be
installed. It measures, on the command line, the time between outputs just
before and after the proof of a verification condition.

For the evaluation of the third party we used the following sources:

- Bedrock

  The implementation of the framework is available on
  [Github](https://github.com/mit-plv/bedrock/tree/e3ff3c2cba9976ac4351caaabb4bf7278bb0dcbd),
  and more specifically the example code we used for the benchmark can be found in
  [`Bedrock/Examples/SinglyLinkedList.v`](https://github.com/mit-plv/bedrock/blob/e3ff3c2cba9976ac4351caaabb4bf7278bb0dcbd/Bedrock/Examples/SinglyLinkedList.v).
  For timing the individual functions, we redefined the Bedrock module
  [`sllM`](https://github.com/mit-plv/bedrock/blob/e3ff3c2cba9976ac4351caaabb4bf7278bb0dcbd/Bedrock/Examples/SinglyLinkedList.v#L101-L154)
  to only contain one of the functions and timed the lemma containing the verification of the specification
  [`sllMOk`](https://github.com/mit-plv/bedrock/blob/e3ff3c2cba9976ac4351caaabb4bf7278bb0dcbd/Bedrock/Examples/SinglyLinkedList.v#L172-L176).

  The Lemmas row in Table 1 of the paper contains the time to check the
  [`nil_fwd`, `nil_bwd`, `cons_fwd`, and `cons_bwd`](https://github.com/mit-plv/bedrock/blob/master/Bedrock/Examples/SinglyLinkedList.v#L40-L61)
  theorems.
- Verified Software Toolchain

  The implementation of VST can be found on [Github](https://github.com/PrincetonUniversity/VST/tree/b88da7af666299725050ee8ec411cbedeb85dc94).
  The [`Lemma body_append` in `progs64/verif_append2.v`](https://github.com/PrincetonUniversity/VST/blob/b88da7af666299725050ee8ec411cbedeb85dc94/progs64/verif_append2.v#L88-L145) is the verification of the `append` function that we timed, and the [`Lemma body_reverse` in `progs64/verif_reverse2.v`](https://github.com/PrincetonUniversity/VST/blob/b88da7af666299725050ee8ec411cbedeb85dc94/progs64/verif_reverse2.v#L105-L157) the verification of the `reverse` function.
- Separation Logic Foundations

  Our benchmarks are based on [version 1.1 of the Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu/slf-1.1/slf.tgz).
  The development of linked-list is in the Representation Predicates chapter in `Repr.v`.
  We took the timings of the `triple_append` and `triple_mcopy` lemmas which are provided and measured the time of our own solution to the `triple_mlength` exercise:

  ```
  Lemma triple_mlength : forall L p,
    triple (mlength p)
      (MList L p)
      (fun r => \[r = val_int (length L)] \* (MList L p)).
  Proof using.
    intros. gen p. induction_wf IH: list_sub L.
    xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
    { intros ->. subst. xval. xsimpl*. xchange* <- MList_nil. }
    { intros x q L' ->. xapp. xapp. xapp.
      xchange <- MList_cons. xsimpl*.
      now rewrite length_cons, plus_nat_eq_plus_int, Z.add_comm.
    }
  Qed.
  ```
  For the Lemmas row in Table 1 we timed `Lemma MList_if`.


## Reusable badge

We see two reuse scenarios for our development.

1. In the implementation of similar verifiers for languages other than Sail. We
   see the contents of our paper as a generic methodology to build such
   verifiers using Kripke-indexed specification monads, and most of the
   definitions in the paper and our implementation of it are not specific to any
   language and can in theory be directly reused.

2. As a verification tool for security properties of Sail models of instruction
   sets, which is the indended use case for which Katamaran is being developed.
   The framework is not tied to the MinimalCaps code nor to the capability
   safety property. The parameterization over a user-provided pure and spatial
   background theory, included a user-provided model of memory, makes the tool
   more widely usable. We are in fact developping a second case study, that
   proves (for a subset of RISC-V) a security property for its optional Physical
   Memory Protection feature
   https://github.com/katamaran-project/katamaran/tree/main/case_study/RiscvPmp

As per the guidelines, we tried to make the build process as easy as possible
and made sure that it compiles with the up-do-date dependencies. An earlier
version of Katamaran was already released in Coq's opam archive to facilitate
reuse through packaging and we intend to publish a new release. We tried to make
make definitions, notations, meta-variables etc. as consistent as possible to
the paper.

## Detailed mappings

In this section we give detailed links of the definition of the paper to the
corresponding definition in the codebase.

| Paper                                | File                             | Definition                                                           | Comment                                                                       |
|--------------------------------------|----------------------------------|----------------------------------------------------------------------|-------------------------------------------------------------------------------|
| Fig. 1 exp                           | theories/Syntax/Expression.v     | `Inductive Exp`                                                      |                                                                               |
| Fig. 1 binop                         | theories/Syntax/BinOps.v         | `Inductive BinOp`                                                    |                                                                               |
| Fig. 1 program                       | theories/Syntax/FunDef.v         | `Parameter FunDef`                                                   | Represented as a mapping from function names to their body.                   |
| Fig. 1 pvar                          | theories/Syntax/Variables.v      | `PVar`                                                               |                                                                               |
| Fig. 1 val                           | theories/Syntax/TypeDecl.v       | `Fixpoint Val`                                                       |                                                                               |
| Fig. 1 store                         | theories/Base.v                  | `Notation CStore`                                                    |                                                                               |
| Section 2 Wpure                      | theories/Shallow/Monads.v      | `Definition CPureSpec`                                              |                                                                               |
| Section 2 Wstore                     | theories/Shallow/Monads.v      | `Definition CHeapSpec`                                              | Additionally includes a separation logic heap.                                |
| Fig. 2 ret                           | theories/Shallow/Monads.v      | `Definition CPureSpec.pure`                                         |                                                                               |
| Fig. 2 angelic                       | theories/Shallow/Monads.v      | `Definition CPureSpec.angelic`                                      |                                                                               |
| Fig. 2 demonic                       | theories/Shallow/Monads.v      | `Definition CPureSpec.demonic`                                      |                                                                               |
| Fig. 2 ⊕                             | theories/Shallow/Monads.v      | `Definition CPureSpec.angelic_binary`                               |                                                                               |
| Fig. 2 ⊗                             | theories/Shallow/Monads.v      | `Definition CPureSpec.demonic_binary`                               |                                                                               |
| Fig. 2 assert                        | theories/Shallow/Monads.v      | `Definition CPureSpec.assert_formula`                               |                                                                               |
| Fig. 2 assume                        | theories/Shallow/Monads.v      | `Definition CPureSpec.assume_formula`                               |                                                                               |
| Fig. 2 push, pop                     | theories/MicroSail/ShallowExecutor.v      | `Definition CStoreSpec.pushpop`                                      | Combines push and pop.                                                        |
| Fig. 3 matchbool⊗                    | theories/Shallow/Monads.v      | `Definition CHeapSpec.demonic_pattern_match`                           |                                                                               |
| Fig. 3 matchbool⊕                    | theories/Shallow/Monads.v      | `Definition CHeapSpec.angelic_pattern_match`                           |                                                                               |
| Fig. 3 matchsum⊗                     | theories/Shallow/Monads.v      | `Definition CHeapSpec.demonic_pattern_match`                            |                                                                               |
| Fig. 3+4 exec                        | theories/MicroSail/ShallowExecutor.v      | `Definition CStoreSpec.exec_aux`                                     |                                                                               |
| Fig. 4 assign                        | theories/MicroSail/ShallowExecutor.v      | `Definition CStoreSpec.assign`                                       |                                                                               |
| Fig. 5 Val                           | theories/Syntax/Terms.v          | `Inductive Term`                                                     |                                                                               |
| Fig. 5 LCtx                          | theories/Base.v                  | `Notation LCtx`                                                      |                                                                               |
| Fig. 5 Sub                           | theories/Syntax/Terms.v          | `Definition Sub`                                                     |                                                                               |
| Fig. 5 Valuation                     | theories/Base.v                  | `Notation Valuation`                                                 |                                                                               |
| Fig. 6 summaxlen                     | test/SumMaxLen.v                 | `Definition fun_summaxlen`                                           |                                                                               |
| Section 2.3 contracts tuple          | theories/Syntax/Assertions.v     | `Record SepContract`                                                 |                                                                               |
| Section 2.3 summaxlen contract       | test/SumMaxLen.v                 | `Definition sep_contract_summaxlen`                                  |                                                                               |
| Fig. 7 exec (call ..)                | theories/MicroSail/ShallowExecutor.v      | `Definition exec_aux` + `Definition cexec_call`                   |                                                                               |
| Section 2.4 vc                       | theories/MicroSail/ShallowExecutor.v      | `Definition vcgen`                                                   |                                                                               |
| Fig. 8 rule #1                       | theories/Sep/Hoare.v             | `rule_stm_if`           **TODO**                                             |                                                                               |
| Fig. 8 rule #2                       | theories/Sep/Hoare.v             | `rule_stm_call_forwards` + `Inductive CTriple` **TODO**                       |                                                                               |
| Fig. 8 rule #3                       | theories/Sep/Hoare.v             | `rule_consequence`                                                   |                                                                               |
| Fig. 8 rule #4                       | theories/Sep/Hoare.v             | `rule_exist`                                                         |                                                                               |
| Fig. 8 rule #5                       | theories/Sep/Hoare.v             | `rule_stm_assign_backwards`        **TODO**                                  |                                                                               |
| Lemma 2.1                            | theories/MicroSail/ShallowSoundness.v     | `Lemma exec_aux_sound`                                               |                                                                               |
| Corollary 2.2                        | theories/MicroSail/ShallowSoundness.v     | `Lemma vcgen_sound`                                                  |                                                                               |
| Fig. 9 Formulas 𝔽                    | theories/Syntax/Formulas.v       | `Inductive Formula`                                                  |                                                                               |
| Fig. 9 Pathcond ℂ                    | theories/Syntax/Formulas.v       | `Definition PathCondition`                                           |                                                                               |
| Fig. 9 Symbolic Propositions 𝕊       | theories/Symbolic/Propositions.v | `Inductive SymProp`                                                  |                                                                               |
| Section 3.2 entailments ⊢            | theories/Syntax/Formulas.v       | `Definition entails` + `Definition entails_formula` **TODO**                 |                                                                               |
| Section 3.2 triangular substitutions | theories/Symbolic/Worlds.v       | `Inductive Tri`                                                      |                                                                               |
| Fig. 10 solver                       | theories/Symbolic/Worlds.v       | `Definition Solver` + `Definition SolverSpec`                        |                                                                               |
| Fig. 11 World                        | theories/Symbolic/Worlds.v       | `Record World`                                                       | This also defines a coercion from World to LCtx.                              |
| Fig. 11 accessibility ⊒              | theories/Symbolic/Worlds.v       | `Inductive Acc`                                                      |                                                                               |
| Fig. 11 Valid `⊢ A`                  | theories/Symbolic/Worlds.v       | `Definition Valid`                                                   |                                                                               |
| Fig. 11 Implication `A → B`          | theories/Symbolic/Worlds.v       | `Definition Impl`                                                    |                                                                               |
| Fig. 11 Box `□A`                     | theories/Symbolic/Worlds.v       | `Definition Box`                                                     |                                                                               |
| Fig. 11 Axiom T                      | theories/Symbolic/Worlds.v       | `Definition T`                                                       |                                                                               |
| Fig. 11 Axiom 4                      | theories/Symbolic/Worlds.v       | `Definition four`                                                    |                                                                               |
| Fig. 11 Axiom K                      | theories/Symbolic/Worlds.v       | `Definition K`                                                       |                                                                               |
| Fig. 11 Persistent type              | theories/Symbolic/Worlds.v       | `Class Persistent`                                                   |                                                                               |
| Fig. 12 Spure                        | theories/Symbolic/Monads.v     | `Definition SPureSpec`                                              |                                                                               |
| Fig. 12 Sstore                       | theories/Symbolic/Monads.v     | `Definition SHeapSpec`                                              | Additionally includes a separation logic heap.                                |
| Fig. 12 Ret                          | theories/Symbolic/Monads.v     | `Definition SPureSpec.pure`                                         |                                                                               |
| Fig. 12 >>=                          | theories/Symbolic/Monads.v     | `Definition SPureSpec.bind`                                         |                                                                               |
| Fig. 12 Assume                       | theories/Symbolic/Monads.v     | `Definition SPureSpec.assume_formula`                              |                                                                               |
| Fig. 12 Demonic                      | theories/Symbolic/Monads.v     | `Definition SPureSpec.demonic`                                      |                                                                               |
| Section 3.4 Matchsum⊗                | theories/Symbolic/Monads.v     | `Definition SPureSpec.demonic_pattern_match`                           |                                                                               |
| Section 3.4 VC                       | theories/MicroSail/SymbolicExecutor.v     | `Definition vcgen`                           |                                                                               |
| Section 3.6 Postprocessing           | theories/Symbolic/Propositions.v | `Module Postprocessing`                                              |                                                                               |
| Section 3.7 summaxlen symbolic VC    | test/SumMaxLen.v                 | `Lemma valid_contract_summaxlen`                                     | It's the calculated proposition.                                              |
| Fig. 13 summaxlen shallow VC         | test/SumMaxLen.v                 | `Lemma valid_contract_summaxlen_shallow`                             | It's the calculated proposition.                                              |
| Fig. 14 chunk                        | theories/Syntax/Chunks.v         | `Inductive SCChunk`                                                  |                                                                               |
| Fig. 14 Chunk                        | theories/Syntax/Chunks.v         | `Inductive GChunk`                                                    |                                                                               |
| Fig. 14 heap                         | theories/Syntax/Chunks.v         | `Inductive SCHeap`                                                   |                                                                               |
| Fig. 14 Heap                         | theories/Syntax/Chunks.v         | `Inductive SHeap`                                                    |                                                                               |
| Section 4 Wheap                      | theories/Shallow/Monads.v      | `Definition CHeapSpec`                                              |                                                                               |
| Section 4 Sheap                      | theories/Symbolic/Monads.v     | `Definition SHeapSpec`                                              |                                                                               |
| Fig. 15 producechunk                 | theories/Shallow/Monads.v      | `Definition produce_chunk`                                           |                                                                               |
| Fig. 15 consumechunk                 | theories/Shallow/Monads.v      | `Definition produce_chunk`                                           |                                                                               |
| Section 4.1 ptr                      | test/LinkedList.v                | `Notation ptr`                                                       |                                                                               |
| Section 4.1 llist                    | test/LinkedList.v                | `Notation llist`                                                     |                                                                               |
| Fig. 16 mkcons contract              | test/LinkedList.v                | `Definition sep_contract_mkcons`                                     |                                                                               |
| Fig. 16 fst contract                 | test/LinkedList.v                | `Definition sep_contract_fst`                                        |                                                                               |
| Fig. 16 setfst contract              | test/LinkedList.v                | `Definition sep_contract_setfst` **TODO**                                     |                                                                               |
| Fig. 16 snd contract                 | test/LinkedList.v                | `Definition sep_contract_snd`                                        |                                                                               |
| Fig. 16 setsnd contract              | test/LinkedList.v                | `Definition sep_contract_setsnd`                                     |                                                                               |
| Section 4.1 mem                      | test/LinkedList.v                | `Definition Memory`                                                  |                                                                               |
| Section 4.1 ↦ₚ                       | test/LinkedList.v                | `ptstocons` of `Inductive Predicate`                                 |                                                                               |
| Section 4.1 ↦ₗ                       | test/LinkedList.v                | `ptstolist` of `Inductive Predicate`                                 |                                                                               |
| Section 4.1 ↦ₗ def                   | test/LinkedList.v                | `Fixpoint ptstolist_interp`                                          | This is defined as an Iris proposition.                                       |
| Fig. 17 open\_nil                    | test/LinkedList.v                | `Definition sep_lemma_open_nil`                                      |                                                                               |
| Fig. 17 close\_nil                   | test/LinkedList.v                | `Definition sep_lemma_close_nil`                                     |                                                                               |
| Fig. 17 open\_cons                   | test/LinkedList.v                | `Definition sep_lemma_open_cons`                                     |                                                                               |
| Fig. 17 close\_cons                  | test/LinkedList.v                | `Definition sep_lemma_close_cons`                                    |                                                                               |
| Fig. 18 append                       | test/LinkedList.v                | `Definition fun_append` + `Definition sep_contract_append`           |                                                                               |
| Fig. 18 appendloop                   | test/LinkedList.v                | `Definition fun_appendloop` + `Definition sep_contract_appendloop`   |                                                                               |
| Fig. 18 appendloop                   | test/LinkedList.v                | `Definition sep_lemma_close_cons`                                    |                                                                               |
| Lemma 5.1                            | theories/MicroSail/RefineExecutor.v    | `Lemma symbolic_vcgen_soundness`                                     |                                                                               |
| Section 5 Valuation : World → Type   | theories/Symbolic/Executor.v     | `Record WValuation` **TODO**                                                  | The record is unused and the fields are always passed separately in the code. |
| Fig 19. R≲                           | theories/Symbolic/Soundness.v    | `Class Refine` **TODO**                                                      |                                                                               |
| Fig 19. R≲[Val,val]                  | theories/Symbolic/Soundness.v    | `Instance RefineInst`  **TODO**                                              |                                                                               |
| Fig 19. R≲[𝕊,ℙ]                      | theories/Symbolic/Soundness.v    | `Instance RefineProp`          **TODO**                                      |                                                                               |
| Fig 19. R≲[□A,a]                     | theories/Symbolic/Soundness.v    | `Instance RefineBox`                   **TODO**                              |                                                                               |
| Fig 19. R≲[A→B,a→b]                  | theories/Symbolic/Soundness.v    | `Instance RefineImpl`                          **TODO**                      |                                                                               |
| Lemma 5.1 proof VC,vc ∈ R≲           | theories/MicroSail/RefineExecutor.v    | `Lemma refine_vcgen`                                                 |                                                                               |
| Lemma 5.1 proof Exec,exec ∈ R≲       | theories/MicroSail/RefineExecutor.v    | `Lemma refine_exec_aux`                                              |                                                                               |
| Lemma 5.1 proof >>=,>>= ∈ R≲         | theories/MicroSail/RefineExecutor.v    | `Lemma refine_bind`                                                  |                                                                               |
| Lemma 5.1 proof Assume,assume ∈ R≲   | theories/Refinement/Monads.v    | `Lemma refine_assume_formula`                                        |                                                                               |
| Section 6.1 step relation            | theories/Smallstep/Step.v        | `Inductive Step`                                                     |                                                                               |
| Lemma 6.1                            | test/SumMaxLen.v                 | `Lemma adequacy_pure`                                                |                                                                               |
| Fig. 21 store function               | case_study/MinimalCaps/Machine.v | `Definition fun_exec_sd`                                             |                                                                               |
| Fig. 21 store contract               | case_study/MinimalCaps/Contracts/Definitions.v | `Definition sep_contract_exec_sd` + `Definition mach_inv_contract` |                                                                               |

