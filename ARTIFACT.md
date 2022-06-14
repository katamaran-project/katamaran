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
- The pre- and postconditions in contracts are written in a deeply-embedded
  assertion language represented (`Inductive Assertion`) that was omitted in the
  paper for space reasons.

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
our how we support the claim of each badge in its own section.

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
be found in the `theories/Shallow/Executor.v` file. Of interest are the
following definitions:

- The pure predicate transformer monad `CPureSpecM` corresponds to the
  definition 𝑊pure from Section 2.
- The symbolic heap and store predicate transformer monad `CHeapSpecM`
  corresponds to 𝑊heap from Section 4.
- The names of the definitions in `Executor.v` for the primitives from Fig 2.
  are `angelic`, `demonic`, `angelic_binary`, `demonic_binary`, `assert_formula`
  and `assume_formula` which are defined for both `CPureSpecM` and `CHeapSpecM`.
- The propositional implementation of control flow from Fig 3. are the
  `angelic_match_*` and `demonic_match_*` functions.
- The main interpreter function that recurses over program statements is
  implemented in `exec` and `exec_aux`.
- The main verification condition generation is implemented `exec_contract`,
  `vcgen` and `ValidContract`.

### Functional Claim 2: Shallow VCG soundness
The proof of the soundness of the shallow VCG can be found in the file
`theories/Shallow/Soundness.v`. Lemma 2.1 of the paper is verified by `Lemma
exec_aux_sound` and `Lemma exec_sound` in the code, with the statement given by
`Definition SoundExec`. Corollary 2.2 of the paper corresponds to `Lemma
vcgen_sound` and `Lemma shallow_vcgen_soundness`.

The definition of the underlying program logic, and what a valid contract
corresponds to in terms of the program logic, can be found in
`theories/Sep/Hoare.v`.

Printing the assumptions of `shallow_vcgen_soundness` in
`theories/Shallow/Soundness.v` would print all the module parameters as
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

The symbolic specification monads come again in two flavours: `SPureSpecM` for
𝑆pure from Section 3 and `SHeapSpecM` for 𝑆ℎ𝑒𝑎𝑝 from Section 4 of the paper. You
will find the symbolic definition of a demonic pattern match on sum types in
`Definition demonic_match_sum'`. The executor function `exec` and `exec_aux` are
the symbolic equivalents to the shallow one you already encountered, and the
overall VCG is defined by `Definition vcgen` which is wrapped and combined with
the postprocessing phase in `Definition ValidContract`.

### Functional Claim 4: Symbolic VCG soundness
The reduction of the soundness of the symbolic VCG to soundness of the shallow
VCG is implemented in file `theories/Symbolic/Soundness.v`. The definition of
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
simultaneously in `Lemma valid_contracts` in
`case_study/MinimalCaps/Contracts.v`, which also became trivial after
simplification.

The branching statistics of Table. 1 can be found in the `summaxlen.txt` and
`linkedlist.txt` files. The details of counting the nodes can be found in the
`Module Statistics` in both `theories/Shallow/Executor.v` and
`theories/Symbolic/Executor.v`. For MinimalCaps, computing the nodes of the
large combined shallow VC (~96k lines) is intractable in Ltac, therefore an
alternative command line-based solution is provided. You can find the results in
`mininmalcaps.txt`.

The running times shown in Table. 1, and of the MinimalCaps case study, can be
produced with `make timings` for which the `moreutils` packages needs to be
installed. It measures, on the command line, the time between outputs just
before and after the proof of a verification condition.

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
   (CAREFUL, NOT ANONYMIZED).

As per the guidelines, we tried to make the build process as easy as possible
and made sure that it compiles with the up-do-date dependencies. An earlier
version of Katamaran was already released in Coq's opam archive to facilitate
reuse through packaging and we intend to publish a new release. We tried to make
make definitions, notations, meta-variables etc. as consistent as possible to
the paper.
