[![CircleCI](https://img.shields.io/circleci/build/github/katamaran-project/katamaran)](https://app.circleci.com/pipelines/github/katamaran-project/katamaran)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran?ref=badge_shield)

Katamaran
=========

Katamaran is a verification framework for instruction set architectures in the
Coq proof assistant. It provides the deeply-embedded language μSail, a variant
of the [Sail](https://github.com/rems-project/sail) language, for the
specification of instructions sets and provides furthermore facilities for the
specification of separation logic-based contracts and for semi-automatically
verifying these contracts. The goal is to formally specify and verify with
machine-checked proofs critical security guarantees of instruction sets. For
more information visit [our website](https://katamaran-project.github.io/).

Dependencies
------------

The development version of Katamaran has the following lower bounds:
```
coq            >= 8.14
coq-equations  >= 1.3
coq-iris       >= 3.5
coq-stdpp      >= 1.6
```
and has also been tested with coq 8.15 and iris 3.6.

Installation
------------

### Via opam (dev version)
Add our opam repository and install the latest development version from Github
with the following commands:
```
opam repo add katamaran https://github.com/katamaran-project/opam-repository.git
opam install coq-katamaran
```

### From github
```
git clone https://github.com/katamaran-project/katamaran.git
cd katamaran && make && make install
```

Using
-----

The easiest way to use the library for new developments is to adapt one of our
existing case studies, for example the
[MinimalCaps](https://github.com/katamaran-project/minimalcaps) machine.

Instantiating the library is done in multiple steps:

1. User-defined datatypes like enums, unions and records are declared fully in
Coq first. The library is then instantiated with the set of user-defined
types in a [`TypeKit`](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Types.v)
and with the one-level folding (construction) and unfolding (pattern-matching) of their
values in a [`ValueKit`](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Values.v).
2. With the types in place we can specify function signatures, lemma signatures
and the types of global registers in a [`TermKit`](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Machine.v).
3. Subsequently, we define a [`ProgramKit`](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Machine.v)
that contains a concrete definition of register and memory stores and
implementations of regular functions as μSail statements and of foreign
functions as Gallina relations.

This concludes the specification part. For the verification we need to continue
with the following steps:

4. The assertion language for contracts is instantiated by defining the signatures
of abstract predicates in an [`AssertionKit`](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Contracts.v).
5. Function contracts and lemma statements are defined in a [`ContractKit`](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Contracts.v).
6. At this point we can run the verification condition (VC) generator on all contracts
   [contracts](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Contracts.v)
   and proof that the VCs hold with all the Coq proof machinery such as Ltac.
7. The lemma statements and the contracts of foreign functions have to be verified directly in the [model](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Model.v). This can be done using the Iris Proof Mode for the [Iris model](https://github.com/katamaran-project/katamaran/blob/main/theories/Iris/Model.v) that is provided as part of the library.
8. The [soundness of the VC gen](https://github.com/katamaran-project/katamaran/blob/main/theories/Symbolic/Sound.v), the [soundness of the model](https://github.com/katamaran-project/katamaran/blob/main/theories/Iris/Model.v), and the [soundness of lemmas and foreign functions](https://github.com/katamaran-project/minimalcaps/blob/main/theories/Model.v) can then be combined in a full soundness statement.

### Debugging VC failures
In case a generated verification condition does not hold, the output of the symbolic 
executor can be instrumented with debug information to locate the cause. More information
about this is provided in [DEBUGGING.md](DEBUGGING.md).


License
-------
The Katamaran implementation is distributed under the 2-clause BSD license.

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran?ref=badge_large)
