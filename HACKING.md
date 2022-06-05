NOTE: The contents of this file is outdated.

Hacking
=======

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
