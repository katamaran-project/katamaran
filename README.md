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

The easiest way to use the library for new developments is to adapt one of our existing case studies, for example the [MinimalCaps](case_study/MinimalCaps) machine.
The basic usage structure of Katamaran is described in the [HACKING.md](HACKING.md) file.

### Debugging VC failures
In case a generated verification condition does not hold, the output of the symbolic
executor can be instrumented with debug information to locate the cause. More information
about this is provided in [DEBUGGING.md](DEBUGGING.md).


License
-------
The Katamaran implementation is distributed under the 2-clause BSD license.

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran?ref=badge_large)
