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
coq            >= 8.19
coq-equations  >= 1.3
coq-iris       >= 4.3
coq-stdpp      >= 1.11
```
and has also been tested with coq 8.20.

### Using opam

An easy way to setup your system is to create a fresh opam switch, pin the Coq and Iris versions and install equations (stdpp will be installed as a dependency of Iris):
```
opam switch create katamaran ocaml-base-compiler.4.14.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.19.2
opam pin add coq-iris 4.3.0
opam install coq-equations
```

### Using nix

The repository contains a flake.nix file that defines development shells that install all dependencies. To use it, you need to have [nix](https://nixos.org/download.html) installed. Then, you can enter a development shell with the following command:
```
nix develop
```
This will install all dependencies and open a shell with them available. Additionally it will set the COQPATH environment variable to include the dependencies. You can then compile the project within that shell or launch your favorite editor from within it.

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

The basic usage structure of Katamaran is described in the [USING.md](USING.md) file.
The easiest and recommended way to use the library for new developments is to adapt one of our existing case studies, for example the [MinimalCaps](case_study/MinimalCaps) machine.
Some more information about the internal structure of the library is provided in the [HACKING.md](HACKING.md) file.

License
-------
The Katamaran implementation is distributed under the 2-clause BSD license.

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran?ref=badge_large)
