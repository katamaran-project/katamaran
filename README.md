Deeply embedded MicroSail in Coq
================================

[Sail](https://github.com/rems-project/sail) is a domain-specific language for
specification of instruction set architectures (ISAs) of processors. The
accompanying Sail tool type-checks Sail code and has multiple backends for both
executable emulators and theorem provers. All theorem prover backends output a
shallow embedding of desugared Sail.

This repository contains the development of MicroSail, a deep embedding of Sail
in Coq which we hope to develop into a full Sail backend.

License
=======
The MicroSail implementation is distributed under the 2-clause BSD license.
