# Extracting the RISCV Block Verifier

This subdirectory contains the necessary OCaml scaffolding code (including dune project) for a minimal (not yet successful) extraction of the Block Verifier.

Steps to run the OCaml code (after building the Rocq project including `theories/Extraction.v`):

1. In `src/`, run `dune build`.
2. In `src/`, run `dune exec main.exe`

Step 2. currently fails because of issues with extracted definitions from the prover.


