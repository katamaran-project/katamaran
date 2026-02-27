# Extracting the RISCV Block Verifier

This subdirectory contains the necessary OCaml scaffolding code (including dune project) for a minimal extraction of the Block Verifier.

Steps to run the OCaml code (after building the Rocq project including `theories/Extraction.v`):


1. Apply the following patches to `lib/Base1.ml`:
    1. Remove the `MMIOENV` type declaration
    2. Remove the `mmioenv` Parameter (not realized)
    3. Remove both `fun_read_mmio` and `fun_write_mmio`, as they rely on the `mmioenv` parameter.
2. Add the following (erased) type definitions in `lib/SymbolicExecutor.ml` and `lib/SymbolicExecutor.mli` above the `MakeExecutor` functor definition:
```ml
type coq_Pred = __
type 'a coq_CPureSpec = __
type 'a coq_CHeapSpec = __
```
3. In `src/`, run `dune build`.
4. In `src/`, run `dune exec bin/main.exe --profile release`

Note: The `--profile release` flag ensures compilation (and execution) continues through warnings and errors.

The program should terminate, printing a prettified SymProp to stdout:

```
forall (?? : <bitvector>), forall (?? : <record>), assert { <val>::int <= (neg[unsigned[<var>::<bitvector><bitvector>]int] + <val>::int)} /\ Coq_block
```

This SymProp represents the output of Katamaran's RISCV-PMP Block Verifier, invoked on a simple Hoare triple, defined in `bin/main.ml`:

```ml
  let bv_zero = Coq_bv.of_N (S O) N0 in
  let triple = 
    { precondition = (Coq_formula Coq_formula_true);
      instrs = [
        ITYPE (bv_zero, bv_zero, bv_zero, RISCV_ADDI)
      ];
      postcondition = (Coq_formula Coq_formula_true) }
  in
  let result = exec_VC Coq_ctx.Coq_nil triple in
  print_endline (string_of_symprop result)
```

## TODO

- Inline the builtin types to better match the OCaml equivalent types
- Inline the bitvector, and weird Zarith stuff somehow
- Inline operations on the builtins like Nat.add
- Create a patch to remove mmio-related code automatically
- Add a make target for extraction
- derive a show instance for symprop and friends automatically (generate an s-expr)
- discuss erasure of LVars: right now they are computationally irrelevant, but in order to print them I need to pattern match on them.
