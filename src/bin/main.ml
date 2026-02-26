open Block_verifier.Examples
open Examples
open Block_verifier.Sig.RiscvPmpSignature
open Block_verifier.SymbolicExecutor
open Block_verifier.Context
open Block_verifier.Datatypes
open Block_verifier.Sig
open Coq_asn

let () =
  let triple = 
    { precondition = (Coq_formula Coq_formula_true);
      instrs = Coq_nil;
      postcondition = (Coq_formula Coq_formula_true) }
  in
  let string_of_symprop s = "Test" (* stubbed the definition for now... *) in
  let result = exec_VC Coq_ctx.Coq_nil triple in
  print_endline (string_of_symprop result)
