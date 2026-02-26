open Block_verifier.Examples
open Examples
open Block_verifier.Sig.RiscvPmpSignature
open Block_verifier.SymbolicExecutor
open Block_verifier.Context
open Block_verifier.Datatypes
open Block_verifier.Sig
open Coq_asn
open SymProp

let rec string_of_symprop (s : SymProp.coq_SymProp) : string =
  match s with
  | Coq_angelic_binary (sp1, sp2) ->
      "Coq_angelic_binary (" ^ string_of_symprop sp1 ^ ", " ^ string_of_symprop sp2 ^ ")"
  | Coq_demonic_binary (sp1, sp2) ->
      "Coq_demonic_binary (" ^ string_of_symprop sp1 ^ ", " ^ string_of_symprop sp2 ^ ")"
  | Coq_error msg ->
      "Coq_error"
  | Coq_block ->
      "Coq_block"
  | Coq_assertk (formula, msg, sp') ->
      "Coq_assertk"
  | Coq_assumek (formula, sp') ->
      "Coq_assumek"
  | Coq_angelicv (binding, sp') ->
      "Coq_angelicv"
  | Coq_demonicv (binding, sp') ->
      "Coq_demonicv"
  | Coq_assert_vareq (lv, ty, binding_in, term, msg, sp') ->
      "Coq_assert_vareq"
  | Coq_assume_vareq (lv, ty, binding_in, term, sp') ->
      "Coq_assume_vareq"
  | Coq_pattern_match (ty, term, pattern, f) ->
      "Coq_pattern_match"
  | Coq_pattern_match_var (lv, ty, binding_in, pattern, f) ->
      "Coq_pattern_match_var"
  | Coq_debug (msg, sp') ->
      "Coq_debug"

let () =
  let triple = 
    { precondition = (Coq_formula Coq_formula_true);
      instrs = [];
      postcondition = (Coq_formula Coq_formula_true) }
  in
  let result = exec_VC Coq_ctx.Coq_nil triple in
  print_endline (string_of_symprop result)
