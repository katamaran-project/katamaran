open Block_verifier.Examples
open Examples
open Block_verifier.Sig.RiscvPmpSignature
open Block_verifier.SymbolicExecutor
open Block_verifier.Context
open Block_verifier.Datatypes
open Block_verifier.Sig
open Block_verifier.Bitvector
open Block_verifier.BinNums
open Block_verifier.Variables
open Block_verifier.TypeDecl
open Block_verifier.BinOps
open Block_verifier.UnOps
open Block_verifier.Base1
open Coq_asn
open SymProp

let rec string_of_ty (ty : Coq_ty.coq_Ty) : string =
  match ty with
  | Coq_int -> "int"
  | Coq_bool -> "bool"
  | Coq_string -> "string"
  | Coq_list t -> "list " ^ string_of_ty t
  | Coq_prod (t1, t2) -> "(" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  | Coq_sum (t1, t2) -> "(" ^ string_of_ty t1 ^ " + " ^ string_of_ty t2 ^ ")"
  | Coq_unit -> "unit"
  | Coq_enum enumi -> "<enum>"
  | Coq_bvec n -> "<bitvector>" 
  | Coq_tuple ctx -> "<tuple>"
  | Coq_union unioni -> "<union>"
  | Coq_record record -> "<record>"

let rec string_of_lvar (n : coq_LVar) : string = "??" (* TODO: LVars are erased, how can I display them? *)

let rec string_of_binding (b : (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding) : string =
  let {Binding.name = n; Binding.coq_type = t} = b in
  "(" ^ string_of_lvar n ^ " : " ^ string_of_ty t ^ ")"

let rec string_of_relop (r : Coq_bop.coq_RelOp) : string =
  match r with
  | Coq_eq t -> "=_" ^ string_of_ty t
  | Coq_neq t -> "<>_" ^ string_of_ty t
  | Coq_le -> "<="
  | Coq_lt -> "<"
  | Coq_bvsle n -> "bvsle"
  | Coq_bvslt n -> "bvslt"
  | Coq_bvule n -> "bvule"
  | Coq_bvult n -> "bvult"

let rec string_of_binop (op : Coq_bop.coq_BinOp) : string = 
  match op with
  | Coq_plus -> "+"
  | Coq_minus -> "-"
  | Coq_times -> "*"
  | Coq_land -> "/\\"
  | Coq_and -> "&&"
  | Coq_or -> "||"
  | Coq_pair (ty1, ty2) -> ", "
  | Coq_cons ty -> "::"
  | Coq_append a -> "<append>"
  | Coq_shiftr (n, m) -> ">>"
  | Coq_shiftl (n, m) -> "<<"
  | Coq_bvadd n -> "+_bv"
  | Coq_bvsub n -> "-_bv"
  | Coq_bvmul n -> "*_bv"
  | Coq_bvand n -> "&&_bv"
  | Coq_bvor n -> "||_bv"
  | Coq_bvxor n -> "(+)_bv"
  | Coq_bvapp (n, m) -> "<append>_bv"
  | Coq_bvcons n -> "::_bv"
  | Coq_update_vector_subrange (n,m,o) -> "<update_vector_subrange>"
  | Coq_relop (ty, relop) -> "<relop " ^ string_of_relop relop ^ ">"


let rec string_of_unop (op : Coq_uop.coq_UnOp) : string = 
  match op with
  | Coq_inl (ty1, ty2) -> "inl"
  | Coq_inr (ty1, ty2) -> "inr"
  | Coq_neg -> "neg"
  | Coq_not -> "not"
  | Coq_rev ty -> "rev"
  | Coq_sext (n, m) -> "sext"
  | Coq_zext (n, m) -> "zext"
  | Coq_get_slice_int n -> "get_slice_int"
  | Coq_signed n -> "signed"
  | Coq_unsigned n -> "unsigned"
  | Coq_truncate (n, m) -> "truncate"
  | Coq_vector_subrange (n, m, o) -> "vector_subrange"
  | Coq_bvnot n -> "bvnot"
  | Coq_bvdrop (n, m) -> "bvdrop"
  | Coq_bvtake (n, m) -> "bvtake"
  | Coq_negate n -> "negate"

let rec string_of_term (t : RiscvPmpBase.coq_Term) : string =
  match t with
  | Coq_term_var (lvar, ty, ctx) -> "<var>::" ^ string_of_ty ty
  | Coq_term_val (ty, value) -> "<val>::" ^ string_of_ty ty
  | Coq_term_binop (ty1, ty2, ty3, binop, term1, term2) ->
      "(" ^ string_of_term term1 ^ " " ^
      string_of_binop binop ^ " " ^
      string_of_term term2 ^ ")"
  | Coq_term_unop (ty1, ty2, unop, term) ->
      string_of_unop unop ^ "[" ^ string_of_term term ^ string_of_ty ty1 ^ "]"
  | Coq_term_tuple (ctx, env) -> "<tuple>"
  | Coq_term_union (unioni, unionk, term) -> "<union>"
  | Coq_term_record (recordi, env) -> "<record>"

let rec string_of_formula (f : coq_Formula) : string = 
  match f with
  | Coq_formula_user (p, env) -> "user formula"
  | Coq_formula_bool t -> "bool " ^ string_of_term t
  | Coq_formula_prop (b, sub, xyz) -> "injected coq prop"
  | Coq_formula_relop (ty, relop, t1, t2) -> "{ " ^ string_of_term t1 ^ " " ^ string_of_relop relop ^ " " ^ string_of_term t2 ^ "}"
  | Coq_formula_true -> "true"
  | Coq_formula_false -> "false"
  | Coq_formula_and (f1, f2) -> string_of_formula f1 ^ " /\\ " ^ string_of_formula f2
  | Coq_formula_or (f1, f2) -> string_of_formula f1 ^ " \\/ " ^ string_of_formula f2

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
      "assert " ^ string_of_formula formula ^ " /\\ " ^ string_of_symprop sp'
  | Coq_assumek (formula, sp') ->
      "Coq_assumek"
  | Coq_angelicv (binding, sp') ->
      "exists " ^ string_of_binding binding ^ ", " ^ string_of_symprop sp'
  | Coq_demonicv (binding, sp') ->
      "forall " ^ string_of_binding binding ^ ", " ^ string_of_symprop sp'
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
