open Classes
open Context
open Datatypes
open String

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_VarKit = { coq_PVar_eq_dec : __ coq_EqDec;
                    coq_LVar_eq_dec : __ coq_EqDec;
                    coq_PVartoLVar : (__ -> __);
                    fresh_pvar : (__ -> (__, __) Binding.coq_Binding
                                 Coq_ctx.coq_Ctx -> __ option -> __);
                    fresh_lvar : (__ -> (__, __) Binding.coq_Binding
                                 Coq_ctx.coq_Ctx -> __ option -> __) }

type coq_PVar = __

type coq_LVar = __

(** val fresh_lvar :
    coq_VarKit -> (coq_LVar, 'a1) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_LVar option -> coq_LVar **)

let fresh_lvar varKit x x0 =
  Obj.magic varKit.fresh_lvar __ x x0

(** val coq_DefaultVarKit : coq_VarKit **)

let coq_DefaultVarKit =
  { coq_PVar_eq_dec = (Obj.magic string_dec); coq_LVar_eq_dec =
    (Obj.magic string_dec); coq_PVartoLVar = (fun x -> x); fresh_pvar =
    (Obj.magic (fun _ -> Coq_ctx.fresh)); fresh_lvar =
    (Obj.magic (fun _ -> Coq_ctx.fresh)) }
