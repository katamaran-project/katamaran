open Ascii
open BinNat
open BinNums
open Classes
open Datatypes
open DecimalString
open List
open PeanoNat
open Prelude
open Specif
open String

type __ = Obj.t

module Binding :
 sig
  type ('n, 't) coq_Binding = { name : 'n; coq_type : 't }
 end

module Coq_ctx :
 sig
  type 'b coq_Ctx =
  | Coq_nil
  | Coq_snoc of 'b coq_Ctx * 'b

  val coq_Ctx_rect :
    'a2 -> ('a1 coq_Ctx -> 'a2 -> 'a1 -> 'a2) -> 'a1 coq_Ctx -> 'a2

  val coq_NoConfusionPackage_Ctx : 'a1 coq_Ctx coq_NoConfusionPackage

  val eq_dec_ctx : 'a1 coq_EqDec -> 'a1 coq_Ctx coq_EqDec

  val cat : 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_Ctx

  type 'b coq_In = nat
    (* singleton inductive, whose constructor was MkIn *)

  val in_zero : 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In

  val in_succ : 'a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_In

  val coq_In_case :
    ('a1 -> 'a1 coq_Ctx -> 'a2) -> ('a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In
    -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2

  val coq_In_rect :
    ('a1 -> 'a1 coq_Ctx -> 'a2) -> ('a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In
    -> 'a2 -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2

  type 'b coq_SnocView =
  | Coq_isZero
  | Coq_isSucc of 'b * 'b coq_In

  val view : 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> __

  val in_cat_left :
    'a1 -> 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In

  val in_cat_right :
    'a1 -> 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In

  type 'b coq_CatView =
  | Coq_isCatLeft of 'b coq_In
  | Coq_isCatRight of 'b coq_In

  val catView :
    'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_CatView

  val coq_In_eqb :
    'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> bool

  val coq_In_eqb_spec :
    'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> reflect

  type ('b, 'p) coq_All =
  | Coq_all_nil
  | Coq_all_snoc of 'b coq_Ctx * 'b * ('b, 'p) coq_All * 'p

  val all_intro : ('a1 -> 'a2) -> 'a1 coq_Ctx -> ('a1, 'a2) coq_All

  val remove : 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_Ctx

  val shift_var :
    'a1 -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In -> 'a1 coq_In

  type 'b coq_OccursCheckView =
  | Same
  | Diff of 'b * 'b coq_In

  val occurs_check_view_step :
    'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> 'a1
    coq_OccursCheckView -> 'a1 coq_OccursCheckView

  val occurs_check_view :
    'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 -> 'a1 coq_In -> 'a1
    coq_OccursCheckView

  val forallb : 'a1 coq_Ctx -> ('a1 -> 'a1 coq_In -> bool) -> bool

  val map : ('a1 -> 'a2) -> 'a1 coq_Ctx -> 'a2 coq_Ctx

  val in_map : ('a1 -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2 coq_In

  val resolve :
    'a1 coq_EqDec -> ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 -> 'a2
    option

  val resolve_mk_in :
    'a1 coq_EqDec -> ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 -> 'a2
    coq_IsSome -> ('a1, 'a2) Binding.coq_Binding coq_In

  val names : ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 list

  val split_at_dot' : string -> (string -> string -> 'a1) -> 'a1

  val split_at_dot : string -> (string, string) prod

  val parse_number : string -> coq_N

  val unparse_number : coq_N -> string

  val max_with_base : string -> string list -> coq_N

  val fresh :
    (string, 'a1) Binding.coq_Binding coq_Ctx -> string option -> string
 end
