open BinInt
open Bitvector
open Classes
open Datatypes
open EqDecInstances
open Nat
open Prelude
open Specif
open TypeDecl

module Coq_bop :
 sig
  type coq_RelOp =
  | Coq_eq of Coq_ty.coq_Ty
  | Coq_neq of Coq_ty.coq_Ty
  | Coq_le
  | Coq_lt
  | Coq_bvsle of nat
  | Coq_bvslt of nat
  | Coq_bvule of nat
  | Coq_bvult of nat

  type coq_BinOp =
  | Coq_plus
  | Coq_minus
  | Coq_times
  | Coq_land
  | Coq_and
  | Coq_or
  | Coq_pair of Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_cons of Coq_ty.coq_Ty
  | Coq_append of Coq_ty.coq_Ty
  | Coq_shiftr of nat * nat
  | Coq_shiftl of nat * nat
  | Coq_bvadd of nat
  | Coq_bvsub of nat
  | Coq_bvmul of nat
  | Coq_bvand of nat
  | Coq_bvor of nat
  | Coq_bvxor of nat
  | Coq_bvapp of nat * nat
  | Coq_bvcons of nat
  | Coq_update_vector_subrange of nat * nat * nat
  | Coq_relop of Coq_ty.coq_Ty * coq_RelOp

  type coq_BinOp_sig = coq_BinOp

  type coq_RelOp_sig = coq_RelOp

  val coq_RelOp_eqdec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_RelOp -> coq_RelOp ->
    coq_RelOp dec_eq

  val coq_RelOp_EqDec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_RelOp coq_EqDec

  type coq_RelOpTel = Coq_ty.coq_Ty * coq_RelOp_sig

  type coq_BinOpTel =
    (Coq_ty.coq_Ty * (Coq_ty.coq_Ty * Coq_ty.coq_Ty)) * coq_BinOp_sig

  val binoptel_pair :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOpTel

  val binoptel_cons : Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_BinOpTel

  val binoptel_append :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_BinOpTel

  val binoptel_shiftr : Coq_ty.coq_TypeDeclKit -> nat -> nat -> coq_BinOpTel

  val binoptel_shiftl : Coq_ty.coq_TypeDeclKit -> nat -> nat -> coq_BinOpTel

  val reloptel_eq_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_RelOp ->
    coq_RelOp -> coq_RelOpTel dec_eq

  val binoptel_eq_dec_relop :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_RelOp ->
    coq_RelOp -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec_clause_1_clause_1_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> sumbool
    -> nat -> nat -> sumbool -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec_clause_1_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> sumbool
    -> nat -> nat -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
    nat -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> nat -> nat -> nat ->
    coq_BinOpTel dec_eq

  val binoptel_eq_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOp ->
    coq_BinOp -> coq_BinOpTel dec_eq

  val eqdep_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOp ->
    coq_BinOp -> sumbool

  val eval_relop_val :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> coq_RelOp -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> bool

  val eval :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> coq_BinOp -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val
 end
