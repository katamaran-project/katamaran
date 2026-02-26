open BinInt
open Bitvector
open Classes
open Datatypes
open EqDecInstances
open List
open Specif
open TypeDecl

module Coq_uop :
 sig
  type coq_UnOp =
  | Coq_inl of Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_inr of Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_neg
  | Coq_not
  | Coq_rev of Coq_ty.coq_Ty
  | Coq_sext of nat * nat
  | Coq_zext of nat * nat
  | Coq_get_slice_int of nat
  | Coq_signed of nat
  | Coq_unsigned of nat
  | Coq_truncate of nat * nat
  | Coq_vector_subrange of nat * nat * nat
  | Coq_bvnot of nat
  | Coq_bvdrop of nat * nat
  | Coq_bvtake of nat * nat
  | Coq_negate of nat

  type coq_Tel = Coq_ty.coq_Ty * coq_UnOp

  val tel_eq_dec_clause_6 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq

  val tel_eq_dec_clause_7 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq

  val tel_eq_dec_clause_10 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_9 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_11 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq

  val tel_eq_dec_clause_12_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
    sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_12 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
    coq_Tel dec_eq

  val tel_eq_dec_clause_14 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_15 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> coq_UnOp -> coq_UnOp -> coq_Tel dec_eq

  val eval :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_UnOp -> Coq_ty.coq_Val -> Coq_ty.coq_Val
 end
