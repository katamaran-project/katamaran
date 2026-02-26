open BinNums
open Bitvector
open Classes
open Context
open Datatypes
open Environment
open EqDecInstances
open Prelude
open Specif
open String
open Base
open Finite
open Option

type __ = Obj.t

module Coq_ty :
 sig
  type coq_TypeDeclKit =
  | Build_TypeDeclKit

  type enumi = __

  type unioni = __

  type recordi = __

  type coq_Ty =
  | Coq_int
  | Coq_bool
  | Coq_string
  | Coq_list of coq_Ty
  | Coq_prod of coq_Ty * coq_Ty
  | Coq_sum of coq_Ty * coq_Ty
  | Coq_unit
  | Coq_enum of enumi
  | Coq_bvec of nat
  | Coq_tuple of coq_Ty Coq_ctx.coq_Ctx
  | Coq_union of unioni
  | Coq_record of recordi

  val coq_NoConfusionPackage_Ty :
    coq_TypeDeclKit -> coq_Ty coq_NoConfusionPackage

  val option : coq_TypeDeclKit -> coq_Ty -> coq_Ty

  val coq_Ty_rect :
    coq_TypeDeclKit -> 'a1 -> 'a1 -> 'a1 -> (coq_Ty -> 'a1 -> 'a1) -> (coq_Ty
    -> coq_Ty -> 'a1 -> 'a1 -> 'a1) -> (coq_Ty -> coq_Ty -> 'a1 -> 'a1 ->
    'a1) -> 'a1 -> (enumi -> 'a1) -> (nat -> 'a1) -> (coq_Ty Coq_ctx.coq_Ctx
    -> (coq_Ty, 'a1) Coq_ctx.coq_All -> 'a1) -> (unioni -> 'a1) -> (recordi
    -> 'a1) -> coq_Ty -> 'a1

  val coq_Ty_rec :
    coq_TypeDeclKit -> 'a1 -> 'a1 -> 'a1 -> (coq_Ty -> 'a1 -> 'a1) -> (coq_Ty
    -> coq_Ty -> 'a1 -> 'a1 -> 'a1) -> (coq_Ty -> coq_Ty -> 'a1 -> 'a1 ->
    'a1) -> 'a1 -> (enumi -> 'a1) -> (nat -> 'a1) -> (coq_Ty Coq_ctx.coq_Ctx
    -> (coq_Ty, 'a1) Coq_ctx.coq_All -> 'a1) -> (unioni -> 'a1) -> (recordi
    -> 'a1) -> coq_Ty -> 'a1

  type coq_TypeDenoteKit =
  | Build_TypeDenoteKit

  type enumt = __

  type uniont = __

  type recordt = __

  type coq_Val = __

  type coq_TypeDefKit = { enum_eqdec : enumi coq_EqDec;
                          union_eqdec : unioni coq_EqDec;
                          record_eqdec : recordi coq_EqDec;
                          enumt_eqdec : (enumi -> enumt coq_EqDec);
                          enumt_finite : (enumi -> enumt coq_Finite);
                          uniont_eqdec : (unioni -> uniont coq_EqDec);
                          unionk_eqdec : (unioni -> __ coq_EqDec);
                          unionk_finite : (unioni -> __ coq_Finite);
                          unionk_ty : (unioni -> __ -> coq_Ty);
                          recordt_eqdec : (recordi -> recordt coq_EqDec);
                          recordf_ty : (recordi -> (__, coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx);
                          unionv_fold : (unioni -> (__, coq_Val) sigT ->
                                        uniont);
                          unionv_unfold : (unioni -> uniont -> (__, coq_Val)
                                          sigT);
                          recordv_fold : (recordi -> (__, coq_Ty, coq_Val)
                                         coq_NamedEnv -> recordt);
                          recordv_unfold : (recordi -> recordt -> (__,
                                           coq_Ty, coq_Val) coq_NamedEnv) }

  val enum_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi coq_EqDec

  val union_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni coq_EqDec

  val record_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi
    coq_EqDec

  val enumt_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi -> enumt
    coq_EqDec

  val enumt_finite :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi -> enumt
    coq_Finite

  val uniont_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    uniont coq_EqDec

  type unionk = __

  val unionk_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    unionk coq_EqDec

  val unionk_finite :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    unionk coq_Finite

  val unionk_ty :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    unionk -> coq_Ty

  val recordt_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    recordt coq_EqDec

  type recordf = __

  val recordf_ty :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    (recordf, coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val unionv_fold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    (unionk, coq_Val) sigT -> uniont

  val unionv_unfold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    uniont -> (unionk, coq_Val) sigT

  val recordv_fold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    (recordf, coq_Ty, coq_Val) coq_NamedEnv -> recordt

  val recordv_unfold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    recordt -> (recordf, coq_Ty, coq_Val) coq_NamedEnv

  val coq_Ty_eq_dec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> coq_Ty coq_EqDec

  val coq_Val_eq_dec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> coq_Ty ->
    coq_Val coq_EqDec

  val inhabit :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_Ty -> coq_Val option
 end
