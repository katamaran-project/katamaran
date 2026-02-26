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

module Coq_ty =
 struct
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

  (** val coq_NoConfusionPackage_Ty :
      coq_TypeDeclKit -> coq_Ty coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_Ty _ =
    Build_NoConfusionPackage

  (** val option : coq_TypeDeclKit -> coq_Ty -> coq_Ty **)

  let option _ t =
    Coq_sum (t, Coq_unit)

  (** val coq_Ty_rect :
      coq_TypeDeclKit -> 'a1 -> 'a1 -> 'a1 -> (coq_Ty -> 'a1 -> 'a1) ->
      (coq_Ty -> coq_Ty -> 'a1 -> 'a1 -> 'a1) -> (coq_Ty -> coq_Ty -> 'a1 ->
      'a1 -> 'a1) -> 'a1 -> (enumi -> 'a1) -> (nat -> 'a1) -> (coq_Ty
      Coq_ctx.coq_Ctx -> (coq_Ty, 'a1) Coq_ctx.coq_All -> 'a1) -> (unioni ->
      'a1) -> (recordi -> 'a1) -> coq_Ty -> 'a1 **)

  let rec coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum p_bvec p_tuple p_union p_record = function
  | Coq_int -> p_int
  | Coq_bool -> p_bool
  | Coq_string -> p_string
  | Coq_list _UU03c3_0 ->
    p_list _UU03c3_0
      (coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c3_0)
  | Coq_prod (_UU03c3_0, _UU03c4_) ->
    p_prod _UU03c3_0 _UU03c4_
      (coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c3_0)
      (coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c4_)
  | Coq_sum (_UU03c3_0, _UU03c4_) ->
    p_sum _UU03c3_0 _UU03c4_
      (coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c3_0)
      (coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c4_)
  | Coq_unit -> p_unit
  | Coq_enum e -> p_enum e
  | Coq_bvec n -> p_bvec n
  | Coq_tuple _UU03c3_s ->
    p_tuple _UU03c3_s
      (Coq_ctx.all_intro
        (coq_Ty_rect tK p_int p_bool p_string p_list p_prod p_sum p_unit
          p_enum p_bvec p_tuple p_union p_record)
        _UU03c3_s)
  | Coq_union u -> p_union u
  | Coq_record r -> p_record r

  (** val coq_Ty_rec :
      coq_TypeDeclKit -> 'a1 -> 'a1 -> 'a1 -> (coq_Ty -> 'a1 -> 'a1) ->
      (coq_Ty -> coq_Ty -> 'a1 -> 'a1 -> 'a1) -> (coq_Ty -> coq_Ty -> 'a1 ->
      'a1 -> 'a1) -> 'a1 -> (enumi -> 'a1) -> (nat -> 'a1) -> (coq_Ty
      Coq_ctx.coq_Ctx -> (coq_Ty, 'a1) Coq_ctx.coq_All -> 'a1) -> (unioni ->
      'a1) -> (recordi -> 'a1) -> coq_Ty -> 'a1 **)

  let rec coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum p_bvec p_tuple p_union p_record = function
  | Coq_int -> p_int
  | Coq_bool -> p_bool
  | Coq_string -> p_string
  | Coq_list _UU03c3_0 ->
    p_list _UU03c3_0
      (coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c3_0)
  | Coq_prod (_UU03c3_0, _UU03c4_) ->
    p_prod _UU03c3_0 _UU03c4_
      (coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c3_0)
      (coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c4_)
  | Coq_sum (_UU03c3_0, _UU03c4_) ->
    p_sum _UU03c3_0 _UU03c4_
      (coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c3_0)
      (coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit p_enum
        p_bvec p_tuple p_union p_record _UU03c4_)
  | Coq_unit -> p_unit
  | Coq_enum e -> p_enum e
  | Coq_bvec n -> p_bvec n
  | Coq_tuple _UU03c3_s ->
    p_tuple _UU03c3_s
      (Coq_ctx.all_intro
        (coq_Ty_rec tK p_int p_bool p_string p_list p_prod p_sum p_unit
          p_enum p_bvec p_tuple p_union p_record)
        _UU03c3_s)
  | Coq_union u -> p_union u
  | Coq_record r -> p_record r

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

  (** val enum_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi
      coq_EqDec **)

  let enum_eqdec _ _ typeDefKit =
    typeDefKit.enum_eqdec

  (** val union_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni
      coq_EqDec **)

  let union_eqdec _ _ typeDefKit =
    typeDefKit.union_eqdec

  (** val record_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi
      coq_EqDec **)

  let record_eqdec _ _ typeDefKit =
    typeDefKit.record_eqdec

  (** val enumt_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi ->
      enumt coq_EqDec **)

  let enumt_eqdec _ _ typeDefKit =
    typeDefKit.enumt_eqdec

  (** val enumt_finite :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi ->
      enumt coq_Finite **)

  let enumt_finite _ _ typeDefKit =
    typeDefKit.enumt_finite

  (** val uniont_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
      uniont coq_EqDec **)

  let uniont_eqdec _ _ typeDefKit =
    typeDefKit.uniont_eqdec

  type unionk = __

  (** val unionk_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
      unionk coq_EqDec **)

  let unionk_eqdec _ _ typeDefKit =
    typeDefKit.unionk_eqdec

  (** val unionk_finite :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
      unionk coq_Finite **)

  let unionk_finite _ _ typeDefKit =
    typeDefKit.unionk_finite

  (** val unionk_ty :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
      unionk -> coq_Ty **)

  let unionk_ty _ _ typeDefKit =
    typeDefKit.unionk_ty

  (** val recordt_eqdec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
      recordt coq_EqDec **)

  let recordt_eqdec _ _ typeDefKit =
    typeDefKit.recordt_eqdec

  type recordf = __

  (** val recordf_ty :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
      (recordf, coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let recordf_ty _ _ typeDefKit =
    typeDefKit.recordf_ty

  (** val unionv_fold :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
      (unionk, coq_Val) sigT -> uniont **)

  let unionv_fold _ _ typeDefKit =
    typeDefKit.unionv_fold

  (** val unionv_unfold :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
      uniont -> (unionk, coq_Val) sigT **)

  let unionv_unfold _ _ typeDefKit =
    typeDefKit.unionv_unfold

  (** val recordv_fold :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
      (recordf, coq_Ty, coq_Val) coq_NamedEnv -> recordt **)

  let recordv_fold _ _ typeDefKit =
    typeDefKit.recordv_fold

  (** val recordv_unfold :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
      recordt -> (recordf, coq_Ty, coq_Val) coq_NamedEnv **)

  let recordv_unfold _ _ typeDefKit =
    typeDefKit.recordv_unfold

  (** val coq_Ty_eq_dec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> coq_Ty
      coq_EqDec **)

  let rec coq_Ty_eq_dec tDC tDN tDF _UU03c3_ _UU03c4_ =
    match _UU03c3_ with
    | Coq_int -> (match _UU03c4_ with
                  | Coq_int -> Coq_left
                  | _ -> Coq_right)
    | Coq_bool -> (match _UU03c4_ with
                   | Coq_bool -> Coq_left
                   | _ -> Coq_right)
    | Coq_string ->
      (match _UU03c4_ with
       | Coq_string -> Coq_left
       | _ -> Coq_right)
    | Coq_list _UU03c3_0 ->
      (match _UU03c4_ with
       | Coq_list _UU03c4_0 ->
         f_equal_dec (fun x -> Coq_list x) _UU03c3_0 _UU03c4_0
           (coq_Ty_eq_dec tDC tDN tDF _UU03c3_0 _UU03c4_0)
       | _ -> Coq_right)
    | Coq_prod (_UU03c3_1, _UU03c3_2) ->
      (match _UU03c4_ with
       | Coq_prod (_UU03c4_1, _UU03c4_2) ->
         f_equal2_dec (fun x x0 -> Coq_prod (x, x0)) _UU03c3_1 _UU03c4_1
           _UU03c3_2 _UU03c4_2
           (coq_Ty_eq_dec tDC tDN tDF _UU03c3_1 _UU03c4_1)
           (coq_Ty_eq_dec tDC tDN tDF _UU03c3_2 _UU03c4_2)
       | _ -> Coq_right)
    | Coq_sum (_UU03c3_1, _UU03c3_2) ->
      (match _UU03c4_ with
       | Coq_sum (_UU03c4_1, _UU03c4_2) ->
         f_equal2_dec (fun x x0 -> Coq_sum (x, x0)) _UU03c3_1 _UU03c4_1
           _UU03c3_2 _UU03c4_2
           (coq_Ty_eq_dec tDC tDN tDF _UU03c3_1 _UU03c4_1)
           (coq_Ty_eq_dec tDC tDN tDF _UU03c3_2 _UU03c4_2)
       | _ -> Coq_right)
    | Coq_unit -> (match _UU03c4_ with
                   | Coq_unit -> Coq_left
                   | _ -> Coq_right)
    | Coq_enum e1 ->
      (match _UU03c4_ with
       | Coq_enum e2 ->
         f_equal_dec (fun x -> Coq_enum x) e1 e2 (eq_dec tDF.enum_eqdec e1 e2)
       | _ -> Coq_right)
    | Coq_bvec n1 ->
      (match _UU03c4_ with
       | Coq_bvec n2 ->
         f_equal_dec (fun x -> Coq_bvec x) n1 n2 (eq_dec nat_EqDec n1 n2)
       | _ -> Coq_right)
    | Coq_tuple _UU03c3_s ->
      (match _UU03c4_ with
       | Coq_tuple _UU03c4_s ->
         f_equal_dec (fun x -> Coq_tuple x) _UU03c3_s _UU03c4_s
           (eq_dec (Coq_ctx.eq_dec_ctx (coq_Ty_eq_dec tDC tDN tDF)) _UU03c3_s
             _UU03c4_s)
       | _ -> Coq_right)
    | Coq_union u1 ->
      (match _UU03c4_ with
       | Coq_union u2 ->
         f_equal_dec (fun x -> Coq_union x) u1 u2
           (eq_dec tDF.union_eqdec u1 u2)
       | _ -> Coq_right)
    | Coq_record r1 ->
      (match _UU03c4_ with
       | Coq_record r2 ->
         f_equal_dec (fun x -> Coq_record x) r1 r2
           (eq_dec tDF.record_eqdec r1 r2)
       | _ -> Coq_right)

  (** val coq_Val_eq_dec :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> coq_Ty ->
      coq_Val coq_EqDec **)

  let rec coq_Val_eq_dec tDC tDN tDF = function
  | Coq_int -> eq_dec (Obj.magic coq_Z_eqdec)
  | Coq_bool -> eq_dec (Obj.magic bool_EqDec)
  | Coq_string -> eq_dec (Obj.magic string_eqdec)
  | Coq_list _UU03c3_0 ->
    eq_dec (Obj.magic list_eqdec (coq_Val_eq_dec tDC tDN tDF _UU03c3_0))
  | Coq_prod (_UU03c3_0, _UU03c4_) ->
    eq_dec
      (Obj.magic prod_eqdec (coq_Val_eq_dec tDC tDN tDF _UU03c3_0)
        (coq_Val_eq_dec tDC tDN tDF _UU03c4_))
  | Coq_sum (_UU03c3_0, _UU03c4_) ->
    eq_dec
      (Obj.magic sum_eqdec (coq_Val_eq_dec tDC tDN tDF _UU03c3_0)
        (coq_Val_eq_dec tDC tDN tDF _UU03c4_))
  | Coq_unit -> eq_dec (Obj.magic unit_EqDec)
  | Coq_enum e -> eq_dec (tDF.enumt_eqdec e)
  | Coq_bvec n -> eq_dec (Obj.magic Coq_bv.eqdec_bv n)
  | Coq_tuple _UU03c3_s ->
    let rec f = function
    | Coq_ctx.Coq_nil -> eq_dec (Obj.magic unit_EqDec)
    | Coq_ctx.Coq_snoc (_UU0393_, b) ->
      eq_dec
        (Obj.magic prod_eqdec (f _UU0393_) (coq_Val_eq_dec tDC tDN tDF b))
    in f _UU03c3_s
  | Coq_union u -> eq_dec (tDF.uniont_eqdec u)
  | Coq_record r -> eq_dec (tDF.recordt_eqdec r)

  (** val inhabit :
      coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_Ty -> coq_Val option **)

  let rec inhabit tDC tDN = function
  | Coq_int -> Some (Obj.magic Z0)
  | Coq_bool -> Some (Obj.magic Coq_true)
  | Coq_string -> Some (Obj.magic EmptyString)
  | Coq_list _ -> Some (Obj.magic Coq_nil)
  | Coq_prod (_UU03c4_1, _UU03c4_2) ->
    Coq_option.bind (inhabit tDC tDN _UU03c4_1) (fun v1 ->
      Coq_option.bind (inhabit tDC tDN _UU03c4_2) (fun v2 -> Some
        (Obj.magic (Coq_pair (v1, v2)))))
  | Coq_sum (_UU03c4_1, _UU03c4_2) ->
    union option_union
      (Coq_option.map (Obj.magic (fun x -> Coq_inl x))
        (inhabit tDC tDN _UU03c4_1))
      (Coq_option.map (Obj.magic (fun x -> Coq_inr x))
        (inhabit tDC tDN _UU03c4_2))
  | Coq_unit -> Some (Obj.magic Coq_tt)
  | Coq_bvec n -> Some (Obj.magic Coq_bv.zero n)
  | _ -> None
 end
