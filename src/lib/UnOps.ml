open BinInt
open Bitvector
open Classes
open Datatypes
open EqDecInstances
open List
open Specif
open TypeDecl

module Coq_uop =
 struct
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

  (** val tel_eq_dec_clause_6 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_6 _ _ _ refine _ =
    refine

  (** val tel_eq_dec_clause_7 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_7 _ _ _ refine _ =
    refine

  (** val tel_eq_dec_clause_10 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_10 _ _ _ refine =
    refine

  (** val tel_eq_dec_clause_9 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_9 _ _ _ refine =
    refine

  (** val tel_eq_dec_clause_11 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_11 _ _ _ refine _ =
    refine

  (** val tel_eq_dec_clause_12_clause_1 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
      sumbool -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_12_clause_1 _ _ _ refine _ _ _ refine0 =
    match refine with
    | Coq_left -> refine0
    | Coq_right -> Coq_right

  (** val tel_eq_dec_clause_12 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
      coq_Tel dec_eq **)

  let tel_eq_dec_clause_12 _ _ _ refine _ s1 s2 =
    match refine with
    | Coq_left -> eq_dec nat_EqDec s1 s2
    | Coq_right -> Coq_right

  (** val tel_eq_dec_clause_14 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> sumbool -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_14 _ _ _ _ refine =
    refine

  (** val tel_eq_dec_clause_15 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> sumbool -> coq_Tel dec_eq **)

  let tel_eq_dec_clause_15 _ _ _ _ refine =
    refine

  (** val tel_eq_dec :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> coq_UnOp -> coq_UnOp -> coq_Tel dec_eq **)

  let tel_eq_dec _ _ _ _ op1 op2 =
    match op1 with
    | Coq_inl (_, _) ->
      (match op2 with
       | Coq_inl (_, _) -> Coq_left
       | Coq_inr (_, _) -> Coq_right
       | _ -> assert false (* absurd case *))
    | Coq_inr (_, _) ->
      (match op2 with
       | Coq_inl (_, _) -> Coq_right
       | Coq_inr (_, _) -> Coq_left
       | _ -> assert false (* absurd case *))
    | Coq_neg ->
      (match op2 with
       | Coq_neg -> Coq_left
       | Coq_signed _ -> Coq_right
       | Coq_unsigned _ -> Coq_right
       | _ -> assert false (* absurd case *))
    | Coq_not ->
      (match op2 with
       | Coq_not -> Coq_left
       | _ -> assert false (* absurd case *))
    | Coq_rev _ ->
      (match op2 with
       | Coq_rev _ -> Coq_left
       | _ -> assert false (* absurd case *))
    | Coq_sext (m, _) ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_sext (m0, _) -> eq_dec nat_EqDec m m0
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | _ -> Coq_right)
    | Coq_zext (m, _) ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_zext (m0, _) -> eq_dec nat_EqDec m m0
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | _ -> Coq_right)
    | Coq_get_slice_int _ ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_get_slice_int _ -> Coq_left
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | _ -> Coq_right)
    | Coq_signed n ->
      (match op2 with
       | Coq_neg -> Coq_right
       | Coq_signed n0 -> eq_dec nat_EqDec n n0
       | Coq_unsigned _ -> Coq_right
       | _ -> assert false (* absurd case *))
    | Coq_unsigned n ->
      (match op2 with
       | Coq_neg -> Coq_right
       | Coq_signed _ -> Coq_right
       | Coq_unsigned n0 -> eq_dec nat_EqDec n n0
       | _ -> assert false (* absurd case *))
    | Coq_truncate (n, _) ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | Coq_truncate (n0, _) -> eq_dec nat_EqDec n n0
       | _ -> Coq_right)
    | Coq_vector_subrange (n, s, _) ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | Coq_vector_subrange (n0, s0, _) ->
         (match eq_dec nat_EqDec n n0 with
          | Coq_left -> eq_dec nat_EqDec s s0
          | Coq_right -> Coq_right)
       | _ -> Coq_right)
    | Coq_bvnot _ ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | Coq_bvnot _ -> Coq_left
       | _ -> Coq_right)
    | Coq_bvdrop (m, _) ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | Coq_bvdrop (m0, _) -> eq_dec nat_EqDec m m0
       | _ -> Coq_right)
    | Coq_bvtake (_, n) ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | Coq_bvtake (_, n0) -> eq_dec nat_EqDec n n0
       | _ -> Coq_right)
    | Coq_negate _ ->
      (match op2 with
       | Coq_inl (_, _) -> assert false (* absurd case *)
       | Coq_inr (_, _) -> assert false (* absurd case *)
       | Coq_neg -> assert false (* absurd case *)
       | Coq_not -> assert false (* absurd case *)
       | Coq_rev _ -> assert false (* absurd case *)
       | Coq_signed _ -> assert false (* absurd case *)
       | Coq_unsigned _ -> assert false (* absurd case *)
       | Coq_negate _ -> Coq_left
       | _ -> Coq_right)

  (** val eval :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> coq_UnOp -> Coq_ty.coq_Val -> Coq_ty.coq_Val **)

  let eval _ _ _ _ = function
  | Coq_inl (_, _) -> Obj.magic (fun x -> Datatypes.Coq_inl x)
  | Coq_inr (_, _) -> Obj.magic (fun x -> Datatypes.Coq_inr x)
  | Coq_neg -> Obj.magic Z.opp
  | Coq_not -> Obj.magic negb
  | Coq_rev _ -> Obj.magic rev
  | Coq_sext (m, n) -> (fun v -> Obj.magic Coq_bv.sext m v n)
  | Coq_zext (m, n) -> (fun v -> Obj.magic Coq_bv.zext m v n)
  | Coq_get_slice_int n -> Obj.magic Coq_bv.of_Z n
  | Coq_signed n -> (fun v -> Obj.magic Coq_bv.signed n v)
  | Coq_unsigned n -> (fun v -> Obj.magic Coq_bv.unsigned n v)
  | Coq_truncate (n, m) -> (fun v -> Obj.magic Coq_bv.truncate n m v)
  | Coq_vector_subrange (n, s, l) -> Obj.magic Coq_bv.vector_subrange n s l
  | Coq_bvnot n -> Obj.magic Coq_bv.not n
  | Coq_bvdrop (m, n) -> Obj.magic Coq_bv.drop m n
  | Coq_bvtake (m, n) -> Obj.magic Coq_bv.take m n
  | Coq_negate n -> Obj.magic Coq_bv.negate n
 end
