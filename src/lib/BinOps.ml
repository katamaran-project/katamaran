open BinInt
open Bitvector
open Classes
open Datatypes
open EqDecInstances
open Nat
open Prelude
open Specif
open TypeDecl

module Coq_bop =
 struct
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

  (** val coq_RelOp_eqdec :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_RelOp -> coq_RelOp ->
      coq_RelOp dec_eq **)

  let coq_RelOp_eqdec _ _ x y =
    match x with
    | Coq_eq _ -> (match y with
                   | Coq_eq _ -> Coq_left
                   | _ -> Coq_right)
    | Coq_neq _ -> (match y with
                    | Coq_neq _ -> Coq_left
                    | _ -> Coq_right)
    | Coq_le ->
      let y0 = Coq_ty.Coq_int,y in
      (match let _,pr2 = y0 in pr2 with
       | Coq_eq _ -> Coq_right
       | Coq_neq _ -> Coq_right
       | Coq_le -> Coq_left
       | Coq_lt -> Coq_right
       | _ -> assert false (* absurd case *))
    | Coq_lt ->
      let y0 = Coq_ty.Coq_int,y in
      (match let _,pr2 = y0 in pr2 with
       | Coq_eq _ -> Coq_right
       | Coq_neq _ -> Coq_right
       | Coq_le -> Coq_right
       | Coq_lt -> Coq_left
       | _ -> assert false (* absurd case *))
    | Coq_bvsle n ->
      let y0 = (Coq_ty.Coq_bvec n),y in
      (match let _,pr2 = y0 in pr2 with
       | Coq_le -> assert false (* absurd case *)
       | Coq_lt -> assert false (* absurd case *)
       | Coq_bvsle _ -> Coq_left
       | _ -> Coq_right)
    | Coq_bvslt n ->
      let y0 = (Coq_ty.Coq_bvec n),y in
      (match let _,pr2 = y0 in pr2 with
       | Coq_le -> assert false (* absurd case *)
       | Coq_lt -> assert false (* absurd case *)
       | Coq_bvslt _ -> Coq_left
       | _ -> Coq_right)
    | Coq_bvule n ->
      let y0 = (Coq_ty.Coq_bvec n),y in
      (match let _,pr2 = y0 in pr2 with
       | Coq_le -> assert false (* absurd case *)
       | Coq_lt -> assert false (* absurd case *)
       | Coq_bvule _ -> Coq_left
       | _ -> Coq_right)
    | Coq_bvult n ->
      let y0 = (Coq_ty.Coq_bvec n),y in
      (match let _,pr2 = y0 in pr2 with
       | Coq_le -> assert false (* absurd case *)
       | Coq_lt -> assert false (* absurd case *)
       | Coq_bvult _ -> Coq_left
       | _ -> Coq_right)

  (** val coq_RelOp_EqDec :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_RelOp coq_EqDec **)

  let coq_RelOp_EqDec =
    coq_RelOp_eqdec

  type coq_RelOpTel = Coq_ty.coq_Ty * coq_RelOp_sig

  type coq_BinOpTel =
    (Coq_ty.coq_Ty * (Coq_ty.coq_Ty * Coq_ty.coq_Ty)) * coq_BinOp_sig

  (** val binoptel_pair :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOpTel **)

  let binoptel_pair _ _UU03c3_1 _UU03c3_2 =
    (_UU03c3_1,(_UU03c3_2,(Coq_ty.Coq_prod (_UU03c3_1,
      _UU03c3_2)))),(Coq_pair (_UU03c3_1, _UU03c3_2))

  (** val binoptel_cons :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_BinOpTel **)

  let binoptel_cons _ _UU03c3_ =
    (_UU03c3_,((Coq_ty.Coq_list _UU03c3_),(Coq_ty.Coq_list
      _UU03c3_))),(Coq_cons _UU03c3_)

  (** val binoptel_append :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_BinOpTel **)

  let binoptel_append _ _UU03c3_ =
    ((Coq_ty.Coq_list _UU03c3_),((Coq_ty.Coq_list _UU03c3_),(Coq_ty.Coq_list
      _UU03c3_))),(Coq_append _UU03c3_)

  (** val binoptel_shiftr :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> coq_BinOpTel **)

  let binoptel_shiftr _ m n =
    ((Coq_ty.Coq_bvec m),((Coq_ty.Coq_bvec n),(Coq_ty.Coq_bvec
      m))),(Coq_shiftr (m, n))

  (** val binoptel_shiftl :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> coq_BinOpTel **)

  let binoptel_shiftl _ m n =
    ((Coq_ty.Coq_bvec m),((Coq_ty.Coq_bvec n),(Coq_ty.Coq_bvec
      m))),(Coq_shiftl (m, n))

  (** val reloptel_eq_dec :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
      Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_RelOp ->
      coq_RelOp -> coq_RelOpTel dec_eq **)

  let reloptel_eq_dec tDC tDN tDF _ _ op1 op2 =
    match op1 with
    | Coq_eq _UU03c3_ ->
      (match op2 with
       | Coq_eq _UU03c4_ ->
         f_equal_dec (fun _UU03c1_ -> _UU03c1_,(Coq_eq _UU03c1_)) _UU03c3_
           _UU03c4_
           (eq_dec (Coq_ty.coq_Ty_eq_dec tDC tDN tDF) _UU03c3_ _UU03c4_)
       | _ -> Coq_right)
    | Coq_neq _UU03c3_ ->
      (match op2 with
       | Coq_neq _UU03c4_ ->
         f_equal_dec (fun _UU03c1_ -> _UU03c1_,(Coq_neq _UU03c1_)) _UU03c3_
           _UU03c4_
           (eq_dec (Coq_ty.coq_Ty_eq_dec tDC tDN tDF) _UU03c3_ _UU03c4_)
       | _ -> Coq_right)
    | Coq_le -> (match op2 with
                 | Coq_le -> Coq_left
                 | _ -> Coq_right)
    | Coq_lt -> (match op2 with
                 | Coq_lt -> Coq_left
                 | _ -> Coq_right)
    | Coq_bvsle m ->
      (match op2 with
       | Coq_bvsle n ->
         f_equal_dec (fun n0 -> (Coq_ty.Coq_bvec n0),(Coq_bvsle n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvslt m ->
      (match op2 with
       | Coq_bvslt n ->
         f_equal_dec (fun n0 -> (Coq_ty.Coq_bvec n0),(Coq_bvslt n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvule m ->
      (match op2 with
       | Coq_bvule n ->
         f_equal_dec (fun n0 -> (Coq_ty.Coq_bvec n0),(Coq_bvule n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvult m ->
      (match op2 with
       | Coq_bvult n ->
         f_equal_dec (fun n0 -> (Coq_ty.Coq_bvec n0),(Coq_bvult n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)

  (** val binoptel_eq_dec_relop :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
      Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_RelOp ->
      coq_RelOp -> coq_BinOpTel dec_eq **)

  let binoptel_eq_dec_relop =
    reloptel_eq_dec

  (** val update_vector_subrange_eq_dec_clause_1_clause_1_clause_1 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat ->
      sumbool -> nat -> nat -> sumbool -> coq_BinOpTel dec_eq **)

  let update_vector_subrange_eq_dec_clause_1_clause_1_clause_1 _ _ _ refine _ _ refine0 _ _ refine1 =
    match refine with
    | Coq_left ->
      (match refine0 with
       | Coq_left -> refine1
       | Coq_right -> Coq_right)
    | Coq_right -> Coq_right

  (** val update_vector_subrange_eq_dec_clause_1_clause_1 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat ->
      sumbool -> nat -> nat -> coq_BinOpTel dec_eq **)

  let update_vector_subrange_eq_dec_clause_1_clause_1 _ _ _ refine _ _ refine0 l1 l2 =
    match refine with
    | Coq_left ->
      (match refine0 with
       | Coq_left -> eq_dec nat_EqDec l1 l2
       | Coq_right -> Coq_right)
    | Coq_right -> Coq_right

  (** val update_vector_subrange_eq_dec_clause_1 :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
      nat -> coq_BinOpTel dec_eq **)

  let update_vector_subrange_eq_dec_clause_1 _ _ _ refine s1 s2 l1 l2 =
    match refine with
    | Coq_left ->
      (match eq_dec nat_EqDec s1 s2 with
       | Coq_left -> eq_dec nat_EqDec l1 l2
       | Coq_right -> Coq_right)
    | Coq_right -> Coq_right

  (** val update_vector_subrange_eq_dec :
      Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> nat -> nat -> nat ->
      coq_BinOpTel dec_eq **)

  let update_vector_subrange_eq_dec _ n1 n2 s1 s2 l1 l2 =
    match eq_dec nat_EqDec n1 n2 with
    | Coq_left ->
      (match eq_dec nat_EqDec s1 s2 with
       | Coq_left -> eq_dec nat_EqDec l1 l2
       | Coq_right -> Coq_right)
    | Coq_right -> Coq_right

  (** val binoptel_eq_dec :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
      Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      coq_BinOp -> coq_BinOp -> coq_BinOpTel dec_eq **)

  let binoptel_eq_dec tDC tDN tDF _ _ _ _ _ _ op1 op2 =
    match op1 with
    | Coq_plus -> (match op2 with
                   | Coq_plus -> Coq_left
                   | _ -> Coq_right)
    | Coq_minus -> (match op2 with
                    | Coq_minus -> Coq_left
                    | _ -> Coq_right)
    | Coq_times -> (match op2 with
                    | Coq_times -> Coq_left
                    | _ -> Coq_right)
    | Coq_land -> (match op2 with
                   | Coq_land -> Coq_left
                   | _ -> Coq_right)
    | Coq_and -> (match op2 with
                  | Coq_and -> Coq_left
                  | _ -> Coq_right)
    | Coq_or -> (match op2 with
                 | Coq_or -> Coq_left
                 | _ -> Coq_right)
    | Coq_pair (_UU03c3_1, _UU03c3_2) ->
      (match op2 with
       | Coq_pair (_UU03c4_1, _UU03c4_2) ->
         f_equal2_dec (binoptel_pair tDC) _UU03c3_1 _UU03c4_1 _UU03c3_2
           _UU03c4_2
           (eq_dec (Coq_ty.coq_Ty_eq_dec tDC tDN tDF) _UU03c3_1 _UU03c4_1)
           (eq_dec (Coq_ty.coq_Ty_eq_dec tDC tDN tDF) _UU03c3_2 _UU03c4_2)
       | _ -> Coq_right)
    | Coq_cons _UU03c3_ ->
      (match op2 with
       | Coq_cons _UU03c4_ ->
         f_equal_dec (binoptel_cons tDC) _UU03c3_ _UU03c4_
           (eq_dec (Coq_ty.coq_Ty_eq_dec tDC tDN tDF) _UU03c3_ _UU03c4_)
       | _ -> Coq_right)
    | Coq_append _UU03c3_ ->
      (match op2 with
       | Coq_append _UU03c4_ ->
         f_equal_dec (binoptel_append tDC) _UU03c3_ _UU03c4_
           (eq_dec (Coq_ty.coq_Ty_eq_dec tDC tDN tDF) _UU03c3_ _UU03c4_)
       | _ -> Coq_right)
    | Coq_shiftr (m, n) ->
      (match op2 with
       | Coq_shiftr (p, q) ->
         f_equal2_dec (binoptel_shiftr tDC) m p n q (eq_dec nat_EqDec m p)
           (eq_dec nat_EqDec n q)
       | _ -> Coq_right)
    | Coq_shiftl (m, n) ->
      (match op2 with
       | Coq_shiftl (p, q) ->
         f_equal2_dec (binoptel_shiftl tDC) m p n q (eq_dec nat_EqDec m p)
           (eq_dec nat_EqDec n q)
       | _ -> Coq_right)
    | Coq_bvadd m ->
      (match op2 with
       | Coq_bvadd n ->
         f_equal_dec (fun n0 -> ((Coq_ty.Coq_bvec n0),((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec n0))),(Coq_bvadd n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvsub m ->
      (match op2 with
       | Coq_bvsub n ->
         f_equal_dec (fun n0 -> ((Coq_ty.Coq_bvec n0),((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec n0))),(Coq_bvsub n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvmul m ->
      (match op2 with
       | Coq_bvmul n ->
         f_equal_dec (fun n0 -> ((Coq_ty.Coq_bvec n0),((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec n0))),(Coq_bvmul n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvand m ->
      (match op2 with
       | Coq_bvand n ->
         f_equal_dec (fun n0 -> ((Coq_ty.Coq_bvec n0),((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec n0))),(Coq_bvand n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvor m ->
      (match op2 with
       | Coq_bvor n ->
         f_equal_dec (fun n0 -> ((Coq_ty.Coq_bvec n0),((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec n0))),(Coq_bvor n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvxor m ->
      (match op2 with
       | Coq_bvxor n ->
         f_equal_dec (fun n0 -> ((Coq_ty.Coq_bvec n0),((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec n0))),(Coq_bvxor n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_bvapp (m1, m2) ->
      (match op2 with
       | Coq_bvapp (n1, n2) ->
         f_equal2_dec (fun m n -> ((Coq_ty.Coq_bvec m),((Coq_ty.Coq_bvec
           n),(Coq_ty.Coq_bvec (add m n)))),(Coq_bvapp (m, n))) m1 n1 m2 n2
           (eq_dec nat_EqDec m1 n1) (eq_dec nat_EqDec m2 n2)
       | _ -> Coq_right)
    | Coq_bvcons m ->
      (match op2 with
       | Coq_bvcons n ->
         f_equal_dec (fun n0 -> (Coq_ty.Coq_bool,((Coq_ty.Coq_bvec
           n0),(Coq_ty.Coq_bvec (S n0)))),(Coq_bvcons n0)) m n
           (eq_dec nat_EqDec m n)
       | _ -> Coq_right)
    | Coq_update_vector_subrange (n1, s1, l1) ->
      (match op2 with
       | Coq_update_vector_subrange (n2, s2, l2) ->
         update_vector_subrange_eq_dec tDC n1 n2 s1 s2 l1 l2
       | _ -> Coq_right)
    | Coq_relop (_UU03c3_, op3) ->
      (match op2 with
       | Coq_relop (_UU03c4_, op4) ->
         binoptel_eq_dec_relop tDC tDN tDF _UU03c3_ _UU03c4_ op3 op4
       | _ -> Coq_right)

  (** val eqdep_dec :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
      Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      coq_BinOp -> coq_BinOp -> sumbool **)

  let eqdep_dec =
    binoptel_eq_dec

  (** val eval_relop_val :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
      Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> coq_RelOp -> Coq_ty.coq_Val
      -> Coq_ty.coq_Val -> bool **)

  let eval_relop_val tDC tDN tDF _ = function
  | Coq_eq _UU03c3_0 ->
    (fun v1 v2 ->
      match eq_dec (Coq_ty.coq_Val_eq_dec tDC tDN tDF _UU03c3_0) v1 v2 with
      | Coq_left -> Coq_true
      | Coq_right -> Coq_false)
  | Coq_neq _UU03c3_0 ->
    (fun v1 v2 ->
      match eq_dec (Coq_ty.coq_Val_eq_dec tDC tDN tDF _UU03c3_0) v1 v2 with
      | Coq_left -> Coq_false
      | Coq_right -> Coq_true)
  | Coq_le -> Obj.magic Z.leb
  | Coq_lt -> Obj.magic Z.ltb
  | Coq_bvsle n -> (fun v1 v2 -> Coq_bv.sleb n (Obj.magic v1) (Obj.magic v2))
  | Coq_bvslt n -> (fun v1 v2 -> Coq_bv.sltb n (Obj.magic v1) (Obj.magic v2))
  | Coq_bvule n -> (fun v1 v2 -> Coq_bv.uleb n (Obj.magic v1) (Obj.magic v2))
  | Coq_bvult n -> (fun v1 v2 -> Coq_bv.ultb n (Obj.magic v1) (Obj.magic v2))

  (** val eval :
      Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
      Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_ty.coq_Ty -> coq_BinOp -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
      Coq_ty.coq_Val **)

  let eval tDC tDN tDF _ _ _ = function
  | Coq_plus -> Obj.magic Z.add
  | Coq_minus -> Obj.magic Z.sub
  | Coq_times -> Obj.magic Z.mul
  | Coq_land -> Obj.magic Z.coq_land
  | Coq_and ->
    Obj.magic (fun b1 b2 ->
      match b1 with
      | Coq_true -> b2
      | Coq_false -> Coq_false)
  | Coq_or ->
    (fun v1 v2 ->
      match Obj.magic v1 with
      | Coq_true -> Obj.magic Coq_true
      | Coq_false -> Obj.magic v2)
  | Coq_pair (_, _) -> Obj.magic (fun x x0 -> Datatypes.Coq_pair (x, x0))
  | Coq_cons _ -> Obj.magic (fun x x0 -> Datatypes.Coq_cons (x, x0))
  | Coq_append _ -> Obj.magic app
  | Coq_shiftr (m, n) -> (fun v1 v2 -> Obj.magic Coq_bv.shiftr m n v1 v2)
  | Coq_shiftl (m, n) -> (fun v1 v2 -> Obj.magic Coq_bv.shiftl m n v1 v2)
  | Coq_bvadd n -> (fun v1 v2 -> Obj.magic Coq_bv.add n v1 v2)
  | Coq_bvsub n -> (fun v1 v2 -> Obj.magic Coq_bv.sub n v1 v2)
  | Coq_bvmul n -> (fun v1 v2 -> Obj.magic Coq_bv.mul n v1 v2)
  | Coq_bvand n -> (fun v1 v2 -> Obj.magic Coq_bv.coq_land n v1 v2)
  | Coq_bvor n -> (fun v1 v2 -> Obj.magic Coq_bv.coq_lor n v1 v2)
  | Coq_bvxor n -> (fun v1 v2 -> Obj.magic Coq_bv.coq_lxor n v1 v2)
  | Coq_bvapp (m, n) -> (fun v1 v2 -> Obj.magic Coq_bv.app m n v1 v2)
  | Coq_bvcons m -> (fun b bs -> Obj.magic Coq_bv.cons m b bs)
  | Coq_update_vector_subrange (n, s, l) ->
    (fun v1 v2 -> Obj.magic Coq_bv.update_vector_subrange n s l v1 v2)
  | Coq_relop (_UU03c3_, op0) ->
    Obj.magic eval_relop_val tDC tDN tDF _UU03c3_ op0
 end
