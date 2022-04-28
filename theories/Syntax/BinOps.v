(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Bool.Bool
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Bitvector
     Context
     Prelude
     Syntax.TypeDecl.

Import ctx.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

Module Type BinOpsOn (Import TD : TypeDecl).

  Inductive BinOp : Ty -> Ty -> Ty -> Set :=
  | binop_plus              : BinOp ty_int ty_int ty_int
  | binop_times             : BinOp ty_int ty_int ty_int
  | binop_minus             : BinOp ty_int ty_int ty_int
  | binop_land              : BinOp ty_int ty_int ty_int
  | binop_eq {σ}            : BinOp σ σ ty_bool
  | binop_le                : BinOp ty_int ty_int ty_bool
  | binop_lt                : BinOp ty_int ty_int ty_bool
  | binop_ge                : BinOp ty_int ty_int ty_bool
  | binop_gt                : BinOp ty_int ty_int ty_bool
  | binop_and               : BinOp ty_bool ty_bool ty_bool
  | binop_or                : BinOp ty_bool ty_bool ty_bool
  | binop_pair {σ1 σ2 : Ty} : BinOp σ1 σ2 (ty_prod σ1 σ2)
  | binop_cons {σ : Ty}     : BinOp σ (ty_list σ) (ty_list σ)
  | binop_append {σ : Ty}   : BinOp (ty_list σ) (ty_list σ) (ty_list σ)
  | binop_tuple_snoc {σs σ} : BinOp (ty_tuple σs) σ (ty_tuple (σs ▻ σ))
  | binop_bvadd {n}         : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
  | binop_bvsub {n}         : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
  | binop_bvmul {n}         : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
  | binop_bvand {n}         : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
  | binop_bvor {n}          : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
  | binop_bvxor {n}         : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
  | binop_bvapp {m n}       : BinOp (ty_bvec m) (ty_bvec n) (ty_bvec (m + n))
  | binop_bvcons {m}        : BinOp (ty_bit) (ty_bvec m) (ty_bvec (S m))
  .

  Derive Signature NoConfusion for BinOp.

  Import Sigma_Notations.

  Definition BinOpTel : Set :=
    Σ i : (Σ σ1 σ2 : Ty, Ty), BinOp i.1 (i.2).1 (i.2).2.

  Definition binoptel_pair (σ1 σ2 : Ty) : BinOpTel :=
    ((σ1, σ2, ty_prod σ1 σ2), binop_pair).
  Definition binoptel_cons (σ : Ty) : BinOpTel :=
    ((σ, ty_list σ, ty_list σ), binop_cons).
  Definition binoptel_append (σ : Ty) : BinOpTel :=
    ((ty_list σ, ty_list σ, ty_list σ), binop_append).
  Definition binoptel_tuple_snoc (σs : Ctx Ty) (σ : Ty) : BinOpTel :=
    ((ty_tuple σs, σ, ty_tuple (σs ▻ σ)), binop_tuple_snoc).

  Definition binoptel_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3}
    (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
    dec_eq (A := BinOpTel) ((σ1,σ2,σ3),op1) ((τ1,τ2,τ3),op2) :=
    match op1 , op2 with
    | binop_plus  , binop_plus   => left eq_refl
    | binop_times , binop_times  => left eq_refl
    | binop_minus , binop_minus  => left eq_refl
    | binop_land  , binop_land   => left eq_refl
    | @binop_eq σ , @binop_eq τ  => f_equal_dec (fun σ => ((σ , σ , ty_bool) , binop_eq)) noConfusion_inv (eq_dec σ τ)
    | binop_le    , binop_le     => left eq_refl
    | binop_lt    , binop_lt     => left eq_refl
    | binop_ge    , binop_ge     => left eq_refl
    | binop_gt    , binop_gt     => left eq_refl
    | binop_and   , binop_and    => left eq_refl
    | binop_or    , binop_or     => left eq_refl
    | @binop_pair σ1 σ2 , @binop_pair τ1 τ2   =>
      f_equal2_dec binoptel_pair noConfusion_inv (eq_dec σ1 τ1) (eq_dec σ2 τ2)
    | @binop_cons σ  , @binop_cons τ   =>
      f_equal_dec binoptel_cons noConfusion_inv (eq_dec σ τ)
    | @binop_append σ , @binop_append τ   =>
      f_equal_dec binoptel_append noConfusion_inv (eq_dec σ τ)
    | @binop_tuple_snoc σs σ , @binop_tuple_snoc τs τ =>
      f_equal2_dec binoptel_tuple_snoc noConfusion_inv (eq_dec σs τs) (eq_dec σ τ)
    | @binop_bvadd m , @binop_bvadd n =>
      f_equal_dec
        (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvadd))
        noConfusion_inv (eq_dec m n)
    | @binop_bvsub m , @binop_bvsub n =>
      f_equal_dec
        (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvsub))
        noConfusion_inv (eq_dec m n)
    | @binop_bvmul m , @binop_bvmul n =>
      f_equal_dec
        (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvmul))
        noConfusion_inv (eq_dec m n)
    | @binop_bvand m , @binop_bvand n =>
      f_equal_dec
        (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvand))
        noConfusion_inv (eq_dec m n)
    | @binop_bvor m , @binop_bvor n =>
      f_equal_dec
        (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvor))
        noConfusion_inv (eq_dec m n)
    | @binop_bvxor m , @binop_bvxor n =>
      f_equal_dec
        (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvxor))
        noConfusion_inv (eq_dec m n)
    | @binop_bvapp m1 m2 , @binop_bvapp n1 n2 =>
      f_equal2_dec
        (fun m n => ((ty_bvec m, ty_bvec n, ty_bvec (m+n)), binop_bvapp))
        noConfusion_inv (eq_dec m1 n1) (eq_dec m2 n2)
    | @binop_bvcons m , @binop_bvcons n =>
      f_equal_dec
        (fun n => ((ty_bit, ty_bvec n, ty_bvec (S n)), binop_bvcons))
        noConfusion_inv (eq_dec m n)
    | _           , _            => right noConfusion_inv
    end.

  Inductive OpEq {σ1 σ2 σ3} (op1 : BinOp σ1 σ2 σ3) : forall τ1 τ2 τ3, BinOp τ1 τ2 τ3 -> Prop :=
  | opeq_refl : OpEq op1 op1.
  Derive Signature for OpEq.
  Global Arguments opeq_refl {_ _ _ _}.

  Lemma binop_eqdep_dec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
    {OpEq op1 op2} + {~ OpEq op1 op2}.
  Proof.
    destruct (binoptel_eq_dec op1 op2).
    - left. dependent elimination e. constructor.
    - right. intro e. apply n. dependent elimination e. reflexivity.
  Defined.

  Local Set Equations With UIP.
  Instance binop_eq_dec {σ1 σ2 σ3} : EqDec (BinOp σ1 σ2 σ3).
  Proof.
    intros x y.
    destruct (binoptel_eq_dec x y) as [p|p].
    - left. dependent elimination p. reflexivity.
    - right. congruence.
  Defined.

  Definition eval_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Val σ1 -> Val σ2 -> Val σ3 :=
    match op in BinOp σ1 σ2 σ3 return Val σ1 -> Val σ2 -> Val σ3 with
    | binop_plus       => Z.add
    | binop_times      => Z.mul
    | binop_minus      => Z.sub
    | binop_land       => Z.land
    | binop_eq         => Val_eqb _
    | binop_le         => Z.leb
    | binop_lt         => Z.ltb
    | binop_ge         => Z.geb
    | binop_gt         => Z.gtb
    | binop_and        => andb
    | binop_or         => fun v1 v2 => orb v1 v2
    | binop_pair       => pair
    | binop_cons       => cons
    | binop_append     => app
    | binop_tuple_snoc => pair
    | binop_bvadd      => fun v1 v2 => bv.add v1 v2
    | binop_bvsub      => fun v1 v2 => bv.sub v1 v2
    | binop_bvmul      => fun v1 v2 => bv.mul v1 v2
    | binop_bvand      => fun v1 v2 => bv.land v1 v2
    | binop_bvor       => fun v1 v2 => bv.lor v1 v2
    | binop_bvxor      => fun v1 v2 => bv.lxor v1 v2
    | binop_bvapp      => fun v1 v2 => bv.app v1 v2
    | binop_bvcons     => fun b bs => bv.cons (Bit_eqb b bitone) bs
    end.

End BinOpsOn.
