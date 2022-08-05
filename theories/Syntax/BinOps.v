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

Module bop.

  Import ty.

  Section WithTypeDecl.
    Context {TDC : TypeDeclKit}.

    Inductive BinOp : Ty -> Ty -> Ty -> Set :=
    | plus              : BinOp int int int
    | times             : BinOp int int int
    | minus             : BinOp int int int
    | land              : BinOp int int int
    | eq {σ}            : BinOp σ σ bool
    | le                : BinOp int int bool
    | lt                : BinOp int int bool
    | ge                : BinOp int int bool
    | gt                : BinOp int int bool
    | and               : BinOp bool bool bool
    | or                : BinOp bool bool bool
    | pair {σ1 σ2 : Ty} : BinOp σ1 σ2 (prod σ1 σ2)
    | cons {σ : Ty}     : BinOp σ (list σ) (list σ)
    | append {σ : Ty}   : BinOp (list σ) (list σ) (list σ)
    | tuple_snoc {σs σ} : BinOp (tuple σs) σ (tuple (σs ▻ σ))
    | bvadd {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvsub {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvmul {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvand {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvor {n}          : BinOp (bvec n) (bvec n) (bvec n)
    | bvxor {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvapp {m n}       : BinOp (bvec m) (bvec n) (bvec (m + n))
    | bvcons {m}        : BinOp (bool) (bvec m) (bvec (S m))
    .
    Set Transparent Obligations.
    Derive Signature NoConfusion for BinOp.

    Import Sigma_Notations.

    Definition BinOpTel : Set :=
      Σ i : (Σ σ1 σ2 : Ty, Ty), BinOp i.1 (i.2).1 (i.2).2.

    Definition binoptel_pair (σ1 σ2 : Ty) : BinOpTel :=
      ((σ1, σ2, prod σ1 σ2), pair).
    Definition binoptel_cons (σ : Ty) : BinOpTel :=
      ((σ, list σ, list σ), cons).
    Definition binoptel_append (σ : Ty) : BinOpTel :=
      ((list σ, list σ, list σ), append).
    Definition binoptel_tuple_snoc (σs : Ctx Ty) (σ : Ty) : BinOpTel :=
      ((tuple σs, σ, tuple (σs ▻ σ)), tuple_snoc).
    Definition binoptel_eq (σ : Ty) : BinOpTel :=
      ((σ, σ, bool), eq).
    Definition binoptel_bvadd n : BinOpTel :=
      ((bvec n, bvec n, bvec n), bvadd).

  End WithTypeDecl.

  Section WithTypeDef.
    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.
    Import Sigma_Notations.

    Definition binoptel_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3 : Ty}
      (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      dec_eq (A := BinOpTel) ((σ1,σ2,σ3),op1) ((τ1,τ2,τ3),op2) :=
      match op1 , op2 with
      | plus  , plus   => left eq_refl
      | times , times  => left eq_refl
      | minus , minus  => left eq_refl
      | land  , land   => left eq_refl
      | @eq _ σ , @eq _ τ  =>
        f_equal_dec binoptel_eq noConfusion_inv (eq_dec σ τ)
      | le    , le     => left eq_refl
      | lt    , lt     => left eq_refl
      | ge    , ge     => left eq_refl
      | gt    , gt     => left eq_refl
      | and   , and    => left eq_refl
      | or    , or     => left eq_refl
      | @pair _ σ1 σ2 , @pair _ τ1 τ2   =>
        f_equal2_dec binoptel_pair noConfusion_inv (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | @cons _ σ  , @cons _ τ   =>
        f_equal_dec binoptel_cons noConfusion_inv (eq_dec σ τ)
      | @append _ σ , @append _ τ   =>
        f_equal_dec binoptel_append noConfusion_inv (eq_dec σ τ)
      | @tuple_snoc _ σs σ , @tuple_snoc _ τs τ =>
        f_equal2_dec binoptel_tuple_snoc noConfusion_inv (eq_dec σs τs) (eq_dec σ τ)
      | @bvadd _ m , @bvadd _ n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvadd))
          noConfusion_inv (eq_dec m n)
      | @bvsub _ m , @bvsub _ n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvsub))
          noConfusion_inv (eq_dec m n)
      | @bvmul _ m , @bvmul _ n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvmul))
          noConfusion_inv (eq_dec m n)
      | @bvand _ m , @bvand _ n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvand))
          noConfusion_inv (eq_dec m n)
      | @bvor _ m , @bvor _ n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvor))
          noConfusion_inv (eq_dec m n)
      | @bvxor _ m , @bvxor _ n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvxor))
          noConfusion_inv (eq_dec m n)
      | @bvapp _ m1 m2 , @bvapp _ n1 n2 =>
        f_equal2_dec
          (fun m n => ((bvec m, bvec n, bvec (m+n)), bvapp))
          noConfusion_inv (eq_dec m1 n1) (eq_dec m2 n2)
      | @bvcons _ m , @bvcons _ n =>
        f_equal_dec
          (fun n => ((bool, bvec n, bvec (S n)), bvcons))
          noConfusion_inv (eq_dec m n)
      | _           , _            => right noConfusion_inv
      end.

    Inductive OpEq {σ1 σ2 σ3} (op1 : BinOp σ1 σ2 σ3) : forall {τ1 τ2 τ3}, BinOp τ1 τ2 τ3 -> Prop :=
    | opeq_refl : OpEq op1 op1.
    Derive Signature for OpEq.
    Global Arguments opeq_refl {_ _ _ _}.

    Lemma eqdep_dec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      {OpEq op1 op2} + {~ OpEq op1 op2}.
    Proof.
      destruct (binoptel_eq_dec op1 op2).
      - left. dependent elimination e. constructor.
      - right. intro e. apply n. dependent elimination e. reflexivity.
    Defined.

    Local Set Equations With UIP.
    Instance eq_dec_binop {σ1 σ2 σ3} : EqDec (BinOp σ1 σ2 σ3).
    Proof.
      intros x y.
      destruct (binoptel_eq_dec x y) as [p|p].
      - left. dependent elimination p. reflexivity.
      - right. congruence.
    Defined.

    Definition eval {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Val σ1 -> Val σ2 -> Val σ3 :=
      match op in BinOp σ1 σ2 σ3 return Val σ1 -> Val σ2 -> Val σ3 with
      | plus       => Z.add
      | times      => Z.mul
      | minus      => Z.sub
      | land       => Z.land
      | eq         => Val_eqb _
      | le         => Z.leb
      | lt         => Z.ltb
      | ge         => Z.geb
      | gt         => Z.gtb
      | and        => andb
      | or         => fun v1 v2 => orb v1 v2
      | pair       => Datatypes.pair
      | cons       => List.cons
      | append     => app
      | tuple_snoc => Datatypes.pair
      | bvadd      => fun v1 v2 => bv.add v1 v2
      | bvsub      => fun v1 v2 => bv.sub v1 v2
      | bvmul      => fun v1 v2 => bv.mul v1 v2
      | bvand      => fun v1 v2 => bv.land v1 v2
      | bvor       => fun v1 v2 => bv.lor v1 v2
      | bvxor      => fun v1 v2 => bv.lxor v1 v2
      | bvapp      => fun v1 v2 => bv.app v1 v2
      | bvcons     => fun b bs => bv.cons b bs
      end.

  End WithTypeDef.
  #[export] Existing Instance eq_dec_binop.

End bop.
#[export] Existing Instance bop.eq_dec_binop.
Export bop ( BinOp ).
