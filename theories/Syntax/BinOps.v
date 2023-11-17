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

Module bop.

  Import ty.

  Section WithTypes.
    Context {TDC : TypeDeclKit}.

    Variant RelOp : Ty -> Set :=
    | eq {σ}            : RelOp σ
    | neq {σ}           : RelOp σ
    | le                : RelOp int
    | lt                : RelOp int
    | bvsle {n}         : RelOp (bvec n)
    | bvslt {n}         : RelOp (bvec n)
    | bvule {n}         : RelOp (bvec n)
    | bvult {n}         : RelOp (bvec n).

    Variant BinOp : Ty -> Ty -> Ty -> Set :=
    | plus              : BinOp int int int
    | times             : BinOp int int int
    | minus             : BinOp int int int
    | land              : BinOp int int int
    | and               : BinOp bool bool bool
    | or                : BinOp bool bool bool
    | pair {σ1 σ2 : Ty} : BinOp σ1 σ2 (prod σ1 σ2)
    | cons {σ : Ty}     : BinOp σ (list σ) (list σ)
    | append {σ : Ty}   : BinOp (list σ) (list σ) (list σ)
    | shiftr {m n}      : BinOp (bvec m) (bvec n) (bvec m)
    | shiftl {m n}      : BinOp (bvec m) (bvec n) (bvec m)
    | bvadd {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvsub {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvmul {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvand {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvor {n}          : BinOp (bvec n) (bvec n) (bvec n)
    | bvxor {n}         : BinOp (bvec n) (bvec n) (bvec n)
    | bvapp {m n}       : BinOp (bvec m) (bvec n) (bvec (m + n))
    | bvcons {m}        : BinOp (bool) (bvec m) (bvec (S m))
    | hl_pair           : BinOp hl_val hl_val hl_val
    | relop {σ} (r : RelOp σ) : BinOp σ σ bool
    .
    Set Transparent Obligations.
    Derive Signature NoConfusion for BinOp RelOp.
    Derive NoConfusionHom for RelOp.
    Derive EqDec for RelOp.

    #[local] Notation "( x , .. , y , z )" :=
      (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..).

    Definition RelOpTel : Set :=
      sigma RelOp_sig.
    Definition BinOpTel : Set :=
      sigma BinOp_sig.

    Definition binoptel_pair (σ1 σ2 : Ty) : BinOpTel :=
      ((σ1, σ2, prod σ1 σ2), pair).
    Definition binoptel_cons (σ : Ty) : BinOpTel :=
      ((σ, list σ, list σ), cons).
    Definition binoptel_append (σ : Ty) : BinOpTel :=
      ((list σ, list σ, list σ), append).
    Definition binoptel_shiftr (m n : nat) : BinOpTel :=
      ((bvec m, bvec n, bvec m), shiftr).
    Definition binoptel_shiftl (m n : nat) : BinOpTel :=
      ((bvec m, bvec n, bvec m), shiftl).

    Definition is_eq {σ} (op : RelOp σ) : Datatypes.bool :=
      match op with eq => true | _ => false end.

    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.

    Definition reloptel_eq_dec {σ τ : Ty} (op1 : RelOp σ) (op2 : RelOp τ) :
      @dec_eq RelOpTel (σ,op1) (τ,op2) :=
      let ninv := @noConfusion_inv RelOpTel (NoConfusionPackage_RelOp) in
      match op1 , op2 with
      | @eq σ    , @eq  τ   => f_equal_dec (fun ρ => (ρ, eq)) (ninv _ _) (eq_dec σ τ)
      | @neq σ   , @neq τ   => f_equal_dec (fun ρ => (ρ, neq)) (ninv _ _) (eq_dec σ τ)
      | le       , le       => left eq_refl
      | lt       , lt       => left eq_refl
      | @bvsle m , @bvsle n => f_equal_dec (fun n => (bvec n, bvsle)) (ninv _ _) (eq_dec m n)
      | @bvslt m , @bvslt n => f_equal_dec (fun n => (bvec n, bvslt)) (ninv _ _) (eq_dec m n)
      | @bvule m , @bvule n => f_equal_dec (fun n => (bvec n, bvule)) (ninv _ _) (eq_dec m n)
      | @bvult m , @bvult n => f_equal_dec (fun n => (bvec n, bvult)) (ninv _ _) (eq_dec m n)
      | _        , _        => right (ninv _ _)
      end.

    Definition binoptel_eq_dec_relop {σ τ} (op1 : RelOp σ) (op2 : RelOp τ) :
      @dec_eq BinOpTel ((σ, σ, bool), relop op1) ((τ, τ, bool), relop op2) :=
      match reloptel_eq_dec op1 op2 with
      | left e  => left (f_equal2' (fun σ op => ((σ, σ, bool), relop op)) e)
      | right n =>
          right (fun e : ((σ, σ, bool), relop op1) = ((τ, τ, bool), relop op2) =>
                   n (noConfusion_inv e))
      end.

    Definition binoptel_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3 : Ty}
      (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      dec_eq (A := BinOpTel) ((σ1,σ2,σ3),op1) ((τ1,τ2,τ3),op2) :=
      let ninv := @noConfusion_inv BinOpTel (NoConfusionPackage_BinOp) in
      match op1 , op2 with
      | plus  , plus   => left eq_refl
      | times , times  => left eq_refl
      | minus , minus  => left eq_refl
      | land  , land   => left eq_refl
      | and   , and    => left eq_refl
      | or    , or     => left eq_refl
      | @pair σ1 σ2 , @pair τ1 τ2   =>
        f_equal2_dec binoptel_pair (ninv _ _) (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | @cons σ  , @cons τ   =>
        f_equal_dec binoptel_cons (ninv _ _) (eq_dec σ τ)
      | @append σ , @append τ   =>
        f_equal_dec binoptel_append (ninv _ _) (eq_dec σ τ)
      | @shiftr m n , @shiftr p q =>
          f_equal2_dec binoptel_shiftr (ninv _ _) (eq_dec m p) (eq_dec n q)
      | @shiftl m n , @shiftl p q =>
          f_equal2_dec binoptel_shiftl (ninv _ _) (eq_dec m p) (eq_dec n q)
      | @bvadd m , @bvadd n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvadd))
          (ninv _ _) (eq_dec m n)
      | @bvsub m , @bvsub n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvsub))
          (ninv _ _) (eq_dec m n)
      | @bvmul m , @bvmul n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvmul))
          (ninv _ _) (eq_dec m n)
      | @bvand m , @bvand n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvand))
          (ninv _ _) (eq_dec m n)
      | @bvor m , @bvor n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvor))
          (ninv _ _) (eq_dec m n)
      | @bvxor m , @bvxor n =>
        f_equal_dec
          (fun n => ((bvec n, bvec n, bvec n), bvxor))
          (ninv _ _) (eq_dec m n)
      | @bvapp m1 m2 , @bvapp n1 n2 =>
        f_equal2_dec
          (fun m n => ((bvec m, bvec n, bvec (m+n)), bvapp))
          (ninv _ _) (eq_dec m1 n1) (eq_dec m2 n2)
      | @bvcons m , @bvcons n =>
        f_equal_dec
          (fun n => ((bool, bvec n, bvec (S n)), bvcons))
          (ninv _ _) (eq_dec m n)
      | hl_pair , hl_pair => left eq_refl
      | @relop σ op1 , @relop τ op2 =>
        binoptel_eq_dec_relop op1 op2
      | _           , _            => right (ninv _ _)
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

    Definition eval_relop_val {σ} (op : RelOp σ) : Val σ -> Val σ -> Datatypes.bool :=
      match op with
      | eq    => fun v1 v2 => if eq_dec v1 v2 then true else false
      | neq   => fun v1 v2 => if eq_dec v1 v2 then false else true
      | le    => Z.leb
      | lt    => Z.ltb
      | bvsle => fun v1 v2 => bv.sleb v1 v2
      | bvslt => fun v1 v2 => bv.sltb v1 v2
      | bvule => fun v1 v2 => bv.uleb v1 v2
      | bvult => fun v1 v2 => bv.ultb v1 v2
      end.

    Definition eval_relop_prop
      (* Force TypeDefKit into the context, so that the eval_relop_equiv lemma
         below doesn't leave unsolved existentials when used in rewriting. *)
      {TDF : TypeDefKit TDN} {σ} (op : RelOp σ) : Val σ -> Val σ -> Prop :=
      match op with
      | eq    => fun v1 v2 => v1 = v2
      | neq   => fun v1 v2 => v1 <> v2
      | le    => fun v1 v2 => (v1 <= v2)%Z
      | lt    => fun v1 v2 => (v1 < v2)%Z
      | bvsle => fun v1 v2 => bv.sle v1 v2
      | bvslt => fun v1 v2 => bv.slt v1 v2
      | bvule => fun v1 v2 => bv.ule v1 v2
      | bvult => fun v1 v2 => bv.ult v1 v2
      end.

    Lemma eval_relop_val_spec {σ} (op : RelOp σ) (v1 v2 : Val σ) :
      reflect (eval_relop_prop op v1 v2) (eval_relop_val op v1 v2).
    Proof with constructor; auto.
      destruct op; cbn.
      - destruct eq_dec...
      - destruct eq_dec...
      - apply Z.leb_spec0.
      - apply Z.ltb_spec0.
      - apply bv.sle_spec.
      - apply bv.slt_spec.
      - apply bv.ule_spec.
      - apply bv.ult_spec.
    Qed.

    Lemma eval_relop_equiv {σ} (op : RelOp σ) (v1 v2 : Val σ) :
      eval_relop_prop op v1 v2 <-> eval_relop_val op v1 v2 = true.
    Proof. now destruct (eval_relop_val_spec op v1 v2). Qed.

    Definition eval {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Val σ1 -> Val σ2 -> Val σ3 :=
      match op in BinOp σ1 σ2 σ3 return Val σ1 -> Val σ2 -> Val σ3 with
      | plus       => Z.add
      | times      => Z.mul
      | minus      => Z.sub
      | land       => Z.land
      | and        => andb
      | or         => fun v1 v2 => orb v1 v2
      | pair       => Datatypes.pair
      | cons       => List.cons
      | shiftr     => fun v1 v2 => bv.shiftr v1 v2
      | shiftl     => fun v1 v2 => bv.shiftl v1 v2
      | append     => app
      | bvadd      => fun v1 v2 => bv.add v1 v2
      | bvsub      => fun v1 v2 => bv.sub v1 v2
      | bvmul      => fun v1 v2 => bv.mul v1 v2
      | bvand      => fun v1 v2 => bv.land v1 v2
      | bvor       => fun v1 v2 => bv.lor v1 v2
      | bvxor      => fun v1 v2 => bv.lxor v1 v2
      | bvapp      => fun v1 v2 => bv.app v1 v2
      | bvcons     => fun b bs => bv.cons b bs
      | hl_pair    => lang.heap_lang.PairV
      | relop op   => eval_relop_val op
      end.

  End WithTypes.
  #[export] Existing Instance eq_dec_binop.

End bop.
#[export] Existing Instance bop.eq_dec_binop.
Export bop ( BinOp, RelOp ).
