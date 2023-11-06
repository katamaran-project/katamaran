(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel                                          *)
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
  Arith.PeanoNat
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

Module uop.

  Import ty.

  Section WithTypeDecl.
    Context {TDC : TypeDeclKit}.

    Variant UnOp : Ty -> Ty -> Set :=
    | inl {σ1 σ2 : Ty}  : UnOp σ1 (sum σ1 σ2)
    | inr {σ1 σ2 : Ty}  : UnOp σ2 (sum σ1 σ2)
    | neg               : UnOp int int
    | not               : UnOp bool bool
    | sext {m n} {p : IsTrue (m <=? n)} : UnOp (bvec m) (bvec n)
    | zext {m n} {p : IsTrue (m <=? n)} : UnOp (bvec m) (bvec n)
    | get_slice_int {n} : UnOp int (bvec n)
    | unsigned {n}      : UnOp (bvec n) int
    | truncate {n} (m : nat) {p : IsTrue (m <=? n)} : UnOp (bvec n) (bvec m)
    | vector_subrange {n} (s l : nat) {p : IsTrue (s + l <=? n)} : UnOp (bvec n) (bvec l)
    | negate {n}        : UnOp (bvec n) (bvec n).
    Set Transparent Obligations.
    Derive Signature for UnOp.
    Derive NoConfusion for UnOp.

    Import Sigma_Notations.

    Definition UnOpTel : Set :=
      Σ i : (Σ σ1 : Ty, Ty), UnOp i.1 i.2.

    Definition unoptel_inl (σ1 σ2 : Ty) : UnOpTel :=
      ((σ1, sum σ1 σ2), inl).
    Definition unoptel_inr (σ1 σ2 : Ty) : UnOpTel :=
      ((σ2, sum σ1 σ2), inr).
    Definition unoptel_sext {m n} {p : IsTrue (m <=? n)} : UnOpTel :=
      ((bvec m, bvec n), sext).
    Definition unoptel_zext {m n} {p : IsTrue (m <=? n)} : UnOpTel :=
      ((bvec m, bvec n), sext).
    Definition unoptel_get_slice_int (n : nat) : UnOpTel :=
      ((int,bvec n), get_slice_int).
    Definition unoptel_unsigned (n : nat) : UnOpTel :=
      ((bvec n,int), unsigned).
    Definition unoptel_negate (n : nat) : UnOpTel :=
      ((bvec n,bvec n), negate).

  End WithTypeDecl.

  Section WithTypeDef.
    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.
    Import Sigma_Notations.

    Definition unoptel_eq_dec_sext {m1 n1 m2 n2}
      {p1 : IsTrue (m1 <=? n1)} {p2 : IsTrue (m2 <=? n2)} :
      dec_eq (A := UnOpTel) ((bvec m1, bvec n1), sext) ((bvec m2, bvec n2), sext).
    Proof.
      destruct (eq_dec m1 m2). destruct (eq_dec n1 n2).
      { subst. left. f_equal. f_equal. apply IsTrue.proof_irrelevance. }
      all: right; intros Heq; now dependent elimination Heq.
    Defined.

    Definition unoptel_eq_dec_zext {m1 n1 m2 n2}
      {p1 : IsTrue (m1 <=? n1)} {p2 : IsTrue (m2 <=? n2)} :
      dec_eq (A := UnOpTel) ((bvec m1, bvec n1), zext) ((bvec m2, bvec n2), zext).
    Proof.
      destruct (eq_dec m1 m2). destruct (eq_dec n1 n2).
      { subst. left. f_equal. f_equal. apply IsTrue.proof_irrelevance. }
      all: right; intros Heq; now dependent elimination Heq.
    Defined.

    Definition unoptel_eq_dec_truncate {m1 n1 m2 n2}
      {p1 : IsTrue (m1 <=? n1)} {p2 : IsTrue (m2 <=? n2)} :
      dec_eq (A := UnOpTel)
        ((bvec n1, bvec m1), truncate m1)
        ((bvec n2, bvec m2), truncate m2).
    Proof.
      destruct (eq_dec n1 n2). destruct (eq_dec m1 m2).
      { subst. left. f_equal. f_equal. apply IsTrue.proof_irrelevance. }
      all: right; intros Heq; now dependent elimination Heq.
    Defined.

    Definition unoptel_eq_dec_subrange {n1 s1 l1 n2 s2 l2}
      {p1 : IsTrue (s1 + l1 <=? n1)} {p2 : IsTrue (s2 + l2 <=? n2)} :
      dec_eq (A := UnOpTel)
        ((bvec n1, bvec l1), vector_subrange s1 l1)
        ((bvec n2, bvec l2), vector_subrange s2 l2).
    Proof.
      destruct (eq_dec n1 n2). destruct (eq_dec l1 l2). destruct (eq_dec s1 s2).
      { subst. left. f_equal. f_equal. apply IsTrue.proof_irrelevance. }
      all: right; intros Heq; now dependent elimination Heq.
    Defined.

    Definition unoptel_eq_dec {σ1 σ2 τ1 τ2 : Ty}
      (op1 : UnOp σ1 σ2) (op2 : UnOp τ1 τ2) :
      dec_eq (A := UnOpTel) ((σ1,σ2),op1) ((τ1,τ2),op2) :=
      let ninv := @noConfusion_inv UnOpTel (NoConfusionPackage_UnOp) in
      match op1 , op2 with
      | @inl _ σ1 σ2 , @inl _ τ1 τ2  =>
          f_equal2_dec unoptel_inl (ninv _ _) (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | @inr _ σ1 σ2 , @inr _ τ1 τ2  =>
          f_equal2_dec unoptel_inr (ninv _ _) (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | neg  , neg  => left eq_refl
      | not  , not  => left eq_refl
      | sext , sext => unoptel_eq_dec_sext
      | zext , zext => unoptel_eq_dec_zext
      | @get_slice_int _ m , @get_slice_int _ n =>
          f_equal_dec unoptel_get_slice_int (ninv _ _) (eq_dec m n)
      | @unsigned _ m , @unsigned _ n =>
          f_equal_dec unoptel_unsigned (ninv _ _) (eq_dec m n)
      | truncate m1 , truncate m2 => unoptel_eq_dec_truncate
      | vector_subrange s1 l1 , vector_subrange s2 l2 => unoptel_eq_dec_subrange
      | @negate _ m , @negate _ n =>
          f_equal_dec unoptel_negate (ninv _ _) (eq_dec m n)
      | _ , _ => right (ninv _ _)
      end.

    Inductive OpEq {σ1 σ2} (op1 : UnOp σ1 σ2) : forall {τ1 τ2}, UnOp τ1 τ2 -> Prop :=
    | opeq_refl : OpEq op1 op1.
    Derive Signature for OpEq.
    Global Arguments opeq_refl {_ _ _}.

    Lemma eqdep_dec {σ1 σ2 τ1 τ2} (op1 : UnOp σ1 σ2) (op2 : UnOp τ1 τ2) :
      {OpEq op1 op2} + {~ OpEq op1 op2}.
    Proof.
      destruct (unoptel_eq_dec op1 op2).
      - left. dependent elimination e. constructor.
      - right. intro e. apply n. dependent elimination e. reflexivity.
    Defined.

    Local Set Equations With UIP.
    Instance eq_dec_unop {σ1 σ2} : EqDec (UnOp σ1 σ2).
    Proof.
      intros x y.
      destruct (unoptel_eq_dec x y) as [p|p].
      - left. dependent elimination p. reflexivity.
      - right. congruence.
    Defined.

    Definition eval {σ1 σ2 : Ty} (op : UnOp σ1 σ2) : Val σ1 -> Val σ2 :=
      match op in UnOp σ1 σ2 return Val σ1 -> Val σ2 with
      | inl                 => Datatypes.inl
      | inr                 => Datatypes.inr
      | neg                 => Z.opp
      | not                 => negb
      | sext                => fun v => bv.sext v
      | zext                => fun v => bv.zext v
      | get_slice_int       => bv.of_Z
      | unsigned            => fun v => bv.unsigned v
      | truncate m          => fun v => bv.truncate m v
      | vector_subrange s l => bv.vector_subrange s l
      | negate              => bv.negate
      end.

  End WithTypeDef.
  #[export] Existing Instance eq_dec_unop.

End uop.
#[export] Existing Instance uop.eq_dec_unop.
Export uop (UnOp).
