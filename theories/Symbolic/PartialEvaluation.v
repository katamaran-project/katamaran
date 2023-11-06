(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     Bool.Bool
     Classes.Morphisms
     Classes.RelationClasses
     NArith.BinNat
     ZArith.BinInt
     micromega.Lia.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Bitvector
     Symbolic.Instantiation
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.UnOps
     Syntax.Variables.

Import (notations) stdpp.base.
Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.
Local Set Equations Transparent.

Module Type PartialEvaluationOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM).

  Local Notation LCtx := (NCtx LVar Ty).
  Local Notation Valuation Σ := (Env (fun xt : Binding LVar Ty => Val (type xt)) Σ).

  Section WithLCtx.
    Context {Σ : LCtx}.

    #[local] Ltac lsolve :=
      try progress cbn;
      try (progress autorewrite with katamaran);
      try easy;
      auto with core katamaran.

    Equations(noeqns) peval_append {σ} (t1 t2 : Term Σ (ty.list σ)) : Term Σ (ty.list σ) :=
    | term_val _ v1                 | term_val _ v2 := term_val (ty.list σ) (app v1 v2);
    (* TODO: recurse over the value instead *)
    | term_val _ nil                | t2 := t2;
    | term_val _ (cons v vs)        | t2 := term_binop bop.cons (term_val σ v) (term_binop bop.append (term_val (ty.list σ) vs) t2);
    | term_binop bop.cons t11 t12 | t2 := term_binop bop.cons t11 (term_binop bop.append t12 t2);
    | t1                            | t2 := term_binop bop.append t1 t2.

    Equations(noeqns) peval_or (t1 t2 : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ true  , t2               => term_val ty.bool true
    | term_val _ false , t2               => t2
    | t1               , term_val _ true  => term_val ty.bool true
    | t1               , term_val _ false => t1
    | t1               , t2               => term_binop bop.or t1 t2.

    Equations peval_plus (t1 t2 : Term Σ ty.int) : Term Σ ty.int :=
    | term_val _ v1  , term_val _ v2    => term_val ty.int (v1 + v2)%Z
    | term_val _ 0%Z , t2               => t2
    | t1             , term_val _ 0%Z   => t1
    | t1             , term_val _ v2    => term_binop bop.plus (term_val ty.int v2) t1
    | t1             , t2               => term_binop bop.plus t1 t2.

    Equations(noeqns) peval_binop' {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (bop.eval op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    Equations(noeqns) peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | bop.append , t1 , t2 => peval_append t1 t2
    | bop.or     , t1 , t2 => peval_or t1 t2
    | bop.plus   , t1 , t2 => peval_plus t1 t2
    | op         , t1 , t2 => peval_binop' op t1 t2.

    Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) :
      peval_append t1 t2 ≡ term_binop bop.append t1 t2.
    Proof.
      depelim t1.
      - reflexivity.
      - depelim t2; cbn.
        + now destruct v.
        + now constructor.
        + now destruct v.
        + depelim op.
      - now depelim op.
      - now depelim op.
    Qed.

    Lemma peval_or_sound (t1 t2 : Term Σ ty.bool) :
      peval_or t1 t2 ≡ term_binop bop.or t1 t2.
    Proof with lsolve.
      depelim t1.
      - depelim t2... destruct v...
      - now destruct v.
      - depelim t2... destruct v...
      - depelim t2... destruct v...
    Qed.

    Lemma peval_plus_sound (t1 t2 : Term Σ ty.int) :
      peval_plus t1 t2 ≡ term_binop bop.plus t1 t2.
    Proof. funelim (peval_plus t1 t2); lsolve; intros ι; cbn; lia. Qed.

    Lemma peval_binop'_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop' op t1 t2 ≡ term_binop op t1 t2.
    Proof.
      unfold peval_binop'.
      now repeat
        match goal with
        | |- context[match ?t with _ => _ end] => destruct t
        end.
    Qed.

    Lemma peval_binop_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop op t1 t2 ≡ term_binop op t1 t2.
    Proof.
      destruct op; cbn [peval_binop];
        auto using peval_binop'_sound, peval_append_sound, peval_or_sound,
        peval_plus_sound.
    Qed.


    Equations peval_not (t : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ v                    => term_val ty.bool (negb v)
    | term_binop bop.and t1 t2        => term_binop bop.or (peval_not t1) (peval_not t2)
    | term_binop bop.or t1 t2         => term_binop bop.and (peval_not t1) (peval_not t2)
    | term_binop (bop.relop op) t1 t2 => term_relop_neg op t1 t2
    | t                               => term_unop uop.not t.

    Definition peval_unop' {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2 :=
      match term_get_val t with
      | Some v => term_val σ2 (uop.eval op v)
      | None   => term_unop op t
      end.

    Definition peval_unop {σ1 σ2} (op : UnOp σ1 σ2) : Term Σ σ1 -> Term Σ σ2 :=
      match op with
      | uop.not => peval_not
      | op      => peval_unop' op
      end.

    Lemma peval_not_sound (t : Term Σ ty.bool) :
      peval_not t ≡ term_unop uop.not t.
    Proof. funelim (peval_not t); lsolve; now apply proper_term_binop. Qed.

    Lemma peval_unop'_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop' op t ≡ term_unop op t.
    Proof. unfold peval_unop'; destruct (term_get_val_spec t); subst; easy. Qed.

    Lemma peval_unop_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop op t ≡ term_unop op t.
    Proof.
      destruct op; cbn [peval_unop];
        auto using peval_unop'_sound, peval_not_sound.
    Qed.

    Definition peval_sext {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) : Term Σ (ty.bvec n) :=
      match term_get_val t with
      | Some v => term_val (ty.bvec n) (bv.sext v)
      | None   => term_sext t
      end.

    Definition peval_zext {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) : Term Σ (ty.bvec n) :=
      match term_get_val t with
      | Some v => term_val (ty.bvec n) (bv.zext v)
      | None   => term_zext t
      end.

    Definition peval_get_slice_int {n} (t : Term Σ ty.int) : Term Σ (ty.bvec n) :=
      match term_get_val t with
      | Some v => term_val (ty.bvec n) (bv.of_Z v)
      | None   => term_get_slice_int t
      end.

    Definition peval_unsigned {n} (t : Term Σ (ty.bvec n)) : Term Σ ty.int :=
      match term_get_val t with
      | Some v => term_val ty.int (bv.unsigned v)
      | None   => term_unsigned t
      end.

    Definition peval_truncate {n} (m : nat) {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec n)) : Term Σ (ty.bvec m) :=
      match term_get_val t with
      | Some v => term_val (ty.bvec m) (bv.truncate m v)
      | None   => term_truncate m t
      end.

    Definition peval_vector_subrange {n} (s l : nat) {p : IsTrue (s + l <=? n)} (t : Term Σ (ty.bvec n)) : Term Σ (ty.bvec l) :=
      match term_get_val t with
      | Some v => term_val (ty.bvec l) (bv.vector_subrange s l v)
      | None   => term_vector_subrange s l t
      end.

    Definition peval_negate {n} (t : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
      match term_get_val t with
      | Some v => term_val (ty.bvec n) (bv.negate v)
      | None   => term_negate t
      end.

    Definition peval_union {U K} (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U) :=
      match term_get_val t with
      | Some v => term_val (ty.union U) (unionv_fold U (existT K v))
      | None   => term_union U K t
      end.

    Import option.notations.
    Fixpoint peval_record' {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) {struct ts} : option (NamedEnv Val rfs) :=
      match ts with
      | env.nil         => Some [env]
      | env.snoc ts _ t => vs <- peval_record' ts ;;
                           v  <- term_get_val t ;;
                           Some (env.snoc vs _ v)
      end.

    Definition peval_record R (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R) :=
      match peval_record' ts with
      | Some a => term_val (ty.record R) (recordv_fold R a)
      | None => term_record R ts
      end.

    Fixpoint peval [σ] (t : Term Σ σ) : Term Σ σ :=
      match t with
      | term_var ς                 => term_var ς
      | term_val _ v               => term_val _ v
      | term_binop op t1 t2        => peval_binop op (peval t1) (peval t2)
      | term_unop op t             => peval_unop op (peval t)
      | term_sext t                => peval_sext (peval t)
      | term_zext t                => peval_zext (peval t)
      | term_get_slice_int t       => peval_get_slice_int (peval t)
      | term_unsigned t            => peval_unsigned (peval t)
      | term_truncate m t          => peval_truncate m (peval t)
      | term_vector_subrange s l t => peval_vector_subrange s l (peval t)
      | term_negate t              => peval_negate (peval t)
      | term_tuple ts              => term_tuple (env.map (fun b => @peval b) ts)
      | term_union U K t           => peval_union (peval t)
      | term_record R ts           => peval_record R (env.map (fun b => peval (σ := type b)) ts)
      end.

    Lemma peval_sext_sound {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
      peval_sext (p := p) t ≡ term_sext t.
    Proof. unfold peval_sext. destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_zext_sound {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
      peval_zext (p := p) t ≡ term_zext t.
    Proof. unfold peval_zext. destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_get_slice_int_sound {n} (t : Term Σ ty.int) :
      @peval_get_slice_int n t ≡ term_get_slice_int t.
    Proof. unfold peval_get_slice_int; destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_unsigned_sound {n} (t : Term Σ (ty.bvec n)) :
      @peval_unsigned n t ≡ term_unsigned t.
    Proof. unfold peval_unsigned; destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_truncate_sound {n} (m : nat) {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec n)) :
      @peval_truncate n m p t ≡ term_truncate m t.
    Proof. unfold peval_truncate; destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_vector_subrange_sound {n} (s l : nat) {p : IsTrue (s + l <=? n)} (t : Term Σ (ty.bvec n)) :
      @peval_vector_subrange n s l p t ≡ term_vector_subrange s l t.
    Proof. unfold peval_vector_subrange; destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_negate_sound {n} (t : Term Σ (ty.bvec n)) :
      peval_negate t ≡ term_negate t.
    Proof. unfold peval_negate; destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_union_sound {U K} (t : Term Σ (unionk_ty U K)) :
      peval_union t ≡ term_union U K t.
    Proof. unfold peval_union. destruct (term_get_val_spec t); now subst. Qed.

    Lemma peval_record'_sound {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) :
      option.wlp (fun vs => forall ι, inst ts ι = vs) (peval_record' ts).
    Proof.
      induction ts; cbn.
      - now constructor.
      - rewrite option.wlp_bind. revert IHts.
        apply option.wlp_monotonic. intros vs IHvs.
        rewrite option.wlp_bind. generalize (term_get_val_spec db).
        apply option.wlp_monotonic. intros v IHv. constructor.
        intros ι. specialize (IHvs ι). subst. reflexivity.
    Qed.

    Lemma peval_record_sound {R} ts :
      peval_record R ts ≡ term_record R ts.
    Proof.
      unfold peval_record. destruct (peval_record'_sound ts); [|reflexivity].
      intros ι; cbn. now f_equal.
    Qed.

    Lemma peval_sound [σ] (t : Term Σ σ) :
      peval t ≡ t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - reflexivity.
      - etransitivity; [apply peval_binop_sound|now apply proper_term_binop].
      - etransitivity; [apply peval_unop_sound|now apply proper_term_unop].
      - etransitivity; [apply peval_sext_sound |now apply proper_term_sext].
      - etransitivity; [apply peval_zext_sound |now apply proper_term_zext].
      - etransitivity; [apply peval_get_slice_int_sound |now apply proper_term_get_slice_int].
      - etransitivity; [apply peval_unsigned_sound |now apply proper_term_unsigned].
      - etransitivity; [apply peval_truncate_sound |now apply proper_term_truncate].
      - etransitivity; [apply peval_vector_subrange_sound |now apply proper_term_vector_subrange].
      - etransitivity; [apply peval_negate_sound |now apply proper_term_negate].
      - apply proper_term_tuple.
        induction IH; [reflexivity|]; cbn.
        now apply proper_env_snoc.
      - etransitivity; [apply peval_union_sound|now apply proper_term_union].
      - rewrite peval_record_sound.
        apply proper_term_record.
        induction IH; cbn; [reflexivity|].
        now apply proper_namedenv_snoc.
    Qed.

    Definition pevals [Δ] : Env (Term Σ) Δ -> Env (Term Σ) Δ :=
      env.map peval.

    Lemma pevals_sound [Δ] (ts : Env (Term Σ) Δ) :
      pevals ts ≡ ts.
    Proof.
      induction ts; [reflexivity|]; cbn.
      apply proper_env_snoc; auto using peval_sound.
    Qed.

  End WithLCtx.
End PartialEvaluationOn.
