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
     NArith.BinNat
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Symbolic.Instantiation
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

Module Type PartialEvaluationOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM).

  Local Notation LCtx := (NCtx LVar Ty).
  Local Notation Valuation Σ := (@Env (Binding LVar Ty) (fun xt : Binding LVar Ty => Val (@type LVar Ty xt)) Σ).

  Section WithLCtx.
    Context {Σ : LCtx}.

    Equations(noeqns) peval_append {σ} (t1 t2 : Term Σ (ty.list σ)) : Term Σ (ty.list σ) :=
    | term_val _ v1                 | term_val _ v2 := term_val (ty.list σ) (app v1 v2);
    (* TODO: recurse over the value instead *)
    | term_val _ nil                | t2 := t2;
    | term_val _ (cons v vs)        | t2 := term_binop bop.cons (term_val σ v) (term_binop bop.append (term_val (ty.list σ) vs) t2);
    | term_binop bop.cons t11 t12 | t2 := term_binop bop.cons t11 (term_binop bop.append t12 t2);
    | t1                            | t2 := term_binop bop.append t1 t2.

    Equations(noeqns) peval_binop' {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (bop.eval op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    Equations(noeqns) peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | bop.append | t1 | t2 := peval_append t1 t2;
    | op           | t1 | t2 := peval_binop' op t1 t2.

    Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) :
      forall (ι : Valuation Σ),
        inst  (peval_append t1 t2) ι =
          bop.eval bop.append (inst t1 ι) (inst t2 ι).
    Proof.
      intros ι.
      dependent elimination t1; cbn; auto.
      - dependent elimination t2; cbn; auto;
        destruct v; cbn; auto.
      - dependent elimination op; cbn; auto.
    Qed.

    Lemma peval_binop'_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      forall (ι : Valuation Σ),
        inst (peval_binop' op t1 t2) ι = bop.eval op (inst t1 ι) (inst t2 ι).
    Proof. intros ι. destruct t1, t2; cbn; auto. Qed.

    Lemma peval_binop_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      forall (ι : Valuation Σ),
        inst (peval_binop op t1 t2) ι = bop.eval op (inst t1 ι) (inst t2 ι).
    Proof.
      intros ι.
      destruct op; cbn [peval_binop];
        auto using peval_binop'_sound, peval_append_sound.
    Qed.

    Equations(noeqns) peval_neg (t : Term Σ ty.int) : Term Σ ty.int :=
    | term_val _ v := term_val ty.int (Z.opp v);
    | t            := term_neg t.

    Equations(noeqns) peval_not (t : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ v                    := term_val ty.bool (negb v);
    | term_binop (bop.relop op) t1 t2 := term_relop_neg op t1 t2;
    | t                               := term_not t.

    Equations(noeqns) peval_inl {σ1 σ2} (t : Term Σ σ1) : Term Σ (ty.sum σ1 σ2) :=
    | term_val _ v := term_val (ty.sum _ _) (@inl (Val _) (Val _) v);
    | t            := term_inl t.

    Equations(noeqns) peval_inr {σ1 σ2} (t : Term Σ σ2) : Term Σ (ty.sum σ1 σ2) :=
    | term_val _ v := term_val (ty.sum _ _) (@inr (Val _) (Val _) v);
    | t            := term_inr t.

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

    Definition peval_union {U K} (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U) :=
      match term_get_val t with
      | Some v => term_val (ty.union U) (unionv_fold U (existT K v))
      | None   => term_union U K t
      end.

    Fixpoint peval [σ] (t : Term Σ σ) : Term Σ σ :=
      match t with
      | term_var ς          => term_var ς
      | term_val _ v        => term_val _ v
      | term_binop op t1 t2 => peval_binop op (peval t1) (peval t2)
      | term_neg t          => peval_neg (peval t)
      | term_not t          => peval_not (peval t)
      | term_inl t          => peval_inl (peval t)
      | term_inr t          => peval_inr (peval t)
      | term_sext t         => peval_sext (peval t)
      | term_zext t         => peval_zext (peval t)
      | @term_tuple _ σs ts => @term_tuple _ σs (env.map (fun b => @peval b) ts)
      | term_union U K t    => peval_union (peval t)
      | @term_record _ R ts => term_record R (env.map (fun b => peval (σ := type b)) ts)
      end.

    Lemma peval_neg_sound (t : Term Σ ty.int) :
      forall (ι : Valuation Σ),
        inst (peval_neg t) ι = inst (term_neg t) ι.
    Proof. dependent elimination t; cbn; auto. Qed.

    Lemma peval_not_sound (t : Term Σ ty.bool) :
      forall (ι : Valuation Σ),
        inst (peval_not t) ι = inst (term_not t) ι.
    Proof.
      dependent elimination t; auto.
      dependent elimination op; auto.
      cbn. intros ι. now rewrite inst_term_relop_neg.
    Qed.

    Lemma peval_inl_sound {σ1 σ2} (t : Term Σ σ1) :
      forall (ι : Valuation Σ),
        inst (peval_inl (σ2 := σ2) t) ι = inst (term_inl t) ι.
    Proof. destruct t; cbn; auto. Qed.

    Lemma peval_inr_sound {σ1 σ2} (t : Term Σ σ2) :
      forall (ι : Valuation Σ),
        inst (peval_inr (σ1 := σ1) t) ι = inst (term_inr t) ι.
    Proof. destruct t; cbn; auto. Qed.

    Lemma peval_sext_sound {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
      forall (ι : Valuation Σ),
        inst (peval_sext t) ι = inst (term_sext t) ι.
    Proof.
      intros ι. unfold peval_sext.
      destruct (term_get_val_spec t); cbn; subst; easy.
    Qed.

    Lemma peval_zext_sound {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) :
      forall (ι : Valuation Σ),
        inst (peval_zext t) ι = inst (term_zext t) ι.
    Proof.
      intros ι. unfold peval_zext.
      destruct (term_get_val_spec t); cbn; subst; easy.
    Qed.

    Lemma peval_union_sound {U K} (t : Term Σ (unionk_ty U K)) :
      forall (ι : Valuation Σ),
        inst (peval_union t) ι = inst (term_union U K t) ι.
    Proof.
      intros ι. unfold peval_union.
      destruct (term_get_val_spec t); cbn; subst; reflexivity.
    Qed.

    Lemma peval_sound [σ] (t : Term Σ σ) :
      forall (ι : Valuation Σ),
        inst (peval t) ι = inst t ι.
    Proof.
      intros ι. symmetry.
      induction t; cbn - [Val];
        change (inst_term ?t ?ι) with (inst t ι).
      - reflexivity.
      - reflexivity.
      - now rewrite peval_binop_sound, IHt1, IHt2.
      - now rewrite peval_neg_sound, IHt.
      - now rewrite peval_not_sound, IHt.
      - now rewrite peval_inl_sound, IHt.
      - now rewrite peval_inr_sound, IHt.
      - now rewrite peval_sext_sound, IHt.
      - now rewrite peval_zext_sound, IHt.
      - f_equal. induction IH; cbn; f_equal; auto.
      - now rewrite peval_union_sound, IHt.
      - f_equal. induction IH; cbn; f_equal; auto.
    Qed.

    Definition pevals [Δ] : Env (Term Σ) Δ -> Env (Term Σ) Δ :=
      env.map peval.

    Lemma pevals_sound [Δ] (ts : Env (Term Σ) Δ) :
      forall (ι : Valuation Σ),
        inst (pevals ts) ι = inst ts ι.
    Proof.
      intros ι. cbv [inst pevals inst_env].
      rewrite env.map_map. apply env.map_ext.
      intros. apply peval_sound.
    Qed.

  End WithLCtx.
End PartialEvaluationOn.
