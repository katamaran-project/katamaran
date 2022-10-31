(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
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
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     NArith.BinNat
     Relations.Relation_Definitions
     ZArith.BinInt.

From Katamaran Require Import
     Base
     Prelude
     Signature
     Symbolic.Worlds.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Equations Transparent.

Module Type SolverOn (Import B : Base) (Import SIG : Signature B).

  Module Solver.

    Open Scope list_scope.
    Import List.ListNotations.
    Import option.notations.

    Definition RFormula {Σ} : relation (Formula Σ) :=
      fun x y => forall ι : Valuation Σ, inst x ι <-> inst y ι.
    Definition RFormulas {Σ} : relation (PathCondition Σ) :=
      fun xs ys => forall ι : Valuation Σ, instprop xs ι <-> instprop ys ι.
    Definition ROFormulas {Σ} : relation (option (PathCondition Σ)) :=
      fun oxs oys =>
        forall ι : Valuation Σ,
          option.wp (fun xs => instprop xs ι) oxs <->
          option.wp (fun ys => instprop ys ι) oys.
    #[local] Notation "x ~ y" := (RFormula x y) (at level 90).
    #[local] Notation "x ≈ y" := (RFormulas x y) (at level 90).
    #[local] Notation "x ≋ y" := (ROFormulas x y) (at level 90).

    #[local] Hint Rewrite @inst_formula_relop_neg @inst_pathcondition_nil @inst_pathcondition_snoc @inst_pathcondition_cat : katamaran.
    #[local] Hint Rewrite @inst_formula_eqs_ctx @inst_formula_eqs_nctx @envrec.of_env_inj
      @recordv_fold_inj @unionv_fold_inj : katamaran.
    #[local] Hint Rewrite @bop.eval_relop_equiv : katamaran.
    #[local] Hint Rewrite <- and_assoc : katamaran.

    #[local] Instance rformula_equiv {Σ} : Equivalence (@RFormula Σ).
    Proof.
      constructor.
      - unfold Reflexive. easy.
      - unfold Symmetric. easy.
      - intros x y z xy yz ι. now transitivity (inst y ι).
    Qed.

    #[local] Instance rformulas_equiv {Σ} : Equivalence (@RFormulas Σ).
    Proof.
      constructor.
      - unfold Reflexive. easy.
      - unfold Symmetric. easy.
      - intros x y z xy yz ι. now transitivity (instprop y ι).
    Qed.

    #[local] Instance roformulas_equiv {Σ} : Equivalence (@ROFormulas Σ).
    Proof.
      constructor.
      - unfold Reflexive. easy.
      - unfold Symmetric. easy.
      - intros x y z xy yz ι.
        now transitivity (option.wp (fun xs => instprop xs ι) y).
    Qed.

    #[local] Instance proper_snoc [Σ] :
      Proper (RFormulas ==> @RFormula Σ ==> RFormulas) ctx.snoc.
    Proof. intros ? ? ? ? ? ? ?. cbn. now apply and_iff_morphism. Qed.

    Lemma proper_some [Σ] :
      Proper (@RFormulas Σ ==> @ROFormulas Σ) Some.
    Proof. intros xs ys Hxys ι. now rewrite ?option.wp_some. Qed.

    Lemma proper_formula_user [Σ p] :
      Proper (SEEnv Σ (𝑷_Ty p) ==> @RFormula Σ) (formula_user p).
    Proof. intros xs ys [xys] ι; cbn; now rewrite xys. Qed.

    Lemma proper_formula_bool [Σ] :
      Proper (SETerm Σ ty.bool ==> @RFormula Σ) formula_bool.
    Proof. intros s t [e] ι; cbn; now rewrite e. Qed.

    Lemma proper_formula_relop [Σ σ] (rop : RelOp σ) :
      Proper (SETerm Σ σ ==> SETerm Σ σ ==> RFormula) (formula_relop rop).
    Proof. intros s1 t1 [e1] s2 t2 [e2] ι; cbn; now rewrite e1, e2. Qed.

    Local Ltac arw :=
      repeat
        (try progress cbn
           [bop.eval bop.eval_relop_val bop.eval_relop_prop
            Val inst inst_formula inst_term] in *;
         autorewrite with katamaran in *;
         repeat
           match goal with
           | |- Some ?x ≋ Some ?y =>
               apply proper_some
           | |- ?k ▻ _ ≈ ?k ▻ _ => apply proper_snoc; [easy|]
           | |- (?A /\ ?B <-> ?A /\ ?C) =>
               apply (@and_iff_compat_l' A B C); intro
           (* | |- (?B /\ ?A <-> ?C /\ ?A) => *)
           (*     apply (@and_iff_compat_r' A B C); intro *)
           end).

    Lemma formula_bool_relop [Σ σ] (op : RelOp σ) (s t : Term Σ σ) :
      formula_bool (term_binop (bop.relop op) s t) ~ formula_relop op s t.
    Proof. intros ι; cbn; symmetry; apply bop.eval_relop_equiv. Qed.
    #[local] Hint Rewrite formula_bool_relop : katamaran.

    (* Simplifies boolean terms to equivalent formulas. These come for instance
       from (formula_bool t) or equations of the form
       (formula_relop bop.eq t = true). *)
    Equations simplify_bool [Σ] (t : Term Σ ty.bool) (k : PathCondition Σ)  :
      option (PathCondition Σ)  :=
    | term_var ς                    | k => Some (k ▻ formula_bool (term_var ς))
    | term_val _ b                  | k => if b then Some k else None
    | term_binop bop.and s t        | k => k' <- simplify_bool s k ;; simplify_bool t k'
    | term_binop (bop.relop op) s t | k => (* We do not recurse into the terms of a relop
                                              to avoid defining too many mutually recursive
                                              functions. We content ourselves with the fact
                                              that the boolean term has been turned into
                                              a Prop. *)
                                           Some (k ▻ formula_relop op s t)
    | term_binop bop.or s t         | k => Some (k ▻ formula_bool (term_binop bop.or s t))
    | term_not t                    | k => simplify_bool_neg t k
    (* Simplifies formulas of the the shape (formula_bool (term_not t)) or
       (formula_relop bop.eq t = false) *)
    with simplify_bool_neg [Σ] (t : Term Σ ty.bool) (k : PathCondition Σ) : option (PathCondition Σ) :=
    | term_var ς                    | k => Some (k ▻ formula_bool (term_not (term_var ς)))
    | term_val _ b                  | k => if b then None else Some k
    | term_binop bop.and s t        | k => Some (k ▻ formula_bool (term_binop bop.or (term_not s) (term_not t)))
    | term_binop bop.or s t         | k => k' <- simplify_bool_neg s k ;; simplify_bool_neg t k'
    | term_binop (bop.relop op) s t | k => Some (k ▻ formula_relop_neg op s t)
    | term_not t                    | k => simplify_bool t k.

    Lemma simplify_bool_spec_combined :
      (forall Σ (t : Term Σ ty.bool) (k : PathCondition Σ),
          simplify_bool t k ≋ Some (k ▻ formula_bool t)) *
      (forall Σ (t : Term Σ ty.bool) (k : PathCondition Σ),
          simplify_bool_neg t k ≋ Some (k ▻ formula_bool (term_not t))).
    Proof.
      (* This uses the fucntional elimination principle
         generated by the equations library. *)
      apply (simplify_bool_elim
               (fun Σ t k r => r ≋ Some (k ▻ formula_bool t))
               (fun Σ t k r => r ≋ Some (k ▻ formula_bool (term_not t)))).
      - intros; reflexivity.
      - intros ? [] *; arw; intros ι; arw; cbn; intuition.
      - intros ? s t k Ht Hs ι. specialize (Ht ι). arw.
        destruct simplify_bool as [kt|]; arw.
        + rewrite (Hs kt ι); arw. now rewrite Ht.
        + clear Hs. intuition.
      - reflexivity.
      - intros Σ σ op s t k. now arw.
      - easy.
      - easy.
      - intros ? [] * ι; arw; intuition.
      - intros * ι; arw; easy.
      - intros ? s t k Ht Hs ι; specialize (Ht ι). arw.
        destruct simplify_bool_neg as [kt|]; arw.
        + specialize (Hs kt ι). arw. now rewrite Hs, Ht.
        + clear Hs. intuition.
      - intros Σ σ op s t k. arw. intros ι; now arw.
      - intros * HYP ι. specialize (HYP ι); now arw.
    Qed.

    Lemma simplify_bool_spec [Σ] (t : Term Σ ty.bool) (k : PathCondition Σ) :
      simplify_bool t k ≋ Some (k ▻ formula_bool t).
    Proof. apply simplify_bool_spec_combined. Qed.

    Lemma simplify_bool_neg_spec [Σ] (t : Term Σ ty.bool) (k : PathCondition Σ) :
      simplify_bool_neg t k ≋ Some (k ▻ formula_bool (term_not t)).
    Proof. apply simplify_bool_spec_combined. Qed.
    #[local] Opaque simplify_bool simplify_bool_neg.
    #[local] Hint Rewrite simplify_bool_spec simplify_bool_neg_spec : katamaran.

    (* Simplifies equations of the form (term_binop op t1 t2 = v). *)
    Equations(noeqns) simplify_eq_binop_val [Σ σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ)
      (k : PathCondition Σ) : option (PathCondition Σ) :=
    | bop.pair       | t1 | t2 | (v1 , v2)  | k =>
      Some (k ▻ formula_relop bop.eq t1 (term_val _ v1)
              ▻ formula_relop bop.eq t2 (term_val _ v2))
    | bop.cons       | t1 | t2 | nil        | k => None
    | bop.cons       | t1 | t2 | cons v1 v2 | k =>
      Some (k ▻ formula_relop bop.eq t1 (term_val _ v1)
              ▻ formula_relop bop.eq t2 (term_val (ty.list _) v2))
    | bop.and        | t1 | t2 | v          | k =>
      if v
      then simplify_bool (term_binop bop.and t1 t2) k
      else simplify_bool_neg (term_binop bop.and t1 t2) k
    | bop.or         | t1 | t2 | v          | k =>
      if v
      then simplify_bool (term_binop bop.or t1 t2) k
      else simplify_bool_neg (term_binop bop.or t1 t2) k
    | bop.relop op   | t1 | t2 | v          | k =>
      if v
      then Some (k ▻ formula_relop op t1 t2)
      else Some (k ▻ formula_relop_neg op t1 t2)
    | op             | t1 | t2 | v          | k =>
      Some (k ▻ formula_relop bop.eq (term_binop op t1 t2) (term_val _ v)).

    Lemma simplify_eq_binop_val_spec [Σ σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) (k : PathCondition Σ) :
      simplify_eq_binop_val op t1 t2 v k ≋
      Some (k ▻ formula_relop bop.eq (term_binop op t1 t2) (term_val σ v)).
    Proof.
      destruct op; cbn; try reflexivity;
        destruct v; arw; try easy; intros ι; now arw.
    Qed.
    #[local] Opaque simplify_eq_binop_val.
    #[local] Hint Rewrite simplify_eq_binop_val_spec : katamaran.

    Definition simplify_eqb {Σ σ} (t1 t2 : Term Σ σ) (k : PathCondition Σ) :
      option (PathCondition Σ) :=
      if Term_eqb t1 t2
      then Some k
      else Some (k ▻ formula_relop bop.eq t1 t2).

    Lemma simplify_eqb_spec [Σ σ] (t1 t2 : Term Σ σ) (k : PathCondition Σ) :
      simplify_eqb t1 t2 k ≋ Some (k ▻ formula_relop bop.eq t1 t2).
    Proof.
      unfold simplify_eqb.
      destruct (Term_eqb_spec t1 t2); arw.
      - subst; intros ι; now arw.
      - reflexivity.
    Qed.
    #[local] Hint Rewrite simplify_eqb_spec : katamaran.
    #[local] Opaque simplify_eqb.

    Equations(noeqns) simplify_eq_binop {Σ σ σ11 σ12 σ21 σ22}
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      (k : PathCondition Σ) : option (PathCondition Σ) :=
    | bop.pair | t11 | t12 | bop.pair | t21 | t22 | k =>
      Some (k ▻ formula_relop bop.eq t11 t21 ▻ formula_relop bop.eq t12 t22)
    | bop.cons | t11 | t12 | bop.cons | t21 | t22 | k =>
      Some (k ▻ formula_relop bop.eq t11 t21 ▻ formula_relop bop.eq t12 t22)
    | op1      | t11 | t12 | op2      | t21 | t22 | k =>
      simplify_eqb (term_binop op1 t11 t12) (term_binop op2 t21 t22) k.

    Lemma simplify_eq_binop_spec [Σ σ σ11 σ12 σ21 σ22]
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      (k : PathCondition Σ) :
      simplify_eq_binop op1 t11 t12 op2 t21 t22 k ≋
      Some (k ▻ formula_relop bop.eq (term_binop op1 t11 t12) (term_binop op2 t21 t22)).
    Proof.
      destruct op1; cbn; arw; try easy; dependent elimination op2;
        cbn; arw; intros ι; now arw.
    Qed.
    #[local] Hint Rewrite simplify_eq_binop_spec : katamaran.
    #[local] Opaque simplify_eq_binop.

    Definition simplify_eq_union [Σ U] [K1 K2 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (t2 : Term Σ (unionk_ty U K2)) (k : PathCondition Σ) :
      option (PathCondition Σ) :=
      match eq_dec K1 K2 with
      | left e  => let t2' := eq_rec_r (fun K => Term Σ (unionk_ty U K)) t2 e in
                   Some (k ▻ formula_relop bop.eq t1 t2')
      | right _ => None
      end.

    Set Equations With UIP.
    Lemma simplify_eq_union_spec [Σ U] [K1 K2 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (t2 : Term Σ (unionk_ty U K2)) (k : PathCondition Σ) :
      simplify_eq_union t1 t2 k ≋
      Some (k ▻ formula_relop bop.eq (term_union U K1 t1) (term_union U K2 t2)).
    Proof.
      unfold simplify_eq_union. destruct eq_dec; arw.
      - intros ι; arw. split; intros HYP.
        + destruct e. now f_equal.
        + depelim HYP. now dependent elimination e.
      - intros ι; arw. intuition.
    Qed.
    #[local] Opaque simplify_eq_union.

    Definition simplify_eq_union_val [Σ U] [K1 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (v2 : Val (ty.union U)) (k : PathCondition Σ) :
      option (PathCondition Σ) :=
       let (K2, v2) := unionv_unfold U v2 in
       match eq_dec K1 K2 with
       | left e  => let v2' := eq_rec_r (fun K1 => Val (unionk_ty U K1)) v2 e in
                    let t2  := term_val (unionk_ty U K1) v2' in
                    Some (k ▻ formula_relop bop.eq t1 t2)
       | right _ => None
       end.

    Lemma simplify_eq_union_val_spec [Σ U] [K1 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (v : Val (ty.union U)) (k : PathCondition Σ) :
      simplify_eq_union_val t1 v k ≋
      Some (k ▻ formula_relop bop.eq (term_union U K1 t1) (term_val (ty.union U) v)).
    Proof.
      unfold simplify_eq_union_val.
      destruct unionv_unfold as [K2 v2] eqn:?.
      apply (f_equal (unionv_fold U)) in Heqs.
      rewrite unionv_fold_unfold in Heqs. subst.
      destruct eq_dec as [e|e]; arw.
      - intros ι; arw. split; intros HYP.
        + destruct e. now f_equal.
        + depelim HYP. now dependent elimination e.
      - intros ι; arw. intuition.
    Qed.
    #[local] Opaque simplify_eq_union_val.

    Fixpoint simplify_eq_val {Σ} [σ] (t : Term Σ σ) : forall (v : Val σ) (k : PathCondition Σ), option (PathCondition Σ) :=
      match t with
      | term_var x          => fun v k => Some (k ▻ formula_relop bop.eq (term_var x) (term_val _ v))
      | term_val σ v        => fun v' k => if eq_dec v v' then Some k else None
      | term_binop op t1 t2 => simplify_eq_binop_val op t1 t2
      | term_neg t          => fun v k => Some (k ▻ formula_relop bop.eq (term_neg t) (term_val ty.int v))
      | term_not t          => fun v k => if v
                                          then simplify_bool_neg t k
                                          else simplify_bool t k
      | term_inl t          => fun v k =>
                                 match v with
                                 | inl v => simplify_eq_val t v k
                                 | inr _ => None
                                 end
      | term_inr t          => fun v k =>
                                 match v with
                                 | inl _ => None
                                 | inr v => simplify_eq_val t v k
                                 end
      | term_sext t         => fun v k => Some (k ▻ formula_relop bop.eq (term_sext t) (term_val _ v))
      | term_zext t         => fun v k => Some (k ▻ formula_relop bop.eq (term_zext t) (term_val _ v))
      | term_tuple ts       => env.Env_rect
                                 (fun σs _ => Val (ty.tuple σs) -> PathCondition Σ -> option (PathCondition Σ))
                                 (fun _ => Some)
                                 (fun τs _ IHts τ t (vτsτ : Val (ty.tuple (τs ▻ τ))) k =>
                                    let (vτs, vτ) := vτsτ in
                                    k' <- simplify_eq_val t vτ k;; IHts vτs k')
                                 ts
      | term_union U K t    => simplify_eq_union_val t
      | term_record R ts    => fun v k => Some (k ▻▻ formula_eqs_nctx ts (lift (recordv_unfold _ v)))
                                 (* env.All_rect *)
                                 (*   (fun Δ _ _ => NamedEnv Val Δ -> PathCondition Σ -> OFormulas Σ) *)
                                 (*   (fun _ => Some) *)
                                 (*   (fun Δ _ b _ _ *)
                                 (*        (IHΔ : NamedEnv Val Δ -> PathCondition Σ -> OFormulas Σ) *)
                                 (*        (IHb : Val (type b) -> PathCondition Σ -> OFormulas Σ) *)
                                 (*        (vΔb : NamedEnv Val (Δ ▻ b)) *)
                                 (*        (k : PathCondition Σ) => *)
                                 (*      let (vΔ , vb) := env.snocView vΔb in *)
                                 (*      k' <- IHb vb k;; IHΔ vΔ k') *)
                                 (*   (env.all_intro (fun b t => simplify_eq_val t) ts) *)
                                 (*   (recordv_unfold R v) *)
      end.

    Lemma simplify_eq_val_spec [Σ σ] (t : Term Σ σ) (v : Val σ) :
      forall (k : PathCondition Σ),
        simplify_eq_val t v k ≋ Some (k ▻ formula_relop bop.eq t (term_val σ v)).
    Proof.
      induction t; cbn; intros k; arw.
      - reflexivity.
      - destruct eq_dec; arw.
        + subst. intros ι; now arw.
        + intros ι; now arw.
      - reflexivity.
      - reflexivity.
      - destruct v; arw; try easy. intros ι; now arw.
      - destruct v; arw.
        + rewrite IHt; arw. intros ι; now arw.
        + intros ι; now arw.
      - destruct v; arw.
        + intros ι; now arw.
        + rewrite IHt; arw. intros ι; now arw.
      - reflexivity.
      - reflexivity.
      - revert k. induction IH; cbn; intros k; arw.
        + destruct v. intros ι; now arw.
        + destruct v as [vs v]. specialize (q v k).
          destruct (simplify_eq_val d v k) as [k'|]; cbn.
          * rewrite (IHIH vs k'); arw. intros ι. specialize (q ι); arw.
            cbn. rewrite q. now arw.
          * clear IHIH. intros ι. specialize (q ι).
            arw. cbn in *. intuition.
      - apply simplify_eq_union_val_spec.
      - intros ι; arw. rewrite inst_lift. split.
        intros ->. now rewrite recordv_fold_unfold.
        intros <-. now rewrite recordv_unfold_fold.
    Qed.
    #[local] Opaque simplify_eq_val.
    #[local] Hint Rewrite simplify_eq_val_spec : katamaran.

    Equations(noeqns) simplify_eq {Σ σ} (t1 t2 : Term Σ σ)
      (k : PathCondition Σ) : option (PathCondition Σ) :=
    | term_val _ v           | t                        | k => simplify_eq_val t v k
    | t                      | term_val _ v             | k => simplify_eq_val t v k
    | term_inr _             | term_inl _               | k => None
    | term_inl _             | term_inr _               | k => None
    | term_inl t1            | term_inl t2              | k => simplify_eq t1 t2 k
    | term_inr t1            | term_inr t2              | k => simplify_eq t1 t2 k
    | term_tuple ts1         | term_tuple ts2           | k => Some (k ▻▻ formula_eqs_ctx ts1 ts2)
    | term_record _ ts1      | term_record _ ts2        | k => Some (k ▻▻ formula_eqs_nctx ts1 ts2)
    | term_binop op1 t11 t12 | term_binop op2 t21 t22   | k => simplify_eq_binop op1 t11 t12 op2 t21 t22 k
    | term_union _ K1 t1     | term_union _ K2 t2       | k => simplify_eq_union t1 t2 k
    | t1                     | t2                       | k => simplify_eqb t1 t2 k.

    Lemma simplify_eq_spec [Σ σ] (s t : Term Σ σ) (k : PathCondition Σ) :
      simplify_eq s t k ≋ Some (k ▻ formula_relop bop.eq s t).
    Proof.
      induction s.
      - dependent elimination t; cbn; now arw.
      - cbn. rewrite simplify_eq_val_spec. now arw.
      - dependent elimination t; cbn; now arw.
      - dependent elimination t; cbn; now arw.
      - dependent elimination t; cbn; now arw.
      - dependent elimination t; cbn; arw; try easy.
        + rewrite IHs; arw. intros ι; now arw.
        + intros ι; now arw.
      - dependent elimination t; cbn; arw; try easy.
        + intros ι; now arw.
        + rewrite IHs; arw. intros ι; now arw.
      - dependent elimination t; cbn; arw; try easy.
      - dependent elimination t; cbn; arw; try easy.
      - dependent elimination t; cbn; arw; try easy.
        intros ι; now arw.
      - dependent elimination t; cbn; arw; try easy.
        apply simplify_eq_union_spec.
      - dependent elimination t; cbn; arw; try easy.
        intros ι; now arw.
    Qed.

    Definition simplify_relopb {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) (k : PathCondition Σ) : option (PathCondition Σ) :=
      match term_get_val t1 , term_get_val t2 with
      | Some v1 , Some v2 => if bop.eval_relop_val op v1 v2 then Some k else None
      | _       , _       => Some (k ▻ formula_relop op t1 t2)
      end.

    Definition simplify_relop {Σ σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ Σ), PathCondition Σ -> option (PathCondition Σ) :=
      match op with
      | bop.eq => fun t1 t2 k => simplify_eq t1 t2 k
      | _      => simplify_relopb op
      end.

    Definition simplify_relopb_spec {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) (k : PathCondition Σ) :
      simplify_relopb op t1 t2 k ≋ Some (k ▻ formula_relop op t1 t2).
    Proof.
      unfold simplify_relopb.
      destruct (term_get_val_spec t1) as [v1|]; try easy. subst.
      destruct (term_get_val_spec t2) as [v2|]; try easy. subst.
      - intros ι; arw. destruct bop.eval_relop_val; now arw.
    Qed.
    #[local] Opaque simplify_relopb.

    Definition simplify_relop_spec {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) (k : PathCondition Σ) :
      simplify_relop op t1 t2 k ≋ Some (k ▻ formula_relop op t1 t2).
    Proof.
      unfold simplify_relop.
      destruct op; cbn; rewrite ?simplify_relopb_spec; try easy.
      now rewrite simplify_eq_spec.
    Qed.

    Fixpoint simplify_formula {Σ} (fml : Formula Σ) (k : PathCondition Σ) : option (PathCondition Σ) :=
      match fml with
      | formula_user p ts      => Some (k ▻ formula_user p (pevals ts))
      | formula_bool t         => simplify_bool (peval t) k
      | formula_prop ζ P       => Some (k ▻ fml)
      | formula_relop op t1 t2 => simplify_relop op (peval t1) (peval t2) k
      | formula_true           => Some k
      | formula_false          => None
      | formula_and F1 F2      => k' <- simplify_formula F1 k ;;
                                  simplify_formula F2 k'
      | formula_or F1 F2       => Some (k ▻ fml)
      end.

    Fixpoint simplify_pathcondition {Σ} (C : PathCondition Σ) (k : PathCondition Σ) : option (PathCondition Σ) :=
      match C with
      | [ctx] => Some k
      | C ▻ F =>
        option.bind (simplify_pathcondition C k) (simplify_formula F)
      end.

    Lemma simplify_formula_spec {Σ} (F : Formula Σ) :
      forall k, simplify_formula F k ≋ Some (k ▻ F).
    Proof.
      induction F; cbn - [peval]; intros k; arw.
      - apply proper_formula_user. apply pevals_sound.
      - apply proper_formula_bool. apply peval_sound.
      - reflexivity.
      - rewrite simplify_relop_spec.
        apply proper_some, proper_snoc; [reflexivity|].
        apply proper_formula_relop; apply peval_sound.
      - intros ι; cbn. easy.
      - intros ι; now arw.
      - intros ι; arw. specialize (IHF1 k ι).
        destruct (simplify_formula F1 k) as [k'|]; arw.
        + rewrite (IHF2 k' ι); arw; intuition.
        + intuition.
      - reflexivity.
    Qed.

    Lemma simplify_pathcondition_spec {Σ} (C k : PathCondition Σ) :
      simplify_pathcondition C k ≋ Some (k ▻▻ C).
    Proof.
      revert k; induction C as [|C IHC F]; cbn; intros k.
      - reflexivity.
      - intros ι. specialize (IHC k ι). arw.
        destruct simplify_pathcondition as [k'|]; arw.
        + rewrite (simplify_formula_spec F k' ι); arw. now rewrite IHC.
        + intuition.
    Qed.

    Definition occurs_check_lt {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | @term_var _ y σ yIn =>
        if Nat.ltb (ctx.in_at xIn) (ctx.in_at yIn) then occurs_check xIn t else None
      | _ => occurs_check xIn t
      end.

    Lemma occurs_check_lt_sound {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) (t' : Term (Σ - x) σ) :
      occurs_check_lt xIn t = Some t' -> t = subst t' (sub_shift xIn).
    Proof.
      unfold occurs_check_lt. intros Hwlp.
      pose proof (occurs_check_sound xIn t) as H.
      unfold OccursCheckSoundPoint in H.
      rewrite option.wlp_forall in H. apply H. clear H.
      destruct t; auto. destruct (Nat.ltb _ _); auto.
      discriminate.
    Qed.

    Equations(noeqns) try_unify_bool {w : World} (t : Term w ty.bool) :
      option { w' & Tri w w' } :=
      try_unify_bool (@term_var _ x σ xIn) :=
        Some (existT _ (tri_cons x (term_val ty.bool true) tri_id));
      try_unify_bool (term_not (@term_var _ x σ xIn)) :=
        Some (existT _ (tri_cons x (term_val ty.bool false) tri_id));
      try_unify_bool _ :=
        None.

    Definition try_unify_eq {w : World} {σ} (t1 t2 : Term w σ) :
      option { w' & Tri w w' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term w σ =>
          match occurs_check_lt ςInΣ t2 with
          | Some t => Some (existT _ (tri_cons ς t tri_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_unify_formula {w : World} (fml : Formula w) :
      option { w' & Tri w w' } :=
      match fml with
      | formula_bool t => try_unify_bool t
      | formula_relop bop.eq t1 t2 =>
        match try_unify_eq t1 t2 with
        | Some r => Some r
        | None => try_unify_eq t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_bool_spec {w : World} (t : Term w ty.bool) :
      option.wlp (fun '(existT w' ν) => forall ι, inst (T := STerm ty.bool) t ι = true <-> inst_triangular ν ι) (try_unify_bool t).
    Proof.
      dependent elimination t; cbn; try constructor; auto.
      intros ι. cbn. intuition.
      dependent elimination e0; cbn; try constructor; auto.
      intros ι. cbn. destruct ι.[??ς]; intuition.
    Qed.

    Lemma try_unify_eq_spec {w : World} {σ} (t1 t2 : Term w σ) :
      option.wlp (fun '(existT w' ν) => forall ι, inst t1 ι = inst t2 ι <-> inst_triangular ν ι) (try_unify_eq t1 t2).
    Proof.
      unfold try_unify_eq. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check_lt ςInΣ t2) eqn:Heq; constructor; auto.
      apply occurs_check_lt_sound in Heq. subst.
      intros ι. rewrite inst_subst, inst_sub_shift.
      cbn. intuition.
    Qed.

    Lemma try_unify_formula_spec {w : World} (fml : Formula w) :
      option.wlp (fun '(existT w' ν) => forall ι, (inst fml ι : Prop) <-> inst_triangular ν ι) (try_unify_formula fml).
    Proof.
      unfold try_unify_formula; destruct fml; cbn; try (constructor; auto; fail).
      - apply try_unify_bool_spec.
      - destruct rop; try constructor; cbn.
        destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|]. constructor. auto.
        destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|]. constructor.
        intros ι. specialize (HYP ι). intuition.
        now constructor.
    Qed.

    Definition unify_formula {w0 : World} (F : Formula w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type :=
      match try_unify_formula F with
      | Some (existT w1 ν01) => existT w1 (ν01 , ctx.nil)
      | None => existT w0 (tri_id , ctx.nil ▻ F)
      end.

    Lemma unify_formula_spec {w0 : World} (fml : Formula w0) :
      match unify_formula fml with
      | existT w1 (ν01 , fmls) =>
        (forall ι0 : Valuation w0,
            inst (A := Prop) fml ι0 ->
            inst_triangular ν01 ι0 /\
            instprop fmls (inst (sub_triangular_inv ν01) ι0)) /\
        (forall ι1 : Valuation w1,
            instprop fmls ι1 ->
            inst (A := Prop) fml (inst (sub_triangular ν01) ι1))
      end.
    Proof.
      unfold unify_formula.
      destruct (try_unify_formula_spec fml).
      - destruct a as [w1 ν01]. split.
        + intros ι0 Hfml. specialize (H ι0). intuition. constructor.
        + intros ι1 []. apply H. apply inst_triangular_valid.
      - split; intros ?; rewrite inst_pathcondition_snoc;
          cbn; rewrite inst_sub_id; intuition.
    Qed.

    Fixpoint unify_pathcondition {w0 : World} (C : PathCondition w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type.
    Proof.
      destruct C as [|C F].
      - exists w0. split. apply tri_id. apply ctx.nil.
      - destruct (unify_pathcondition w0 C) as (w1 & ν01 & C1).
        clear unify_pathcondition C.
        destruct (unify_formula (persist F (acc_triangular ν01))) as (w2 & ν12 & C2).
        exists w2. split. apply (tri_comp ν01 ν12).
        refine (persist C1 (acc_triangular ν12) ▻▻ C2).
    Defined.

    Lemma unify_pathcondition_spec {w0 : World} (C0 : PathCondition w0) :
      match unify_pathcondition C0 with
      | existT w1 (ν01 , C1) =>
        (forall ι0 : Valuation w0,
            instprop C0 ι0 ->
            inst_triangular ν01 ι0 /\
            instprop C1 (inst (sub_triangular_inv ν01) ι0)) /\
        (forall ι1 : Valuation w1,
            instprop C1 ι1 ->
            instprop C0 (inst (sub_triangular ν01) ι1))
      end.
    Proof.
      induction C0 as [|C0 IHC F0]; cbn.
      - intuition.
      - destruct unify_pathcondition as (w1 & ν01 & C1).
        pose proof (unify_formula_spec (persist F0 (acc_triangular ν01))) as IHF.
        destruct (unify_formula (persist F0 (acc_triangular ν01))) as (w2 & ν12 & C2).
        destruct IHC as [IHC01 IHC10].
        destruct IHF as [IHF12 IHF21].
        split.
        + intros ι0. intros [HCι0 HFι0].
          specialize (IHC01 ι0 HCι0). destruct IHC01 as [Hν01 HCι1].
          specialize (IHF12 (inst (sub_triangular_inv ν01) ι0)).
          rewrite inst_persist, sub_acc_triangular in IHF12.
          rewrite inst_triangular_right_inverse in IHF12; auto.
          specialize (IHF12 HFι0). destruct IHF12 as [Hν12 Hfmls2].
          repeat fold PathCondition.
          change (fun w : World => Ctx (Formula w))
            with (fun w : World => PathCondition w).
          rewrite inst_pathcondition_cat.
          rewrite inst_persist, inst_tri_comp, sub_acc_triangular.
          split; auto. rewrite sub_triangular_inv_comp, inst_subst. split; auto.
          revert HCι1. remember (inst (sub_triangular_inv ν01) ι0) as ι1.
          rewrite inst_triangular_right_inverse; auto.
        + intros ι2.
          repeat fold PathCondition.
          change (fun w : World => Ctx (Formula w))
            with (fun w : World => PathCondition w).
          rewrite !inst_pathcondition_cat, inst_persist, sub_acc_triangular.
          intros [HCι1 HFι2].
          specialize (IHF21 ι2 HFι2). rewrite inst_persist, sub_acc_triangular in IHF21.
          specialize (IHC10 (inst (sub_triangular ν12) ι2) HCι1).
          rewrite sub_triangular_comp, inst_subst.
          split; auto.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ τ op2 t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ ?(σ) op2 t21 t22) (left eq_refl) :=
          (if eq_dec op1 op2 then true else false) &&& Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ τ op2 t21 t22) (right _) := false
      };
      formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) with 𝑷_eq_dec p q => {
        formula_eqb (@formula_user _ p ts1) (@formula_user _ ?(p) ts2) (left eq_refl) :=
          env.eqb_hom (@Term_eqb _) ts1 ts2;
        formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) (right _) := false
      };
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      induction f1; dependent elimination f2; simp formula_eqb;
        repeat
          match goal with
          | |- BoolSpec _ _ false   => constructor; auto
          | |- context[eq_dec _ _ ] => destruct eq_dec; subst; cbn
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; intuition; fail)
          end.
      - destruct 𝑷_eq_dec.
        + destruct e; cbn.
          destruct (env.eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) ts ts0);
            constructor; intuition.
        + now constructor.
    Qed.

    Fixpoint assumption_formula {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) {struct C} : PathCondition Σ :=
      match C with
      | [ctx]  => k ▻ F
      | C ▻ F' => if formula_eqb F F'
                     then k
                     else assumption_formula C F k
      end.

    Fixpoint assumption_pathcondition {Σ} (C : PathCondition Σ) (FS : PathCondition Σ) (k : PathCondition Σ) {struct FS} : PathCondition Σ :=
      match FS with
      | [ctx]  => k
      | FS ▻ F => assumption_formula C F (assumption_pathcondition C FS k)
      end.

    Lemma assumption_formula_spec {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) (ι : Valuation Σ) :
      instprop C ι -> instprop k ι /\ instprop F ι <-> instprop (assumption_formula C F k) ι.
    Proof.
      induction C as [|C ? F']; cbn; auto.
      intros [HCι HFι']. specialize (IHC HCι).
      destruct (formula_eqb_spec F F');
        subst; intuition.
    Qed.

    Lemma assumption_pathcondition_spec {Σ} (C : PathCondition Σ) (FS : PathCondition Σ) (k : PathCondition Σ) (ι : Valuation Σ) :
      instprop C ι -> instprop k ι /\ instprop FS ι <-> instprop (assumption_pathcondition C FS k) ι.
    Proof.
      intros HCι. induction FS as [|FS ? F]; cbn.
      - intuition.
      - pose proof (assumption_formula_spec C F (assumption_pathcondition C FS k) ι HCι).
        intuition.
    Qed.

    Definition solver_generic_round : Solver :=
      fun w0 C0 =>
        match simplify_pathcondition C0 ctx.nil with
        | Some C1 => Some (unify_pathcondition (assumption_pathcondition (wco w0) C1 ctx.nil))
        | None => None
        end.

    Lemma solver_generic_round_spec : SolverSpec solver_generic_round.
    Proof.
      unfold solver_generic_round. intros w0 fmls0.
      pose proof (simplify_pathcondition_spec fmls0 ctx.nil) as Hequiv.
      destruct simplify_pathcondition as [fmls0'|]; constructor; cbn.
      - pose proof (unify_pathcondition_spec (assumption_pathcondition (wco w0) fmls0' ctx.nil)) as Hunify.
        destruct (unify_pathcondition (assumption_pathcondition (wco w0) fmls0' ctx.nil)) as (w1 & ν01 & fmls1).
        intros ι0 Hpc0. specialize (Hequiv ι0). autorewrite with katamaran in Hequiv.
        pose proof (assumption_pathcondition_spec (wco w0) fmls0' ctx.nil ι0 Hpc0) as Hassumption.
        destruct Hassumption as [Hassumption01 Hassumption10].
        destruct Hunify as [Hunify01 Hunify10]. specialize (Hunify01 ι0).
        split.
        + intros Hfmls0. apply Hunify01. apply Hassumption01.
          split. constructor. apply Hequiv. split; auto.
        + intros ι1 Heqι. specialize (Hunify10 ι1).
          split.
          * intros Hfmls0. destruct Hequiv as [_ Hequiv].
            inster Hequiv by split; auto; constructor.
            inster Hassumption01 by split; auto; constructor.
            inster Hunify01 by auto. destruct Hunify01 as [Hν01 Hfmls1].
            revert Hfmls1. subst. now rewrite inst_triangular_left_inverse.
          * intros Hfmls1. inster Hunify10 by subst; auto.
            apply Hequiv. apply Hassumption10. subst; auto.
      - intros ι. specialize (Hequiv ι).
        autorewrite with katamaran in Hequiv.
        intuition.
    Qed.

    Definition solver_compose (s1 s2 : Solver) : Solver :=
      fun w0 fmls0 =>
        option.bind
          (s1 _ fmls0)
          (fun '(existT w1 (ν01 , fmls1)) =>
             option.map
               (fun '(existT w2 (ν12 , fmls2)) =>
                  existT w2 (tri_comp ν01 ν12 , fmls2))
               (s2 _ fmls1)).

    Lemma solver_compose_spec {s1 s2} (spec1 : SolverSpec s1) (spec2 : SolverSpec s2) : SolverSpec (solver_compose s1 s2).
    Proof.
      unfold SolverSpec, solver_compose. intros w0 fmls0.
      apply option.spec_bind.
      generalize (spec1 _ fmls0); clear spec1.
      apply option.spec_monotonic; auto.
      intros (w1 & ν01 & fmls1) H1.
      apply option.spec_map.
      generalize (spec2 _ fmls1); clear spec2.
      apply option.spec_monotonic; auto.
      - intros (w2 & ν12 & fmls2) H2. intros ι0 Hpc0.
        specialize (H1 ι0 Hpc0). destruct H1 as [H01 H10].
        rewrite inst_tri_comp. split.
        + intros Hfmls0. split; auto.
          remember (inst (sub_triangular_inv ν01) ι0) as ι1.
          assert (instprop (wco w1) ι1) as Hpc1 by
              (subst; apply entails_triangular_inv; auto).
          apply H2; auto. apply H10; auto.
          subst; rewrite inst_triangular_right_inverse; auto.
        + intros ι2 Hpc2 Hι0. rewrite sub_triangular_comp, inst_subst in Hι0.
          remember (inst (sub_triangular ν12) ι2) as ι1.
          assert (instprop (wco w1) ι1) as Hpc1 by
              (revert Hpc2; subst; rewrite <- sub_acc_triangular, <- inst_persist; apply ent_acc).
          rewrite H10; eauto. apply H2; auto.
      - intros Hfmls1 ι0 Hpc0 Hfmls0. specialize (H1 ι0 Hpc0).
        destruct H1 as [H01 H10]. inster H01 by auto.
        pose (inst (sub_triangular_inv ν01) ι0) as ι1.
        assert (instprop (wco w1) ι1) as Hpc1 by
            (subst; apply entails_triangular_inv; auto).
        apply (Hfmls1 ι1 Hpc1). revert Hfmls0.
        apply H10; auto. subst ι1.
        now rewrite inst_triangular_right_inverse.
    Qed.

    Definition generic (user : Solver) : Solver :=
      let g   := solver_generic_round in
      let gg  := solver_compose g g in
      let ggu := solver_compose gg user in
      solver_compose ggu (solver_compose ggu gg).

    Lemma generic_spec {user} (H : SolverSpec user) :
      SolverSpec (generic user).
    Proof.
      unfold generic.
      auto using solver_compose_spec, solver_generic_round_spec.
    Qed.

  End Solver.

End SolverOn.

Module MakeSolver
  (B : Base)
  (Import SIG : Signature B)
  (SOLV : SolverKit B SIG)
  <: SolverKit B SIG.

  Include SolverOn B SIG.

  Definition solver : Solver :=
    Solver.generic SOLV.solver.
  Definition solver_spec : SolverSpec solver :=
    Solver.generic_spec SOLV.solver_spec.

End MakeSolver.
