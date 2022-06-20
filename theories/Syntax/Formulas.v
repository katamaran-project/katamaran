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
     Classes.Morphisms
     Classes.RelationClasses
     Program.Basics
     Program.Tactics
     ZArith.

From Katamaran Require Import
     Prelude
     Notations
     Syntax.Predicates
     Base.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type FormulasOn
  (Import B : Base)
  (Import P : PredicateKit B).

  Local Obligation Tactic := idtac.

  Inductive Formula (Σ : LCtx) : Type :=
  | formula_user   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | formula_bool (t : Term Σ ty.bool)
  | formula_prop {Σ'} (ζ : Sub Σ' Σ) (P : abstract_named Val Σ' Prop)
  | formula_ge (t1 t2 : Term Σ ty.int)
  | formula_gt (t1 t2 : Term Σ ty.int)
  | formula_le (t1 t2 : Term Σ ty.int)
  | formula_lt (t1 t2 : Term Σ ty.int)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).
  Arguments formula_user {_} p ts.
  Arguments formula_bool {_} t.

  Equations(noeqns) formula_eqs_ctx {Δ : Ctx Ty} {Σ : LCtx}
    (δ δ' : Env (Term Σ) Δ) : list (Formula Σ) :=
    formula_eqs_ctx env.nil          env.nil            := nil;
    formula_eqs_ctx (env.snoc δ _ t) (env.snoc δ' _ t') :=
      formula_eq t t' :: formula_eqs_ctx δ δ'.

  Equations(noeqns) formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ : LCtx}
    (δ δ' : NamedEnv (Term Σ) Δ) : list (Formula Σ) :=
    formula_eqs_nctx env.nil          env.nil            := nil;
    formula_eqs_nctx (env.snoc δ _ t) (env.snoc δ' _ t') :=
      formula_eq t t' :: formula_eqs_nctx δ δ'.

  Global Instance sub_formula : Subst Formula :=
    fun Σ1 fml Σ2 ζ =>
      match fml with
      | formula_user p ts => formula_user p (subst ts ζ)
      | formula_bool t    => formula_bool (subst t ζ)
      | formula_prop ζ' P => formula_prop (subst ζ' ζ) P
      | formula_ge t1 t2  => formula_ge (subst t1 ζ) (subst t2 ζ)
      | formula_gt t1 t2  => formula_gt (subst t1 ζ) (subst t2 ζ)
      | formula_le t1 t2  => formula_le (subst t1 ζ) (subst t2 ζ)
      | formula_lt t1 t2  => formula_lt (subst t1 ζ) (subst t2 ζ)
      | formula_eq t1 t2  => formula_eq (subst t1 ζ) (subst t2 ζ)
      | formula_neq t1 t2 => formula_neq (subst t1 ζ) (subst t2 ζ)
      end.

  Global Instance substlaws_formula : SubstLaws Formula.
  Proof.
    constructor.
    { intros ? []; cbn; f_equal; apply subst_sub_id. }
    { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
  Qed.

  Global Instance inst_formula : Inst Formula Prop :=
    fun {Σ} (fml : Formula Σ) (ι : Valuation Σ) =>
      match fml with
      | formula_user p ts => env.uncurry (𝑷_inst p) (inst ts ι)
      | formula_bool t    => inst (A := Val ty.bool) t ι = true
      | formula_prop ζ P  => uncurry_named P (inst ζ ι)
      | formula_ge t1 t2  => inst (A := Val ty.int) t1 ι >= inst (A := Val ty.int) t2 ι
      | formula_gt t1 t2  => inst (A := Val ty.int) t1 ι >  inst (A := Val ty.int) t2 ι
      | formula_le t1 t2  => inst (A := Val ty.int) t1 ι <= inst (A := Val ty.int) t2 ι
      | formula_lt t1 t2  => inst (A := Val ty.int) t1 ι <  inst (A := Val ty.int) t2 ι
      | formula_eq t1 t2  => inst t1 ι =  inst t2 ι
      | formula_neq t1 t2 => inst t1 ι <> inst t2 ι
      end%Z.

  Global Instance inst_subst_formula : InstSubst Formula Prop.
  Proof.
    intros ? ? ? ? f.
    induction f; cbn; repeat f_equal; apply inst_subst.
  Qed.

  Import option.notations.
  Global Instance OccursCheckFormula : OccursCheck Formula :=
    fun Σ x xIn fml =>
      match fml with
      | formula_user p ts => option.map (formula_user p) (occurs_check xIn ts)
      | formula_bool t    => option.map formula_bool (occurs_check xIn t)
      | formula_prop ζ P  => option.map (fun ζ' => formula_prop ζ' P) (occurs_check xIn ζ)
      | formula_ge t1 t2  => t1' <- occurs_check xIn t1 ;; t2' <- occurs_check xIn t2 ;; Some (formula_ge t1' t2')
      | formula_gt t1 t2  => t1' <- occurs_check xIn t1 ;; t2' <- occurs_check xIn t2 ;; Some (formula_gt t1' t2')
      | formula_le t1 t2  => t1' <- occurs_check xIn t1 ;; t2' <- occurs_check xIn t2 ;; Some (formula_le t1' t2')
      | formula_lt t1 t2  => t1' <- occurs_check xIn t1 ;; t2' <- occurs_check xIn t2 ;; Some (formula_lt t1' t2')
      | formula_eq t1 t2  => t1' <- occurs_check xIn t1 ;; t2' <- occurs_check xIn t2 ;; Some (formula_eq t1' t2')
      | formula_neq t1 t2 => t1' <- occurs_check xIn t1 ;; t2' <- occurs_check xIn t2 ;; Some (formula_neq t1' t2')
      end.

  Global Instance occurs_check_laws_formula : OccursCheckLaws Formula.
  Proof. occurs_check_derive. Qed.

  (* The path condition expresses a set of constraints on the logic variables
     that encode the path taken during execution. *)
  Section PathCondition.

    Definition PathCondition (Σ : LCtx) : Type :=
      list (Formula Σ).

    Global Instance inst_pathcondition : Inst PathCondition Prop :=
      fix inst_pc {Σ} (pc : list (Formula Σ)) (ι : Valuation Σ) : Prop :=
        match pc with
        | nil => True
        | cons f pc => inst f ι /\ inst_pc pc ι
        end.

    Global Instance inst_subst_pathcondition : InstSubst PathCondition Prop.
    Proof.
      intros Σ Σ' ζ ι pc.
      induction pc; cbn; f_equal; auto using inst_subst.
    Qed.

    Lemma inst_pathcondition_cons {Σ} (ι : Valuation Σ) (f : Formula Σ) (pc : PathCondition Σ) :
      inst (cons f pc) ι <-> inst f ι /\ inst pc ι.
    Proof. reflexivity. Qed.

    Lemma inst_pathcondition_app {Σ} (ι : Valuation Σ) (pc1 pc2 : PathCondition Σ) :
      inst (app pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι.
    Proof.
      induction pc1; cbn.
      - intuition.
      - rewrite IHpc1. clear IHpc1. intuition.
    Qed.

    Lemma inst_pathcondition_rev_append {Σ} (ι : Valuation Σ) (pc1 pc2 : PathCondition Σ) :
      inst (List.rev_append pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι.
    Proof.
      revert pc2.
      induction pc1; cbn; intros pc2.
      - intuition.
      - rewrite IHpc1. clear IHpc1. cbn. intuition.
    Qed.

    Lemma inst_formula_eqs_ctx {Δ Σ} (ι : Valuation Σ) (xs ys : Env (Term Σ) Δ) :
      inst (T := PathCondition) (A := Prop) (formula_eqs_ctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs.
      - destruct (env.nilView ys). cbn. intuition.
      - destruct (env.snocView ys). cbn.
        rewrite IHxs. clear IHxs.
        change (inst db ι = inst v ι /\ inst xs ι = inst E ι <->
                inst xs ι ► (b ↦ inst db ι) = inst E ι ► (b ↦ inst v ι)).
        split.
        + now intros []; f_equal.
        + now intros []%env.inversion_eq_snoc.
    Qed.

    Lemma inst_formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ} (ι : Valuation Σ) (xs ys : NamedEnv (Term Σ) Δ) :
      inst (T := PathCondition) (A := Prop) (formula_eqs_nctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs.
      - destruct (env.nilView ys). cbn. intuition.
      - destruct (env.snocView ys). cbn.
        rewrite IHxs. clear IHxs.
        change (inst db ι = inst v ι /\ inst xs ι = inst E ι <->
                inst xs ι ► (b ↦ inst db ι) = inst E ι ► (b ↦ inst v ι)).
        split.
        + now intros []; f_equal.
        + now intros []%env.inversion_eq_snoc.
    Qed.

  End PathCondition.

  (* Avoid some Prop <-> Type confusion. *)
  Notation instpc pc ι := (@inst _ _ inst_pathcondition _ pc ι).

  Module Entailment.

    (* A preorder on path conditions. This encodes that either pc1 belongs to a
       longer symbolic execution path (or that it's the same path, but with
       potentially some constraints substituted away). *)
    Definition entails {Σ} (pc1 pc0 : PathCondition Σ) : Prop :=
      forall (ι : Valuation Σ),
        instpc pc1 ι ->
        instpc pc0 ι.
    Infix "⊢" := (@entails _).

    Definition entails_formula {Σ}
               (pc : PathCondition Σ) (f : Formula Σ) : Prop :=
      forall (ι : Valuation Σ),
        instpc pc ι -> (inst f ι : Prop).
    Infix "⊢f" := (@entails_formula _).

    Lemma entails_cons {Σ} (pc1 pc2 : PathCondition Σ) (f : Formula Σ) :
      (pc1 ⊢ pc2) /\ (pc1 ⊢f f) <-> (pc1 ⊢ (f :: pc2)%list).
    Proof. unfold entails, entails_formula. cbn. intuition. Qed.

    Definition entails_refl {Σ} : Reflexive (@entails Σ).
    Proof. now unfold Reflexive, entails. Qed.

    Definition entails_trans {Σ} : Transitive (@entails Σ).
    Proof. unfold Transitive, entails; eauto. Qed.

    Global Instance preorder_entails {Σ} : PreOrder (@entails Σ).
    Proof. split; auto using entails_refl, entails_trans. Qed.

    Lemma proper_subst_entails {Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc1 pc2 : PathCondition Σ1) :
      (pc1 ⊢ pc2) -> (subst pc1 ζ12 ⊢ subst pc2 ζ12).
    Proof.
      intros pc12 ι.
      rewrite ?inst_subst; eauto.
    Qed.

    Definition entails_eq {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ) (a0 a1 : AT Σ) : Prop :=
      forall (ι : Valuation Σ), instpc pc ι -> inst a0 ι = inst a1 ι.
    Notation "pc ⊢ a0 == a1" :=
      (entails_eq pc a0 a1)
      (at level 99, a1 at level 200, no associativity).

    (* Not sure this instance is a good idea...
       This seems to cause rewrite to take very long... *)
    Global Instance proper_entails_pc_iff
           {Σ} (pc : PathCondition Σ):
         Proper (entails_eq pc ==> iff) (entails pc).
    Proof.
      intros pc1 pc2 pc12.
      split; intros HYP ι ιpc;
        specialize (pc12 ι ιpc);
        specialize (HYP ι ιpc);
        congruence.
    Qed.

    Global Instance proper_entails_formula_iff
           {Σ} (pc : PathCondition Σ):
         Proper (entails_eq pc ==> iff) (entails_formula pc).
    Proof.
      intros pc1 pc2 pc12.
      split; intros HYP ι ιpc;
        specialize (pc12 ι ιpc);
        specialize (HYP ι ιpc);
        congruence.
    Qed.

    Global Instance proper_entails_eq_impl {AT A} {Σ} {Γ} : Proper (flip (@entails Σ) ==> eq ==> eq ==> impl) (@entails_eq AT A Γ Σ).
    Proof.
      intros pc1 pc2 pc21 a1 _ [] a2 _ [] eq1 ι ιpc2; eauto.
    Qed.

    Global Instance proper_entails_eq_flip_impl {AT A} `{Inst AT A} {Σ} : Proper ((@entails Σ) ==> eq ==> eq ==> flip impl) entails_eq.
    Proof.
      intros pc1 pc2 pc21 a1 _ [] a2 _ [] eq1 ι ιpc2; eauto.
    Qed.

    Global Instance equiv_entails_eq `{instA : Inst AT A} {Σ} {pc : PathCondition Σ} : Equivalence (entails_eq pc).
    Proof.
      split.
      - intuition.
      - intros x y xy ι ipc; specialize (xy ι); intuition.
      - intros x y z xy yz ι ipc.
        specialize (xy ι ipc).
        specialize (yz ι ipc).
        intuition.
    Qed.

    Global Instance proper_entails_eq_flip_impl_pc {AT A} `{Inst AT A} {Σ} {pc : PathCondition Σ}: Proper (entails_eq pc ==> entails_eq pc ==> iff) (entails_eq pc).
    Proof.
      split; intros Heq.
      - transitivity x; [|transitivity x0]; easy.
      - transitivity y; [|transitivity y0]; easy.
    Qed.

    Global Instance proper_entails_eq_sub_comp
           {Σ1 Σ2 Σ3} {ζ : Sub Σ1 Σ2} (pc : PathCondition Σ3):
      Proper (entails_eq pc ==> entails_eq pc) (subst ζ).
    Proof.
      intros ζ1 ζ2 ζ12.
      unfold entails_eq in *.
      intros ι Hpc. specialize (ζ12 ι Hpc).
      now rewrite ?inst_subst, ζ12.
    Qed.

  End Entailment.

End FormulasOn.
