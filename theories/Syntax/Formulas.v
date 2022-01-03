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
     Notation
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
  | formula_bool (t : Term Σ ty_bool)
  | formula_prop {Σ'} (ζ : Sub Σ' Σ) (P : abstract_named Val Σ' Prop)
  | formula_ge (t1 t2 : Term Σ ty_int)
  | formula_gt (t1 t2 : Term Σ ty_int)
  | formula_le (t1 t2 : Term Σ ty_int)
  | formula_lt (t1 t2 : Term Σ ty_int)
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

  Instance sub_formula : Subst Formula :=
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

  Instance substlaws_formula : SubstLaws Formula.
  Proof.
    constructor.
    { intros ? []; cbn; f_equal; apply subst_sub_id. }
    { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
  Qed.

  Definition inst_formula {Σ} (fml : Formula Σ) (ι : Valuation Σ) : Prop :=
    match fml with
    | formula_user p ts => env.uncurry (𝑷_inst p) (inst ts ι)
    | formula_bool t    => inst (A := Val ty_bool) t ι = true
    | formula_prop ζ P  => uncurry_named P (inst ζ ι)
    | formula_ge t1 t2  => inst (A := Val ty_int) t1 ι >= inst (A := Val ty_int) t2 ι
    | formula_gt t1 t2  => inst (A := Val ty_int) t1 ι >  inst (A := Val ty_int) t2 ι
    | formula_le t1 t2  => inst (A := Val ty_int) t1 ι <= inst (A := Val ty_int) t2 ι
    | formula_lt t1 t2  => inst (A := Val ty_int) t1 ι <  inst (A := Val ty_int) t2 ι
    | formula_eq t1 t2  => inst t1 ι =  inst t2 ι
    | formula_neq t1 t2 => inst t1 ι <> inst t2 ι
    end%Z.

  Instance instantiate_formula : Inst Formula Prop :=
    {| inst Σ := inst_formula;
       lift Σ P := formula_prop env.nil P
    |}.

  Instance instantiate_formula_laws : InstLaws Formula Prop.
  Proof.
    constructor; auto. intros Σ Σ' ζ ι t.
    induction t; cbn; repeat f_equal; apply inst_subst.
  Qed.

  Global Instance OccursCheckFormula : OccursCheck Formula :=
    fun Σ x xIn fml =>
          match fml with
          | formula_user p ts => option_map (formula_user p) (occurs_check xIn ts)
          | formula_bool t    => option_map formula_bool (occurs_check xIn t)
          | formula_prop ζ P  => option_map (fun ζ' => formula_prop ζ' P) (occurs_check xIn ζ)
          | formula_ge t1 t2  => option_ap (option_map (@formula_ge _) (occurs_check xIn t1)) (occurs_check xIn t2)
          | formula_gt t1 t2  => option_ap (option_map (@formula_gt _) (occurs_check xIn t1)) (occurs_check xIn t2)
          | formula_le t1 t2  => option_ap (option_map (@formula_le _) (occurs_check xIn t1)) (occurs_check xIn t2)
          | formula_lt t1 t2  => option_ap (option_map (@formula_lt _) (occurs_check xIn t1)) (occurs_check xIn t2)
          | formula_eq t1 t2  => option_ap (option_map (@formula_eq _ _) (occurs_check xIn t1)) (occurs_check xIn t2)
          | formula_neq t1 t2 => option_ap (option_map (@formula_neq _ _) (occurs_check xIn t1)) (occurs_check xIn t2)
            end.

  Global Instance OccursCheckLawsFormula : OccursCheckLaws Formula.
  Proof.
    constructor.
    - intros ? ? ? ? []; cbn; now rewrite ?occurs_check_shift.
    - intros ? ? ? [] fml' Heq; cbn in *;
        repeat
          lazymatch goal with
          | H: option_map _ _ = Some _ |- _ =>
              apply option_map_eq_some' in H; destruct_conjs; subst; cbn
          | H: option_ap _ _ = Some _ |- _ =>
              apply option_bind_eq_some in H; destruct_conjs; subst; cbn
          | H: @occurs_check ?T ?OC ?Σ ?b ?bIn ?t = Some ?t' |- _ =>
              apply (@occurs_check_sound T _ OC _ Σ b bIn t t') in H; subst
          end; auto.
  Qed.

  (* The path condition expresses a set of constraints on the logic variables
     that encode the path taken during execution. *)
  Section PathCondition.

    Definition PathCondition (Σ : LCtx) : Type :=
      list (Formula Σ).
    Fixpoint fold_right1 {A R} (cns : A -> R -> R) (sing : A -> R) (v : A) (l : list A) : R :=
      match l with
        nil => sing v
      | cons v' vs => cns v (fold_right1 cns sing v' vs)
      end.
    Definition fold_right10 {A R} (cns : A -> R -> R) (sing : A -> R) (nl : R) (l : list A) : R :=
      match l with
        nil => nl
      | cons v vs => fold_right1 cns sing v vs
      end.

    Lemma fold_right_1_10 {A} {cns : A -> Prop -> Prop} {sing : A -> Prop} {nl : Prop}
          (consNilIffSing : forall v, sing v <-> cns v nl)
          (v : A) (l : list A) :
          fold_right1 cns sing v l <-> cns v (fold_right10 cns sing nl l).
    Proof.
      induction l; cbn; auto.
    Qed.

    Lemma fold_right_1_10_prop {A} {P : A -> Prop}
          (v : A) (l : list A) :
          fold_right1 (fun v acc => P v /\ acc) P v l <-> P v /\ (fold_right10 (fun v acc => P v /\ acc) P True l).
    Proof.
      refine (fold_right_1_10 _ v l).
      intuition.
    Qed.

    (* Note: we use fold_right10 instead of fold_right to make inst_lift hold. *)
    Definition inst_pathcondition {Σ} (pc : PathCondition Σ) (ι : Valuation Σ) : Prop :=
      fold_right10 (fun fml pc => inst fml ι /\ pc) (fun fml => inst fml ι) True pc.
    Global Arguments inst_pathcondition : simpl never.

    Lemma inst_subst1 {Σ Σ' } (ζ : Sub Σ Σ') (ι : Valuation Σ') (f : Formula Σ) (pc : list (Formula Σ)) :
      fold_right1 (fun fml pc => inst fml ι /\ pc) (fun fml => inst fml ι) (subst f ζ) (subst pc ζ) =
      fold_right1 (fun fml pc => inst fml (inst ζ ι) /\ pc) (fun fml => inst fml (inst ζ ι)) f pc.
    Proof.
      revert f.
      induction pc; intros f; cbn.
      - apply inst_subst.
      - f_equal.
        + apply inst_subst.
        + apply IHpc.
    Qed.

    Lemma inst_subst10 {Σ Σ' } (ζ : Sub Σ Σ') (ι : Valuation Σ') (pc : list (Formula Σ)) :
      fold_right10 (fun fml pc => inst fml ι /\ pc) (fun fml => inst fml ι) True (subst pc ζ) =
      fold_right10 (fun fml pc => inst fml (inst ζ ι) /\ pc) (fun fml => inst fml (inst ζ ι)) True pc.
    Proof.
      destruct pc.
      - reflexivity.
      - apply inst_subst1.
    Qed.

    Global Instance instantiate_pathcondition : Inst PathCondition Prop :=
      {| inst Σ := inst_pathcondition;
         lift Σ P := cons (lift P : Formula Σ) nil
      |}.

    Global Instance instantiate_pathcondition_laws : InstLaws PathCondition Prop.
    Proof.
      constructor.
      - reflexivity.
      - intros Σ Σ' ζ ι pc.
        eapply inst_subst10.
    Qed.

    Lemma inst_pathcondition_cons {Σ} (ι : Valuation Σ) (f : Formula Σ) (pc : PathCondition Σ) :
      inst (cons f pc) ι <-> inst f ι /\ inst pc ι.
    Proof.
      apply (fold_right_1_10_prop (P := fun fml => inst fml ι)).
    Qed.

    Lemma inst_pathcondition_app {Σ} (ι : Valuation Σ) (pc1 pc2 : PathCondition Σ) :
      inst (app pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι.
    Proof.
      induction pc1; cbn [app].
      - intuition. constructor.
      - rewrite ?inst_pathcondition_cons.
        rewrite IHpc1. intuition.
    Qed.

    Lemma inst_pathcondition_rev_append {Σ} (ι : Valuation Σ) (pc1 pc2 : PathCondition Σ) :
      inst (List.rev_append pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι.
    Proof.
      revert pc2.
      induction pc1; cbn [List.rev_append]; intros pc2.
      - intuition. constructor.
      - rewrite IHpc1.
        rewrite ?inst_pathcondition_cons.
        intuition.
    Qed.

    Lemma inst_formula_eqs_ctx {Δ Σ} (ι : Valuation Σ) (xs ys : Env (Term Σ) Δ) :
      inst (T := PathCondition) (A := Prop) (formula_eqs_ctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs.
      - destruct (env.nilView ys). cbn. intuition. constructor.
      - destruct (env.snocView ys). cbn - [inst].
        rewrite inst_pathcondition_cons, IHxs. clear IHxs.
        change (inst db ι = inst v ι /\ inst xs ι = inst E ι <->
                inst xs ι ► (b ↦ inst db ι) = inst E ι ► (b ↦ inst v ι)).
        split.
        + intros [Hfml Hpc]; f_equal; auto.
        + intros Heq. apply noConfusion_inv in Heq. cbn in Heq.
          inversion Heq. intuition.
    Qed.

    Lemma inst_formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ} (ι : Valuation Σ) (xs ys : NamedEnv (Term Σ) Δ) :
      inst (T := PathCondition) (A := Prop) (formula_eqs_nctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs.
      - destruct (env.nilView ys). cbn. intuition. constructor.
      - destruct (env.snocView ys). cbn - [inst].
        rewrite inst_pathcondition_cons, IHxs. clear IHxs.
        change (inst db ι = inst v ι /\ inst xs ι = inst E ι <->
                inst xs ι ► (b ↦ inst db ι) = inst E ι ► (b ↦ inst v ι)).
        split.
        + intros [Hfml Hpc]; f_equal; auto.
        + intros ?%env.inversion_eq_snoc.
          intuition.
    Qed.

  End PathCondition.

  (* Avoid some Prop <-> Type confusion. *)
  Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

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
    Proof.
      split.
      - intros (pc12 & pc1f).
        intros ι ιpc1. cbn.
        unfold inst, inst_pathcondition. cbn.
        rewrite fold_right_1_10_prop.
        intuition.
      - intros pc1f2.
        split; intros ι ιpc1;
          specialize (pc1f2 ι ιpc1); cbn in pc1f2;
          unfold inst, inst_pathcondition in pc1f2; cbn in pc1f2;
          rewrite fold_right_1_10_prop in pc1f2;
          destruct pc1f2 as [Hf Hpc2]; auto.
    Qed.

    Definition entails_refl {Σ} : Reflexive (@entails Σ).
    Proof. now unfold Reflexive, entails. Qed.

    Definition entails_trans {Σ} : Transitive (@entails Σ).
    Proof. unfold Transitive, entails; eauto. Qed.

    Global Instance preorder_entails {Σ} : PreOrder (@entails Σ).
    Proof. split; auto using entails_refl, entails_trans. Qed.

    (* Global Instance proper_subst_pc_entails {Σ1 Σ2} : *)
    (*   Proper ((@entails Σ1) ==> eq ==> (@entails Σ2)) (subst (T := PathCondition)) . *)
    (* Proof. *)
    (*   intros pc1 pc2 pc12 ι. *)
    (*   rewrite ?inst_subst; eauto. *)
    (* Qed. *)

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

    (* Global Instance proper_subst_entails_eq {AT A} `{InstLaws AT A} {Σ1 Σ2} {ζ : Sub Σ1 Σ2} {pc : PathCondition Σ1} : *)
    (*   Proper ((entails_eq pc) ==> (entails_eq (subst pc ζ))) (subst ζ). *)
    (* Proof. *)
    (*   intros a1 a2 a12 ι. *)
    (*   rewrite ?inst_subst; auto. *)
    (* Qed. *)

    (* Global Instance proper_subst_entails_eq_pc *)
    (*        {Σ1 Σ2} `{InstLaws AT A} *)
    (*        (pc : PathCondition Σ2): *)
    (*   Proper (entails_eq pc ==> eq ==> entails_eq pc) (@subst AT _ Σ1 Σ2). *)
    (* Proof. *)
    (*   intros ζ1 ζ2 ζ12 a1 a2 [] ι ιpc. *)
    (*   rewrite ?inst_subst. *)
    (*   now rewrite (ζ12 ι ιpc). *)
    (* Qed. *)


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

    (* Infix "⊢" := (@entails _) (at level 80, no associativity). *)
    (* Infix "⊢f" := (@entails_formula _) (at level 80, no associativity). *)
    (* Notation "pc ⊢ a0 == a1" := *)
    (*   (entails_eq pc a0 a1) *)
    (*     (at level 80, a0 at next level, no associativity). *)

  End Entailment.

End FormulasOn.
