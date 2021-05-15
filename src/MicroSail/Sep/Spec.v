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

From Coq Require
     Vector.
From Coq Require Import
     Bool.Bool
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Program.Basics
     Program.Tactics
     String.

From MicroSail Require Import
     Notation
     Sep.Logic
     Syntax.

From Equations Require Import
     Equations.

Import CtxNotations.
Import EnvNotations.

Set Implicit Arguments.

Module Type AssertionKit
       (termkit : TermKit)
       (Export progkit : ProgramKit termkit).

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Declare Instance 𝑷_eq_dec : EqDec 𝑷.

End AssertionKit.

Module Assertions
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (Export assertkit : AssertionKit termkit progkit).

  Inductive Formula (Σ : LCtx) : Type :=
  | formula_bool (t : Term Σ ty_bool)
  | formula_prop {Σ'} (ζ : Sub Σ' Σ) (P : abstract_named Lit Σ' Prop)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).
  Arguments formula_bool {_} t.

  Equations(noeqns) formula_eqs {Δ : PCtx} {Σ : LCtx}
    (δ δ' : NamedEnv (Term Σ) Δ) : list (Formula Σ) :=
    formula_eqs env_nil          env_nil            := nil;
    formula_eqs (env_snoc δ _ t) (env_snoc δ' _ t') :=
      formula_eq t t' :: formula_eqs δ δ'.

  Instance sub_formula : Subst Formula :=
    fun Σ1 Σ2 ζ fml =>
      match fml with
      | formula_bool t    => formula_bool (subst ζ t)
      | formula_prop ζ' P => formula_prop (subst ζ ζ') P
      | formula_eq t1 t2  => formula_eq (subst ζ t1) (subst ζ t2)
      | formula_neq t1 t2 => formula_neq (subst ζ t1) (subst ζ t2)
      end.

  Instance substlaws_formula : SubstLaws Formula.
  Proof.
    constructor.
    { intros ? []; cbn; f_equal; apply subst_sub_id. }
    { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
  Qed.

  Definition inst_formula {Σ} (ι : SymInstance Σ) (fml : Formula Σ) : Prop :=
    match fml with
    | formula_bool t    => is_true (inst (A := Lit ty_bool) ι t)
    | formula_prop ζ P  => uncurry_named P (inst ι ζ)
    | formula_eq t1 t2  => inst ι t1 =  inst ι t2
    | formula_neq t1 t2 => inst ι t1 <> inst ι t2
    end.

  Instance instantiate_formula : Inst Formula Prop :=
    {| inst Σ := inst_formula;
       lift Σ P := formula_prop env_nil P
    |}.

  Instance instantiate_formula_laws : InstLaws Formula Prop.
  Proof.
    constructor; auto.
    intros Σ Σ' ζ ι t.
    induction t.
    - unfold subst, sub_formula, inst at 1 2, instantiate_formula, inst_formula.
      f_equal.
      apply inst_subst.
    - unfold subst, sub_formula, inst at 1 2, instantiate_formula, inst_formula.
      f_equal.
      eapply inst_subst.
    - unfold subst, sub_formula, inst at 1 2, instantiate_formula, inst_formula.
      f_equal; eapply inst_subst.
    - unfold subst, sub_formula, inst at 1 2, instantiate_formula, inst_formula.
      repeat f_equal; eapply inst_subst.
  Qed.

  Global Instance OccursCheckFormula : OccursCheck Formula :=
    fun Σ x xIn fml =>
          match fml with
          | formula_bool t    => option_map formula_bool (occurs_check xIn t)
          | formula_prop ζ P  => option_map (fun ζ' => formula_prop ζ' P) (occurs_check xIn ζ)
          | formula_eq t1 t2  => option_ap (option_map (@formula_eq _ _) (occurs_check xIn t1)) (occurs_check xIn t2)
          | formula_neq t1 t2 => option_ap (option_map (@formula_neq _ _) (occurs_check xIn t1)) (occurs_check xIn t2)
            end.

  Global Instance OccursCheckLawsFormula : OccursCheckLaws Formula.
  Proof.
    constructor.
    - intros ? ? ? ? []; cbn;
        now rewrite ?occurs_check_shift.
    - intros ? ? ? [] fml' Heq; cbn in *.
      + apply option_map_eq_some' in Heq; destruct_conjs; subst; cbn.
        f_equal. now apply (occurs_check_sound (T := fun Σ => Term Σ _)).
      + apply option_map_eq_some' in Heq; destruct_conjs; subst; cbn.
        f_equal. now apply occurs_check_sound.
      + apply option_bind_eq_some in Heq; destruct Heq as (f & Heq1 & Heq2).
        apply option_bind_eq_some in Heq1; destruct Heq1 as (t1' & Heq11 & Heq12).
        apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq11. subst t1.
        apply noConfusion_inv in Heq12; cbn in Heq12; subst f; cbn.
        apply option_bind_eq_some in Heq2; destruct Heq2 as (t2' & Heq21 & Heq22).
        apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq21. subst t2.
        apply noConfusion_inv in Heq22; cbn in Heq22; subst fml'; cbn.
        reflexivity.
      + apply option_bind_eq_some in Heq; destruct Heq as (f & Heq1 & Heq2).
        apply option_bind_eq_some in Heq1; destruct Heq1 as (t1' & Heq11 & Heq12).
        apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq11. subst t1.
        apply noConfusion_inv in Heq12; cbn in Heq12; subst f; cbn.
        apply option_bind_eq_some in Heq2; destruct Heq2 as (t2' & Heq21 & Heq22).
        apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq21. subst t2.
        apply noConfusion_inv in Heq22; cbn in Heq22; subst fml'; cbn.
        reflexivity.
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
    Fixpoint fold_right10 {A R} (cns : A -> R -> R) (sing : A -> R) (nl : R) (l : list A) : R :=
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
    Definition inst_pathcondition {Σ} (ι : SymInstance Σ) (pc : PathCondition Σ) : Prop :=
      fold_right10 (fun fml pc => inst ι fml /\ pc) (fun fml => inst ι fml) True pc.
    Global Arguments inst_pathcondition : simpl never.

    Lemma inst_subst1 {Σ Σ' } (ζ : Sub Σ Σ') (ι : SymInstance Σ') (f : Formula Σ) (pc : list (Formula Σ)) :
      fold_right1 (fun fml pc => inst ι fml /\ pc) (fun fml => inst ι fml) (subst ζ f) (subst ζ pc) =
      fold_right1 (fun fml pc => inst (inst ι ζ) fml /\ pc) (fun fml => inst (inst ι ζ) fml) f pc.
    Proof.
      revert f.
      induction pc; intros f; cbn.
      - apply inst_subst.
      - f_equal.
        + apply inst_subst.
        + apply IHpc.
    Qed.

    Lemma inst_subst10 {Σ Σ' } (ζ : Sub Σ Σ') (ι : SymInstance Σ') (pc : list (Formula Σ)) :
      fold_right10 (fun fml pc => inst ι fml /\ pc) (fun fml => inst ι fml) True (subst ζ pc) =
      fold_right10 (fun fml pc => inst (inst ι ζ) fml /\ pc) (fun fml => inst (inst ι ζ) fml) True pc.
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

    Lemma inst_pathcondition_cons {Σ} (ι : SymInstance Σ) (f : Formula Σ) (pc : PathCondition Σ) :
      inst ι (cons f pc) <-> inst ι f /\ inst ι pc.
    Proof.
      apply fold_right_1_10_prop.
    Qed.

    Lemma inst_formula_eqs {Δ Σ} (ι : SymInstance Σ) (xs ys : SStore Δ Σ) :
      inst (T := PathCondition) (A := Prop)ι (formula_eqs xs ys) <-> inst ι xs = inst ι ys.
    Proof.
      induction xs.
      - destruct (nilView ys). cbn. intuition. constructor.
      - destruct (snocView ys). cbn - [inst].
        rewrite inst_pathcondition_cons, IHxs. clear IHxs.
        change (inst ι db = inst ι v /\ inst ι xs = inst ι E <->
                inst ι xs ► (b ↦ inst ι db) = inst ι E ► (b ↦ inst ι v)).
        split.
        + intros [Hfml Hpc]; f_equal; auto.
        + intros Heq. apply noConfusion_inv in Heq. cbn in Heq.
          inversion Heq. intuition.
    Qed.

  End PathCondition.

  (* Avoid some Prop <-> Type confusion. *)
  Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

  Module Entailment.

    (* A preorder on path conditions. This encodes that either pc1 belongs to a
       longer symbolic execution path (or that it's the same path, but with
       potentially some constraints substituted away). *)
    Definition entails {Σ} (pc1 pc0 : PathCondition Σ) : Prop :=
      forall (ι : SymInstance Σ),
        instpc ι pc1 ->
        instpc ι pc0.
    Infix "⊢" := (@entails _) (at level 80, no associativity).

    Definition entails_formula {Σ}
               (pc : PathCondition Σ) (f : Formula Σ) : Prop :=
      forall (ι : SymInstance Σ),
        instpc ι pc -> (inst ι f : Prop).
    Infix "⊢f" := (@entails_formula _) (at level 80, no associativity).

    Lemma entails_cons {Σ} (pc1 pc2 : PathCondition Σ) (f : Formula Σ) :
      (pc1 ⊢ pc2 /\ pc1 ⊢f f) <-> pc1 ⊢ (f :: pc2)%list.
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

    Global Instance preorder_entails {Σ} : PreOrder (@entails Σ).
    Proof.
      split.
      - intuition.
      - intros x y z xy yz ι ιx.
        eauto.
    Qed.

    Global Instance proper_subst_pc_entails {Σ1 Σ2} {ζ}: Proper ((@entails Σ1) ==> (@entails Σ2)) (subst ζ).
    Proof.
      intros pc1 pc2 pc12 ι.
      rewrite ?inst_subst; eauto.
    Qed.

    Definition entails_eq {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ) (a0 a1 : AT Σ) : Prop :=
      forall (ι : SymInstance Σ), instpc ι pc -> inst ι a0 = inst ι a1.
    Notation "pc ⊢ a0 == a1" :=
      (entails_eq pc a0 a1)
      (at level 80, a0 at next level, no associativity).

    Global Instance proper_subst_entails_eq {AT A} `{InstLaws AT A} {Σ1 Σ2} {ζ : Sub Σ1 Σ2} {pc : PathCondition Σ1} :
      Proper ((entails_eq pc) ==> (entails_eq (subst ζ pc))) (subst ζ).
    Proof.
      intros a1 a2 a12 ι.
      rewrite ?inst_subst; auto.
    Qed.

    Global Instance proper_subst_entails_eq_pc
           {Σ1 Σ2} `{InstLaws AT A}
           (pc : PathCondition Σ2):
      Proper (entails_eq pc ==> eq ==> entails_eq pc) (@subst AT _ Σ1 Σ2).
    Proof.
      intros ζ1 ζ2 ζ12 a1 a2 [] ι ιpc.
      rewrite ?inst_subst.
      now rewrite (ζ12 ι ιpc).
    Qed.


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
      Proper (entails_eq pc ==> entails_eq pc) (sub_comp ζ).
    Proof.
      intros ζ1 ζ2 ζ12.
      unfold sub_comp; rewrite ζ12; easy.
    Qed.

    (* Infix "⊢" := (@entails _) (at level 80, no associativity). *)
    (* Infix "⊢f" := (@entails_formula _) (at level 80, no associativity). *)
    (* Notation "pc ⊢ a0 == a1" := *)
    (*   (entails_eq pc a0 a1) *)
    (*     (at level 80, a0 at next level, no associativity). *)

  End Entailment.

  Section Solver.

    Definition try_solve_eq {Σ σ} (t1 t2 : Term Σ σ) : option bool :=
      if Term_eqb t1 t2
      then Some true
      else
        (* If the terms are literals, we can trust the negative result. *)
        match t1 , t2 with
        | term_lit _ _ , term_lit _ _ => Some false
        | term_inr _   , term_inl _   => Some false
        | term_inl _   , term_inr _   => Some false
        | _            , _            => None
        end.

    Lemma try_solve_eq_spec {Σ σ} (t1 t2 : Term Σ σ) :
      OptionSpec
        (fun b => forall ι, inst ι t1 = inst ι t2 <-> is_true b)
        True
        (try_solve_eq t1 t2).
    Proof.
      unfold try_solve_eq.
      destruct (Term_eqb_spec t1 t2).
      - constructor. intros. apply reflect_iff.
        constructor. congruence.
      - destruct t1; dependent elimination t2; constructor; auto;
        intros; apply reflect_iff; constructor; cbn; congruence.
    Qed.

    (* Check if the given formula is always true or always false for any
       assignments of the logic variables. *)
    Definition try_solve_formula {Σ} (fml : Formula Σ) : option bool :=
      match fml with
      | formula_bool t =>
        match t in Term _ σ return option (Lit σ)
        with
        | term_lit _ b => Some b
        | _            => None
        end
      | formula_prop _ _ => None
      | formula_eq t1 t2 => try_solve_eq t1 t2
        (* else Term_eqvb t1 t2 *)
      | formula_neq t1 t2 => option_map negb (try_solve_eq t1 t2)
        (* else option_map negb (Term_eqvb t1 t2) *)
      end.

    Lemma try_solve_formula_spec {Σ} (fml : Formula Σ) :
      OptionSpec
        (fun b => forall ι, inst ι fml <-> is_true b)
        True
        (try_solve_formula fml).
    Proof.
      destruct fml; cbn.
      - dependent elimination t; constructor; auto.
      - constructor; auto.
      - destruct (try_solve_eq_spec t1 t2); now constructor.
      - destruct (try_solve_eq_spec t1 t2); constructor; auto.
        intros ι. specialize (H ι). destruct a; intuition.
    Qed.

    (* Poor man's unification *)
    Definition try_unify {Σ σ} (t1 t2 : Term Σ σ) :
      option { Σ' & MultiSub Σ Σ' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term Σ σ =>
          match occurs_check ςInΣ t2 with
          | Some t => Some (existT _ (multisub_cons ς t multisub_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_propagate {Σ} (fml : Formula Σ) :
      option { Σ' & MultiSub Σ Σ' } :=
      match fml with
      | formula_eq t1 t2 =>
        match try_unify t1 t2 with
        | Some r => Some r
        | None => try_unify t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_spec {Σ σ} (t1 t2 : Term Σ σ) :
      OptionSpec (fun '(existT Σ' ζ) => forall ι, inst ι t1 = inst ι t2 <-> inst_multisub ι ζ) True (try_unify t1 t2).
    Proof.
      unfold try_unify. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:Heq; constructor; auto.
      apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq. subst.
      intros ι. rewrite inst_subst, inst_sub_shift.
      cbn. intuition.
    Qed.

    Lemma try_propagate_spec {Σ} (fml : Formula Σ) :
      OptionSpec (fun '(existT Σ' ζ) => forall ι, (inst ι fml : Prop) <-> inst_multisub ι ζ) True (try_propagate fml).
    Proof.
      unfold try_propagate; destruct fml; cbn; try (constructor; auto; fail).
      destruct (try_unify_spec t1 t2) as [[Σ' ζ] HYP|_]. constructor. auto.
      destruct (try_unify_spec t2 t1) as [[Σ' ζ] HYP|_]. constructor.
      intros ι. specialize (HYP ι). intuition.
      now constructor.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
       formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) (right _) := false
      };
      formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) (right _) := false
      };
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      induction f1; dependent elimination f2;
        simp formula_eqb;
        try (constructor; auto; fail).
      - destruct (Term_eqb_spec t t0); constructor; intuition.
      - destruct (eq_dec σ σ0); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
      - destruct (eq_dec σ σ1); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
    Qed.

    Fixpoint try_assumption {Σ} (pc : PathCondition Σ) (fml : Formula Σ) {struct pc} : bool :=
      match pc with
      | nil       => false
      | cons f pc => formula_eqb f fml ||| try_assumption pc fml
      end.

    Lemma try_assumption_spec {Σ} (pc : PathCondition Σ) (fml : Formula Σ) :
      BoolSpec (forall ι, instpc ι pc -> inst (A := Prop) ι fml) True (try_assumption pc fml).
    Proof.
      induction pc; cbn.
      - constructor; auto.
      - destruct (formula_eqb_spec a fml).
        + subst a. constructor. intros ι.
          rewrite inst_pathcondition_cons.
          intuition.
        + destruct IHpc.
          * constructor. intros ι.
            rewrite inst_pathcondition_cons.
            intuition.
          * constructor; auto.
    Qed.

    Definition solver {Σ0} (pc : PathCondition Σ0) (fml : Formula Σ0) :
      option { Σ1 & MultiSub Σ0 Σ1 * List Formula Σ1 }%type :=
      match try_propagate fml with
      | Some (existT Σ1 vareqs) => Some (existT Σ1 (vareqs , nil))
      | None =>
        match try_solve_formula fml with
        | Some true => Some (existT Σ0 (multisub_id , nil))
        | Some false => None
        | None =>
          if try_assumption pc fml
          then Some (existT Σ0 (multisub_id , nil))
          else Some (existT Σ0 (multisub_id , (cons fml nil)))
        end
      end.

    Lemma inst_multisub_inst_sub_multi {Σ0 Σ1} (ζ01 : MultiSub Σ0 Σ1) (ι1 : SymInstance Σ1) :
      inst_multisub (inst ι1 (sub_multi ζ01)) ζ01.
    Proof.
        induction ζ01; cbn; auto.
        unfold sub_comp.
        rewrite <- inst_sub_shift.
        rewrite <- ?inst_subst.
        repeat
          match goal with
          | |- context[subst ?ζ1 ?ζ2] =>
            change (subst ζ1 ζ2) with (sub_comp ζ2 ζ1)
          end.
        rewrite <- inst_lookup.
        rewrite lookup_sub_comp.
        rewrite lookup_sub_single_eq.
        rewrite <- subst_sub_comp.
        rewrite <- sub_comp_assoc.
        rewrite sub_comp_shift_single.
        rewrite sub_comp_id_left.
        split; auto.
    Qed.

    Lemma solver_spec {Σ0} (pc : PathCondition Σ0) (fml : Formula Σ0) :
      OptionSpec
        (fun '(existT Σ1 (ζ, fmls)) =>
           forall ι0,
             instpc ι0 pc ->
             (inst (A:= Prop) ι0 fml -> inst_multisub ι0 ζ) /\
             (forall ι1,
                 ι0 = inst ι1 (sub_multi ζ) ->
                 inst ι0 fml <-> inst ι1 fmls))
        (forall ι, instpc ι pc -> inst (A := Prop) ι fml -> False)
        (solver pc fml).
    Proof.
      unfold solver.
      destruct (try_propagate_spec fml) as [[Σ1 ζ01]|].
      { constructor. intros ι0 Hpc. specialize (H ι0).
        split. intuition. intros ι1 ->.
        change (inst (inst ι1 (sub_multi ζ01)) fml <-> True).
        intuition. clear H. apply H1.
        apply inst_multisub_inst_sub_multi.
      }
      clear H.
      destruct (try_solve_formula_spec fml) as [b|].
      { destruct b.
        - constructor. intros ι0 Hpc. cbn. split; auto.
          intros ? Hι. rewrite inst_sub_id in Hι. subst ι1.
          specialize (H ι0). intuition. constructor.
        - constructor. unfold is_true in H. intuition.
      }
      clear H.
      destruct (try_assumption_spec pc fml).
      { constructor. intros ι0 Hpc. specialize (H ι0).
        cbn. split; auto. intros ι1 ->.
        rewrite inst_sub_id in *. intuition.
        constructor.
      }
      clear H.
      { constructor. intros ι0 Hpc. split.
        cbn; auto. intros ι1 ->.
        rewrite inst_pathcondition_cons.
        cbn. rewrite inst_sub_id.
        intuition. constructor.
      }
    Qed.

  End Solver.

  Section Chunks.

    (* Semi-concrete chunks *)
    Inductive SCChunk : Type :=
    | scchunk_user   (p : 𝑷) (vs : Env Lit (𝑷_Ty p))
    | scchunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ).
    Global Arguments scchunk_user _ _ : clear implicits.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive NoConfusion for SCChunk.
    End TransparentObligations.

    (* Symbolic chunks *)
    Inductive Chunk (Σ : LCtx) : Type :=
    | chunk_user   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
    | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).
    Global Arguments chunk_user [_] _ _.

    Definition chunk_eqb {Σ} (c1 c2 : Chunk Σ) : bool :=
      match c1 , c2 with
      | chunk_user p1 ts1, chunk_user p2 ts2 =>
        match eq_dec p1 p2 with
        | left e => env_eqb_hom
                      (@Term_eqb _)
                      (eq_rect _ (fun p => Env _ (𝑷_Ty p)) ts1 _ e)
                      ts2
        | right _ => false
        end
      | chunk_ptsreg r1 t1 , chunk_ptsreg r2 t2 =>
        match eq_dec_het r1 r2 with
        | left e  => Term_eqb
                       (eq_rect _ (Term Σ) t1 _ (f_equal projT1 e))
                       t2
        | right _ => false
        end
      | _ , _ => false
      end.

    (* Equations(noeqns) chunk_eqb {Σ} (c1 c2 : Chunk Σ) : bool := *)
    (*   chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) *)
    (*   with eq_dec p1 p2 => { *)
    (*     chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) (left eq_refl) := env_eqb_hom (@Term_eqb _) ts1 ts2; *)
    (*     chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) (right _)      := false *)
    (*   }; *)
    (*   chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) *)
    (*   with eq_dec_het r1 r2 => { *)
    (*     chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := Term_eqb t1 t2; *)
    (*     chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := false *)
    (*   }; *)
    (*   chunk_eqb _ _  := false. *)

    Global Instance sub_chunk : Subst Chunk :=
      fun Σ1 Σ2 ζ c =>
        match c with
        | chunk_user p ts => chunk_user p (subst ζ ts)
        | chunk_ptsreg r t => chunk_ptsreg r (subst ζ t)
        end.

    Global Instance substlaws_chunk : SubstLaws Chunk.
    Proof.
      constructor.
      { intros ? []; cbn; f_equal; apply subst_sub_id. }
      { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
    Qed.

    Global Instance inst_chunk : Inst Chunk SCChunk :=
      {| inst Σ ι c := match c with
                       | chunk_user p ts => scchunk_user p (inst ι ts)
                       | chunk_ptsreg r t => scchunk_ptsreg r (inst ι t)
                       end;
         lift Σ c   := match c with
                       | scchunk_user p vs => chunk_user p (lift vs)
                       | scchunk_ptsreg r v => chunk_ptsreg r (lift v)
                       end
      |}.

    Global Instance instlaws_chunk : InstLaws Chunk SCChunk.
    Proof.
      constructor.
      - intros ? ? []; cbn; f_equal; apply inst_lift.
      - intros ? ? ζ ι []; cbn; f_equal; apply inst_subst.
    Qed.

    Global Instance OccursCheckChunk :
      OccursCheck Chunk :=
      fun Σ b bIn c =>
        match c with
        | chunk_user p ts => option_map (chunk_user p) (occurs_check bIn ts)
        | chunk_ptsreg r t => option_map (chunk_ptsreg r) (occurs_check bIn t)
        end.

  End Chunks.

  Section Heaps.

    Definition SCHeap : Type := list SCChunk.
    Definition SHeap : LCtx -> Type := List Chunk.

    Global Instance inst_heap : Inst SHeap SCHeap :=
      instantiate_list.
    Global Instance instlaws_heap : InstLaws SHeap SCHeap.
    Proof. apply instantiatelaws_list. Qed.

  End Heaps.

  Section Messages.

    (* A record to collect information passed to the user. *)
    Record Message (Σ : LCtx) : Type :=
      MkMessage
        { msg_function        : string;
          msg_message         : string;
          msg_program_context : PCtx;
          msg_localstore      : SStore msg_program_context Σ;
          msg_heap            : SHeap Σ;
          msg_pathcondition   : PathCondition Σ;
        }.
    Global Arguments MkMessage {Σ} _ _ _ _ _ _.

    Global Instance SubstMessage : Subst Message :=
      fun Σ1 Σ2 ζ12 err =>
        match err with
        | MkMessage f m Γ δ h pc => MkMessage f m Γ (subst ζ12 δ) (subst ζ12 h) (subst ζ12 pc)
        end.

    Global Instance SubstLawsMessage : SubstLaws Message.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Global Instance OccursCheckMessage : OccursCheck Message :=
      fun Σ x xIn msg =>
        match msg with
        | MkMessage f m Γ δ h pc =>
          option_ap
            (option_ap
               (option_map
                  (MkMessage f m Γ)
                  (occurs_check xIn δ))
               (occurs_check xIn h))
            (occurs_check xIn pc)
        end.

    Inductive Error (Σ : LCtx) (msg : Message Σ) : Prop :=.

  End Messages.

  Inductive Assertion (Σ : LCtx) : Type :=
  | asn_formula (fml : Formula Σ)
  | asn_chunk (c : Chunk Σ)
  | asn_if   (b : Term Σ ty_bool) (a1 a2 : Assertion Σ)
  | asn_match_enum (E : 𝑬) (k : Term Σ (ty_enum E)) (alts : forall (K : 𝑬𝑲 E), Assertion Σ)
  | asn_match_sum (σ τ : Ty) (s : Term Σ (ty_sum σ τ)) (xl : 𝑺) (alt_inl : Assertion (Σ ▻ (xl :: σ))) (xr : 𝑺) (alt_inr : Assertion (Σ ▻ (xr :: τ)))
  | asn_match_list
      {σ : Ty} (s : Term Σ (ty_list σ)) (alt_nil : Assertion Σ) (xh xt : 𝑺)
      (alt_cons : Assertion (Σ ▻ xh∶σ ▻ xt∶ty_list σ))
  | asn_match_pair
      {σ1 σ2 : Ty} (s : Term Σ (ty_prod σ1 σ2))
      (xl xr : 𝑺) (rhs : Assertion (Σ ▻ xl∶σ1 ▻ xr∶σ2))
  | asn_match_tuple
      {σs : Ctx Ty} {Δ : LCtx} (s : Term Σ (ty_tuple σs))
      (p : TuplePat σs Δ) (rhs : Assertion (Σ ▻▻ Δ))
  | asn_match_record
      {R : 𝑹} {Δ : LCtx} (s : Term Σ (ty_record R))
      (p : RecordPat (𝑹𝑭_Ty R) Δ) (rhs : Assertion (Σ ▻▻ Δ))
  | asn_match_union
      {U : 𝑼} (s : Term Σ (ty_union U))
      (alt__ctx : forall (K : 𝑼𝑲 U), LCtx)
      (alt__pat : forall (K : 𝑼𝑲 U), Pattern (alt__ctx K) (𝑼𝑲_Ty K))
      (alt__rhs : forall (K : 𝑼𝑲 U), Assertion (Σ ▻▻ alt__ctx K))
  | asn_sep  (a1 a2 : Assertion Σ)
  | asn_exist (ς : 𝑺) (τ : Ty) (a : Assertion (Σ ▻ (ς :: τ)))
  | asn_debug.
  Arguments asn_match_enum [_] E _ _.
  Arguments asn_match_sum [_] σ τ _ _ _.
  Arguments asn_match_list [_] {σ} s alt_nil xh xt alt_cons.
  Arguments asn_match_pair [_] {σ1 σ2} s xl xr rhs.
  Arguments asn_match_tuple [_] {σs Δ} s p rhs.
  Arguments asn_match_record [_] R {Δ} s p rhs.
  Arguments asn_match_union [_] U s alt__ctx alt__pat alt__rhs.
  Arguments asn_exist [_] _ _ _.
  Arguments asn_debug {_}.

  Notation asn_bool b := (asn_formula (formula_bool b)).
  Notation asn_prop Σ P := (asn_formula (@formula_prop Σ Σ (sub_id Σ) P)).
  Notation asn_eq t1 t2 := (asn_formula (formula_eq t1 t2)).
  Notation asn_true := (asn_bool (term_lit ty_bool true)).
  Notation asn_false := (asn_bool (term_lit ty_bool false)).

  (* Instance sub_assertion : Subst Assertion := *)
  (*   fix sub_assertion {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (a : Assertion Σ1) {struct a} : Assertion Σ2 := *)
  (*     match a with *)
  (*     | asn_formula fml => asn_formula (subst ζ fml) *)
  (*     | asn_chunk c => asn_chunk (subst ζ c) *)
  (*     | asn_if b a1 a2 => asn_if (subst ζ b) (sub_assertion ζ a1) (sub_assertion ζ a2) *)
  (*     | asn_match_enum E k alts => *)
  (*       asn_match_enum E (subst ζ k) (fun z => sub_assertion ζ (alts z)) *)
  (*     | asn_match_sum σ τ t xl al xr ar => *)
  (*       asn_match_sum σ τ (subst ζ t) xl (sub_assertion (sub_up1 ζ) al) xr (sub_assertion (sub_up1 ζ) ar) *)
  (*     | asn_match_list s anil xh xt acons => *)
  (*       asn_match_list (subst ζ s) (sub_assertion ζ anil) xh xt (sub_assertion (sub_up1 (sub_up1 ζ)) acons) *)
  (*     | asn_match_pair s xl xr asn => *)
  (*       asn_match_pair (subst ζ s) xl xr (sub_assertion (sub_up1 (sub_up1 ζ)) asn) *)
  (*     | asn_match_tuple s p rhs => *)
  (*       asn_match_tuple (subst ζ s) p (sub_assertion _ rhs) *)
  (*     | asn_match_record R s p rhs => *)
  (*       asn_match_record R (subst ζ s) p (sub_assertion _ rhs) *)
  (*     | asn_match_union U s ctx pat rhs => *)
  (*       asn_match_union U (subst ζ s) ctx pat (fun K => sub_assertion _ (rhs K)) *)
  (*     | asn_sep a1 a2 => asn_sep (sub_assertion ζ a1) (sub_assertion ζ a2) *)
  (*     | asn_exist ς τ a => asn_exist ς τ (sub_assertion (sub_up1 ζ) a) *)
  (*     | asn_debug => asn_debug *)
  (*     end. *)

  Global Instance OccursCheckAssertion :
    OccursCheck Assertion :=
    fix occurs Σ b (bIn : b ∈ Σ) (asn : Assertion Σ) : option (Assertion (Σ - b)) :=
      match asn with
      | asn_formula fml => option_map (@asn_formula _) (occurs_check bIn fml)
      | asn_chunk c     => option_map (@asn_chunk _) (occurs_check bIn c)
      | asn_if b a1 a2  =>
        option_ap (option_ap (option_map (@asn_if _) (occurs_check bIn b)) (occurs _ _ bIn a1)) (occurs _ _ bIn a2)
      | asn_match_enum E k alts => None (* TODO *)
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        option_ap
          (option_ap
             (option_map
                (fun s' alt_inl' alt_inr' =>
                   asn_match_sum σ τ s' xl alt_inl' xr alt_inr')
                (occurs_check bIn s))
             (occurs (Σ ▻ (xl :: σ)) b (inctx_succ bIn) alt_inl))
          (occurs (Σ ▻ (xr :: τ)) b (inctx_succ bIn) alt_inr)
      | @asn_match_list _ σ s alt_nil xh xt alt_cons => None (* TODO *)
      | @asn_match_pair _ σ1 σ2 s xl xr rhs => None (* TODO *)
      | @asn_match_tuple _ σs Δ s p rhs => None (* TODO *)
      | @asn_match_record _ R4 Δ s p rhs => None (* TODO *)
      | asn_match_union U s alt__ctx alt__pat alt__rhs => None (* TODO *)
      | asn_sep a1 a2 => option_ap (option_map (@asn_sep _) (occurs _ _ bIn a1)) (occurs _ _ bIn a2)
      | asn_exist ς τ a => option_map (@asn_exist _ ς τ) (occurs _ _ (inctx_succ bIn) a)
      | asn_debug => Some asn_debug
      end.

  Record SepContract (Δ : PCtx) (τ : Ty) : Type :=
    MkSepContract
      { sep_contract_logic_variables  : LCtx;
        sep_contract_localstore       : SStore Δ sep_contract_logic_variables;
        sep_contract_precondition     : Assertion sep_contract_logic_variables;
        sep_contract_result           : 𝑺;
        sep_contract_postcondition    : Assertion (sep_contract_logic_variables ▻ (sep_contract_result :: τ));
      }.

  Arguments MkSepContract : clear implicits.

  Definition lint_contract {Δ σ} (c : SepContract Δ σ) : bool :=
    match c with
    | {| sep_contract_logic_variables := Σ;
         sep_contract_localstore      := δ;
         sep_contract_precondition    := pre
      |} =>
      ctx_forallb Σ
        (fun b bIn =>
           match occurs_check bIn (δ , pre) with
           | Some _ => false
           | None   => true
           end)
    end.

  Definition Linted {Δ σ} (c : SepContract Δ σ) : Prop :=
    Bool.Is_true (lint_contract c).

  Definition SepContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), option (SepContract Δ τ).
  Definition SepContractEnvEx : Type :=
    forall Δ τ (f : 𝑭𝑿 Δ τ), SepContract Δ τ.

  Section DebugInfo.

    Record DebugCall : Type :=
      MkDebugCall
        { debug_call_logic_context          : LCtx;
          debug_call_instance               : SymInstance debug_call_logic_context;
          debug_call_function_parameters    : PCtx;
          debug_call_function_result_type   : Ty;
          debug_call_function_name          : 𝑭 debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_contract      : SepContract debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_arguments     : SStore debug_call_function_parameters debug_call_logic_context;
          debug_call_pathcondition          : PathCondition debug_call_logic_context;
          debug_call_program_context        : PCtx;
          debug_call_localstore             : SStore debug_call_program_context debug_call_logic_context;
          debug_call_heap                   : SHeap debug_call_logic_context;
        }.

    Record DebugStm : Type :=
      MkDebugStm
        { debug_stm_program_context        : PCtx;
          debug_stm_statement_type         : Ty;
          debug_stm_statement              : Stm debug_stm_program_context debug_stm_statement_type;
          debug_stm_logic_context          : LCtx;
          debug_stm_instance               : SymInstance debug_stm_logic_context;
          debug_stm_pathcondition          : PathCondition debug_stm_logic_context;
          debug_stm_localstore             : SStore debug_stm_program_context debug_stm_logic_context;
          debug_stm_heap                   : SHeap debug_stm_logic_context;
        }.

    Record DebugAsn : Type :=
      MkDebugAsn
        { debug_asn_logic_context          : LCtx;
          debug_asn_instance               : SymInstance debug_asn_logic_context;
          debug_asn_pathcondition          : PathCondition debug_asn_logic_context;
          debug_asn_program_context        : PCtx;
          debug_asn_localstore             : SStore debug_asn_program_context debug_asn_logic_context;
          debug_asn_heap                   : SHeap debug_asn_logic_context;
        }.

    Record SDebugCall (Σ : LCtx) : Type :=
      MkSDebugCall
        { sdebug_call_function_parameters    : PCtx;
          sdebug_call_function_result_type   : Ty;
          sdebug_call_function_name          : 𝑭 sdebug_call_function_parameters sdebug_call_function_result_type;
          sdebug_call_function_contract      : SepContract sdebug_call_function_parameters sdebug_call_function_result_type;
          sdebug_call_function_arguments     : SStore sdebug_call_function_parameters Σ;
          sdebug_call_program_context        : PCtx;
          sdebug_call_pathcondition          : PathCondition Σ;
          sdebug_call_localstore             : SStore sdebug_call_program_context Σ;
          sdebug_call_heap                   : SHeap Σ;
        }.

    Record SDebugStm (Σ : LCtx) : Type :=
      MkSDebugStm
        { sdebug_stm_program_context        : PCtx;
          sdebug_stm_statement_type         : Ty;
          sdebug_stm_statement              : Stm sdebug_stm_program_context sdebug_stm_statement_type;
          sdebug_stm_pathcondition          : PathCondition Σ;
          sdebug_stm_localstore             : SStore sdebug_stm_program_context Σ;
          sdebug_stm_heap                   : SHeap Σ;
        }.

    Record SDebugAsn (Σ : LCtx) : Type :=
      MkSDebugAsn
        { sdebug_asn_program_context        : PCtx;
          sdebug_asn_pathcondition          : PathCondition Σ;
          sdebug_asn_localstore             : SStore sdebug_asn_program_context Σ;
          sdebug_asn_heap                   : SHeap Σ;
        }.

    Global Instance SubstDebugCall : Subst SDebugCall :=
      fun (Σ0 Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) (d : SDebugCall Σ0) =>
        match d with
        | MkSDebugCall f c ts pc δ h =>
          MkSDebugCall f c (subst ζ01 ts) (subst ζ01 pc) (subst ζ01 δ) (subst ζ01 h)
        end.

    Global Instance InstDebugCall : Inst SDebugCall DebugCall :=
      {| inst Σ ι d :=
           match d with
           | MkSDebugCall f c ts pc δ h =>
             MkDebugCall ι f c ts pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugCall ι f c ts pc δ h =>
             MkSDebugCall f c (lift (inst ι ts)) (lift (inst ι pc)) (lift (inst ι δ)) (lift (inst ι h))
           end;
      |}.

    Global Instance OccursCheckDebugCall : OccursCheck SDebugCall :=
      fun Σ x xIn d =>
        match d with
        | MkSDebugCall f c ts pc δ h =>
          option_ap
            (option_ap
               (option_ap
                  (option_map
                     (fun ts' => @MkSDebugCall _ _ _ f c ts' _)
                     (occurs_check xIn ts))
                  (occurs_check xIn pc))
               (occurs_check xIn δ))
            (occurs_check xIn h)
        end.

    Global Instance SubstDebugStm : Subst SDebugStm :=
      fun (Σ0 Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) (d : SDebugStm Σ0) =>
        match d with
        | MkSDebugStm s pc δ h =>
          MkSDebugStm s (subst ζ01 pc) (subst ζ01 δ) (subst ζ01 h)
        end.

    Global Instance InstDebugStm : Inst SDebugStm DebugStm :=
      {| inst Σ ι d :=
           match d with
           | MkSDebugStm s pc δ h =>
             MkDebugStm s ι pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugStm s ι pc δ h =>
             MkSDebugStm s (lift (inst ι pc)) (lift (inst ι δ)) (lift (inst ι h))
           end
      |}.

    Global Instance OccursCheckDebugStm : OccursCheck SDebugStm :=
      fun Σ x xIn d =>
        match d with
        | MkSDebugStm s pc δ h =>
          option_ap
            (option_ap
               (option_map
                  (MkSDebugStm s)
                  (occurs_check xIn pc))
               (occurs_check xIn δ))
            (occurs_check xIn h)
        end.

    Global Instance SubstDebugAsn : Subst SDebugAsn :=
      fun (Σ0 Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) (d : SDebugAsn Σ0) =>
        match d with
        | MkSDebugAsn pc δ h =>
          MkSDebugAsn (subst ζ01 pc) (subst ζ01 δ) (subst ζ01 h)
        end.

    Global Instance InstDebugAsn : Inst SDebugAsn DebugAsn :=
      {| inst Σ ι d :=
           match d with
           | MkSDebugAsn pc δ h =>
             MkDebugAsn ι pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugAsn ι pc δ h =>
             MkSDebugAsn (lift (inst ι pc)) (lift (inst ι δ)) (lift (inst ι h))
           end
      |}.

    Global Instance OccursCheckDebugAsn : OccursCheck SDebugAsn :=
      fun Σ x xIn d =>
        match d with
        | MkSDebugAsn pc δ h =>
          option_ap
            (option_ap
               (option_map
                  (@MkSDebugAsn _ _)
                  (occurs_check xIn pc))
               (occurs_check xIn δ))
            (occurs_check xIn h)
        end.

  End DebugInfo.

  Section Experimental.

    Definition sep_contract_pun_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
      ctx_map (fun '(x::σ) => (𝑿to𝑺 x::σ)) Δ ▻▻ Σ.

    Record SepContractPun (Δ : PCtx) (τ : Ty) : Type :=
      MkSepContractPun
        { sep_contract_pun_logic_variables   : LCtx;
          sep_contract_pun_precondition      : Assertion
                                                 (sep_contract_pun_logvars
                                                    Δ sep_contract_pun_logic_variables);
          sep_contract_pun_result            : 𝑺;
          sep_contract_pun_postcondition     : Assertion
                                                 (sep_contract_pun_logvars Δ
                                                                           sep_contract_pun_logic_variables
                                                                           ▻ (sep_contract_pun_result :: τ))
        }.

    Global Arguments MkSepContractPun : clear implicits.

    Definition sep_contract_pun_to_sep_contract {Δ τ} :
      SepContractPun Δ τ -> SepContract Δ τ :=
      fun c =>
        match c with
        | MkSepContractPun _ _ Σ req result ens =>
          MkSepContract
            Δ τ
            (sep_contract_pun_logvars Δ Σ)
            (env_tabulate (fun '(x::σ) xIn =>
                             @term_var
                               (sep_contract_pun_logvars Δ Σ)
                               (𝑿to𝑺 x)
                               σ
                               (inctx_cat_left Σ (inctx_map (fun '(y::τ) => (𝑿to𝑺 y::τ)) xIn))))
            req result ens
        end.

    Global Coercion sep_contract_pun_to_sep_contract : SepContractPun >-> SepContract.

  End Experimental.

  Class IHeaplet (L : Type) := {
    is_ISepLogic :> ISepLogic L;
    luser (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) : L;
    lptsreg  {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Lit σ) : L
  }.

  Arguments luser {L _} p ts.

  Section Contracts.
    Context `{Logic : IHeaplet L}.

    Import LogicNotations.

    Definition interpret_chunk {Σ} (ι : SymInstance Σ) (c : Chunk Σ) : L :=
      match c with
      | chunk_user p ts => luser p (inst ι ts)
      | chunk_ptsreg r t => lptsreg r (inst ι t)
      end.

    Fixpoint interpret_assertion {Σ} (ι : SymInstance Σ) (a : Assertion Σ) : L :=
      match a with
      | asn_formula fml => !!(inst ι fml) ∧ emp
      | asn_chunk c => interpret_chunk ι c
      | asn_if b a1 a2 => if inst (A := Lit ty_bool) ι b then interpret_assertion ι a1 else interpret_assertion ι a2
      | asn_match_enum E k alts => interpret_assertion ι (alts (inst (T := fun Σ => Term Σ _) ι k))
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        match inst (T := fun Σ => Term Σ _) ι s with
        | inl v => interpret_assertion(ι ► (xl :: σ ↦ v)) alt_inl
        | inr v => interpret_assertion(ι ► (xr :: τ ↦ v)) alt_inr
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) ι s with
        | nil        => interpret_assertion ι alt_nil
        | cons vh vt => interpret_assertion(ι ► (xh :: _ ↦ vh) ► (xt :: ty_list _ ↦ vt)) alt_cons
        end
      | asn_match_pair s xl xr rhs =>
        match inst (T := fun Σ => Term Σ _) ι s with
        | (vl,vr)    => interpret_assertion(ι ► (xl :: _ ↦ vl) ► (xr :: _ ↦ vr)) rhs
        end
      | asn_match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) ι s in
        let ι' := tuple_pattern_match p t in
        interpret_assertion(ι ►► ι') rhs
      | asn_match_record R s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) ι s in
        let ι' := record_pattern_match p (𝑹_unfold t) in
        interpret_assertion(ι ►► ι') rhs
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) ι s in
        let (K , v) := 𝑼_unfold t in
        let ι' := pattern_match (alt__pat K) v in
        interpret_assertion(ι ►► ι') (alt__rhs K)
      | asn_sep a1 a2 => interpret_assertion ι a1 ✱ interpret_assertion ι a2
      | asn_exist ς τ a => ∃ (v : Lit τ), interpret_assertion(ι ► (ς∶τ ↦ v)) a
      | asn_debug => emp
    end%logic.

    Definition inst_contract_localstore {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) : LocalStore Δ :=
      inst ι (sep_contract_localstore c).

    Definition interpret_contract_precondition {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) : L :=
      interpret_assertion ι (sep_contract_precondition c).

    Definition interpret_contract_postcondition {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) (result : Lit τ) :  L :=
        interpret_assertion (env_snoc ι (sep_contract_result c::τ) result) (sep_contract_postcondition c).

  End Contracts.

  Arguments interpret_assertion {_ _ _} _ _.

  Section ChunkExtraction.
    Context {Σ : LCtx}.

    Infix ">=>" := option_comp (at level 80, right associativity).

    Section WithMatchTerm.

      Variable match_term_eqb : forall {σ}, Term Σ σ -> Term Σ σ -> PathCondition Σ -> option (PathCondition Σ).

      Equations(noeqns) match_env_eqb' {σs} (te : Env (Term Σ) σs) (tr : Env (Term Σ) σs) :
        PathCondition Σ -> option (PathCondition Σ) :=
        match_env_eqb' env_nil env_nil := Some;
        match_env_eqb' (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) := match_env_eqb' E1 E2 >=> match_term_eqb t1 t2.

    End WithMatchTerm.

    Equations(noeqns) match_term_eqb {σ} (te : Term Σ σ) (tr : Term Σ σ) :
      PathCondition Σ -> option (PathCondition Σ) :=
      match_term_eqb (term_lit ?(σ) l1) (term_lit σ l2) :=
        if Lit_eqb σ l1 l2 then Some else fun _ => None;
      match_term_eqb (term_inl t1) (term_inl t2) := match_term_eqb t1 t2;
      match_term_eqb (term_inl t1) (term_lit (inl l2)) := match_term_eqb t1 (term_lit _ l2);
      match_term_eqb (term_inr t1) (term_inr t2) := match_term_eqb t1 t2;
      match_term_eqb (term_inr t1) (term_lit (inr l2)) := match_term_eqb t1 (term_lit _ l2);
      match_term_eqb te tr :=
        if Term_eqb te tr
        then Some
        else fun pc => Some (cons (formula_eq te tr) pc).

    Definition match_env_eqb := @match_env_eqb' (@match_term_eqb).

    Equations(noeqns) match_chunk_eqb (ce : Chunk Σ) (cr : Chunk Σ) :
      PathCondition Σ -> option (PathCondition Σ) :=
      match_chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2)
      with eq_dec p1 p2 => {
        match_chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) (left eq_refl) := match_env_eqb ts1 ts2;
        match_chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) (right _)      := fun _ => None
      };
      match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := match_term_eqb t1 t2;
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk_eqb _ _  := fun _ => None.

    Lemma match_chunk_eqb_spec (ce cr : Chunk Σ) (fmls : List Formula Σ) :
      OptionSpec
        (fun fmls2 =>
           forall ι : SymInstance Σ,
             instpc ι fmls2 ->
             inst ι ce = inst ι cr /\ instpc ι fmls)
        True
        (match_chunk_eqb ce cr fmls).
    Proof.
      destruct ce, cr; cbn; try constructor; auto.
      - destruct (eq_dec p p0); cbn.
        + destruct e; cbn. admit.
        + now constructor.
      - destruct (eq_dec_het r r0); cbn.
        + dependent elimination e; cbn. admit.
        + now constructor.
    Admitted.

    Definition extract_chunk_eqb (ce : Chunk Σ) (h : SHeap Σ) :
      List (Pair PathCondition SHeap) Σ :=
      stdpp.base.omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk_eqb ce cr nil))
        (heap_extractions h).

  End ChunkExtraction.

  Section WithEvarEnv.

    Import stdpp.base.

    Context {Σe Σr} (δ : EvarEnv Σe Σr).

    Definition eval_chunk_evar (c : Chunk Σe) : option (Chunk Σr) :=
      match c with
      | chunk_user p ts => chunk_user p <$> traverse_env (eval_term_evar δ) ts
      | chunk_ptsreg r t => chunk_ptsreg r <$> eval_term_evar δ t
      end.

    Equations(noeqns) match_chunk (ce : Chunk Σe) (cr : Chunk Σr) :
      EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
      match_chunk (chunk_user p1 ts1) (chunk_user p2 ts2)
      with eq_dec p1 p2 => {
        match_chunk (chunk_user p1 ts1) (chunk_user p2 ts2) (left eq_refl) := match_env ts1 ts2;
        match_chunk (chunk_user p1 ts1) (chunk_user p2 ts2) (right _)      := fun _ => None
      };
      match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := match_term t1 t2;
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk _ _  := fun _ => None.

    Definition extract_chunk (ce : Chunk Σe) (h : SHeap Σr) (L : EvarEnv Σe Σr) :
      List (Pair (EvarEnv Σe) SHeap) Σr :=
      omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk ce cr L))
        (heap_extractions h).

  End WithEvarEnv.

End Assertions.

Module Type SymbolicContractKit
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit).

  Module Export ASS := Assertions termkit progkit assertkit.

  Parameter Inline CEnv   : SepContractEnv.
  Parameter Inline CEnvEx : SepContractEnvEx.

End SymbolicContractKit.
