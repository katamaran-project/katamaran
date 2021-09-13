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
  (* Duplicable? *)
  Declare Instance 𝑷_is_dup : IsDuplicable 𝑷.

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

  Equations(noeqns) formula_eqs_ctx {Δ : Ctx Ty} {Σ : LCtx}
    (δ δ' : Env (Term Σ) Δ) : list (Formula Σ) :=
    formula_eqs_ctx env_nil          env_nil            := nil;
    formula_eqs_ctx (env_snoc δ _ t) (env_snoc δ' _ t') :=
      formula_eq t t' :: formula_eqs_ctx δ δ'.

  Equations(noeqns) formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ : LCtx}
    (δ δ' : NamedEnv (Term Σ) Δ) : list (Formula Σ) :=
    formula_eqs_nctx env_nil          env_nil            := nil;
    formula_eqs_nctx (env_snoc δ _ t) (env_snoc δ' _ t') :=
      formula_eq t t' :: formula_eqs_nctx δ δ'.

  Instance sub_formula : Subst Formula :=
    fun Σ1 fml Σ2 ζ =>
      match fml with
      | formula_bool t    => formula_bool (subst t ζ)
      | formula_prop ζ' P => formula_prop (subst ζ' ζ) P
      | formula_eq t1 t2  => formula_eq (subst t1 ζ) (subst t2 ζ)
      | formula_neq t1 t2 => formula_neq (subst t1 ζ) (subst t2 ζ)
      end.

  Instance substlaws_formula : SubstLaws Formula.
  Proof.
    constructor.
    { intros ? []; cbn; f_equal; apply subst_sub_id. }
    { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
  Qed.

  Definition inst_formula {Σ} (fml : Formula Σ) (ι : SymInstance Σ) : Prop :=
    match fml with
    | formula_bool t    => is_true (inst (A := Lit ty_bool) t ι)
    | formula_prop ζ P  => uncurry_named P (inst ζ ι)
    | formula_eq t1 t2  => inst t1 ι =  inst t2 ι
    | formula_neq t1 t2 => inst t1 ι <> inst t2 ι
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
    Definition inst_pathcondition {Σ} (pc : PathCondition Σ) (ι : SymInstance Σ) : Prop :=
      fold_right10 (fun fml pc => inst fml ι /\ pc) (fun fml => inst fml ι) True pc.
    Global Arguments inst_pathcondition : simpl never.

    Lemma inst_subst1 {Σ Σ' } (ζ : Sub Σ Σ') (ι : SymInstance Σ') (f : Formula Σ) (pc : list (Formula Σ)) :
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

    Lemma inst_subst10 {Σ Σ' } (ζ : Sub Σ Σ') (ι : SymInstance Σ') (pc : list (Formula Σ)) :
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

    Lemma inst_pathcondition_cons {Σ} (ι : SymInstance Σ) (f : Formula Σ) (pc : PathCondition Σ) :
      inst (cons f pc) ι <-> inst f ι /\ inst pc ι.
    Proof.
      apply (fold_right_1_10_prop (P := fun fml => inst fml ι)).
    Qed.

    Lemma inst_pathcondition_app {Σ} (ι : SymInstance Σ) (pc1 pc2 : PathCondition Σ) :
      inst (app pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι.
    Proof.
      induction pc1; cbn [app].
      - intuition. constructor.
      - rewrite ?inst_pathcondition_cons.
        rewrite IHpc1. intuition.
    Qed.

    Lemma inst_pathcondition_rev_append {Σ} (ι : SymInstance Σ) (pc1 pc2 : PathCondition Σ) :
      inst (List.rev_append pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι.
    Proof.
      revert pc2.
      induction pc1; cbn [List.rev_append]; intros pc2.
      - intuition. constructor.
      - rewrite IHpc1.
        rewrite ?inst_pathcondition_cons.
        intuition.
    Qed.

    Lemma inst_formula_eqs_ctx {Δ Σ} (ι : SymInstance Σ) (xs ys : Env (Term Σ) Δ) :
      inst (T := PathCondition) (A := Prop) (formula_eqs_ctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs.
      - destruct (nilView ys). cbn. intuition. constructor.
      - destruct (snocView ys). cbn - [inst].
        rewrite inst_pathcondition_cons, IHxs. clear IHxs.
        change (inst db ι = inst v ι /\ inst xs ι = inst E ι <->
                inst xs ι ► (b ↦ inst db ι) = inst E ι ► (b ↦ inst v ι)).
        split.
        + intros [Hfml Hpc]; f_equal; auto.
        + intros Heq. apply noConfusion_inv in Heq. cbn in Heq.
          inversion Heq. intuition.
    Qed.

    Lemma inst_formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ} (ι : SymInstance Σ) (xs ys : NamedEnv (Term Σ) Δ) :
      inst (T := PathCondition) (A := Prop) (formula_eqs_nctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs.
      - destruct (nilView ys). cbn. intuition. constructor.
      - destruct (snocView ys). cbn - [inst].
        rewrite inst_pathcondition_cons, IHxs. clear IHxs.
        change (inst db ι = inst v ι /\ inst xs ι = inst E ι <->
                inst xs ι ► (b ↦ inst db ι) = inst E ι ► (b ↦ inst v ι)).
        split.
        + intros [Hfml Hpc]; f_equal; auto.
        + intros ?%inversion_eq_env_snoc.
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
      forall (ι : SymInstance Σ),
        instpc pc1 ι ->
        instpc pc0 ι.
    Infix "⊢" := (@entails _) (at level 80, no associativity).

    Definition entails_formula {Σ}
               (pc : PathCondition Σ) (f : Formula Σ) : Prop :=
      forall (ι : SymInstance Σ),
        instpc pc ι -> (inst f ι : Prop).
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

    (* Global Instance proper_subst_pc_entails {Σ1 Σ2} : *)
    (*   Proper ((@entails Σ1) ==> eq ==> (@entails Σ2)) (subst (T := PathCondition)) . *)
    (* Proof. *)
    (*   intros pc1 pc2 pc12 ι. *)
    (*   rewrite ?inst_subst; eauto. *)
    (* Qed. *)

    Lemma proper_subst_entails {Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc1 pc2 : PathCondition Σ1) :
      pc1 ⊢ pc2 -> subst pc1 ζ12 ⊢ subst pc2 ζ12.
    Proof.
      intros pc12 ι.
      rewrite ?inst_subst; eauto.
    Qed.

    Definition entails_eq {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ) (a0 a1 : AT Σ) : Prop :=
      forall (ι : SymInstance Σ), instpc pc ι -> inst a0 ι = inst a1 ι.
    Notation "pc ⊢ a0 == a1" :=
      (entails_eq pc a0 a1)
      (at level 80, a0 at next level, no associativity).

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

  Section Chunks.

    (* Semi-concrete chunks *)
    Inductive SCChunk : Type :=
    | scchunk_user   (p : 𝑷) (vs : Env Lit (𝑷_Ty p))
    | scchunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ)
    | scchunk_conj   (c1 c2 : SCChunk)
    | scchunk_wand   (c1 c2 : SCChunk).
    Global Arguments scchunk_user _ _ : clear implicits.

    (* Symbolic chunks *)
    Inductive Chunk (Σ : LCtx) : Type :=
    | chunk_user   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
    | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ)
    | chunk_conj   (c1 c2 : Chunk Σ)
    | chunk_wand   (c1 c2 : Chunk Σ).
    Global Arguments chunk_user [_] _ _.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive NoConfusion for SCChunk.
      Derive NoConfusion for Chunk.
    End TransparentObligations.

    Global Instance scchunk_isdup : IsDuplicable SCChunk := {
      is_duplicable := fun c => match c with
                             | scchunk_user p _ => is_duplicable p
                             | scchunk_ptsreg _ _ => false
                             | scchunk_conj _ _ => false
                             | scchunk_wand _ _ => false
                             end
      }.

    Global Instance chunk_isdup {Σ} : IsDuplicable (Chunk Σ) := {
      is_duplicable := fun c => match c with
                             | chunk_user p _ => is_duplicable p
                             | chunk_ptsreg _ _ => false
                             | chunk_conj _ _ => false
                             | chunk_wand _ _ => false
                             end
      }.

    Open Scope lazy_bool_scope.

    Fixpoint chunk_eqb {Σ} (c1 c2 : Chunk Σ) : bool :=
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
      | chunk_conj c11 c12 , chunk_conj c21 c22 =>
        chunk_eqb c11 c21 &&& chunk_eqb c12 c22
      | chunk_wand c11 c12 , chunk_wand c21 c22 =>
        chunk_eqb c11 c21 &&& chunk_eqb c12 c22
      | _ , _ => false
      end.

    Local Set Equations With UIP.
    Lemma chunk_eqb_spec {Σ} (c1 c2 : Chunk Σ) :
      reflect (c1 = c2) (chunk_eqb c1 c2).
    Proof.
      revert c2.
      induction c1 as [p1 ts1|σ1 r1 t1|c11 IHc11 c12 IHc12|c11 IHc11 c12 IHc12];
        intros [p2 ts2|σ2 r2 t2|c21 c22|c21 c22];
        try (constructor; discriminate; fail); cbn.
      - destruct (eq_dec p1 p2).
        + destruct e; cbn.
          destruct (env_eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) ts1 ts2).
          * constructor. f_equal; auto.
          * constructor. intros Heq.
            dependent elimination Heq.
            auto.
        + constructor. intros Heq.
          dependent elimination Heq.
          auto.
      - destruct (eq_dec_het r1 r2).
        + dependent elimination e; cbn.
          destruct (Term_eqb_spec t1 t2).
          * constructor. f_equal; auto.
          * constructor. intros Heq.
          dependent elimination Heq.
          auto.
        + constructor. intros Heq.
          dependent elimination Heq.
          auto.
      - destruct (IHc11 c21), (IHc12 c22);
          constructor; intuition; fail.
      - destruct (IHc11 c21), (IHc12 c22);
          constructor; intuition; fail.
    Qed.

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

    Fixpoint sub_chunk {Σ1} (c : Chunk Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct c} : Chunk Σ2 :=
      match c with
      | chunk_user p ts => chunk_user p (subst ts ζ)
      | chunk_ptsreg r t => chunk_ptsreg r (subst t ζ)
      | chunk_conj c1 c2 =>
        chunk_conj (sub_chunk c1 ζ) (sub_chunk c2 ζ)
      | chunk_wand c1 c2 =>
        chunk_wand (sub_chunk c1 ζ) (sub_chunk c2 ζ)
      end.

    Global Instance SubstChunk : Subst Chunk :=
      @sub_chunk.

    Global Instance substlaws_chunk : SubstLaws Chunk.
    Proof.
      constructor.
      { intros ? c. induction c; cbn; f_equal; auto; apply subst_sub_id. }
      { intros ? ? ? ? ? c. induction c; cbn; f_equal; auto; apply subst_sub_comp. }
    Qed.

    Fixpoint inst_chunk {Σ} (c : Chunk Σ) (ι : SymInstance Σ) {struct c} : SCChunk :=
      match c with
      | chunk_user p ts => scchunk_user p (inst ts ι)
      | chunk_ptsreg r t => scchunk_ptsreg r (inst t ι)
      | chunk_conj c1 c2 => scchunk_conj (inst_chunk c1 ι) (inst_chunk c2 ι)
      | chunk_wand c1 c2 => scchunk_wand (inst_chunk c1 ι) (inst_chunk c2 ι)
      end.

    Fixpoint lift_chunk {Σ} (c : SCChunk) {struct c} : Chunk Σ :=
      match c with
      | scchunk_user p vs => chunk_user p (lift vs)
      | scchunk_ptsreg r v => chunk_ptsreg r (lift v)
      | scchunk_conj c1 c2 => chunk_conj (lift_chunk c1) (lift_chunk c2)
      | scchunk_wand c1 c2 => chunk_wand (lift_chunk c1) (lift_chunk c2)
      end.

    Global Instance InstChunk : Inst Chunk SCChunk :=
      {| inst := @inst_chunk;
         lift := @lift_chunk;
      |}.

    Global Instance instlaws_chunk : InstLaws Chunk SCChunk.
    Proof.
      constructor.
      - intros ? ? c; induction c; cbn; f_equal; auto; apply inst_lift.
      - intros ? ? ζ ι c; induction c; cbn; f_equal; auto; apply inst_subst.
    Qed.

    Global Instance OccursCheckChunk :
      OccursCheck Chunk :=
      fun Σ b bIn =>
        fix occurs_check_chunk (c : Chunk Σ) : option (Chunk (Σ - b)) :=
        match c with
        | chunk_user p ts => option_map (chunk_user p) (occurs_check bIn ts)
        | chunk_ptsreg r t => option_map (chunk_ptsreg r) (occurs_check bIn t)
        | chunk_conj c1 c2 => option_ap (option_map (@chunk_conj _) (occurs_check_chunk c1)) (occurs_check_chunk c2)
        | chunk_wand c1 c2 => option_ap (option_map (@chunk_wand _) (occurs_check_chunk c1)) (occurs_check_chunk c2)
        end.

  End Chunks.

  Section Heaps.

    Definition SCHeap : Type := list SCChunk.
    Definition SHeap : LCtx -> Type := fun Σ => list (Chunk Σ).

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
      fun Σ1 msg Σ2 ζ12 =>
        match msg with
        | MkMessage f m Γ δ h pc => MkMessage f m Γ (subst δ ζ12) (subst h ζ12) (subst pc ζ12)
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
      (alt_cons : Assertion (Σ ▻ (xh::σ) ▻ (xt::ty_list σ)))
  | asn_match_prod
      {σ1 σ2 : Ty} (s : Term Σ (ty_prod σ1 σ2))
      (xl xr : 𝑺) (rhs : Assertion (Σ ▻ (xl::σ1) ▻ (xr::σ2)))
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
  Arguments asn_match_prod [_] {σ1 σ2} s xl xr rhs.
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

  Global Instance sub_assertion : Subst Assertion :=
    fix sub_assertion {Σ1} (a : Assertion Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct a} : Assertion Σ2 :=
      match a with
      | asn_formula fml => asn_formula (subst fml ζ)
      | asn_chunk c => asn_chunk (subst c ζ)
      | asn_if b a1 a2 => asn_if (subst b ζ) (sub_assertion a1 ζ) (sub_assertion a2 ζ)
      | asn_match_enum E k alts =>
        asn_match_enum E (subst k ζ) (fun z => sub_assertion (alts z) ζ)
      | asn_match_sum σ τ t xl al xr ar =>
        asn_match_sum σ τ (subst t ζ) xl (sub_assertion al (sub_up1 ζ)) xr (sub_assertion ar (sub_up1 ζ))
      | asn_match_list s anil xh xt acons =>
        asn_match_list (subst s ζ) (sub_assertion anil ζ) xh xt (sub_assertion acons (sub_up1 (sub_up1 ζ)))
      | asn_match_prod s xl xr asn =>
        asn_match_prod (subst s ζ) xl xr (sub_assertion asn (sub_up1 (sub_up1 ζ)))
      | asn_match_tuple s p rhs =>
        asn_match_tuple (subst s ζ) p (sub_assertion rhs (sub_up ζ _))
      | asn_match_record R s p rhs =>
        asn_match_record R (subst s ζ) p (sub_assertion rhs (sub_up ζ _))
      | asn_match_union U s ctx pat rhs =>
        asn_match_union U (subst s ζ) ctx pat (fun K => sub_assertion (rhs K) (sub_up ζ _))
      | asn_sep a1 a2 => asn_sep (sub_assertion a1 ζ) (sub_assertion a2 ζ)
      | asn_exist ς τ a => asn_exist ς τ (sub_assertion a (sub_up1 ζ))
      | asn_debug => asn_debug
      end.

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
      | @asn_match_prod _ σ1 σ2 s xl xr rhs => None (* TODO *)
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

  Record Lemma (Δ : PCtx) : Type :=
    MkLemma
      { lemma_logic_variables  : LCtx;
        lemma_patterns         : SStore Δ lemma_logic_variables;
        lemma_precondition     : Assertion lemma_logic_variables;
        lemma_postcondition    : Assertion lemma_logic_variables;
      }.

  Arguments MkLemma : clear implicits.

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

  Definition lint_lemma {Δ} (l : Lemma Δ) : bool :=
    match l with
    | {| lemma_logic_variables := Σ;
         lemma_patterns        := δ;
         lemma_precondition    := pre
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
  Definition LemmaEnv : Type :=
    forall Δ (l : 𝑳 Δ), Lemma Δ.

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
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkSDebugCall f c ts pc δ h =>
          MkSDebugCall f c (subst ts ζ01) (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance InstDebugCall : Inst SDebugCall DebugCall :=
      {| inst Σ d ι :=
           match d with
           | MkSDebugCall f c ts pc δ h =>
             MkDebugCall ι f c ts pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugCall ι f c ts pc δ h =>
             MkSDebugCall f c (lift (inst ts ι)) (lift (inst pc ι)) (lift (inst δ ι)) (lift (inst h ι))
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
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkSDebugStm s pc δ h =>
          MkSDebugStm s (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance InstDebugStm : Inst SDebugStm DebugStm :=
      {| inst Σ d ι :=
           match d with
           | MkSDebugStm s pc δ h =>
             MkDebugStm s ι pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugStm s ι pc δ h =>
             MkSDebugStm s (lift (inst pc ι)) (lift (inst δ ι)) (lift (inst h ι))
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
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkSDebugAsn pc δ h =>
          MkSDebugAsn (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance InstDebugAsn : Inst SDebugAsn DebugAsn :=
      {| inst Σ d ι :=
           match d with
           | MkSDebugAsn pc δ h =>
             MkDebugAsn ι pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugAsn ι pc δ h =>
             MkSDebugAsn (lift (inst pc ι)) (lift (inst δ ι)) (lift (inst h ι))
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
      is_ISepLogic :> ISepLogic L
    ; luser (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) : L
    ; lptsreg  {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Lit σ) : L
    ; lduplicate (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) :
        is_duplicable p = true ->
        (lentails (luser (p := p) ts) (sepcon (luser (p := p) ts) (luser (p := p) ts)))
  }.

  Arguments luser {L _} p ts.

  Section Contracts.
    Context `{Logic : IHeaplet L}.

    Import LogicNotations.

    Fixpoint interpret_chunk {Σ} (c : Chunk Σ) (ι : SymInstance Σ) {struct c} : L :=
      match c with
      | chunk_user p ts => luser p (inst ts ι)
      | chunk_ptsreg r t => lptsreg r (inst t ι)
      | chunk_conj c1 c2 => sepcon (interpret_chunk c1 ι) (interpret_chunk c2 ι)
      | chunk_wand c1 c2 => wand (interpret_chunk c1 ι) (interpret_chunk c2 ι)
      end.

    Fixpoint interpret_assertion {Σ} (a : Assertion Σ) (ι : SymInstance Σ) : L :=
      match a with
      | asn_formula fml => !!(inst fml ι) ∧ emp
      | asn_chunk c => interpret_chunk c ι
      | asn_if b a1 a2 => if inst (A := Lit ty_bool) b ι then interpret_assertion a1 ι else interpret_assertion a2 ι
      | asn_match_enum E k alts => interpret_assertion (alts (inst (T := fun Σ => Term Σ _) k ι)) ι
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | inl v => interpret_assertion alt_inl (ι ► (xl :: σ ↦ v))
        | inr v => interpret_assertion alt_inr (ι ► (xr :: τ ↦ v))
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => interpret_assertion alt_nil ι
        | cons vh vt => interpret_assertion alt_cons (ι ► (xh :: _ ↦ vh) ► (xt :: ty_list _ ↦ vt))
        end
      | asn_match_prod s xl xr rhs =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | (vl,vr)    => interpret_assertion rhs (ι ► (xl :: _ ↦ vl) ► (xr :: _ ↦ vr))
        end
      | asn_match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_lit p t in
        interpret_assertion rhs (ι ►► ι')
      | asn_match_record R s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := record_pattern_match_lit p t in
        interpret_assertion rhs (ι ►► ι')
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := 𝑼_unfold t in
        let ι' := pattern_match_lit (alt__pat K) v in
        interpret_assertion (alt__rhs K) (ι ►► ι')
      | asn_sep a1 a2 => interpret_assertion a1 ι ✱ interpret_assertion a2 ι
      | asn_exist ς τ a => ∃ (v : Lit τ), interpret_assertion a (ι ► (ς::τ ↦ v))
      | asn_debug => emp
    end%logic.

    Definition inst_contract_localstore {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) : CStore Δ :=
      inst (sep_contract_localstore c) ι.

    Definition interpret_contract_precondition {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) : L :=
      interpret_assertion (sep_contract_precondition c) ι.

    Definition interpret_contract_postcondition {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) (result : Lit τ) :  L :=
        interpret_assertion (sep_contract_postcondition c) (env_snoc ι (sep_contract_result c::τ) result).

  End Contracts.

  Arguments interpret_assertion {_ _ _} _ _.

End Assertions.

Module Type SymbolicContractKit
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit).

  Module Export ASS := Assertions termkit progkit assertkit.

  Parameter Inline CEnv   : SepContractEnv.
  Parameter Inline CEnvEx : SepContractEnvEx.
  Parameter Inline LEnv   : LemmaEnv.

End SymbolicContractKit.
