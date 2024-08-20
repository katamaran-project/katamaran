(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel, Dominique Devriese                      *)
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

(* Strongly based on https://github.com/decrn/em *)

From Coq Require Import
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     Relations.Relation_Definitions
.
From Equations Require Import
     Equations.
From stdpp Require Import base.
From Katamaran Require Import
     Prelude
     Base
     Environment
     Symbolic.Worlds
     Syntax.Predicates
.
From iris Require bi.derived_connectives bi.interface proofmode.tactics.

Declare Scope pred_scope.
Delimit Scope pred_scope with P.

Module Type UnifLogicOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P).

  Ltac punfold_connectives :=
    change (@interface.bi_and (@bi_pred ?w) ?P ?Q ?ι) with (P ι /\ Q ι) in * ||
    change (@interface.bi_sep (@bi_pred ?w) ?P ?Q ?ι) with (sepₚ (w := w) P Q ι) in * ||
    change (@eqₚ ?T ?A ?instTA ?w ?t1 ?t2 ?ι) with (inst t1 ι = inst t2 ι) in * ||
    change (@repₚ ?T ?A ?instTA ?t2 ?w ?t1 ?ι) with (inst t1 ι = t2) in *||
    change (@wandₚ ?w ?P ?Q ?ι) with (P ι -> Q ι)%type in *||
    change (@proprepₚ ?T ?instTP ?t2 ?w ?t1 ?ι) with (instprop t1 ι <-> t2)%type in *||
    change (@interface.bi_emp (@bi_pred _) ?ι) with (empₚ ι) in *||
    change (@interface.bi_wand (@bi_pred ?w) ?P ?Q ?ι) with (@wandₚ w P Q ι) in *||
    change (@interface.bi_entails (@bi_pred _) ?P ?Q) with (entails P Q) in *||
    change (@interface.bi_persistently (@bi_pred _) ?P ?ι) with (persistently P ι) in *||
    change (@interface.bi_or (@bi_pred ?w) ?P ?Q ?ι) with (P ι \/ Q ι) in *||
    change (@interface.bi_impl (@bi_pred ?w) ?P ?Q ?ι) with (P ι -> Q ι) in *||
    change (@derived_connectives.bi_iff (@bi_pred ?w) ?P ?Q ?ι) with (iff (P ι) (Q ι)) in *||
    change (@interface.bi_pure (@bi_pred _) ?P _) with P in *||
    change (@interface.bi_forall (@bi_pred ?w) ?A ?f ?ι) with (forall a, f a ι) ||
    (* the change seems to trigger some coq binding bug, so I removed the "in *" for now... *)
    change (@interface.bi_exist (@bi_pred ?w) ?A ?P) with (fun ι => exists a : A, P a ι) in *||
    unfold derived_connectives.bi_wand_iff, derived_connectives.bi_intuitionistically, derived_connectives.bi_affinely, interface.bi_emp_valid, proprepₚ in *;
    (* change (@subst Pred subst_pred _ _ ?P _ ?θ ?ι) with (P (inst θ ι)) in *; *)
    try progress (cbn beta).
  (* Ltac crushPredEntailsMatch3 := *)
  (*   match goal with *)
  (*   | [ H: interface.bi_entails ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromEntails x y H ι Hpc); clear H) *)
  (*   | [ |- interface.bi_entails ?x ?y ] => constructor *)
  (*   | [ H: interface.bi_sep _ _ _ |- _ ] => destruct H *)
  (*   | [ |- interface.bi_sep _ _ _ ] => split *)
  (*   | [ H: interface.bi_and _ _ _ |- _ ] => destruct H *)
  (*   | [ |- interface.bi_and _ _ _ ] => split *)
  (*   | [ H: interface.bi_persistently ?P ?ι |- _ ] => destruct H *)
  (*   | [ |- interface.bi_persistently ?P ?ι ] => constructor *)
  (*   | [ |- interface.bi_wand _ _ _ ] => constructor; intros *)
  (*   | [ H : interface.bi_wand _ _ _ |- _ ] => destruct H; cbn in H *)
  (*   | [ |- interface.bi_emp _ ] => constructor *)
  (*   end. *)
  Ltac crushPredEntails3 := cbn; intros;
                            repeat punfold_connectives;
                            repeat (repeat punfold_connectives; crushPredEntailsMatch1 || crushPredEntailsMatch2);
                            repeat punfold_connectives;
                            intuition.
                                 
  Module Import notations.

    Import iris.bi.interface iris.bi.derived_connectives.

    Notation "P ⊣⊢ₚ Q" := (@equiv (bi_car (@bi_pred _)) (@pred_equiv _) P%P Q%P)
      (at level 95).
    Notation "(⊣⊢ₚ)" := (@equiv (bi_car (@bi_pred _)) (@pred_equiv _))
      (only parsing).

    Notation "P ⊢ₚ Q" := (@bi_entails (@bi_pred _) P%P Q%P) (at level 95).
    Notation "(⊢ₚ)" := (@bi_entails (@bi_pred _)) (only parsing).

    Notation "⊤ₚ" := (@bi_pure (@bi_pred _) True) : pred_scope.
    Notation "⊥ₚ" := (@bi_pure (@bi_pred _) False) : pred_scope.
    Notation "P <->ₚ Q" := (@bi_iff (@bi_pred _) P%P Q%P) (at level 94) : pred_scope.
    Notation "P ->ₚ Q"  := (@bi_impl (@bi_pred _) P%P Q%P) (at level 94, right associativity) : pred_scope.
    Notation "P /\ₚ Q"  := (@bi_and (@bi_pred _) P%P Q%P) (at level 80, right associativity) : pred_scope.
    Notation "P \/ₚ Q"  := (@bi_or (@bi_pred _) P%P Q%P) (at level 85, right associativity) : pred_scope.

    Infix "=ₚ" := eqₚ (at level 70, no associativity) : pred_scope.

    Notation "∀ₚ x .. y , P" :=
      (@bi_forall (@bi_pred _) _ (fun x => .. (@bi_forall (@bi_pred _) _ (fun y => P%P)) ..))
      (at level 200, x binder, y binder, right associativity,
        format "'[ ' '[ ' ∀ₚ  x .. y ']' ,  '/' P ']'") : pred_scope.
    Notation "∃ₚ x .. y , P" :=
      (@bi_exist (@bi_pred _) _ (fun x => .. (@bi_exist (@bi_pred _) _ (fun y => P%P)) ..))
      (at level 200, x binder, y binder, right associativity,
        format "'[ ' '[ ' ∃ₚ  x .. y ']' ,  '/' P ']'") : pred_scope.

  End notations.

  #[export] Instance pred_absorbing {w} {P : Pred w} : derived_connectives.Absorbing P.
  Proof.
    unfold derived_connectives.Absorbing, derived_connectives.bi_absorbingly.
    crushPredEntails3.
  Qed.

  Lemma bientails_unfold [w] (P Q : Pred w) :
    (P ⊣⊢ₚ Q) <-> forall ι, instprop (wco w) ι -> P ι <-> Q ι.
  Proof. crushPredEntails3. Qed.
  Lemma entails_unfold [w] (P Q : Pred w) :
    (P ⊢ₚ Q) <-> forall ι, instprop (wco w) ι -> P ι -> Q ι.
  Proof. crushPredEntails3. Qed.
  Lemma sep_unfold w (P Q : Pred w) :
    ∀ ι, interface.bi_sep P Q ι ↔ (P ι /\ Q ι).
  Proof. crushPredEntails3. Qed.
  Lemma wand_unfold w (P Q : Pred w) :
    ∀ ι, interface.bi_wand P Q ι ↔ (P ι → Q ι).
  Proof. crushPredEntails3. Qed.
  Lemma intuitionistically_unfold w (P : Pred w) :
    ∀ ι, @derived_connectives.bi_intuitionistically _ P ι <-> P ι.
  Proof. crushPredEntails3. Qed.

  Create HintDb punfold.
  #[export] Hint Rewrite bientails_unfold entails_unfold sep_unfold wand_unfold
    intuitionistically_unfold (* (@inst_subst OEnv Env _ _ _) *)
    (* (@inst_subst OExp Exp _ _ _) (@inst_subst OTy Ty _ _ _) *)
    (* (@inst_lift OEnv Env _ _ _) (@inst_lift OExp Exp _ _ _) *)
    (* (@inst_lift OTy Ty _ _ _) (@inst_thin Par _ Par.lk_thin_par) *)
    (* @inst_refl @inst_trans @inst_insert @Open.inst_pure *)
    (* @oexp.inst_var @oexp.inst_true @oexp.inst_false @oexp.inst_ifte *)
    (* @oexp.inst_absu @oexp.inst_abst @oexp.inst_app *) : punfold.

  Ltac pred_unfold :=
    repeat
      (punfold_connectives;
       try rewrite_db punfold; auto 1 with typeclass_instances;
       cbn [eqₚ inst] in *;
       (* repeat rewrite ?inst_subst, ?inst_lift, ?inst_refl, ?inst_trans, *)
       (*   ?inst_insert, ?oexp.inst_var, ?oexp.inst_true, ?oexp.inst_false, *)
       (*   ?oexp.inst_absu, ?oexp.inst_abst, ?oexp.inst_app, ?oexp.inst_ifte in *; *)
       try
         match goal with
         | |- forall ι : Valuation _, _ =>
             let ι := fresh "ι" in
             intro ι; pred_unfold;
             first [clear ι | revert ι]
         | |- @interface.bi_emp_valid (@bi_pred _) _ => constructor; intros ι _; cbn
         | |- @interface.bi_entails (@bi_pred _) _ _ => constructor; intros ι; cbn
         (* | H: context[@inst ?AT ?A ?I ?w ?x ?ι] |- _ => *)
         (*     is_var x; generalize (@inst AT A I w x ι); *)
         (*     clear x; intro x; subst *)
         | |- context[@inst ?AT ?A ?I ?w ?x ?ι] =>
             is_var x; generalize (@inst AT A I w x ι);
             clear x; intro x; subst
         end).

  Section Lemmas.

    Import iris.bi.interface iris.bi.derived_laws.bi.
    Create HintDb obligation.
    (* #[local] Hint Rewrite @inst_refl @inst_trans : obligation. *)

    #[local] Ltac obligation :=
      cbv [Proper flip respectful pointwise_relation forall_relation];
      repeat (autorewrite with obligation in *; cbn in *; intros; subst; pred_unfold);
      repeat
        (match goal with
         | H: _ ⊢ₚ _ |- _ => destruct H as [H]
         | H: _ ⊣⊢ₚ _ |- _ => destruct H as [H]
         | H: forall (H : ?A), _, a : ?A |- _ =>
           specialize (H a); autorewrite with obligation in H; cbn in H
         | |- (forall _ : ?A, _) <-> (forall _ : ?A, _) =>
             apply all_iff_morphism; intro; autorewrite with obligation; cbn
         | |- (exists _ : ?A, _) <-> (exists _ : ?A, _) =>
             apply ex_iff_morphism; intro; autorewrite with obligation; cbn
         (* | |- _ ⊣⊢ₚ _ => constructor; cbn; intros *)
         (* | |- _ ⊢ₚ _ => constructor; cbn; intros *)
         end);
      try easy; try (intuition; fail); try (intuition congruence; fail).
    #[local] Obligation Tactic := obligation.

    #[local] Hint Rewrite <- @tactics.forall_and_distr : obligation.

    (* #[export] Instance proper_subst_bientails {Θ w} : *)
    (*   Proper ((⊣⊢ₚ) ==> forall_relation (fun _ => eq ==> (⊣⊢ₚ))) *)
    (*   (@subst Pred Pred.subst_pred Θ w). *)
    (* Proof. obligation. Qed. *)

    Lemma split_bientails {w} (P Q : Pred w) : (P ⊣⊢ₚ Q) <-> (P ⊢ₚ Q) /\ (Q ⊢ₚ P).
    Proof. crushPredEntails3. Qed.
    Lemma impl_and_adjoint {w} (P Q R : Pred w) : (P /\ₚ Q ⊢ₚ R) <-> (P ⊢ₚ Q ->ₚ R).
    Proof. crushPredEntails3. Qed.
    Lemma and_true_l {w} (P : Pred w) : ⊤ₚ /\ₚ P ⊣⊢ₚ P.
    Proof. crushPredEntails3. Qed.
    Lemma and_true_r {w} (P : Pred w) : P /\ₚ ⊤ₚ ⊣⊢ₚ P.
    Proof. crushPredEntails3. Qed.
    Lemma and_false_l {w} (P : Pred w) : ⊥ₚ /\ₚ P ⊣⊢ₚ ⊥ₚ.
    Proof. crushPredEntails3. Qed.
    Lemma and_false_r {w} (P : Pred w) : P /\ₚ ⊥ₚ ⊣⊢ₚ ⊥ₚ.
    Proof. crushPredEntails3. Qed.
    Lemma impl_true_l {w} (P : Pred w) : ⊤ₚ ->ₚ P ⊣⊢ₚ P.
    Proof. crushPredEntails3. Qed.
    Lemma impl_true_r {w} (P : Pred w) : P ->ₚ ⊤ₚ ⊣⊢ₚ ⊤ₚ.
    Proof. crushPredEntails3. Qed.
    Lemma impl_false_l {w} (P : Pred w) : ⊥ₚ ->ₚ P ⊣⊢ₚ ⊤ₚ.
    Proof. crushPredEntails3. Qed.
    (* Lemma false_l {w} (P : Pred w) : ⊥ₚ ⊢ₚ P. *)
    (* Proof. crushPredEntails3. Qed. *)
    (* Lemma true_r {w} (P : Pred w) : P ⊢ₚ ⊤ₚ. *)
    (* Proof. crushPredEntails3. Qed. *)
    (* Lemma impl_forget {w} (P Q R : Pred w) : P ⊢ₚ R -> P ⊢ₚ (Q ->ₚ R). *)
    (* Proof. crushPredEntails3. Qed. *)
    Lemma impl_and [w] (P Q R : Pred w) : ((P /\ₚ Q) ->ₚ R) ⊣⊢ₚ (P ->ₚ Q ->ₚ R).
    Proof. crushPredEntails3. Qed.

    Lemma forall_l {I : Type} {w} (P : I -> Pred w) Q :
      (exists x : I, P x ⊢ₚ Q) -> (∀ x : I, P x)%I ⊢ₚ Q.
    Proof. crushPredEntails3. Qed.
    Lemma forall_r {I : Type} {w} P (Q : I -> Pred w) :
      (P ⊢ₚ (∀ₚ x : I, Q x)) <-> (forall x : I, P ⊢ₚ Q x).
    Proof. crushPredEntails3. Qed.

    Lemma exists_l {I : Type} {w} (P : I -> Pred w) (Q : Pred w) :
      (forall x : I, P x ⊢ₚ Q) -> (∃ₚ x : I, P x) ⊢ₚ Q.
    Proof. crushPredEntails3. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (exists x : I, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x : I, Q x).
    Proof. crushPredEntails3. Qed.
    #[global] Arguments exists_r {I w P Q} _.

    Lemma wand_is_impl [w] (P Q : Pred w) : (P -∗ Q)%I ⊣⊢ₚ (P ->ₚ Q).
    Proof. crushPredEntails3. Qed.

    Lemma sep_is_and [w] (P Q : Pred w) : (P ∗ Q)%I ⊣⊢ₚ (P ∧ Q)%I.
    Proof. crushPredEntails3. Qed.

    Lemma pApply {w} {P Q R : Pred w} : P ⊢ₚ Q -> Q ⊢ₚ R -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma pApply_r {w} {P Q R : Pred w} : Q ⊢ₚ R -> P ⊢ₚ Q -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma elim_debugPred {B : LCtx → Type} {w : World} {b : B w} {P : Pred w} :
      DebugPred B b P ⊢ P.
    Proof.
      crushPredEntails3.
      now destruct H0.
    Qed.

    Section Eq.

      Context {T A} {instTA : Inst T A}.

      Lemma eqₚ_intro {w : World} (t : T w) : ⊢ (t =ₚ t)%P.
      Proof. crushPredEntails3. Qed.

      Lemma eqₚ_refl {w : World} (t : T w) : t =ₚ t ⊣⊢ₚ ⊤ₚ.
      Proof. crushPredEntails3. Qed.

      Lemma eqₚ_sym {w : World} (s t : T w) : s =ₚ t ⊣⊢ₚ t =ₚ s.
      Proof. crushPredEntails3. Qed.

      Lemma eqₚ_trans {w : World} (s t u : T w) : s =ₚ t /\ₚ t =ₚ u ⊢ₚ s =ₚ u.
      Proof. crushPredEntails3. now transitivity (inst t ι). Qed.

    End Eq.
    #[global] Arguments eqₚ_trans {T A _ w} s t u.

  End Lemmas.

  Section SubstMod.
    Import ModalNotations.
    Import ctx.notations.
    Import classes.

    Lemma acc_pathcond {w1 w2} (ω : w2 ⊒ w1) :
      forall ι,  instprop (wco w1) ι -> instprop (wco w2) (inst (sub_acc ω) ι).
    Proof.
      intros.
      rewrite <-instprop_subst.
      now apply (ent_acc_sub ω ι H).
    Qed.

    Import iris.bi.interface.

    (* #[export] Instance knowing_params : *)
    (*   Params (@knowing) 3. Qed. *)

    #[export] Instance knowing_proper {w1 w2 : World} {ω : Sub w1 w2} :
      Proper (entails ==> entails) (knowing ω).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    #[export] Instance knowing_proper_bientails {w1 w2 : World} {ω : Sub w1 w2} :
      Proper (bientails ==> bientails) (knowing ω).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.


    Lemma knowing_exists {w1 w2 : World} {ω : Sub w1 w2} {A} (P : A -> Pred w2) :
      (∃ v, knowing ω (P v)) ⊣⊢ knowing ω (∃ v, P v).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_sepₚ {w1 w2 : World} {ω : Sub w1 w2} (P1 P2 : Pred w2) :
      (knowing ω (P1 ∗ P2)) ⊢ knowing ω P1 ∗ knowing ω P2.
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma assuming_sepₚ {w1 w2 : World} {ω : Sub w1 w2} (P1 P2 : Pred w2) :
      (assuming ω (P1 ∗ P2)) ⊣⊢ assuming ω P1 ∗ assuming ω P2.
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Lemma assuming_True {w1 w2 : World} {ω : Sub w1 w2}  :
      assuming ω True ⊣⊢ True.
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance assuming_proper {w1 w2 : World} {ω : Sub w1 w2} :
      Proper (entails ==> entails) (assuming ω).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance assuming_proper_bientails {w1 w2 : World} {ω : Sub w1 w2} :
      Proper (bientails ==> bientails) (assuming ω).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Class IntoWorldAcc {w1 w2 : World} (sub : Sub w1 w2) (ω : w1 ⊒ w2) :=
      intoacc_eq : sub_acc ω = sub.

    #[export] Instance intoacc_sub_acc  {w1 w2 : World} (ω : w1 ⊒ w2) : IntoWorldAcc (sub_acc ω) ω :=
      eq_refl.

    #[export] Instance intoacc_trans  {w1 w2 w3 : World} {sub12 : Sub w1 w2} {sub23 : Sub w2 w3}
      {ω12 ω23} {intoacc12 : IntoWorldAcc sub12 ω12} {intoacc23 : IntoWorldAcc sub23 ω23}
      : IntoWorldAcc (subst sub12 sub23) (acc_trans ω12 ω23).
    Proof.
      unfold IntoWorldAcc.
      now rewrite sub_acc_trans intoacc12 intoacc23.
    Qed.

    #[export] Instance intoacc_sub_triangular {w1 w2} {ζ : Tri w1 w2} :
      IntoWorldAcc (sub_triangular ζ) (acc_triangular ζ).
    Proof.
      unfold IntoWorldAcc.
      now rewrite sub_acc_triangular.
    Qed.

    #[export] Instance intoacc_refl {w} : IntoWorldAcc (sub_id _) (acc_refl (w := w)). Proof. now cbn. Qed.

    #[export] Instance intoacc_lift {Σ : LCtx} {ι : Valuation Σ} : IntoWorldAcc (w1 := wlctx Σ) (w2 := wnil) (lift ι) (acc_wlctx_valuation ι).
    Proof. by cbn. Qed.
    
    #[export] Instance forgetting_proper {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} :
      Proper (entails ==> entails) (forgetting sub).
    Proof.
      unfold forgetting.
      rewrite <-H.
      crushPredEntails3.
      apply (fromEntails H0); last done.
      now apply acc_pathcond.
    Qed.

    #[export] Instance forgetting_proper_bientails {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} :
      Proper (equiv ==> equiv) (forgetting sub).
    Proof.
      unfold forgetting.
      rewrite <-H.
      crushPredEntails3;
        (apply (fromBientails H0); last done;
         now apply acc_pathcond).
    Qed.
    
    Lemma forgetting_forall {w1 w2 : World} {ω : Sub w1 w2} {A} {P : A -> Pred w1} :
      (∀ v : A, forgetting ω (P v)) ⊣⊢ forgetting ω (∀ v : A, P v).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_wand {w1 w2 : World} {ω : Sub w1 w2} {P1 P2 : Pred w1} :
      (forgetting ω P1 -∗ forgetting ω P2) ⊣⊢ forgetting ω (P1 -∗ P2).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_wand_iff {w1 w2 : World} {ω : Sub w1 w2} {P1 P2 : Pred w1} :
      (forgetting ω P1 ∗-∗ forgetting ω P2) ⊣⊢ forgetting ω (P1 ∗-∗ P2).
    Proof.
      unfold forgetting, bi_wand_iff.
      crushPredEntails3.
    Qed.


    Lemma knowing_assuming {w1 w2 : World} (ω : Sub w2 w1) {P Q} :
      knowing ω P ∗ assuming ω Q ⊢ knowing ω (P ∗ Q).
    Proof.
      unfold knowing, assuming.
      crushPredEntails3.
    Qed.

    Lemma knowing_absorb_forgetting {w1 w2 : World} (ω : Sub w2 w1) {P Q} :
      knowing ω P ∗ Q ⊣⊢ knowing ω (P ∗ forgetting ω Q).
    Proof.
      unfold knowing, forgetting.
      crushPredEntails3; now subst.
    Qed.

    Lemma knowing_pure {w1 w2 : World} (ω : Sub w2 w1) {P} :
      knowing ω (bi_pure P) ⊢ bi_pure P.
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_forall {w1 w2 : World} {ω : Sub w1 w2} {A} {P : A -> Pred w2} :
      knowing ω (∀ v : A, P v) ⊢ (∀ v : A, knowing ω (P v)).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma forgetting_pure {w1 w2 : World} (ω : Sub w2 w1) {P} :
      forgetting ω (bi_pure P) ⊣⊢ bi_pure P.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_emp {w1 w2 : World} (ω : Sub w2 w1) :
      forgetting ω emp ⊣⊢ emp.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_sep {w1 w2 : World} (ω : Sub w2 w1) {P Q}:
      forgetting ω (P ∗ Q) ⊣⊢ forgetting ω P ∗ forgetting ω Q.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma assuming_pure {w1 w2 : World} (ω : Sub w2 w1) {P} :
      bi_pure P ⊢ assuming ω (bi_pure P).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Lemma forgetting_unconditionally {w1 w2 : World} `{IntoWorldAcc w2 w1 sub ω} (P : (□ Pred) w2) :
      forgetting sub (unconditionally P) ⊢ unconditionally (four P ω).
    Proof.
      rewrite -H.
      unfold forgetting, unconditionally, assuming.
      crushPredEntails3.
      eapply H1; eauto using acc_pathcond.
      now rewrite <-H2, <-inst_subst, <-sub_acc_trans.
    Qed.

    Lemma forgetting_unconditionally_drastic {w1 w2 : World} `{IntoWorldAcc w2 w1 sub ω} {P} :
      forgetting sub (unconditionally P) ⊢ P _ ω.
    Proof.
      rewrite -H.
      unfold forgetting, unconditionally, assuming.
      constructor.
      intros.
      now apply (H1 w1 ω ι).
    Qed.

    Lemma unconditionally_T {w} (P : (□ Pred) w) :
      unconditionally P ⊢ T P.
    Proof.
      unfold T, unconditionally, assuming.
      crushPredEntails3.
      eapply H0; try assumption.
      eapply inst_sub_id.
    Qed.

    Lemma getcurval {w : World} :
      ⊢ ∃ (ι : Valuation w), curval ι.
    Proof. unfold curval. crushPredEntails3. Qed.

    Lemma eval_ex `{Inst AT A} {w : World} (t : AT w) :
      ⊢ ∃ v, repₚ v (w := w) t.
    Proof. crushPredEntails3. now eexists. Qed.

    Lemma eval_prop `{InstPred AT} {w : World} (t : AT w) :
      ⊢ ∃ P, proprepₚ P (w := w) t.
    Proof. crushPredEntails3. now exists (instpred t ι). Qed.

    Lemma forgetting_valuation_curval {Σ} {ι : Valuation Σ} :
      ⊢ forgetting (w1 := wlctx Σ) (w2 := wnil) (lift ι) (curval (ι : Valuation (wlctx Σ))).
    Proof.
      unfold curval, forgetting.
      crushPredEntails3.
      now rewrite inst_lift.
    Qed.

    Lemma repₚ_inst_curval {w : World} {ι : Valuation w} {T : LCtx -> Type} `{Inst T A} { t : T w} :
      curval ι ⊢ repₚ (inst t ι) t.
    Proof.
      unfold curval. crushPredEntails3. now subst.
    Qed.

    Lemma forgetting_curval {w w2 : World} {ω2 : Sub w w2} {ι : Valuation w} :
      forgetting ω2 (curval ι) ⊣⊢ repₚ ι ω2.
    Proof.
      unfold forgetting, curval.
      now crushPredEntails3.
    Qed.

    Lemma lift_repₚ `{InstLift AT A} (v : A) {w : World} :
      ⊢ repₚ v (lift v : AT w).
    Proof.
      crushPredEntails3.
    Qed.

    Lemma repₚ_triv {T : LCtx -> Type} `{Inst T A} {a : A} {w : World} {vt : T w}:
      (∀ ι : Valuation w, inst vt ι = a) ->
      ⊢ repₚ a vt.
    Proof.
      crushPredEntails3.
    Qed.

    Lemma repₚ_eqₚ {T : LCtx -> Type} `{Inst T A} {a : A} {w : World} {vt1 vt2 : T w}:
      repₚ a vt1 ∗ eqₚ vt1 vt2 ⊢ repₚ a vt2.
    Proof.
      crushPredEntails3. now rewrite <-H1.
    Qed.


    Lemma eqₚ_triv {T : LCtx -> Type} `{Inst T A} {w : World} {vt1 vt2 : T w}:
      (∀ ι : Valuation w, inst vt1 ι = inst vt2 ι) ->
      ⊢ eqₚ vt1 vt2.
    Proof.
      crushPredEntails3.
    Qed.


    Lemma repₚ_antisym_left {T : LCtx -> Type} `{Inst T A} {a1 a2 : A} {w : World} {sa : T w} :
      ⊢ repₚ a1 sa -∗ repₚ a2 sa -∗ ⌜ a1 = a2 ⌝.
    Proof.
      crushPredEntails3. now subst.
    Qed.

    Lemma proprepₚ_triv {T : LCtx -> Type} `{InstPred T} {a : Prop} {w : World} {vt : T w}:
      (∀ ι : Valuation w, instprop vt ι <-> a) ->
      ⊢ proprepₚ a vt.
    Proof.
      unfold proprepₚ.
      crushPredEntails3.
      - now rewrite instpred_prop in H3.
      - now rewrite instpred_prop.
    Qed.

    Lemma repₚ_cong {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      (f : A1 -> A2) {w : World} (fs : T1 w -> T2 w)
      {v1 : A1} {vs1 : T1 w} :
      (∀ (ι : Valuation w) vs1, inst (fs vs1) ι = f (inst vs1 ι)) ->
      repₚ v1 vs1 ⊢ repₚ (f v1) (fs vs1).
    Proof.
      crushPredEntails3.
      now rewrite H1 H3.
    Qed.

    Lemma repₚ_cong₂ {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      {T3 : LCtx -> Type} `{Inst T3 A3}
      (f : A1 -> A2 -> A3) {w : World} (fs : T1 w -> T2 w -> T3 w)
      {v1 : A1} {vs1 : T1 w} {v2 : A2} {vs2 : T2 w} :
      (∀ (ι : Valuation w) vs1 vs2, inst (fs vs1 vs2) ι = f (inst vs1 ι) (inst vs2 ι)) ->
      repₚ v1 vs1 ∗ repₚ v2 vs2 ⊢ repₚ (f v1 v2) (fs vs1 vs2).
    Proof.
      crushPredEntails3.
      now rewrite H2 H4 H5.
    Qed.

    Lemma repₚ_term_prod {σ1 σ2} {v1 : Val σ1} {v2 : Val σ2} {w : World} {sv1 : STerm σ1 w} {sv2 : STerm σ2 w} :
      repₚ (T := STerm (ty.prod σ1 σ2)) (v1,v2) (term_binop bop.pair sv1 sv2) ⊣⊢ repₚ v1 sv1 ∗ repₚ v2 sv2.
    Proof.
      unfold repₚ.
      crushPredEntails3.
      - now inversion H0.
      - now inversion H0.
      - now f_equal.
    Qed.

    Lemma proprepₚ_cong {T1 : LCtx -> Type} `{InstPred T1}
      {T2 : LCtx -> Type} `{InstPred T2}
      {w : World} (fs : T1 w -> T2 w)
      {v1 : Prop} {vs1 : T1 w} :
      (forall vs1, instpred (fs vs1) ⊣⊢ instpred vs1) ->
      proprepₚ v1 vs1 ⊢ proprepₚ v1 (fs vs1).
    Proof.
      crushPredEntails3.
    Qed.

    Lemma proprepₚ_cong₂ {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      {T3 : LCtx -> Type} `{InstPred T3}
      (f : A1 -> A2 -> Prop) {w : World} (fs : T1 w -> T2 w -> T3 w)
      {v1 : A1} {vs1 : T1 w} {v2 : A2} {vs2 : T2 w} :
      (∀ (ι : Valuation w) vs1 vs2, instpred (fs vs1 vs2) ι <-> f (inst vs1 ι) (inst vs2 ι)) ->
      repₚ v1 vs1 ∗ repₚ v2 vs2 ⊢ proprepₚ (f v1 v2) (fs vs1 vs2).
    Proof.
      crushPredEntails3; now subst.
    Qed.

    Lemma repₚ_elim {T : LCtx -> Type} `{Inst T A} {a b : A} {w : World} {vt : T w}:
      (∀ ι : Valuation w, inst vt ι = a) ->
      repₚ b vt ⊢ ⌜ b = a ⌝.
    Proof.
      crushPredEntails3.
      now transitivity (inst vt ι).
    Qed.

    Lemma repₚ_const {A} {v sv} {w} : repₚ (w := w) (T := Const A) sv v ⊣⊢  ⌜ v = sv ⌝.
    Proof. crushPredEntails3. Qed.
      

    Lemma repₚ_elim_repₚ {T : LCtx -> Type} `{Inst T A} {a1 : A} (a2 : A) {w : World} {vt1 : T w} (vt2 : T w):
      (∀ ι : Valuation w, inst vt1 ι = a1 -> inst vt2 ι = a2) ->
      repₚ a1 vt1 ⊢ repₚ a2 vt2.
    Proof. now crushPredEntails3. Qed.

    Lemma repₚ_inversion_term_inl {σ τ} (v : Val (ty.sum σ τ)) {w : World} (svl : STerm σ w) :
      (repₚ v (term_inl svl) : Pred w) ⊢ ∃ (vl : Val σ), ⌜ v = inl vl ⌝ ∗ repₚ vl svl.
    Proof.
      unfold repₚ.
      destruct v; crushPredEntails3; now inversion H0.
    Qed.

    Lemma repₚ_inversion_term_inr {σ τ} (v : Val (ty.sum σ τ)) {w : World} (svr : STerm τ w) :
      (repₚ v (term_inr svr) : Pred w) ⊢ ∃ vr, ⌜ v = inr vr ⌝ ∗ repₚ vr svr.
    Proof.
      unfold repₚ.
      destruct v; crushPredEntails3; now inversion H0.
    Qed.


    Lemma repₚ_inversion_record {N R} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
      {w : World} {v : recordt R} {svs : NamedEnv (λ τ : Ty, Term w τ) (recordf_ty R)} :
      repₚ (T := STerm (ty.record R)) v (term_record R svs) ⊢
        ∃ (vs : NamedEnv Val (recordf_ty R)), ⌜ v = recordv_fold R vs ⌝ ∗ repₚ vs svs.
    Proof.
      unfold repₚ. crushPredEntails3.
      exists (recordv_unfold R v).
      rewrite recordv_fold_unfold.
      crushPredEntails3.
      now rewrite <-H0, recordv_unfold_fold.
    Qed.

    Lemma repₚ_inversion_union {U} (K : unionk U) {v : Val (ty.union U)}
      {w : World} {st : STerm (unionk_ty U K) w} :
      repₚ (T := STerm (ty.union U)) v (term_union U K st) ⊢
        ∃ (t : Val (unionk_ty U K)), ⌜ v = unionv_fold U (existT K t) ⌝ ∗ repₚ t st.
    Proof.
      unfold repₚ. crushPredEntails3.
      destruct (unionv_unfold U v) as [K' t] eqn:Heqv .
      rewrite <-H0 in Heqv.
      rewrite unionv_unfold_fold in Heqv.
      dependent elimination Heqv.
      exists (inst (st : STerm _ w) ι).
      now crushPredEntails3.
    Qed.

    Section WithEnvironments.
      Import ctx.notations.
      Import env.notations.
      
      Lemma repₚ_invert_snoc
        (T : Set) {S : LCtx → T → Set} {A : T → Set} {Σ : Ctx T}
        {w : World} {b : T} {E1 : Env A Σ} {Es1 : Env (S w) Σ} {v : A b} {db : S w b} 
        (instSA : ∀ τ : T, Inst (λ Σ : LCtx, S Σ τ) (A τ)) :
        @repₚ _ _ inst_env (env.snoc E1 b v) w (env.snoc Es1 b db) ⊢  repₚ E1 Es1 ∗ repₚ v db.
      Proof.
        crushPredEntails3;
        now apply env.inversion_eq_snoc in H0.
      Qed.
    End WithEnvironments.
        
    Lemma forgetting_repₚ `{InstSubst AT, @SubstLaws AT _} {v w1 w2}  `{IntoWorldAcc w1 w2 sub ω} (t : AT w1) :
      (repₚ v (persist t ω) ⊣⊢ forgetting sub (repₚ v t))%I.
    Proof.
      rewrite persist_subst.
      unfold forgetting, repₚ.
      rewrite <-H3.
      constructor. split; rewrite inst_subst; auto using acc_pathcond.
    Qed.

    Lemma instpred_persist {T : LCtx -> Type} `{InstPredSubst T} {_ : SubstLaws T} `{IntoWorldAcc w1 w2 sub ω} (t : T w1) :
      instpred (persist t ω) ⊣⊢ forgetting sub (instpred t).
    Proof.
      now rewrite persist_subst instpred_subst H2.
    Qed.

    Lemma forgetting_proprepₚ `{InstPredSubst AT, @SubstLaws AT _} {v w1 w2} `{IntoWorldAcc w1 w2 sub ω}  (t : AT w1) :
      (proprepₚ v (persist t ω) ⊣⊢ forgetting sub (proprepₚ v t))%I.
    Proof.
      unfold proprepₚ.
      now rewrite instpred_persist -forgetting_wand_iff forgetting_pure.
    Qed.

    Lemma assuming_id {w} {P : Pred w} : assuming (sub_id _) P ⊣⊢ P.
    Proof.
      rewrite /assuming.
      crushPredEntails3.
      - apply H0; [apply inst_sub_id|done].
      - rewrite inst_sub_id in H1; now subst.
    Qed.

    Lemma knowing_trans {w1 w2 w3 : World} {sub12 : Sub w1 w2} `{IntoWorldAcc w2 w3 sub23 ω23} {P : Pred w3} :
      knowing (subst sub12 sub23) P ⊣⊢ knowing sub12 (knowing sub23 P).
    Proof.
      rewrite /knowing.
      rewrite <-H.
      crushPredEntails3.
      - rewrite inst_subst in H1.
        exists (inst (sub_acc ω23) x).
        repeat split; try done.
        { now apply acc_pathcond. }
        now exists x.
      - rewrite inst_subst.
        now subst.
    Qed.

    Lemma assuming_trans {w1 w2 w3 : World} {sub12 : Sub w1 w2} `{IntoWorldAcc w2 w3 sub23 ω23} {P : Pred w3} :
      assuming (subst sub12 sub23) P ⊣⊢ assuming sub12 (assuming sub23 P).
    Proof.
      rewrite /assuming -H.
      crushPredEntails3.
      - rewrite inst_subst in H1.
        apply H1; last done.
        now rewrite H4.
      - rewrite inst_subst in H2.
        apply (H1 (inst (sub_acc ω23) ιpast)); try done.
        now apply acc_pathcond.
    Qed.

    Lemma forgetting_trans {w1 w2 w3 : World} {ω12 : Sub w1 w2} {ω23 : Sub w2 w3} {P : Pred w1} :
      forgetting (subst ω12 ω23) P ⊣⊢ forgetting ω23 (forgetting ω12 P).
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - now rewrite inst_subst in H0.
      - now rewrite inst_subst.
    Qed.

    Lemma forgetting_id {w} {P : Pred w} : forgetting (sub_id _) P ⊣⊢ P.
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - now rewrite <-inst_sub_id.
      - now rewrite inst_sub_id.
    Qed.

    Lemma forgetting_assuming {w1 w2 : World} {ω : Sub w1 w2} {P : Pred w2} :
      forgetting ω (assuming ω P) ⊢ P.
    Proof.
      rewrite /forgetting /assuming.
      now crushPredEntails3.
    Qed.

    Lemma knowing_forgetting {w1 w2 : World} {ω : Sub w1 w2} {P : Pred w1} :
      knowing ω (forgetting ω P) ⊢ P.
    Proof.
      rewrite /forgetting /knowing.
      crushPredEntails3.
      now rewrite <-H0.
    Qed.

    Lemma forgetting_knowing {w1 w2 : World} {ω : Sub w1 w2} {P : Pred w2} :
      P ⊢ forgetting ω (knowing ω P).
    Proof.
      rewrite /forgetting /knowing.
      now crushPredEntails3.
    Qed.

    Lemma assuming_forgetting {w1 w2 : World} {ω : Sub w1 w2} {P : Pred w1} :
      P ⊢ assuming ω (forgetting ω P).
    Proof.
      rewrite /forgetting /assuming.
      crushPredEntails3.
      now rewrite H1.
    Qed.

    Import iris.proofmode.modalities.
    Import iris.proofmode.classes.
    Import iris.proofmode.tactics.

    #[export] Instance intowand_forgetting_unconditionally {p q} {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} {P : ((□ Pred) w1)%modal} {Q R} :
      IntoWand p q (P w2 ω) Q R -> IntoWand p q (forgetting sub (unconditionally P)) Q R | 0.
    Proof.
      unfold IntoWand; cbn.
      unfold IntoWorldAcc in H; rewrite -H.
      now rewrite forgetting_unconditionally_drastic.
    Qed.

    #[export] Instance intowand_forgetting {w1 w2 : World} {sub : Sub w1 w2} `{IntoWorldAcc _ _ sub ω} {P : Pred w1} {Q R}:
      IntoWand false false P Q R -> IntoWand false false (forgetting sub P) (forgetting sub Q) (forgetting sub R) | 1.
    Proof.
      iIntros (Hiw).
      unfold IntoWand; cbn.
      unfold IntoWorldAcc in H.
      rewrite <-H.
      rewrite forgetting_wand.
      pose proof (into_wand false false P Q R) as Hwand.
      cbn in Hwand.
      now rewrite Hwand.
    Qed.

    #[export] Instance intowand_unconditionally {p q} {w} {P : ((□ Pred) w)%modal} {Q R}:
      IntoWand p q (P w acc_refl) Q R -> IntoWand p q (unconditionally P) Q R.
    Proof.
      unfold IntoWand; cbn.
      now rewrite unconditionally_T.
    Qed.

    #[export] Instance intoforall_forgetting {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} {P : Pred w1} {A} {Φ}:
      IntoForall (A := A) P Φ -> IntoForall (forgetting sub P) (fun a => forgetting sub (Φ a)).
    Proof.
      iIntros (Hiw).
      rewrite -H.
      unfold IntoForall; cbn.
      rewrite forgetting_forall.
      now rewrite (into_forall P).
    Qed.

    #[export] Instance intoforall_unconditionally {w} {P : (□ Pred) w} {A} {Φ}:
      IntoForall (A := A) (P w acc_refl) Φ -> IntoForall (unconditionally P) Φ.
    Proof.
      unfold IntoForall; cbn.
      now rewrite unconditionally_T.
    Qed.

    #[export] Instance fromExist_knowing {w1 w2 : World} {A} {ω : Sub w1 w2} {P} {Φ : A -> Pred _}:
      FromExist P Φ -> FromExist (knowing ω P) (fun v => knowing ω (Φ v)).
    Proof.
      unfold FromExist.
      iIntros (H) "[%v H]".
      (* doesn't work for some reason *)
      (* rewrite <-H. *)
      iApply (knowing_proper _ _ H).
      iApply (knowing_proper with "H").
      iIntros "H".
      now iExists v.
    Qed.

    #[export] Instance fromExist_assuming {w1 w2 : World} {A} {ω : Sub w1 w2} {P} {Φ : A -> Pred _}:
      FromExist P Φ -> FromExist (assuming ω P) (fun v => assuming ω (Φ v)).
    Proof.
      unfold FromExist.
      iIntros (H) "[%v H]".
      (* doesn't work for some reason *)
      (* rewrite <-H. *)
      iApply (assuming_proper _ _ H).
      iApply (assuming_proper with "H").
      iIntros "H".
      now iExists v.
    Qed.



    Global Instance elim_modal_unconditionally {w} {P : Box Pred w} {Q : Pred w} :
      ElimModal True false false (unconditionally P) (P w acc_refl) Q Q.
    Proof.
      iIntros (_) "[#HP Hk]".
      iApply "Hk".
      iSpecialize ("HP" $! w acc_refl).
      now rewrite /ElimModal /unconditionally assuming_id.
    Qed.

    Class IntoAssuming {w1 w2 : World} (ω : Sub w1 w2) (P : Pred w1) (Q : Pred w2) :=
      into_assuming : P ⊢ assuming ω Q.

    #[export] Instance into_assuming_default {w1 w2 : World} {ω : Sub w1 w2} (P : Pred w1) :
      IntoAssuming ω P (forgetting ω P) | 10.
    Proof. unfold IntoAssuming. now apply assuming_forgetting. Qed.

    #[export] Instance into_assuming_assuming {w1 w2 : World} {ω : Sub w1 w2} (P : Pred w2) :
      IntoAssuming ω (assuming ω P) P | 0.
    Proof. now unfold IntoAssuming. Qed.

    #[export] Instance into_assuming_forgetting {w1 w2 w3 : World} {ω12 : Sub w1 w2} {ω23 : Sub w2 w3 }(P : Pred w1) :
      IntoAssuming ω23 (forgetting ω12 P) (forgetting (subst ω12 ω23) P) | 0.
    Proof. unfold IntoAssuming. rewrite forgetting_trans. now apply assuming_forgetting. Qed.

    Lemma modality_mixin_assuming {w1 w2 : World} {ω : Sub w1 w2} : modality_mixin (assuming ω) (MIEnvTransform (IntoAssuming ω)) (MIEnvTransform (IntoAssuming ω)).
    Proof.
      constructor; cbn; try done; rewrite /assuming; crushPredEntails3.
      destruct into_assuming as [HPQ].
      crushPredEntails3.
    Qed.

    Definition modality_assuming {w1 w2 : World} (ω : Sub w1 w2) : modality (Pred w2) (Pred w1) :=
      Modality (assuming ω) modality_mixin_assuming.

    #[export] Instance fromModal_assuming {w1 w2 : World} {ω : Sub w1 w2} {P} :
      FromModal True (modality_assuming ω) tt (assuming ω P) P.
    Proof.
      constructor; crushPredEntails3.
    Qed.

    Class IntoForgetting {w1 w2 : World} (ω : Sub w1 w2) (P : Pred w2) (Q : Pred w1) :=
      into_forgetting : P ⊢ forgetting ω Q.

    #[export] Instance into_forgetting_default {w1 w2 : World} {ω : Sub w1 w2} (P : Pred w2) :
      IntoForgetting ω P (knowing ω P) | 10.
    Proof. unfold IntoForgetting. now apply forgetting_knowing. Qed.

    #[export] Instance into_forgetting_knowing {w1 w2 w3 : World} `{IntoWorldAcc w1 w2 sub12 ω12} `{IntoWorldAcc w2 w3 sub23 ω23} (P : Pred w3) :
      IntoForgetting sub12 (knowing sub23 P) (knowing (subst sub12 sub23) P) | 0.
    Proof. unfold IntoForgetting. rewrite knowing_trans. now apply forgetting_knowing. Qed.

    #[export] Instance into_forgetting_forgetting {w1 w2 : World} {ω : Sub w1 w2} (P : Pred w1) :
      IntoForgetting ω (forgetting ω P) P | 0.
    Proof. now unfold IntoForgetting. Qed.


    (* TODO: define typeclass FromForgetting to preserve other forgetting assumptions *)
    Lemma modality_mixin_forgetting {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} : modality_mixin (forgetting sub) (MIEnvTransform (IntoForgetting sub)) (MIEnvTransform (IntoForgetting sub)).
    Proof.
      rewrite -H.
      constructor; cbn; try done; rewrite /forgetting; crushPredEntails3.
      - destruct H0 as [H0]. apply H0; done.
      - apply H0; last done. now apply acc_pathcond.
    Qed.

    Definition modality_forgetting {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} : modality (Pred w1) (Pred w2) :=
      Modality (forgetting sub) modality_mixin_forgetting.

    #[export] Instance fromModal_forgetting {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} {P} :
      FromModal True modality_forgetting tt (forgetting sub P) P.
    Proof.
      constructor; crushPredEntails3.
    Qed.

    Lemma knowing_acc_snoc_right {w b P} :
      knowing (w1 := wsnoc w b) sub_wk1 P ⊣⊢ ∃ v, forgetting (w1 := wsnoc w b) (sub_snoc (sub_id w) b (term_val _ v)) P.
    Proof.
      unfold knowing, forgetting.
      crushPredEntails3.
      - destruct (env.view x) as [ιp v].
        exists v.
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b v).
        now rewrite inst_sub_id -H0 inst_sub_wk1.
      - exists (env.snoc ι b x).
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b x) in H0.
        rewrite inst_sub_id in H0.
        repeat split; eauto using inst_sub_wk1.
        now rewrite instprop_subst inst_sub_wk1.
    Qed.

    Lemma knowing_acc_subst_right {w : World} {x σ} `{xIn : (x∷σ ∈ w)%katamaran}
      {t : Term (w - x∷σ) σ} {P} :
      (knowing (w1 := wsubst w x t) (sub_single xIn t) P : Pred w) ⊣⊢ 
        (eqₚ (term_var_in xIn) (subst t (sub_shift xIn)) ∗
           assuming (w1 := wsubst w x t) (sub_single xIn t) P)%I.
    Proof.
      unfold knowing, assuming.
      crushPredEntails3.
      - subst; cbn.
        rewrite <-inst_lookup, <-inst_subst.
        now rewrite lookup_sub_single_eq subst_shift_single.
      - rewrite !inst_sub_single2 in H3 H0.
        apply (f_equal (fun ι => env.remove (x∷σ) ι xIn)) in H0, H3.
        rewrite !env.remove_insert in H3, H0.
        assert (ιpast = x0) by (now transitivity (env.remove (x∷σ) ι xIn)).
        now subst.
      - exists (inst (sub_shift xIn) ι).
        assert (instprop (wco w) (inst (sub_single xIn t) (inst (sub_shift xIn) ι))) as Hpc2.
        { rewrite inst_sub_single_shift; first done.
          now rewrite <-inst_subst.
        }
        assert (inst t (inst (sub_shift xIn) ι) = env.lookup ι xIn) as Hinst.
        { now rewrite <-inst_subst. }
        assert (inst (sub_single xIn t) (inst (sub_shift xIn) ι) = ι) as Hinst2.
        { now rewrite inst_sub_single_shift. }
        repeat split; try done.
        + now rewrite instprop_subst.
        + apply H1; try done.
          now rewrite instprop_subst.
    Qed.
      

    Lemma forgetting_acc_snoc_left_repₚ {w1 w2 : World} {b} {ω : Sub w1 w2} {v} :
      ⊢ forgetting (w1 := wsnoc w1 b) (sub_snoc ω b (term_val _ v)) (repₚ v term_var_zero).
    Proof.
      unfold forgetting.
      now crushPredEntails3.
    Qed.

    Lemma assuming_acc_snoc_right {w b P} :
      assuming (w1 := wsnoc w b) sub_wk1 P ⊣⊢ ∀ v, forgetting (w1 := wsnoc w b) (sub_snoc (sub_id _) b (term_val _ v)) P.
    Proof.
      unfold assuming, forgetting.
      crushPredEntails3.
      - change (P (env.snoc (inst (sub_id w) ι) b a)).
        rewrite inst_sub_id.
        apply H0.
        + eapply inst_sub_wk1.
        + now rewrite instprop_subst inst_sub_wk1.
      - destruct (env.view ιpast) as [ι' v].
        rewrite inst_sub_wk1 in H1; subst.
        specialize (H0 v).
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b v) in H0.
        rewrite inst_sub_id in H0.
        now apply H0.
    Qed.

    Lemma forgetting_acc_pathcondition_right {w : World}
      {C : PathCondition w}
      {P : Pred (wpathcondition w C)} :
      (forgetting (w2 := wpathcondition w C) (sub_id _) P : Pred w) ⊣⊢ P.
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id in H0.
      - now rewrite inst_sub_id.
    Qed.

    Lemma assuming_acc_pathcondition_right
      {w : World} {sc : PathCondition w} {P : Pred w} :
      instpred sc ∗ assuming (w2 := wpathcondition w sc) (sub_id _) P ⊢ P.
    Proof.
      unfold assuming.
      crushPredEntails3.
      apply H1.
      - apply inst_sub_id.
      - rewrite instpred_prop in H0.
        now apply instprop_cat.
    Qed.

    
    Lemma forgetting_acc_pathcondition_right_sep {w : World} {P : Pred w} {C : PathCondition w}
      {Q : Pred (wpathcondition w C)} :
      (forgetting (w1 := wpathcondition w C) (sub_id _) (P ∗ Q) : Pred w) ⊣⊢ 
        P ∗ forgetting (w2 := wpathcondition w C) (sub_id _) Q.
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id in H0.
      - now rewrite inst_sub_id.
    Qed.
    
    (* Lemma assuming_acc_subst_right_left  {w : World} x {σ} {xIn : x∷σ ∈ w} *)
    (*   (t : Term (w - x∷σ) σ) {P} : *)
    (*   assuming (acc_subst_right x t) P ⊣⊢ *)
    (*     eqₚ (term_var xIn) (subst (sub_wk1 xIn) t) ∗ *)
    (*     forgetting (acc_subst_left x) P. *)

    Definition assuming_acc_match_right {w : World} {σ} {s : Term w σ}
      {p : @Pattern LVar σ} (pc : PatternCase p) : 
      ⊢ assuming (w1 := wmatch w s p pc) (sub_cat_left (PatternCaseCtx pc))
        (eqₚ (persist s (acc_match_right pc)) (pattern_match_term_reverse p pc (sub_wmatch_patctx pc))).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

  End SubstMod.

  Module logicalrelation.
    Import ModalNotations.
    Import iris.bi.interface.
    Import iris.proofmode.classes.
    Import iris.proofmode.tactics.
    Class Rel (AT : TYPE) (A : Type) : Type :=
      MkRel { RSat : A -> (⊢ AT -> Pred)%modal }.
    Bind Scope rel_scope with Rel.

    #[global] Arguments MkRel [AT A] &.
    #[global] Arguments RSat {_ _} !Rel _ {w} _.
    (* We use the same script ℛ as in the paper. This encodes (ι,x,y) ∈ ℛ[_,_]
       from the paper as (ℛ ι x y), i.e. the types of the relation are
       implicit. *)
    #[local] Notation "ℛ⟦ R ⟧" := (RSat R%R) (format "ℛ⟦ R ⟧").

    
    (* This instance can be used for any (first-class) symbolic data that can be
       instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
    Definition RInst AT A {instA : Inst AT A} : Rel AT A :=
      MkRel repₚ.
    Arguments RInst _ _ {_} : simpl never.

    Definition RInstPropIff AT {instA : InstPred AT} : Rel AT Prop :=
      MkRel proprepₚ.
    Arguments RInstPropIff _ {_}.

    #[export] Instance RBox {AT A} (RA : Rel AT A) : Rel (Box AT) A :=
      MkRel 
        (fun v w t => unconditionally (fun w2 ω => ℛ⟦ RA ⟧ v (t w2 ω))).
    Arguments RBox {AT A} RA : simpl never.

    #[export] Instance RImpl {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
      Rel (Impl AT BT) (A -> B) :=
      MkRel (fun fc w fs => ∀ a ta, ℛ⟦ RA ⟧ a ta -∗ ℛ⟦ RB ⟧ (fc a) (fs ta))%I.
    Arguments RImpl {_ _ _ _} RA RB : simpl never.

    #[export] Instance intowand_rimpl {A AT B BT} {RA : Rel AT A} {RB : Rel BT B}  {w} {a sa f} {sf} :
      IntoWand false false (RSat (RImpl RA RB) f sf) (RSat RA a sa) (RSat RB (f a) (w := w) (sf sa)).
    Proof.
      unfold IntoWand, RImpl; cbn.
      iIntros "H".
      now iApply "H".
    Qed.

    #[export] Instance RForall {𝑲}
      {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
      (RA : forall K, Rel (AT K) (A K)) :
      Rel (@W.Forall 𝑲 AT) (forall K : 𝑲, A K) :=
      MkRel (fun fc w fs => ∀ₚ K : 𝑲, ℛ⟦ RA K ⟧ (fc K) (fs K))%P.
    Arguments RForall {_ _ _} RA : simpl never.
    #[export] Instance intoforall_rforall {𝑲}
      {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
      {RA : forall K, Rel (AT K) (A K)} {f w} {sf : forall K, AT K w} :
      IntoForall (RSat (RForall RA) f sf) (fun K => RSat (RA K) (f K) (sf K)).
    Proof.
      unfold IntoForall, RForall.
      now cbn.
    Qed.

    #[export] Instance RVal (σ : Ty) : Rel (fun Σ => Term Σ σ) (Val σ) :=
      RInst (fun Σ => Term Σ σ) (Val σ).
    Arguments RVal σ : simpl never.

    #[export] Instance RNEnv (N : Set) (Δ : NCtx N Ty) : Rel _ _ :=
      RInst (fun Σ => NamedEnv (Term Σ) Δ) (NamedEnv Val Δ).
    #[export] Instance REnv (Δ : Ctx Ty) : Rel _ _ :=
        RInst (fun Σ : LCtx => Env (Term Σ) Δ) (Env Val Δ).
    #[export] Instance RUnit : Rel Unit unit := RInst Unit unit.

    #[export] Instance RPathCondition : Rel PathCondition Prop := RInstPropIff PathCondition.
    Arguments RPathCondition : simpl never.
    #[export] Instance RFormula : Rel Formula Prop := RInstPropIff Formula.
    Arguments RFormula : simpl never.

    #[export] Instance RChunk : Rel Chunk SCChunk := RInst Chunk SCChunk.

    (* Give the [RMsg] instance a lower priority (3) than [RImpl]. *)
    #[export] Instance RMsg M {AT A} (RA : Rel AT A) : Rel (M -> AT) A | 3 :=
      MkRel (fun v w t => ∀ₚ m, RSat RA v (t m))%P.
    #[global] Arguments RMsg M%modal {AT A} RA%R.

    Inductive RList' {AT A} (R : Rel AT A) :
      list A -> ∀ [w : World], WList AT w -> Pred w :=
    | rlist_nil : ∀ w ι, @RList' _ _ R nil w nil ι
    | rlist_cons {w v ts vs} {t : AT w}: ∀ ι,
      RSat R v t ι -> RList' R vs ts ι ->
      RList' R (cons v vs) (cons t ts) ι.

    #[export] Instance RList {AT A} (R : Rel AT A) : Rel (WList AT) (list A) :=
      MkRel (RList' R).

    #[export] Instance RHeap : Rel SHeap SCHeap := RList RChunk.
    (* priority 1 so that RUnit is picked first (not sure why we have both) *)
    #[export] Instance RConst A : Rel (Const A) A | 1 := RInst (Const A) A.

    #[export] Instance RProd `(RA : Rel AT A, RB : Rel BT B) :
      Rel (WProd AT BT) (A * B)%type :=
      MkRel (fun '(va,vb) w '(ta,tb) => ℛ⟦RA⟧ va ta ∗ ℛ⟦RB⟧ vb tb)%I.

    #[export] Instance RMatchResult {N σ} (p : @Pattern N σ) :
      Rel (SMatchResult p) (MatchResult p) :=
      MkRel
        (fun '(existT pc2 vs) w '(existT pc1 ts) =>
           ∃ₚ e : pc1 = pc2,
             ℛ⟦RNEnv _ (PatternCaseCtx pc2)⟧
               vs
               (eq_rect pc1 (fun pc => NamedEnv (Term w) (PatternCaseCtx pc))
                  ts pc2 e)
               )%P.

    #[export] Instance RIn b : Rel (ctx.In b) (Val (type b)) :=
      MkRel (fun v w bIn ι => env.lookup ι bIn = v).

    Module Import notations.
      Open Scope rel_scope.
      Notation "ℛ⟦ R ⟧" := (RSat R%R) (format "ℛ⟦ R ⟧").
      Notation "A -> B" := (RImpl A%R B%R) : rel_scope.
      Notation "□ᵣ A"    := (RBox A%R) (at level 9) : rel_scope.
      Notation "'∀ᵣ' x .. y , R " :=
        (RForall (fun x => .. (RForall (fun y => R)) ..))
          (at level 200, x binder, y binder, right associativity,
            format "'[  ' '[  ' ∀ᵣ  x  ..  y ']' ,  '/' R ']'")
          : rel_scope.
    End notations.

  End logicalrelation.

  Section ModalRel.
    Import logicalrelation logicalrelation.notations iris.bi.interface notations ModalNotations.
    Lemma forgetting_RImpl {AT A BT B} {RA : Rel AT A} {RB : Rel BT B} {w1 w2 : World} {ω : Sub w1 w2} {f sf} :
      forgetting ω (ℛ⟦ RImpl RA RB ⟧ f sf) ⊣⊢ (∀ a sa, forgetting ω (ℛ⟦ RA ⟧ a sa) -∗ forgetting ω (ℛ⟦ RB ⟧ (f a) (sf sa))).
    Proof.
      unfold RImpl at 1. cbn.
      rewrite <-forgetting_forall.
      apply derived_laws.bi.forall_proper; intros a.
      rewrite <-forgetting_forall.
      apply derived_laws.bi.forall_proper; intros sa.
      rewrite <-forgetting_wand.
      now apply derived_laws.bi.wand_proper.
    Qed.
  End ModalRel.

  Section LRCompat.
    Import notations.
    Import logicalrelation.
    Import logicalrelation.notations.
    (* Import ModalNotations. *)
    Import iris.proofmode.tactics.
    
    Lemma refine_term_val {w τ v} : ⊢ (ℛ⟦RVal τ⟧ v (term_val τ v) : Pred w).
    Proof. unfold RVal, RInst. crushPredEntails3. Qed.

    Lemma refine_term_val2 {w τ v1 v2} : bi_pure (v1 = v2) ⊣⊢ (ℛ⟦RVal τ⟧ v1 (term_val τ v2) : Pred w).
    Proof. unfold RVal, RInst. crushPredEntails3. Qed.

    Lemma refine_term_binop {w τ1 τ2 τ3} {op : BinOp τ1 τ2 τ3} {a1 sa1 a2 sa2}:
      ℛ⟦RVal τ1⟧ a1 sa1 ∗ ℛ⟦RVal τ2⟧ a2 sa2 ⊢
        ℛ⟦RVal τ3⟧ (bop.eval op a1 a2) (w := w) (term_binop op sa1 sa2).
    Proof.
      unfold RVal, RInst; crushPredEntails3; now subst.
    Qed.
    
    Lemma refine_unit {w} {u su} :
      ⊢ ℛ⟦ RUnit ⟧ u su : Pred w.
    Proof. destruct u, su. now crushPredEntails3. Qed.
    
    Lemma refine_nil {AT A} {R : Rel AT A} {w} :
      ⊢ ℛ⟦ RList R ⟧ nil (nil : list (AT w)).
    Proof.
      crushPredEntails3.
      constructor.
    Qed.
    Hint Resolve refine_nil : core.

    Lemma refine_cons {AT A} {R : Rel AT A} {w} :
      ⊢ ℛ⟦ R -> RList R -> RList R ⟧ cons (@cons (AT w)).
    Proof.
      crushPredEntails3.
      now constructor.
    Qed.

    Lemma refine_if {AT A} {R : Rel AT A} {w} {v1 sv1 v2 sv2 c sc}:
      ⊢ ℛ⟦ RConst bool ⟧ c sc -∗ ℛ⟦ R ⟧ v1 sv1 -∗ ℛ⟦ R ⟧ v2 sv2 -∗
        ℛ⟦ R ⟧ (if c then v1 else v2) (if sc then sv1 else sv2 : AT w).
    Proof.
      unfold RConst, RInst; cbn.
      crushPredEntails3; subst.
      now destruct sc.
    Qed.

    Lemma RList_ind {AT : TYPE} {A : Type} {R : Rel AT A}
      (P : Rel (WList AT) (list A)) :
      ∀ (w : World),
        (ℛ⟦P⟧ [] ([] : WList AT w) ∗
           (∀ (v : A) (t : AT w) (vs : list A) (ts : WList AT w),
               ℛ⟦R⟧ v t -∗ ℛ⟦ RList R ⟧ vs ts -∗ ℛ⟦P⟧ vs ts -∗ ℛ⟦P⟧ (v :: vs) (t :: ts)) ⊢
           ∀ (l : list A) (l0 : WList AT w), ℛ⟦ RList R ⟧ l l0 -∗ ℛ⟦P⟧ l l0)%I.
    Proof.
      intros w. constructor.
      intros ι Hpc (Hnil & Hcons) l l0 HRList.
      induction HRList.
      - now apply Hnil.
      - apply Hcons; try done.
        now apply IHHRList.
    Qed.

    Lemma refine_map {AT1 A1} {R1 : Rel AT1 A1} {AT2 A2} {R2 : Rel AT2 A2} {w} :
      ⊢ ℛ⟦ (R1 -> R2) -> RList R1 -> RList R2 ⟧ (@map _ _) (@map _ _ : Impl _ _ w).
    Proof.
      iIntros (f sf) "Hf %l %sl Hl".
      iApply (RList_ind (R := R1) (MkRel (fun l w sl => ℛ⟦ (R1 -> R2) -> RList R2 ⟧ (fun f => map f l) (fun sf => map sf sl : list (AT2 w)))) with "[] Hl Hf").
      clear; iIntros; iSplit.
      - iIntros (f sf) "Hf".
        iApply (refine_nil (R := R2)).
      - iIntros (v sv vs svs) "Hv Hvs IHvs %f %sf #Hf".
        iApply (refine_cons (R := R2) with "[Hf Hv]").
        + now iApply ("Hf" $! v sv with "Hv").
        + now iApply ("IHvs" $! f sf with "Hf").
    Qed.

    Lemma RList_RInst {AT A} `{InstSubst AT A, @SubstLaws AT _} :
      forall (v : list A) (w : World) (t : list (AT w)),
        ℛ⟦RList (RInst AT A)⟧ v t ⊣⊢ ℛ⟦RInst (fun w => list (AT w)) (list A)⟧ v t.
    Proof.
      unfold RInst. crushPredEntails3.
      - induction H4; first done.
        now rewrite <-H4, <-IHRList'.
      - revert v H4. induction t; intros v H4; subst; repeat constructor.
        now apply IHt.
    Qed.

    Lemma refine_four {w1 w2} `{IntoWorldAcc w2 w1 sub ω} {AT A} (RA : Rel AT A) :
      (⊢ ∀ (v__s : Box AT w2) v, (forgetting sub (ℛ⟦□ᵣ RA⟧ v v__s) → ℛ⟦□ᵣ RA⟧ v (four v__s ω)))%I.
    Proof.
      iIntros (v__s v) "Hbox".
      now iApply (forgetting_unconditionally (λ (w0 : World) (ω0 : Acc w2 w0), ℛ⟦RA⟧ v (v__s w0 ω0))).
    Qed.

    Lemma refine_T {AT A} (R : Rel AT A) :
      forall v (w : World), (⊢ ∀ (t : Box AT w), (ℛ⟦ □ᵣ R ⟧ v t) → ℛ⟦R⟧ v (T t))%I.
    Proof.
      iIntros (v w t) "Hvt".
      unfold RBox; cbn.
      now iApply (unconditionally_T (λ (w2 : World) (ω : Acc w w2), ℛ⟦R⟧ v (t w2 ω))).
    Qed.

    Lemma refine_apply {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
      forall v f (w : World),
        (⊢ ∀ F (t : AT w), ℛ⟦RA -> RB⟧ f F → ℛ⟦RA⟧ v t → ℛ⟦RB⟧ (f v) (F t))%I.
    Proof. iIntros (v f w F t) "#Hf #Hv". now iApply "Hf". Qed.

    Lemma refine_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _}
      {v : A} {w1 w2 : World} `{IntoWorldAcc w1 w2 sub ω} (t : AT w1) :
        forgetting sub (ℛ⟦RInst AT A⟧ v t) ⊢ ℛ⟦RInst AT A⟧ v (persist t ω).
    Proof. 
      iIntros "Hvt".
      now iApply forgetting_repₚ.
    Qed.

    Lemma refine_formula_bool {w : World} {v} {sv : Term w ty.bool} :
      ℛ⟦RVal ty.bool⟧ v sv ⊢ ℛ⟦RFormula⟧ (v = true) (formula_bool sv).
    Proof. unfold RVal, RInst. crushPredEntails3; cbn in *; now subst. Qed.

    Lemma refine_formula_relop {w : World} {σ v1 v2} {sv1 sv2 : Term w σ}  {relop : RelOp σ}:
      ℛ⟦ RVal σ ⟧ v1 sv1 ∗ ℛ⟦ RVal σ ⟧ v2 sv2 ⊢
        ℛ⟦RFormula⟧ (bop.eval_relop_prop relop v1 v2) (formula_relop relop sv1 sv2).
    Proof.
      unfold RFormula, RVal, RInst. crushPredEntails3; now subst.
    Qed.

    Lemma refine_formula_persist :
      forall (w1 w2 : World) `{IntoWorldAcc w1 w2 sub ω} (f : Formula w1) (p : Prop),
        ⊢ forgetting sub (ℛ⟦RFormula⟧ p f) -∗ ℛ⟦RFormula⟧ p (persist f ω).
    Proof.
      iIntros (v w1 w2 sub ω Hsubω t) "Hvt".
      now iApply forgetting_proprepₚ.
    Qed.

    Lemma refine_inst_subst {Σ} {T : LCtx -> Type} `{InstSubst T A} (vs : T Σ) {w : World} :
      ⊢ ℛ⟦ RInst (Sub Σ) (Valuation Σ) -> RInst T A ⟧ (inst vs) (subst vs : Sub Σ w -> T w)%I.
    Proof.
      unfold RImpl, RInst. cbn.
      crushPredEntails3.
      now rewrite inst_subst H4.
    Qed.

    Lemma refine_instprop_subst {Σ} {T : LCtx -> Type} `{InstPredSubst T}
      (vs : T Σ) {w : World} :
      ⊢ ℛ⟦ (RInst (Sub Σ) (Valuation Σ) -> RInstPropIff T) ⟧ (instprop vs) (subst vs : Sub Σ w -> T w)%I.
    Proof.
      unfold RImpl, RInst. cbn.
      unfold proprepₚ; cbn.
      crushPredEntails3; subst.
      - rewrite instpred_prop in H5.
        now rewrite <-instprop_subst.
      - now rewrite instpred_prop instprop_subst.
    Qed.

    Lemma refine_lift {AT A} `{InstLift AT A} {w : World} (a : A) :
      ⊢ ℛ⟦RInst AT A⟧ a (lift a : AT w).
    Proof. iApply lift_repₚ. Qed.

    Lemma refine_rinst_sub_initial {w : World} {ι : Valuation w}: 
      curval ι ⊢ ℛ⟦RInst (Sub w) (Valuation w)⟧ ι (sub_id w).
    Proof. unfold RInst. crushPredEntails3. now rewrite inst_sub_id. Qed.

    Import ModalNotations. 
    Lemma refine_rnenv_sub_acc {w : World} {ι : Valuation w} {w2 : World} {ω2 : Sub w w2} :
      forgetting ω2 (curval (w := w) ι) ⊢ ℛ⟦RNEnv LVar w⟧ ι ω2.
    Proof.
      unfold forgetting, RNEnv, RInst, curval; now crushPredEntails3.
    Qed.

    Section WithNotations.
      Import env.notations.
      Import ctx.notations.
      Lemma refine_namedenv_snoc {N} {Δ : NCtx N Ty} {x : N} {σ : Ty} {w : World} {vs : NamedEnv Val Δ} {svs : NamedEnv (Term w) Δ} {v : Val σ} {sv : Term w σ} :
        ℛ⟦RNEnv N Δ⟧ vs svs ∗ ℛ⟦RVal σ⟧ v sv ⊢ ℛ⟦RNEnv N (Δ ▻ x∷σ)⟧ (vs.[x∷σ ↦ v])%env (svs.[x∷σ ↦ sv])%env.
      Proof.
        iIntros "[Hvs Hv]".
        iApply (repₚ_cong₂ (T1 := fun w => NamedEnv (Term w) Δ) (T2 := STerm σ) (T3 := fun w => NamedEnv (Term w) (Δ ▻ x∷σ)) (fun vs v => vs.[x∷σ ↦ v]) (fun vs (v : Term w σ) => vs.[x∷σ ↦ v]) with "[$Hvs $Hv]").
        now intros.
      Qed.

      Lemma refine_sub_snoc {τ : Ty} {Γ : LCtx} {x : LVar}
        {w : World} {vs : NamedEnv Val Γ} {svs : NamedEnv (Term w) Γ}
        {v : Val τ} {sv : Term w τ} :
        (ℛ⟦RNEnv LVar Γ⟧ vs svs) ∗  ℛ⟦RVal τ⟧ v sv ⊢
          ℛ⟦RNEnv LVar (Γ ▻ x∷τ)⟧ (vs.[x∷τ ↦ v])%env (sub_snoc svs (x∷τ) sv).
      Proof.
        iIntros "[H1 H2]".
        iApply (repₚ_cong₂ (T1 := fun w => NamedEnv (Term w) Γ) (T2 := STerm τ) (T3 := fun w => NamedEnv (Term w) (Γ ▻ (x∷τ))) (fun vs v => vs.[x∷τ ↦ v]) (fun vs (v : Term w τ) => sub_snoc vs (x∷τ) v) with "[$H1 $H2]").
        now intros.
      Qed.

      Lemma refine_env_snoc {Δ : Ctx Ty} {τ} {w : World} {vs : Env Val Δ} {svs : Env (Term w) Δ} {v : Val τ} {sv : Term w τ} :
        ℛ⟦REnv Δ⟧ vs svs ∗ ℛ⟦RVal τ⟧ v sv ⊢ ℛ⟦REnv (Δ ▻ τ)⟧ (vs ► ( τ ↦ v ))%env (svs ► (τ ↦ sv ))%env.
      Proof.
        iIntros "[Hvs Hv]".
        iApply (repₚ_cong₂ (T1 := fun w => Env (Term w) Δ) (T2 := STerm τ) (T3 := fun w => Env (Term w) (Δ ▻ τ)) (fun vs v => vs ► ( τ ↦ v )) (fun vs (v : Term w τ) => vs ► ( τ ↦ v )) with "[$Hvs $Hv]").
        now intros.
      Qed.

      Lemma refine_env_nil {w : World} {vs : Env Val [ctx]} {svs : Env (Term w) [ctx]} :
        ⊢ ℛ⟦REnv [ctx]⟧ vs (w := w) svs.
      Proof.
        unfold REnv, RInst; cbn.
        env.destroy vs.
        env.destroy svs.
        now iApply (repₚ_triv (T := fun w => Env (Term w) [ctx])).
      Qed.


      Lemma refine_namedenv_nil {N} {w : World} :
         ⊢ ℛ⟦RNEnv N [ctx] ⟧ env.nil (env.nil : NamedEnv (Term w) [ctx]).
      Proof.
        iApply (repₚ_triv (T := fun w => NamedEnv (Term w) [ctx])).
        now intros.
      Qed.

      Lemma refine_namedenv_singleton {N : Set} {x : N} {σ : Ty} {w : World} {v : Val σ} {sv : Term w σ} :
        ℛ⟦RVal σ⟧ v sv ⊢ ℛ⟦RNEnv N (ctx.nil ▻ x∷σ)⟧ ([env].[x∷σ ↦ v])%env ([env].[x∷σ ↦ sv])%env.
      Proof.
        iIntros "Hv".
        iApply (refine_namedenv_snoc with "[$Hv]").
        iApply refine_namedenv_nil.
      Qed.

    End WithNotations.

    Lemma refine_chunk_ptsreg {w τ} {pc a ta} : 
      ℛ⟦RVal τ ⟧ a ta ⊢ ℛ⟦RChunk⟧ (scchunk_ptsreg pc a) (w := w)(chunk_ptsreg pc ta).
    Proof.
      unfold RChunk, RVal, RInst; cbn.
      crushPredEntails3; now subst.
    Qed.

    Lemma refine_chunk_user {w : World} { c vs svs} :
      ℛ⟦REnv (𝑯_Ty c)⟧ vs svs ⊢ ℛ⟦RChunk⟧ (scchunk_user c vs) (w := w) (chunk_user c svs).
    Proof.
      unfold REnv, RChunk, RInst; crushPredEntails3.
      now subst.
    Qed.

    Lemma refine_pattern_match {w : World} {σ} {v : Val σ} {sv : Term w σ}
      {p : @Pattern LVar σ} : 
      ℛ⟦ RVal σ ⟧ v sv ⊢
        let (pc, δpc) := pattern_match_val p v in
        knowing (w1 := wmatch w sv p pc) (sub_cat_left (PatternCaseCtx pc))
          (ℛ⟦ RNEnv LVar (PatternCaseCtx pc) ⟧  δpc
             (sub_cat_right (PatternCaseCtx pc) : NamedEnv _ _)).
    Proof.
      pose proof (pattern_match_val_inverse_left p v) as eq.
      destruct (pattern_match_val p v) as [pc args].
      unfold pattern_match_val_reverse' in eq; cbn in eq.
      unfold knowing, RVal, RNEnv, RInst.
      crushPredEntails3.
      exists (env.cat ι args).
      now rewrite instprop_subst inst_subst !inst_sub_cat_left
        inst_pattern_match_term_reverse inst_sub_cat_right eq.
    Qed.

    Import ctx.notations.
    Lemma refine_pattern_match_var {w : World} {σ} {v : Val σ} {x : LVar} {xIn : ctx.In (x∷σ) w}
      {p : @Pattern LVar σ} : 
      ℛ⟦ RIn (x∷σ) ⟧ v xIn ⊢
        let (pc, δpc) := pattern_match_val p v in
        knowing (w1 := wmatchvar w xIn p pc) (sub_matchvar_right (x := x) pc)
        (ℛ⟦ RNEnv LVar (PatternCaseCtx pc) ⟧  δpc
           (wmatchvar_patternvars pc : NamedEnv (Term (wmatchvar w xIn p pc)) _)).
    Proof.
      pose proof (pattern_match_val_inverse_left p v) as eq.
      destruct (pattern_match_val p v) as [pc args].
      unfold pattern_match_val_reverse' in eq; cbn in eq.
      unfold knowing, RVal, RNEnv, RInst.
      crushPredEntails3.
      exists (env.remove (x∷σ) (env.cat ι args) (ctx.in_cat_left (PatternCaseCtx pc) xIn)).
      rewrite !instprop_subst !inst_subst.
      rewrite inst_sub_single2 inst_pattern_match_term_reverse.
      unfold wmatchvar_patternvars.
      rewrite inst_eq_rect.
      rewrite env.remove_cat_left.
      rewrite eq_rect_sym1.
      rewrite inst_sub_cat_right.
      rewrite eq.
      rewrite <-env.insert_cat_left.
      rewrite <-H0.
      rewrite env.insert_remove.
      now rewrite inst_sub_cat_left.
    Qed.

    Lemma refine_unfreshen_patterncaseenv {N : Set} {w : World} {Σ} {n : N -> LVar} {σ}
      {p : @Pattern N σ} {pc : PatternCase (freshen_pattern n Σ p)}
      {vs : NamedEnv Val (PatternCaseCtx pc)}
      {svs : NamedEnv (Term w) (PatternCaseCtx pc)} :
      ℛ⟦RNEnv LVar (PatternCaseCtx pc)⟧ vs svs
          ⊢ ℛ⟦RNEnv N (PatternCaseCtx (unfreshen_patterncase n Σ p pc))⟧ (unfreshen_patterncaseenv n p pc vs) (unfreshen_patterncaseenv n p pc svs).
    Proof.
      unfold RNEnv, RInst, repₚ; cbn.
      crushPredEntails3.
      now rewrite inst_unfreshen_patterncaseenv H0.
    Qed.


    Lemma RVal_eqₚ {σ v} {w : World} {sv1 sv2 : Term w σ}:
      ℛ⟦ RVal σ ⟧ v sv1 ∗ eqₚ sv1 sv2 ⊢ ℛ⟦ RVal σ ⟧ v sv2.
    Proof.
      unfold RVal, RInst.
      crushPredEntails3.
      now subst.
    Qed.

    Lemma RVal_pair {σ1 σ2 v1 v2} {w : World} {sv1 : Term w σ1} {sv2 : Term w σ2}:
      ℛ⟦ RVal σ1 ⟧ v1 sv1 ∗ ℛ⟦ RVal σ2 ⟧ v2 sv2 ⊣⊢ ℛ⟦ RVal (ty.prod σ1 σ2) ⟧ (v1 , v2) (term_binop bop.pair sv1 sv2).
    Proof.
      unfold RVal, RInst, repₚ.
      crushPredEntails3.
      - now f_equal.
      - now inversion H0.
      - now inversion H0.
    Qed.

    Lemma RVal_union_invertK {U : unioni} {K1 K2 : unionk U} {vf : Val (unionk_ty U K1)} {w : World} {tf : Term w (unionk_ty U K2)} :
      ℛ⟦RVal (ty.union U)⟧ (unionv_fold U (existT K1 vf)) (term_union U K2 tf) ⊢ bi_pure (K1 = K2).
    Proof.
      unfold RVal, RInst, repₚ; crushPredEntails3.
      rewrite unionv_fold_inj in H0.
      now inversion H0.
    Qed.

    Lemma RVal_union {U : unioni} {K : unionk U} {vf : Val (unionk_ty U K)} {w : World} {tf : Term w (unionk_ty U K)} :
      ℛ⟦RVal (ty.union U)⟧ (unionv_fold U (existT K vf)) (term_union U K tf) ⊣⊢
        ℛ⟦RVal (unionk_ty U K)⟧ vf tf.
    Proof.
      unfold RVal, RInst, repₚ; crushPredEntails3; last by subst.
      rewrite unionv_fold_inj in H0.
      now apply inj_right_pair in H0.
    Qed.

    Lemma refine_tuple_pattern_match_env {N Δ σs} {p : TuplePat σs Δ} {w : World} :
      ⊢ ℛ⟦REnv σs -> RNEnv N Δ⟧ (tuple_pattern_match_env p) (tuple_pattern_match_env (T := Term w) p).
    Proof.
      iIntros (e se) "He". iStopProof.
      unfold RNEnv, REnv, RInst, repₚ.
      crushPredEntails3; subst.
      now rewrite inst_tuple_pattern_match.
    Qed.

    Lemma RVal_tuple {σs} {v : Val (ty.tuple σs)} {w : World} {a : Env (Term w) σs} :
      ℛ⟦RVal (ty.tuple σs)⟧ v (term_tuple a) ⊣⊢ ℛ⟦REnv σs⟧ (envrec.to_env σs v) a.
    Proof.
      unfold RVal, REnv, RInst, repₚ.
      crushPredEntails3; subst.
      - now rewrite envrec.to_of_env.
      - now rewrite H0 envrec.of_to_env.
    Qed.

    Lemma refine_record_pattern_match_env {N R Δ} {p : RecordPat (recordf_ty R) Δ} {w : World}
      {e} {se : NamedEnv (Term w) (recordf_ty R)} :
      ℛ⟦RNEnv recordf (recordf_ty R)⟧ e se ⊣⊢
        ℛ⟦RNEnv N Δ⟧ (record_pattern_match_env p e) (record_pattern_match_env p se).
    Proof.
      unfold RNEnv, RInst, repₚ.
      crushPredEntails3; subst.
      - now rewrite inst_record_pattern_match.
      - rewrite inst_record_pattern_match in H0.
        apply (f_equal (record_pattern_match_env_reverse p)) in H0.
        now rewrite !record_pattern_match_env_inverse_left in H0.
    Qed.

    Lemma RVal_record {R} {w : World} {v : NamedEnv Val (recordf_ty R)} {a : NamedEnv (Term w) (recordf_ty R)} :
      ℛ⟦RNEnv recordf (recordf_ty R)⟧ v a ⊣⊢
       ℛ⟦RVal (ty.record R)⟧ (recordv_fold R v) (term_record R a).
    Proof.
      unfold RNEnv, RVal, RInst, repₚ.
      crushPredEntails3; subst; first done.
      apply (f_equal (recordv_unfold R)) in H0.
      now rewrite !recordv_unfold_fold in H0.
    Qed.

    Lemma RVal_invert_inl {σ τ} {v} {w : World} {sl : Term w σ} : 
      ℛ⟦RVal (ty.sum σ τ)⟧ v (term_inl sl) ⊢ ∃ (vl : Val σ), bi_pure (v = inl vl) ∗ ℛ⟦RVal σ⟧ vl sl.
    Proof.
      unfold RVal, RInst, repₚ, bi_pure; simpl.
      crushPredEntails3; subst.
      eexists. split; reflexivity.
    Qed.

    Lemma RVal_invert_inr {σ τ} {v} {w : World} {sl : Term w τ} : 
      ℛ⟦RVal (ty.sum σ τ)⟧ v (term_inr sl) ⊢ ∃ (vl : Val τ), bi_pure (v = inr vl) ∗ ℛ⟦RVal τ⟧ vl sl.
    Proof.
      unfold RVal, RInst, repₚ, bi_pure; simpl.
      crushPredEntails3; subst.
      eexists. split; reflexivity.
    Qed.

  End LRCompat.

  Import notations logicalrelation.notations logicalrelation iris.proofmode.tactics.
  Global Hint Extern 0 (environments.envs_entails _ (ℛ⟦ RUnit ⟧ _ _)) => iApply refine_unit : core.
End UnifLogicOn.