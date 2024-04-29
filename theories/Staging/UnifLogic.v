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
     (* Shallow.Monads *)
     (* Symbolic.Monads *)
     (* Symbolic.Propositions *)
     (* Symbolic.Solver *)
     Symbolic.Worlds
     (* Syntax.Assertions *)
     (* Syntax.Chunks *)
     (* Syntax.Formulas *)
     Syntax.Predicates
     .
From iris Require bi.derived_connectives bi.interface proofmode.tactics.

Declare Scope pred_scope.
Delimit Scope pred_scope with P.

Module Pred
  (Import B : Base)
  (Import PK : PredicateKit B)
  (Import WR : WorldsMixin B PK).

  Definition Pred : TYPE := fun w => Valuation w -> Prop.
  
  Bind Scope pred_scope with Pred.

  Section Definitions.
    Import ModalNotations.
    Definition Tm (A : LCtx -> Type) : TYPE :=
      fun w => A w.
    
    Definition eqₚ {T : LCtx -> Type} {A : Type} {instTA : Inst T A} : ⊢ Tm T -> Tm T -> Pred :=
      fun w t1 t2 ι => (instprop (wco w) ι -> inst t1 ι = inst t2 ι)%type.
    #[global] Arguments eqₚ {T A _} [w] _ _ _/.
    
  End Definitions.
  
  Section EntailmentDefinitions.

    Context {w : World}.

    Record bientails (P Q : Pred w) : Prop :=
      MkBientails { fromBientails : forall ι, instprop (wco w) ι -> P ι <-> Q ι }.
    Record entails (P Q : Pred w) : Prop :=
      MkEntails { fromEntails : forall ι, instprop (wco w) ι -> P ι -> Q ι }.

    #[export] Instance pred_equiv : Equiv (Pred w) := bientails.

  End EntailmentDefinitions.

  Ltac crushPredEntailsMatch1 :=
    match goal with
    | [ H : ?P /\ ?Q |- _ ] => destruct H
    | [ H : ?P \/ ?Q |- _ ] => destruct H
    | [ H: entails ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromEntails x y H ι Hpc); clear H)
    | [ H: equiv ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromBientails x y H ι Hpc); clear H)
    | [ H: bientails ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromBientails x y H ι Hpc); clear H)
    end.
  Ltac crushPredEntails1 := repeat constructor; intros; cbn in *; repeat crushPredEntailsMatch1; intuition.
  
  Section RewriteRelations.
    Context {w : World}.
    
    #[export] Instance pred_equivalence : Equivalence (≡@{Pred w}).
    Proof. crushPredEntails1. Qed.

    #[export] Instance preorder_entails : RelationClasses.PreOrder (entails (w := w)).
    Proof. crushPredEntails1. Qed.
    #[export] Instance subrelation_bientails_entails :
      subrelation (≡@{Pred w}) entails.
    Proof. crushPredEntails1. Qed.
    #[export] Instance subrelation_bientails_flip_entails :
      subrelation (≡@{Pred w}) (Basics.flip entails).
    Proof. crushPredEntails1. Qed.

    (* #[export] Instance proper_bientails : *)
    (*   Proper (bientails ==> bientails ==> iff) bientails. *)
    (* Proof. intuition. Qed. *)
    #[export] Instance proper_entails_bientails :
      Proper ((≡@{Pred w}) ==> (≡@{Pred w}) ==> iff) entails.
    Proof. crushPredEntails1. Qed.
    #[export] Instance proper_entails_entails :
      Proper (Basics.flip (entails (w := w)) ==> (entails (w := w)) ==> Basics.impl) entails.
    Proof. crushPredEntails1. Qed.

  End RewriteRelations.
  #[global] Arguments bientails {w} (_ _)%P.
  #[global] Arguments entails {w} (_ _)%P.

  Module Import proofmode.

    Import iris.bi.interface.

    Variant empₚ {w} (ι : Valuation w) : Prop :=
      MkEmp : empₚ ι.
    Variant sepₚ {w} (P Q : Pred w) (ι : Valuation w) : Prop :=
      MkSep : instprop (wco w) ι -> P ι -> Q ι -> sepₚ P Q ι.
    Variant wandₚ {w} (P Q : Pred w) (ι : Valuation w) : Prop :=
      MkWand : (instprop (wco w) ι -> P ι -> Q ι) -> wandₚ P Q ι.
    Variant persistently {w} (P : Pred w) (ι : Valuation w) : Prop :=
      MkSubstly : instprop (wco w) ι -> P ι -> persistently P ι.

    #[export] Instance ofe_dist_pred {w} : ofe.Dist (Pred w) :=
      ofe.discrete_dist.

    (* Iris defines [bi_later_mixin_id] for BI algebras without later. However,
       the identity function as later still causes some later-specific
       typeclasses to be picked. We just define our own trivial modality and
       mixin to avoid that. *)
    Variant later {w} (P : Pred w) (ι : Valuation w) : Prop :=
      MkLater : P ι -> later P ι.

    (* Note domi: This tactic is defined specifically to prove bi_pred below because firstorder enters a rabbit hole somewhere.
       Note: order of matches is important.
     *)
    Ltac crushPredEntailsMatch2 :=
        match goal with
        | [ |- True ] => constructor
        | [ H : dist _ _ _ |- _ ] => cbv in H
        | [ H : ?P |- ?P \/ _ ] => left
        | [ H : ?P |- _ \/ ?P ] => right
        | [ |- iff _ _ ] => split
        | [ |- _ -> _ ] => intro
        | [ |- _ /\ _ ] => split
        | [ |- forall P, _ ] => intro
        | [ H1: instprop ?pc ?ι -> ?Q, H2 : instprop ?pc ?ι |- _ ] => specialize (H1 H2)
        | [ |- Reflexive _] => intro
        | [ |- Transitive _] => intro
        | [ |- PreOrder _] => constructor
        | [ |- entails _ _] => constructor
        | [ |- bientails _ _] => constructor
        | [ |- equiv _ _] => constructor
        | [ H : ?H |- ?H ] => assumption
        | [ H1 : ?P1 -> ?P2, H2: ?P1  |- ?P2 ] => apply (H1 H2)
        | [ H : ?H1 -> ?H2 |- ?H2 ] => apply H
        | [ H : ?H1 <-> ?H2 |- ?H2 ] => apply (proj1 H); clear H
        | [ H : ?H1 <-> ?H2 |- ?H1 ] => apply (proj2 H); clear H
        | [ H : ?P1 <-> ?P2, H2 : ?P1 |- _ ] => apply (proj1 H) in H2; clear H
        | [ H : ?P1 <-> ?P2, H2 : ?P2 |- _ ] => apply (proj2 H) in H2; clear H
        | [ |- Proper _ _ ] => intro; intros
        | [ |- dist _ ?P ?Q ] => change (equiv P Q)
        | [ |- respectful _ _ ?P ?Q ] => intro; intro; intro
        | [ H1 : pointwise_relation ?A _ _ _, H2: ?A |- _ ] => specialize (H1 H2)
        | [ H1 : (forall (a : ?A), _), H2: ?A |- _ ] => specialize (H1 H2)
        | [ H1 : (exists (a : ?A), _) |- _ ] => destruct H1
        | [ a : ?A |- exists (a : ?A), _ ] => exists a
        | [ H : sepₚ _ _ _ |- _ ] => destruct H
        | [ |- sepₚ _ _ _ ] => split
        | [ |- eqₚ ?t1 ?t2 ?ι ] => intro
        | [ |- wandₚ _ _ _ ] => constructor; intros
        | [ H : wandₚ _ _ _ |- _ ] => destruct H; cbn in H
        | [ H : (fun x => _) _ |- _ ] => cbn in H
        | [ |- True ] => trivial
        | [ |- empₚ _ ] => constructor
        | [ |- persistently _ _ ] => constructor
        | [ H: persistently _ _ |- _ ] => destruct H
        | [ |- later _ _ ] => constructor
        | [ H: later _ _ |- _ ] => destruct H
        | [ |- later (λ _ , False) _ ∨ _ ] => right
        end.
    Ltac crushPredEntails2 := cbn; intros; cbn in *; repeat (crushPredEntailsMatch1 || crushPredEntailsMatch2); intuition.

    Canonical bi_pred {w : World} : bi.
    Proof.
      refine
        {| bi_car := Pred w;
          bi_entails := entails;
          bi_emp := empₚ;
          bi_pure P _ := P;
          bi_and P Q ι := instprop (wco w) ι -> P ι /\ Q ι;
          bi_or P Q ι := instprop (wco w) ι -> P ι \/ Q ι;
          bi_impl P Q ι := instprop (wco w) ι -> P ι -> Q ι;
          bi_forall A f ι := instprop (wco w) ι -> forall a, f a ι;
          bi_exist A f ι := instprop (wco w) ι -> exists a, f a ι;
          bi_sep := sepₚ;
          bi_wand := wandₚ;
          bi_persistently := persistently;
          bi_later := later;
        |}.
      constructor; crushPredEntails2.
      constructor; crushPredEntails2.
      constructor; crushPredEntails2.

    Defined.

    #[export] Instance persistent_pred {w} {P : Pred w} :
      derived_connectives.Persistent P.
    Proof. constructor. intros ι HP. now constructor. Qed.

    #[export] Instance affine_pred {w} {P : Pred w} :
      derived_connectives.Affine P.
    Proof. constructor. intros ι HP. now constructor. Qed.

  End proofmode.

  Ltac punfold_connectives :=
    change (@interface.bi_and (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> P ι /\ Q ι) in *;
    change (@interface.bi_sep (@bi_pred _) ?P ?Q ?ι) with (sepₚ P Q ι) in *;
    change (@eqₚ ?T ?A ?instTA ?w ?t1 ?t2 ?ι) with (instprop (wco w) ι -> inst t1 ι = inst t2 ι) in *;
    change (@interface.bi_emp (@bi_pred _) ?ι) with (empₚ ι) in *;
    change (@interface.bi_wand (@bi_pred _) ?P ?Q ?ι) with (wandₚ P Q ι) in *;
    change (@interface.bi_entails (@bi_pred _) ?P ?Q) with (entails P Q) in *;
    change (@interface.bi_persistently (@bi_pred _) ?P ?ι) with (persistently P ι) in *;
    change (@interface.bi_or (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> P ι \/ Q ι) in *;
    change (@interface.bi_impl (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> P ι -> Q ι) in *;
    change (@derived_connectives.bi_iff (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> iff (P ι) (Q ι)) in *;
    change (@interface.bi_pure (@bi_pred _) ?P _) with P in *;
    change (@interface.bi_forall (@bi_pred ?w) ?A ?P) with (fun ι => instprop (wco w) ι -> forall a : A, P a ι) in *;
    change (@interface.bi_exist (@bi_pred ?w) ?A ?P) with (fun ι => instprop (wco w) ι -> exists a : A, P a ι) in *;
    unfold derived_connectives.bi_intuitionistically, derived_connectives.bi_affinely, interface.bi_emp_valid in *;
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

  Lemma bientails_unfold [w] (P Q : Pred w) :
    (P ⊣⊢ₚ Q) <-> forall ι, instprop (wco w) ι -> P ι <-> Q ι.
  Proof. crushPredEntails3. Qed.
  Lemma entails_unfold [w] (P Q : Pred w) :
    (P ⊢ₚ Q) <-> forall ι, instprop (wco w) ι -> P ι -> Q ι.
  Proof. crushPredEntails3. Qed.
  Lemma sep_unfold w (P Q : Pred w) :
    ∀ ι, instprop (wco w) ι -> interface.bi_sep P Q ι ↔ (P ι /\ Q ι).
  Proof. crushPredEntails3. Qed.
  Lemma wand_unfold w (P Q : Pred w) :
    ∀ ι, instprop (wco w) ι -> interface.bi_wand P Q ι ↔ (P ι → Q ι).
  Proof. crushPredEntails3. Qed.
  Lemma intuitionistically_unfold w (P : Pred w) :
    ∀ ι, instprop (wco w) ι -> @derived_connectives.bi_intuitionistically _ P ι <-> P ι.
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

    (* Lemma forall_l {I : Type} {w} (P : I -> Pred w) Q : *)
    (*   (exists x : I, P x ⊢ₚ Q) -> (∀ x : I, P x)%I ⊢ₚ Q. *)
    (* Proof. crushPredEntails3. firstorder. Qed. *)
    (* Lemma forall_r {I : Type} {w} P (Q : I -> Pred w) : *)
    (*   (P ⊢ₚ (∀ₚ x : I, Q x)) <-> (forall x : I, P ⊢ₚ Q x). *)
    (* Proof. crushPredEntails3. firstorder. Qed. *)

    Lemma exists_l {I : Type} {w} (P : I -> Pred w) (Q : Pred w) :
      (forall x : I, P x ⊢ₚ Q) -> (∃ₚ x : I, P x) ⊢ₚ Q.
    Proof. crushPredEntails3. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (exists x : I, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x : I, Q x).
    Proof. crushPredEntails3. Qed.
    #[global] Arguments exists_r {I w P Q} _.

    Lemma wand_is_impl [w] (P Q : Pred w) : (P -∗ Q)%I ⊣⊢ₚ (P ->ₚ Q).
    Proof. crushPredEntails3. Qed.

    Lemma pApply {w} {P Q R : Pred w} : P ⊢ₚ Q -> Q ⊢ₚ R -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

    Lemma pApply_r {w} {P Q R : Pred w} : Q ⊢ₚ R -> P ⊢ₚ Q -> P ⊢ₚ R.
    Proof. now transitivity Q. Qed.

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

    Lemma acc_pathcond {w1 w2} (ω : w2 ⊒ w1) :
      forall ι,  instprop (wco w1) ι -> instprop (wco w2) (inst (sub_acc ω) ι).
    Proof.
      intros.
      rewrite <-instprop_subst.
      now apply (ent_acc_sub ω ι H).
    Qed.


    (* update: one of these requires an assumption of the path condition... *)
    Definition before {w1 w2} (ω : w2 ⊒ w1) : Pred w1 -> Pred w2 :=
      fun Rpast ι => forall ιpast, inst (sub_acc ω) ιpast = ι -> Rpast ιpast.
    Definition after {w1 w2} (ω : w2 ⊒ w1) : Pred w2 -> Pred w1 :=
      fun Rfut ι => Rfut (inst (sub_acc ω) ι).
  End SubstMod.

  Section LogicalRelation.
    Import logicalrelation.
    Import ModalNotations.
    
    Definition Related {AT A} (R : Rel AT A) : ⊢ AT -> Const A -> Pred :=
      fun w t v ι => (instprop (wco w) ι -> RSat R ι t v)%type.

  End LogicalRelation.

  Module Import ufl_notations.
    Import logicalrelation.
    Open Scope rel_scope.
    Notation "ℛ⟦ R ⟧" := (Related R%R) (format "ℛ⟦ R ⟧").
    Notation "A -> B" := (RImpl A%R B%R) : rel_scope.
    Notation "□ᵣ A"    := (RBox A%R) (at level 9) : rel_scope.
    Notation "'∀ᵣ' x .. y , R " :=
      (RForall (fun x => .. (RForall (fun y => R)) ..))
        (at level 200, x binder, y binder, right associativity,
          format "'[  ' '[  ' ∀ᵣ  x  ..  y ']' ,  '/' R ']'")
        : rel_scope.
  End ufl_notations.

  Section LRCompat.
    Import notations.
    Import ufl_notations.
    Import logicalrelation.
    (* Import ModalNotations. *)
    Import iris.proofmode.tactics.
    

    Lemma refine_four {w1 w2} {ω : Acc w2 w1} {AT A} (RA : Rel AT A) :
      (⊢ ∀ (v__s : Box AT w2) v, (after ω (ℛ⟦□ᵣ RA⟧ w2 v__s v) ->ₚ ℛ⟦RBox RA⟧ w1 (four v__s ω) v))%P.
    Proof.
      constructor.
      intros ι2 Hpc _ _ v__s _ v _ Htv _ w0 r01 ι0 -> Hpc0.
      unfold four, after in *.
      unfold RBox, Related in Htv. cbn in Htv.
      apply Htv.
      - now apply acc_pathcond.
      - now rewrite <-inst_subst, sub_acc_trans.
      - done.
    Qed.


End Pred.
