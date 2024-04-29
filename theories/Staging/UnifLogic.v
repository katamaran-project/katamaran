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
    change (@interface.bi_emp (@bi_pred _) ?ι) with (empₚ ι) in *;
    change (@interface.bi_wand (@bi_pred _) ?P ?Q ?ι) with (wandₚ P Q ι) in *;
    change (@interface.bi_entails (@bi_pred _) ?P ?Q) with (entails P Q) in *;
    change (@interface.bi_persistently (@bi_pred _) ?P ?ι) with (persistently P ι) in *;
    change (@interface.bi_or (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> P ι \/ Q ι) in *;
    change (@interface.bi_impl (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> P ι -> Q ι) in *;
    change (@derived_connectives.bi_iff (@bi_pred ?w) ?P ?Q ?ι) with (instprop (wco w) ι -> iff (P ι) (Q ι)) in *;
    change (@interface.bi_pure (@bi_pred _) ?P _) with P in *;
    change (@interface.bi_forall (@bi_pred _) ?A ?P) with (fun ι => forall a : A, P a ι) in *;
    change (@interface.bi_exist (@bi_pred _) ?A ?P) with (fun ι => exists a : A, P a ι) in *;
    unfold derived_connectives.bi_intuitionistically, derived_connectives.bi_affinely in *;
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
                            repeat (punfold_connectives; crushPredEntailsMatch1 || crushPredEntailsMatch2);
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
    Proof. crushPredEntails3; firstorder. Qed.
    Lemma exists_r {I : Type} {w} P (Q : I -> Pred w) :
      (exists x : I, P ⊢ₚ Q x) -> P ⊢ₚ (∃ₚ x : I, Q x).
    Proof. crushPredEntails3; firstorder. Qed.
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
      Admitted.
      (* Proof. crushPredEntails3. Qed. *)

      Lemma eqₚ_refl {w : World} (t : T w) : t =ₚ t ⊣⊢ₚ ⊤ₚ.
      Admitted.
      (* Proof. crushPredEntails3. Qed. *)

      Lemma eqₚ_sym {w : World} (s t : T w) : s =ₚ t ⊣⊢ₚ t =ₚ s.
      Admitted.
      (* Proof. crushPredEntails3. Qed. *)

      Lemma eqₚ_trans {w : World} (s t u : T w) : s =ₚ t /\ₚ t =ₚ u ⊢ₚ s =ₚ u.
      Admitted.
      (* Proof. crushPredEntails3. Qed. *)

    End Eq.
    #[global] Arguments eqₚ_trans {T A _ w} s t u.

    (* Lemma peq_ty_noconfusion {w : World} (t1 t2 : OTy w) : *)
    (*   t1 =ₚ t2 ⊣⊢ₚ *)
    (*   match t1 , t2 with *)
    (*   | oty.evar  _      , _                => t1 =ₚ t2 *)
    (*   | _                , oty.evar _       => t1 =ₚ t2 *)
    (*   | oty.bool         , oty.bool         => ⊤ₚ *)
    (*   | oty.func t11 t12 , oty.func t21 t22 => t11 =ₚ t21 /\ₚ t12 =ₚ t22 *)
    (*   | _                , _                => ⊥ₚ *)
    (*   end. *)
    (* Proof. destruct t1, t2; crushPredEntails3. Qed. *)

    (* Lemma eq_pair *)
    (*   {AT BT : OType} {A B : Type} {instA : Inst AT A} {instB : Inst BT B} *)
    (*   [w] (a1 a2 : AT w) (b1 b2 : BT w) : *)
    (*   (a1,b1) =ₚ (a2,b2) ⊣⊢ₚ ((a1 =ₚ a2) /\ₚ (b1 =ₚ b2)). *)
    (* Proof. *)
    (*   pred_unfold. intros ι; cbn. split. *)
    (*   - now injection 1. *)
    (*   - intros []. now f_equal. *)
    (* Qed. *)

    Section Subst.

      (* Lemma subst_eq {T : OType} {substT : Subst T} *)
      (*   {A : Type} {instTA : Inst T A} {instSubstTA : InstSubst T A} *)
      (*   {Θ : SUB} {w0 w1} (θ : Θ w0 w1) (t1 t2 : T w0) : *)
      (*   subst (t1 =ₚ t2) θ ⊣⊢ₚ subst t1 θ =ₚ subst t2 θ. *)
      (* Proof. *)
      (*   pred_unfold. unfold subst, subst_pred. intros ι. *)
      (*   now rewrite !inst_subst. *)
      (* Qed. *)

      (* Context {Θ : SUB}. *)

      (* We could define a SubstLaws instance for the Pred type, but that's
         requires functional extensionality. Instead, we provide similar
         lemmas that use bientailment instead of Leibniz equality and thus
         avoid functional extensionality. *)
      (* Lemma subst_pred_refl `{lkReflΘ : LkRefl Θ} [w] (P : Pred w) : *)
      (*   subst P refl ⊣⊢ₚ P. *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_pred_trans `{lktransΘ : LkTrans Θ} *)
      (*   {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (P : Pred w0) : *)
      (*   subst P (θ1 ⊙ θ2) ⊣⊢ₚ subst (subst P θ1) θ2. *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_and {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) : *)
      (*   subst (P /\ₚ Q) θ ⊣⊢ₚ subst P θ /\ₚ subst Q θ. *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_impl {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) : *)
      (*   subst (P ->ₚ Q) θ ⊣⊢ₚ (subst P θ ->ₚ subst Q θ). *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_wand {w0 w1} (θ : Θ w0 w1) (P Q : Pred w0) : *)
      (*   subst (interface.bi_wand P Q) θ ⊣⊢ₚ interface.bi_wand (subst P θ) (subst Q θ). *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_false {w0 w1} (θ : Θ w0 w1) : *)
      (*   subst ⊥ₚ θ ⊣⊢ₚ ⊥ₚ. *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_true {w0 w1} (θ : Θ w0 w1) : *)
      (*   subst ⊤ₚ θ ⊣⊢ₚ ⊤ₚ. *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_forall [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) : *)
      (*   subst (∀ₚ a : A, Q a) θ ⊣⊢ₚ (∀ₚ a : A, subst (Q a) θ). *)
      (* Proof. crushPredEntails3. Qed. *)
      (* Lemma subst_exists [A] [w0 w1] (θ : Θ w0 w1) (Q : A -> Pred w0) : *)
      (*   subst (∃ₚ a : A, Q a) θ ⊣⊢ₚ (∃ₚ a : A, subst (Q a) θ). *)
      (* Proof. crushPredEntails3. Qed. *)

      (* Lemma subst_tpb {w0 w1} (θ : Θ w0 w1) G (e : Exp) (t : OTy w0) (ee : OExp w0) : *)
      (*   subst (G |--ₚ e; t ~> ee) θ ⊣⊢ₚ *)
      (*   subst G θ |--ₚ e; subst t θ ~> subst ee θ. *)
      (* Proof. crushPredEntails3. Qed. *)

    End Subst.

  End Lemmas.

  (* Module Sub. *)
  (*   Import iris.bi.interface iris.bi.derived_laws.bi. *)
  (*   Import (hints) Par. *)
  (*   Section WithSubstitution. *)
  (*     Context {Θ : SUB}. *)

  (*     Definition wp {w0 w1} (θ : Θ w0 w1) (Q : Pred w1) : Pred w0 := *)
  (*       fun ι0 => exists (ι1 : Assignment w1), inst θ ι1 = ι0 /\ Q ι1. *)
  (*     Definition wlp {w0 w1} (θ : Θ w0 w1) (Q : Pred w1) : Pred w0 := *)
  (*       fun ι0 => forall (ι1 : Assignment w1), inst θ ι1 = ι0 -> Q ι1. *)

  (*     #[global] Arguments wp {_ _} _ _ ι0/. *)
  (*     #[global] Arguments wlp {_ _} _ _ ι0/. *)

  (*     #[export] Instance proper_wp_bientails {w0 w1} (θ : Θ w0 w1) : *)
  (*       Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ)) (wp θ). *)
  (*     Proof. firstorder. Qed. *)

  (*     #[export] Instance proper_wp_entails {w0 w1} (θ : Θ w0 w1) : *)
  (*       Proper ((⊢ₚ) ==> (⊢ₚ)) (wp θ). *)
  (*     Proof. firstorder. Qed. *)

  (*     #[export] Instance proper_wlp_bientails {w0 w1} (θ : Θ w0 w1) : *)
  (*       Proper ((⊣⊢ₚ) ==> (⊣⊢ₚ)) (wlp θ). *)
  (*     Proof. firstorder. Qed. *)

  (*     #[export] Instance proper_wlp_entails {w0 w1} (θ : Θ w0 w1) : *)
  (*       Proper ((⊢ₚ) ==> (⊢ₚ)) (wlp θ). *)
  (*     Proof. firstorder. Qed. *)

  (*     Lemma wp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} *)
  (*       {w} (Q : Pred w) : wp refl Q ⊣⊢ₚ Q. *)
  (*     Proof. *)
  (*       unfold wp; pred_unfold. intros ι; split. *)
  (*       - intros (ι' & Heq & HQ). now subst. *)
  (*       - intros HQ. exists ι. easy. *)
  (*     Qed. *)

  (*     Lemma wp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ} *)
  (*       {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q : *)
  (*       wp (θ1 ⊙ θ2) Q ⊣⊢ₚ wp θ1 (wp θ2 Q). *)
  (*     Proof. *)
  (*       unfold wp; pred_unfold. intros ι; split. *)
  (*       - intros (ι2 & Heq & HQ). eauto. *)
  (*       - intros (ι1 & Heq1 & ι2 & Heq2 & HQ). subst. eauto. *)
  (*     Qed. *)

  (*     Lemma wp_false {w0 w1} (θ : Θ w0 w1) : *)
  (*       wp θ ⊥ₚ ⊣⊢ₚ ⊥ₚ. *)
  (*     Proof. firstorder. Qed. *)

  (*     Lemma and_wp_l {w0 w1} (θ : Θ w0 w1) P Q : *)
  (*       wp θ P /\ₚ Q ⊣⊢ₚ wp θ (P /\ₚ subst Q θ). *)
  (*     Proof. *)
  (*       unfold wp; pred_unfold. split. *)
  (*       - intros [(ι1 & <- & HP) HQ]. eauto. *)
  (*       - intros (ι1 & <- & HP & HQ). eauto. *)
  (*     Qed. *)

  (*     Lemma and_wp_r {w0 w1} (θ : Θ w0 w1) (P : Pred w0) (Q : Pred w1) : *)
  (*       P /\ₚ wp θ Q ⊣⊢ₚ wp θ (subst P θ /\ₚ Q). *)
  (*     Proof. now rewrite and_comm and_wp_l and_comm. Qed. *)

  (*     Lemma wp_thick {thickΘ : Thick Θ} {lkThickΘ : LkThick Θ} *)
  (*       {w α} (αIn : world.In α w) (t : OTy (w - α)) (Q : Pred (w - α)) : *)
  (*       wp (thick α t) Q ⊣⊢ₚ oty.evar αIn =ₚ subst t (thin (Θ := Par) α) /\ₚ subst Q (thin (Θ := Par) α). *)
  (*     Proof. *)
  (*       unfold wp; pred_unfold. intros ι. split. *)
  (*       - intros (ι1 & Heq & HQ). subst. *)
  (*         now rewrite inst_thick env.remove_insert env.lookup_insert. *)
  (*       - intros [Heq HQ]. exists (env.remove α ι αIn). *)
  (*         now rewrite inst_thick -Heq env.insert_remove. *)
  (*     Qed. *)

  (*     Lemma wlp_refl {reflΘ : Refl Θ} {lkreflΘ : LkRefl Θ} *)
  (*       {w} (Q : Pred w) : wlp refl Q ⊣⊢ₚ Q. *)
  (*     Proof. *)
  (*       unfold wlp; pred_unfold. intros ι. split. *)
  (*       - intros HQ. auto. *)
  (*       - intros HQ ? <-. auto. *)
  (*     Qed. *)

  (*     Lemma wlp_trans {transR : Trans Θ} {lktransΘ : LkTrans Θ} *)
  (*       {w0 w1 w2} (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) Q : *)
  (*       wlp (θ1 ⊙ θ2) Q ⊣⊢ₚ wlp θ1 (wlp θ2 Q). *)
  (*     Proof. *)
  (*       unfold wlp; pred_unfold. intros ι. split. *)
  (*       - intros HQ ι1 Heq1 ι2 Heq2. subst; auto. *)
  (*       - intros HQ ι2 Heq. subst; eauto. *)
  (*     Qed. *)

  (*     Lemma wlp_true {w0 w1} (θ : Θ w0 w1) : *)
  (*       wlp θ ⊤ₚ ⊣⊢ₚ ⊤ₚ. *)
  (*     Proof. firstorder. Qed. *)

  (*     (* Lemma wlp_and {w0 w1} (θ : Θ w0 w1) P Q : *) *)
  (*     (*   wlp θ P /\ₚ wlp θ Q ⊣⊢ₚ wlp θ (P /\ₚ Q). *) *)
  (*     (* Proof. firstorder. Qed. *) *)

  (*     (* Lemma wp_or {w0 w1} (θ : Θ w0 w1) P Q : *) *)
  (*     (*   wp θ P \/ₚ wp θ Q ⊣⊢ₚ wp θ (P \/ₚ Q). *) *)
  (*     (* Proof. firstorder. Qed. *) *)

  (*     Lemma wp_mono {w0 w1} (θ : Θ w0 w1) P Q: *)
  (*       wlp θ (interface.bi_wand P Q) ⊢ₚ interface.bi_wand (wp θ P) (wp θ Q). *)
  (*     Proof. firstorder. Qed. *)

  (*     Lemma wlp_mono {w0 w1} (θ : Θ w0 w1) P Q : *)
  (*       wlp θ (interface.bi_wand P Q) ⊢ₚ interface.bi_wand (wlp θ P) (wlp θ Q). *)
  (*     Proof. firstorder. Qed. *)

  (*     Lemma entails_wlp {w0 w1} (θ : Θ w0 w1) P Q : *)
  (*       (subst P θ ⊢ₚ Q) <-> (P ⊢ₚ wlp θ Q). *)
  (*     Proof. *)
  (*       unfold wlp; pred_unfold. split; intros HPQ. *)
  (*       - intros ι0 HP ι1 <-. revert HP. apply HPQ. *)
  (*       - intros ι1 HP. now apply (HPQ (inst θ ι1)). *)
  (*     Qed. *)

  (*     Lemma entails_wp {w0 w1} (θ : Θ w0 w1) P Q : *)
  (*       (P ⊢ₚ subst Q θ) <-> (wp θ P ⊢ₚ Q). *)
  (*     Proof. *)
  (*       unfold wp; pred_unfold. split; intros HPQ. *)
  (*       - intros ι0 (ι1 & <- & HP). now apply HPQ. *)
  (*       - intros ι1 HP. apply (HPQ (inst θ ι1)). exists ι1. split; auto. *)
  (*     Qed. *)

  (*     Lemma wp_impl {w0 w1} (θ1 : Θ w0 w1) (P : Pred _) (Q : Pred _) : *)
  (*       (wp θ1 P ->ₚ Q) ⊣⊢ₚ wlp θ1 (P ->ₚ subst Q θ1). *)
  (*     Proof. *)
  (*       unfold wp, wlp; pred_unfold. intros ι0; split. *)
  (*       - intros H ι1 <- HP. apply H. now exists ι1. *)
  (*       - intros HPQ (ι1 & <- & HP). now apply HPQ. *)
  (*     Qed. *)

  (*     Lemma subst_wlp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) : *)
  (*       subst (wlp θ P) θ ⊢ₚ P. *)
  (*     Proof. firstorder. Qed. *)

  (*     (* Lemma subst_wp {w0 w1} {θ : Θ w0 w1} (P : Pred w1) : *) *)
  (*     (*   P ⊢ₚ subst (wp θ P) θ. *) *)
  (*     (* Proof. firstorder. Qed. *) *)

  (*     Lemma wlp_frame {w0 w1} (θ : Θ w0 w1) (P : Pred _) (Q : Pred _) : *)
  (*       P ->ₚ wlp θ Q ⊣⊢ₚ wlp θ (subst P θ ->ₚ Q). *)
  (*     Proof. *)
  (*       unfold wlp; pred_unfold. intros ι; split. *)
  (*       - intros H ι1 <- HP. now apply (H HP). *)
  (*       - intros H HP ι1 <-. apply H; auto. *)
  (*     Qed. *)

  (*   End WithSubstitution. *)
  (*   (* #[global] Opaque wp. *) *)
  (*   (* #[global] Opaque wlp. *) *)

  (*   Lemma intro_wp_step' {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ} *)
  (*     {w α} (P : Pred w) (Q : Pred (w ، α)) (t : Ty) : *)
  (*     (subst P step ⊢ₚ lift t =ₚ @oty.evar _ α world.in_zero ->ₚ Q) -> *)
  (*     (P ⊢ₚ wp (step (Θ := Θ)) Q). *)
  (*   Proof. *)
  (*     pred_unfold. intros H ι HP. set (ι1 := env.snoc ι α t). exists ι1. *)
  (*     specialize (H ι1). rewrite inst_step in H |- *; cbn in *. intuition. *)
  (*   Qed. *)

  (*   (* Better for iris proof mode. *) *)
  (*   Lemma intro_wp_step {Θ} {stepΘ : Step Θ} {lkStepΘ : LkStep Θ} *)
  (*     t {w α} (Q : Pred (w ، α)) : *)
  (*     wlp step (lift t =ₚ oty.evar world.in_zero ->ₚ Q) ⊢ₚ wp (step (Θ := Θ)) Q. *)
  (*   Proof. apply (intro_wp_step' t). now rewrite subst_wlp. Qed. *)

  (*   (* Lemma wp_split  {Θ : SUB} [w0 w1] (θ : Θ w0 w1) P : *) *)
  (*   (*   wp θ ⊤ₚ /\ₚ wlp θ P ⊢ₚ wp θ P. *) *)
  (*   (* Proof. now rewrite and_wp_l, subst_wlp, and_true_l. Qed. *) *)

  (*   Lemma wp_hmap `{LkHMap Θ1 Θ2} [w0 w1] (θ : Θ1 w0 w1) P : *)
  (*     wp (hmap θ) P ⊣⊢ₚ wp θ P. *)
  (*   Proof. *)
  (*     constructor. intros ι0; cbn. apply ex_iff_morphism. *)
  (*     intro ι1. now rewrite inst_hmap. *)
  (*   Qed. *)

  (*   Lemma wlp_hmap `{LkHMap Θ1 Θ2} [w0 w1] (θ : Θ1 w0 w1) P : *)
  (*     wlp (hmap θ) P ⊣⊢ₚ wlp θ P. *)
  (*   Proof. *)
  (*     constructor. intros ι0; cbn. apply all_iff_morphism. *)
  (*     intro ι1. now rewrite inst_hmap. *)
  (*   Qed. *)

  (* End Sub. *)

  (* Definition PBox {Θ} : ⊧ Box Θ Pred ⇢ Pred := *)
  (*   fun w Q => (∀ₚ w' (θ : Θ w w'), Sub.wlp θ (Q w' θ))%P. *)
  (* Notation "◼ Q" := (PBox Q%B) (at level 9, right associativity, format "◼ Q"). *)

  (* Section InstPred. *)
  (*   Import iris.bi.derived_laws iris.bi.interface. *)

  (*   (* A type class for things that can be interpreted as a predicate. *) *)
  (*   Class InstPred (A : OType) := *)
  (*     instpred : ⊧ A ⇢ Pred. *)
  (*   #[global] Arguments instpred {_ _ _}. *)

  (*   (* #[export] Instance instpred_option {A} `{ipA : InstPred A} : *) *)
  (*   (*   InstPred (Option A) := *) *)
  (*   (*   fun w o => wp_option o instpred. *) *)
  (*   #[export] Instance instpred_list {A} `{ipA : InstPred A} : *)
  (*     InstPred (List A) := *)
  (*     fun w => *)
  (*       fix ip xs {struct xs} := *)
  (*       match xs with *)
  (*       | nil       => ⊤ₚ *)
  (*       | cons y ys => instpred y /\ₚ ip ys *)
  (*       end%P. *)
  (*   #[local] Instance instpred_prod_ty : InstPred (OTy * OTy) := *)
  (*     fun w '(t1,t2) => eqₚ t1 t2. *)
  (*   #[export] Instance instpred_unit : InstPred Unit := *)
  (*     fun w _ => ⊤ₚ%P. *)
  (*   #[global] Arguments instpred_unit [w] _ /. *)

  (*   Lemma instpred_list_app {A} `{ipA : InstPred A} [w] (xs ys : List A w) : *)
  (*     instpred (xs ++ ys) ⊣⊢ₚ instpred xs /\ₚ instpred ys. *)
  (*   Proof. *)
  (*     induction xs; cbn. *)
  (*     - now rewrite and_true_l. *)
  (*     - rewrite -bi.and_assoc. now apply bi.and_proper. *)
  (*   Qed. *)

  (*   Class InstPredSubst A {ipA : InstPred A} {subA : Subst A} := *)
  (*     instpred_subst [Θ : SUB] {w0 w1} (θ : Θ w0 w1) (a : A w0) : *)
  (*       instpred (subst a θ) ⊣⊢ₚ subst (instpred a) θ. *)
  (*   #[global] Arguments InstPredSubst _ {_ _}. *)

  (*   #[export] Instance instpred_subst_list `{InstPredSubst A} : *)
  (*     InstPredSubst (List A). *)
  (*   Proof. *)
  (*     intros Θ w0 w1 θ xs. unfold subst, subst_list. *)
  (*     induction xs; cbn; [easy|]. now rewrite instpred_subst IHxs. *)
  (*   Qed. *)

  (*   #[local] Instance instpred_subst_prod_ty : InstPredSubst (OTy * OTy). *)
  (*   Proof. intros Θ w0 w1 θ [τ1 τ2]; cbn. now rewrite subst_eq. Qed. *)

  (* End InstPred. *)

  (* Lemma pno_cycle {w} (t1 t2 : OTy w) (Hsub : oty.OTy_subterm t1 t2) : *)
  (*   t1 =ₚ t2 ⊢ₚ ⊥ₚ. *)
  (* Proof. *)
  (*   constructor. intros ι Heq. apply (inst_subterm ι) in Hsub. *)
  (*   rewrite <- Heq in Hsub. now apply ty.no_cycle in Hsub. *)
  (* Qed. *)

  (* Lemma eqₚ_insert {w} (G1 G2 : OEnv w) (x : string) (t1 t2 : OTy w) : *)
  (*   G1 =ₚ G2 /\ₚ t1 =ₚ t2 ⊢ₚ *)
  (*   insert (M := OEnv w) x t1 G1 =ₚ insert (M := OEnv w) x t2 G2. *)
  (* Proof. pred_unfold. intros []. now f_equal. Qed. *)

  (* Lemma eq_func {w} (s1 s2 t1 t2 : OTy w) : *)
  (*   oty.func s1 s2 =ₚ oty.func t1 t2 ⊣⊢ₚ (s1 =ₚ t1) /\ₚ (s2 =ₚ t2). *)
  (* Proof. now rewrite peq_ty_noconfusion. Qed. *)

  (* #[export] Instance params_tpb : Params (@TPB) 1 := {}. *)
  (* #[export] Instance params_ifte : Params (@oexp.ifte) 1 := {}. *)
  (* #[export] Instance params_eqₚ : Params (@eqₚ) 4 := {}. *)
  (* #[export] Instance params_subst : Params (@subst) 4 := {}. *)

  (* Section PBoxModality. *)
  (*   Import iris.proofmode.tactics. *)

  (*   #[export] Instance elimpbox `{LkRefl Θ} (p : bool) *)
  (*     {w} (P : ◻Pred w) (Q : Pred w) : *)
  (*     ElimModal True p true ◼P (P w refl) Q Q. *)
  (*   Proof. *)
  (*     intros _. unfold PBox. cbn. iIntros "[#H1 H2]". iApply "H2". *)
  (*     destruct p; cbn; iSpecialize ("H1" $! w (refl (Refl := reflΘ))); *)
  (*       now erewrite Sub.wlp_refl. *)
  (*   Qed. *)

  (*   Lemma subst_pbox `{LkTrans Θ} [w] (Q : ◻Pred w) [w1] (θ1 : Θ w w1) : *)
  (*     (◼Q)[θ1] ⊢ₚ ◼(Q[θ1]). *)
  (*   Proof. *)
  (*     constructor; intros ι1 HQ w2 θ2 ι2 <-. *)
  (*     apply HQ. now rewrite inst_trans. *)
  (*   Qed. *)

  (* End PBoxModality. *)

  (* Section IntoSubst. *)

  (*   Context {Θ : SUB}. *)

  (*   Class IntoSubst `{Inst T A, Subst T} *)
  (*     [w0 w1] (θ : Θ w0 w1) (x : T w0) (y : T w1) : Prop := *)
  (*     into_subst : forall ι : Assignment w1, inst (subst x θ) ι = inst y ι. *)

  (*   #[export] Instance into_subst_default `{Inst T A, Subst T} *)
  (*     [w0 w1] (θ : Θ w0 w1) (t : T w0) : IntoSubst θ t (subst t θ) | 10. *)
  (*   Proof. easy. Qed. *)

  (*   (* #[export] Instance into_subst_subst `{LkTrans Θ, InstSubst T A} *) *)
  (*   (*   [w0 w1 w2] (θ1 : Θ w0 w1) (θ2 : Θ w1 w2) (t : T w0) : *) *)
  (*   (*   IntoSubst θ2 (subst t θ1) (subst t (trans θ1 θ2)) | 0. *) *)
  (*   (* Proof. intros ι. now rewrite !inst_subst, inst_trans. Qed. *) *)

  (*   #[export] Instance into_subst_lift {T A} {instTA : Inst T A} {liftTA : Lift T A} *)
  (*     {subT : Subst T} {instLiftTA : InstLift T A} {instSubTA : InstSubst T A} *)
  (*     [w0 w1] (θ : Θ w0 w1) (a : A) : *)
  (*     IntoSubst θ (lift a) (lift a) | 0. *)
  (*   Proof. intros ι. now rewrite inst_subst, !inst_lift. Qed. *)

  (*   #[export] Instance into_subst_insert *)
  (*     [w0 w1] (θ : Θ w0 w1) (G0 : OEnv w0) x (τ0 : OTy w0) G1 τ1 *)
  (*     (HG : IntoSubst θ G0 G1) (Hτ : IntoSubst θ τ0 τ1) : *)
  (*     IntoSubst θ (G0 ,, x ∷ τ0) (G1 ,, x ∷ τ1) | 0. *)
  (*   Proof. *)
  (*     intros ι1. specialize (HG ι1). specialize (Hτ ι1). *)
  (*     change_no_check (@gmap.gmap string _ _ (OTy ?w)) with (OEnv w). *)
  (*     rewrite subst_insert, !inst_insert. now f_equal. *)
  (*   Qed. *)

  (* End IntoSubst. *)

  (* Section WlpModality. *)

  (*   Import iris.proofmode.tactics. *)

  (*   Context {Θ : SUB} [w0 w1] (θ : Θ w0 w1). *)

  (*   Class IntoWlp (P : Pred w0) (Q : Pred w1) := *)
  (*     into_wlp : P ⊢ Sub.wlp θ Q. *)

  (*   #[export] Instance into_wlp_default (P : Pred w0) : *)
  (*     IntoWlp P (subst P θ) | 10. *)
  (*   Proof. unfold IntoWlp. now apply Sub.entails_wlp. Qed. *)

  (*   Definition modality_wlp_mixin : *)
  (*     modality_mixin (Sub.wlp θ) *)
  (*       (MIEnvTransform IntoWlp) *)
  (*       (MIEnvTransform IntoWlp). *)
  (*   Proof. firstorder. Qed. *)

  (*   Definition modality_wlp : modality bi_pred bi_pred := *)
  (*     Modality _ (modality_wlp_mixin). *)

  (*   #[export] Instance from_modal_wlp P : *)
  (*     FromModal True modality_wlp (Sub.wlp θ P) (Sub.wlp θ P) P. *)
  (*   Proof. firstorder. Qed. *)

  (*   #[export] Instance into_wlp_pbox `{LkTrans Θ} (P : ◻Pred w0) : *)
  (*     IntoWlp ◼P ◼(fun _ θ2 => P _ (θ ⊙ θ2)) | 0. *)
  (*   Proof. unfold IntoWlp. iIntros "H !>". now rewrite subst_pbox. Qed. *)

  (*   #[export] Instance into_wlp_tpb (G1 : OEnv w0) (e : Exp) (τ1 : OTy w0) *)
  (*     (ee1 : OExp w0) G2 τ2 ee2 (HG : IntoSubst θ G1 G2) *)
  (*     (Hτ : IntoSubst θ τ1 τ2) (Hee : IntoSubst θ ee1 ee2) : *)
  (*     IntoWlp (TPB G1 e τ1 ee1) (TPB G2 e τ2 ee2) | 0. *)
  (*   Proof. *)
  (*     constructor. intros ι0 HT ι1 <-. pred_unfold. *)
  (*     specialize (HG ι1). specialize (Hτ ι1). specialize (Hee ι1). *)
  (*     rewrite !inst_subst in HG, Hτ, Hee. congruence. *)
  (*   Qed. *)

  (*   #[export] Instance into_wlp_eqp `{InstSubst T A} *)
  (*     (x1 x2 : T w0) (y1 y2 : T w1) (Hxy1 : IntoSubst θ x1 y1) (Hxy2 :IntoSubst θ x2 y2) : *)
  (*     IntoWlp (eqₚ x1 x2) (eqₚ y1 y2) | 0. *)
  (*   Proof. *)
  (*     constructor. pred_unfold. intros ι0 Heq ι1 ?Heq; cbn. *)
  (*     specialize (Hxy1 ι1). specialize (Hxy2 ι1). *)
  (*     rewrite !inst_subst in Hxy1, Hxy2. congruence. *)
  (*   Qed. *)

  (*   #[export] Instance into_wlp_wlp (P : Pred w1) : *)
  (*     IntoWlp (Sub.wlp θ P) P | 0. *)
  (*   Proof. unfold IntoWlp. reflexivity. Qed. *)

  (* End WlpModality. *)

  (* #[global] Arguments IntoWlp {Θ} [w0 w1] θ P Q. *)
  (* #[global] Arguments into_wlp {Θ} [w0 w1] θ P Q {_}. *)
  (* #[global] Hint Mode IntoWlp + + + + - - : typeclass_instances. *)

  (* Import (hints) Par. *)

  (* Create HintDb predsimpl. *)
  (* #[export] Hint Rewrite (@subst_eq OEnv _ _ _ _) (@subst_eq OTy _ _ _ _) *)
  (*   (@subst_refl OEnv _ _) (@subst_refl OTy _ _) (@subst_trans OEnv _ _) *)
  (*   (@subst_trans OTy _ _) @Sub.wlp_refl @Sub.wlp_trans @Sub.wlp_true *)
  (*   @Sub.wp_false @Sub.wp_refl @Sub.wp_trans @and_false_l @and_false_r *)
  (*   @and_true_l @and_true_r @eq_func @eqₚ_refl @impl_and @impl_false_l *)
  (*   @impl_true_l @impl_true_r @lk_refl @lk_step @lk_trans @subst_and @subst_false *)
  (*   @subst_pred_refl @subst_pred_trans @subst_tpb @subst_true @trans_refl_r *)
  (*   : predsimpl. *)
  (* Ltac predsimpl := *)
  (*   repeat *)
  (*     (try (progress cbn); unfold _4; *)
  (*      change_no_check (@gmap.gmap string _ _ (OTy ?w)) with (OEnv w) in *; *)
  (*      repeat *)
  (*        match goal with *)
  (*        | |- Sub.wp ?θ _ ⊣⊢ₚ Sub.wp ?θ _ => apply Sub.proper_wp_bientails *)
  (*        | |- Sub.wlp ?θ _ ⊣⊢ₚ Sub.wlp ?θ _ => apply Sub.proper_wlp_bientails *)
  (*        end; *)
  (*      try easy; repeat rewrite_db predsimpl; auto 1 with typeclass_instances; *)
  (*      repeat *)
  (*        match goal with *)
  (*        | |- context[@subst ?A ?I ?Θ ?w0 ?x ?w1 ?θ] => *)
  (*            is_var x; generalize (@subst A I Θ w0 x w1 θ); clear x; intros x; *)
  (*            try (clear w0 θ) *)
  (*        | |- context[@lk ?Θ (?w0 ، ?α) ?w1 ?θ ?α world.in_zero] => *)
  (*            is_var θ; *)
  (*            generalize (@lk Θ (w0 ، α) w1 θ α world.in_zero); *)
  (*            clear θ w0; intros ?t *)
  (*        end). *)

End Pred.
