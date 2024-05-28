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
     Signature
     (* Shallow.Monads *)
     (* Symbolic.Monads *)
     Symbolic.Propositions
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
  (Import SIG  : Signature B).

  Definition Pred : TYPE := fun w => Valuation w -> Prop.
  
  Bind Scope pred_scope with Pred.

  Section Definitions.
    Import ModalNotations.
    Definition Tm (A : LCtx -> Type) : TYPE :=
      fun w => A w.
    
    Definition eqₚ {T : LCtx -> Type} {A : Type} {instTA : Inst T A} : ⊢ Tm T -> Tm T -> Pred :=
      fun w t1 t2 ι => (inst t1 ι = inst t2 ι)%type.
    #[global] Arguments eqₚ {T A _} [w] _ _ _/.
    
    Definition repₚ {T : LCtx -> Type} {A : Type} {instTA : Inst T A} : A -> ⊢ Tm T -> Pred :=
      fun t2 w t1 ι => (inst t1 ι = t2)%type.
    #[global] Arguments repₚ {T A _} _ [w] _ _/.
    
    Definition curval {w : World} : Valuation w -> Pred w :=
      fun ι1 ι2 => ι1 = ι2.
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

    #[export] Instance entails_rewriterelation : RewriteRelation (@entails w) := {}.

    (* #[export] Instance proper_bientails : *)
    (*   Proper (@bientails w ==> @bientails w ==> iff) bientails. *)
    (* Proof. crushPredEntails1. Qed. *)
    (* #[export] Instance proper_entails_bientails : *)
    (*   Proper ((≡@{Pred w}) ==> (≡@{Pred w}) ==> iff) entails. *)
    (* Proof. crushPredEntails1. Qed. *)
    #[export] Instance proper_entails_entails :
      Proper (Basics.flip (entails (w := w)) ==> (entails (w := w)) ==> Basics.impl) entails.
    Proof. crushPredEntails1. Qed.

  End RewriteRelations.
  #[global] Arguments bientails {w} (_ _)%P.
  #[global] Arguments entails {w} (_ _)%P.

  Module Import proofmode.

    Import iris.bi.interface.
    Import iris.bi.extensions.

    Definition empₚ {w} (ι : Valuation w) : Prop := True.
    Arguments empₚ {w} ι /.
    Definition sepₚ {w} (P Q : Pred w) (ι : Valuation w) : Prop := P ι /\ Q ι.
    Arguments sepₚ {w} P Q ι /.
    Definition wandₚ {w} (P Q : Pred w) (ι : Valuation w) : Prop := P ι -> Q ι.
    Arguments wandₚ {w} P Q ι /.
    Variant persistently {w} (P : Pred w) (ι : Valuation w) : Prop :=
      MkSubstly : P ι -> persistently P ι.

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
        (* | [ |- ∀ₚ _ ] => intro *)
        | [ |- wandₚ _ _ _ ] => intro
        | [ H : wandₚ _ _ _ |- _ ] => cbn in H
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
          bi_and P Q ι := P ι /\ Q ι;
          bi_or P Q ι := P ι \/ Q ι;
          bi_impl P Q ι := P ι -> Q ι;
          bi_forall A f ι :=  forall a, f a ι;
          bi_exist A f ι := exists a, f a ι;
          bi_sep := sepₚ;
          bi_wand := wandₚ;
          bi_persistently := persistently;
          bi_later := later;
        |}.
      - constructor; crushPredEntails2.
        apply H1; crushPredEntails2.
      - constructor; crushPredEntails2.
      - constructor; crushPredEntails2.
    Defined.

    Definition proprepₚ {T : LCtx -> Type} {instTA : InstProp T} : Prop -> forall w, Tm T w -> Pred w :=
      fun t2 w t1 => ((instprop t1 : Pred w) ∗-∗ bi_pure t2)%I.
    #[global] Arguments proprepₚ {T _} _ [w] _ _/.

    #[export] Instance persistent_pred {w} {P : Pred w} :
      derived_connectives.Persistent P.
    Proof. constructor. intros ι HP. now constructor. Qed.

    #[export] Instance affine_pred {w} {P : Pred w} :
      derived_connectives.Affine P.
    Proof. constructor. intros ι HP. now constructor. Qed.


    #[export] Instance pred_pure_forall {w} : BiPureForall (Pred w).
    Proof. constructor. crushPredEntails2. Qed.

  End proofmode.

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

    Lemma acc_pathcond {w1 w2} (ω : w2 ⊒ w1) :
      forall ι,  instprop (wco w1) ι -> instprop (wco w2) (inst (sub_acc ω) ι).
    Proof.
      intros.
      rewrite <-instprop_subst.
      now apply (ent_acc_sub ω ι H).
    Qed.

    Import iris.bi.interface.

    (* update: better/more standard names? *)
    Definition assuming {w1 w2} (ω : w2 ⊒ w1) : Pred w1 -> Pred w2 :=
      fun Rpast ι => forall (ιpast : Valuation w1), inst (sub_acc ω) ιpast = ι -> instprop (wco w1) ιpast -> Rpast ιpast.
    Definition knowing {w1 w2} (ω : w2 ⊒ w1) : Pred w1 -> Pred w2 :=
      fun Rpast ι => (exists (ιpast : Valuation w1), inst (sub_acc ω) ιpast = ι /\ instprop (wco w1) ιpast /\ Rpast ιpast)%type.
    Definition forgetting {w1 w2} (ω : w1 ⊒ w2) : Pred w1 -> Pred w2 :=
      fun Rfut ι => Rfut (inst (sub_acc ω) ι).
    Definition unconditionally {w} : (□ Pred) w -> Pred w :=
      fun P => (∀ {w2} (ω : w ⊒ w2), assuming ω (P w2 ω))%I.

    (* #[export] Instance knowing_params : *)
    (*   Params (@knowing) 3. Qed. *)

    #[export] Instance knowing_proper {w1 w2} {ω : Acc w1 w2} :
      Proper (entails ==> entails) (knowing ω).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_exists {w1 w2} {ω : Acc w1 w2} {A} (P : A -> Pred w2) :
      (∃ v, knowing ω (P v)) ⊣⊢ knowing ω (∃ v, P v).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_sepₚ {w1 w2} {ω : Acc w1 w2} (P1 P2 : Pred w2) :
      (knowing ω (P1 ∗ P2)) ⊢ knowing ω P1 ∗ knowing ω P2.
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma assuming_sepₚ {w1 w2} {ω : Acc w1 w2} (P1 P2 : Pred w2) :
      (assuming ω (P1 ∗ P2)) ⊣⊢ assuming ω P1 ∗ assuming ω P2.
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance assuming_proper {w1 w2} {ω : Acc w1 w2} :
      Proper (entails ==> entails) (assuming ω).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance assuming_proper_bientails {w1 w2} {ω : Acc w1 w2} :
      Proper (bientails ==> bientails) (assuming ω).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    #[export] Instance forgetting_proper {w1 w2} {ω : Acc w1 w2} :
      Proper (entails ==> entails) (forgetting ω).
    Proof.
      unfold forgetting.
      crushPredEntails3.
      apply (fromEntails _ _ H); last done.
      now apply acc_pathcond.
    Qed.

    #[export] Instance forgetting_proper_bientails {w1 w2} {ω : Acc w1 w2} :
      Proper (equiv ==> equiv) (forgetting ω).
    Proof.
      unfold forgetting.
      crushPredEntails3;
        (apply (fromBientails _ _ H); last done;
         now apply acc_pathcond).
    Qed.
    
    Lemma forgetting_forall {w1 w2} {ω : Acc w1 w2} {A} {P : A -> Pred w1} :
      (∀ v : A, forgetting ω (P v)) ⊣⊢ forgetting ω (∀ v : A, P v).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma forgetting_wand {w1 w2} {ω : Acc w1 w2} {P1 P2 : Pred w1} :
      (forgetting ω P1 -∗ forgetting ω P2) ⊣⊢ forgetting ω (P1 -∗ P2).
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma knowing_assuming {w1 w2} (ω : w2 ⊒ w1) {P Q} :
      knowing ω P ∗ assuming ω Q ⊢ knowing ω (P ∗ Q).
    Proof.
      unfold knowing, assuming.
      crushPredEntails3.
    Qed.

    Lemma knowing_pure {w1 w2} (ω : w2 ⊒ w1) {P} :
      knowing ω (bi_pure P) ⊢ bi_pure P.
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma knowing_forall {w1 w2} {ω : Acc w1 w2} {A} {P : A -> Pred w2} :
      knowing ω (∀ v : A, P v) ⊢ (∀ v : A, knowing ω (P v)).
    Proof.
      unfold knowing.
      crushPredEntails3.
    Qed.

    Lemma forgetting_pure {w1 w2} (ω : w2 ⊒ w1) {P} :
      forgetting ω (bi_pure P) ⊣⊢ bi_pure P.
    Proof.
      unfold forgetting.
      crushPredEntails3.
    Qed.

    Lemma assuming_pure {w1 w2} (ω : w2 ⊒ w1) {P} :
      bi_pure P ⊢ assuming ω (bi_pure P).
    Proof.
      unfold assuming.
      crushPredEntails3.
    Qed.

    Lemma forgetting_unconditionally {w1 w2} {ω : w2 ⊒ w1} (P : (□ Pred) w2) :
      forgetting ω (unconditionally P) ⊢ unconditionally (four P ω).
    Proof.
      unfold forgetting, unconditionally, assuming.
      crushPredEntails3.
      eapply H0; eauto using acc_pathcond.
      now rewrite <-H1, <-inst_subst, <-sub_acc_trans.
    Qed.

    Lemma forgetting_unconditionally_drastic {w1 w2} {ω : w2 ⊒ w1} (P : (□ Pred) w2) :
      forgetting ω (unconditionally P) ⊢ P _ ω.
    Proof.
      unfold forgetting, unconditionally, assuming.
      constructor.
      intros.
      now apply (H0 w1 ω ι).
    Qed.

    Lemma unconditionally_T {w} (P : (□ Pred) w) :
      unconditionally P ⊢ T P.
    Proof.
      unfold T, unconditionally, assuming.
      crushPredEntails3.
      eapply H0; try assumption.
      eapply inst_sub_id.
    Qed.

    Lemma eval `{Inst AT A} {w : World} (t : AT w) :
      ⊢ ∃ v, repₚ v (w := w) t.
    Proof. crushPredEntails3. now eexists. Qed.

    Lemma eval_prop `{InstProp AT} {w : World} (t : AT w) :
      ⊢ ∃ P, proprepₚ P (w := w) t.
    Proof. crushPredEntails3. now eexists. Qed.

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

    Lemma repₚ_antisym_left {T : LCtx -> Type} `{Inst T A} {a1 a2 : A} {w : World} {sa : T w} :
      ⊢ repₚ a1 sa -∗ repₚ a2 sa -∗ ⌜ a1 = a2 ⌝.
    Proof.
      crushPredEntails3. now subst.
    Qed.

    Lemma proprepₚ_triv {T : LCtx -> Type} `{InstProp T} {a : Prop} {w : World} {vt : T w}:
      (∀ ι : Valuation w, instprop vt ι <-> a) ->
      ⊢ proprepₚ a vt.
    Proof.
      unfold proprepₚ.
      crushPredEntails3.
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

    Lemma proprepₚ_cong {T1 : LCtx -> Type} `{InstProp T1}
      {T2 : LCtx -> Type} `{InstProp T2}
      {w : World} (fs : T1 w -> T2 w)
      {v1 : Prop} {vs1 : T1 w} :
      (∀ (ι : Valuation w) vs1, instprop (fs vs1) ι <-> instprop vs1 ι) ->
      proprepₚ v1 vs1 ⊢ proprepₚ v1 (fs vs1).
    Proof.
      crushPredEntails3.
    Qed.

    Lemma proprepₚ_cong₂ {T1 : LCtx -> Type} `{Inst T1 A1}
      {T2 : LCtx -> Type} `{Inst T2 A2}
      {T3 : LCtx -> Type} `{InstProp T3}
      (f : A1 -> A2 -> Prop) {w : World} (fs : T1 w -> T2 w -> T3 w)
      {v1 : A1} {vs1 : T1 w} {v2 : A2} {vs2 : T2 w} :
      (∀ (ι : Valuation w) vs1 vs2, instprop (fs vs1 vs2) ι <-> f (inst vs1 ι) (inst vs2 ι)) ->
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

    Lemma repₚ_elim_repₚ {T : LCtx -> Type} `{Inst T A} {a1 : A} (a2 : A) {w : World} {vt1 : T w} (vt2 : T w):
      (∀ ι : Valuation w, inst vt1 ι = a1 -> inst vt2 ι = a2) ->
      repₚ a1 vt1 ⊢ repₚ a2 vt2.
    Proof. now crushPredEntails3. Qed.


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
        
    Lemma forgetting_repₚ `{InstSubst AT, @SubstLaws AT _} {v w1 w2} {ω : Acc w1 w2}  (t : AT w1) :
      (repₚ v (persist t ω) ⊣⊢ forgetting ω (repₚ v t))%I.
    Proof.
      rewrite persist_subst.
      unfold forgetting, repₚ.
      constructor. split; rewrite inst_subst; auto using acc_pathcond.
    Qed.

    Lemma forgetting_proprepₚ `{InstPropSubst AT, @SubstLaws AT _} {v w1 w2} {ω : Acc w1 w2}  (t : AT w1) :
      (proprepₚ v (persist t ω) ⊣⊢ forgetting ω (proprepₚ v t))%I.
    Proof.
      unfold forgetting, proprepₚ, derived_connectives.bi_wand_iff.
      constructor.
      crushPredEntails3.
      - now apply H4, instprop_persist.
      - now apply instprop_persist.
      - now apply H4, instprop_persist.
      - now apply instprop_persist.
    Qed.

    Lemma assuming_refl {w} {P : Pred w} : assuming acc_refl P ⊣⊢ P.
    Proof.
      rewrite /assuming.
      crushPredEntails3.
      - apply H0; [apply inst_sub_id|done].
      - rewrite inst_sub_id in H1; now subst.
    Qed.

    Lemma knowing_refl {w} {P : Pred w} : knowing acc_refl P ⊣⊢ P.
    Proof.
      rewrite /knowing.
      crushPredEntails3.
      - rewrite inst_sub_id in H0. now subst.
      - now rewrite inst_sub_id.
    Qed.

    Lemma knowing_trans {w1 w2 w3} {ω12 : Acc w1 w2} {ω23 : Acc w2 w3} {P : Pred w3} :
      knowing (acc_trans ω12 ω23) P ⊣⊢ knowing ω12 (knowing ω23 P).
    Proof.
      rewrite /knowing.
      crushPredEntails3.
      - rewrite sub_acc_trans inst_subst in H0.
        exists (inst (sub_acc ω23) x).
        repeat split; try done.
        { now apply acc_pathcond. }
        now exists x.
      - rewrite sub_acc_trans inst_subst.
        now subst.
    Qed.

    Lemma assuming_trans {w1 w2 w3} {ω12 : Acc w1 w2} {ω23 : Acc w2 w3} {P : Pred w3} :
      assuming (acc_trans ω12 ω23) P ⊣⊢ assuming ω12 (assuming ω23 P).
    Proof.
      rewrite /assuming.
      crushPredEntails3.
      - rewrite sub_acc_trans inst_subst in H0.
        apply H0; last done.
        now rewrite H3.
      - rewrite sub_acc_trans inst_subst in H1.
        apply (H0 (inst (sub_acc ω23) ιpast)); try done.
        now apply acc_pathcond.
    Qed.

    Lemma forgetting_trans {w1 w2 w3} {ω12 : Acc w1 w2} {ω23 : Acc w2 w3} {P : Pred w1} :
      forgetting (acc_trans ω12 ω23) P ⊣⊢ forgetting ω23 (forgetting ω12 P).
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - now rewrite sub_acc_trans inst_subst in H0.
      - now rewrite sub_acc_trans inst_subst.
    Qed.

    Lemma forgetting_refl {w} {P : Pred w} : forgetting acc_refl P ⊣⊢ P.
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - now rewrite <-inst_sub_id.
      - now rewrite inst_sub_id.
    Qed.

    Lemma forgetting_refl' {w} {P : Pred w} (ω : w ⊒ w) :
      sub_acc ω = sub_id w ->
      forgetting ω P ⊣⊢ P.
    Proof.
      rewrite /forgetting.
      crushPredEntails3.
      - rewrite H in H1.
        now rewrite <-inst_sub_id.
      - now rewrite H inst_sub_id.
    Qed.

    Lemma forgetting_assuming {w1 w2} {ω : Acc w1 w2} {P : Pred w2} :
      forgetting ω (assuming ω P) ⊢ P.
    Proof.
      rewrite /forgetting /assuming.
      now crushPredEntails3.
    Qed.

    Lemma knowing_forgetting {w1 w2} {ω : Acc w1 w2} {P : Pred w1} :
      knowing ω (forgetting ω P) ⊢ P.
    Proof.
      rewrite /forgetting /knowing.
      crushPredEntails3.
      now rewrite <-H0.
    Qed.

    Lemma forgetting_knowing {w1 w2} {ω : Acc w1 w2} {P : Pred w2} :
      P ⊢ forgetting ω (knowing ω P).
    Proof.
      rewrite /forgetting /knowing.
      now crushPredEntails3.
    Qed.

    Lemma knowing_forgetting_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
      (H : IsIsomorphism ω ω') :
      P ⊣⊢ knowing ω (forgetting ω P).
    Proof.
      rewrite /forgetting /knowing.
      crushPredEntails3.
      - exists (inst (sub_acc ω') ι).
        rewrite wiso_there; intuition.
        now apply acc_pathcond.
      - now subst.
    Qed.

    Lemma assuming_forgetting_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
      (H : IsIsomorphism ω ω') :
      P ⊣⊢ assuming ω (forgetting ω P).
    Proof.
      rewrite /forgetting /assuming.
      crushPredEntails3.
      - now subst.
      - specialize (H1 (inst (sub_acc ω') ι)).
        rewrite wiso_there in H1; intuition.
        now apply H2, acc_pathcond.
    Qed.

    Lemma forgetting_knowing_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w2}
      (H : IsIsomorphism ω ω') :
      P ⊣⊢ forgetting ω (knowing ω P).
    Proof.
      rewrite /forgetting /knowing.
      crushPredEntails3.
      apply (f_equal (inst (sub_acc ω'))) in H1.
      rewrite !wiso_back in H1; intuition.
      now subst.
    Qed.

    Lemma knowing_knowing_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
      (H : IsIsomorphism ω ω') :
      knowing ω (knowing ω' P) ⊣⊢ P.
    Proof.
      unfold knowing.
      crushPredEntails3.
      - subst.
        now rewrite wiso_there.
      - exists (inst (sub_acc ω') ι).
        repeat split.
        + now apply wiso_there.
        + now apply acc_pathcond.
        + now exists ι.
    Qed.


    Lemma forgetting_knowing_iso2 {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w1}
      (H : IsIsomorphism ω ω') :
      knowing ω' P ⊣⊢ forgetting ω P.
    Proof.
      rewrite (forgetting_knowing_iso (P := (knowing ω' P)) H).
      now rewrite knowing_knowing_iso.
    Qed.

    Lemma assuming_forgetting {w1 w2} {ω : Acc w1 w2} {P : Pred w1} :
      P ⊢ assuming ω (forgetting ω P).
    Proof.
      rewrite /forgetting /assuming.
      crushPredEntails3.
      now rewrite H1.
    Qed.

    Lemma forgetting_assuming_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} {P : Pred w2}
      (iso : IsIsomorphism ω ω') :
      P ⊣⊢ forgetting ω (assuming ω P).
    Proof.
      rewrite /forgetting /assuming.
      crushPredEntails3.
      apply (f_equal (inst (sub_acc ω'))) in H1.
      rewrite !wiso_back in H1; intuition.
      now subst.
    Qed.

    Lemma cancel_forgetting_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} `{iso : IsIsomorphism ω ω'}
      {P Q : Pred w1} :
      (forgetting ω P ⊢ forgetting ω Q) -> P ⊢ Q.
    Proof.
      intros H.
      rewrite (knowing_forgetting_iso (P := P) iso) (knowing_forgetting_iso (P := Q) iso).
      now rewrite H.
    Qed.

    Lemma cancel_knowing_iso {w1 w2} {ω : Acc w1 w2} {ω' : Acc w2 w1} `{iso : IsIsomorphism ω ω'}
      {P Q : Pred w2} :
      (knowing ω P ⊢ knowing ω Q) -> P ⊢ Q.
    Proof.
      intros H.
      rewrite (forgetting_knowing_iso (P := P) iso)
        (forgetting_knowing_iso (P := Q) iso).
      now rewrite H.
    Qed.

    Lemma forgetting_assuming_adjoint {w1 w2} {ω : Acc w1 w2} {P Q} :
      (forgetting ω P ⊢ Q) <-> (P ⊢ assuming ω Q).
    Proof.
      rewrite /forgetting /assuming.
      split; crushPredEntails3.
      - subst; now apply H4.
      - apply (fromEntails _ _ H) with (inst (sub_acc ω) ι);
          auto using acc_pathcond.
    Qed.

    Lemma forgetting_knowing_adjoint {w1 w2} {ω : Acc w1 w2} {P Q} :
      (knowing ω P ⊢ Q) <-> (P ⊢ forgetting ω Q).
    Proof.
      rewrite /forgetting /assuming /knowing.
      split; crushPredEntails3.
      - apply (fromEntails _ _ H); auto using acc_pathcond.
        now exists ι.
      - now subst.
    Qed.

    Import iris.proofmode.modalities.
    Import iris.proofmode.classes.
    Import iris.proofmode.tactics.

    #[export] Instance fromExist_knowing {w1 w2} {A} {ω : Acc w1 w2} {P} {Φ : A -> Pred _}:
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

    #[export] Instance fromExist_assuming {w1 w2} {A} {ω : Acc w1 w2} {P} {Φ : A -> Pred _}:
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
      now rewrite /ElimModal /unconditionally assuming_refl.
    Qed.

    Class IntoAssuming {w1 w2} (ω : Acc w1 w2) (P : Pred w1) (Q : Pred w2) :=
      into_assuming : P ⊢ assuming ω Q.

    #[export] Instance into_assuming_default {w1 w2} {ω : Acc w1 w2} (P : Pred w1) :
      IntoAssuming ω P (forgetting ω P) | 10.
    Proof. unfold IntoAssuming. now apply assuming_forgetting. Qed.

    #[export] Instance into_assuming_assuming {w1 w2} {ω : Acc w1 w2} (P : Pred w2) :
      IntoAssuming ω (assuming ω P) P | 0.
    Proof. now unfold IntoAssuming. Qed.

    Lemma modality_mixin_assuming {w1 w2} {ω : Acc w1 w2} : modality_mixin (assuming ω) (MIEnvTransform (IntoAssuming ω)) (MIEnvTransform (IntoAssuming ω)).
    Proof.
      constructor; cbn; try done; rewrite /assuming; crushPredEntails3.
      destruct into_assuming as [HPQ].
      crushPredEntails3.
    Qed.

    Definition modality_assuming {w1 w2} (ω : Acc w1 w2) : modality (Pred w2) (Pred w1) :=
      Modality (assuming ω) modality_mixin_assuming.

    #[export] Instance fromModal_assuming {w1 w2} {ω : Acc w1 w2} {P} :
      FromModal True (modality_assuming ω) tt (assuming ω P) P.
    Proof.
      constructor; crushPredEntails3.
    Qed.

    Class IntoForgetting {w1 w2} (ω : Acc w1 w2) (P : Pred w2) (Q : Pred w1) :=
      into_forgetting : P ⊢ forgetting ω Q.

    #[export] Instance into_forgetting_default {w1 w2} {ω : Acc w1 w2} (P : Pred w2) :
      IntoForgetting ω P (knowing ω P) | 10.
    Proof. unfold IntoForgetting. now apply forgetting_knowing. Qed.

    #[export] Instance into_forgetting_forgetting {w1 w2} {ω : Acc w1 w2} (P : Pred w1) :
      IntoForgetting ω (forgetting ω P) P | 0.
    Proof. now unfold IntoForgetting. Qed.


    (* TODO: define typeclass FromForgetting to preserve other forgetting assumptions *)
    Lemma modality_mixin_forgetting {w1 w2} {ω : Acc w1 w2} : modality_mixin (forgetting ω) (MIEnvTransform (IntoForgetting ω)) (MIEnvTransform (IntoForgetting ω)).
    Proof.
      constructor; cbn; try done; rewrite /forgetting; crushPredEntails3.
      - destruct H as [H]. apply H; done.
      - apply H; last done. now apply acc_pathcond.
    Qed.

    Definition modality_forgetting {w1 w2} (ω : Acc w1 w2) : modality (Pred w1) (Pred w2) :=
      Modality (forgetting ω) modality_mixin_forgetting.

    #[export] Instance fromModal_forgetting {w1 w2} {ω : Acc w1 w2} {P} :
      FromModal True (modality_forgetting ω) tt (forgetting ω P) P.
    Proof.
      constructor; crushPredEntails3.
    Qed.

    Lemma knowing_acc_snoc_right {w b P} :
      knowing (@acc_snoc_right w b) P ⊣⊢ ∃ v, forgetting (acc_snoc_left' b (term_val _ v)) P.
    Proof.
      unfold knowing, forgetting.
      crushPredEntails3.
      - destruct (env.view x) as [ιp v].
        exists v.
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b v).
        rewrite inst_sub_id.
        rewrite inst_sub_wk1 in H0.
        now subst.
      - exists (env.snoc ι b x).
        change (env.snoc _ _ _) with (env.snoc (inst (sub_id w) ι) b x) in H0.
        rewrite inst_sub_id in H0.
        repeat split; eauto using inst_sub_wk1.
        now rewrite instprop_subst inst_sub_wk1.
    Qed.

    Lemma knowing_acc_subst_right {w : World} {x σ} `{xIn : (x∷σ ∈ w)%katamaran}
      {t : Term (w - x∷σ) σ} {P} :
      (knowing (acc_subst_right t) P : Pred w) ⊣⊢ 
        (eqₚ (term_var_in xIn) (subst t (sub_shift xIn)) ∗
           assuming (acc_subst_right t) P)%I.
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
      

    Lemma assuming_acc_snoc_let {w b P v} :
      assuming (@acc_snoc_right w b) P ⊢ assuming (@acc_let_right w b v) P.
    Proof.
      unfold assuming.
      now crushPredEntails3.
    Qed.

    Lemma forgetting_acc_snoc_left_repₚ {w1 w2 b} {ω : Acc w1 w2} {v} :
      ⊢ forgetting (acc_snoc_left ω b (term_val _ v)) (repₚ v term_var_zero).
    Proof.
      unfold forgetting.
      now crushPredEntails3.
    Qed.

    Lemma assuming_acc_snoc_right {w b P} :
      assuming (@acc_snoc_right w b) P ⊣⊢ ∀ v, forgetting (acc_snoc_left' b (term_val _ v)) P.
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

    Lemma assuming_acc_snoc_right_let {w b} {P : Pred (wsnoc w b)} :
      assuming (@acc_snoc_right w b) P ⊣⊢ ∀ v, forgetting (acc_let_left b v) P.
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
        change (P (env.snoc (inst (sub_id w) ι) b v)) in H0.
        now rewrite inst_sub_id in H0.
    Qed.

    Lemma assuming_acc_let_right {w b v P} :
      assuming (@acc_let_right w b v) P ⊣⊢ forgetting (acc_let_left b v) P.
    Proof.
      unfold assuming, forgetting.
      crushPredEntails3.
      - change (P (env.snoc (inst (sub_id w) ι) b v)).
        rewrite inst_sub_id.
        apply H0.
        + eapply inst_sub_wk1.
        + now rewrite instprop_subst inst_sub_wk1.
      - destruct (env.view ιpast) as [ι' v'].
        rewrite inst_sub_wk1 in H1; subst.
        change (P (env.snoc (inst (sub_id w) ι) b v')) in H0.
        now rewrite inst_sub_id in H0.
    Qed.

    Lemma assuming_acc_let_snoc {w b v P} :
      assuming (acc_let_left (w := w) b v) P ⊣⊢ (repₚ v term_var_zero -∗ forgetting acc_snoc_right P).
    Proof.
      unfold assuming, forgetting, repₚ.
      crushPredEntails3; destruct (env.view ι) as [ι v']; subst; cbn in *.
      - rewrite instprop_subst inst_sub_wk1 in H; subst.
        crushPredEntails3.
        rewrite inst_sub_wk1.
        apply H0; try done.
        f_equal; try done.
        now apply inst_sub_id.
      - rewrite inst_sub_wk1 in H0.
        change (env.map _ _) with (inst (sub_id w) ιpast) in H1.
        rewrite inst_sub_id in H1.
        destruct (proj1 (env.inversion_eq_snoc ιpast ι v v') H1) as [-> ->].
        now apply H0.
    Qed.

    Lemma entails_let_snoc_wkn {w b v} {P Q} :
      @entails (wsnoc w b) (repₚ v term_var_zero ∗ P)%I Q <-> @entails (wlet w b v) P Q.
    Proof.
      crushPredEntails3.
      - rewrite instprop_snoc in H0.
        crushPredEntails3.
        apply H3; crushPredEntails3.
      - now apply (fromEntails _ _ H).
    Qed.

    Lemma bi_sep_let_snoc_wkn {w b v} {P Q} :
      @bientails (wsnoc w b) (bi_sep (PROP := bi_pred (w := wlet w b v)) P Q)%I (bi_sep (PROP := bi_pred (w := wsnoc w b)) P Q)%I.
    Proof. crushPredEntails3. Qed.
    
    Lemma forgetting_acc_pathcondition_right_snoc {w : World}
      {C : PathCondition w} {b : Formula w} 
      {P : Pred (wpathcondition w (C ▻ b))} :
      (forgetting (acc_pathcondition_right w (C ▻ b)) P : Pred w) ⊣⊢ 
        forgetting (acc_pathcondition_right w C) (forgetting (acc_formula_right (w := wpathcondition w C) b) P).
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id.
      - now rewrite inst_sub_id in H0.
    Qed.

    Lemma assuming_acc_pathcondition_right
      {w : World} {sc : PathCondition w} {P : Pred w} :
      (instprop sc : Pred w) ∗ assuming (acc_pathcondition_right w sc) P ⊢ P.
    Proof.
      unfold assuming.
      crushPredEntails3.
      apply H1.
      - apply inst_sub_id.
      - now apply instprop_cat.
    Qed.

    
    Lemma forgetting_acc_pathcondition_right_sep {w : World} {P : Pred w} {C : PathCondition w}
      {Q : Pred (wpathcondition w C)} :
      (forgetting (acc_pathcondition_right w C) (P ∗ Q) : Pred w) ⊣⊢ 
        P ∗ forgetting (acc_pathcondition_right w C) Q.
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id in H0.
      - now rewrite inst_sub_id.
    Qed.
    
    Lemma forgetting_acc_pathcondition_right {w : World} {P : Pred w} {C : PathCondition w} :
      (forgetting (acc_pathcondition_right w C) P : Pred w) ⊣⊢ P.
    Proof.
      unfold forgetting, acc_pathcondition_right, wpathcondition; cbn.
      crushPredEntails3.
      - now rewrite inst_sub_id in H0.
      - now rewrite inst_sub_id.
    Qed.
      
    (* Lemma assuming_acc_subst_right_let  {w : World} x {σ} {xIn : x∷σ ∈ w} *)
    (*   (t : Term (w - x∷σ) σ) {P} : *)
    (*   assuming (acc_subst_right x t) P ⊣⊢ *)
    (*     eqₚ (term_var xIn) (subst (sub_wk1 xIn) t) ∗ *)
    (*     forgetting (acc_subst_left x) P. *)
  End SubstMod.

  Module logicalrelation.
    Import ModalNotations.
    Import iris.bi.interface.
    Class Rel (AT : TYPE) (A : Type) : Type :=
      MkRel { RSat : A -> (⊢ AT -> Pred)%modal }.
    Bind Scope rel_scope with Rel.

    #[global] Arguments MkRel [AT A] &.
    #[global] Arguments RSat {_ _} _ _ {w} _.
    (* We use the same script ℛ as in the paper. This encodes (ι,x,y) ∈ ℛ[_,_]
       from the paper as (ℛ ι x y), i.e. the types of the relation are
       implicit. *)
    #[local] Notation "ℛ⟦ R ⟧" := (RSat R%R) (format "ℛ⟦ R ⟧").

    
    (* This instance can be used for any (first-class) symbolic data that can be
       instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
    Definition RInst AT A {instA : Inst AT A} : Rel AT A :=
      MkRel repₚ.
    Arguments RInst _ _ {_}.

    (* huh? missing instance? *)
    #[export] Instance instprop_symprop : InstProp 𝕊 := fun Σ v ι => SymProp.safe v ι.

    Definition RInstPropIff AT {instA : InstProp AT} : Rel AT Prop :=
      MkRel proprepₚ.
    Arguments RInstPropIff _ {_}.

    #[export] Instance RBox {AT A} (RA : Rel AT A) : Rel (Box AT) A :=
      MkRel 
        (fun v w t => unconditionally (fun w2 ω => ℛ⟦ RA ⟧ v (t w2 ω))).

    #[export] Instance RImpl {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
      Rel (Impl AT BT) (A -> B) :=
      MkRel (fun fc w fs => ∀ a ta, ℛ⟦ RA ⟧ a ta -∗ ℛ⟦ RB ⟧ (fc a) (fs ta))%I.

    #[export] Instance RForall {𝑲}
      {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
      (RA : forall K, Rel (AT K) (A K)) :
      Rel (@SIG.Forall 𝑲 AT) (forall K : 𝑲, A K) :=
      MkRel (fun fc w fs => ∀ₚ K : 𝑲, ℛ⟦ RA K ⟧ (fc K) (fs K))%P.

    #[export] Instance RVal (σ : Ty) : Rel (fun Σ => Term Σ σ) (Val σ) :=
      RInst (fun Σ => Term Σ σ) (Val σ).

    #[export] Instance RNEnv (N : Set) (Δ : NCtx N Ty) : Rel _ _ :=
      RInst (fun Σ => NamedEnv (Term Σ) Δ) (NamedEnv Val Δ).
    #[export] Instance REnv (Δ : Ctx Ty) : Rel _ _ :=
        RInst (fun Σ : LCtx => Env (Term Σ) Δ) (Env Val Δ).
    #[export] Instance RUnit : Rel Unit unit := RInst Unit unit.

    #[export] Instance RPathCondition : Rel PathCondition Prop := RInstPropIff PathCondition.
    #[export] Instance RFormula : Rel Formula Prop := RInstPropIff Formula.

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
    #[export] Instance RConst A : Rel (Const A) A := RInst (Const A) A.

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
  End logicalrelation.

  Module Import ufl_notations.
    Import logicalrelation.
    Open Scope rel_scope.
    Notation "ℛ⟦ R ⟧" := (RSat R%R) (format "ℛ⟦ R ⟧").
    Notation "A -> B" := (RImpl A%R B%R) : rel_scope.
    Notation "□ᵣ A"    := (RBox A%R) (at level 9) : rel_scope.
    Notation "'∀ᵣ' x .. y , R " :=
      (RForall (fun x => .. (RForall (fun y => R)) ..))
        (at level 200, x binder, y binder, right associativity,
          format "'[  ' '[  ' ∀ᵣ  x  ..  y ']' ,  '/' R ']'")
        : rel_scope.
  End ufl_notations.

  Section ModalRel.
    Import logicalrelation ufl_notations iris.bi.interface notations ModalNotations.
    Lemma forgetting_RImpl {AT A BT B} {RA : Rel AT A} {RB : Rel BT B} {w1 w2} {ω : w1 ⊒ w2} {f sf} :
      forgetting ω (ℛ⟦ RImpl RA RB ⟧ f sf) ⊣⊢ (∀ a sa, forgetting ω (ℛ⟦ RA ⟧ a sa) -∗ forgetting ω (ℛ⟦ RB ⟧ (f a) (sf sa))).
    Proof.
      unfold RSat at 1; cbn -[RSat].
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
    Import ufl_notations.
    Import logicalrelation.
    (* Import ModalNotations. *)
    Import iris.proofmode.tactics.
    
    Lemma refine_unit {w} :
      ⊢ (ℛ⟦ RUnit ⟧ () () : Pred w).
    Proof. now crushPredEntails3. Qed.
    
    Lemma refine_nil {AT A} {R : Rel AT A} {w} :
      ⊢ ℛ⟦ RList R ⟧ nil (nil : list (AT w)).
    Proof.
      crushPredEntails3.
      constructor.
    Qed.

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
      crushPredEntails3.
      - induction H4; first done.
        now rewrite <-H4, <-IHRList'.
      - revert v H4. induction t; intros v H4; subst; repeat constructor.
        now apply IHt.
    Qed.

    Lemma refine_four {w1 w2} {ω : Acc w2 w1} {AT A} (RA : Rel AT A) :
      (⊢ ∀ (v__s : Box AT w2) v, (forgetting ω (ℛ⟦□ᵣ RA⟧ v v__s) → ℛ⟦□ᵣ RA⟧ v (four v__s ω)))%I.
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

    Lemma refine_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _} :
      forall (v : A) (w1 w2 : World) (ω : Acc w1 w2),
        ⊢ ∀ (t : AT w1), (forgetting ω (ℛ⟦RInst AT A⟧ v t) → ℛ⟦RInst AT A⟧ v (persist t ω))%I.
    Proof. 
      iIntros (v w1 w2 ω t) "Hvt".
      now iApply forgetting_repₚ.
    Qed.

    Lemma refine_formula_persist :
      forall (w1 w2 : World) (r12 : Acc w1 w2) (f : Formula w1) (p : Prop),
        ⊢ forgetting r12 (ℛ⟦RFormula⟧ p f) -∗ ℛ⟦RFormula⟧ p (persist f r12).
    Proof.
      iIntros (v w1 w2 ω t) "Hvt".
      now iApply forgetting_proprepₚ.
    Qed.

    Lemma refine_inst_subst {Σ} {T : LCtx -> Type} `{InstSubst T A} (vs : T Σ) {w : World} :
      ⊢ ℛ⟦ RInst (Sub Σ) (Valuation Σ) -> RInst T A ⟧ (inst vs) (subst vs : Sub Σ w -> T w)%I.
    Proof.
      crushPredEntails3.
      now rewrite inst_subst H4.
    Qed.

    Lemma refine_instprop_subst {Σ} {T : LCtx -> Type} `{InstPropSubst T}
      (vs : T Σ) {w : World} :
      ⊢ ℛ⟦ (RInst (Sub Σ) (Valuation Σ) -> RInstPropIff T) ⟧ (instprop vs) (subst vs : Sub Σ w -> T w)%I.
    Proof.
      crushPredEntails3; subst.
      - now rewrite <-instprop_subst.
      - now rewrite instprop_subst.
    Qed.

    Lemma refine_lift {AT A} `{InstLift AT A} {w : World} (a : A) :
      ⊢ ℛ⟦RInst AT A⟧ a (lift a : AT w).
    Proof. iApply lift_repₚ. Qed.

    Lemma refine_rinst_sub_initial {w : World} {ι : Valuation w}: 
      ℛ⟦RInst (Sub w) (Valuation w)⟧ ι (sub_id w) ι.
    Proof.
      apply inst_sub_id.
    Qed.
  End LRCompat.
End Pred.
