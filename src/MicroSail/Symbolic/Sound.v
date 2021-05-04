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

From Coq Require Import
     Bool.Bool
     Program.Equality
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     Symbolic.Mutator.
From MicroSail Require Import
     SemiConcrete.Mutator
     SemiConcrete.Outcome
     SemiConcrete.Sound.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).
  Module MUT := Mutators termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic termkit progkit assertkit contractkit.
  Import LOG.
  Module SCMUT := SemiConcrete.Sound.Soundness termkit progkit assertkit contractkit.
  Import SCMUT.
  Import SCMUT.MUT.

  Local Notation "[ ι ] x == y" := (inst ι x = inst ι y) (at level 50).
  (* Avoid some Prop <-> Type confusion. *)
  Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

  Global Instance inst_symbolicstate {Γ} : Inst (SymbolicState Γ) (SCState Γ) :=
    {| inst Σ ι '(MkSymbolicState δ h) := MkSCState (inst ι δ) (inst ι h);
       lift Σ '(MkSCState δ h) := MkSymbolicState (lift δ) (lift h);
    |}.

  Global Instance instlaws_symbolicState {Γ} : InstLaws (SymbolicState Γ) (SCState Γ).
  Proof.
    constructor.
    - intros ? ? []; cbn; now rewrite ?inst_lift.
    - intros ? ? ? ? []; cbn; now rewrite ?inst_subst.
  Qed.

  (* Read: If ς is equivalent to t in ι, then substituting t for ς is equivalent to the identity. *)
  Lemma inst_single_shift {Σ ς σ} (ςInΣ : ς :: σ ∈ Σ) (t : Term (Σ - (ς :: σ)) σ) ι :
    [ ι ] term_var ς == subst (sub_shift ςInΣ) t ->
    [ ι ] sub_comp (sub_single ςInΣ t) (sub_shift ςInΣ) == sub_id _.
  Proof.
    unfold sub_comp.
    rewrite ?inst_subst.
    rewrite inst_sub_id.
    rewrite ?inst_sub_shift.
    cbn. intros H.
    now apply inst_sub_single.
  Qed.

  Lemma subst_sub_id_right {Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
    subst ζ (sub_id _) = ζ.
  Proof. exact (sub_comp_id_left ζ). Qed.

  Lemma inst_record_pattern_match {Δ__R : NCtx 𝑹𝑭 Ty} {Σ Δ : LCtx}
    (ι : SymInstance Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ__R) :
    inst ι (record_pattern_match p ts) = record_pattern_match p (inst ι ts).
  Proof.
    unfold inst at 1; cbn.
    induction p; cbn.
    - reflexivity.
    - destruct (snocView ts); cbn.
      f_equal. apply IHp.
  Qed.

  Section Entailment.

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

  End Entailment.
  Infix "⊢" := (@entails _) (at level 80, no associativity).
  Infix "⊢f" := (@entails_formula _) (at level 80, no associativity).
  Notation "pc ⊢ a0 == a1" :=
    (entails_eq pc a0 a1)
    (at level 80, a0 at next level, no associativity).

  Section SemiConcreteWP.

    Definition scmut_wp {Γ1 Γ2 A}
      (m : SCMut Γ1 Γ2 A)
      (POST : A -> SCState Γ2 -> Prop)
      (s1 : SCState Γ1) : Prop :=
      outcome_satisfy (m s1) (fun r => POST (scmutres_value r) (scmutres_state r)).

    Lemma scmut_wp_monotonic {A} {Γ1 Γ2} (m : SCMut Γ1 Γ2 A) (s1 : SCState Γ1)
      (P Q : A -> SCState Γ2 -> Prop) (PQ : forall a s, P a s -> Q a s) :
      scmut_wp m P s1 -> scmut_wp m Q s1.
    Proof. unfold scmut_wp. apply outcome_satisfy_monotonic; intros []; apply PQ. Qed.

    Lemma scmut_wp_equiv {A} {Γ1 Γ2} (m : SCMut Γ1 Γ2 A) (s1 : SCState Γ1)
      (P Q : A -> SCState Γ2 -> Prop) (PQ : forall a s, P a s <-> Q a s) :
        scmut_wp m P s1 <-> scmut_wp m Q s1.
    Proof. split; apply scmut_wp_monotonic; apply PQ. Qed.

    Lemma scmut_wp_bind {Γ1 Γ2 Γ3 A B} (ma : SCMut Γ1 Γ2 A) (f : A -> SCMut Γ2 Γ3 B)
          (POST : B -> SCState Γ3 -> Prop) :
      forall s1 : SCState Γ1,
        scmut_wp (scmut_bind ma f) POST s1 <->
        scmut_wp ma (fun a => scmut_wp (f a) POST) s1.
    Proof.
      unfold SCMut, scmut_bind, scmut_wp in *; cbn; intros.
      now rewrite outcome_satisfy_bind.
    Qed.

    Lemma scmut_wp_demonic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic sm) POST s__sc <-> forall v, scmut_wp (sm v) POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic; cbn; intuition. Qed.

    Lemma scmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic_binary sm1 sm2) POST s__sc <->
      scmut_wp sm1 POST s__sc /\ scmut_wp sm2 POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic_binary; cbn; intuition. Qed.

    Lemma scmut_wp_angelic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_angelic sm) POST s__sc <-> exists v, scmut_wp (sm v) POST s__sc.
    Proof. unfold scmut_wp, scmut_angelic; cbn; intuition. Qed.

    Lemma scmut_wp_angelic_binary {Γ1 Γ2 A} (sm1 sm2 : SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_angelic_binary sm1 sm2) POST s__sc <->
      scmut_wp sm1 POST s__sc \/ scmut_wp sm2 POST s__sc.
    Proof. unfold scmut_wp, scmut_angelic_binary; cbn; intuition. Qed.

    Lemma scmut_wp_state {Γ1 Γ2 A} (f : SCState Γ1 -> A * SCState Γ2) (POST : A -> SCState Γ2 -> Prop) :
      forall (s1 : SCState Γ1),
        scmut_wp (scmut_state f) POST s1 <-> POST (fst (f s1)) (snd (f s1)).
    Proof. intros s1. cbn. now destruct (f s1); cbn. Qed.

  End SemiConcreteWP.

  Module TwoPointOSoundness.

    Global Instance InstDynamicMutatorResult {AT A} `{Inst AT A} {Γ} : Inst (DynamicMutatorResult Γ AT) (SCMutResult Γ A).
    Proof.
      constructor.
      - intros ? ? r.
        destruct r as [a s].
        constructor.
        revert a. now apply inst.
        revert s. now apply inst.
      - intros ? r.
        destruct r as [a s].
        constructor.
        apply (lift a).
        apply (lift s).
    Defined.

    Global Instance InstLawsDynamicMutatorResult {AT A} `{InstLaws AT A} {Γ} : InstLaws (DynamicMutatorResult Γ AT) (SCMutResult Γ A).
    Proof.
      constructor.
      - intros ? ? []; cbn; now rewrite ?inst_lift.
      - intros ? ? ? ? []; cbn; now rewrite ?inst_subst.
    Qed.

    Lemma sout_arrow_dcl_eta {AT A BT B} `{Subst AT, Subst BT, Inst AT A, Inst BT B} {Γ Σ1} (f : sout_arrow (DynamicMutatorResult Γ AT) BT Σ1) :
      sout_arrow_dcl
        (AT := DynamicMutatorResult Γ AT)
        (fun Σ2 ζ12 pc2 r =>
           f Σ2 ζ12 pc2 {| dmutres_result_value := dmutres_result_value r; dmutres_result_state := dmutres_result_state r |}) ->
      sout_arrow_dcl f.
    Proof.
      intros HYP Σ2 Σ3 ζ12 ζ13 pc2 pc3 ζ23 r2 r3 F P Q PQ ι2 ι3;
        specialize (HYP Σ2 Σ3 ζ12 ζ13 pc2 pc3 ζ23 r2 r3 F P Q PQ ι2 ι3);
        destruct r2, r3; intuition.
    Qed.

    Lemma sout_arrow_dcl_pure {BT B} `{Subst ET, Subst BT, Inst BT B} {Γ3 Σ1} :
        sout_arrow_dcl
          (fun (Σ3 : LCtx) (_ : Sub Σ1 Σ3) (_ : PathCondition Σ3) (X : DynamicMutatorResult Γ3 BT Σ3) =>
             match X with
             | MkDynMutResult b3 δ3 => sout_pure (MkDynMutResult b3 δ3)
             end).
    Proof. unfold sout_arrow_dcl. destruct a1, a2. cbn. intuition. Qed.

    Definition dmut_arrow Γ1 Γ2 AT BT Σ0 : Type :=
      forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> DynamicMutator Γ1 Γ2 BT Σ1.

    Definition dmut_wp {AT A} `{Inst AT A} {Γ1 Γ2 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0)
      {Σ1} (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1)
      (ι1 : SymInstance Σ1) (P : A -> SCState Γ2 -> Prop) : Prop.
    Proof.
      unfold DynamicMutator in d.
      refine (sout_wp (d Σ1 ζ01 pc1 s1) ι1 _).
      intros [a sc2].
      apply (P a sc2).
    Defined.

    Ltac fold_dmut_wp :=
      match goal with
      | |- context[sout_wp (?d ?Σ ?ζ ?pc ?s) ?ι (fun r => ?P _ _)] =>
        change (sout_wp (d Σ ζ pc s) ι _) with (dmut_wp d ζ pc s ι P)
      end.

    Lemma dmut_wp_monotonic {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d : DynamicMutator Γ1 Γ2 AT Σ0)
      (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s11 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
      (P Q : A -> SCState Γ2 -> Prop) (PQ : forall a s, P a s -> Q a s) :
        dmut_wp d ζ01 pc1 s11 ι1 P -> dmut_wp d ζ01 pc1 s11 ι1 Q.
    Proof.
      unfold dmut_wp. apply sout_wp_monotonic; intros []; apply PQ.
    Qed.

    Lemma dmut_wp_equiv {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d : DynamicMutator Γ1 Γ2 AT Σ0)
      (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s11 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
      (P Q : A -> SCState Γ2 -> Prop) (PQ : forall a s, P a s <-> Q a s) :
        dmut_wp d ζ01 pc1 s11 ι1 P <-> dmut_wp d ζ01 pc1 s11 ι1 Q.
    Proof.
      unfold dmut_wp. split; apply sout_wp_monotonic; intros []; apply PQ.
    Qed.

    Lemma dmut_wp_pure {AT A} `{InstLaws AT A} {Γ Σ0 Σ1} (a0 : AT Σ0)
      (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ Σ1) (ι1 : SymInstance Σ1)
      (P : A -> SCState Γ -> Prop) :
      dmut_wp (dmut_pure (Γ := Γ) a0) ζ01 pc1 s1 ι1 P <-> P (inst (inst ι1 ζ01) a0) (inst ι1 s1).
    Proof. unfold dmut_wp, dmut_pure; cbn. now rewrite inst_subst. Qed.

    Lemma dmut_wp_fail {AT A D} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1} (func msg : string) (data : D) (ζ01 : Sub Σ0 Σ1)
          (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
          (P : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_fail func msg data) ζ01 pc1 s1 ι1 P <-> False.
    Proof. destruct s1; cbn. split; intros []. Qed.

    Lemma dmut_wp_sub {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1 Σ2} (ζ01 : Sub Σ0 Σ1) (d : DynamicMutator Γ1 Γ2 AT Σ0)
      (pc2 : PathCondition Σ2) (s2 : SymbolicState Γ1 Σ2) (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2)
      (P : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_sub ζ01 d) ζ12 pc2 s2 ι2 P <->
      dmut_wp d (sub_comp ζ01 ζ12) pc2 s2 ι2 P.
    Proof. reflexivity. Qed.

    Definition dmut_geq {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
      forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) (ζ12 : Sub Σ1 Σ2) pc2 s2 ζ02 ι1 ι2,
        ι1 = inst ι2 ζ12 ->
        instpc ι1 pc1 ->
        instpc ι2 pc2 ->
        inst ι1 s1 = inst ι2 s2 ->
        inst ι1 ζ01 = inst ι2 ζ02 ->
        forall (P Q : A -> SCState Γ2 -> Prop) (PQ : forall a s, P a s -> Q a s),
          dmut_wp d1 ζ01 pc1 s1 ι1 P ->
          dmut_wp d2 ζ02 pc2 s2 ι2 Q.

    Definition dmut_dcl {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
      dmut_geq d d.

    Definition dmut_arrow_dcl {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0} (f : dmut_arrow Γ1 Γ2 AT BT Σ0) : Prop :=
      forall Σ1 Σ2 ζ01 ζ02 a1 a2 Σ3 Σ4 ζ13 ζ24 ζ34 pc3 pc4 s3 s4,
      forall (ι3 : SymInstance Σ3) (ι4 : SymInstance Σ4),
        ι3 = inst ι4 ζ34 ->
        instpc ι3 pc3 ->
        instpc ι4 pc4 ->
        inst ι3 (sub_comp ζ01 ζ13) = inst ι4 (sub_comp ζ02 ζ24) ->
        inst (inst ι3 ζ13) a1 = inst (inst ι4 ζ24) a2 ->
        inst ι3 s3 = inst ι4 s4 ->
        forall (P Q : B -> SCState Γ2 -> Prop) (PQ : forall b s, P b s -> Q b s),
          dmut_wp (f Σ1 ζ01 a1) ζ13 pc3 s3 ι3 P ->
          dmut_wp (f Σ2 ζ02 a2) ζ24 pc4 s4 ι4 Q.

    Lemma dmut_arrow_dcl_specialize {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
      (f : dmut_arrow Γ1 Γ2 AT BT Σ0) (f_dcl : dmut_arrow_dcl f) :
      forall Σ1 (ζ01 : Sub Σ0 Σ1) (a1 : AT Σ1),
        dmut_dcl (f Σ1 ζ01 a1).
    Proof.
      unfold dmut_dcl, dmut_geq. intros until Q; intros PQ.
      eapply f_dcl; eauto; unfold sub_comp; rewrite ?inst_subst; congruence.
    Qed.

    Lemma dmut_pure_dcl {AT A} `{InstLaws AT A} {Γ Σ} (a : AT Σ) :
      dmut_dcl (dmut_pure (Γ := Γ) a).
    Proof.
      unfold dmut_dcl, dmut_geq. intros * -> Hpc1 Hpc2 Hs Hζ * PQ.
      rewrite ?dmut_wp_pure. rewrite Hs, Hζ. apply PQ.
    Qed.

    Lemma dmut_wp_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ2}
      (d : DynamicMutator Γ1 Γ2 AT Σ0) (f : dmut_arrow Γ2 Γ3 AT BT Σ0) (f_dcl : dmut_arrow_dcl f)
      (pc2 : PathCondition Σ2) (s2 : SymbolicState Γ1 Σ2) (ζ02 : Sub Σ0 Σ2) (ι2 : SymInstance Σ2)
      (Q : B -> SCState Γ3 -> Prop) (Hpc2 : instpc ι2 pc2) :
      dmut_wp (dmut_bind d f) ζ02 pc2 s2 ι2 Q <->
      dmut_wp d ζ02 pc2 s2 ι2 (fun a s => dmut_wp (f _ (sub_id _) (lift a)) ζ02 pc2 (lift s) ι2 Q).
    Proof.
      unfold dmut_wp, dmut_bind; cbn.
      rewrite sout_wp_bind; auto. split; apply sout_wp_monotonic.
      - intros [a sc2]; cbn. rewrite sub_comp_id_right.
        rewrite sout_wp_bind; try exact sout_arrow_dcl_pure; auto.
        unfold dmut_arrow_dcl, dmut_wp in f_dcl. cbn.
        specialize (f_dcl Σ2 Σ0 ζ02 (sub_id _) (lift a) (lift a) Σ2 Σ2 (sub_id _) ζ02 (sub_id _) pc2 pc2 (lift sc2) (lift sc2) ι2 ι2).
        inster f_dcl by (unfold sub_comp; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; auto).
        specialize (f_dcl Q Q). inster f_dcl by auto.
        intros Hwp; apply f_dcl; revert Hwp.
        apply sout_wp_monotonic. intros [b sc3]. cbn.
        now rewrite ?inst_lift.
      - intros [a sc2]; cbn. rewrite sub_comp_id_right.
        rewrite sout_wp_bind; try exact sout_arrow_dcl_pure; auto.
        unfold dmut_arrow_dcl, dmut_wp in f_dcl. cbn.
        specialize (f_dcl Σ0 Σ2 (sub_id _) ζ02 (lift a) (lift a) Σ2 Σ2 ζ02 (sub_id _) (sub_id _) pc2 pc2 (lift sc2) (lift sc2) ι2 ι2).
        inster f_dcl by (unfold sub_comp; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; auto).
        specialize (f_dcl Q Q). inster f_dcl by auto.
        intros Hwp; apply f_dcl in Hwp; revert Hwp.
        apply sout_wp_monotonic. intros [b sc3]. cbn.
        now rewrite ?inst_lift.
      - unfold sout_arrow_dcl. destruct a1 as [a1 s21], a2 as [a3 s23]; cbn. intros.
        revert H12. inversion H11.
        rewrite ?sout_wp_bind; try exact sout_arrow_dcl_pure; auto.
        unfold lift; cbn. setoid_rewrite inst_lift.
        unfold dmut_arrow_dcl, dmut_wp in f_dcl.
        specialize (f_dcl Σ1 Σ3 (sub_comp ζ02 ζ1) (sub_comp ζ02 ζ2) a1 a3 Σ1 Σ3 (sub_id _) (sub_id _) ζ12 pc1 pc0 s21 s23 ι1 ι0).
        inster f_dcl by (try exact HF0; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id; intuition).
        specialize (f_dcl (fun b s => P (MkSCMutResult b s)) (fun b s => Q0 (MkSCMutResult b s))).
        apply f_dcl; intuition.
    Qed.

    Lemma dmut_wp_fmap {AT A BT B} `{InstLaws AT A, Inst BT B, Subst BT} {Γ1 Γ2 Σ0 Σ2}
      (d : DynamicMutator Γ1 Γ2 AT Σ0) (f : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> BT Σ1)
      (f_dcl : sout_mapping_dcl f)
      (pc2 : PathCondition Σ2) (s2 : SymbolicState Γ1 Σ2) (ζ02 : Sub Σ0 Σ2) (ι2 : SymInstance Σ2)
      (Q : B -> SCState Γ2 -> Prop) (Hpc2 : instpc ι2 pc2) :
      dmut_wp (dmut_fmap d f) ζ02 pc2 s2 ι2 Q <->
      dmut_wp d ζ02 pc2 s2 ι2 (fun a : A => Q (inst ι2 (f Σ2 ζ02 (lift a)))).
    Proof.
      unfold dmut_fmap, dmut_wp. rewrite sout_wp_map.
      split; apply sout_wp_monotonic; intros [a sc2]; cbn.
      - now rewrite sub_comp_id_right, inst_lift.
      - now rewrite sub_comp_id_right, inst_lift.
      - unfold sout_mapping_dcl. destruct a1 as [a1 s1], a2 as [a3 s3]; cbn.
        intros * -> Hζ. inversion 1. f_equal.
        eapply f_dcl; unfold sub_comp; rewrite ?inst_subst; intuition.
    Qed.

    Lemma dmut_wp_pair {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
      (da : DynamicMutator Γ1 Γ2 AT Σ0) (db : DynamicMutator Γ2 Γ3 BT Σ0) (db_dcl : dmut_dcl db)
      (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) s1 ι1 (Hpc : instpc ι1 pc1) P :
      dmut_wp (dmut_pair da db) ζ01 pc1 s1 ι1 P <->
      dmut_wp da ζ01 pc1 s1 ι1 (fun a sc2 => dmut_wp db ζ01 pc1 (lift sc2) ι1 (fun b => P (a,b))).
    Proof.
      unfold dmut_pair, dmut_fmap2. rewrite dmut_wp_bind; eauto.
      apply dmut_wp_equiv. intros a sc2. rewrite dmut_wp_fmap; eauto.
      rewrite dmut_wp_sub, sub_comp_id_left.
      apply dmut_wp_equiv. intros b sc3. cbn.
      now rewrite ?inst_subst, ?inst_sub_id, ?inst_lift.
      - unfold sout_mapping_dcl. intros *. cbn.
        rewrite ?inst_subst, ?inst_lift. intuition.
      - intros until Q; intros PQ.
        rewrite ?dmut_wp_fmap; eauto.
        + rewrite ?dmut_wp_sub. eapply db_dcl; eauto.
          intros *. cbn. rewrite ?inst_subst, ?inst_lift, H11.
          intuition.
        + unfold sout_mapping_dcl. intros *. cbn.
          rewrite ?inst_subst, ?inst_lift. intros. subst.
          f_equal; auto. f_equal; auto.
        + unfold sout_mapping_dcl. intros *. cbn.
          rewrite ?inst_subst, ?inst_lift. intros. subst.
          f_equal; auto. f_equal; auto.
    Qed.

    Lemma dmut_wp_bind_right {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
          (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0) (d2_dcl : dmut_dcl d2)
          (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
          (P : B -> SCState Γ3 -> Prop) (Hpc1 : instpc ι1 pc1) :
      dmut_wp (dmut_bind_right d1 d2) ζ01 pc1 s1 ι1 P <->
      dmut_wp d1 ζ01 pc1 s1 ι1 (fun a sc2 => dmut_wp d2 ζ01 pc1 (lift sc2) ι1 P).
    Proof.
      unfold dmut_bind_right. rewrite dmut_wp_bind; auto.
      unfold dmut_wp, dmut_sub.
      split; apply sout_wp_monotonic;
        intros [a sc2]; now rewrite sub_comp_id_left.
      unfold dmut_arrow_dcl. intros until Q; intros PQ.
      rewrite ?dmut_wp_sub. eapply d2_dcl; eauto.
    Qed.

    Lemma dmut_bind_right_arrow_dcl {AT A BT B CT C} `{InstLaws AT A, InstLaws BT B, InstLaws CT C} {Γ1 Γ2 Γ3 Σ1}
      (d1 : dmut_arrow Γ1 Γ2 AT BT Σ1) (d1_dcl : dmut_arrow_dcl d1)
      (d2 : dmut_arrow Γ2 Γ3 AT CT Σ1) (d2_dcl : dmut_arrow_dcl d2) :
      dmut_arrow_dcl (fun Σ2 ζ02 a2 => dmut_bind_right (d1 Σ2 ζ02 a2) (d2 Σ2 ζ02 a2)).
    Proof.
      intros until Q. intros PQ.
      rewrite ?dmut_wp_bind_right; eauto.
      eapply d1_dcl; eauto. intros ? ?.
      eapply d2_dcl; eauto. now rewrite ?inst_lift.
      now apply dmut_arrow_dcl_specialize.
      now apply dmut_arrow_dcl_specialize.
    Qed.

    Lemma dmut_bind_arrow_dcl {AT A BT B CT C} `{InstLaws AT A, InstLaws BT B, InstLaws CT C}
        {Γ1 Γ2 Γ3 Σ0}
        (d1 : dmut_arrow Γ1 Γ2 AT BT Σ0) (d1_dcl : dmut_arrow_dcl d1)
        (d2 : dmut_arrow Γ2 Γ3 BT CT Σ0) (d2_dcl : dmut_arrow_dcl d2) :
      dmut_arrow_dcl (fun Σ2 ζ02 a2 => dmut_bind (d1 Σ2 ζ02 a2) (fun Σ3 ζ23 a3 => d2 Σ3 (sub_comp ζ02 ζ23) a3)).
    Proof.
      unfold dmut_arrow_dcl, dmut_geq.
      intros * -> Hpc1 Hpc2 Hζ Ha Hs P Q PQ; cbn.
      rewrite ?dmut_wp_bind; auto. eapply d1_dcl; eauto. intros a s.
      eapply d2_dcl; eauto; unfold sub_comp in *; rewrite ?inst_subst in Hζ;
        rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; intuition.

      unfold dmut_arrow_dcl.
      intros * -> Hpc3 Hpc4 Hζ2 Ha2 Hs2 P2 Q2 PQ2; cbn.
      eapply d2_dcl; eauto.
      unfold sub_comp.
      unfold sub_comp in Hζ2.
      rewrite ?inst_subst in Hζ2.
      now rewrite ?inst_subst, Hζ2.

      unfold dmut_arrow_dcl.
      intros * -> Hpc3 Hpc4 Hζ2 Ha2 Hs2 P2 Q2 PQ2; cbn.
      eapply d2_dcl; eauto.
      unfold sub_comp.
      unfold sub_comp in Hζ2.
      rewrite ?inst_subst in Hζ2.
      now rewrite ?inst_subst, Hζ2.
    Qed.

    Lemma dmut_sub_arrow_dcl {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ2 Γ3 Σ0} (d : DynamicMutator Γ2 Γ3 BT Σ0) (d_dcl : dmut_dcl d) :
      dmut_arrow_dcl (fun (Σ2 : LCtx) (ζ02 : Sub Σ0 Σ2) (_ : AT Σ2) => dmut_sub ζ02 d).
    Proof. intros until Q; intros PQ. rewrite ?dmut_wp_sub. eapply d_dcl; eauto. Qed.

    Lemma dmut_pure_arrow_dcl {AT A} `{InstLaws AT A} {Γ Σ0} :
      dmut_arrow_dcl (fun Σ1 (ζ01 : Sub Σ0 Σ1) (a1 : AT Σ1) => dmut_pure (Γ := Γ) a1).
    Proof.
      intros until Q; intros PQ. cbn.
      intros HP. apply PQ. revert HP.
      rewrite ?inst_subst. intuition.
    Qed.

    Lemma dmut_wp_bind_left {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
          (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0) (d2_dcl : dmut_dcl d2)
          (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
          (P : A -> SCState Γ3 -> Prop) (Hpc1 : instpc ι1 pc1) :
      dmut_wp (dmut_bind_left d1 d2) ζ01 pc1 s1 ι1 P <->
      dmut_wp d1 ζ01 pc1 s1 ι1 (fun a sc2 => dmut_wp d2 ζ01 pc1 (lift sc2) ι1 (fun _ => P a)).
    Proof.
      unfold dmut_bind_left. rewrite dmut_wp_bind; auto. apply dmut_wp_equiv.
      intros a sc2. rewrite dmut_wp_bind_right, dmut_wp_sub; auto.
      split; eapply d2_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id; auto;
        intros _ sc3; now rewrite dmut_wp_pure, ?inst_lift.
      apply dmut_pure_dcl.
      apply dmut_bind_right_arrow_dcl.
      now apply dmut_sub_arrow_dcl.
      apply dmut_pure_arrow_dcl.
    Qed.

    Lemma dmut_wp_state {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ1 Σ2} (f : forall Σ2, Sub Σ1 Σ2 -> SymbolicState Γ1 Σ2 -> Pair AT (SymbolicState Γ2) Σ2)
          (pc2 : PathCondition Σ2) (s12 : SymbolicState Γ1 Σ2) (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2) (Q : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_state f) ζ12 pc2 s12 ι2 Q <->
      match f Σ2 ζ12 s12 with | (a, s22) => Q (inst ι2 a) (inst ι2 s22) end.
    Proof.
      unfold dmut_wp, dmut_state; cbn.
      now destruct (f Σ2 ζ12 s12).
    Qed.

    Lemma dmut_wp_demonic_binary {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ0 Σ1} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0)
          (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s11 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
          (P : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_demonic_binary d1 d2) ζ01 pc1 s11 ι1 P <->
      dmut_wp d1 ζ01 pc1 s11 ι1 P /\ dmut_wp d2 ζ01 pc1 s11 ι1 P.
    Proof. reflexivity. Qed.

    Lemma dmut_wp_angelic_binary {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ0 Σ1} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0)
      (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (s11 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1) (P : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_angelic_binary d1 d2) ζ01 pc1 s11 ι1 P <->
      dmut_wp d1 ζ01 pc1 s11 ι1 P \/ dmut_wp d2 ζ01 pc1 s11 ι1 P.
    Proof. reflexivity. Qed.

    Lemma dmut_wp_angelic {AT A I} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ Σ1} (d : I -> DynamicMutator Γ1 Γ2 AT Σ) (* (d_dcl : dmut_dcl d) *)
      (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
      (P : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_angelic d) ζ01 pc1 s1 ι1 P <->
      exists i, dmut_wp (d i) ζ01 pc1 s1 ι1 P.
    Proof. reflexivity. Qed.

    Lemma dmut_wp_fresh {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ Σ1 x σ} (d : DynamicMutator Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : dmut_dcl d)
          (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
          (P : A -> SCState Γ2 -> Prop) (hpc : instpc ι1 pc1) :
      dmut_wp (dmut_fresh x σ d) ζ01 pc1 s1 ι1 P <->
      forall v : Lit σ, dmut_wp d (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 s1 ι1 P.
    Proof.
      unfold dmut_wp, dmut_fresh; cbn.
      split; intros Hwp v; specialize (Hwp v); revert Hwp.
      - apply (d_dcl
                 (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) Σ1 (sub_snoc (sub_comp ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))) (subst sub_wk1 pc1)
                 (subst sub_wk1 s1) (sub_snoc (sub_id Σ1) (fresh Σ1 (Some x) :: σ) (term_lit σ v)) pc1 s1 (sub_snoc ζ01 (x :: σ) (term_lit σ v)));
          rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
        unfold sub_comp. now rewrite inst_subst, inst_sub_wk1.
      - apply (d_dcl
                 Σ1 (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 s1 sub_wk1 (subst sub_wk1 pc1) (subst sub_wk1 s1)
                 (sub_snoc (sub_comp ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))));
          rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
        unfold sub_comp. now rewrite inst_subst, inst_sub_wk1.
    Qed.

    Lemma dmut_wp_angelic_list {AT A D} `{InstLaws AT A} {Γ Σ} (func msg : string) (data : D)
      (xs : List AT Σ) Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (s11 : SymbolicState Γ Σ1) (ι1 : SymInstance Σ1)
      (P : A -> SCState Γ -> Prop) :
      dmut_wp (dmut_angelic_list func msg data xs) ζ01 pc1 s11 ι1 P <->
      exists x : AT _, List.In x xs /\ P (inst (inst ι1 ζ01) x) (inst ι1 s11).
    Proof.
      induction xs; cbn - [dmut_wp].
      - rewrite dmut_wp_fail. split. intro Fm; exfalso; intuition.
        intros []; intuition.
      - destruct xs; cbn - [dmut_wp] in *.
        + rewrite dmut_wp_fail in IHxs.
          rewrite dmut_wp_pure.
          destruct IHxs. split; intros; destruct_conjs.
          exists a. intuition.
          intuition.
        + rewrite dmut_wp_angelic_binary, dmut_wp_pure.
          split. intros [Hwp|Hwp].
          * exists a. split; auto.
          * apply IHxs in Hwp. destruct Hwp as [x [Hwp HP]].
            exists x. split; auto.
          * intros [x [Hwp HP]].
            destruct Hwp as [Hwp|Hwp]. subst. left. auto.
            destruct Hwp as [Hwp|Hwp]. subst.
            right. apply IHxs. exists x. split; auto.
            right. apply IHxs. exists x. split; auto.
    Qed.

    Lemma dmut_wp_demonic_list {AT A} `{InstLaws AT A} {Γ Σ}
      (xs : List AT Σ) Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (s11 : SymbolicState Γ Σ1) (ι1 : SymInstance Σ1)
      (P : A -> SCState Γ -> Prop) :
      dmut_wp (dmut_demonic_list xs) ζ01 pc1 s11 ι1 P <->
      forall x : AT _, List.In x xs -> P (inst (inst ι1 ζ01) x) (inst ι1 s11).
    Proof.
      induction xs.
      - cbn; firstorder.
      - destruct xs; cbn; rewrite inst_subst; intuition.
    Qed.

    Lemma dmut_wp_demonic_finite {X AT A} `{finite.Finite X, Subst AT, Inst AT A, InstLaws AT A, SubstLaws AT} {Γ1 Γ2 Σ Σ1}
      (k : X -> DynamicMutator Γ1 Γ2 AT Σ) (k_dcl : forall x, dmut_dcl (k x))
      (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ1 Σ1) (ι1 : SymInstance Σ1)
      (P : A -> SCState Γ2 -> Prop) (Hpc : instpc ι1 pc1) :
      dmut_wp (dmut_demonic_finite X k) ζ01 pc1 s1 ι1 P <->
      (forall x : X, dmut_wp (k x) ζ01 pc1 s1 ι1 P).
    Proof.
      unfold dmut_demonic_finite.
      rewrite dmut_wp_bind.
      - rewrite dmut_wp_demonic_list.
        setoid_rewrite dmut_wp_sub.
        setoid_rewrite sub_comp_id_left.
        setoid_rewrite <-base.elem_of_list_In.
        split.
        + intros Hk x.
          specialize (Hk x).
          specialize (Hk (finite.elem_of_enum x)).
          revert Hk.
          eapply k_dcl; erewrite ?inst_sub_id, ?inst_lift; trivial.
        + intros Hk x _.
          specialize (Hk x).
          revert Hk.
          eapply k_dcl; erewrite ?inst_sub_id, ?inst_lift; trivial.
      - intros until Q; intros PQ. rewrite ?dmut_wp_sub.
        unfold instantiate_const, inst in H12; subst.
        eapply k_dcl; eauto.
      - eauto.
    Qed.

    Lemma dmut_wp_freshtermvar {Γ Σ Σ1 x σ}
      (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (s1 : SymbolicState Γ Σ1) (ι1 : SymInstance Σ1)
      (P : Lit σ -> SCState Γ -> Prop) (Hpc : instpc ι1 pc1) :
      dmut_wp (@dmut_freshtermvar Γ _ σ x) ζ01 pc1 s1 ι1 P <->
      forall v : Lit σ, P v (inst ι1 s1).
    Proof.
      unfold dmut_freshtermvar. rewrite dmut_wp_fresh; auto.
      apply dmut_pure_dcl.
    Qed.

    Lemma dmut_fail_dcl `{Inst AT A, Subst AT} {D Γ1 Γ2 Σ} func msg data :
      dmut_dcl (@dmut_fail Γ1 Γ2 AT Σ D func msg data).
    Proof.
      unfold dmut_dcl, dmut_geq. intros * -> Hpc1 Hpc2 Hs Hζ * PQ.
      now rewrite ?dmut_wp_fail.
    Qed.

    Lemma dmut_sub_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_dcl : dmut_dcl d) :
      forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), dmut_dcl (dmut_sub ζ1 d).
    Proof.
      unfold dmut_dcl, dmut_geq. intros * -> Hpc1 Hpc2 Hs Hζ * PQ. rewrite ?dmut_wp_sub.
      apply d_dcl with ζ12; auto. unfold sub_comp. rewrite ?inst_subst. congruence.
    Qed.

    Lemma dmut_fresh_dcl {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ x σ} (d : DynamicMutator Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : dmut_dcl d) :
      dmut_dcl (dmut_fresh x σ d).
    Proof.
      unfold dmut_dcl, dmut_geq. intros until Q; intros PQ.
      rewrite ?dmut_wp_fresh; auto.
      intros Hwp v. specialize (Hwp v). revert Hwp.
      eapply d_dcl; eauto. rewrite ?inst_sub_snoc.
      cbn. f_equal. exact H5.
    Qed.

    Lemma dmut_freshtermvar_dcl {Γ Σ x σ} :
      dmut_dcl (@dmut_freshtermvar Γ Σ σ x).
    Proof. apply dmut_fresh_dcl, dmut_pure_dcl. Qed.

    Ltac fold_inst_term :=
      repeat change (@inst_term ?Σ ?ι ?σ ?t) with (@inst (fun Σ => Term Σ σ) (Lit σ) (@instantiate_term σ) Σ ι t) in *.

    Lemma dmut_bind_dcl {AT A BT B} `{InstLaws AT A, InstLaws BT B}
        {Γ1 Γ2 Γ3 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_dcl : dmut_dcl d)
        (f : dmut_arrow Γ2 Γ3 AT BT Σ0) (f_dcl : dmut_arrow_dcl f) :
      dmut_dcl (dmut_bind d f).
    Proof.
      unfold dmut_dcl, dmut_geq. intros * -> Hpc1 Hpc2 Hs Hζ P Q PQ; cbn.
      rewrite ?dmut_wp_bind; auto. eapply d_dcl; eauto. intros a s.
      eapply f_dcl; eauto; unfold sub_comp;
        rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; intuition.
    Qed.

    Lemma dmut_bind_right_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
      (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0)
      (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) :
      dmut_dcl (dmut_bind_right d1 d2).
    Proof.
      unfold dmut_bind_right, dmut_sub. apply dmut_bind_dcl; auto.
      unfold dmut_arrow_dcl. intros. revert H13. eapply d2_dcl; eauto.
    Qed.

    Lemma dmut_bind_left_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
      (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0)
      (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) :
      dmut_dcl (dmut_bind_left d1 d2).
    Proof.
      unfold dmut_bind_left. apply dmut_bind_dcl; auto.
      apply dmut_bind_right_arrow_dcl.
      now apply dmut_sub_arrow_dcl.
      apply dmut_pure_arrow_dcl.
    Qed.

    Lemma dmut_demonic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) :
      dmut_dcl (dmut_demonic_binary d1 d2).
    Proof.
      unfold dmut_dcl, dmut_geq. intros until Q; intros PQ.
      rewrite ?dmut_wp_demonic_binary. intros [Hwp1 Hwp2].
      split.
      - revert Hwp1. eapply d1_dcl; eauto.
      - revert Hwp2. eapply d2_dcl; eauto.
    Qed.

    Lemma dmut_angelic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) :
      dmut_dcl (dmut_angelic_binary d1 d2).
    Proof.
      unfold dmut_dcl, dmut_geq. intros until Q; intros PQ.
      rewrite ?dmut_wp_angelic_binary. intros [Hwp1|Hwp2].
      - left. revert Hwp1. eapply d1_dcl; eauto.
      - right. revert Hwp2. eapply d2_dcl; eauto.
    Qed.

    Lemma dmut_state_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ}
          (f : forall Σ' : LCtx, Sub Σ Σ' -> SymbolicState Γ1 Σ' -> Pair AT (SymbolicState Γ2) Σ')
          (f_dcl : forall Σ1 Σ2 (ζ01 : Sub Σ Σ1) (ζ02 : Sub Σ Σ2) (ζ12 : Sub Σ1 Σ2) (s1 : SymbolicState Γ1 Σ1) (s2 : SymbolicState Γ1 Σ2) ι1 ι2,
              ι1 = inst ι2 ζ12 ->
              inst ι1 s1 = inst ι2 s2 ->
              inst ι1 ζ01 = inst ι2 ζ02 ->
              inst ι1 (f Σ1 ζ01 s1) = inst ι2 (f Σ2 ζ02 s2)) :
      dmut_dcl (dmut_state f).
    Proof.
      unfold dmut_dcl; intros until Q. intros PQ. rewrite ?dmut_wp_state.
      pose proof (f_dcl Σ1 Σ2 ζ01 ζ02 ζ12 s1 s2 ι1 ι2) as Hf.
      inster Hf by auto. destruct (f Σ1 ζ01 s1), (f Σ2 ζ02 s2); cbn.
      inversion Hf. intros Hp. apply PQ. revert Hp. intuition.
    Qed.
    Local Hint Resolve dmut_state_dcl : core.

    Lemma dmut_put_heap_dcl {Γ Σ} (h : SymbolicHeap Σ) :
      dmut_dcl (dmut_put_heap (Γ := Γ) h).
    Proof.
      apply dmut_state_dcl. destruct s1 as [δ h1], s2 as [δ2 h2].
      cbn. intros ? ? -> Heqs Heqζ. inversion Heqs.
      f_equal. f_equal. rewrite ?inst_subst. intuition.
    Qed.
    Local Hint Resolve dmut_put_heap_dcl : core.

    Lemma dmut_pop_local_dcl {Γ x σ Σ} :
      dmut_dcl (@dmut_pop_local Γ x σ Σ).
    Proof.
      unfold dmut_pop_local, dmut_modify_local, dmut_state_local.
      apply dmut_state_dcl. destruct s1 as [δ1 h1], s2 as [δ2 h2]; cbn.
      intros * -> Hs Hζ. inversion Hs. clear Hs.
      destruct (snocView δ1), (snocView δ2). cbn in H0.
      apply noConfusion_inv, (f_equal pr1) in H0. cbn in H0.
      f_equal. f_equal. cbn. apply H0.
    Qed.

    Lemma dmut_block_dcl {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ}  :
      dmut_dcl (Γ1 := Γ1) (Γ2 := Γ2) (Σ0 := Σ) dmut_block.
    Proof. now unfold dmut_dcl, dmut_block. Qed.

    (* Lemma dmut_demonic_list_dcl {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ} (l : list (DynamicMutator Γ1 Γ2 AT Σ)) *)
    (*   (l_dcl : forall d, List.In d l -> dmut_dcl d) : *)
    (*   dmut_dcl (dmut_demonic_list l). *)
    (* Proof. *)
    (*   induction l; cbn. *)
    (*   - apply dmut_block_dcl. *)
    (*   - destruct l. *)
    (*     + apply l_dcl. now left. *)
    (*     + apply dmut_demonic_binary_dcl. *)
    (*       apply l_dcl. now left. *)
    (*       apply IHl. intros d' dIn'. *)
    (*       apply l_dcl. now right. *)
    (* Qed. *)

    Lemma dmut_angelic_list_dcl {AT A D} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A}
          {Γ Σ} func msg (data : D) (l : list (AT Σ)) :
      dmut_dcl (Γ2 := Γ) (dmut_angelic_list func msg data l).
    Proof.
      induction l; cbn.
      - apply dmut_fail_dcl.
      - destruct l.
        + apply dmut_pure_dcl.
        + apply dmut_angelic_binary_dcl.
          apply dmut_pure_dcl.
          apply IHl.
    Qed.

    Lemma dmut_angelic_list_arrow_dcl {AT A BT B D} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A, Inst BT B, InstLaws BT B}
          {Γ Σ} func msg (data : D) (l : forall Σ2 (ζ : Sub Σ Σ2) s, list (BT Σ2))
      (Hl : forall (Σ1 Σ2 : LCtx) (ζ01 : Sub Σ Σ1) (ζ02 : Sub Σ Σ2) (a1 : AT Σ1) (a2 : AT Σ2) (Σ3 Σ4 : LCtx)
         (ζ13 : Sub Σ1 Σ3) (ζ24 : Sub Σ2 Σ4) (ζ34 : Sub Σ3 Σ4) (pc3 : PathCondition Σ3) (pc4 : PathCondition Σ4)
         (ι3 : SymInstance Σ3) (ι4 : SymInstance Σ4),
          ι3 = inst ι4 ζ34 ->
          instpc ι3 pc3 ->
          instpc ι4 pc4 ->
          inst ι3 (sub_comp ζ01 ζ13) = inst ι4 (sub_comp ζ02 ζ24) ->
          inst (inst ι3 ζ13) a1 = inst (inst ι4 ζ24) a2 ->
          inst (inst ι3 ζ13) (l Σ1 ζ01 a1) = inst (inst ι4 ζ24) (l Σ2 ζ02 a2)) :
      dmut_arrow_dcl (Γ2 := Γ) (fun Σ2 (ζ : Sub Σ Σ2) s => dmut_angelic_list func msg data (l Σ2 ζ s)).
    Proof.
      unfold dmut_arrow_dcl.
      intros until Q.
      intros PQ.
      assert (eql : inst (inst ι3 ζ13) (l Σ1 ζ01 a1) = inst (inst ι4 ζ24) (l Σ2 ζ02 a2)) by (eapply Hl; eauto).
      rewrite ?dmut_wp_angelic_list; eauto.
      intros (x & xInl1 & Px).
      apply (List.in_map (inst (inst ι3 ζ13))) in xInl1.
      unfold inst at 1 3 in eql; cbn in eql.
      rewrite eql in xInl1.
      eapply List.in_map_iff in xInl1.
      destruct xInl1 as (x2 & eq2 & x2Inl2).
      apply PQ in Px.
      rewrite <-eq2,H17 in Px.
      exists x2; eauto.
    Qed.

    (* Lemma dmut_demonic_finite_dcl {F AT A} `{finite.Finite F, Subst AT, Inst AT A} {Γ Σ} *)
    (*   (k : F -> DynamicMutator Γ Γ AT Σ) (k_dcl : forall x, dmut_dcl (k x)) : *)
    (*   dmut_dcl (dmut_demonic_finite F k). *)
    (* Proof. *)
    (*   unfold dmut_demonic_finite. apply dmut_demonic_list_dcl. *)
    (*   intros d. rewrite List.in_map_iff. *)
    (*   intros [x [? xIn]]. subst d. apply k_dcl. *)
    (* Qed. *)

    (* Lemma dmut_angelic_finite_dcl {F AT A} `{finite.Finite F, Subst AT, Inst AT A} {Γ Σ} *)
    (*   (k : F -> DynamicMutator Γ Γ AT Σ) (k_dcl : forall x, dmut_dcl (k x)) : *)
    (*   dmut_dcl (dmut_angelic_finite F k). *)
    (* Proof. *)
    (*   unfold dmut_angelic_finite. apply dmut_angelic_list_dcl. *)
    (*   intros d. rewrite List.in_map_iff. *)
    (*   intros [x [? xIn]]. subst d. apply k_dcl. *)
    (* Qed. *)

    Lemma dmut_wp_assume_formula {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fml : Formula Σ1) (s2 : SymbolicState Γ Σ2)
          (ι2 : SymInstance Σ2) P :
      instpc ι2 pc2 ->
      dmut_wp (dmut_assume_formula fml) ζ12 pc2 s2 ι2 P <->
      ((inst (inst ι2 ζ12) fml : Prop) -> P tt (inst ι2 s2)).
    Proof.
      unfold dmut_wp, dmut_assume_formula. intros.
      rewrite sout_wp_bind; auto.
      - rewrite sout_wp_assume_formula.
        rewrite ?subst_sub_id, ?inst_subst.
        reflexivity.
      - unfold sout_arrow_dcl. cbn. intros.
        revert H5. rewrite ?inst_subst.
        rewrite H3, H4. apply PQ.
    Qed.

    Lemma dmut_assume_formula_dcl {Γ Σ} (fml : Formula Σ) :
      dmut_dcl (Γ1 := Γ) (dmut_assume_formula fml).
    Proof.
      unfold dmut_dcl, dmut_geq; intros. revert H4.
      rewrite ?dmut_wp_assume_formula; auto.
      rewrite H2, H3. intuition.
    Qed.

    Lemma dmut_assume_formulas_dcl {Γ Σ} (fmls : list (Formula Σ)) :
      dmut_dcl (Γ1 := Γ) (dmut_assume_formulas fmls).
    Proof.
      induction fmls.
      + now eapply dmut_pure_dcl.
      + cbn.
        eapply dmut_bind_right_dcl.
        eapply dmut_assume_formula_dcl.
        eapply IHfmls.
    Qed.

    Lemma dmut_wp_assume_formulas {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fmls : list (Formula Σ1)) (s2 : SymbolicState Γ Σ2)
      (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
      dmut_wp (dmut_assume_formulas fmls) ζ12 pc2 s2 ι2 P <->
      (instpc (inst ι2 ζ12) fmls -> P tt (inst ι2 s2)).
    Proof.
      unfold dmut_assume_formulas. revert s2.
      induction fmls; cbn [List.fold_right]; intros s2.
      - rewrite dmut_wp_pure. cbn. intuition.
        apply H. constructor.
      - rewrite dmut_wp_bind_right; auto.
        rewrite dmut_wp_assume_formula; auto.
        rewrite IHfmls.
        rewrite inst_pathcondition_cons.
        rewrite inst_lift.
        intuition.
        eapply dmut_assume_formulas_dcl.
    Qed.

    Lemma dmut_wp_assert_formula {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fml : Formula Σ1) (s2 : SymbolicState Γ Σ2)
      (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
      dmut_wp (dmut_assert_formula fml) ζ12 pc2 s2 ι2 P <->
      (inst (inst ι2 ζ12) fml /\ P tt (inst ι2 s2)).
    Proof.
      unfold dmut_wp, dmut_assert_formula.
      rewrite sout_wp_bind, sout_wp_assert_formula; cbn;
        rewrite ?inst_subst, ?inst_sub_id; auto.
      unfold sout_arrow_dcl. cbn. intros.
      revert H4. rewrite ?inst_subst.
      rewrite H2, H3. apply PQ.
    Qed.

    Lemma dmut_assert_formula_dcl {Γ Σ} (fml : Formula Σ) :
      dmut_dcl (Γ1 := Γ) (dmut_assert_formula fml).
    Proof.
      unfold dmut_dcl, dmut_geq. intros. revert H4.
      rewrite ?dmut_wp_assert_formula; auto.
      rewrite H2, H3. intuition.
    Qed.

    Lemma dmut_dcl_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) :
      dmut_dcl (dmut_assert_formulas (Γ := Γ) fmls).
    Proof.
      induction fmls; cbn; [eapply dmut_pure_dcl|].
      eapply dmut_bind_right_dcl.
      eapply dmut_assert_formula_dcl.
      eapply IHfmls.
    Qed.

    Lemma dmut_wp_assert_formulas {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fmls : list (Formula Σ1)) (s2 : SymbolicState Γ Σ2)
      (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
      dmut_wp (dmut_assert_formulas fmls) ζ12 pc2 s2 ι2 P <->
      (instpc (inst ι2 ζ12) fmls /\ P tt (inst ι2 s2)).
    Proof.
      unfold dmut_assert_formulas. revert s2.
      induction fmls; cbn [List.fold_right]; intros s2.
      - rewrite dmut_wp_pure. intuition.
        constructor.
      - rewrite dmut_wp_bind_right; auto.
        rewrite dmut_wp_assert_formula; auto.
        rewrite IHfmls.
        rewrite inst_pathcondition_cons.
        rewrite inst_lift.
        intuition.
        fold (dmut_assert_formulas (Γ := Γ) fmls).
        eapply dmut_dcl_assert_formulas.
    Qed.

    Lemma dmut_wp_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
      (d : 𝑬𝑲 E -> DynamicMutator Γ1 Γ2 AT Σ1) (d_dcl : forall x, dmut_dcl (d x))
      Σ2 (ζ12 : Sub Σ1 Σ2) pc2 s2 ι2 P :
      instpc ι2 pc2 ->
      dmut_wp (dmut_match_enum t d) ζ12 pc2 s2 ι2 P <->
      dmut_wp (d (inst (T := fun Σ => Term Σ _) (A := 𝑬𝑲 E) (inst ι2 ζ12) t)) ζ12 pc2 s2 ι2 P.
    Proof.
      intros Hpc2. unfold dmut_match_enum. cbn.
      destruct (term_get_lit_spec (subst (T := fun Σ => Term Σ (ty_enum E)) ζ12 t)) as [k Heqιs|]; cbn [Lit] in *.
      - fold_dmut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. now rewrite Heqιs.
      - fold_dmut_wp. rewrite dmut_wp_demonic_finite. split; intros Hwp.
        + specialize (Hwp (inst (T := fun Σ => Term Σ _) (inst ι2 ζ12) t)).
          rewrite dmut_wp_bind_right, dmut_wp_assume_formula, dmut_wp_sub in Hwp; auto.
          rewrite sub_comp_id_right, inst_sub_id in Hwp. cbn in Hwp.
          inster Hwp by now rewrite inst_subst. revert Hwp.
          eapply d_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto.
          now apply dmut_sub_dcl.
        + intros x. rewrite dmut_wp_bind_right; auto.
          rewrite dmut_wp_assume_formula; auto. cbn.
          rewrite inst_subst, inst_sub_id. intros <-.
          rewrite dmut_wp_sub. rewrite sub_comp_id_right. revert Hwp.
          eapply d_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto.
          now apply dmut_sub_dcl.
        + intros x.
          apply dmut_bind_right_dcl.
          apply dmut_assume_formula_dcl.
          now apply dmut_sub_dcl.
        + assumption.
    Qed.

    Lemma dmut_wp_match_sum {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (x y : 𝑺) (σ τ : Ty) (s : Term Σ1 (ty_sum σ τ))
      (dinl : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (x :: σ)))  (dinl_dcl : dmut_dcl dinl)
      (dinr : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (y :: τ)))  (dinr_dcl : dmut_dcl dinr)
      Σ2 (ζ12 : Sub Σ1 Σ2) pc2 s2 ι2 P :
      instpc ι2 pc2 ->
      dmut_wp (dmut_match_sum s dinl dinr) ζ12 pc2 s2 ι2 P <->
      (forall sl,
          inst (T := fun Σ => Term Σ _) (A := Lit σ + Lit τ) (inst ι2 ζ12) s =
          @inl (Lit σ) (Lit τ) (inst (T := fun Σ => Term Σ _) (A := Lit σ) ι2 sl) ->
          dmut_wp dinl (sub_snoc ζ12 (x :: σ) sl) pc2 s2 ι2 P) /\
      (forall sr,
          inst (T := fun Σ => Term Σ (ty_sum σ τ)) (A := Lit σ + Lit τ) (inst ι2 ζ12) s =
          @inr (Lit σ) (Lit τ) (inst (T := fun Σ => Term Σ τ) (A := Lit τ) ι2 sr) ->
          dmut_wp dinr (sub_snoc ζ12 (y :: τ) sr) pc2 s2 ι2 P).
    Proof.
      intros Hpc2. unfold dmut_match_sum. cbn.
      destruct (term_get_sum_spec (subst (T := fun Σ => Term Σ (ty_sum σ τ)) ζ12 s)) as [[sl|sr] Heqιs|_].
      - fold_dmut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. split.
        + intros Hwp. split.
          * intros sl' Heq. revert Hwp. rewrite Heqιs in Heq. inversion Heq.
            eapply dinl_dcl; unfold sub_comp;
              rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto.
            now f_equal.
          * intros sr Heq. rewrite Heqιs in Heq. discriminate.
        + intros [Hl Hr]. specialize (Hl sl Heqιs). revert Hl. auto.
      - fold_dmut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. split.
        + intros Hwp. split.
          * intros sl Heq. rewrite Heqιs in Heq. discriminate.
          * intros sr' Heq. revert Hwp. rewrite Heqιs in Heq. inversion Heq.
            eapply dinr_dcl; unfold sub_comp;
              rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto.
            now f_equal.
        + intros [Hl Hr]. specialize (Hr sr Heqιs). revert Hr.
          eapply dinr_dcl; unfold sub_comp;
            rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto.
      - fold_dmut_wp. rewrite dmut_wp_demonic_binary.
        rewrite ?dmut_wp_fresh; auto.
        { split; intros [Hl Hr]; (split; [clear Hr|clear Hl]).
          - intros sl Heqsl. specialize (Hl (inst ι2 sl)).
            rewrite dmut_wp_bind_right, dmut_wp_assume_formula in Hl; auto.
            rewrite inst_sub_snoc in Hl. cbn in Hl.
            rewrite inst_subst, inst_sub_wk1 in Hl.
            specialize (Hl Heqsl). revert Hl.
            eapply dinl_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
          - intros sr Heqsr. specialize (Hr (inst ι2 sr)).
            rewrite dmut_wp_bind_right, dmut_wp_assume_formula in Hr; auto.
            rewrite inst_sub_snoc in Hr. cbn in Hr.
            rewrite inst_subst, inst_sub_wk1 in Hr.
            specialize (Hr Heqsr). revert Hr.
            eapply dinr_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
          - intros vl. specialize (Hl (term_lit _ vl)).
            rewrite dmut_wp_bind_right, dmut_wp_assume_formula; auto.
            rewrite inst_sub_snoc. cbn. rewrite inst_subst, inst_sub_wk1.
            intros Heq. specialize (Hl Heq). revert Hl.
            eapply dinl_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
          - intros vr. specialize (Hr (term_lit _ vr)).
            rewrite dmut_wp_bind_right, dmut_wp_assume_formula; auto.
            rewrite inst_sub_snoc. cbn. rewrite inst_subst, inst_sub_wk1.
            intros Heq. specialize (Hr Heq). revert Hr.
            eapply dinr_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
        }
        + apply dmut_bind_right_dcl; auto.
          apply dmut_assume_formula_dcl.
        + apply dmut_bind_right_dcl; auto.
          apply dmut_assume_formula_dcl.
    Qed.

    Definition dmut_wp_match_pair {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (x y : 𝑺) (σ τ : Ty) (s : Term Σ1 (ty_prod σ τ))
      (d : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (d_dcl : dmut_dcl d)
      Σ2 (ζ12 : Sub Σ1 Σ2) pc2 s2 ι2 (Hpc : instpc ι2 pc2) P :
      dmut_wp (dmut_match_pair s d) ζ12 pc2 s2 ι2 P <->
      (forall sl sr,
          inst (T := fun Σ => Term Σ _) (A := Lit (ty_prod σ τ)) (inst ι2 ζ12) s =
          (inst (T := fun Σ => Term Σ _) (A := Lit σ) ι2 sl,
           inst (T := fun Σ => Term Σ _) (A := Lit τ) ι2 sr) ->
          dmut_wp d (sub_snoc (sub_snoc ζ12 (x :: σ) sl) (y :: τ) sr) pc2 s2 ι2 P).
    Proof.
      unfold dmut_match_pair. cbn - [sub_wk1].
      destruct (term_get_pair_spec (subst (T := fun Σ => Term Σ _) ζ12 s)) as [[sl sr] Heqs|];
        fold_dmut_wp.
      - specialize (Heqs ι2). rewrite inst_subst in Heqs. split; auto.
        intros Hwp sl2 sr2 Heqs2. rewrite Heqs2 in Heqs.
        inversion Heqs. revert Hwp.
        eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
        f_equal; auto. f_equal; auto.
      - split; intros Hwp.
        { intros sl sr Heqs.
          rewrite dmut_wp_fresh in Hwp; auto. specialize (Hwp (inst ι2 sl)).
          rewrite dmut_wp_fresh in Hwp; auto. specialize (Hwp (inst ι2 sr)).
          rewrite dmut_wp_bind_right in Hwp; auto.
          rewrite dmut_wp_assume_formula in Hwp; auto.
          rewrite ?inst_sub_snoc in Hwp. cbn - [sub_wk1] in Hwp.
          unfold sub_comp in Hwp. rewrite ?inst_subst, ?inst_sub_wk1 in Hwp.
          specialize (Hwp Heqs). revert Hwp.
          eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto.
          - apply dmut_bind_right_dcl; auto.
            apply dmut_assume_formula_dcl.
          - apply dmut_fresh_dcl.
            apply dmut_bind_right_dcl; auto.
            apply dmut_assume_formula_dcl.
        }
        { rewrite dmut_wp_fresh; auto. intros vl.
          rewrite dmut_wp_fresh; auto. intros vr.
          rewrite dmut_wp_bind_right; auto.
          rewrite dmut_wp_assume_formula; auto.
          unfold sub_comp. rewrite ?inst_sub_snoc. cbn - [sub_wk1].
          rewrite ?inst_subst, ?inst_sub_wk1. intros Heqs.
          specialize (Hwp (lift vl) (lift vr) Heqs). revert Hwp.
          eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto.
          - apply dmut_bind_right_dcl; auto.
            apply dmut_assume_formula_dcl.
          - apply dmut_fresh_dcl.
            apply dmut_bind_right_dcl; auto.
            apply dmut_assume_formula_dcl.
        }
    Qed.

    Lemma dmut_wp_freshen_recordpat' {Γ : PCtx} {σs : NCtx 𝑹𝑭 Ty} {Σ1 Δ : LCtx}
      (p : RecordPat σs Δ)
      (Σ2 : LCtx) (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2)
      (s2 : SymbolicState Γ Σ2) (ι2 : SymInstance Σ2) (Hpc : instpc ι2 pc2)
      (P : NamedEnv Lit σs * SymInstance Δ -> SCState Γ -> Prop) :
      dmut_wp (dmut_freshen_recordpat' id p) ζ12 pc2 s2 ι2 P <->
      forall (ts : NamedEnv Lit σs) (ιΔ : SymInstance Δ),
        record_pattern_match p ts = ιΔ -> P (ts,ιΔ) (inst ι2 s2).
    Proof.
      induction p; cbn - [dmut_wp].
      - split; cbn; auto.
        intros HP * Heq.
        subst.
        now destruct (nilView ts).
      - unfold dmut_fmap2. rewrite dmut_wp_bind; auto.
        rewrite IHp. split; intros Hwp ts ιΔ.
        + destruct (snocView ts) as [ts].
          destruct (snocView ιΔ) as [ιΔ]. cbn.
          specialize (Hwp ts ιΔ).
          remember (record_pattern_match p ts) as ιΔ'.
          intros Heq. dependent elimination Heq.
          specialize (Hwp eq_refl).
          rewrite dmut_wp_fmap, dmut_wp_sub in Hwp; auto.
          rewrite dmut_wp_freshtermvar in Hwp; auto.
          specialize (Hwp v). cbn in Hwp.
          rewrite ?inst_lift in Hwp.
          change (P (inst ι2 (subst ζ12 (lift ts)) ► (rf :: τ ↦ v) ,
                     inst ι2 (subst ζ12 (lift ιΔ')) ► (x :: τ ↦ v))
                    (inst ι2 s2)) in Hwp.
          now rewrite ?inst_subst, ?inst_lift in Hwp.
          clear. unfold sout_mapping_dcl. intros. cbn.
          change
            (inst ι1 (subst ζ01 (lift ts)) ► (rf :: τ ↦ inst ι1 a1) :: inst ι1 (subst ζ01 (lift ιΔ')) ► (x :: τ ↦ inst ι1 a1) =
             inst ι2 (subst ζ02 (lift ts)) ► (rf :: τ ↦ inst ι2 a2) :: inst ι2 (subst ζ02 (lift ιΔ')) ► (x :: τ ↦ inst ι2 a2)).
          rewrite ?inst_subst, ?inst_lift. cbn. now rewrite H1.
        + intros Heq.
          rewrite dmut_wp_fmap, dmut_wp_sub; auto.
          rewrite dmut_wp_freshtermvar; auto.
          intros v. cbn. rewrite ?inst_lift.
          change (P (inst ι2 (subst ζ12 (lift ts)) ► (rf :: τ ↦ v) ,
                     inst ι2 (subst ζ12 (lift ιΔ)) ► (x :: τ ↦ v))
                    (inst ι2 s2)).
          rewrite ?inst_subst, ?inst_lift.
          specialize (Hwp (env_snoc ts (_,_) v) (env_snoc ιΔ (_,_) v)).
          cbn in Hwp. now inster Hwp by now rewrite Heq.
          clear. unfold sout_mapping_dcl. intros. cbn.
          change
            (inst ι1 (subst ζ01 (lift ts)) ► (rf :: τ ↦ inst ι1 a1) :: inst ι1 (subst ζ01 (lift ιΔ)) ► (x :: τ ↦ inst ι1 a1) =
             inst ι2 (subst ζ02 (lift ts)) ► (rf :: τ ↦ inst ι2 a2) :: inst ι2 (subst ζ02 (lift ιΔ)) ► (x :: τ ↦ inst ι2 a2)).
          rewrite ?inst_subst, ?inst_lift. cbn. now rewrite H1.
        + clear. intros until Q; intros PQ.
          cbn - [sub_id sub_wk1]. intros HYP v. specialize (HYP v). revert HYP.
          rewrite ?inst_subst, ?inst_sub_wk1.
          rewrite <- ?sub_up1_id. cbn. rewrite ?sub_comp_id_left.
          destruct a1 as [ts0 ιΔ0], a2 as [ts2 ιΔ2]. cbn - [inst].
          admit.
    Admitted.

    Lemma dmut_wp_match_record {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Δ} (t : Term Σ1 (ty_record R))
      (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (d : DynamicMutator Γ1 Γ2 AT (Σ1 ▻▻ Δ)) (d_dcl : dmut_dcl d)
      Σ2 (ζ12 : Sub Σ1 Σ2) pc2 (s2 : SymbolicState Γ1 Σ2) (ι2 : SymInstance Σ2) (Hpc : instpc ι2 pc2)
      (P : A -> SCState Γ2 -> Prop) :
      dmut_wp (dmut_match_record p t d) ζ12 pc2 s2 ι2 P <->
      forall ts : NamedEnv (Term _) (𝑹𝑭_Ty R),
        inst (T := fun Σ => Term Σ _) (A := Lit (ty_record R)) (inst ι2 ζ12) t = 𝑹_fold (inst ι2 ts) ->
        dmut_wp d (ζ12 ►► record_pattern_match p ts) pc2 s2 ι2 P.
    Proof.
      unfold dmut_match_record. cbn.
      destruct (term_get_record_spec (subst (T := fun Σ => Term Σ _) ζ12 t)) as [ts Heqts|];
        fold_dmut_wp.
      - specialize (Heqts ι2). rewrite inst_subst in Heqts. split; auto.
        intros Hwp ts2 Heqts2. rewrite Heqts2 in Heqts.
        apply (f_equal (@𝑹_unfold R)) in Heqts.
        rewrite ?𝑹_unfold_fold in Heqts. revert Hwp.
        eapply d_dcl; rewrite ?inst_sub_id; eauto.
        unfold inst; cbn. rewrite ?env_map_cat.
        f_equal.
        change (inst ι2 (record_pattern_match p ts) = inst ι2 (record_pattern_match p ts2)).
        now rewrite ?inst_record_pattern_match, Heqts.
      - rewrite dmut_wp_bind; auto.
        split; intros Hwp.
        { intros ts Heqts.
          unfold dmut_freshen_recordpat in Hwp.
          rewrite dmut_wp_fmap in Hwp; auto.
          rewrite dmut_wp_freshen_recordpat' in Hwp; auto.
          specialize (Hwp (inst ι2 ts) _ eq_refl).
          rewrite <- inst_record_pattern_match in Hwp.
          remember (record_pattern_match p ts) as ts__R.
          cbn - [dmut_wp inst_term] in Hwp.
          rewrite subst_sub_id, inst_lift in Hwp.
          rewrite dmut_wp_bind_right, dmut_wp_assume_formula in Hwp; auto.
          cbn - [inst_term] in Hwp. fold_inst_term.
          rewrite inst_lift in Hwp. rewrite Heqts in Hwp.
          cbn in Hwp. inster Hwp by admit.
          rewrite inst_lift, dmut_wp_sub in Hwp.
          revert Hwp.
          eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; eauto.
          unfold inst; cbn.
          rewrite ?env_map_cat.
          f_equal.
          change (inst (inst ι2 ζ12) (sub_id Σ1) = inst ι2 ζ12).
          now rewrite inst_sub_id.
          change (inst (inst ι2 ζ12) (lift (inst ι2 ts__R)) = inst ι2 ts__R).
          now rewrite inst_lift.
          now apply dmut_sub_dcl.
          clear. unfold sout_mapping_dcl. destruct a1, a2; cbn - [inst_term].
          intros. fold_inst_term. subst. inversion H1. f_equal; auto.
          admit.
        }
    Admitted.

    Lemma dmut_match_enum_dcl {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
      (d : 𝑬𝑲 E -> DynamicMutator Γ1 Γ2 AT Σ1) (d_dcl : forall K, dmut_dcl (d K)) :
      dmut_dcl (dmut_match_enum t d).
    Proof.
      intros until Q; intros PQ. rewrite ?dmut_wp_match_enum; auto.
      subst. rewrite H7. eapply d_dcl; eauto.
    Qed.

    Lemma dmut_match_sum_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ x y σ τ} (s : Term Σ (ty_sum σ τ))
      (dinl : DynamicMutator Γ1 Γ2 AT (Σ ▻ (x :: σ))) (dinl_dcl : dmut_dcl dinl)
      (dinr : DynamicMutator Γ1 Γ2 AT (Σ ▻ (y :: τ))) (dinr_dcl : dmut_dcl dinr) :
      dmut_dcl (dmut_match_sum s dinl dinr).
    Proof.
      intros until Q; intros PQ. rewrite ?dmut_wp_match_sum; auto. cbn.
      intros [Hl Hr].
      split.
      - intros sl Heq. specialize (Hl (lift (inst ι2 sl))).
        inster Hl by (rewrite inst_lift; intuition). revert Hl.
        eapply dinl_dcl; rewrite ?inst_sub_snoc, ?inst_lift; auto.
        f_equal. auto.
      - intros sr Heq. specialize (Hr (lift (inst ι2 sr))).
        inster Hr by (rewrite inst_lift; intuition). revert Hr.
        eapply dinr_dcl; rewrite ?inst_sub_snoc, ?inst_lift; auto.
        f_equal. auto.
    Qed.

    Lemma dmut_match_pair_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 x y σ τ} (s : Term Σ1 (ty_prod σ τ))
      (d : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (d_dcl : dmut_dcl d) :
      dmut_dcl (dmut_match_pair s d).
    Proof.
      intros until Q; intros PQ. rewrite ?dmut_wp_match_pair; auto.
      intros Hwp sl sr Heqs. specialize (Hwp (lift (inst ι2 sl)) (lift (inst ι2 sr))).
      rewrite ?inst_lift in Hwp. rewrite <- H7 in Heqs. specialize (Hwp Heqs). revert Hwp.
      eapply d_dcl; unfold sub_comp; rewrite ?inst_sub_snoc, ?inst_lift; auto.
      f_equal; auto. f_equal; auto.
    Qed.

    Lemma dmut_match_record_dcl {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Δ} (t : Term Σ1 (ty_record R))
      (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (d : DynamicMutator Γ1 Γ2 AT (Σ1 ▻▻ Δ)) (d_dcl : dmut_dcl d) :
      dmut_dcl (@dmut_match_record AT R Γ1 Γ2 Σ1 Δ p t d).
    Proof.
      intros until Q; intros PQ. rewrite ?dmut_wp_match_record; auto.
      intros Hwp ζ__R Heqs. specialize (Hwp (lift (inst ι2 ζ__R))).
      rewrite ?inst_lift in Hwp. rewrite <- H7 in Heqs. specialize (Hwp Heqs). revert Hwp.
      eapply d_dcl; eauto. unfold inst at 1 3; cbn. rewrite ?env_map_cat.
      f_equal. exact H7. admit.
    Admitted.

    Lemma dmut_produce_chunk_dcl {Γ Σ} (c : Chunk Σ) :
      dmut_dcl (Γ1 := Γ) (dmut_produce_chunk c).
    Proof.
      unfold dmut_produce_chunk, dmut_modify_heap, dmut_modify.
      apply dmut_state_dcl. destruct s1 as [δ1 h1], s2 as [δ2 h2].
      cbn - [instantiate_list]. intros. inversion H0. cbn.
      change (List.map (inst ?ι) ?h) with (inst ι h).
      rewrite ?inst_subst. congruence.
    Qed.

    Lemma dmut_produce_dcl {Γ Σ} (asn : Assertion Σ) :
      dmut_dcl (Γ1 := Γ) (dmut_produce asn).
    Proof.
      induction asn; cbn.
      - apply dmut_assume_formula_dcl.
      - apply dmut_produce_chunk_dcl.
      - apply dmut_demonic_binary_dcl; apply dmut_bind_right_dcl;
          unfold dmut_assume_term; auto using dmut_assume_formula_dcl.
      - now apply dmut_match_enum_dcl.
      - now apply dmut_match_sum_dcl.
      - admit.
      - now apply dmut_match_pair_dcl.
      - admit.
      - now apply dmut_match_record_dcl.
      - admit.
      - now apply dmut_bind_right_dcl.
      - now apply dmut_fresh_dcl.
      - admit.
    Admitted.

    Lemma dmut_consume_chunk_dcl {Γ Σ} (c : Chunk Σ) :
      dmut_dcl (Γ1 := Γ) (dmut_consume_chunk c).
    Proof.
      unfold dmut_consume_chunk.
      apply dmut_bind_dcl.
      apply dmut_state_dcl. destruct s1, s2; cbn.
      intros. congruence.
      intros until Q. intros PQ.
    Admitted.

    Lemma dmut_consume_dcl {Γ Σ} (asn : Assertion Σ) :
      dmut_dcl (Γ1 := Γ) (dmut_consume asn).
    Proof.
      induction asn; cbn.
      - apply dmut_assert_formula_dcl.
      - apply dmut_consume_chunk_dcl.
      - apply dmut_demonic_binary_dcl; apply dmut_bind_right_dcl;
          unfold dmut_assume_term; auto using dmut_assume_formula_dcl.
      - now apply dmut_match_enum_dcl.
      - now apply dmut_match_sum_dcl.
      - admit.
      - now apply dmut_match_pair_dcl.
      - admit.
      - now apply dmut_match_record_dcl.
      - admit.
      - now apply dmut_bind_right_dcl.
      - admit.
      - admit.
    Admitted.

    Lemma dmut_exec_dcl {Γ τ Σ} (s : Stm Γ τ) :
      dmut_dcl (Σ0 := Σ) (dmut_exec s).
    Proof. Admitted.

    Definition APPROX Γ1 Γ2 AT A {instA : Inst AT A} : Type :=
      forall Σ (ι : SymInstance Σ),
        DynamicMutator Γ1 Γ2 AT Σ -> SCMut Γ1 Γ2 A -> Prop.
    Arguments APPROX _ _ _ _ {_}.

    Definition bapprox {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
      fun Σ0 ι0 dm sm =>
        forall Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (ι1 : SymInstance Σ1) POST s1,
          ι0 = inst ι1 ζ01 ->
          instpc ι1 pc1 ->
          dmut_wp dm ζ01 pc1 s1 ι1 POST ->
          scmut_wp sm POST (inst ι1 s1).

    Definition bapprox2 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
      fun Σ0 ι0 dm sm =>
        forall POST sc,
          dmut_wp dm (lift ι0) nil (lift sc) env_nil POST ->
          scmut_wp sm POST sc.

    Lemma bapprox_bapprox2 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (dm_dcl : dmut_dcl dm) (sm : SCMut Γ1 Γ2 A) :
      bapprox ι dm sm <-> bapprox2 ι dm sm.
    Proof.
      unfold bapprox, bapprox2. split; intros HYP.
      - intros POST sc Hwp.
        specialize (HYP ctx_nil (lift ι) nil env_nil POST (lift sc)).
        rewrite ?inst_lift in HYP. apply HYP; auto. constructor.
      - intros ? ? ? ? ? ? Hι Hpc Hwp. specialize (HYP POST (inst ι1 s1)).
        apply HYP. revert Hwp.
        apply (dm_dcl Σ1 ε ζ01 _ _ (lift ι1)); rewrite ?inst_lift; auto.
        constructor.
    Qed.

    Definition inst_dmut {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (d : DynamicMutator Γ1 Γ2 AT Σ) : SCMut Γ1 Γ2 A :=
      fun sc => inst_symoutcome ι (d Σ (sub_id Σ) nil (lift sc)).
    Definition inst_dmut' {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (d : DynamicMutator Γ1 Γ2 AT Σ) : SCMut Γ1 Γ2 A :=
      fun sc => inst_symoutcome env_nil (d ctx_nil (lift ι) nil (lift sc)).

    Definition bapprox3 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
      fun Σ0 ι0 dm sm =>
        forall POST sc,
          scmut_wp (inst_dmut ι0 dm) POST sc ->
          scmut_wp sm POST sc.

    Definition bapprox4 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
      fun Σ0 ι0 dm sm =>
        forall POST sc,
          scmut_wp (inst_dmut' ι0 dm) POST sc ->
          scmut_wp sm POST sc.

    Lemma bapprox_bapprox3 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (dm_dcl : dmut_dcl dm) (sm : SCMut Γ1 Γ2 A) :
      bapprox ι dm sm <-> bapprox3 ι dm sm.
    Proof.
      split; unfold bapprox, bapprox3; intros HYP.
      - intros POST sc Hwp.
        specialize (HYP Σ (sub_id _) nil ι POST (lift sc)).
        inster HYP by rewrite ?inst_sub_id; constructor.
        rewrite inst_lift in HYP. apply HYP.
        unfold dmut_wp. rewrite sout_wp_wp'. exact Hwp.
      - intros ? ? ? ? ? ? Hι Hpc Hwp. apply HYP.
        unfold scmut_wp, inst_dmut.
        change (sout_wp' (dm Σ (sub_id Σ) nil (lift (inst ι1 s1))) ι
                         (fun X : SCMutResult Γ2 A => POST (scmutres_value X) (scmutres_state X))).
        rewrite <- sout_wp_wp'. fold_dmut_wp. revert Hwp.
        eapply dm_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto.
        constructor.
    Qed.

    Lemma bapprox_bapprox4 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (dm_dcl : dmut_dcl dm) (sm : SCMut Γ1 Γ2 A) :
      bapprox ι dm sm <-> bapprox4 ι dm sm.
    Proof.
      split; unfold bapprox, bapprox4; intros HYP.
      - intros POST sc Hwp.
        specialize (HYP ctx_nil (lift ι) nil env_nil POST (lift sc)).
        inster HYP by rewrite ?inst_lift; constructor.
        rewrite inst_lift in HYP. apply HYP.
        unfold dmut_wp. rewrite sout_wp_wp'. exact Hwp.
      - intros ? ? ? ? ? ? Hι Hpc Hwp. apply HYP.
        unfold scmut_wp, inst_dmut'.
        change (sout_wp' (dm ctx_nil (lift ι) nil (lift (inst ι1 s1))) env_nil
                         (fun X : SCMutResult Γ2 A => POST (scmutres_value X) (scmutres_state X))).
        rewrite <- sout_wp_wp'. fold_dmut_wp. revert Hwp.
        eapply dm_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto.
        constructor.
    Qed.

    Lemma bapprox_demonic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
          (dm1 dm2 : DynamicMutator Γ1 Γ2 AT Σ) (sm1 sm2 : SCMut Γ1 Γ2 A) :
      bapprox ι dm1 sm1 ->
      bapprox ι dm2 sm2 ->
      bapprox ι (dmut_demonic_binary dm1 dm2) (scmut_demonic_binary sm1 sm2).
    Proof. unfold bapprox. cbn. intuition. Qed.

    Lemma bapprox_angelic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
          (dm1 dm2 : DynamicMutator Γ1 Γ2 AT Σ) (sm1 sm2 : SCMut Γ1 Γ2 A) :
      bapprox ι dm1 sm1 ->
      bapprox ι dm2 sm2 ->
      bapprox ι (dmut_angelic_binary dm1 dm2) (scmut_angelic_binary sm1 sm2).
    Proof. unfold bapprox. cbn. intuition. Qed.

    Lemma bapprox_fresh {Γ Σ ς τ} (ι : SymInstance Σ)
          (dm : DynamicMutator Γ Γ Unit (Σ ▻ (ς,τ))) (d_dcl : dmut_dcl dm)
          (sm : Lit τ -> SCMut Γ Γ unit) :
      (forall v, bapprox (env_snoc ι _ v) dm (sm v)) ->
      bapprox ι
        (dmut_fresh ς τ dm)
        (scmut_demonic sm).
    Proof.
      unfold bapprox, scmut_demonic. intros HYP * Hι Hpc Hwp vτ.
      apply (HYP vτ _ (sub_snoc ζ01 (ς :: τ) (term_lit τ vτ)) pc1); auto.
      subst ι; reflexivity.
      unfold dmut_fresh in Hwp. cbn in Hwp. specialize (Hwp vτ). revert Hwp.
      eapply (d_dcl _ _ _ _ _ (sub_snoc (sub_id Σ1) (fresh Σ1 (Some ς) :: τ) (term_lit τ vτ))); auto.
      - now rewrite inst_sub_snoc, inst_sub_id.
      - now rewrite inst_subst, inst_sub_wk1.
      - now rewrite inst_subst, inst_sub_wk1.
      - unfold sub_comp. now rewrite ?inst_sub_snoc, ?inst_subst, ?inst_sub_wk1.
    Qed.

    Lemma bapprox2_fresh {Γ Σ ς τ} (ι : SymInstance Σ)
          (dm : DynamicMutator Γ Γ Unit (Σ ▻ (ς,τ))) (d_dcl : dmut_dcl dm)
          (sm : Lit τ -> SCMut Γ Γ unit) :
      (forall v, bapprox2 (env_snoc ι _ v) dm (sm v)) ->
      bapprox2 ι
        (dmut_fresh ς τ dm)
        (scmut_demonic sm).
    Proof.
      unfold bapprox2, scmut_demonic. intros HYP POST sc Hwp vτ. apply HYP.
      rewrite dmut_wp_fresh in Hwp; eauto. apply (Hwp vτ). constructor.
    Qed.

    Lemma bapprox_pure {AT A} `{InstLaws AT A} {Γ Σ} (ι : SymInstance Σ) (t : AT Σ) (a : A) :
      a = inst ι t ->
      bapprox ι (dmut_pure (Γ := Γ) t) (scmut_pure a).
    Proof.
      unfold bapprox. intros -> * -> Hpc. cbn.
      now rewrite inst_subst.
    Qed.

    Lemma bapprox_block {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) :
      bapprox ι (@dmut_block Γ1 Γ2 AT Σ) scmut_block.
    Proof. unfold bapprox; auto. Qed.

    Lemma bapprox_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B}
      {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (sma : SCMut Γ1 Γ2 A)
      (dmf : dmut_arrow Γ2 Γ3 AT BT Σ0)
      (dmf_dcl : dmut_arrow_dcl dmf)
      (smf : A -> SCMut Γ2 Γ3 B) :
      bapprox ι0 dma sma ->
      (forall (a0 : AT Σ0),
          bapprox ι0 (dmf Σ0 (sub_id _) a0) (smf (inst ι0 a0))) ->
      bapprox ι0 (dmut_bind dma dmf) (scmut_bind sma smf).
    Proof.
      unfold bapprox. intros Hapa Hapf * Hι Hpc.
      rewrite dmut_wp_bind; eauto. rewrite scmut_wp_bind.
      intros Hwp. eapply Hapa; eauto. revert Hwp.
      apply dmut_wp_monotonic. intros a sc2 Hwp.
      apply Hapf in Hwp; auto. revert Hwp. now rewrite ?inst_lift.
    Qed.

    Lemma bapprox_bind_right {AT A BT B} `{InstLaws AT A, InstLaws BT B}
      {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (sma : SCMut Γ1 Γ2 A)
      (dmb : DynamicMutator Γ2 Γ3 BT Σ0) (dmb_dcl : dmut_dcl dmb) (smb : SCMut Γ2 Γ3 B) :
      bapprox ι0 dma sma ->
      bapprox ι0 dmb smb ->
      bapprox ι0 (dmut_bind_right dma dmb) (scmut_bind_right sma smb).
    Proof.
      unfold bapprox. intros A1 A2 * -> Hpc1.
      rewrite dmut_wp_bind_right; auto.
      unfold scmut_bind_right. rewrite scmut_wp_bind.
      intros Hwp; eapply A1 in Hwp; eauto. revert Hwp.
      apply scmut_wp_monotonic; intros a s2.
      intros Hwp; eapply A2 in Hwp; eauto. revert Hwp. 
      now rewrite inst_lift.
    Qed.

    Lemma bapprox_bind_left {AT A BT B} `{InstLaws AT A, InstLaws BT B}
      {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (sma : SCMut Γ1 Γ2 A)
      (dmb : DynamicMutator Γ2 Γ3 BT Σ0) (dmb_dcl : dmut_dcl dmb) (smb : SCMut Γ2 Γ3 B) :
      bapprox ι0 dma sma ->
      bapprox ι0 dmb smb ->
      bapprox ι0 (dmut_bind_left dma dmb) (scmut_bind_left sma smb).
    Proof.
      intros A1 A2. unfold bapprox. intros * -> Hpc1.
      rewrite dmut_wp_bind_left; auto.
      unfold scmut_bind_left. rewrite scmut_wp_bind.
      intros Hwp; eapply A1 in Hwp; eauto. revert Hwp.
      apply scmut_wp_monotonic; intros a s2. rewrite scmut_wp_bind.
      intros Hwp; eapply A2 in Hwp; eauto. revert Hwp.
      now rewrite inst_lift.
    Qed.

    Lemma bapprox2_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      bapprox2
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assume_formula fml)
        (scmut_assume_formula ι fml).
    Proof.
      unfold bapprox2. intros POST sc.
      rewrite dmut_wp_assume_formula; auto. rewrite ?inst_lift.
      intuition.
      constructor.
    Qed.

    Lemma bapprox_angelic {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ Σ} (ι : SymInstance Σ)
      (dm : AT Σ -> DynamicMutator Γ Γ BT Σ)
      (sm : A -> SCMut Γ Γ B) :
      (forall a, bapprox ι (dm a) (sm (inst ι a))) ->
      bapprox ι
        (dmut_angelic dm)
        (scmut_angelic sm).
    Proof.
      unfold bapprox, dmut_angelic.
      intros HYP * Hι Hpc [a Hwp]. rewrite scmut_wp_angelic. exists (inst ι a).
      change (dmut_wp (dm a) ζ01 pc1 s1 ι1 POST) in Hwp.
      revert Hwp. apply HYP; auto.
    Qed.

    Lemma bapprox_sub {AT A} `{Inst AT A, Subst AT} {Γ Σ0 Σ1} (ζ01 : Sub Σ0 Σ1)
      (d : DynamicMutator Γ Γ AT Σ0) (s : SCMut Γ Γ A) (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1) :
      ι0 = inst ι1 ζ01 ->
      bapprox ι0 d s -> bapprox ι1 (dmut_sub ζ01 d) s.
    Proof.
      intros Hι0 Hap. unfold bapprox. intros * Hι1 Hpc2.
      rewrite dmut_wp_sub. apply Hap; auto.
      unfold sub_comp; rewrite inst_subst; now subst.
    Qed.

    Lemma bapprox_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      bapprox
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assume_formula fml)
        (scmut_assume_formula ι fml).
    Proof.
      unfold bapprox. intros * -> Hpc Hwp Hfml. revert Hwp.
      rewrite dmut_wp_assume_formula; eauto. cbn. intuition.
    Qed.

    Lemma bapprox_assert_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      bapprox
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assert_formula fml)
        (scmut_assert_formula ι fml).
    Proof.
      unfold bapprox. intros * Hι Hpc1.
      rewrite dmut_wp_assert_formula; eauto.
      cbn. intuition.
    Qed.

    Lemma bapprox_state {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0} (ι0 : SymInstance Σ0)
          (f : forall Σ1 (ζ01 : Sub Σ0 Σ1), SymbolicState Γ1 Σ1 -> Pair AT (SymbolicState Γ2) Σ1)
          (g : SCState Γ1 -> A * SCState Γ2)
          (fg : forall Σ1 ζ01 s1 ι1,
                 ι0 = inst ι1 ζ01 -> inst ι1 (f Σ1 ζ01 s1) = g (inst ι1 s1)) :
      bapprox ι0 (dmut_state f) (scmut_state g).
    Proof.
      unfold bapprox. intros * Hι Hpc.
      specialize (fg Σ1 ζ01 s1 ι1 Hι).
      cbn. rewrite dmut_wp_state.
      destruct (f Σ1 ζ01 s1) as [a1 s21], (g (inst ι1 s1)) as [a sc2]; cbn.
      inversion fg. now subst.
    Qed.

    Lemma bapprox_produce_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
      bapprox
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce_chunk c)
        (scmut_produce_chunk (inst ι c)).
    Proof.
      unfold bapprox, dmut_produce_chunk, scmut_produce_chunk.
      unfold scmut_wp.
      intros * -> Hpc1. destruct s1. cbn. now rewrite inst_subst.
    Qed.

    Lemma bapprox_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
      (dm : Lit (ty_enum E) -> DynamicMutator Γ1 Γ2 AT Σ1) (dm_dcl : forall x, dmut_dcl (dm x))
      (sm : Lit (ty_enum E) -> SCMut Γ1 Γ2 A)
      (ι : SymInstance Σ1) :
      (forall k, bapprox ι (dm k) (sm k)) ->
      bapprox
        ι
        (dmut_match_enum t dm)
        (scmut_match_enum (inst (T := fun Σ => Term Σ (ty_enum E)) ι t) sm).
    Proof.
      unfold bapprox. intros Hap * ? Hpc. subst.
      rewrite dmut_wp_match_enum; auto. now apply Hap.
    Qed.

    Lemma bapprox_match_sum {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} {x y : 𝑺} {σ τ} (s : Term Σ1 (ty_sum σ τ))
      (dinl : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (x :: σ))) (dinl_dcl : dmut_dcl dinl)
      (dinr : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (y :: τ))) (dinr_dcl : dmut_dcl dinr)
      (sinl : Lit σ -> SCMut Γ1 Γ2 A) (sinr : Lit τ -> SCMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
      (forall v, bapprox (env_snoc ι _ v) dinl (sinl v)) ->
      (forall v, bapprox (env_snoc ι _ v) dinr (sinr v)) ->
      bapprox
        ι
        (dmut_match_sum s dinl dinr)
        (scmut_match_sum (inst (T := fun Σ => Term Σ (ty_sum σ τ)) (A := Lit σ + Lit τ) ι s) sinl sinr).
    Proof.
      unfold bapprox. intros Hapl Hapr * ? Hpc.
      rewrite dmut_wp_match_sum; auto. intros [Hl Hr].
      destruct (inst ι s) eqn:Heqs; [ clear Hr | clear Hl ]; subst ι.
      + specialize (Hl (term_lit σ l) Heqs). revert Hl. now apply Hapl.
      + specialize (Hr (term_lit τ l) Heqs). revert Hr. now apply Hapr.
    Qed.

    Lemma bapprox_match_pair {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} {x y : 𝑺} {σ τ} (s : Term Σ1 (ty_prod σ τ))
      (dm : DynamicMutator Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (dm_dcl : dmut_dcl dm)
      (sm : Lit σ -> Lit τ -> SCMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
      (forall vl vr, bapprox (env_snoc (env_snoc ι _ vl) _ vr) dm (sm vl vr)) ->
      bapprox
        ι
        (dmut_match_pair s dm)
        (scmut_match_pair (inst (T := fun Σ => Term Σ (ty_prod σ τ)) (A := Lit σ * Lit τ) ι s) sm).
    Proof.
      unfold bapprox. intros Hap * ? Hpc.
      rewrite dmut_wp_match_pair; auto. intros Hwp.
      destruct (inst ι s) as [vl vr] eqn:Heqs. subst ι.
      specialize (Hwp (lift vl) (lift vr) Heqs). revert Hwp.
      now apply Hap.
    Qed.

    Lemma bapprox_match_record {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ0 Δ} (t : Term Σ0 (ty_record R))
      (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (dm : DynamicMutator Γ1 Γ2 AT (Σ0 ▻▻ Δ)) (dm_dcl : dmut_dcl dm)
      (sm : SymInstance Δ -> SCMut Γ1 Γ2 A) (ι : SymInstance Σ0) :
      (forall ι__Δ : SymInstance Δ, bapprox (env_cat ι ι__Δ) dm (sm ι__Δ)) ->
      bapprox
        ι
        (dmut_match_record p t dm)
        (scmut_match_record p (inst (T := fun Σ => Term Σ (ty_record R)) ι t) sm).
    Proof.
      unfold bapprox. intros Hap * Hι Hpc.
      rewrite dmut_wp_match_record; auto. intros Hwp.
      unfold scmut_match_record.
      specialize (Hwp (lift (𝑹_unfold (inst (T := fun Σ => Term Σ _) ι t)))).
      inster Hwp by now rewrite inst_lift, 𝑹_fold_unfold, Hι.
      eapply Hap; eauto. cbn [Lit].
      generalize (𝑹_unfold (inst (T := fun Σ => Term Σ (ty_record R)) (A := 𝑹𝑻 R) ι t)).
      subst. clear. intros ts. unfold inst at 2; cbn.
      rewrite env_map_cat. f_equal.
      change (record_pattern_match p ts = inst ι1 (record_pattern_match p (lift ts))).
      now rewrite inst_record_pattern_match, inst_lift.
    Qed.

    Lemma bapprox_produce {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) :
      bapprox
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce asn)
        (scmut_produce ι asn).
    Proof.
      induction asn; cbn - [subst].
      - apply bapprox_assume_formula.
      - apply bapprox_produce_chunk.
      - apply bapprox_demonic_binary; apply bapprox_bind_right;
          try apply bapprox_assume_formula; auto using dmut_produce_dcl.
      - apply bapprox_match_enum; auto using dmut_produce_dcl.
      - apply bapprox_match_sum; auto using dmut_produce_dcl.
      - admit.
      - apply bapprox_match_pair; auto using dmut_produce_dcl.
      - admit.
      - apply bapprox_match_record; auto using dmut_produce_dcl.
      - admit.
      - apply bapprox_bind_right; auto using dmut_produce_dcl.
      - apply bapprox_fresh; auto using dmut_produce_dcl.
      - unfold bapprox. intuition.
    Admitted.

    Lemma match_chunk_eqb_spec {Σ} (ce cr : Chunk Σ) (fmls : List Formula Σ) :
      OptionSpec
        (fun fmls2 =>
           forall ι : SymInstance Σ,
             instpc ι fmls2 ->
             inst ι ce = inst ι cr /\ instpc ι fmls)
        True
        (Soundness.MUT.match_chunk_eqb ce cr fmls).
    Proof.
      destruct ce, cr; cbn; try constructor; auto.
      - destruct (eq_dec p p0); cbn.
        + destruct e; cbn. admit.
        + now constructor.
      - destruct (eq_dec_het r r0); cbn.
        + dependent elimination e; cbn. admit.
        + now constructor.
    Admitted.

    Lemma heap_extractions_map {A B} (f : A -> B) (h : list A) :
      heap_extractions (List.map f h) = List.map (base.prod_map f (List.map f)) (heap_extractions h).
    Proof.
      induction h; cbn.
      - reflexivity.
      - f_equal.
        rewrite IHh.
        rewrite ?List.map_map.
        apply List.map_ext.
        intros [x xs]. reflexivity.
    Qed.

    Lemma bapprox_consume_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
      bapprox
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_consume_chunk c)
        (scmut_consume_chunk (inst ι c)).
    Proof.
      unfold bapprox, dmut_consume_chunk, scmut_consume_chunk.
      intros * Hι Hpc.
      unfold dmut_get_heap, scmut_get_heap, scmut_state_heap.
      rewrite dmut_wp_bind, scmut_wp_bind; auto.
      rewrite dmut_wp_state.
      rewrite dmut_wp_bind; auto.
      rewrite dmut_wp_angelic_list. intros [[Δpc h'] [HIn Hwp]].
      rewrite subst_sub_id in HIn.
      cbn - [dmut_wp] in Hwp. rewrite dmut_wp_bind_right in Hwp; auto.
      rewrite dmut_wp_assert_formulas in Hwp; auto.
      rewrite ?inst_lift in Hwp. destruct Hwp as [HΔpc Hwp].
      destruct s1 as [δ1 h1]. cbn [symbolicstate_heap] in HIn. cbn in Hwp.
      rewrite ?inst_subst, ?inst_lift in Hwp.
      rewrite scmut_wp_state; cbn - [scmut_wp extract_chunk_eqb].
      unfold scmut_wp, scmut_angelick_list.
      rewrite outcome_satisfy_angelick_list.
      left. exists (inst ι h').
      split.
      - apply base.elem_of_list_In in HIn.
        unfold Soundness.MUT.extract_chunk_eqb, extract_chunk_eqb in *.
        unfold base.omap in HIn.
        apply list.elem_of_list_omap in HIn.
        destruct HIn as [[c' h''] [HIn Heq]].
        apply List.in_map_iff.
        destruct (match_chunk_eqb_spec c c' nil); cbn in Heq; try discriminate.
        inversion Heq. subst h'' a. clear Heq.
        specialize (H ι). inster H by (subst; auto). destruct H as [H _].
        exists (inst ι c', inst (T := List Chunk) ι h'). cbn.
        apply base.elem_of_list_In in HIn.
        split; auto. apply List.filter_In.
        split.
        + unfold lift, inst in HIn. cbn in HIn.
          rewrite List.map_map in HIn.
          rewrite heap_extractions_map in HIn.
          rewrite List.in_map_iff in HIn.
          destruct HIn as [[c1 h1'] [Heq HIn]].
          unfold base.prod_map in Heq; cbn in Heq.
          rewrite <- List.map_map in Heq.
          change (lift (inst ι1 c1) :: lift (inst ι1 h1') = c' :: h') in Heq.
          inversion Heq. subst. clear Heq.
          rewrite ?inst_lift in *.
          unfold inst at 3. cbn.
          rewrite heap_extractions_map.
          rewrite List.in_map_iff.
          exists (c1, h1'). split; auto.
        + destruct (MUT.match_chunk_eqb_spec (inst ι c) (inst ι c')); auto.
      - cbn; now subst.
      - admit.
      - admit.
    Admitted.

    Lemma bapprox_consume {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) :
      bapprox
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_consume asn)
        (scmut_consume ι asn).
    Proof.
      induction asn; cbn - [subst].
      - apply bapprox_assert_formula.
      - apply bapprox_consume_chunk.
      - apply bapprox_demonic_binary; apply bapprox_bind_right;
          auto using dmut_consume_dcl.
        apply bapprox_assume_formula.
        apply bapprox_assume_formula.
      - apply bapprox_match_enum; auto using dmut_consume_dcl.
      - apply bapprox_match_sum; auto using dmut_consume_dcl.
      - admit.
      - apply bapprox_match_pair; auto using dmut_consume_dcl.
      - admit.
      - apply bapprox_match_record; auto using dmut_consume_dcl.
      - admit.
      - apply bapprox_bind_right; auto using dmut_consume_dcl.
      - apply (bapprox_angelic (AT := fun Σ => Term Σ τ)). intros t.
        eapply bapprox_sub; eauto. now rewrite inst_sub_snoc, inst_sub_id.
      - admit.
    Admitted.

    Lemma bapprox_call {Γ Δ τ Σ} (c : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) (ι : SymInstance Σ) :
      bapprox ι (@dmut_call Γ Δ τ Σ c ts) (scmut_call c (inst ι ts)).
    Proof.
      destruct c as [Σ__c δ pre result post]; cbn [dmut_call scmut_call].
      apply bapprox_angelic. intros ζ. unfold bapprox. intros * Hι Hpc.
      rewrite dmut_wp_bind_right; auto.
      rewrite dmut_wp_assert_formulas; auto.
      intros [Hfmls Hwp]. rewrite dmut_wp_sub in Hwp.
      rewrite scmut_wp_angelic.
      assert (inst ι ts = inst (inst ι ζ) δ) as Heq.
      { rewrite <- Hι in Hfmls. clear - Hfmls.
        induction ts; [destruct (nilView δ) | destruct (snocView δ)].
        - reflexivity.
        - cbn - [inst] in Hfmls.
          rewrite inst_pathcondition_cons in Hfmls.
          destruct Hfmls as [Hfml Hfmls].
          cbn. f_equal.
          + now apply IHts.
          + now rewrite <- inst_subst.
      }
      exists Heq.
      rewrite dmut_wp_bind_right in Hwp; auto.
      eapply bapprox_consume in Hwp; eauto. revert Hwp.
      unfold sub_comp, scmut_bind_right.
      rewrite inst_subst, inst_lift, scmut_wp_bind.
      subst ι. apply scmut_wp_monotonic.
      intros _ sc__consume Hwp.
      rewrite dmut_wp_fresh in Hwp; auto.
      rewrite scmut_wp_demonic. intros v.
      specialize (Hwp v).
      rewrite scmut_wp_bind.
      rewrite dmut_wp_bind_right in Hwp; auto.
      eapply bapprox_produce in Hwp; eauto. revert Hwp.
      rewrite inst_sub_snoc, inst_subst, inst_lift. cbn.
      apply scmut_wp_monotonic.
      intros _ sc__produce.
      now rewrite inst_lift.
      apply dmut_pure_dcl.
      apply dmut_bind_right_dcl.
      apply dmut_produce_dcl.
      apply dmut_pure_dcl.
      apply dmut_fresh_dcl.
      apply dmut_bind_right_dcl.
      apply dmut_produce_dcl.
      apply dmut_pure_dcl.
      apply dmut_sub_dcl.
      apply dmut_bind_right_dcl.
      apply dmut_consume_dcl.
      apply dmut_fresh_dcl.
      apply dmut_bind_right_dcl.
      apply dmut_produce_dcl.
      apply dmut_pure_dcl.
    Qed.

    Lemma eval_exp_inst {Γ Σ τ} (ι : SymInstance Σ) (δΓΣ : SymbolicLocalStore Γ Σ) (e : Exp Γ τ) :
      eval e (inst ι δΓΣ) = inst ι (symbolic_eval_exp δΓΣ e).
    Proof.
      induction e; cbn; repeat f_equal; auto.
      { unfold inst; cbn. now rewrite env_lookup_map. }
      2: {
        induction es as [|eb n es IHes]; cbn in *.
        { reflexivity. }
        { destruct X as [-> Heqs].
          change (inst_term ?ι ?t) with (inst ι t).
          destruct (inst ι (symbolic_eval_exp δΓΣ eb));
            cbn; f_equal; auto.
        }
      }
      all: induction es; cbn in *; destruct_conjs; f_equal; auto.
    Qed.

    Lemma bapprox_eval_exp {Γ Σ τ} (e : Exp Γ τ) (ι : SymInstance Σ) :
      bapprox ι (dmut_eval_exp e) (scmut_eval_exp e).
    Proof.
      unfold dmut_eval_exp, scmut_eval_exp, dmut_gets_local, dmut_gets, scmut_gets_local, scmut_state_local.
      apply bapprox_state. intros. destruct s1. cbn. f_equal.
      now rewrite eval_exp_inst.
    Qed.

    Lemma bapprox_pushpop {AT A} `{InstLaws AT A} {Γ1 Γ2 x σ Σ} (ι : SymInstance Σ) (a : Term Σ σ)
      (dm : DynamicMutator (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) (dm_dcl : dmut_dcl dm)
      (sm : SCMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) A) :
      bapprox ι dm sm ->
      bapprox ι (dmut_pushpop a dm) (scmut_pushpop (inst ι a) sm).
    Proof.
      intros Hap. unfold dmut_pushpop, scmut_pushpop.
      apply bapprox_bind_right; auto.
      apply dmut_bind_left_dcl; auto.
      apply dmut_pop_local_dcl.
      unfold
        dmut_push_local, dmut_modify_local, dmut_state_local,
        scmut_push_local, scmut_modify_local, scmut_state_local.
      apply bapprox_state. destruct s1 as [δ1 h1]; intros. cbn.
      f_equal. f_equal. subst. now rewrite <- inst_subst.
      apply bapprox_bind_left; eauto.
      apply dmut_pop_local_dcl.
      unfold
        dmut_pop_local, dmut_modify_local, dmut_state_local,
        scmut_pop_local, scmut_modify_local, scmut_state_local.
      apply bapprox_state. destruct s1 as [δ1 h1]; intros. cbn.
      f_equal. f_equal. subst. now destruct (snocView δ1).
    Qed.

    Lemma bapprox_pushspops {AT A} `{InstLaws AT A} {Γ1 Γ2 Δ Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT Σ) (dm_dcl : dmut_dcl dm)
      (sm : SCMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) (Hap : bapprox ι dm sm) :
      forall (δ__sym : SymbolicLocalStore Δ Σ) (δ__sc : LocalStore Δ),
        δ__sc = inst ι δ__sym ->
        bapprox ι (dmut_pushspops δ__sym dm) (scmut_pushspops δ__sc sm).
    Proof. Admitted.

    Lemma bapprox_exec {Γ σ} (s : Stm Γ σ) :
      forall Σ (ι : SymInstance Σ),
        bapprox ι (dmut_exec s) (scmut_exec s).
    Proof.
      induction s; cbn [dmut_exec scmut_exec]; intros Σ ι.
      - unfold bapprox. cbn. auto.
      - now apply bapprox_eval_exp.
      - apply bapprox_bind; auto. admit.
        intros a. apply bapprox_pushpop; auto.
        apply dmut_exec_dcl; auto.
      - apply bapprox_pushspops;
          rewrite ?inst_lift;
          auto using dmut_exec_dcl.
      - apply bapprox_bind; auto. admit.
        intros a.
        apply bapprox_bind_right; auto.
        apply dmut_pure_dcl.
        unfold
          dmut_modify_local, dmut_state_local,
          scmut_modify_local, scmut_state_local.
        apply bapprox_state.
        destruct s1 as [δ1 h1]; intros * ->; cbn.
        f_equal. f_equal. rewrite <- inst_subst.
        unfold inst at 1; cbn.
        now rewrite env_map_update.
        now apply bapprox_pure.
      - destruct (CEnv f).
        + apply bapprox_bind; auto. admit. admit.
          intros ?. apply bapprox_call.
        + admit.
      - apply bapprox_bind. admit.
        { apply bapprox_state. destruct s1; cbn; auto. }
        intros δ0. apply bapprox_bind_right.
        apply dmut_bind_left_dcl. apply dmut_exec_dcl.
        { apply dmut_state_dcl.
          destruct s1, s2; intros ? ? -> Heqs Heqζ; inversion Heqs; cbn in *.
          rewrite ?inst_subst. f_equal. f_equal; congruence. }
        { apply bapprox_state. destruct s1; cbn; intros.
          now rewrite inst_subst, inst_lift. }
        admit.
      - apply bapprox_bind. admit. admit. intros args.
        apply bapprox_call.
      - admit.
      - apply bapprox_bind_right; auto. apply dmut_exec_dcl.
      - apply bapprox_bind. admit.
        apply bapprox_eval_exp.
        intros t. admit.
      - apply bapprox_block.
      - admit.
      - apply bapprox_bind. admit.
        apply bapprox_eval_exp.
        intros t. apply bapprox_match_sum. admit. admit.
        + intros ?. apply bapprox_pushpop; auto using dmut_exec_dcl.
        + intros ?. apply bapprox_pushpop; auto using dmut_exec_dcl.
      - apply bapprox_bind. admit.
        apply bapprox_eval_exp.
        intros t. apply bapprox_match_pair. admit.
        intros ? ?. apply bapprox_pushspops; auto using dmut_exec_dcl.
      - apply bapprox_bind. admit.
        apply bapprox_eval_exp.
        intros t. admit.
      - admit.
      - admit.
      - admit.
      - apply (bapprox_angelic (AT := fun Σ => Term Σ τ)).
        intros t. apply bapprox_bind_right. admit.
        (* apply bapprox_consume_chunk. *)
        admit.
        apply bapprox_bind_right. apply dmut_pure_dcl.
        apply (bapprox_produce_chunk (chunk_ptsreg reg t)).
        now apply bapprox_pure.
      - apply bapprox_bind. admit.
        apply bapprox_eval_exp.
        intros t.
        apply (bapprox_angelic (AT := fun Σ => Term Σ τ)).
        intros t'. apply bapprox_bind_right. admit.
        (* apply bapprox_consume_chunk. *)
        admit.
        apply bapprox_bind_right. apply dmut_pure_dcl.
        apply (bapprox_produce_chunk (chunk_ptsreg reg t)).
        now apply bapprox_pure.
      - admit.
      - admit.
    Admitted.

    Lemma bapprox_contract {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) (ι : SymInstance (sep_contract_logic_variables c)) :
      bapprox ι (@dmut_contract Γ τ c s) (@scmut_contract Γ τ c s ι).
    Proof.
      unfold dmut_contract, scmut_contract; destruct c as [Σ δ pre result post]; cbn in *.
      apply bapprox_bind_right. admit.
      apply bapprox_produce.
      apply bapprox_bind. admit.
      apply bapprox_exec.
      intros res.
      eapply bapprox_sub; eauto.
      rewrite inst_sub_snoc, inst_sub_id.
      (* apply bapprox_consume. *)
    Admitted.

    Lemma symbolic_sound {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
      ValidContractNoEvar c body ->
      ValidContractSCMut c body.
    Proof.
      unfold ValidContractNoEvar, ValidContractSCMut. intros Hwp.
      unfold ForallNamed in Hwp. rewrite Forall_forall in Hwp.
      intros ι. cbn. specialize (Hwp ι).
      pose proof (bapprox_contract c body) as H.
      specialize (H ι _ (sub_id _) nil ι (fun _ _ => True)).
      specialize (H (symbolicstate_initial (sep_contract_localstore c))).
      rewrite inst_sub_id in H. inster H by constructor.
      rewrite outcome_satisfy_map. apply H. clear H.
      unfold dmut_contract_outcome in Hwp.
    Admitted.

    (* Print Assumptions dmut_wp_assume_formula. *)
    (* Print Assumptions dmut_wp_bind. *)
    (* Print Assumptions dmut_wp_bind_right. *)
    (* Print Assumptions dmut_wp_equiv. *)
    (* Print Assumptions dmut_wp_fmap. *)
    (* Print Assumptions dmut_wp_fresh. *)
    (* Print Assumptions dmut_wp_match_pair. *)
    (* Print Assumptions dmut_wp_match_sum. *)
    (* Print Assumptions dmut_wp_pair. *)
    (* Print Assumptions dmut_wp_pure. *)
    (* Print Assumptions dmut_wp_sub. *)

    (* Print Assumptions dmut_pure_dcl. *)
    (* Print Assumptions dmut_fresh_dcl. *)
    (* Print Assumptions dmut_arrow_dcl_specialize. *)
    (* Print Assumptions dmut_arrow_dcl_specialize. *)
    (* Print Assumptions dmut_bind_dcl. *)
    (* Print Assumptions dmut_bind_right_dcl. *)

    (* Print Assumptions symbolic_sound. *)

  End TwoPointOSoundness.

  Section Leftovers.

    Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : (x ∶ σ)%ctx ∈ Γ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
      (subst ζ (δ ‼ x)%exp = (subst ζ δ ‼ x)%exp).
    Proof.
      unfold subst at 2, subst_localstore, SubstEnv.
      now rewrite env_lookup_map.
    Qed.

    Lemma subst_symboliceval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
      subst (T := fun Σ => Term Σ _) ζ (symbolic_eval_exp δ e) = symbolic_eval_exp (subst ζ δ) e.
    Proof.
      induction e; cbn; f_equal; auto.
      { now rewrite (subst_lookup xInΓ). }
      all: induction es; cbn in *; destruct_conjs; f_equal; auto.
    Qed.

  End Leftovers.

End Soundness.
