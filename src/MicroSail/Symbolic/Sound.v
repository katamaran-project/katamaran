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

  Global Instance InstSMutResult {AT A} `{Inst AT A} {Γ} : Inst (SMutResult Γ AT) (CMutResult Γ A).
  Proof.
    constructor.
    - intros ? ? r.
      destruct r as [a δ h].
      constructor.
      revert a. now apply inst.
      revert δ. now apply inst.
      revert h. now apply inst.
    - intros ? r.
      destruct r as [a δ h].
      constructor.
      apply (lift a).
      apply (lift δ).
      apply (lift h).
  Defined.

  Global Instance InstLawsSMutResult {AT A} `{InstLaws AT A} {Γ} : InstLaws (SMutResult Γ AT) (CMutResult Γ A).
  Proof.
    constructor.
    - intros ? ? []; cbn; now rewrite ?inst_lift.
    - intros ? ? ? ? []; cbn; now rewrite ?inst_subst.
  Qed.

  (* Lemma spath_arrow_dcl_eta {AT A BT B} `{Subst AT, Subst BT, Inst AT A, Inst BT B} {Γ Σ1} (f : spath_arrow (SMutResult Γ AT) BT Σ1) : *)
  (*   spath_arrow_dcl *)
  (*     (AT := SMutResult Γ AT) *)
  (*     (fun Σ2 ζ12 pc2 r => *)
  (*        f Σ2 ζ12 pc2 {| dmutres_value := dmutres_result_value r; dmutres_result_state := dmutres_result_state r |}) -> *)
  (*   spath_arrow_dcl f. *)
  (* Proof. *)
  (*   intros HYP Σ2 Σ3 ζ12 ζ13 pc2 pc3 ζ23 r2 r3 F P Q PQ ι2 ι3; *)
  (*     specialize (HYP Σ2 Σ3 ζ12 ζ13 pc2 pc3 ζ23 r2 r3 F P Q PQ ι2 ι3); *)
  (*     destruct r2, r3; intuition. *)
  (* Qed. *)

  Lemma spath_arrow_dcl_pure {BT B} `{Subst ET, Subst BT, Inst BT B} {Γ3 Σ1} :
      spath_arrow_dcl
        (fun (Σ3 : LCtx) (_ : Sub Σ1 Σ3) (_ : PathCondition Σ3) (X : SMutResult Γ3 BT Σ3) =>
           match X with
           | MkSMutResult b3 δ3 h3 => spath_pure (MkSMutResult b3 δ3 h3)
           end).
  Proof. unfold spath_arrow_dcl. destruct a1, a2. cbn. intuition. Qed.

  Definition smut_arrow Γ1 Γ2 AT BT Σ0 : Type :=
    forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> SMut Γ1 Γ2 BT Σ1.

  Definition smut_wp {AT A} `{Inst AT A} {Γ1 Γ2 Σ0} (d : SMut Γ1 Γ2 AT Σ0)
    {Σ1} (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1)
    (ι1 : SymInstance Σ1) (P : A -> SCProp Γ2) : Prop :=
    spath_wp (d Σ1 ζ01 pc1 δ1 h1) ι1 (fun r => P (scmutres_value r) (scmutres_store r) (scmutres_heap r)).
  Global Arguments smut_wp : simpl never.

  Ltac fold_smut_wp :=
    match goal with
    | |- context[spath_wp (?d ?Σ ?ζ ?pc ?δ ?h) ?ι (fun r => ?P _ _ _)] =>
      change (spath_wp (d Σ ζ pc δ h) ι _) with (smut_wp d ζ pc δ h ι P)
    end.

  Lemma smut_wp_monotonic {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d : SMut Γ1 Γ2 AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h -> Q a δ h) :
      smut_wp d ζ01 pc1 δ1 h1 ι1 P -> smut_wp d ζ01 pc1 δ1 h1 ι1 Q.
  Proof.
    unfold smut_wp. apply spath_wp_monotonic; intros []; apply PQ.
  Qed.

  Lemma smut_wp_equiv {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d : SMut Γ1 Γ2 AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h <-> Q a δ h) :
      smut_wp d ζ01 pc1 δ1 h1 ι1 P <-> smut_wp d ζ01 pc1 δ1 h1 ι1 Q.
  Proof.
    unfold smut_wp. split; apply spath_wp_monotonic; intros []; apply PQ.
  Qed.

  Lemma smut_wp_pure {AT A} `{InstLaws AT A} {Γ Σ0 Σ1} (a0 : AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ) :
    smut_wp (smut_pure (Γ := Γ) a0) ζ01 pc1 δ1 h1 ι1 P <-> P (inst (inst ι1 ζ01) a0) (inst ι1 δ1) (inst ι1 h1).
  Proof. unfold smut_wp, smut_pure; cbn. now rewrite inst_subst. Qed.

  Lemma smut_wp_fail {AT A D} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1} (func msg : string) (data : D) (ζ01 : Sub Σ0 Σ1)
        (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) :
    smut_wp (smut_fail func msg data) ζ01 pc1 δ1 h1 ι1 P <-> False.
  Proof. split; intros []. Qed.

  Lemma smut_wp_sub {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1 Σ2} (ζ01 : Sub Σ0 Σ1) (d : SMut Γ1 Γ2 AT Σ0)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2)
    (P : A -> SCProp Γ2) :
    smut_wp (smut_sub ζ01 d) ζ12 pc2 δ2 h2 ι2 P <->
    smut_wp d (sub_comp ζ01 ζ12) pc2 δ2 h2 ι2 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_debug {AT A DT D} `{InstLaws AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2 Σ0 Σ1} d (k : SMut Γ1 Γ2 AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) :
    smut_wp (smut_debug d k) ζ01 pc1 δ1 h1 ι1 P <-> smut_wp k ζ01 pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_debug; cbn. split.
    - now intros [].
    - now constructor.
  Qed.

  Definition smut_geq {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d1 d2 : SMut Γ1 Γ2 AT Σ0) : Prop :=
    forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ζ02 ι1 ι2,
      ι1 = inst ι2 ζ12 ->
      instpc ι1 pc1 ->
      instpc ι2 pc2 ->
      inst ι1 δ1 = inst ι2 δ2 ->
      inst ι1 h1 = inst ι2 h2 ->
      inst ι1 ζ01 = inst ι2 ζ02 ->
      forall (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h -> Q a δ h),
        smut_wp d1 ζ01 pc1 δ1 h1 ι1 P ->
        smut_wp d2 ζ02 pc2 δ2 h2 ι2 Q.

  Definition smut_dcl {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d : SMut Γ1 Γ2 AT Σ0) : Prop :=
    smut_geq d d.

  Definition smut_arrow_dcl {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0} (f : smut_arrow Γ1 Γ2 AT BT Σ0) : Prop :=
    forall Σ1 Σ2 ζ01 ζ02 a1 a2 Σ3 Σ4 ζ13 ζ24 ζ34 pc3 pc4 δ3 h3 δ4 h4,
    forall (ι3 : SymInstance Σ3) (ι4 : SymInstance Σ4),
      ι3 = inst ι4 ζ34 ->
      instpc ι3 pc3 ->
      instpc ι4 pc4 ->
      inst ι3 (sub_comp ζ01 ζ13) = inst ι4 (sub_comp ζ02 ζ24) ->
      inst (inst ι3 ζ13) a1 = inst (inst ι4 ζ24) a2 ->
      inst ι3 δ3 = inst ι4 δ4 ->
      inst ι3 h3 = inst ι4 h4 ->
      forall (P Q : B -> SCProp Γ2) (PQ : forall b δ h, P b δ h -> Q b δ h),
        smut_wp (f Σ1 ζ01 a1) ζ13 pc3 δ3 h3 ι3 P ->
        smut_wp (f Σ2 ζ02 a2) ζ24 pc4 δ4 h4 ι4 Q.

  Lemma smut_arrow_dcl_specialize {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
    (f : smut_arrow Γ1 Γ2 AT BT Σ0) (f_dcl : smut_arrow_dcl f) :
    forall Σ1 (ζ01 : Sub Σ0 Σ1) (a1 : AT Σ1),
      smut_dcl (f Σ1 ζ01 a1).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    eapply f_dcl; eauto; unfold sub_comp; rewrite ?inst_subst; congruence.
  Qed.

  Lemma smut_pure_dcl {AT A} `{InstLaws AT A} {Γ Σ} (a : AT Σ) :
    smut_dcl (smut_pure (Γ := Γ) a).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hδ Hh Hζ * PQ.
    rewrite ?smut_wp_pure. rewrite Hδ, Hh, Hζ. apply PQ.
  Qed.

  Lemma smut_wp_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ2}
    (d : SMut Γ1 Γ2 AT Σ0) (f : smut_arrow Γ2 Γ3 AT BT Σ0) (f_dcl : smut_arrow_dcl f)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ02 : Sub Σ0 Σ2) (ι2 : SymInstance Σ2)
    (Q : B -> SCProp Γ3) (Hpc2 : instpc ι2 pc2) :
    smut_wp (smut_bind d f) ζ02 pc2 δ2 h2 ι2 Q <->
    smut_wp d ζ02 pc2 δ2 h2 ι2 (fun a δ h => smut_wp (f _ (sub_id _) (lift a)) ζ02 pc2 (lift δ) (lift h) ι2 Q).
  Proof.
    unfold smut_wp, smut_bind; cbn.
    rewrite spath_wp_bind; auto. split; apply spath_wp_monotonic.
    - intros [a scδ2 sch2]; cbn. rewrite sub_comp_id_right.
      rewrite spath_wp_bind; try exact spath_arrow_dcl_pure; auto.
      unfold smut_arrow_dcl, smut_wp in f_dcl. cbn.
      specialize (f_dcl Σ2 Σ0 ζ02 (sub_id _) (lift a) (lift a) Σ2 Σ2 (sub_id _) ζ02 (sub_id _) pc2 pc2).
      specialize (f_dcl (lift scδ2) (lift sch2) (lift scδ2) (lift sch2) ι2 ι2).
      inster f_dcl by (unfold sub_comp; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; auto).
      specialize (f_dcl Q Q). inster f_dcl by auto.
      intros Hwp; apply f_dcl; revert Hwp.
      apply spath_wp_monotonic. intros [b sc3]. cbn.
      now rewrite ?inst_lift.
    - intros [a scδ2 sch2]; cbn. rewrite sub_comp_id_right.
      rewrite spath_wp_bind; try exact spath_arrow_dcl_pure; auto.
      unfold smut_arrow_dcl, smut_wp in f_dcl. cbn.
      specialize (f_dcl Σ0 Σ2 (sub_id _) ζ02 (lift a) (lift a) Σ2 Σ2 ζ02 (sub_id _) (sub_id _) pc2 pc2).
      specialize (f_dcl (lift scδ2) (lift sch2) (lift scδ2) (lift sch2) ι2 ι2).
      inster f_dcl by (unfold sub_comp; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; auto).
      specialize (f_dcl Q Q). inster f_dcl by auto.
      intros Hwp; apply f_dcl in Hwp; revert Hwp.
      apply spath_wp_monotonic. intros [b sc3]. cbn.
      now rewrite ?inst_lift.
    - unfold spath_arrow_dcl. destruct a1 as [a1 δ1 h1], a2 as [a3 δ3 h3]; cbn. intros.
      revert H12. inversion H11. clear H11.
      rewrite ?spath_wp_bind; try exact spath_arrow_dcl_pure; auto.
      unfold lift; cbn. setoid_rewrite inst_lift.
      unfold smut_arrow_dcl, smut_wp in f_dcl.
      specialize (f_dcl Σ1 Σ3 (sub_comp ζ02 ζ1) (sub_comp ζ02 ζ2) a1 a3 Σ1 Σ3 (sub_id _) (sub_id _) ζ12 pc1 pc0).
      specialize (f_dcl δ1 h1 δ3 h3 ι1 ι0).
      inster f_dcl by (try exact HF0; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id; intuition).
      specialize (f_dcl (fun b δ h => P (MkCMutResult b δ h)) (fun b δ h => Q0 (MkCMutResult b δ h))).
      apply f_dcl; intuition.
  Qed.

  Lemma smut_wp_fmap {AT A BT B} `{InstLaws AT A, Inst BT B, Subst BT} {Γ1 Γ2 Σ0 Σ2}
    (d : SMut Γ1 Γ2 AT Σ0) (f : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> BT Σ1)
    (f_dcl : spath_mapping_dcl f)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ02 : Sub Σ0 Σ2) (ι2 : SymInstance Σ2)
    (Q : B -> SCProp Γ2) (Hpc2 : instpc ι2 pc2) :
    smut_wp (smut_fmap d f) ζ02 pc2 δ2 h2 ι2 Q <->
    smut_wp d ζ02 pc2 δ2 h2 ι2 (fun a : A => Q (inst ι2 (f Σ2 ζ02 (lift a)))).
  Proof.
    unfold smut_fmap, smut_wp. rewrite spath_wp_map.
    split; apply spath_wp_monotonic; intros [a δ2' h2']; cbn.
    - now rewrite sub_comp_id_right, ?inst_lift.
    - now rewrite sub_comp_id_right, ?inst_lift.
    - unfold spath_mapping_dcl. destruct a1 as [a1 δ1 h1], a2 as [a3 δ3 h3]; cbn.
      intros * -> Hζ. inversion 1. f_equal.
      eapply f_dcl; unfold sub_comp; rewrite ?inst_subst; intuition.
  Qed.

  Lemma smut_wp_pair {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
    (da : SMut Γ1 Γ2 AT Σ0) (db : SMut Γ2 Γ3 BT Σ0) (db_dcl : smut_dcl db)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) δ1 h1 ι1 (Hpc : instpc ι1 pc1) P :
    smut_wp (smut_pair da db) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp da ζ01 pc1 δ1 h1 ι1 (fun a δ2 h2 => smut_wp db ζ01 pc1 (lift δ2) (lift h2) ι1 (fun b => P (a,b))).
  Proof.
    unfold smut_pair, smut_fmap2. rewrite smut_wp_bind; eauto.
    apply smut_wp_equiv. intros a δ2 h2. rewrite smut_wp_fmap; eauto.
    rewrite smut_wp_sub, sub_comp_id_left.
    apply smut_wp_equiv. intros b δ3 h3. cbn.
    now rewrite ?inst_subst, ?inst_sub_id, ?inst_lift.
    - unfold spath_mapping_dcl. intros *. cbn.
      rewrite ?inst_subst, ?inst_lift. intuition.
    - intros until Q; intros PQ.
      rewrite ?smut_wp_fmap; eauto.
      + rewrite ?smut_wp_sub. eapply db_dcl; eauto.
        intros *. cbn. rewrite ?inst_subst, ?inst_lift, H11.
        intuition.
      + unfold spath_mapping_dcl. intros *. cbn.
        rewrite ?inst_subst, ?inst_lift. intros. subst.
        f_equal; auto. f_equal; auto.
      + unfold spath_mapping_dcl. intros *. cbn.
        rewrite ?inst_subst, ?inst_lift. intros. subst.
        f_equal; auto. f_equal; auto.
  Qed.

  Lemma smut_wp_bind_right {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
        (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0) (d2_dcl : smut_dcl d2)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : B -> SCProp Γ3) (Hpc1 : instpc ι1 pc1) :
    smut_wp (smut_bind_right d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 (fun a δ2 h2 => smut_wp d2 ζ01 pc1 (lift δ2) (lift h2) ι1 P).
  Proof.
    unfold smut_bind_right. rewrite smut_wp_bind; auto.
    unfold smut_wp, smut_sub.
    split; apply spath_wp_monotonic;
      intros [a sc2]; now rewrite sub_comp_id_left.
    unfold smut_arrow_dcl. intros until Q; intros PQ.
    rewrite ?smut_wp_sub. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_bind_right_arrow_dcl {AT A BT B CT C} `{InstLaws AT A, InstLaws BT B, InstLaws CT C} {Γ1 Γ2 Γ3 Σ1}
    (d1 : smut_arrow Γ1 Γ2 AT BT Σ1) (d1_dcl : smut_arrow_dcl d1)
    (d2 : smut_arrow Γ2 Γ3 AT CT Σ1) (d2_dcl : smut_arrow_dcl d2) :
    smut_arrow_dcl (fun Σ2 ζ02 a2 => smut_bind_right (d1 Σ2 ζ02 a2) (d2 Σ2 ζ02 a2)).
  Proof.
    intros until Q. intros PQ.
    rewrite ?smut_wp_bind_right; eauto.
    eapply d1_dcl; eauto. intros ? ? ?.
    eapply d2_dcl; eauto; now rewrite ?inst_lift.
    now apply smut_arrow_dcl_specialize.
    now apply smut_arrow_dcl_specialize.
  Qed.

  Lemma smut_bind_arrow_dcl {AT A BT B CT C} `{InstLaws AT A, InstLaws BT B, InstLaws CT C}
      {Γ1 Γ2 Γ3 Σ0}
      (d1 : smut_arrow Γ1 Γ2 AT BT Σ0) (d1_dcl : smut_arrow_dcl d1)
      (d2 : smut_arrow Γ2 Γ3 BT CT Σ0) (d2_dcl : smut_arrow_dcl d2) :
    smut_arrow_dcl (fun Σ2 ζ02 a2 => smut_bind (d1 Σ2 ζ02 a2) (fun Σ3 ζ23 a3 => d2 Σ3 (sub_comp ζ02 ζ23) a3)).
  Proof.
    unfold smut_arrow_dcl, smut_geq.
    intros * -> Hpc1 Hpc2 Hζ Ha Hδ Hh P Q PQ; cbn.
    rewrite ?smut_wp_bind; auto. eapply d1_dcl; eauto. intros a δ h.
    eapply d2_dcl; eauto; unfold sub_comp in *; rewrite ?inst_subst in Hζ;
      rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; intuition.

    unfold smut_arrow_dcl.
    intros * -> Hpc3 Hpc4 Hζ2 Ha2 Hδ2 Hh2 P2 Q2 PQ2; cbn.
    eapply d2_dcl; eauto.
    unfold sub_comp.
    unfold sub_comp in Hζ2.
    rewrite ?inst_subst in Hζ2.
    now rewrite ?inst_subst, Hζ2.

    unfold smut_arrow_dcl.
    intros * -> Hpc3 Hpc4 Hζ2 Ha2 Hδ2 Hh2 P2 Q2 PQ2; cbn.
    eapply d2_dcl; eauto.
    unfold sub_comp.
    unfold sub_comp in Hζ2.
    rewrite ?inst_subst in Hζ2.
    now rewrite ?inst_subst, Hζ2.
  Qed.

  Lemma smut_sub_arrow_dcl {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ2 Γ3 Σ0} (d : SMut Γ2 Γ3 BT Σ0) (d_dcl : smut_dcl d) :
    smut_arrow_dcl (fun (Σ2 : LCtx) (ζ02 : Sub Σ0 Σ2) (_ : AT Σ2) => smut_sub ζ02 d).
  Proof. intros until Q; intros PQ. rewrite ?smut_wp_sub. eapply d_dcl; eauto. Qed.

  Lemma smut_pure_arrow_dcl {AT A} `{InstLaws AT A} {Γ Σ0} :
    smut_arrow_dcl (fun Σ1 (ζ01 : Sub Σ0 Σ1) (a1 : AT Σ1) => smut_pure (Γ := Γ) a1).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_pure.
    intros HP. apply PQ. revert HP.
    rewrite ?inst_subst. intuition.
  Qed.

  Lemma smut_wp_bind_left {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
        (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0) (d2_dcl : smut_dcl d2)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ3) (Hpc1 : instpc ι1 pc1) :
    smut_wp (smut_bind_left d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 (fun a δ2 h2 => smut_wp d2 ζ01 pc1 (lift δ2) (lift h2) ι1 (fun _ => P a)).
  Proof.
    unfold smut_bind_left. rewrite smut_wp_bind; auto. apply smut_wp_equiv.
    intros a scδ2 sch2. rewrite smut_wp_bind_right, smut_wp_sub; auto.
    split; eapply d2_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id; auto;
      intros _ scδ3 sch3; now rewrite smut_wp_pure, ?inst_lift.
    apply smut_pure_dcl.
    apply smut_bind_right_arrow_dcl.
    now apply smut_sub_arrow_dcl.
    apply smut_pure_arrow_dcl.
  Qed.

  Lemma smut_wp_state {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ1 Σ2}
    (f : forall Σ2, Sub Σ1 Σ2 -> SStore Γ1 Σ2 -> SHeap Σ2 -> SMutResult Γ2 AT Σ2)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2) (Q : A -> SCProp Γ2) :
    smut_wp (smut_state f) ζ12 pc2 δ2 h2 ι2 Q <->
    match f Σ2 ζ12 δ2 h2 with MkSMutResult a δ2' h2' => Q (inst ι2 a) (inst ι2 δ2') (inst ι2 h2') end.
  Proof.
    unfold smut_wp, smut_state; cbn.
    now destruct (f Σ2 ζ12 _).
  Qed.

  Lemma smut_wp_demonic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d1 d2 : SMut Γ1 Γ2 AT Σ0)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) :
    smut_wp (smut_demonic_binary d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 P /\ smut_wp d2 ζ01 pc1 δ1 h1 ι1 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_angelic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d1 d2 : SMut Γ1 Γ2 AT Σ0)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) :
    smut_wp (smut_angelic_binary d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 P \/ smut_wp d2 ζ01 pc1 δ1 h1 ι1 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_angelic {AT A I} `{Inst AT A} {Γ1 Γ2 Σ Σ1} (d : I -> SMut Γ1 Γ2 AT Σ) (* (d_dcl : smut_dcl d) *)
    (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) :
    smut_wp (smut_angelic d) ζ01 pc1 δ1 h1 ι1 P <->
    exists i, smut_wp (d i) ζ01 pc1 δ1 h1 ι1 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_angelicv {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ Σ1 x σ} (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : smut_dcl d)
        (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) (hpc : instpc ι1 pc1) :
    smut_wp (smut_angelicv x σ d) ζ01 pc1 δ1 h1 ι1 P <->
    exists v : Lit σ, smut_wp d (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_angelicv; cbn.
    split; intros [v Hwp]; exists v; revert Hwp.
    - apply (d_dcl
               (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) Σ1 (sub_snoc (sub_comp ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))) (subst sub_wk1 pc1)
               (subst sub_wk1 δ1) (subst sub_wk1 h1) (sub_snoc (sub_id Σ1) (fresh Σ1 (Some x) :: σ) (term_lit σ v)) pc1 δ1 h1 (sub_snoc ζ01 (x :: σ) (term_lit σ v)));
        rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
      unfold sub_comp. now rewrite inst_subst, inst_sub_wk1.
    - apply (d_dcl
               Σ1 (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 δ1 h1 sub_wk1 (subst sub_wk1 pc1) (subst sub_wk1 δ1) (subst sub_wk1 h1)
               (sub_snoc (sub_comp ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))));
        rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
      unfold sub_comp. now rewrite inst_subst, inst_sub_wk1.
  Qed.

  Lemma smut_wp_angelicvs {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ Σ1 Δ} (d : SMut Γ1 Γ2 AT (Σ ▻▻ Δ)) (d_dcl : smut_dcl d)
    (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) (hpc : instpc ι1 pc1) :
    smut_wp (smut_angelicvs Δ d) ζ01 pc1 δ1 h1 ι1 P <->
    exists ιΔ : SymInstance Δ, smut_wp d (env_cat ζ01 (lift (T := fun Σ => Sub _ Σ) ιΔ)) pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_angelicvs; cbn.
    rewrite spath_wp_angelicvs.
    split; intros [ιΔ Hwp]; exists ιΔ; revert Hwp.
    - (* eapply d_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn. *)
      (* unfold sub_comp. now rewrite inst_subst, inst_sub_wk1. *)
      admit.
    - (* eapply d_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn. *)
      (* unfold sub_comp. now rewrite inst_subst, inst_sub_wk1. *)
      admit.
  Admitted.

  Lemma smut_wp_demonicv {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ Σ1 x σ} (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : smut_dcl d)
        (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) (hpc : instpc ι1 pc1) :
    smut_wp (smut_demonicv x σ d) ζ01 pc1 δ1 h1 ι1 P <->
    forall v : Lit σ, smut_wp d (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_demonicv; cbn.
    split; intros Hwp v; specialize (Hwp v); revert Hwp.
    - apply (d_dcl
               (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) Σ1 (sub_snoc (sub_comp ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))) (subst sub_wk1 pc1)
               (subst sub_wk1 δ1) (subst sub_wk1 h1) (sub_snoc (sub_id Σ1) (fresh Σ1 (Some x) :: σ) (term_lit σ v)) pc1 δ1 h1 (sub_snoc ζ01 (x :: σ) (term_lit σ v)));
        rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
      unfold sub_comp. now rewrite inst_subst, inst_sub_wk1.
    - apply (d_dcl
               Σ1 (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 δ1 h1 sub_wk1 (subst sub_wk1 pc1) (subst sub_wk1 δ1) (subst sub_wk1 h1)
               (sub_snoc (sub_comp ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))));
        rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
      unfold sub_comp. now rewrite inst_subst, inst_sub_wk1.
  Qed.

  Lemma smut_wp_angelic_list {AT A D} `{InstLaws AT A} {Γ Σ} (func msg : string) (data : D)
    (xs : List AT Σ) Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ) :
    smut_wp (smut_angelic_list func msg data xs) ζ01 pc1 δ1 h1 ι1 P <->
    exists x : AT _, List.In x xs /\ P (inst (inst ι1 ζ01) x) (inst ι1 δ1) (inst ι1 h1).
  Proof.
    induction xs; cbn - [smut_wp].
    - rewrite smut_wp_fail. split. intro Fm; exfalso; intuition.
      intros []; intuition.
    - destruct xs; cbn - [smut_wp] in *.
      + rewrite smut_wp_fail in IHxs.
        rewrite smut_wp_pure.
        destruct IHxs. split; intros; destruct_conjs.
        exists a. intuition.
        intuition.
      + rewrite smut_wp_angelic_binary, smut_wp_pure.
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

  Lemma smut_wp_demonic_list {AT A} `{InstLaws AT A} {Γ Σ}
    (xs : List AT Σ) Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ) :
    smut_wp (smut_demonic_list xs) ζ01 pc1 δ1 h1 ι1 P <->
    forall x : AT _, List.In x xs -> P (inst (inst ι1 ζ01) x) (inst ι1 δ1) (inst ι1 h1).
  Proof.
    induction xs.
    - cbn; firstorder.
    - destruct xs; cbn.
      + rewrite smut_wp_pure.
        intuition.
      + rewrite smut_wp_demonic_binary.
        rewrite smut_wp_pure.
        intuition.
  Qed.

  Lemma smut_wp_demonic_listk {AT BT B} `{InstLaws BT B} {Γ1 Γ2 Σ}
        (xs : List AT Σ) (k : AT Σ -> SMut Γ1 Γ2 BT Σ)
        Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : B -> SCProp Γ2) :
    smut_wp (smut_demonic_listk xs k) ζ01 pc1 δ1 h1 ι1 P <->
    forall x : AT _, List.In x xs -> smut_wp (k x) ζ01 pc1 δ1 h1 ι1 P.
  Proof.
    induction xs.
    - cbn; firstorder.
    - destruct xs.
      + cbn in *. intuition.
      + change (smut_wp (smut_demonic_listk (a :: a0 :: xs)%list k) ζ01 pc1 δ1 h1 ι1 P)
          with (smut_wp (k a) ζ01 pc1 δ1 h1 ι1 P /\ smut_wp (smut_demonic_listk (a0 :: xs)%list k) ζ01 pc1 δ1 h1 ι1 P).
        rewrite IHxs. cbn. intuition.
  Qed.

  Lemma smut_wp_demonic_finite {X AT A} `{finite.Finite X, Subst AT, Inst AT A, InstLaws AT A, SubstLaws AT} {Γ1 Γ2 Σ Σ1}
    (k : X -> SMut Γ1 Γ2 AT Σ) (k_dcl : forall x, smut_dcl (k x))
    (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) (Hpc : instpc ι1 pc1) :
    smut_wp (smut_demonic_finite X k) ζ01 pc1 δ1 h1 ι1 P <->
    (forall x : X, smut_wp (k x) ζ01 pc1 δ1 h1 ι1 P).
  Proof.
    unfold smut_demonic_finite.
    rewrite smut_wp_demonic_listk.
    setoid_rewrite <-base.elem_of_list_In.
    split; intros HYP x; specialize (HYP x); auto.
    apply HYP, finite.elem_of_enum.
  Qed.

  Lemma smut_wp_demonic_termvar {Γ Σ Σ1 x σ}
    (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : Lit σ -> SCProp Γ) (Hpc : instpc ι1 pc1) :
    smut_wp (@smut_demonic_termvar Γ _ σ x) ζ01 pc1 δ1 h1 ι1 P <->
    forall v : Lit σ, P v (inst ι1 δ1) (inst ι1 h1).
  Proof.
    unfold smut_demonic_termvar. rewrite smut_wp_demonicv; auto.
    apply smut_pure_dcl.
  Qed.

  Lemma smut_fail_dcl `{Inst AT A, Subst AT} {D Γ1 Γ2 Σ} func msg data :
    smut_dcl (@smut_fail Γ1 Γ2 AT Σ D func msg data).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hδ Hh Hζ * PQ.
    now rewrite ?smut_wp_fail.
  Qed.

  Lemma smut_sub_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d : SMut Γ1 Γ2 AT Σ0) (d_dcl : smut_dcl d) :
    forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), smut_dcl (smut_sub ζ1 d).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hs Hζ * PQ. rewrite ?smut_wp_sub.
    apply d_dcl with ζ12; auto. unfold sub_comp. rewrite ?inst_subst. congruence.
  Qed.

  Lemma smut_demonicv_dcl {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ x σ} (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : smut_dcl d) :
    smut_dcl (smut_demonicv x σ d).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    rewrite ?smut_wp_demonicv; auto.
    intros Hwp v. specialize (Hwp v). revert Hwp.
    eapply d_dcl; eauto. rewrite ?inst_sub_snoc.
    cbn. f_equal; auto.
  Qed.

  Lemma smut_demonic_termvar_dcl {Γ Σ x σ} :
    smut_dcl (@smut_demonic_termvar Γ Σ σ x).
  Proof. apply smut_demonicv_dcl, smut_pure_dcl. Qed.

  Ltac fold_inst_term :=
    repeat change (@inst_term ?Σ ?ι ?σ ?t) with (@inst (fun Σ => Term Σ σ) (Lit σ) (@instantiate_term σ) Σ ι t) in *.

  Lemma smut_bind_dcl {AT A BT B} `{InstLaws AT A, InstLaws BT B}
      {Γ1 Γ2 Γ3 Σ0} (d : SMut Γ1 Γ2 AT Σ0) (d_dcl : smut_dcl d)
      (f : smut_arrow Γ2 Γ3 AT BT Σ0) (f_dcl : smut_arrow_dcl f) :
    smut_dcl (smut_bind d f).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hδ Hh Hζ P Q PQ; cbn.
    rewrite ?smut_wp_bind; auto. eapply d_dcl; eauto. intros a δ h.
    eapply f_dcl; eauto; unfold sub_comp;
      rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; intuition.
  Qed.

  Lemma smut_bind_right_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
    (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0)
    (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_bind_right d1 d2).
  Proof.
    unfold smut_bind_right, smut_sub. apply smut_bind_dcl; auto.
    unfold smut_arrow_dcl. intros. revert H14. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_bind_left_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
    (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0)
    (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_bind_left d1 d2).
  Proof.
    unfold smut_bind_left. apply smut_bind_dcl; auto.
    apply smut_bind_right_arrow_dcl.
    now apply smut_sub_arrow_dcl.
    apply smut_pure_arrow_dcl.
  Qed.

  Lemma smut_demonic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : SMut Γ1 Γ2 AT Σ0) (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_demonic_binary d1 d2).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    rewrite ?smut_wp_demonic_binary. intros [Hwp1 Hwp2].
    split.
    - revert Hwp1. eapply d1_dcl; eauto.
    - revert Hwp2. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_angelic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : SMut Γ1 Γ2 AT Σ0) (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_angelic_binary d1 d2).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    rewrite ?smut_wp_angelic_binary. intros [Hwp1|Hwp2].
    - left. revert Hwp1. eapply d1_dcl; eauto.
    - right. revert Hwp2. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_state_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ}
    (f : forall Σ' : LCtx, Sub Σ Σ' -> SStore Γ1 Σ' -> SHeap Σ' -> SMutResult Γ2 AT Σ')
    (f_dcl :
       forall Σ1 Σ2 (ζ01 : Sub Σ Σ1) (ζ02 : Sub Σ Σ2) (ζ12 : Sub Σ1 Σ2)
         (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1)
         (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) ι1 ι2,
         ι1 = inst ι2 ζ12 ->
         inst ι1 δ1 = inst ι2 δ2 ->
         inst ι1 h1 = inst ι2 h2 ->
         inst ι1 ζ01 = inst ι2 ζ02 ->
         inst ι1 (f Σ1 ζ01 δ1 h1) = inst ι2 (f Σ2 ζ02 δ2 h2)) :
    smut_dcl (smut_state f).
  Proof.
    unfold smut_dcl; intros until Q. intros PQ. rewrite ?smut_wp_state.
    pose proof (f_dcl Σ1 Σ2 ζ01 ζ02 ζ12 δ1 h1 δ2 h2 ι1 ι2) as Hf.
    destruct (f Σ1 ζ01 δ1 h1), (f Σ2 ζ02 δ2 h2); cbn.
    cbn in Hf. inster Hf by (f_equal; auto).
    inversion Hf. intros Hp. apply PQ. revert Hp. intuition.
  Qed.
  Local Hint Resolve smut_state_dcl : core.

  Lemma smut_put_local_dcl {Γ1 Γ2 Σ} (δ : SStore Γ2 Σ) :
    smut_dcl (smut_put_local (Γ := Γ1) δ).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ. cbn.
    f_equal; auto. rewrite ?inst_subst. intuition.
  Qed.
  Local Hint Resolve smut_put_local_dcl : core.

  Lemma smut_get_local_dcl {Γ Σ}  :
    smut_dcl (smut_get_local (Σ := Σ) (Γ := Γ)).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ. cbn.
    f_equal; auto.
  Qed.
  Local Hint Resolve smut_get_local_dcl : core.

  Lemma smut_put_heap_dcl {Γ Σ} (h : SHeap Σ) :
    smut_dcl (smut_put_heap (Γ := Γ) h).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ. cbn.
    f_equal; auto. rewrite ?inst_subst. intuition.
  Qed.
  Local Hint Resolve smut_put_heap_dcl : core.

  Lemma smut_get_heap_dcl {Γ Σ} :
    smut_dcl (smut_get_heap (Γ := Γ) (Σ := Σ)).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ.
    cbn. f_equal; auto.
  Qed.
  Local Hint Resolve smut_get_heap_dcl : core.

  Lemma smut_pop_local_dcl {Γ x σ Σ} :
    smut_dcl (@smut_pop_local Γ x σ Σ).
  Proof.
    unfold smut_pop_local. apply smut_state_dcl. intros * -> Hδ Hh Hζ.
    destruct (snocView δ1), (snocView δ2). cbn in Hδ.
    apply noConfusion_inv, (f_equal pr1) in Hδ. cbn in Hδ.
    cbn. f_equal. apply Hδ. auto.
  Qed.

  Lemma smut_block_dcl {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ}  :
    smut_dcl (Γ1 := Γ1) (Γ2 := Γ2) (Σ0 := Σ) smut_block.
  Proof. now unfold smut_dcl, smut_block. Qed.

  (* Lemma smut_demonic_list_dcl {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ} (l : list (SMut Γ1 Γ2 AT Σ)) *)
  (*   (l_dcl : forall d, List.In d l -> smut_dcl d) : *)
  (*   smut_dcl (smut_demonic_list l). *)
  (* Proof. *)
  (*   induction l; cbn. *)
  (*   - apply smut_block_dcl. *)
  (*   - destruct l. *)
  (*     + apply l_dcl. now left. *)
  (*     + apply smut_demonic_binary_dcl. *)
  (*       apply l_dcl. now left. *)
  (*       apply IHl. intros d' dIn'. *)
  (*       apply l_dcl. now right. *)
  (* Qed. *)

  Lemma smut_angelic_list_dcl {AT A D} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A}
        {Γ Σ} func msg (data : D) (l : list (AT Σ)) :
    smut_dcl (Γ2 := Γ) (smut_angelic_list func msg data l).
  Proof.
    induction l; cbn.
    - apply smut_fail_dcl.
    - destruct l.
      + apply smut_pure_dcl.
      + apply smut_angelic_binary_dcl.
        apply smut_pure_dcl.
        apply IHl.
  Qed.

  Lemma smut_angelic_list_arrow_dcl {AT A BT B D} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A, Inst BT B, InstLaws BT B}
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
    smut_arrow_dcl (Γ2 := Γ) (fun Σ2 (ζ : Sub Σ Σ2) s => smut_angelic_list func msg data (l Σ2 ζ s)).
  Proof.
    unfold smut_arrow_dcl.
    intros until Q.
    intros PQ.
    assert (eql : inst (inst ι3 ζ13) (l Σ1 ζ01 a1) = inst (inst ι4 ζ24) (l Σ2 ζ02 a2)) by (eapply Hl; eauto).
    rewrite ?smut_wp_angelic_list; eauto.
    intros (x & xInl1 & Px).
    apply (List.in_map (inst (inst ι3 ζ13))) in xInl1.
    unfold inst at 1 3 in eql; cbn in eql.
    rewrite eql in xInl1.
    eapply List.in_map_iff in xInl1.
    destruct xInl1 as (x2 & eq2 & x2Inl2).
    apply PQ in Px.
    rewrite <-eq2,H17,H18 in Px.
    exists x2; eauto.
  Qed.

  (* Lemma smut_demonic_finite_dcl {F AT A} `{finite.Finite F, Subst AT, Inst AT A} {Γ Σ} *)
  (*   (k : F -> SMut Γ Γ AT Σ) (k_dcl : forall x, smut_dcl (k x)) : *)
  (*   smut_dcl (smut_demonic_finite F k). *)
  (* Proof. *)
  (*   unfold smut_demonic_finite. apply smut_demonic_list_dcl. *)
  (*   intros d. rewrite List.in_map_iff. *)
  (*   intros [x [? xIn]]. subst d. apply k_dcl. *)
  (* Qed. *)

  (* Lemma smut_angelic_finite_dcl {F AT A} `{finite.Finite F, Subst AT, Inst AT A} {Γ Σ} *)
  (*   (k : F -> SMut Γ Γ AT Σ) (k_dcl : forall x, smut_dcl (k x)) : *)
  (*   smut_dcl (smut_angelic_finite F k). *)
  (* Proof. *)
  (*   unfold smut_angelic_finite. apply smut_angelic_list_dcl. *)
  (*   intros d. rewrite List.in_map_iff. *)
  (*   intros [x [? xIn]]. subst d. apply k_dcl. *)
  (* Qed. *)

  Lemma smut_wp_assume_formula {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fml : Formula Σ1)
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2) (ι2 : SymInstance Σ2) P :
    instpc ι2 pc2 ->
    smut_wp (smut_assume_formula fml) ζ12 pc2 δ2 h2 ι2 P <->
    ((inst (inst ι2 ζ12) fml : Prop) -> P tt (inst ι2 δ2) (inst ι2 h2)).
  Proof.
    unfold smut_wp, smut_assume_formula. intros.
    rewrite spath_wp_bind; auto.
    - rewrite spath_wp_assume_formula.
      rewrite ?subst_sub_id, ?inst_subst.
      reflexivity.
    - unfold spath_arrow_dcl. cbn. intros.
      revert H5. rewrite ?inst_subst.
      rewrite H3, H4. apply PQ.
  Qed.

  Lemma smut_assume_formula_dcl {Γ Σ} (fml : Formula Σ) :
    smut_dcl (Γ1 := Γ) (smut_assume_formula fml).
  Proof.
    unfold smut_dcl, smut_geq; intros. revert H5.
    rewrite ?smut_wp_assume_formula; auto.
    rewrite H2, H3. intuition.
  Qed.

  Lemma smut_assume_formulas_dcl {Γ Σ} (fmls : list (Formula Σ)) :
    smut_dcl (Γ1 := Γ) (smut_assume_formulas fmls).
  Proof.
    induction fmls.
    + now eapply smut_pure_dcl.
    + cbn.
      eapply smut_bind_right_dcl.
      eapply smut_assume_formula_dcl.
      eapply IHfmls.
  Qed.

  Lemma smut_wp_assume_formulas {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fmls : list (Formula Σ1))
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2) (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
    smut_wp (smut_assume_formulas fmls) ζ12 pc2 δ2 h2 ι2 P <->
    (instpc (inst ι2 ζ12) fmls -> P tt (inst ι2 δ2) (inst ι2 h2)).
  Proof.
    unfold smut_assume_formulas. revert δ2 h2.
    induction fmls; cbn [List.fold_right]; intros δ2 h2.
    - rewrite smut_wp_pure. cbn. intuition.
      apply H. constructor.
    - rewrite smut_wp_bind_right; auto.
      rewrite smut_wp_assume_formula; auto.
      rewrite IHfmls.
      rewrite inst_pathcondition_cons.
      rewrite ?inst_lift.
      intuition.
      eapply smut_assume_formulas_dcl.
  Qed.

  Lemma smut_wp_assert_formula {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fml : Formula Σ1)
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2)
    (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
    smut_wp (smut_assert_formula fml) ζ12 pc2 δ2 h2 ι2 P <->
    (inst (inst ι2 ζ12) fml /\ P tt (inst ι2 δ2) (inst ι2 h2)).
  Proof.
    unfold smut_wp, smut_assert_formula.
    rewrite spath_wp_bind, spath_wp_assert_formula; cbn;
      rewrite ?inst_subst, ?inst_sub_id; auto.
    unfold spath_arrow_dcl. cbn. intros.
    revert H4. rewrite ?inst_subst.
    rewrite H2, H3. apply PQ.
  Qed.

  Lemma smut_wp_assert_formulak {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Σ2} (fml : Formula Σ1) (k : SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_dcl k)
    (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
    smut_wp (smut_assert_formulak fml k) ζ12 pc2 δ2 h2 ι2 P <->
    (inst (inst ι2 ζ12) fml /\ smut_wp k ζ12 pc2 δ2 h2 ι2 P).
  Proof.
    unfold smut_assert_formulak.
    rewrite smut_wp_bind_right; auto.
    rewrite smut_wp_assert_formula; auto.
    split; intros [Hfml Hwp]; split; auto; revert Hwp;
      eapply k_dcl; rewrite ?inst_lift; eauto.
  Qed.

  Lemma smut_assert_formula_dcl {Γ Σ} (fml : Formula Σ) :
    smut_dcl (Γ1 := Γ) (smut_assert_formula fml).
  Proof.
    unfold smut_dcl, smut_geq. intros. revert H5.
    rewrite ?smut_wp_assert_formula; auto.
    rewrite H2, H3. intuition.
  Qed.

  Lemma smut_assert_formulas_dcl {Γ Σ} (fmls : list (Formula Σ)) :
    smut_dcl (smut_assert_formulas (Γ := Γ) fmls).
  Proof.
    induction fmls; cbn; [eapply smut_pure_dcl|].
    eapply smut_bind_right_dcl.
    eapply smut_assert_formula_dcl.
    eapply IHfmls.
  Qed.

  Lemma smut_assert_formulak_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (fml : Formula Σ) (k : SMut Γ1 Γ2 AT Σ) (k_dcl : smut_dcl k) :
    smut_dcl (smut_assert_formulak fml k).
  Proof.
    unfold smut_assert_formulak.
    apply smut_bind_right_dcl; auto.
    apply smut_assert_formula_dcl.
  Qed.

  Lemma smut_assert_formulask_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (fmls : List Formula Σ) (k : SMut Γ1 Γ2 AT Σ) (k_dcl : smut_dcl k) :
    smut_dcl (smut_assert_formulask fmls k).
  Proof.
    unfold smut_assert_formulask.
    induction fmls; cbn.
    - assumption.
    - now apply smut_assert_formulak_dcl.
  Qed.

  Lemma smut_wp_assert_formulask {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Σ2} (fmls : PathCondition Σ1) (k : SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_dcl k)
    (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2)
    (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
    smut_wp (smut_assert_formulask fmls k) ζ12 pc2 δ2 h2 ι2 P <->
    (inst (inst ι2 ζ12) fmls /\ smut_wp k ζ12 pc2 δ2 h2 ι2 P).
  Proof.
    unfold smut_assert_formulask. revert δ2 h2.
    induction fmls; cbn [List.fold_right]; intros δ2 h2.
    - intuition. constructor.
    - rewrite smut_wp_assert_formulak; auto.
      rewrite IHfmls.
      rewrite inst_pathcondition_cons.
      intuition.
      now apply smut_assert_formulask_dcl.
  Qed.

  Lemma smut_wp_assert_formulas {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fmls : list (Formula Σ1))
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2)
    (ι2 : SymInstance Σ2) (Hpc2 : instpc ι2 pc2) P :
    smut_wp (smut_assert_formulas fmls) ζ12 pc2 δ2 h2 ι2 P <->
    (instpc (inst ι2 ζ12) fmls /\ P tt (inst ι2 δ2) (inst ι2 h2)).
  Proof.
    unfold smut_assert_formulas. revert δ2 h2.
    induction fmls; cbn [List.fold_right]; intros δ2 h2.
    - rewrite smut_wp_pure. intuition.
      constructor.
    - rewrite smut_wp_bind_right; auto.
      rewrite smut_wp_assert_formula; auto.
      rewrite IHfmls.
      rewrite inst_pathcondition_cons.
      rewrite ?inst_lift.
      intuition.
      apply smut_assert_formulas_dcl.
  Qed.

  Lemma smut_wp_demonic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (s : Term Σ1 ty_bool)
    (kt kf : SMut Γ1 Γ2 AT Σ1) (kt_dcl : smut_dcl kt) (kf_dcl : smut_dcl kf)
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 P :
    instpc ι2 pc2 ->
    smut_wp (smut_demonic_match_bool s kt kf) ζ12 pc2 δ2 h2 ι2 P <->
    (inst (T := fun Σ => Term Σ _) (A := Lit ty_bool) (inst ι2 ζ12) s = true ->
     smut_wp kt ζ12 pc2 δ2 h2 ι2 P) /\
    (inst (T := fun Σ => Term Σ _) (A := Lit ty_bool) (inst ι2 ζ12) s = false ->
     smut_wp kf ζ12 pc2 δ2 h2 ι2 P).
  Proof.
    intros Hpc2. unfold smut_demonic_match_bool.
    unfold smut_wp at 1.
    destruct (term_get_lit_spec (subst (T := fun Σ => Term Σ ty_bool) ζ12 s)) as [[] Heqιs|_]; fold_smut_wp.
    - specialize (Heqιs ι2). rewrite inst_subst in Heqιs. split.
      + intros Hwp. split; auto.
        intros Heq. rewrite Heqιs in Heq. discriminate.
      + intros [Ht Hf]. auto.
    - specialize (Heqιs ι2). rewrite inst_subst in Heqιs. split.
      + intros Hwp. split; auto.
        intros Heq. rewrite Heqιs in Heq. discriminate.
      + intros [Ht Hf]. auto.
    - rewrite smut_wp_demonic_binary.
      split; intros [Ht Hf]; (split; [clear Hf|clear Ht]).
      + rewrite smut_wp_bind_right, smut_wp_assume_formula in Ht; auto.
        cbn in Ht. rewrite inst_sub_id, inst_subst in Ht.
        intros Heq. specialize (Ht Heq). revert Ht.
        eapply kt_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; auto.
        now apply smut_sub_dcl.
      + rewrite smut_wp_bind_right, smut_wp_assume_formula in Hf; auto.
        cbn in Hf. fold_inst_term. rewrite inst_sub_id, inst_subst in Hf.
        intros Heq. unfold is_true in Hf. rewrite negb_true_iff in Hf. specialize (Hf Heq). revert Hf.
        eapply kf_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; auto.
        now apply smut_sub_dcl.
      + rewrite smut_wp_bind_right, smut_wp_assume_formula; auto.
        cbn. rewrite inst_sub_id, inst_subst.
        intros Heq. specialize (Ht Heq). revert Ht.
        eapply kt_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; auto.
        now apply smut_sub_dcl.
      + rewrite smut_wp_bind_right, smut_wp_assume_formula; auto.
        cbn. fold_inst_term. rewrite inst_sub_id, inst_subst.
        intros Heq. unfold is_true in Heq. rewrite negb_true_iff in Heq. specialize (Hf Heq). revert Hf.
        eapply kf_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; auto.
        now apply smut_sub_dcl.
  Qed.

  Lemma smut_wp_angelic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (s : Term Σ1 ty_bool)
    (kt kf : SMut Γ1 Γ2 AT Σ1) (kt_dcl : smut_dcl kt) (kf_dcl : smut_dcl kf)
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 P :
    instpc ι2 pc2 ->
    smut_wp (smut_angelic_match_bool s kt kf) ζ12 pc2 δ2 h2 ι2 P <->
    (inst (T := fun Σ => Term Σ _) (A := Lit ty_bool) (inst ι2 ζ12) s = true /\
     smut_wp kt ζ12 pc2 δ2 h2 ι2 P \/
     inst (T := fun Σ => Term Σ _) (A := Lit ty_bool) (inst ι2 ζ12) s = false /\
     smut_wp kf ζ12 pc2 δ2 h2 ι2 P).
  Proof.
  Admitted.

  Lemma smut_wp_demonic_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ1) (d_dcl : forall x, smut_dcl (d x))
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 P :
    instpc ι2 pc2 ->
    smut_wp (smut_demonic_match_enum t d) ζ12 pc2 δ2 h2 ι2 P <->
    smut_wp (d (inst (T := fun Σ => Term Σ _) (A := 𝑬𝑲 E) (inst ι2 ζ12) t)) ζ12 pc2 δ2 h2 ι2 P.
  Proof.
    intros Hpc2. unfold smut_demonic_match_enum. cbn.
    unfold smut_wp at 1.
    destruct (term_get_lit_spec (subst (T := fun Σ => Term Σ (ty_enum E)) ζ12 t)) as [k Heqιs|]; cbn [Lit] in *.
    - fold_smut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. now rewrite Heqιs.
    - fold_smut_wp. rewrite smut_wp_demonic_finite. split; intros Hwp.
      + specialize (Hwp (inst (T := fun Σ => Term Σ _) (inst ι2 ζ12) t)).
        rewrite smut_wp_bind_right, smut_wp_assume_formula, smut_wp_sub in Hwp; auto.
        rewrite sub_comp_id_right, inst_sub_id in Hwp. cbn in Hwp.
        inster Hwp by now rewrite inst_subst. revert Hwp.
        eapply d_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto.
        now apply smut_sub_dcl.
      + intros x. rewrite smut_wp_bind_right; auto.
        rewrite smut_wp_assume_formula; auto. cbn.
        rewrite inst_subst, inst_sub_id. intros <-.
        rewrite smut_wp_sub. rewrite sub_comp_id_right. revert Hwp.
        eapply d_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto.
        now apply smut_sub_dcl.
      + intros x.
        apply smut_bind_right_dcl.
        apply smut_assume_formula_dcl.
        now apply smut_sub_dcl.
      + assumption.
  Qed.

  Lemma smut_wp_demonic_match_sum {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (x y : 𝑺) (σ τ : Ty) (s : Term Σ1 (ty_sum σ τ))
    (dinl : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ)))  (dinl_dcl : smut_dcl dinl)
    (dinr : SMut Γ1 Γ2 AT (Σ1 ▻ (y :: τ)))  (dinr_dcl : smut_dcl dinr)
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 P :
    instpc ι2 pc2 ->
    smut_wp (smut_demonic_match_sum s dinl dinr) ζ12 pc2 δ2 h2 ι2 P <->
    (forall sl,
        inst (T := fun Σ => Term Σ _) (A := Lit σ + Lit τ) (inst ι2 ζ12) s =
        @inl (Lit σ) (Lit τ) (inst (T := fun Σ => Term Σ _) (A := Lit σ) ι2 sl) ->
        smut_wp dinl (sub_snoc ζ12 (x :: σ) sl) pc2 δ2 h2 ι2 P) /\
    (forall sr,
        inst (T := fun Σ => Term Σ (ty_sum σ τ)) (A := Lit σ + Lit τ) (inst ι2 ζ12) s =
        @inr (Lit σ) (Lit τ) (inst (T := fun Σ => Term Σ τ) (A := Lit τ) ι2 sr) ->
        smut_wp dinr (sub_snoc ζ12 (y :: τ) sr) pc2 δ2 h2 ι2 P).
  Proof.
    intros Hpc2. unfold smut_demonic_match_sum.
    unfold smut_wp at 1. cbn.
    destruct (term_get_sum_spec (subst (T := fun Σ => Term Σ (ty_sum σ τ)) ζ12 s)) as [[sl|sr] Heqιs|_].
    - fold_smut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. split.
      + intros Hwp. split.
        * intros sl' Heq. revert Hwp. rewrite Heqιs in Heq. inversion Heq.
          eapply dinl_dcl; unfold sub_comp;
            rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto.
          now f_equal.
        * intros sr Heq. rewrite Heqιs in Heq. discriminate.
      + intros [Hl Hr]. specialize (Hl sl Heqιs). revert Hl. auto.
    - fold_smut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. split.
      + intros Hwp. split.
        * intros sl Heq. rewrite Heqιs in Heq. discriminate.
        * intros sr' Heq. revert Hwp. rewrite Heqιs in Heq. inversion Heq.
          eapply dinr_dcl; unfold sub_comp;
            rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto.
          now f_equal.
      + intros [Hl Hr]. specialize (Hr sr Heqιs). revert Hr.
        eapply dinr_dcl; unfold sub_comp;
          rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto.
    - fold_smut_wp. rewrite smut_wp_demonic_binary.
      rewrite ?smut_wp_demonicv; auto.
      { split; intros [Hl Hr]; (split; [clear Hr|clear Hl]).
        - intros sl Heqsl. specialize (Hl (inst ι2 sl)).
          rewrite smut_wp_bind_right, smut_wp_assume_formula in Hl; auto.
          rewrite inst_sub_snoc in Hl. cbn in Hl.
          rewrite inst_subst, inst_sub_wk1 in Hl.
          specialize (Hl Heqsl). revert Hl.
          eapply dinl_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
        - intros sr Heqsr. specialize (Hr (inst ι2 sr)).
          rewrite smut_wp_bind_right, smut_wp_assume_formula in Hr; auto.
          rewrite inst_sub_snoc in Hr. cbn in Hr.
          rewrite inst_subst, inst_sub_wk1 in Hr.
          specialize (Hr Heqsr). revert Hr.
          eapply dinr_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
        - intros vl. specialize (Hl (term_lit _ vl)).
          rewrite smut_wp_bind_right, smut_wp_assume_formula; auto.
          rewrite inst_sub_snoc. cbn. rewrite inst_subst, inst_sub_wk1.
          intros Heq. specialize (Hl Heq). revert Hl.
          eapply dinl_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
        - intros vr. specialize (Hr (term_lit _ vr)).
          rewrite smut_wp_bind_right, smut_wp_assume_formula; auto.
          rewrite inst_sub_snoc. cbn. rewrite inst_subst, inst_sub_wk1.
          intros Heq. specialize (Hr Heq). revert Hr.
          eapply dinr_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
      }
      + apply smut_bind_right_dcl; auto.
        apply smut_assume_formula_dcl.
      + apply smut_bind_right_dcl; auto.
        apply smut_assume_formula_dcl.
  Qed.

  Definition smut_wp_demonic_match_pair {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (x y : 𝑺) (σ τ : Ty) (s : Term Σ1 (ty_prod σ τ))
    (d : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (d_dcl : smut_dcl d)
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 (Hpc : instpc ι2 pc2) P :
    smut_wp (smut_demonic_match_pair s d) ζ12 pc2 δ2 h2 ι2 P <->
    (forall sl sr,
        inst (T := fun Σ => Term Σ _) (A := Lit (ty_prod σ τ)) (inst ι2 ζ12) s =
        (inst (T := fun Σ => Term Σ _) (A := Lit σ) ι2 sl,
         inst (T := fun Σ => Term Σ _) (A := Lit τ) ι2 sr) ->
        smut_wp d (sub_snoc (sub_snoc ζ12 (x :: σ) sl) (y :: τ) sr) pc2 δ2 h2 ι2 P).
  Proof.
    unfold smut_demonic_match_pair. cbn - [sub_wk1].
    unfold smut_wp at 1.
    destruct (term_get_pair_spec (subst (T := fun Σ => Term Σ _) ζ12 s)) as [[sl sr] Heqs|];
      fold_smut_wp.
    - specialize (Heqs ι2). rewrite inst_subst in Heqs. split; auto.
      intros Hwp sl2 sr2 Heqs2. rewrite Heqs2 in Heqs.
      inversion Heqs. revert Hwp.
      eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
      f_equal; auto. f_equal; auto.
    - split; intros Hwp.
      { intros sl sr Heqs.
        rewrite smut_wp_demonicv in Hwp; auto. specialize (Hwp (inst ι2 sl)).
        rewrite smut_wp_demonicv in Hwp; auto. specialize (Hwp (inst ι2 sr)).
        rewrite smut_wp_bind_right in Hwp; auto.
        rewrite smut_wp_assume_formula in Hwp; auto.
        rewrite ?inst_sub_snoc in Hwp. cbn - [sub_wk1] in Hwp.
        unfold sub_comp in Hwp. rewrite ?inst_subst, ?inst_sub_wk1 in Hwp.
        specialize (Hwp Heqs). revert Hwp.
        eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto.
        - apply smut_bind_right_dcl; auto.
          apply smut_assume_formula_dcl.
        - apply smut_demonicv_dcl.
          apply smut_bind_right_dcl; auto.
          apply smut_assume_formula_dcl.
      }
      { rewrite smut_wp_demonicv; auto. intros vl.
        rewrite smut_wp_demonicv; auto. intros vr.
        rewrite smut_wp_bind_right; auto.
        rewrite smut_wp_assume_formula; auto.
        unfold sub_comp. rewrite ?inst_sub_snoc. cbn - [sub_wk1].
        rewrite ?inst_subst, ?inst_sub_wk1. intros Heqs.
        specialize (Hwp (lift vl) (lift vr) Heqs). revert Hwp.
        eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto.
        - apply smut_bind_right_dcl; auto.
          apply smut_assume_formula_dcl.
        - apply smut_demonicv_dcl.
          apply smut_bind_right_dcl; auto.
          apply smut_assume_formula_dcl.
      }
  Qed.

  Lemma smut_wp_demonic_freshen_recordpat' {Γ : PCtx} {σs : NCtx 𝑹𝑭 Ty} {Σ1 Δ : LCtx}
    (p : RecordPat σs Δ)
    (Σ2 : LCtx) (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2)
    δ2 h2 (ι2 : SymInstance Σ2) (Hpc : instpc ι2 pc2)
    (P : NamedEnv Lit σs * SymInstance Δ -> SCProp Γ) :
    smut_wp (smut_demonic_freshen_recordpat' id p) ζ12 pc2 δ2 h2 ι2 P <->
    forall (ts : NamedEnv Lit σs) (ιΔ : SymInstance Δ),
      record_pattern_match p ts = ιΔ -> P (ts,ιΔ) (inst ι2 δ2) (inst ι2 h2).
  Proof.
    induction p; cbn - [smut_wp].
    - rewrite smut_wp_pure.
      split; cbn; auto.
      intros HP * Heq.
      subst.
      now destruct (nilView ts).
    - unfold smut_fmap2. rewrite smut_wp_bind; auto.
      rewrite IHp. split; intros Hwp ts ιΔ.
      + destruct (snocView ts) as [ts].
        destruct (snocView ιΔ) as [ιΔ]. cbn.
        specialize (Hwp ts ιΔ).
        remember (record_pattern_match p ts) as ιΔ'.
        intros Heq. dependent elimination Heq.
        specialize (Hwp eq_refl).
        rewrite smut_wp_fmap, smut_wp_sub in Hwp; auto.
        rewrite smut_wp_demonic_termvar in Hwp; auto.
        specialize (Hwp v). cbn in Hwp.
        rewrite ?inst_lift in Hwp.
        change (P (inst ι2 (subst ζ12 (lift ts)) ► (rf :: τ ↦ v) ,
                   inst ι2 (subst ζ12 (lift ιΔ')) ► (x :: τ ↦ v))
                  (inst ι2 δ2) (inst ι2 h2)) in Hwp.
        now rewrite ?inst_subst, ?inst_lift in Hwp.
        clear. unfold spath_mapping_dcl. intros. cbn.
        change
          (inst ι1 (subst ζ01 (lift ts)) ► (rf :: τ ↦ inst ι1 a1) :: inst ι1 (subst ζ01 (lift ιΔ')) ► (x :: τ ↦ inst ι1 a1) =
           inst ι2 (subst ζ02 (lift ts)) ► (rf :: τ ↦ inst ι2 a2) :: inst ι2 (subst ζ02 (lift ιΔ')) ► (x :: τ ↦ inst ι2 a2)).
        rewrite ?inst_subst, ?inst_lift. cbn. now rewrite H1.
      + intros Heq.
        rewrite smut_wp_fmap, smut_wp_sub; auto.
        rewrite smut_wp_demonic_termvar; auto.
        intros v. cbn. rewrite ?inst_lift.
        change (P (inst ι2 (subst ζ12 (lift ts)) ► (rf :: τ ↦ v) ,
                   inst ι2 (subst ζ12 (lift ιΔ)) ► (x :: τ ↦ v))
                  (inst ι2 δ2) (inst ι2 h2)).
        rewrite ?inst_subst, ?inst_lift.
        specialize (Hwp (env_snoc ts (_,_) v) (env_snoc ιΔ (_,_) v)).
        cbn in Hwp. now inster Hwp by now rewrite Heq.
        clear. unfold spath_mapping_dcl. intros. cbn.
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

  Lemma smut_wp_demonic_match_record {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Δ} (t : Term Σ1 (ty_record R))
    (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (d : SMut Γ1 Γ2 AT (Σ1 ▻▻ Δ)) (d_dcl : smut_dcl d)
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 (ι2 : SymInstance Σ2) (Hpc : instpc ι2 pc2)
    (P : A -> SCProp Γ2) :
    smut_wp (smut_demonic_match_record p t d) ζ12 pc2 δ2 h2 ι2 P <->
    forall ts : NamedEnv (Term _) (𝑹𝑭_Ty R),
      inst (T := fun Σ => Term Σ _) (A := Lit (ty_record R)) (inst ι2 ζ12) t = 𝑹_fold (inst ι2 ts) ->
      smut_wp d (ζ12 ►► record_pattern_match p ts) pc2 δ2 h2 ι2 P.
  Proof.
    unfold smut_demonic_match_record. cbn.
    unfold smut_wp at 1.
    destruct (term_get_record_spec (subst (T := fun Σ => Term Σ _) ζ12 t)) as [ts Heqts|];
      fold_smut_wp.
    - specialize (Heqts ι2). rewrite inst_subst in Heqts. split; auto.
      intros Hwp ts2 Heqts2. rewrite Heqts2 in Heqts.
      apply (f_equal (@𝑹_unfold R)) in Heqts.
      rewrite ?𝑹_unfold_fold in Heqts. revert Hwp.
      eapply d_dcl; rewrite ?inst_sub_id; eauto.
      unfold inst; cbn. rewrite ?env_map_cat.
      f_equal.
      change (inst ι2 (record_pattern_match p ts) = inst ι2 (record_pattern_match p ts2)).
      now rewrite ?inst_record_pattern_match, Heqts.
    - rewrite smut_wp_bind; auto.
      split; intros Hwp.
      { intros ts Heqts.
        unfold smut_demonic_freshen_recordpat in Hwp.
        rewrite smut_wp_fmap in Hwp; auto.
        rewrite smut_wp_demonic_freshen_recordpat' in Hwp; auto.
        specialize (Hwp (inst ι2 ts) _ eq_refl).
        rewrite <- inst_record_pattern_match in Hwp.
        remember (record_pattern_match p ts) as ts__R.
        cbn - [smut_wp inst_term] in Hwp.
        rewrite subst_sub_id, inst_lift in Hwp.
        rewrite smut_wp_bind_right, smut_wp_assume_formula in Hwp; auto.
        cbn - [inst_term] in Hwp. fold_inst_term.
        rewrite inst_lift in Hwp. rewrite Heqts in Hwp.
        cbn in Hwp. inster Hwp by admit.
        rewrite inst_lift, smut_wp_sub in Hwp.
        revert Hwp.
        eapply d_dcl; unfold sub_comp; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; eauto.
        unfold inst; cbn.
        rewrite ?env_map_cat.
        f_equal.
        change (inst (inst ι2 ζ12) (sub_id Σ1) = inst ι2 ζ12).
        now rewrite inst_sub_id.
        change (inst (inst ι2 ζ12) (lift (inst ι2 ts__R)) = inst ι2 ts__R).
        now rewrite inst_lift.
        now apply smut_sub_dcl.
        clear. unfold spath_mapping_dcl. destruct a1, a2; cbn - [inst_term].
        intros. fold_inst_term. subst. inversion H1. f_equal; auto.
        admit.
      }
  Admitted.

  Lemma smut_demonic_match_bool_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (s : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df) :
    smut_dcl (smut_demonic_match_bool s dt df).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_bool; auto.
    rewrite H8. intros [Ht Hf].
    split.
    - intros Heq. specialize (Ht Heq). revert Ht.
      eapply dt_dcl; rewrite ?inst_lift; auto.
    - intros Heq. specialize (Hf Heq). revert Hf.
      eapply df_dcl; rewrite ?inst_lift; auto.
  Qed.

  Lemma smut_angelic_match_bool_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (s : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df) :
    smut_dcl (smut_angelic_match_bool s dt df).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_angelic_match_bool; auto.
    rewrite H8. intros [[? Hwp]|[? Hwp]]; [left|right]; split; auto; revert Hwp.
    - eapply dt_dcl; rewrite ?inst_lift; auto.
    - eapply df_dcl; rewrite ?inst_lift; auto.
  Qed.

  Lemma smut_demonic_match_enum_dcl {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ1) (d_dcl : forall K, smut_dcl (d K)) :
    smut_dcl (smut_demonic_match_enum t d).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_enum; auto.
    subst. rewrite H8. eapply d_dcl; eauto.
  Qed.

  Lemma smut_demonic_match_sum_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ x y σ τ} (s : Term Σ (ty_sum σ τ))
    (dinl : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (dinl_dcl : smut_dcl dinl)
    (dinr : SMut Γ1 Γ2 AT (Σ ▻ (y :: τ))) (dinr_dcl : smut_dcl dinr) :
    smut_dcl (smut_demonic_match_sum s dinl dinr).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_sum; auto. cbn.
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

  Lemma smut_demonic_match_pair_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 x y σ τ} (s : Term Σ1 (ty_prod σ τ))
    (d : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (d_dcl : smut_dcl d) :
    smut_dcl (smut_demonic_match_pair s d).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_pair; auto.
    intros Hwp sl sr Heqs. specialize (Hwp (lift (inst ι2 sl)) (lift (inst ι2 sr))).
    rewrite ?inst_lift in Hwp. rewrite <- H8 in Heqs. specialize (Hwp Heqs). revert Hwp.
    eapply d_dcl; unfold sub_comp; rewrite ?inst_sub_snoc, ?inst_lift; auto.
    f_equal; auto. f_equal; auto.
  Qed.

  Lemma smut_demonic_match_record_dcl {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Δ} (t : Term Σ1 (ty_record R))
    (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (d : SMut Γ1 Γ2 AT (Σ1 ▻▻ Δ)) (d_dcl : smut_dcl d) :
    smut_dcl (@smut_demonic_match_record AT R Γ1 Γ2 Σ1 Δ p t d).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_record; auto.
    intros Hwp ζ__R Heqs. specialize (Hwp (lift (inst ι2 ζ__R))).
    rewrite ?inst_lift in Hwp. rewrite <- H8 in Heqs. specialize (Hwp Heqs). revert Hwp.
    eapply d_dcl; eauto. unfold inst at 1 3; cbn. rewrite ?env_map_cat.
    f_equal. exact H8. admit.
  Admitted.

  Lemma smut_produce_chunk_dcl {Γ Σ} (c : Chunk Σ) :
    smut_dcl (Γ1 := Γ) (smut_produce_chunk c).
  Proof.
    unfold smut_produce_chunk. apply smut_state_dcl.
    intros * -> Hδ Hh Hζ. cbn.
    change (List.map (inst ?ι) ?h) with (inst ι h).
    rewrite ?inst_subst. congruence.
  Qed.

  Lemma smut_debug_dcl {AT A DT D} `{InstLaws AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2 Σ1}
    (d : forall Σ2 : LCtx, Sub Σ1 Σ2 -> PathCondition Σ2 -> SStore Γ1 Σ2 -> SHeap Σ2 -> DT Σ2)
    (k : SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_dcl k) :
    smut_dcl (smut_debug d k).
  Proof.
    intros until Q; intros PQ.
    rewrite ?smut_wp_debug.
    eapply k_dcl; eauto.
  Qed.

  Lemma smut_produce_dcl {Γ Σ} (asn : Assertion Σ) :
    smut_dcl (Γ1 := Γ) (smut_produce asn).
  Proof.
    induction asn; cbn.
    - apply smut_assume_formula_dcl.
    - apply smut_produce_chunk_dcl.
    - now apply smut_demonic_match_bool_dcl.
    - now apply smut_demonic_match_enum_dcl.
    - now apply smut_demonic_match_sum_dcl.
    - admit.
    - now apply smut_demonic_match_pair_dcl.
    - admit.
    - now apply smut_demonic_match_record_dcl.
    - admit.
    - now apply smut_bind_right_dcl.
    - now apply smut_demonicv_dcl.
    - apply smut_debug_dcl, smut_pure_dcl.
  Admitted.

  Lemma smut_consume_chunk_dcl {Γ Σ} (c : Chunk Σ) :
    smut_dcl (Γ1 := Γ) (smut_consume_chunk c).
  Proof.
    unfold smut_consume_chunk.
    apply smut_bind_dcl.
    apply smut_get_heap_dcl.
    intros until Q. intros PQ.
  Admitted.

  Lemma smut_consume_dcl {Γ Σ} (asn : Assertion Σ) :
    smut_dcl (Γ1 := Γ) (smut_consume asn).
  Proof.
    induction asn; cbn.
    - apply smut_assert_formula_dcl.
    - apply smut_consume_chunk_dcl.
    - now apply smut_demonic_match_bool_dcl.
    - now apply smut_demonic_match_enum_dcl.
    - now apply smut_demonic_match_sum_dcl.
    - admit.
    - now apply smut_demonic_match_pair_dcl.
    - admit.
    - now apply smut_demonic_match_record_dcl.
    - admit.
    - now apply smut_bind_right_dcl.
    - admit.
    - apply smut_debug_dcl, smut_pure_dcl.
  Admitted.

  Lemma smut_exec_dcl {Γ τ Σ} (s : Stm Γ τ) :
    smut_dcl (Σ0 := Σ) (smut_exec s).
  Proof. Admitted.

  Definition APPROX Γ1 Γ2 AT A {instA : Inst AT A} : Type :=
    forall Σ (ι : SymInstance Σ),
      SMut Γ1 Γ2 AT Σ -> CMut Γ1 Γ2 A -> Prop.
  Arguments APPROX _ _ _ _ {_}.

  Definition bapprox {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (ι1 : SymInstance Σ1) POST δ1 h1,
        ι0 = inst ι1 ζ01 ->
        instpc ι1 pc1 ->
        smut_wp dm ζ01 pc1 δ1 h1 ι1 POST ->
        cmut_wp sm POST (inst ι1 δ1) (inst ι1 h1).

  Definition bapprox2 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall POST δ h,
        smut_wp dm (lift ι0) nil (lift δ) (lift h) env_nil POST ->
        cmut_wp sm POST δ h.

  Lemma bapprox_bapprox2 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm <-> bapprox2 ι dm sm.
  Proof.
    unfold bapprox, bapprox2. split; intros HYP.
    - intros POST δ h Hwp.
      specialize (HYP ctx_nil (lift ι) nil env_nil POST (lift δ) (lift h)).
      rewrite ?inst_lift in HYP. apply HYP; auto. constructor.
    - intros ? ? ? ? ? ? ? Hι Hpc Hwp. specialize (HYP POST (inst ι1 δ1) (inst ι1 h1)).
      apply HYP. revert Hwp.
      apply (dm_dcl Σ1 ε ζ01 _ _ _ (lift ι1)); rewrite ?inst_lift; auto.
      constructor.
  Qed.

  Definition inst_dmut {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (d : SMut Γ1 Γ2 AT Σ) : CMut Γ1 Γ2 A :=
    fun δ h => inst_spath ι (d Σ (sub_id Σ) nil (lift δ) (lift h)).
  Definition inst_dmut' {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (d : SMut Γ1 Γ2 AT Σ) : CMut Γ1 Γ2 A :=
    fun δ h => inst_spath env_nil (d ctx_nil (lift ι) nil (lift δ) (lift h)).

  Definition bapprox3 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall POST δ h,
        cmut_wp (inst_dmut ι0 dm) POST δ h ->
        cmut_wp sm POST δ h.

  Definition bapprox4 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall POST δ h,
        cmut_wp (inst_dmut' ι0 dm) POST δ h ->
        cmut_wp sm POST δ h.

  Lemma bapprox_bapprox3 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm <-> bapprox3 ι dm sm.
  Proof.
    split; unfold bapprox, bapprox3; intros HYP.
    - intros POST δ h Hwp.
      specialize (HYP Σ (sub_id _) nil ι POST (lift δ) (lift h)).
      inster HYP by rewrite ?inst_sub_id; constructor.
      rewrite ?inst_lift in HYP. apply HYP.
      unfold smut_wp. rewrite spath_wp_wp'. exact Hwp.
    - intros ? ? ? ? ? ? ? Hι Hpc Hwp. apply HYP.
      unfold cmut_wp, inst_dmut.
      (* change (spath_wp' (dm Σ (sub_id Σ) nil (lift (inst ι1 δ1)) (lift (inst ι1 h1))) ι *)
      (*                  (fun X : CMutResult Γ2 A => POST (scmutres_value X) (scmutres_state X))). *)
      (* rewrite <- spath_wp_wp'. fold_smut_wp. revert Hwp. *)
      (* eapply dm_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto. *)
      (* constructor. *)
  Admitted.

  Lemma bapprox_bapprox4 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm <-> bapprox4 ι dm sm.
  Proof.
    split; unfold bapprox, bapprox4; intros HYP.
    - intros POST δ h Hwp.
      specialize (HYP ctx_nil (lift ι) nil env_nil POST (lift δ) (lift h)).
      inster HYP by rewrite ?inst_lift; constructor.
      rewrite ?inst_lift in HYP. apply HYP.
      unfold smut_wp. rewrite spath_wp_wp'. exact Hwp.
    - intros ? ? ? ? ? ? ? Hι Hpc Hwp. apply HYP.
      unfold cmut_wp, inst_dmut'.
      (* change (spath_wp' (dm ctx_nil (lift ι) nil (lift (inst ι1 s1))) env_nil *)
      (*                  (fun X : CMutResult Γ2 A => POST (scmutres_value X) (scmutres_state X))). *)
      (* rewrite <- spath_wp_wp'. fold_smut_wp. revert Hwp. *)
      (* eapply dm_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto. *)
      (* constructor. *)
  Admitted.

  Lemma bapprox_demonic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
        (dm1 dm2 : SMut Γ1 Γ2 AT Σ) (sm1 sm2 : CMut Γ1 Γ2 A) :
    bapprox ι dm1 sm1 ->
    bapprox ι dm2 sm2 ->
    bapprox ι (smut_demonic_binary dm1 dm2) (cmut_demonic_binary sm1 sm2).
  Proof.
    intros ? ?. unfold bapprox. intros *.
    rewrite smut_wp_demonic_binary, cmut_wp_demonic_binary.
    intuition.
  Qed.

  Lemma bapprox_angelic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
        (dm1 dm2 : SMut Γ1 Γ2 AT Σ) (sm1 sm2 : CMut Γ1 Γ2 A) :
    bapprox ι dm1 sm1 ->
    bapprox ι dm2 sm2 ->
    bapprox ι (smut_angelic_binary dm1 dm2) (cmut_angelic_binary sm1 sm2).
  Proof.
    intros ? ?. unfold bapprox. intros *.
    rewrite smut_wp_angelic_binary, cmut_wp_angelic_binary.
    intuition.
  Qed.

  Lemma bapprox_angelicv {Γ Σ ς τ} (ι : SymInstance Σ)
        (dm : SMut Γ Γ Unit (Σ ▻ (ς,τ))) (d_dcl : smut_dcl dm)
        (sm : Lit τ -> CMut Γ Γ unit) :
    (forall v, bapprox (env_snoc ι _ v) dm (sm v)) ->
    bapprox ι
      (smut_angelicv ς τ dm)
      (cmut_angelic sm).
  Proof.
    unfold bapprox. intros HYP * Hι Hpc.
    rewrite smut_wp_angelicv, cmut_wp_angelic; auto.
    intros [vτ Hwp]. exists vτ.
    apply (HYP vτ _ (sub_snoc ζ01 (ς :: τ) (term_lit τ vτ)) pc1); auto.
    subst ι; reflexivity.
  Qed.

  Lemma bapprox_angelicvs {AT A} `{Subst AT, Inst AT A} {Γ Σ Δ} (ι : SymInstance Σ)
        (dm : SMut Γ Γ AT (Σ ▻▻ Δ)) (d_dcl : smut_dcl dm)
        (sm : SymInstance Δ -> CMut Γ Γ A) :
    (forall ιΔ, bapprox (env_cat ι ιΔ) dm (sm ιΔ)) ->
    bapprox ι
      (smut_angelicvs Δ dm)
      (cmut_angelic sm).
  Proof.
    unfold bapprox. intros HYP * Hι Hpc.
    rewrite smut_wp_angelicvs, cmut_wp_angelic; auto.
    intros [ιΔ Hwp]. exists ιΔ. revert Hwp.
    apply HYP; auto.
  Admitted.

  Lemma bapprox_demonicv {AT A} `{InstLaws AT A} {Γ Σ ς τ} (ι : SymInstance Σ)
        (dm : SMut Γ Γ AT (Σ ▻ (ς,τ))) (d_dcl : smut_dcl dm)
        (sm : Lit τ -> CMut Γ Γ A) :
    (forall v, bapprox (env_snoc ι _ v) dm (sm v)) ->
    bapprox ι
      (smut_demonicv ς τ dm)
      (cmut_demonic sm).
  Proof.
    unfold bapprox. intros HYP * Hι Hpc.
    rewrite smut_wp_demonicv, cmut_wp_demonic; auto.
    intros Hwp vτ.
    apply (HYP vτ _ (sub_snoc ζ01 (ς :: τ) (term_lit τ vτ)) pc1); auto.
    subst ι; reflexivity.
  Qed.

  Lemma bapprox2_demonicv {AT A} `{InstLaws AT A} {Γ Σ ς τ} (ι : SymInstance Σ)
        (dm : SMut Γ Γ AT (Σ ▻ (ς,τ))) (d_dcl : smut_dcl dm)
        (sm : Lit τ -> CMut Γ Γ A) :
    (forall v, bapprox2 (env_snoc ι _ v) dm (sm v)) ->
    bapprox2 ι
      (smut_demonicv ς τ dm)
      (cmut_demonic sm).
  Proof.
    unfold bapprox2. intros HYP POST δ h Hwp.
    rewrite cmut_wp_demonic. intros vτ.
    apply HYP.
    rewrite smut_wp_demonicv in Hwp; eauto. apply (Hwp vτ). constructor.
  Qed.

  Lemma bapprox_pure {AT A} `{InstLaws AT A} {Γ Σ} (ι : SymInstance Σ) (t : AT Σ) (a : A) :
    a = inst ι t ->
    bapprox ι (smut_pure (Γ := Γ) t) (cmut_pure a).
  Proof.
    unfold bapprox. intros -> * -> Hpc.
    rewrite smut_wp_pure. intros Hwp; apply Hwp.
  Qed.

  Lemma bapprox_block {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) :
    bapprox ι (@smut_block Γ1 Γ2 AT Σ) cmut_block.
  Proof. unfold bapprox; auto. Qed.

  Lemma bapprox_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
    (dma : SMut Γ1 Γ2 AT Σ0) (sma : CMut Γ1 Γ2 A)
    (dmf : smut_arrow Γ2 Γ3 AT BT Σ0)
    (dmf_dcl : smut_arrow_dcl dmf)
    (smf : A -> CMut Γ2 Γ3 B) :
    bapprox ι0 dma sma ->
    (forall (a0 : AT Σ0),
        bapprox ι0 (dmf Σ0 (sub_id _) a0) (smf (inst ι0 a0))) ->
    bapprox ι0 (smut_bind dma dmf) (cmut_bind sma smf).
  Proof.
    unfold bapprox. intros Hapa Hapf * Hι Hpc.
    rewrite smut_wp_bind; eauto. rewrite cmut_wp_bind.
    intros Hwp. eapply Hapa; eauto. revert Hwp.
    apply smut_wp_monotonic. intros a δ2 h2 Hwp.
    apply Hapf in Hwp; auto. revert Hwp. now rewrite ?inst_lift.
  Qed.

  Lemma bapprox_bind_right {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
    (dma : SMut Γ1 Γ2 AT Σ0) (sma : CMut Γ1 Γ2 A)
    (dmb : SMut Γ2 Γ3 BT Σ0) (dmb_dcl : smut_dcl dmb) (smb : CMut Γ2 Γ3 B) :
    bapprox ι0 dma sma ->
    bapprox ι0 dmb smb ->
    bapprox ι0 (smut_bind_right dma dmb) (cmut_bind_right sma smb).
  Proof.
    unfold bapprox. intros A1 A2 * -> Hpc1.
    rewrite smut_wp_bind_right; auto.
    unfold cmut_bind_right. rewrite cmut_wp_bind.
    intros Hwp; eapply A1 in Hwp; eauto. revert Hwp.
    apply cmut_wp_monotonic; intros a δ2 h2.
    intros Hwp; eapply A2 in Hwp; eauto. revert Hwp.
    now rewrite ?inst_lift.
  Qed.

  Lemma bapprox_bind_left {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
    (dma : SMut Γ1 Γ2 AT Σ0) (sma : CMut Γ1 Γ2 A)
    (dmb : SMut Γ2 Γ3 BT Σ0) (dmb_dcl : smut_dcl dmb) (smb : CMut Γ2 Γ3 B) :
    bapprox ι0 dma sma ->
    bapprox ι0 dmb smb ->
    bapprox ι0 (smut_bind_left dma dmb) (cmut_bind_left sma smb).
  Proof.
    intros A1 A2. unfold bapprox. intros * -> Hpc1.
    rewrite smut_wp_bind_left; auto.
    unfold cmut_bind_left. rewrite cmut_wp_bind.
    intros Hwp; eapply A1 in Hwp; eauto. revert Hwp.
    apply cmut_wp_monotonic; intros a δ2 h2. rewrite cmut_wp_bind.
    intros Hwp; eapply A2 in Hwp; eauto. revert Hwp.
    now rewrite ?inst_lift.
  Qed.

  Lemma bapprox2_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
    bapprox2
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_assume_formula fml)
      (cmut_assume_formula ι fml).
  Proof.
    unfold bapprox2. intros POST δ h.
    rewrite smut_wp_assume_formula; auto. rewrite ?inst_lift.
    intuition.
    constructor.
  Qed.

  Lemma bapprox_angelic {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ Σ} (ι : SymInstance Σ)
    (dm : AT Σ -> SMut Γ Γ BT Σ)
    (sm : A -> CMut Γ Γ B) :
    (forall a, bapprox ι (dm a) (sm (inst ι a))) ->
    bapprox ι
      (smut_angelic dm)
      (cmut_angelic sm).
  Proof.
    intros HYP. unfold bapprox. intros * Hι Hpc.
    rewrite smut_wp_angelic, cmut_wp_angelic.
    intros [a Hwp]. exists (inst ι a).
    revert Hwp. apply HYP; auto.
  Qed.

  Lemma bapprox_sub {AT A} `{Inst AT A, Subst AT} {Γ Σ0 Σ1} (ζ01 : Sub Σ0 Σ1)
    (d : SMut Γ Γ AT Σ0) (s : CMut Γ Γ A) (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1) :
    ι0 = inst ι1 ζ01 ->
    bapprox ι0 d s -> bapprox ι1 (smut_sub ζ01 d) s.
  Proof.
    intros Hι0 Hap. unfold bapprox. intros * Hι1 Hpc2.
    rewrite smut_wp_sub. apply Hap; auto.
    unfold sub_comp; rewrite inst_subst; now subst.
  Qed.

  Lemma bapprox_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_assume_formula fml)
      (cmut_assume_formula ι fml).
  Proof.
    unfold bapprox. intros * -> Hpc Hwp Hfml. revert Hwp.
    rewrite smut_wp_assume_formula; eauto. cbn. intuition.
  Qed.

  Lemma bapprox_assert_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_assert_formula fml)
      (cmut_assert_formula ι fml).
  Proof.
    unfold bapprox. intros * Hι Hpc1.
    rewrite smut_wp_assert_formula, cmut_wp_assert_formula; auto.
    intuition.
  Qed.

  Lemma bapprox_assert_formulak {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (fml : Formula Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm ->
    bapprox ι (smut_assert_formulak fml dm) (cmut_assert_formulak ι fml sm).
  Proof.
    intros HYP. unfold bapprox. intros * -> Hpc.
    rewrite smut_wp_assert_formulak; auto.
    rewrite cmut_wp_assert_formulak.
    intros [Hfml Hwp]; split; auto; revert Hwp.
    apply HYP; auto.
  Qed.

  Lemma bapprox_assert_formulask {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (fmls : List Formula Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm ->
    bapprox ι (smut_assert_formulask fmls dm) (cmut_assert_formulask ι fmls sm).
  Proof.
  Admitted.

  Lemma bapprox_state {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0} (ι0 : SymInstance Σ0)
    (f : forall Σ1 (ζ01 : Sub Σ0 Σ1), SStore Γ1 Σ1 -> SHeap Σ1 -> SMutResult Γ2 AT Σ1)
    (g : LocalStore Γ1 -> SCHeap -> CMutResult Γ2 A)
    (fg : forall Σ1 ζ01 δ1 h1 ι1,
        ι0 = inst ι1 ζ01 -> inst ι1 (f Σ1 ζ01 δ1 h1) = g (inst ι1 δ1) (inst ι1 h1)) :
    bapprox ι0 (smut_state f) (cmut_state g).
  Proof.
    unfold bapprox. intros * Hι Hpc.
    rewrite smut_wp_state, cmut_wp_state.
    specialize (fg Σ1 ζ01 δ1 h1 ι1 Hι).
    destruct (f Σ1 ζ01 _ _) as [a1 δ2 h2]. cbn in *.
    destruct (g _ _) as [a δ3 h3].
    inversion fg. now subst.
  Qed.

  Lemma bapprox_produce_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_produce_chunk c)
      (cmut_produce_chunk (inst ι c)).
  Proof.
    unfold bapprox. intros * Hι Hpc.
    unfold smut_produce_chunk, cmut_produce_chunk.
    rewrite smut_wp_state, cmut_wp_state. cbn. subst.
    now rewrite inst_subst.
  Qed.

  Lemma bapprox_demonic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (s : Term Σ1 ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ1) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df)
    (st sf : CMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
    bapprox ι dt st ->
    bapprox ι df sf ->
    bapprox
      ι
      (smut_demonic_match_bool s dt df)
      (cmut_match_bool (inst ι s) st sf).
  Proof.
    intros ? ?. unfold bapprox. intros * -> ?.
    rewrite smut_wp_demonic_match_bool; auto.
    rewrite cmut_wp_match_bool.
    destruct (inst (inst ι1 ζ01) s); intuition.
  Qed.

  Lemma bapprox_demonic_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (dm : Lit (ty_enum E) -> SMut Γ1 Γ2 AT Σ1) (dm_dcl : forall x, smut_dcl (dm x))
    (sm : Lit (ty_enum E) -> CMut Γ1 Γ2 A)
    (ι : SymInstance Σ1) :
    (forall k, bapprox ι (dm k) (sm k)) ->
    bapprox
      ι
      (smut_demonic_match_enum t dm)
      (cmut_match_enum (inst (T := fun Σ => Term Σ (ty_enum E)) ι t) sm).
  Proof.
    unfold bapprox. intros Hap * ? Hpc. subst.
    rewrite smut_wp_demonic_match_enum; auto. now apply Hap.
  Qed.

  Lemma bapprox_demonic_match_sum {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} {x y : 𝑺} {σ τ} (s : Term Σ1 (ty_sum σ τ))
    (dinl : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ))) (dinl_dcl : smut_dcl dinl)
    (dinr : SMut Γ1 Γ2 AT (Σ1 ▻ (y :: τ))) (dinr_dcl : smut_dcl dinr)
    (sinl : Lit σ -> CMut Γ1 Γ2 A) (sinr : Lit τ -> CMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
    (forall v, bapprox (env_snoc ι _ v) dinl (sinl v)) ->
    (forall v, bapprox (env_snoc ι _ v) dinr (sinr v)) ->
    bapprox
      ι
      (smut_demonic_match_sum s dinl dinr)
      (cmut_match_sum (inst (T := fun Σ => Term Σ (ty_sum σ τ)) (A := Lit σ + Lit τ) ι s) sinl sinr).
  Proof.
    unfold bapprox. intros Hapl Hapr * ? Hpc.
    rewrite smut_wp_demonic_match_sum; auto. intros [Hl Hr].
    destruct (inst ι s) eqn:Heqs; [ clear Hr | clear Hl ]; subst ι.
    + specialize (Hl (term_lit σ l) Heqs). revert Hl. now apply Hapl.
    + specialize (Hr (term_lit τ l) Heqs). revert Hr. now apply Hapr.
  Qed.

  Lemma bapprox_demonic_match_pair {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} {x y : 𝑺} {σ τ} (s : Term Σ1 (ty_prod σ τ))
    (dm : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (dm_dcl : smut_dcl dm)
    (sm : Lit σ -> Lit τ -> CMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
    (forall vl vr, bapprox (env_snoc (env_snoc ι _ vl) _ vr) dm (sm vl vr)) ->
    bapprox
      ι
      (smut_demonic_match_pair s dm)
      (cmut_match_pair (inst (T := fun Σ => Term Σ (ty_prod σ τ)) (A := Lit σ * Lit τ) ι s) sm).
  Proof.
    unfold bapprox. intros Hap * ? Hpc.
    rewrite smut_wp_demonic_match_pair; auto. intros Hwp.
    destruct (inst ι s) as [vl vr] eqn:Heqs. subst ι.
    specialize (Hwp (lift vl) (lift vr) Heqs). revert Hwp.
    now apply Hap.
  Qed.

  Lemma bapprox_demonic_match_record {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ0 Δ} (t : Term Σ0 (ty_record R))
    (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (dm : SMut Γ1 Γ2 AT (Σ0 ▻▻ Δ)) (dm_dcl : smut_dcl dm)
    (sm : SymInstance Δ -> CMut Γ1 Γ2 A) (ι : SymInstance Σ0) :
    (forall ι__Δ : SymInstance Δ, bapprox (env_cat ι ι__Δ) dm (sm ι__Δ)) ->
    bapprox
      ι
      (smut_demonic_match_record p t dm)
      (cmut_match_record p (inst (T := fun Σ => Term Σ (ty_record R)) ι t) sm).
  Proof.
    unfold bapprox. intros Hap * Hι Hpc.
    rewrite smut_wp_demonic_match_record; auto. intros Hwp.
    unfold cmut_match_record.
    specialize (Hwp (lift (𝑹_unfold (inst (T := fun Σ => Term Σ _) ι t)))).
    inster Hwp by now rewrite inst_lift, 𝑹_fold_unfold, Hι.
    eapply Hap; eauto. cbn [Lit].
    generalize (𝑹_unfold (inst (T := fun Σ => Term Σ (ty_record R)) (A := 𝑹𝑻 R) ι t)).
    subst. clear. intros ts. unfold inst at 2; cbn.
    rewrite env_map_cat. f_equal.
    change (record_pattern_match p ts = inst ι1 (record_pattern_match p (lift ts))).
    now rewrite inst_record_pattern_match, inst_lift.
  Qed.

  Lemma bapprox_debug {AT A DT D} `{InstLaws AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2 Σ0}
    (ι : SymInstance Σ0)
    (d : forall Σ1, Sub Σ0 Σ1 -> PathCondition Σ1 -> SStore Γ1 Σ1 -> SHeap Σ1 -> DT Σ1)
    (dm : SMut Γ1 Γ2 AT Σ0) sm :
    bapprox ι dm sm ->
    bapprox ι (smut_debug d dm) sm.
  Proof.
    intros HYP. unfold bapprox. intros * -> Hpc Hwp.
    eapply HYP; eauto. apply Hwp.
  Qed.

  Lemma bapprox_produce {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_produce asn)
      (cmut_produce ι asn).
  Proof.
    induction asn; cbn - [subst].
    - apply bapprox_assume_formula.
    - apply bapprox_produce_chunk.
    - apply bapprox_demonic_match_bool; auto using smut_produce_dcl.
    - apply bapprox_demonic_match_enum; auto using smut_produce_dcl.
    - apply bapprox_demonic_match_sum; auto using smut_produce_dcl.
    - admit.
    - apply bapprox_demonic_match_pair; auto using smut_produce_dcl.
    - admit.
    - apply bapprox_demonic_match_record; auto using smut_produce_dcl.
    - admit.
    - apply bapprox_bind_right; auto using smut_produce_dcl.
    - apply bapprox_demonicv; auto using smut_produce_dcl.
    - now apply bapprox_debug, bapprox_pure.
  Admitted.

  Lemma bapprox_consume_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_consume_chunk c)
      (cmut_consume_chunk (inst ι c)).
  Proof.
    unfold bapprox. intros * Hι Hpc.
    unfold smut_consume_chunk, cmut_consume_chunk.
    unfold smut_get_heap, cmut_get_heap.
    unfold smut_put_heap, cmut_put_heap.
    rewrite smut_wp_bind, cmut_wp_bind; auto.
    rewrite smut_wp_state, cmut_wp_state.
    rewrite smut_wp_bind; auto.
    rewrite smut_wp_angelic_list. intros [[Δpc h'] [HIn Hwp]].
    rewrite subst_sub_id in HIn.
    cbn in Hwp. rewrite smut_wp_bind_right in Hwp; auto.
    rewrite smut_wp_assert_formulas in Hwp; auto.
    rewrite ?inst_lift in Hwp. destruct Hwp as [HΔpc Hwp].
    rewrite smut_wp_state in Hwp; auto. cbn in Hwp, HIn.
    rewrite ?inst_subst, ?inst_lift in Hwp. cbn.
    rewrite cmut_wp_angelick_list.
    exists (inst ι h').
    split.
    - apply base.elem_of_list_In in HIn.
      unfold extract_chunk_eqb, extract_scchunk_eqb in *.
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
      + destruct (match_scchunk_eqb_spec (inst ι c) (inst ι c')); auto.
    - cbn; now subst.
    - apply smut_state_dcl. intros * ->. cbn.
      rewrite ?inst_subst, ?inst_lift. congruence.
    - admit.
    - admit.
  Admitted.

  Lemma bapprox_consume {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_consume asn)
      (cmut_consume ι asn).
  Proof.
    induction asn; cbn - [subst].
    - apply bapprox_assert_formula.
    - apply bapprox_consume_chunk.
    - apply bapprox_demonic_match_bool; auto using smut_consume_dcl.
    - apply bapprox_demonic_match_enum; auto using smut_consume_dcl.
    - apply bapprox_demonic_match_sum; auto using smut_consume_dcl.
    - admit.
    - apply bapprox_demonic_match_pair; auto using smut_consume_dcl.
    - admit.
    - apply bapprox_demonic_match_record; auto using smut_consume_dcl.
    - admit.
    - apply bapprox_bind_right; auto using smut_consume_dcl.
    - apply bapprox_angelicv; auto using smut_consume_dcl.
    - now apply bapprox_debug, bapprox_pure.
  Admitted.

  Lemma bapprox_call {Γ Δ τ Σ} (c : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) (ι : SymInstance Σ) :
    bapprox ι (@smut_call Γ Δ τ Σ c ts) (cmut_call c (inst ι ts)).
  Proof.
    destruct c as [Σ__c δ pre result post]; cbn [smut_call cmut_call].
    apply bapprox_angelicvs. admit.
    intros ιc. change (SymInstance Σ__c) in ιc.
    unfold bapprox. intros * Hι Hpc.
    destruct (catView ζ01) as [ζ01 ζc].
    change (Sub Σ Σ1) in ζ01.
    change (Sub Σ__c Σ1) in ζc.
    rewrite smut_wp_assert_formulask; auto.
    rewrite cmut_wp_assert_formulask.
    rewrite ?inst_formula_eqs.
    rewrite ?inst_subst, ?inst_lift.
    intros [Hfmls Hwp]. split.
    - admit.
    - rewrite smut_wp_sub in Hwp. revert Hwp.
      rewrite sub_comp_cat_right.
      eapply bapprox_bind_right; eauto. admit.
      admit.
      eapply bapprox_demonicv. admit.
      intros v.
      apply bapprox_bind_right; auto. admit.
      admit.
      admit.
    - admit.
  Admitted.

  Lemma bapprox_eval_exp {Γ Σ τ} (e : Exp Γ τ) (ι : SymInstance Σ) :
    bapprox ι (smut_eval_exp e) (cmut_eval_exp e).
  Proof.
    unfold smut_eval_exp, cmut_eval_exp.
    apply bapprox_state. intros. cbn. f_equal.
    now rewrite eval_exp_inst.
  Qed.

  Lemma bapprox_pushpop {AT A} `{InstLaws AT A} {Γ1 Γ2 x σ Σ} (ι : SymInstance Σ) (a : Term Σ σ)
    (dm : SMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) (dm_dcl : smut_dcl dm)
    (sm : CMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) A) :
    bapprox ι dm sm ->
    bapprox ι (smut_pushpop a dm) (cmut_pushpop (inst ι a) sm).
  Proof.
    intros Hap. unfold smut_pushpop, cmut_pushpop.
    apply bapprox_bind_right; auto.
    apply smut_bind_left_dcl; auto.
    apply smut_pop_local_dcl.
    unfold smut_push_local, cmut_push_local.
    apply bapprox_state. intros. cbn.
    f_equal. f_equal. subst. now rewrite <- inst_subst.
    apply bapprox_bind_left; eauto.
    apply smut_pop_local_dcl.
    unfold smut_pop_local, cmut_pop_local.
    apply bapprox_state. intros. cbn.
    f_equal. subst. now destruct (snocView δ1).
  Qed.

  Lemma bapprox_pushspops {AT A} `{InstLaws AT A} {Γ1 Γ2 Δ Σ} (ι : SymInstance Σ)
    (dm : SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT Σ) (dm_dcl : smut_dcl dm)
    (sm : CMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) (Hap : bapprox ι dm sm) :
    forall (δ__sym : SStore Δ Σ) (δ__sc : LocalStore Δ),
      δ__sc = inst ι δ__sym ->
      bapprox ι (smut_pushspops δ__sym dm) (cmut_pushspops δ__sc sm).
  Proof. Admitted.

  Lemma bapprox_exec {Γ σ} (s : Stm Γ σ) :
    forall Σ (ι : SymInstance Σ),
      bapprox ι (smut_exec s) (cmut_exec s).
  Proof.
    induction s; cbn [smut_exec cmut_exec]; intros Σ ι.
    - unfold bapprox. cbn. auto.
    - now apply bapprox_eval_exp.
    - apply bapprox_bind; auto. admit.
      intros a. apply bapprox_pushpop; auto.
      apply smut_exec_dcl; auto.
    - apply bapprox_pushspops;
        rewrite ?inst_lift;
        auto using smut_exec_dcl.
    - apply bapprox_bind; auto. admit.
      intros a.
      apply bapprox_bind_right; auto.
      apply smut_pure_dcl.
      apply bapprox_state.
      intros * ->; cbn.
      f_equal. rewrite <- inst_subst.
      unfold inst at 1; cbn.
      now rewrite env_map_update.
      now apply bapprox_pure.
    - destruct (CEnv f).
      + apply bapprox_bind; auto. admit. admit.
        intros ?. apply bapprox_call.
      + admit.
    - apply bapprox_bind. admit.
      { apply bapprox_state. cbn; auto. }
      intros δ0. apply bapprox_bind_right.
      apply smut_bind_left_dcl. apply smut_exec_dcl.
      apply smut_put_local_dcl.
      { apply bapprox_state. cbn; intros.
        now rewrite inst_subst, inst_lift. }
      admit.
    - apply bapprox_bind. admit. admit. intros args.
      apply bapprox_call.
    - admit.
    - apply bapprox_bind_right; auto. apply smut_exec_dcl.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t. admit.
    - apply bapprox_block.
    - admit.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t. apply bapprox_demonic_match_sum. admit. admit.
      + intros ?. apply bapprox_pushpop; auto using smut_exec_dcl.
      + intros ?. apply bapprox_pushpop; auto using smut_exec_dcl.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t. apply bapprox_demonic_match_pair. admit.
      intros ? ?. apply bapprox_pushspops; auto using smut_exec_dcl.
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
      apply bapprox_bind_right. apply smut_pure_dcl.
      apply (bapprox_produce_chunk (chunk_ptsreg reg t)).
      now apply bapprox_pure.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t.
      apply (bapprox_angelic (AT := fun Σ => Term Σ τ)).
      intros t'. apply bapprox_bind_right. admit.
      (* apply bapprox_consume_chunk. *)
      admit.
      apply bapprox_bind_right. apply smut_pure_dcl.
      apply (bapprox_produce_chunk (chunk_ptsreg reg t)).
      now apply bapprox_pure.
    - admit.
    - admit.
  Admitted.

  Lemma bapprox_contract {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) (ι : SymInstance (sep_contract_logic_variables c)) :
    bapprox ι (@smut_contract Γ τ c s) (@cmut_contract Γ τ c s ι).
  Proof.
    unfold smut_contract, cmut_contract; destruct c as [Σ δ pre result post]; cbn in *.
    apply bapprox_bind_right. admit.
    apply bapprox_produce.
    apply bapprox_bind. admit.
    apply bapprox_exec.
    intros res.
    eapply bapprox_sub; eauto.
    rewrite inst_sub_snoc, inst_sub_id.
    apply bapprox_consume.
  Admitted.

  Lemma symbolic_sound {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    ValidContractNoEvar c body ->
    ValidContractCMut c body.
  Proof.
    unfold ValidContractNoEvar, ValidContractCMut. intros Hwp.
    unfold ForallNamed in Hwp. rewrite Forall_forall in Hwp.
    intros ι. cbn. specialize (Hwp ι).
    pose proof (bapprox_contract c body) as H.
    specialize (H ι _ (sub_id _) nil ι (fun _ _ _ => True)).
    specialize (H (sep_contract_localstore c) nil).
    rewrite inst_sub_id in H. inster H by constructor.
    apply H. clear H.
    unfold smut_contract_outcome in Hwp.
  Admitted.

  (* Print Assumptions smut_wp_assume_formula. *)
  (* Print Assumptions smut_wp_bind. *)
  (* Print Assumptions smut_wp_bind_right. *)
  (* Print Assumptions smut_wp_equiv. *)
  (* Print Assumptions smut_wp_fmap. *)
  (* Print Assumptions smut_wp_fresh. *)
  (* Print Assumptions smut_wp_match_pair. *)
  (* Print Assumptions smut_wp_match_sum. *)
  (* Print Assumptions smut_wp_pair. *)
  (* Print Assumptions smut_wp_pure. *)
  (* Print Assumptions smut_wp_sub. *)

  (* Print Assumptions smut_pure_dcl. *)
  (* Print Assumptions smut_fresh_dcl. *)
  (* Print Assumptions smut_arrow_dcl_specialize. *)
  (* Print Assumptions smut_arrow_dcl_specialize. *)
  (* Print Assumptions smut_bind_dcl. *)
  (* Print Assumptions smut_bind_right_dcl. *)

  (* Print Assumptions symbolic_sound. *)

End Soundness.
