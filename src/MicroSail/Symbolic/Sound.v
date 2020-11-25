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
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.

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
  Import SCMUT.MUT.

  Module DynMutV1Soundness.

    Import DynMutV1.

    Global Instance inst_heap : Inst SymbolicHeap SCHeap :=
      instantiate_list.
    Global Instance instlaws_heap : InstLaws SymbolicHeap SCHeap.
    Proof. apply instantiatelaws_list. Qed.

    (* Relate two symbolic instances at different points during execution. This
       essentially encodes a preorder on the total space { Σ & SymInstance Σ },
       which encodes that ι2 is a future of ι1, i.e. it is derived by compatible
       for existing variables and values for new universal variables. *)
    Definition syminstance_rel {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2) : Prop :=
      inst ι2 ζ = ι1.

    Lemma syminstance_rel_refl {Σ} (ι : SymInstance Σ) :
      syminstance_rel (sub_id Σ) ι ι.
    Proof. apply inst_sub_id. Qed.

    Lemma syminstance_rel_snoc {Σ1 Σ2 x τ} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) ι2 :
      forall t v,
        syminstance_rel (env_snoc ζ (x,τ) t) (env_snoc ι1 (x,τ) v) ι2 <->
        syminstance_rel ζ ι1 ι2 /\ v = inst ι2 t.
    Proof.
      unfold syminstance_rel. intros. split.
      - cbn; intros.
        now dependent elimination H.
      - cbn; intros []; subst; now cbn.
    Qed.

    Lemma syminstance_rel_comp {Σ0 Σ1 Σ2} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2)
          (ι0 : SymInstance Σ0) (ι2 : SymInstance Σ2):
      syminstance_rel (sub_comp ζ1 ζ2) ι0 ι2 <->
      syminstance_rel ζ1 ι0 (inst ι2 ζ2).
    Proof. unfold syminstance_rel. now rewrite <- inst_subst. Qed.

    Lemma syminstance_rel_wk1 {Σ : NCtx 𝑺 Ty} {x τ} (ι : SymInstance Σ) (v : Lit τ) :
      syminstance_rel sub_wk1 ι (ι ► ((x, τ) ↦ v)).
    Proof. apply inst_sub_wk1. Qed.

    (* A relation that links semi-concrete states with symbolic states. This
       simply requires that when instantiating the symbolic state you get the
       semi-concrete one (and the path-condition is true). Note that the
       equality used in the heap instantiation requires the symbolic and the
       semi-concrete executor to be in lock step with respect to the heap: i.e.
       the symbolic executor and the semi-concrete executor need to end up with
       a heap that has the same chunks in the same order. This can be relaxed
       later to allow permutations or even some kind of semantic equivalence. *)
    Definition represents {Γ Σ} (ι : SymInstance Σ) (s__sym : SymbolicState Γ Σ) (s__sc : SCState Γ) : Prop :=
      inst                ι (symbolicstate_heap s__sym)       = scstate_heap s__sc /\
      inst                ι (symbolicstate_localstore s__sym) = scstate_localstore s__sc /\
      inst_pathcondition  ι (symbolicstate_pathcondition s__sym).

    (* This is a preservation lemma for state representation. The symbolic
       executor is allwed to add a formula (local assumption) to the
       path-condition if it's true for the current instance ι. We only
       need the -> direction I think. *)
    Lemma represents_assume_formula {Γ Σ} (ι : SymInstance Σ) (s__sym : SymbolicState Γ Σ) (s__sc : SCState Γ) fml :
      represents ι s__sym s__sc /\ inst_formula ι fml <->
      represents ι (symbolicstate_assume_formula fml s__sym) s__sc.
    Proof. unfold represents; destruct s__sym, s__sc; cbn; intuition. Qed.

    Lemma represents_produce_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ)
          (s__sym : SymbolicState Γ Σ) (s__sc : SCState Γ) :
      represents ι s__sym s__sc <->
      represents ι (symbolicstate_produce_chunk c s__sym) (scstate_produce_chunk (inst ι c) s__sc).
    Proof.
      unfold represents; destruct s__sym, s__sc; cbn - [inst].
      change (inst ι (cons c ?h)) with (cons (inst ι c) (inst ι h)).
      apply and_iff_compat_r.
      split; intros; subst; auto.
      now dependent elimination H.
    Qed.

    Lemma inst_subst_formula {Σ1 Σ2} (ι : SymInstance Σ2) (ζ : Sub Σ1 Σ2) (fml : Formula Σ1) :
      inst_formula (inst ι ζ) fml <-> inst_formula ι (subst ζ fml).
    Proof. destruct fml; cbn - [inst]; now rewrite !inst_subst. Qed.

    Lemma inst_subst_pathcondition {Σ1 Σ2} (ι : SymInstance Σ2) (ζ : Sub Σ1 Σ2) (pc : PathCondition Σ1) :
      inst_pathcondition (inst ι ζ) pc <-> inst_pathcondition ι (subst ζ pc).
    Proof.
      induction pc; cbn - [inst].
      - reflexivity.
      - rewrite inst_subst_formula.
        apply and_iff_compat_l, IHpc.
    Qed.

    (* This is another preservation lemma. This one covers every state change in
       the symbolic executor that is implemented via a universal variable
       substitution, i.e. local equality assumptions that are substituted right
       away and allocation of fresh universal variables. *)
    Lemma represents_rel {Γ Σ0 Σ1} (ζ1 : Sub Σ0 Σ1) (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1) :
      syminstance_rel ζ1 ι0 ι1 ->
      forall (s__sym : SymbolicState Γ Σ0) (s__sc : SCState Γ),
        represents ι0 s__sym s__sc <->
        represents ι1 (subst ζ1 s__sym) s__sc.
    Proof.
      unfold syminstance_rel, represents; intros. subst.
      destruct s__sym as [pc δ__sym h__sym], s__sc as [δ__sc h__sc];
        cbn - [inst inst_pathcondition].
      now rewrite !inst_subst, inst_subst_pathcondition.
    Qed.

    (* These should be kept abstract in the rest of the proof. If you need some
       property, add a lemma above. *)
    Local Opaque inst_chunk.
    Local Opaque inst_heap.
    Local Opaque inst_pathcondition.
    Local Opaque instantiate_env.
    Local Opaque instantiate_list.
    Local Opaque represents.
    Local Opaque symbolicstate_assume_formula.
    Local Opaque symbolicstate_produce_chunk.

    Definition scmut_wp {Γ1 Γ2 A}
      (m : SCMut Γ1 Γ2 A)
      (POST : A -> SCState Γ2 -> Prop)
      (s1 : SCState Γ1) : Prop :=
      outcome_satisfy (m s1) (fun r => POST (scmutres_value r) (scmutres_state r)).

    Lemma scmut_wp_bind {Γ1 Γ2 Γ3 A B} (ma : SCMut Γ1 Γ2 A) (f : A -> SCMut Γ2 Γ3 B)
          (POST : B -> SCState Γ3 -> Prop) :
      forall s1 : SCState Γ1,
        scmut_wp (scmut_bind ma f) POST s1 <->
        scmut_wp ma (fun a => scmut_wp (f a) POST) s1.
    Proof.
      unfold SCMut, scmut_bind, scmut_wp in *; cbn; intros.
      now rewrite outcome_satisfy_bind.
    Qed.

    Definition ResultProperty Γ A Σ :=
      DynamicMutatorResult Γ A Σ -> Prop.

    Definition dmutres_leq {Γ A Σ} `{Subst A} (r1 r2 : DynamicMutatorResult Γ A Σ) : Prop :=
      match r1 , r2 with
      | MkDynMutResult ζ1 a1 s1, MkDynMutResult ζ2 a2 s2 =>
        exists ζ21, (ζ1 = sub_comp ζ2 ζ21 /\ a1 = subst ζ21 a2 /\ s1 = subst ζ21 s2)
      end.

    Global Instance dmutres_leq_preorder {Γ A Σ} {subA : Subst A} {subLA : SubstLaws A} : PreOrder (@dmutres_leq Γ A Σ subA).
    Proof.
      constructor.
      - intros [Σ1 ζ1 a1 s1]. exists (sub_id _).
        now rewrite sub_comp_id_right, ?subst_sub_id.
      - intros [Σ1 ζ1 a1 s1] [Σ2 ζ2 a2 s2] [Σ3 ζ3 a3 s3].
        unfold dmutres_leq; cbn; intros; destruct_conjs; subst.
        exists (sub_comp H0 H). now rewrite ?sub_comp_assoc, ?subst_sub_comp.
    Qed.

    Definition resultprop_specialize {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
      ResultProperty Γ A Σ1 -> ResultProperty Γ A Σ2 :=
      fun p r => p (cosubst_dmutres ζ r).

    Definition resultprop_downwards_closed {Γ A Σ} `{Subst A} (p : ResultProperty Γ A Σ) : Prop :=
      forall (r1 r2 : DynamicMutatorResult Γ A Σ),
        dmutres_leq r1 r2 -> p r2 -> p r1.

    Definition StateProperty Γ A Σ :=
      forall Σ1, Sub Σ Σ1 -> A Σ1 -> SymbolicState Γ Σ1 -> Prop.

    Definition stateprop_specialize {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) (p: StateProperty Γ A Σ1) :
      StateProperty Γ A Σ2 := fun Σ3 ζ3 => p Σ3 (sub_comp ζ ζ3).

    Definition stateprop_impl {Γ A Σ} (P Q : StateProperty Γ A Σ) : Prop :=
      forall Σ1 (ζ : Sub Σ Σ1) (a : A Σ1) (s : SymbolicState Γ Σ1),
        P Σ1 ζ a s -> Q Σ1 ζ a s.

    Definition stateprop_downwards_closed {Γ Σ A} `{Subst A} (p : StateProperty Γ A Σ) : Prop :=
      forall Σ1 Σ2 (ζ1 : Sub Σ Σ1) (ζ2 : Sub Σ1 Σ2) (a1 : A Σ1) (s1 : SymbolicState Γ Σ1),
        p Σ1 ζ1 a1 s1 ->
        p Σ2 (sub_comp ζ1 ζ2) (subst ζ2 a1) (subst ζ2 s1).

    Definition dmut_wp {Γ1 Γ2 Σ0 A}
      (m : DynamicMutator Γ1 Γ2 A Σ0)
      (POST : StateProperty Γ2 A Σ0)
      (s1 : SymbolicState Γ1 Σ0) : Prop :=
      forall Σ1 (ζ1 : Sub Σ0 Σ1),
        outcome_satisfy
          (m Σ1 ζ1 (subst ζ1 s1))
          (fun '(@MkDynMutResult _ _ _ Σ2 ζ2 a2 s2) =>
             POST Σ2 (sub_comp ζ1 ζ2) a2 s2).

    Lemma dmut_wp_monotonic {Γ1 Γ2 Σ0 A} (m : DynamicMutator Γ1 Γ2 A Σ0)
          (P Q : StateProperty Γ2 A Σ0) (HYP : stateprop_impl P Q) :
      forall (s1 : SymbolicState Γ1 Σ0),
        dmut_wp m P s1 -> dmut_wp m Q s1.
    Proof.
      unfold dmut_wp; cbn; intros s1 H Σ1 ζ1.
      specialize (H Σ1 ζ1). revert H.
      apply outcome_satisfy_monotonic.
      intros [Σ2 ζ2 a2 s2]; cbn.
      intuition.
    Qed.

    Definition stateprop_lift {Γ AT A Σ} {instA : Inst AT A} (ι : SymInstance Σ) (POST : A -> SCState Γ -> Prop) :
      StateProperty Γ AT Σ :=
      fun Σ1 ζ1 v1 s__sym1 =>
        forall ι1 s__sc1,
          syminstance_rel ζ1 ι ι1 ->
          represents ι1 s__sym1 s__sc1 ->
          POST (inst ι1 v1) s__sc1.

    Lemma stateprop_lift_dcl {Γ AT A Σ} `{InstLaws AT A} (ι : SymInstance Σ) (POST : A -> SCState Γ -> Prop) :
      stateprop_downwards_closed (stateprop_lift ι POST).
    Proof.
      unfold stateprop_downwards_closed, stateprop_lift; intros.
      rewrite inst_subst.
      apply syminstance_rel_comp in H4.
      apply (H3 (inst ι1 ζ2) s__sc1).
      - assumption.
      - revert H5. now apply represents_rel.
    Qed.

    Definition approximates {Γ1 Γ2 AT A Σ} `{instA : Inst AT A} (ι : SymInstance Σ)
               (dm : DynamicMutator Γ1 Γ2 AT Σ) (sm : SCMut Γ1 Γ2 A) : Prop :=
      forall (s__sym : SymbolicState Γ1 Σ) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop),
        represents ι s__sym s__sc ->
        dmut_wp dm (stateprop_lift ι POST) s__sym ->
        scmut_wp sm POST s__sc.

    Lemma scmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic_binary sm1 sm2) POST s__sc <-> scmut_wp sm1 POST s__sc /\ scmut_wp sm2 POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic_binary; cbn; intuition. Qed.

    Lemma dmut_wp_demonic_binary {Γ1 Γ2 Σ A} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ)
      (POST : forall Σ', Sub Σ Σ' -> A Σ' -> SymbolicState Γ2 Σ' -> Prop) (s : SymbolicState Γ1 Σ) :
        dmut_wp (dmut_demonic_binary m1 m2) POST s <->
        dmut_wp m1 POST s /\ dmut_wp m2 POST s.
    Proof. unfold dmut_wp, dmut_demonic_binary; cbn; intuition. Qed.

    Lemma approximates_demonic_binary {Γ1 Γ2 Σ} (ι : SymInstance Σ)
          (dm1 dm2 : DynamicMutator Γ1 Γ2 Unit Σ) (sm1 sm2 : SCMut Γ1 Γ2 unit) :
      approximates ι dm1 sm1 ->
      approximates ι dm2 sm2 ->
      approximates ι (dmut_demonic_binary dm1 dm2) (scmut_demonic_binary sm1 sm2).
    Proof.
      intros H1 H2 ? ? ? H__s H.
      apply scmut_wp_demonic_binary.
      apply dmut_wp_demonic_binary in H.
      split.
      now apply (H1 _ _ _ H__s).
      now apply (H2 _ _ _ H__s).
    Qed.

    Lemma scmut_wp_demonic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic sm) POST s__sc <-> forall v, scmut_wp (sm v) POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic; cbn; intuition. Qed.

    Lemma dmut_wp_demonic {Γ1 Γ2 Σ A B} (m : B -> DynamicMutator Γ1 Γ2 A Σ)
      (POST : StateProperty Γ2 A Σ) (s : SymbolicState Γ1 Σ) :
        dmut_wp (dmut_demonic m) POST s <->
        forall b, dmut_wp (m b) POST s.
    Proof. unfold dmut_wp, dmut_demonic; cbn; intuition. Qed.

    Lemma dmut_wp_produce_chunk {Γ Σ} (c : Chunk Σ) (s__sym : SymbolicState Γ Σ)
          (POST : StateProperty Γ Unit Σ) (POST_dcl : stateprop_downwards_closed POST) :
      dmut_wp (dmut_produce_chunk c) POST s__sym <->
      POST Σ (sub_id Σ) tt (symbolicstate_produce_chunk c s__sym).
    Proof.
      split.
      - intros dwp. specialize (dwp Σ (sub_id Σ)). cbn in dwp.
        now rewrite ?sub_comp_id_left, ?subst_sub_id in dwp.
      - intros ? ? ?. cbn.
        replace (symbolicstate_produce_chunk (subst ζ1 c) (subst ζ1 s__sym))
          with (subst ζ1 (symbolicstate_produce_chunk c s__sym)) by now destruct s__sym.
        replace (sub_comp ζ1 (sub_id Σ1)) with (sub_comp (sub_id Σ) ζ1)
          by now rewrite sub_comp_id_right, sub_comp_id_left.
        now apply POST_dcl.
    Qed.

    Lemma dmut_produce_chunk_sound {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
      approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce_chunk c)
        (scmut_produce_chunk (inst ι c)).
    Proof.
      intros ? ? ? Hrep dwp. cbn.
      apply dmut_wp_produce_chunk in dwp; auto using stateprop_lift_dcl.
      apply (dwp ι); auto using syminstance_rel_refl.
      now apply represents_produce_chunk.
    Qed.

    Lemma dmut_assume_formula_sound {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assume_formula fml)
        (scmut_assume_formula ι fml).
    Proof.
      intros ? ? ? H__state H.
      unfold dmut_wp, dmut_assume_formula in H.
      specialize (H Σ (sub_id Σ)).
      rewrite subst_sub_id in H.
      destruct (try_solve_formula_spec (ι := ι) fml) as [? H1|_].
      - intros ->%H1. clear H1. cbn in *.
        rewrite subst_sub_id, sub_comp_id_left in H.
        refine (H _ _ _ H__state).
        apply syminstance_rel_refl.
      - destruct fml; cbn in *; intros;
          rewrite ?subst_sub_id, ?sub_comp_id_left in H.
        + apply (H _ _ (syminstance_rel_refl ι)).
          now apply represents_assume_formula.
        + apply (H _ _ (syminstance_rel_refl ι)).
          now apply represents_assume_formula.
        + admit.
        + apply (H _ _ (syminstance_rel_refl ι)).
          now apply represents_assume_formula.
    Admitted.

    Opaque dmut_assume_term.
    Opaque dmut_assume_prop.
    Opaque dmut_assume_formula.

    Definition dmut_wf {Γ1 Γ2 A Σ0} `{Subst A} (d : DynamicMutator Γ1 Γ2 A Σ0) : Prop :=
      forall Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (s1 : SymbolicState Γ1 Σ1)
             (POST : ResultProperty Γ2 A Σ1) (POST_dcl : resultprop_downwards_closed POST),
        outcome_satisfy (d Σ1 ζ1 s1) POST ->
        outcome_satisfy (d Σ2 (sub_comp ζ1 ζ2) (subst ζ2 s1)) (resultprop_specialize ζ2 POST).

    Lemma dmut_wf_pure {Γ A Σ} {subA: Subst A} {sublA: SubstLaws A} (a : A Σ) :
      dmut_wf (dmut_pure (Γ := Γ) a).
    Proof.
      unfold dmut_wf, resultprop_specialize; cbn; intros.
      revert H.
      apply POST_dcl.
      unfold dmutres_leq.
      exists ζ2; cbn.
      rewrite sub_comp_id_right, sub_comp_id_left, subst_sub_comp.
      intuition.
    Qed.

    Definition dmut_wf' {Γ1 Γ2 A Σ0} `{Subst A} (d : DynamicMutator Γ1 Γ2 A Σ0) : Prop :=
      forall (POST : StateProperty Γ2 A Σ0) (POST_dcl : stateprop_downwards_closed POST)
             (s : SymbolicState Γ1 Σ0) Σ1 (ζ : Sub Σ0 Σ1),
        dmut_wp d POST s ->
        dmut_wp (dmut_sub ζ d) (stateprop_specialize ζ POST) (subst ζ s).

    Lemma dmut_wf'_pure {Γ A Σ} `{Subst A} (a : A Σ) :
      dmut_wf' (dmut_pure (Γ := Γ) a).
    Proof.
      unfold dmut_wf', dmut_wp, dmut_sub, dmut_pure, stateprop_specialize; cbn; intros.
      now rewrite <- sub_comp_assoc, <- subst_sub_comp.
    Qed.

    Definition dmut_wf'' {Γ1 Γ2 A Σ0} `{Subst A} (d : DynamicMutator Γ1 Γ2 A Σ0) : Prop :=
      forall (POST : StateProperty Γ2 A Σ0) (POST_dcl : stateprop_downwards_closed POST),
        stateprop_downwards_closed
          (fun Σ1 ζ1 _ => dmut_wp (dmut_sub ζ1 d) (stateprop_specialize ζ1 POST)).

    Lemma dmut_wf''_pure {Γ A Σ} `{SubstLaws A} (a : A Σ) :
      dmut_wf'' (dmut_pure (Γ := Γ) a).
    Proof.
      unfold dmut_wf'', dmut_wp, dmut_sub, dmut_pure, stateprop_downwards_closed, stateprop_specialize; cbn; intros.
      generalize (H1 _ (sub_comp ζ2 ζ0)).
      now rewrite !sub_comp_id_right, !subst_sub_comp, !sub_comp_assoc.
    Qed.

    Lemma dmut_wf_equiv {Γ1 Γ2 A Σ0} `{Subst A} (d : DynamicMutator Γ1 Γ2 A Σ0) :
      dmut_wf d <-> dmut_wf' d.
    Proof.
      unfold dmut_wf', dmut_wf, dmut_wp, dmut_sub; split; intros.
      - specialize (H1 Σ2 (sub_comp ζ ζ1)). rewrite subst_sub_comp in H1.
        refine (outcome_satisfy_monotonic _ _ H1).
        clear. intros [Σ3 ζ3 r3].
        unfold stateprop_specialize.
        now rewrite sub_comp_assoc.
      - admit.
    Admitted.

    Opaque subst.
    Opaque sub_up1.
    Opaque sub_snoc.
    Opaque wk1.
    Opaque SubstEnv.

    Lemma dmut_wp_bind {Γ1 Γ2 Γ3 A B Σ0} {subB : Subst B} (ma : DynamicMutator Γ1 Γ2 A Σ0)
          (f : forall Σ', Sub Σ0 Σ' -> A Σ' -> DynamicMutator Γ2 Γ3 B Σ')
          (f_wf : forall Σ' ζ a, dmut_wf (f Σ' ζ a))
          (POST : StateProperty Γ3 B Σ0) (POST_dcl : stateprop_downwards_closed POST) :
      forall s0 : SymbolicState Γ1 Σ0,
        dmut_wp (dmut_bind ma f) POST s0 <->
        dmut_wp ma (fun Σ1 ζ1 a1 => dmut_wp (f Σ1 ζ1 a1) (stateprop_specialize ζ1 POST)) s0.
    Proof.
      unfold DynamicMutator, dmut_bind, dmut_wp, dmut_wf in *; cbn; intros s0.
      split; intros H Σ1 ζ1; specialize (H Σ1 ζ1). revert H.
      - rewrite outcome_satisfy_bind. apply outcome_satisfy_monotonic.
        intros [Σ2 ζ2 a2 s2] H Σ3 ζ3.
        rewrite outcome_satisfy_bind in H.
        apply (f_wf Σ2 (sub_comp ζ1 ζ2) a2 Σ2 Σ3 (sub_id Σ2) ζ3) in H.
        + revert H. rewrite sub_comp_id_left.
          apply outcome_satisfy_monotonic.
          intros [Σ4 ζ4 b4 s4]. cbn.
          now rewrite <- sub_comp_assoc.
        + clear f_wf H.
          unfold resultprop_downwards_closed.
          intros [] [] []; destruct_conjs; subst. cbn.
          rewrite <- ?sub_comp_assoc.
          apply POST_dcl.
      - rewrite outcome_satisfy_bind. revert H.
        apply outcome_satisfy_monotonic.
        intros [Σ2 ζ2 a2 s2] H. specialize (H Σ2 (sub_id _)).
        revert H. rewrite outcome_satisfy_bind, subst_sub_id.
        apply outcome_satisfy_monotonic.
        intros [Σ3 ζ3 b3 s3]. cbn.
        unfold stateprop_specialize.
        now rewrite sub_comp_id_left, sub_comp_assoc.
    Qed.

    Lemma dmut_wp_fresh {Γ Σ0 A x τ} `{Subst A}
          (d : DynamicMutator Γ Γ A (Σ0 ▻ (x,τ))%ctx)
          (POST : StateProperty Γ A Σ0)
          (POST_dcl : stateprop_downwards_closed POST)
          (s : SymbolicState Γ Σ0) (wfd : dmut_wf d) :
      dmut_wp (dmut_fresh (x,τ) d) POST s <->
      dmut_wp d (stateprop_specialize sub_wk1 POST) (subst sub_wk1 s).
    Proof.
      unfold dmut_wp, dmut_fresh; cbn; split; intros HYP ? ?.
      - dependent elimination ζ1 as [@env_snoc Σ0 ζ1 _ v]; cbn in v.
        rewrite <- subst_sub_comp, sub_comp_wk1_tail; cbn.
        specialize (HYP Σ1 ζ1).
        rewrite outcome_satisfy_map in HYP; cbn in *.
        apply (@wfd _ Σ1 _ (env_snoc (sub_id _) (_,τ) v)) in HYP; clear wfd.
        + change (wk1 (subst ζ1 s)) with (subst (sub_wk1 (b:=(x,τ))) (subst ζ1 s)) in HYP.
          rewrite <- subst_sub_comp, <- sub_snoc_comp, sub_comp_id_right, sub_comp_wk1_tail in HYP.
          cbn in HYP. rewrite subst_sub_id in HYP.
          refine (outcome_satisfy_monotonic _ _ HYP).
          intros [Σ2 ζ2 r2]. cbn. clear.
          intuition.
          rewrite <- (sub_comp_assoc sub_wk1), sub_comp_wk1_tail in H; cbn in H.
          rewrite sub_comp_id_left in H.
          unfold stateprop_specialize.
          now rewrite <- sub_comp_assoc, sub_comp_wk1_tail.
        + revert POST_dcl; clear.
          unfold stateprop_downwards_closed, resultprop_downwards_closed.
          intros ? [Σ2 ζ2 a2 s2] [Σ3 ζ3 a3 s3]; cbn.
          intros [ζ12]; intuition. subst.
          apply (POST_dcl _ _ _ ζ12) in H1.
          now rewrite !sub_comp_assoc in H1.
      - rewrite outcome_satisfy_map.
        specialize (HYP (Σ1 ▻ (x,τ)) (sub_up1 ζ1)).
        rewrite <- subst_sub_comp, sub_comp_wk1_comm in HYP.
        change (wk1 (b := (x,τ)) (subst ζ1 s)) with (subst (sub_wk1 (b := (x,τ))) (subst ζ1 s)).
        rewrite <- subst_sub_comp.
        refine (outcome_satisfy_monotonic _ _ HYP).
        intros [Σ2 ζ2 r2]. clear.
        dependent elimination ζ2 as [@env_snoc Σ1 ζ2 _ t].
        unfold stateprop_specialize.
        now rewrite <- ?sub_comp_assoc, <- sub_comp_wk1_comm.
    Qed.

    Lemma dmut_fresh_sound {Γ Σ ς τ} (ι : SymInstance Σ)
          (dm : DynamicMutator Γ Γ Unit (Σ ▻ (ς,τ))) (wfdm : dmut_wf dm)
          (sm : Lit τ -> SCMut Γ Γ unit) :
      (forall v, approximates (env_snoc ι _ v) dm (sm v)) ->
      approximates ι
        (dmut_fresh (ς,τ) dm)
        (scmut_demonic sm).
    Proof.
      intros HYP.
      unfold approximates; cbn.
      intros ? ? ? H__state H.
      apply scmut_wp_demonic. intros v.
      apply (HYP v (subst sub_wk1 s__sym) s__sc POST).
      - revert H__state. clear.
        apply represents_rel.
        apply syminstance_rel_wk1.
      - apply (@dmut_wp_fresh Γ Σ Unit ς τ SubstUnit) in H.
        + revert H; clear.
          apply dmut_wp_monotonic; cbn; intros ? ? []; intros.
          dependent elimination ζ as [@env_snoc Σ0 ζ _ t].
          unfold stateprop_specialize in H.
          rewrite sub_comp_wk1_tail in H; cbn in *.
          intros ι1 s1 H0 H1.
          apply H.
          * now apply syminstance_rel_snoc in H0.
          * assumption.
        + apply stateprop_lift_dcl.
        + assumption.
    Qed.

    Lemma dmut_produce_sound {Γ Σ} (asn : Assertion Σ) (ι : SymInstance Σ) :
      approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce asn)
        (scmut_produce ι asn).
    Proof.
      induction asn; cbn.
      - apply dmut_assume_formula_sound.
      - apply dmut_produce_chunk_sound.
      - apply approximates_demonic_binary.
        + admit.
        + admit.
      - admit.
      - admit.
      - apply dmut_fresh_sound.
        + admit.
        + intros. apply IHasn.
    Admitted.

    Opaque dmut_wp.
    Opaque scmut_wp.

    Section WithSemantics.

      Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

      Definition interpret_heap {Σ} (ι : SymInstance Σ) (h : SymbolicHeap Σ) : L :=
        List.fold_right (fun c h => ASS.inst_chunk ι c ∧ h) ltrue h.

      Ltac sauto :=
        repeat
          match goal with
          | [ |- ?P ⊢ ?P ] =>
            apply entails_refl
          | [ |- ?P ∧ _ ⊢ ?P ∧ _ ] =>
            apply land_right; [ apply land_left1, entails_refl | idtac ]
          | [ |- _ ⊢ _ ∧ !!(?x = ?x) ] =>
            apply land_right; [ idtac | apply lprop_right; reflexivity ]
          | [ |- !! _ ⊢ _ ] =>
            apply lprop_right; intro
          | [ H: ?P |- _ ⊢ !!?P ] =>
            apply lprop_right; exact H
          end.

      Local Ltac sound_inster :=
        match goal with
        | [ IH: outcome_satisfy (dmut_exec ?s _ _) |-
            outcome_satisfy (dmut_exec ?s _ _) _ ] =>
          refine (outcome_satisfy_monotonic _ _ IH); clear IH
        | [ IH: context[_ -> outcome_satisfy (dmut_exec ?s _ _) _] |-
            outcome_satisfy (dmut_exec ?s _ _) _ ] =>
          microsail_insterU (fail) IH; refine (outcome_satisfy_monotonic _ _ IH); clear IH
        end.

      Transparent subst SubstEnv.
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

      Transparent inst instantiate_env.

      Lemma eval_exp_inst {Γ Σ τ} (ι : SymInstance Σ) (δΓΣ : SymbolicLocalStore Γ Σ) (e : Exp Γ τ) :
        eval e (inst ι δΓΣ) = inst ι (symbolic_eval_exp δΓΣ e).
      Proof.
        induction e; cbn; repeat f_equal; auto.
        { now rewrite env_lookup_map. }
        2: {
          induction es as [|eb n es IHes]; cbn in *.
          { reflexivity. }
          { destruct X as [-> Heqs].
            destruct (inst_term ι (symbolic_eval_exp δΓΣ eb));
              cbn; f_equal; auto.
          }
        }
        all: induction es; cbn in *; destruct_conjs; f_equal; auto.
      Qed.

      Local Opaque inst_heap.

      Opaque env_tail.

      Notation "'dmutres_pathcondition' res" := (symbolicstate_pathcondition (dmutres_result_state res)) (at level 10).
      Notation "'dmutres_heap' res" := (symbolicstate_heap (dmutres_result_state res)) (at level 10).
      Notation "'dmutres_localstore' res" := (symbolicstate_localstore (dmutres_result_state res)) (at level 10).

      Lemma dmut_exec_sound {Γ σ} (POST : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) :
        forall Σ0 Σ1  (ι : SymInstance Σ1) (ζ1 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SymbolicLocalStore Γ Σ1) (h1 : SymbolicHeap Σ1),
          let δ       := inst ι δ1 in
          let pre__pc   := inst_pathcondition ι pc1 in
          let pre__heap := interpret_heap ι h1 in
          outcome_satisfy
            (dmut_exec s ζ1 (MkSymbolicState pc1 δ1 h1))
            (fun '(@MkDynMutResult _ _ _ Σ2 ζ2 t (MkSymbolicState pc2 δ2 h2)) =>
               forall (ι' : SymInstance Σ2),
                 ι = env_map (fun _ => inst_term ι') ζ2 ->
                 let post__pc   := inst_pathcondition ι' pc2 in
                 let post__heap := interpret_heap ι' h2 in
                 !! post__pc ∧ post__heap ⊢ POST (inst ι' t) (inst ι' δ2)) ->
          pre__pc ->
          outcome_satisfy
            (scmut_exec s (MkSCState δ (inst ι h1)))
            (fun '(MkSCMutResult v2 (MkSCState δ2 h2)) =>
               SCMUT.inst_scheap h2 ⊢ POST v2 δ2).
      Proof.
        intros ? ? ? ? ? ? ?; cbn.
        revert pc1 h1.
        induction s.

        - cbn. intros.
          assert (ι = env_map (fun b : 𝑺 * Ty => inst_term ι) (sub_id Σ1)) as Heqι by admit.
          specialize (H ι Heqι); clear Heqι.
          refine (entails_trans _ _ _ _ H).
          apply land_right.
          + now apply lprop_right.
          + admit.

        - cbn. intros.
          assert (ι = env_map (fun b : 𝑺 * Ty => inst_term ι) (sub_id Σ1)) as Heqι by admit.
          specialize (H ι Heqι); clear Heqι.
          change (env_map (fun (b : 𝑿 * Ty) (t : Term Σ1 (snd b)) => inst_term ι t) δ1) with
              (inst ι δ1).
          rewrite eval_exp_inst.
          refine (entails_trans _ _ _ _ H).
          apply land_right.
          + now apply lprop_right.
          + admit.

        - repeat (unfold dmut_bind_right, dmut_sub, dmut_bind, scmut_bind,
                  scmut_bind_left; cbn).
          repeat
            (repeat setoid_rewrite outcome_satisfy_bind;
             repeat setoid_rewrite outcome_satisfy_map; cbn).
          intros.

      Admitted.

      Lemma dmut_contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
        ValidContractDynMut c body ->
        ValidContract c body.
      Proof.
      Admitted.

    End  WithSemantics.

  End DynMutV1Soundness.

End Soundness.
