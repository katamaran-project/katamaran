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

    Definition inconsistent {Σ} (pc : PathCondition Σ) : Prop :=
      forall ι, ~ inst ι pc.

    Global Instance inst_heap : Inst SymbolicHeap SCHeap :=
      instantiate_list.
    Global Instance instlaws_heap : InstLaws SymbolicHeap SCHeap.
    Proof. apply instantiatelaws_list. Qed.

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

    (* Relate two symbolic instances at different points during execution. This
       essentially encodes a preorder on the total space { Σ & SymInstance Σ },
       which encodes that ι2 is a future of ι1, i.e. it is derived by compatible
       for existing variables and values for new universal variables. *)
    Definition syminstance_rel {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2) : Prop :=
      inst ι2 ζ = ι1.
    Hint Unfold syminstance_rel : core.

    Lemma syminstance_rel_refl {Σ} (ι : SymInstance Σ) :
      syminstance_rel (sub_id Σ) ι ι.
    Proof. apply inst_sub_id. Qed.

    Lemma syminstance_rel_refl_inv {Σ} (ι1 ι2 : SymInstance Σ) :
      syminstance_rel (sub_id Σ) ι1 ι2 -> ι2 = ι1.
    Proof. unfold syminstance_rel. now rewrite inst_sub_id. Qed.

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

    Lemma syminstance_rel_trans {Σ0 Σ1 Σ2} {ζ1 : Sub Σ0 Σ1} {ζ2 : Sub Σ1 Σ2}
          {ι0 : SymInstance Σ0} {ι1 : SymInstance Σ1} {ι2 : SymInstance Σ2} :
      syminstance_rel ζ1 ι0 ι1 -> syminstance_rel ζ2 ι1 ι2 ->
      syminstance_rel (sub_comp ζ1 ζ2) ι0 ι2.
    Proof. intros. apply syminstance_rel_comp. congruence. Qed.

    Lemma syminstance_rel_wk1 {Σ : NCtx 𝑺 Ty} {x τ} (ι : SymInstance Σ) (v : Lit τ) :
      syminstance_rel sub_wk1 ι (ι ► ((x, τ) ↦ v)).
    Proof. apply inst_sub_wk1. Qed.

    Lemma syminstance_rel_up {Σ1 Σ2 x τ} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) ι2 :
      forall v,
        syminstance_rel (sub_up1 ζ) (env_snoc ι1 (x,τ) v) (env_snoc ι2 (x,τ) v) <->
        syminstance_rel ζ ι1 ι2.
    Proof.
      unfold syminstance_rel. intros v.
      change (inst (ι2 ► (x :: τ ↦ v)) (sub_comp ζ sub_wk1) ► (x :: τ ↦ v) =
              ι1 ► (x :: τ ↦ v) <-> inst ι2 ζ = ι1).
      unfold sub_comp. rewrite inst_subst, inst_sub_wk1.
      split; intros H.
      - now dependent elimination H.
      - now f_equal.
    Qed.

    (* UNUSED *)
    Definition syngeq {AT} `{Subst AT, Rewrite AT} {Σ0 Σ1} (ζ1 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (a0 : AT Σ0) (a1 : AT Σ1) : Prop :=
      rewrite pc1 a1 (subst ζ1 a0).

    (* A generic preorder on symbolic data. The terms a0 and a1 should be
       considered to be outputs of the executor along the same path, just with
       different constraints. More specifically: if we run a symbolic
       computation up to some point with result a0, then a1 denotes the result if
       we ran it with the new constraints given by pc1. *)
    Definition geq {AT A} `{Inst AT A} {Σ0 Σ1} (ζ1 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (a0 : AT Σ0) (a1 : AT Σ1) : Prop :=
      forall (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1),
        syminstance_rel ζ1 ι0 ι1 ->
        (inst ι1 pc1 : Prop) ->
        inst ι0 a0 = inst ι1 a1.

    (* A preorder on path conditions. This encodes that either pc1 belongs to a
       longer symbolic execution path or that it's the same path, but with
       potentially additional constraints. *)
    Definition geqpc {Σ0 Σ1} (ζ1 : Sub Σ0 Σ1) (pc0 : PathCondition Σ0) (pc1 : PathCondition Σ1) : Prop :=
      forall (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1),
        syminstance_rel ζ1 ι0 ι1 ->
        (inst ι1 pc1 : Prop) ->
        (inst ι0 pc0 : Prop).

    Lemma geq_refl {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ) (a : AT Σ) :
      geq (sub_id _) pc a a.
    Proof. intros ? ? <-. now rewrite inst_sub_id. Qed.

    Lemma geq_trans {AT A} `{Inst AT A} {Σ1 Σ2 Σ3}
          {ζ12 : Sub Σ1 Σ2} (pc2 : PathCondition Σ2)
          {ζ23 : Sub Σ2 Σ3} {pc3 : PathCondition Σ3}
          {a1 : AT Σ1} (a2 : AT Σ2) {a3 : AT Σ3} :
      geqpc ζ23 pc2 pc3 ->
      geq ζ12 pc2 a1 a2 ->
      geq ζ23 pc3 a2 a3 ->
      geq (sub_comp ζ12 ζ23) pc3 a1 a3.
    Proof.
      intros Hpc23 Ha12 Ha23 ι1 ι3 rel13 Hpc3.
      pose (inst ι3 ζ23) as ι2.
      pose proof (Hpc23 ι2 ι3 eq_refl Hpc3) as Hpc2.
      specialize (Ha23 ι2 ι3 eq_refl Hpc3).
      apply syminstance_rel_comp in rel13.
      specialize (Ha12 ι1 ι2 rel13 Hpc2).
      now transitivity (inst ι2 a2).
    Qed.

    Lemma geq_syntactic {AT A} `{InstLaws AT A} {Σ0 Σ1} (ζ1 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (a0 : AT Σ0) (a1 : AT Σ1) :
      a1 = subst ζ1 a0 ->
      geq ζ1 pc1 a0 a1.
    Proof.
      unfold geq, syminstance_rel.
      intros -> * <-. now rewrite inst_subst.
    Qed.

    Lemma geq_subst {AT A} `{InstLaws AT A} {Σ2 Σ3 Σ4} (a : AT Σ2) (ζ23 : Sub Σ2 Σ3) (ζ24 : Sub Σ2 Σ4) (ζ34 : Sub Σ3 Σ4)
          (pc4 : PathCondition Σ4) :
      geq ζ34 pc4 ζ23 ζ24 -> geq ζ34 pc4 (subst ζ23 a) (subst ζ24 a).
    Proof.
      intros Hζ34 ι3 ι4 rel34 Hpc4. specialize (Hζ34 ι3 ι4 rel34 Hpc4).
      rewrite ?inst_subst. now f_equal.
    Qed.

    Lemma geq_pre_comp {Σ1 Σ2 Σ3 Σ4} (ζ12 : Sub Σ1 Σ2) (ζ23 : Sub Σ2 Σ3) (ζ24 : Sub Σ2 Σ4) (ζ34 : Sub Σ3 Σ4)
          (pc4 : PathCondition Σ4) :
      geq ζ34 pc4 ζ23 ζ24 -> geq ζ34 pc4 (sub_comp ζ12 ζ23) (sub_comp ζ12 ζ24).
    Proof. apply geq_subst. Qed.

    Lemma geq_sub_comp {Σ1 Σ2 Σ3} (pc3 : PathCondition Σ3) (ζ12 : Sub Σ1 Σ2) (ζ23 : Sub Σ2 Σ3) :
      geq ζ23 pc3 ζ12 (sub_comp ζ12 ζ23).
    Proof. apply geq_syntactic. reflexivity. Qed.

    Lemma geqpc_refl {Σ} (pc : PathCondition Σ) :
      geqpc (sub_id Σ) pc pc.
    Proof. intros ? ι <-. now rewrite inst_sub_id. Qed.

    Lemma geqpc_trans {Σ0 Σ1 Σ2} (ζ01 : Sub Σ0 Σ1) (ζ02 : Sub Σ0 Σ2) (ζ12 : Sub Σ1 Σ2)
          (pc0 : PathCondition Σ0) (pc1 : PathCondition Σ1) (pc2 : PathCondition Σ2) :
      geq ζ12 pc2 ζ01 ζ02 -> geqpc ζ01 pc0 pc1 -> geqpc ζ12 pc1 pc2 -> geqpc ζ02 pc0 pc2.
    Proof.
      intros Hζ H01 H12 ι0 ι2 rel02 Hpc2. pose (inst ι2 ζ12) as ι1.
      specialize (Hζ ι1 ι2 eq_refl Hpc2).
      assert (syminstance_rel ζ01 ι0 ι1) as rel01 by congruence.
      eauto.
    Qed.

    (* A proper preorder on the result of a symbolic execution, using the
    generic geq on every component. *)
    Definition dmutres_geq {Γ AT A Σ} {instA : Inst AT A} (r1 r2 : DynamicMutatorResult Γ AT Σ) : Prop :=
      match r1 , r2 with
      | MkDynMutResult ζ1 pc1 a1 s1, MkDynMutResult ζ2 pc2 a2 s2 =>
        exists ζ12,
        geqpc ζ12 pc1 pc2 /\
        geq ζ12 pc2 ζ1 ζ2 /\
        geq ζ12 pc2 a1 a2 /\
        geq ζ12 pc2 s1 s2
      end.

    Definition dmutres_geq_low_level {Γ A V Σ} {instA : Inst A V} (r1 r2 : DynamicMutatorResult Γ A Σ) : Prop :=
      match r1 , r2 with
      | MkDynMutResult ζ1 pc1 a1 s1, MkDynMutResult ζ2 pc2 a2 s2 =>
        exists ζ12,
        forall ι1 ι2,
          syminstance_rel ζ12 ι1 ι2 ->
          (inst ι2 pc2 : Prop) ->
          inst ι1 pc1 /\
          inst ι1 ζ1 = inst ι2 ζ2 /\
          inst ι1 a1 = inst ι2 a2 /\
          inst ι1 s1 = inst ι2 s2
      end.

    Lemma dmutres_geq_low_equiv {Γ A V Σ} {instA : Inst A V} :
      forall (r1 r2 : DynamicMutatorResult Γ A Σ),
        dmutres_geq r1 r2 <-> dmutres_geq_low_level r1 r2.
    Proof.
      intros [Σ1 ζ1 pc1 a1 s1] [Σ2 ζ2 pc2 a2 s2]; cbn. unfold geqpc, geq.
      split; intros [ζ12 Hgeq]; exists ζ12; intuition.
    Qed.

    (* A frequent special case. *)
    Lemma dmutres_geq_syntactic {Γ A V Σ} `{InstLaws A V} :
      forall r1 r2 : DynamicMutatorResult Γ A Σ,
        (match r1 , r2 with
         | MkDynMutResult ζ1 pc1 a1 s1, MkDynMutResult ζ2 pc2 a2 s2 =>
           exists ζ12,
           ζ2  = sub_comp ζ1 ζ12 /\
           pc2 = subst ζ12 pc1 /\
           a2  = subst ζ12 a1 /\
           s2  = subst ζ12 s1
         end
        ) ->
        dmutres_geq r1 r2.
    Proof.
      intros [Σ1 ζ1 pc1 a1 s1] [Σ2 ζ2 pc2 a2 s2] [ζ12 Hgeq]; cbn - [dmutres_geq];
        destruct_conjs; subst.
      apply dmutres_geq_low_equiv.
      exists ζ12. intros ? ? <-.
      unfold sub_comp; now rewrite ?inst_subst.
    Qed.

    Global Instance dmutres_geq_preorder {Γ AT A Σ} `{Inst AT A} : PreOrder (@dmutres_geq Γ AT A Σ _).
    Proof.
      constructor.
      - intros [Σ1 ζ1 pc a1 s]. exists (sub_id _).
        repeat split; try apply geq_refl. apply geqpc_refl.
      - intros [Σ1 ζ1 pc1 a1 s1] [Σ2 ζ2 pc2 a2 s2] [Σ3 ζ3 pc3 a3 s3] [ζ12] [ζ23]; cbn.
        destruct_conjs. exists (sub_comp ζ12 ζ23).
        repeat split.
        + apply geqpc_trans with ζ12 ζ23 pc2; auto using geq_sub_comp.
        + apply geq_trans with pc2 ζ2; auto.
        + apply geq_trans with pc2 a2; auto.
        + apply geq_trans with pc2 s2; auto.
    Qed.

    Global Instance dmutres_geq_rewrite {Γ AT A Σ} `{Inst AT A} : RewriteRelation (@dmutres_geq Γ AT A Σ _).
    Qed.

    Lemma dmutres_geq_pre_comp {AT A} `{Inst AT A} {Γ Σ1 Σ2 Σ3}
          (ζ2 : Sub Σ1 Σ2) (a2 : AT Σ2) pc2 (s2 : SymbolicState Γ Σ2)
          (ζ3 : Sub Σ1 Σ3) (a3 : AT Σ3) pc3 (s3 : SymbolicState Γ Σ3) :
      forall Σ0 (ζ1 : Sub Σ0 Σ1),
        dmutres_geq (MkDynMutResult ζ2 pc2 a2 s2) (MkDynMutResult ζ3 pc3 a3 s3) ->
        dmutres_geq (MkDynMutResult (sub_comp ζ1 ζ2) pc2 a2 s2) (MkDynMutResult (sub_comp ζ1 ζ3) pc3 a3 s3).
    Proof.
      intros ? ?. intros [ζ23]. exists ζ23. destruct_conjs.
      repeat split; auto using geq_pre_comp.
    Qed.

    Definition dmutres_equiv {Γ AT A Σ} {instA : Inst AT A} (r1 r2 : DynamicMutatorResult Γ AT Σ) : Prop :=
      dmutres_geq r1 r2 /\ dmutres_geq r2 r1.

    Section StateProp.

      Definition StateProperty Γ A Σ :=
        forall Σ1, Sub Σ Σ1 -> PathCondition Σ1 -> A Σ1 -> SymbolicState Γ Σ1 -> Prop.

      Definition stateprop_downwards_closed {Γ Σ AT A} `{Inst AT A} (p : StateProperty Γ AT Σ) : Prop :=
        forall Σ1 (ζ1 : Sub Σ Σ1) pc1 a1 s1 Σ2 (ζ2 : Sub Σ Σ2) pc2 a2 s2,
          dmutres_geq (MkDynMutResult ζ1 pc1 a1 s1) (MkDynMutResult ζ2 pc2 a2 s2) ->
          p Σ1 ζ1 pc1 a1 s1 -> p Σ2 ζ2 pc2 a2 s2.

      (* The property always holds vacuously on inconsistent paths. *)
      Definition stateprop_vacuous {Γ AT Σ} (p : StateProperty Γ AT Σ) : Prop :=
        forall Σ1 (ζ1 : Sub Σ Σ1) pc a1 s1, inconsistent pc -> p Σ1 ζ1 pc a1 s1.

      Definition stateprop_impl {Γ A Σ} (P Q : StateProperty Γ A Σ) : Prop :=
        forall Σ1 (ζ : Sub Σ Σ1) (pc : PathCondition Σ1) (a : A Σ1) (s : SymbolicState Γ Σ1),
          P Σ1 ζ pc a s -> Q Σ1 ζ pc a s.

      Definition stateprop_specialize {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) (p: StateProperty Γ A Σ1) :
        StateProperty Γ A Σ2 := fun Σ3 ζ3 => p Σ3 (sub_comp ζ ζ3).

      Definition stateprop_lift {Γ AT A Σ} {instA : Inst AT A} (ι : SymInstance Σ) (POST : A -> SCState Γ -> Prop) :
        StateProperty Γ AT Σ :=
        fun Σ1 ζ1 pc1 v1 s1 =>
          forall ι1,
            syminstance_rel ζ1 ι ι1 ->
            (inst ι1 pc1 : Prop) ->
            POST (inst ι1 v1) (inst ι1 s1).

      Lemma stateprop_lift_dcl {Γ AT A Σ1} `{Inst AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        stateprop_downwards_closed (stateprop_lift ι1 POST).
      Proof.
        unfold stateprop_downwards_closed, stateprop_lift.
        intros Σ2 ζ2 pc2 a2 s2 Σ3 ζ3 pc3 a3 s3.
        intros [ζ23 Hgeq]%dmutres_geq_low_equiv Hpost.
        intros ι3 rel13 Hpc3. pose (inst ι3 ζ23) as ι2.
        specialize (Hgeq ι2 ι3 eq_refl Hpc3).
        specialize (Hpost ι2). unfold syminstance_rel in *. subst.
        intuition.
      Qed.

      Lemma stateprop_lift_vac {Γ AT A Σ1} `{Inst AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        stateprop_vacuous (stateprop_lift ι1 POST).
      Proof. unfold stateprop_vacuous, stateprop_lift. intuition. Qed.

    End StateProp.

    Section ResultProp.

      Definition ResultProperty Γ A Σ :=
        DynamicMutatorResult Γ A Σ -> Prop.

      Definition resultprop_specialize {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
        ResultProperty Γ A Σ1 -> ResultProperty Γ A Σ2 :=
        fun p r => p (cosubst_dmutres ζ r).

      Definition resultprop_downwards_closed {Γ AT Σ A} `{Inst AT A} (p : ResultProperty Γ AT Σ) : Prop :=
        forall (r1 r2 : DynamicMutatorResult Γ AT Σ),
          dmutres_geq r1 r2 -> p r1 -> p r2.

      Definition resultprop_vacuous {Γ AT Σ A} `{Inst AT A} (p : ResultProperty Γ AT Σ) : Prop :=
        forall r, inconsistent (dmutres_pathcondition r) -> p r.

      Lemma resultprop_specialize_vac {Γ A AV Σ1 Σ2} `{Inst A AV} (ζ : Sub Σ1 Σ2)
            (P : ResultProperty Γ A Σ1) (P_vac : resultprop_vacuous P) :
        resultprop_vacuous (resultprop_specialize ζ P).
      Proof.
        intros [Σ3 ζ23 pc3 a3 s3]; unfold resultprop_specialize; cbn.
        intros HYP. apply P_vac; auto.
      Qed.

      Lemma resultprop_specialize_dcl {Γ A AV Σ1 Σ2} `{Inst A AV} (ζ : Sub Σ1 Σ2)
            (POST : ResultProperty Γ A Σ1) (POST_dcl : resultprop_downwards_closed POST) :
        resultprop_downwards_closed (resultprop_specialize ζ POST).
      Proof.
        unfold resultprop_downwards_closed, resultprop_specialize.
        intros [Σ3 ζ3 pc3 a3 s3] [Σ4 ζ4 pc4 a4 s4] Hgeq; cbn.
        now apply POST_dcl, dmutres_geq_pre_comp.
      Qed.

      Lemma resultprop_specialize_id {Γ A Σ} (P : ResultProperty Γ A Σ) :
        forall r, resultprop_specialize (sub_id _) P r <-> P r.
      Proof.
        intros [Σ' ζ pc a s]; unfold resultprop_specialize; cbn.
        now rewrite sub_comp_id_left.
      Qed.

      Lemma resultprop_specialize_comp {Γ A Σ1 Σ2 Σ3} (ζ12 : Sub Σ1 Σ2) (ζ23 : Sub Σ2 Σ3) (P : ResultProperty Γ A Σ1) :
        forall r,
          resultprop_specialize (sub_comp ζ12 ζ23) P r <->
          resultprop_specialize ζ23 (resultprop_specialize ζ12 P) r.
      Proof.
        intros [Σ' ζ pc a s]; unfold resultprop_specialize; cbn.
        now rewrite sub_comp_assoc.
      Qed.

      Definition resultprop_specialize_pc {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) :
        ResultProperty Γ A Σ1 -> ResultProperty Γ A Σ2 :=
        fun p r => geqpc (dmutres_substitution r) pc2 (dmutres_pathcondition r) /\ p (cosubst_dmutres ζ r).

      Lemma resultprop_specialize_pc_dcl {Γ A AV Σ1 Σ2} `{Inst A AV} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2)
            (POST : ResultProperty Γ A Σ1) (POST_dcl : resultprop_downwards_closed POST) :
        resultprop_downwards_closed (resultprop_specialize_pc ζ12 pc2 POST).
      Proof.
        unfold resultprop_downwards_closed, resultprop_specialize_pc.
        intros [Σ3 ζ23 pc3 a3 s3] [Σ4 ζ24 pc4 a4 s4]; cbn.
        intros [ζ34] [Hpc23 Hpost]; destruct_conjs; cbn.
        split.
        - apply geqpc_trans with ζ23 ζ34 pc3; auto.
        - revert Hpost. apply POST_dcl. exists ζ34.
          repeat split; auto. now apply geq_pre_comp.
      Qed.

      Lemma resultprop_specialize_pc_vac {Γ A AV Σ1 Σ2} `{Inst A AV} (ζ : Sub Σ1 Σ2) (pc2 : PathCondition Σ2)
            (P : ResultProperty Γ A Σ1) (P_vac : resultprop_vacuous P) :
        resultprop_vacuous (resultprop_specialize_pc ζ pc2 P).
      Proof.
      Admitted.

      Definition resultprop_lift {Γ AT A Σ1} {instA : Inst AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        ResultProperty Γ AT Σ1 :=
        fun dres =>
          match dres with
          | MkDynMutResult ζ2 pc2 a2 s2 =>
            stateprop_lift ι1 POST ζ2 pc2 a2 s2
          end.

      Definition resultprop_lift_dcl {Γ AT A Σ1} `{InstLaws AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        resultprop_downwards_closed (resultprop_lift ι1 POST).
      Proof.
        unfold resultprop_downwards_closed, resultprop_lift.
        intros [Σ3 ζ3 pc3 a3 s3] [Σ4 ζ4 pc4 a4 s4].
        apply stateprop_lift_dcl.
      Qed.

      Definition resultprop_lift_vac {Γ AT A Σ1} `{InstLaws AT A} (ι1 : SymInstance Σ1) (POST : A -> SCState Γ -> Prop) :
        resultprop_vacuous (resultprop_lift ι1 POST).
      Proof.
        unfold resultprop_vacuous, resultprop_lift, stateprop_lift.
        intros [Σ2 ζ2 pc2 a2 s2] Hpc2; cbn in *. intuition.
      Qed.

    End ResultProp.

    Definition DynamicMutatorArrow Γ1 Γ2 A B Σ0 : Type :=
      forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> DynamicMutator Γ1 Γ2 B Σ1.

    Definition DynamicMutatorArrow' Γ1 Γ2 A B Σ0 : Type :=
      forall Σ1,
        Sub Σ0 Σ1 -> A Σ1 -> PathCondition Σ1 ->
        SymbolicState Γ1 Σ1 -> Outcome (DynamicMutatorResult Γ2 B Σ1).

    Definition dmut_bind' {Γ1 Γ2 Γ3 A B Σ0}
               (ma : DynamicMutator Γ1 Γ2 A Σ0) (f : DynamicMutatorArrow' Γ2 Γ3 A B Σ0) : DynamicMutator Γ1 Γ3 B Σ0 :=
      fun (Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) =>
        outcome_bind (ma Σ1 ζ01 pc1 s1) (fun r : DynamicMutatorResult Γ2 A Σ1 =>
        outcome_bind (f (dmutres_context r) (sub_comp ζ01 (dmutres_substitution r)) (dmutres_result_value r) (dmutres_pathcondition r) (dmutres_result_state r))
                     (fun r2 : DynamicMutatorResult Γ3 B (dmutres_context r) => outcome_pure (cosubst_dmutres (dmutres_substitution r) r2))).

    Section Vacuous.

      Definition outcome_vac `{Inst AT A} {Γ Σ} (pc : PathCondition Σ) (o : Outcome (DynamicMutatorResult Γ AT Σ)) : Prop :=
        forall (P : ResultProperty Γ AT Σ) (P_vac : resultprop_vacuous P),
          inconsistent pc -> outcome_satisfy o P.
      Local Hint Unfold outcome_satisfy : core.
      Local Hint Unfold outcome_vac : core.

      Definition dmut_vac `{Inst AT A} {Γ1 Γ2 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 s1, outcome_vac pc1 (d Σ1 ζ01 pc1 s1).
      Local Hint Unfold dmut_vac : core.

      (* TODO: It would be great to reformulate this to use the above. *)
      Definition dmut_arrow_vac `{Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
        (f : DynamicMutatorArrow Γ1 Γ2 AT BT Σ0) : Prop :=
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 (a1 : AT Σ1) s1,
          outcome_vac pc1 (f Σ1 ζ01 a1 Σ1 (sub_id _) pc1 s1).
      Local Hint Unfold dmut_arrow_vac : core.

      Definition dmut_arrow_vac' `{Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
        (f : DynamicMutatorArrow' Γ1 Γ2 AT BT Σ0) : Prop :=
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 (a1 : AT Σ1) s1,
          outcome_vac pc1 (f Σ1 ζ01 a1 pc1 s1).
      Local Hint Unfold dmut_arrow_vac' : core.

      Lemma dmut_pure_vac `{Subst AT, Inst AT A} {Γ Σ} (a : AT Σ) :
        dmut_vac (dmut_pure (Γ := Γ) a).
      Proof. unfold dmut_pure; auto. Qed.
      Local Hint Resolve dmut_pure_vac : core.

      Lemma dmut_block_vac `{Inst AT A} {Γ1 Γ2 Σ} :
        dmut_vac (@dmut_block Γ1 Γ2 AT Σ).
      Proof. unfold dmut_block; auto. Qed.
      Local Hint Resolve dmut_block_vac : core.

      Lemma dmut_contradiction_vac `{Inst AT A} {D Γ1 Γ2 Σ} func msg data :
        dmut_vac (@dmut_contradiction Γ1 Γ2 AT Σ D func msg data).
      Proof. unfold dmut_contradiction; auto. Qed.
      Local Hint Resolve dmut_contradiction_vac : core.

      Lemma dmut_fail_vac `{Inst AT A} {D Γ1 Γ2 Σ} func msg data :
        dmut_vac (@dmut_fail Γ1 Γ2 AT Σ D func msg data).
      Proof.
        unfold dmut_fail, dmut_vac, outcome_vac; cbn.
        unfold inconsistent, Error. intros.
        (* UH OH *)
      Admitted.
      Local Hint Resolve dmut_fail_vac : core.

      Lemma dmut_bind_vac' `{Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
        (d : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d : dmut_vac d)
        (f : DynamicMutatorArrow' Γ2 Γ3 AT BT Σ0) (vac_f : dmut_arrow_vac' f) :
        dmut_vac (dmut_bind' d f).
      Proof. (* LESS IMPORTANT *) Admitted.
      Local Hint Resolve dmut_bind_vac' : core.

      Lemma dmut_bind_vac `{Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
        (d : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d : dmut_vac d)
        (f : DynamicMutatorArrow Γ2 Γ3 AT BT Σ0) (vac_f : dmut_arrow_vac f) :
        dmut_vac (dmut_bind d f).
      Proof. (* MORE IMPORTANT *) Admitted.
      Local Hint Resolve dmut_bind_vac : core.

      Lemma dmut_sub_vac `{Inst AT A} {Γ1 Γ2 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d : dmut_vac d) :
        forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), dmut_vac (dmut_sub ζ1 d).
      Proof. unfold dmut_sub; auto. Qed.
      Local Hint Resolve dmut_sub_vac : core.

      Lemma dmut_bind_right_vac `{Inst AT A, Inst BT B} {Γ1 Γ2 Γ3 Σ0}
        (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0) (vac_d1 : dmut_vac d1) (vac_d2 : dmut_vac d2) :
        dmut_vac (dmut_bind_right d1 d2).
      Proof. unfold dmut_bind_right; eauto. Qed.
      Local Hint Resolve dmut_bind_right_vac : core.

      Lemma dmut_demonic_binary_vac `{Inst AT A} {Γ1 Γ2 Σ0}
        (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d1 : dmut_vac d1) (vac_d2 : dmut_vac d2) :
        dmut_vac (dmut_demonic_binary d1 d2).
      Proof. Admitted.
      Local Hint Resolve dmut_demonic_binary_vac : core.

      Lemma dmut_angelic_binary_vac `{Inst AT A} {Γ1 Γ2 Σ0}
        (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (vac_d1 : dmut_vac d1) (vac_d2 : dmut_vac d2) :
        dmut_vac (dmut_angelic_binary d1 d2).
      Proof. Admitted.
      Local Hint Resolve dmut_angelic_binary_vac : core.

      Lemma dmut_demonic_finite_vac {AT A} {F : Type} `{Subst AT, Inst AT A, finite.Finite F} {Γ Σ} (k : F -> DynamicMutator Γ Γ AT Σ) :
        (forall v, dmut_vac (k v)) ->
        dmut_vac (dmut_demonic_finite F k).
      Proof. Admitted.
      Local Hint Resolve dmut_demonic_finite_vac : core.

      Lemma dmut_assume_formula_vac {Γ Σ} (f : Formula Σ) :
        dmut_vac (@dmut_assume_formula Γ Σ f).
      Proof. Admitted.
      Local Hint Resolve dmut_assume_formula_vac : core.

      Lemma dmut_produce_chunk_vac {Γ Σ} (c : Chunk Σ) :
        dmut_vac (@dmut_produce_chunk Γ Σ c).
      Proof. Admitted.
      Local Hint Resolve dmut_produce_chunk_vac : core.

      Lemma dmut_fresh_vac {AT A} `{Inst AT A} {Γ Σ σ x} (d : DynamicMutator Γ Γ AT (Σ ▻ (x :: σ))) (d_vac : dmut_vac d) :
        dmut_vac (dmut_fresh (x :: σ) d).
      Proof. Admitted.
      Local Hint Resolve dmut_fresh_vac : core.

      Lemma dmut_freshtermvar_vac {Γ Σ σ x} :
        dmut_vac (@dmut_freshtermvar Γ Σ σ x).
      Proof. unfold dmut_freshtermvar; auto. Qed.
      Local Hint Resolve dmut_freshtermvar_vac : core.

      Local Hint Extern 5 (outcome_vac _ (dmut_bind_right _ _ _ _ _)) =>
        apply dmut_bind_right_vac : core.

      Lemma dmut_produce_vac {Γ Σ} (asn : Assertion Σ) :
        dmut_vac (@dmut_produce Γ Σ asn).
      Proof.
        induction asn; cbn [dmut_produce]; unfold dmut_assume_term; eauto.
        - destruct (term_get_sum s) as [[]|]; eauto 10.
        - destruct (term_get_pair s) as [[]|]; auto. admit.
        - destruct (term_get_record s); eauto. admit.
        - destruct (term_get_union s) as [[]|]; auto.
      Admitted.

      Lemma dmut_exec_vac {Γ Σ τ} (s : Stm Γ τ) :
        dmut_vac (@dmut_exec Γ τ Σ s).
      Proof. Admitted.

    End Vacuous.

    Local Notation "[ ι ] x == y" := (inst ι x = inst ι y) (at level 50).

    (* Read: If ς is equivalent to t in ι, then substituting t for ς is equivalent to the identity. *)
    Lemma inst_single_shift {Σ ς σ} (ςInΣ : ς :: σ ∈ Σ) (t : Term (Σ - (ς :: σ)) σ) ι :
      [ ι ] term_var ς == subst (sub_shift ςInΣ) t ->
      [ ι ] sub_comp (sub_single ςInΣ t) (sub_shift ςInΣ) == sub_id _.
    Proof.
      intros H.
      apply env_lookup_extensional; cbn.
      intros [] bIn.
      unfold sub_id, sub_comp, subst, SubstEnv, inst; cbn.
      rewrite ?env_lookup_map, ?env_lookup_tabulate.
      pose proof (occurs_check_var_spec ςInΣ bIn).
      destruct (occurs_check_var ςInΣ bIn) eqn:?.
      - dependent elimination e. cbn in H0. subst.
        rewrite lookup_sub_single_eq. symmetry. exact H.
      - f_equal.
        destruct H0. subst bIn.
        rewrite lookup_sub_single_neq.
        cbn. unfold sub_shift.
        rewrite env_lookup_tabulate.
        reflexivity.
    Qed.

    Lemma dmutres_try_assume_eq_geq {Γ Σ0 σ} (pc0 : PathCondition Σ0) (t1 t2 : Term Σ0 σ) (s0 : SymbolicState Γ Σ0) :
      OptionSpec
        (fun '(MkDynMutResult ζ01 pc1 tt s1) =>
           geqpc ζ01 (cons (formula_eq t1 t2) pc0) pc1 /\
           geq ζ01 pc1 s0 s1)
        True
        (dmutres_try_assume_eq pc0 t1 t2 s0).
    Proof.
      destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:?; constructor; auto.
      apply (@occurs_check_sound _ _ (@OccursCheckTerm _)) in Heqo;
        auto with typeclass_instances. subst t2.
      split.
      - intros ι0 ι1 <- Hpc0. rewrite inst_pathcondition_cons.
        rewrite <- ?inst_subst. split; cbn; auto.
        rewrite lookup_sub_single_eq.
        rewrite <- ?subst_sub_comp.
        rewrite sub_comp_shift_single.
        rewrite subst_sub_id.
        reflexivity.
      - now apply geq_syntactic.
    Qed.

    Lemma dmutres_try_assume_eq_spec {Γ Σ σ} (pc : PathCondition Σ) (t1 t2 : Term Σ σ) (s__sym : SymbolicState Γ Σ)
      (POST : ResultProperty Γ Unit Σ) (POST_dcl : resultprop_downwards_closed POST) :
      OptionSpec
        (fun r => POST r <->
                  POST (MkDynMutResult
                          (sub_id Σ)
                          (cons (formula_eq t1 t2) pc)
                          tt
                          s__sym))
        True
        (dmutres_try_assume_eq pc t1 t2 s__sym).
    Proof.
      destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:?; constructor; auto.
      apply (@occurs_check_sound _ _ (@OccursCheckTerm _)) in Heqo;
        auto with typeclass_instances. subst t2.
      split.
      - apply POST_dcl. apply dmutres_geq_low_equiv. exists (sub_shift ςInΣ).
        intros * <- Hpc. cbn. rewrite inst_pathcondition_cons in Hpc.
        destruct Hpc as [Hfml Hpc]; cbn in Hfml.
        apply inst_single_shift in Hfml.
        rewrite <- ?inst_subst.
        change (subst (sub_shift ςInΣ) (sub_single ςInΣ t)) with
            (sub_comp (sub_single ςInΣ t) (sub_shift ςInΣ)).
        rewrite <- ?subst_sub_comp.
        rewrite ?inst_subst.
        rewrite Hfml.
        rewrite ?inst_sub_id.
        auto.
      - apply POST_dcl. apply dmutres_geq_low_equiv. exists (sub_single ςInΣ t).
        intros * <- Hpc. rewrite inst_pathcondition_cons.
        rewrite inst_sub_id.
        rewrite <- ?inst_subst. cbn.
        rewrite <- subst_sub_comp.
        rewrite lookup_sub_single_eq.
        rewrite sub_comp_shift_single, subst_sub_id.
        auto.
    Qed.

    (* This should subsume the two lemmas above *)
    Lemma dmutres_try_assume_eq_spec_v2 {Γ Σ0 σ} (pc0 : PathCondition Σ0) (t1 t2 : Term Σ0 σ) (s0 : SymbolicState Γ Σ0) :
      OptionSpec
        (dmutres_equiv (MkDynMutResult (sub_id _) (cons (formula_eq t1 t2) pc0) tt s0))
        True
        (dmutres_try_assume_eq pc0 t1 t2 s0).
    Proof.
    Admitted.

    Lemma dmutres_assume_formula_spec {Γ Σ} (pc : PathCondition Σ) (fml : Formula Σ) (s__sym : SymbolicState Γ Σ)
      (POST : ResultProperty Γ Unit Σ) (POST_dcl : resultprop_downwards_closed POST) :
      POST (dmutres_assume_formula pc fml s__sym) <->
      POST (MkDynMutResult
              (sub_id Σ)
              (cons fml pc)
              tt
              s__sym).
    Proof.
      destruct fml; cbn; auto.
      destruct (dmutres_try_assume_eq_spec pc t1 t2 s__sym POST_dcl); auto. clear H.
      destruct (dmutres_try_assume_eq_spec pc t2 t1 s__sym POST_dcl); auto.
      rewrite H.
      split; apply POST_dcl, dmutres_geq_low_equiv; exists (sub_id _); intros ? ? <-;
          rewrite ?inst_pathcondition_cons, ?inst_sub_id; intuition.
    Qed.

    Lemma dmutres_assume_formula_geq {Γ Σ0} (pc0 : PathCondition Σ0) (fml0 : Formula Σ0) (s0 : SymbolicState Γ Σ0) :
      match dmutres_assume_formula pc0 fml0 s0 with
      | MkDynMutResult ζ01 pc1 tt s1 =>
        geqpc ζ01 (cons fml0 pc0) pc1 /\
        geq ζ01 pc1 s0 s1
      end.
    Proof.
      destruct fml0; cbn; try (split; [ apply geqpc_refl | apply geq_refl ]).
      destruct (dmutres_try_assume_eq_geq pc0 t1 t2 s0); cbn.
      { destruct a as [Σ1 ζ01 pc1 [] s1]; cbn; destruct_conjs; auto. }
      clear H.
      destruct (dmutres_try_assume_eq_geq pc0 t2 t1 s0); cbn.
      { destruct a as [Σ1 ζ01 pc1 [] s1]; cbn.
        destruct H as [Hpc01 Hs]. split; auto.
        intros ? ? rel Hpc1. specialize (Hpc01 _ _ rel Hpc1).
        rewrite inst_pathcondition_cons in *. cbn in *.
        intuition.
      }
      clear H. split.
      - intros ? ? <-.
        rewrite inst_sub_id. rewrite ?inst_pathcondition_cons.
        cbn. intuition.
      - apply geq_refl.
    Qed.

    (* Subsumes the two above. *)
    Lemma dmutres_assume_formula_spec_v2 {Γ Σ0} (pc0 : PathCondition Σ0) (fml0 : Formula Σ0) (s0 : SymbolicState Γ Σ0) :
      dmutres_equiv (dmutres_assume_formula pc0 fml0 s0) (MkDynMutResult (sub_id _) (cons fml0 pc0) tt s0).
    Proof.
    Admitted.

    (* These should be kept abstract in the rest of the proof. If you need some
       property, add a lemma above. *)
    Local Opaque dmutres_try_assume_eq.
    Local Opaque dmutres_assume_formula.

    Section DownwardsClosure.

      Definition dmut_dcl {Γ1 Γ2 AT Σ0 A} `{Inst AT A} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
        forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) (ζ12 : Sub Σ1 Σ2) pc2 s2 ζ02,
          geqpc ζ12 pc1 pc2 ->
          geq ζ12 pc2 s1 s2 ->
          geq ζ12 pc2 ζ01 ζ02 ->
          forall (P : ResultProperty Γ2 AT Σ1) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P)
                 (Q : ResultProperty Γ2 AT Σ2) (PQ : forall r, resultprop_specialize_pc ζ12 pc2 P r -> Q r),
            outcome_satisfy (d Σ1 ζ01 pc1 s1) P ->
            outcome_satisfy (d Σ2 ζ02 pc2 s2) Q.

      Definition dmut_dcl' {Γ1 Γ2 AT Σ0 A} `{Inst AT A} (d : DynamicMutator Γ1 Γ2 AT Σ0) : Prop :=
        forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (s1 : SymbolicState Γ1 Σ1) (ζ12 : Sub Σ1 Σ2) pc2 s2 ζ02,
          geqpc ζ12 pc1 pc2 ->
          geq ζ12 pc2 s1 s2 ->
          geq ζ12 pc2 ζ01 ζ02 ->
          forall (P : ResultProperty Γ2 AT Σ1) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P),
            outcome_satisfy (d Σ1 ζ01 pc1 s1) P ->
            outcome_satisfy (d Σ2 ζ02 pc2 s2) (resultprop_specialize_pc ζ12 pc2 P).

      Lemma dmut_dcl_dcl' {Γ1 Γ2 AT Σ0 A} `{Inst AT A} (d : DynamicMutator Γ1 Γ2 AT Σ0) :
        dmut_dcl d <-> dmut_dcl' d.
      Proof.
        split.
        - unfold dmut_dcl, dmut_dcl'.
          intros d_dcl * Hpc12 Hs12 Hζ12 P P_dcl P_vac.
          eapply d_dcl; eauto.
        - unfold dmut_dcl, dmut_dcl'.
          intros d_dcl * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ.
          intros HP. eapply d_dcl in HP; eauto. revert HP.
          apply outcome_satisfy_monotonic. intros r. apply PQ.
      Qed.

      Lemma dmut_pure_dcl {Γ AT Σ A} {subA: Subst AT} {sublAT: SubstLaws AT}
            {instA : Inst AT A} {instlA : InstLaws AT A} (a : AT Σ) :
        dmut_dcl (dmut_pure (Γ := Γ) a).
      Proof.
        apply dmut_dcl_dcl'. unfold dmut_dcl', dmut_pure; cbn.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac HP.
        split. cbn. apply geqpc_refl. revert HP.
        apply P_dcl.
        exists ζ12. repeat split; auto.
        - apply geq_syntactic. change (subst ζ12 ?ζ) with (sub_comp ζ ζ12).
          now rewrite sub_comp_id_right, sub_comp_id_left.
        - revert Hζ12.
          unfold geq. intros HYP ι1 ι2 rel12 Hpc2.
          specialize (HYP ι1 ι2 rel12 Hpc2) .
          rewrite ?inst_subst. congruence.
      Qed.

      Lemma dmut_fail_dcl `{Inst AT A} {D Γ1 Γ2 Σ} func msg data :
        dmut_dcl (@dmut_fail Γ1 Γ2 AT Σ D func msg data).
      Proof. apply dmut_dcl_dcl'. unfold dmut_dcl', dmut_fail; cbn. intuition. Qed.

      Definition dmut_arrow_dcl' {Γ1 Γ2 AT A BT B Σ0} `{Inst AT A, Inst BT B}
        (f : DynamicMutatorArrow' Γ1 Γ2 AT BT Σ0) : Prop :=
        forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) (ζ02 : Sub Σ0 Σ2) (ζ12 : Sub Σ1 Σ2) pc1 pc2 (a1 : AT Σ1) (a2 : AT Σ2) s1 s2,
          geqpc ζ12 pc1 pc2 ->
          geq ζ12 pc2 s1 s2 ->
          geq ζ12 pc2 ζ01 ζ02 ->
          forall (P : ResultProperty Γ2 BT Σ1) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P)
            (Q : ResultProperty Γ2 BT Σ2) (PQ : forall r, resultprop_specialize_pc ζ12 pc2 P r -> Q r),
            outcome_satisfy (f Σ1 ζ01 a1 pc1 s1) P ->
            outcome_satisfy (f Σ2 ζ02 a2 pc2 s2) Q.

      Lemma dmut_bind_dcl' {AT A BT B} {substB : Subst BT} {instB : Inst BT B} {instA : Inst AT A}
            {subA : Subst AT} {subLA : SubstLaws AT} {instLA : InstLaws AT A}
            {Γ1 Γ2 Γ3 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_dcl : dmut_dcl d)
            (f : DynamicMutatorArrow' Γ2 Γ3 AT BT Σ0)
            (f_dcl : dmut_arrow_dcl' f)
            (f_vac : dmut_arrow_vac' f) :
        dmut_dcl (dmut_bind' d f).
      Proof.
        apply dmut_dcl_dcl'. unfold dmut_dcl', dmut_bind'.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac.
        rewrite ?outcome_satisfy_bind; cbn.
        eapply d_dcl; eauto.
        - clear - f_dcl P P_dcl P_vac.
          unfold resultprop_downwards_closed.
          intros [Σ2 ζ12 pc2 a2 s2] [Σ3 ζ13 pc3 a3 s3] [ζ23 (Hpc23 & Hζ23 & ?)]; cbn in *.
          rewrite ?outcome_satisfy_bind; cbn.
          destruct_conjs. eapply f_dcl; eauto using geq_pre_comp.
          now apply resultprop_specialize_dcl.
          now apply resultprop_specialize_vac.
          intros [Σ4 ζ34 pc4 b4 s4]; unfold resultprop_specialize_pc; cbn.
          intros [Hpc34 HP]; revert HP. apply P_dcl.
          exists (sub_id _).
          repeat split; try apply geq_refl.
          apply geqpc_refl. rewrite <- sub_comp_assoc.
          clear - Hζ23 Hpc34. intros ? ι4 <-. rewrite inst_sub_id.
          pose (inst ι4 ζ34) as ι3.
          pose (inst ι3 ζ23) as ι2.
          specialize (Hζ23 ι2 ι3 eq_refl).
          specialize (Hpc34 ι3 ι4 eq_refl).
          unfold sub_comp; rewrite ?inst_subst.
          intuition.
        - intros [Σ3 ζ23 pc3 a3 s3]; cbn.
          rewrite outcome_satisfy_bind; cbn.
          now apply f_vac, resultprop_specialize_vac.
        - intros [Σ3 ζ23 pc3 a3 s3]; unfold resultprop_specialize_pc; cbn.
          rewrite ?outcome_satisfy_bind; cbn.
          intros [Hpc23 Hpost]; revert Hpost.
          eapply f_dcl; try apply geq_refl.
          + apply geqpc_refl.
          + clear - Hζ12 Hpc23.
            intros ? ι3 <- Hpc3.
            rewrite inst_sub_id.
            pose (inst ι3 ζ23) as ι2.
            pose (inst ι2 ζ12) as ι1.
            specialize (Hpc23 ι2 ι3 eq_refl).
            specialize (Hζ12 ι1 ι2 eq_refl).
            unfold sub_comp. rewrite ?inst_subst.
            intuition.
          + now apply resultprop_specialize_dcl.
          + now apply resultprop_specialize_vac.
          + intros [Σ4 ζ34 pc4 b4 s4]; unfold resultprop_specialize_pc; cbn.
            intros [Hpc34 Hpost]. rewrite sub_comp_id_left, sub_comp_assoc in Hpost.
            split; cbn; auto. apply geqpc_trans with ζ23 ζ34 pc3; auto.
            now apply geq_syntactic.
      Qed.

      Definition dmut_arrow_dcl {Γ1 Γ2 AT A BT B Σ0} `{Inst AT A, Inst BT B}
                 (f : DynamicMutatorArrow Γ1 Γ2 AT BT Σ0) : Prop :=
        forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) (ζ02 : Sub Σ0 Σ2) (ζ12 : Sub Σ1 Σ2) pc1 pc2 (a1 : AT Σ1) (a2 : AT Σ2) s1 s2,
          geqpc ζ12 pc1 pc2 ->
          geq ζ12 pc2 s1 s2 ->
          geq ζ12 pc2 ζ01 ζ02 ->
          forall (P : ResultProperty Γ2 BT Σ1) (P_dcl : resultprop_downwards_closed P) (P_vac : resultprop_vacuous P)
            (Q : ResultProperty Γ2 BT Σ2) (PQ : forall r, resultprop_specialize_pc ζ12 pc2 P r -> Q r),
            outcome_satisfy (f Σ1 ζ01 a1 Σ1 (sub_id _) pc1 s1) P ->
            outcome_satisfy (f Σ2 ζ02 a2 Σ2 (sub_id _) pc2 s2) Q.

      Lemma dmut_bind_dcl {AT A BT B} {substB : Subst BT} {instB : Inst BT B} {instA : Inst AT A}
            {subA : Subst AT} {subLA : SubstLaws AT} {instLA : InstLaws AT A}
            {Γ1 Γ2 Γ3 Σ0} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_wf : dmut_dcl d)
            (f : DynamicMutatorArrow Γ2 Γ3 AT BT Σ0)
            (f_dcl : dmut_arrow_dcl f)
            (f_vac : dmut_arrow_vac f) :
        dmut_dcl (dmut_bind d f).
      Proof.
        apply dmut_dcl_dcl'. unfold dmut_dcl', dmut_bind.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac.
        rewrite ?outcome_satisfy_bind; cbn.
        eapply d_wf; eauto.
        - clear - f_dcl f_vac P P_dcl P_vac.
          unfold resultprop_downwards_closed.
          intros [Σ2 ζ12 pc2 a2 s2] [Σ3 ζ13 pc3 a3 s3] [ζ23 (Hpc23 & Hζ23 & ?)]; cbn in *.
          rewrite ?outcome_satisfy_bind; cbn.
          destruct_conjs. eapply f_dcl; eauto using geq_pre_comp.
          + unfold resultprop_downwards_closed.
            intros [] [] Hgeq; cbn - [dmutres_geq].
            apply P_dcl. revert Hgeq. apply dmutres_geq_pre_comp.
          + unfold resultprop_vacuous.
            intros [] Hpc; cbn in *. now apply P_vac.
          + intros [Σ4 ζ34 pc4 b4 s4]; unfold resultprop_specialize_pc; cbn.
            intros [Hpc34 HP]; revert HP. apply P_dcl.
            exists (sub_id _).
            repeat split; try apply geq_refl.
            apply geqpc_refl.
            clear - Hζ23 Hpc34.
            intros ? ι4 <-. rewrite inst_sub_id.
            pose (inst ι4 ζ34) as ι3.
            pose (inst ι3 ζ23) as ι2.
            specialize (Hζ23 ι2 ι3 eq_refl).
            specialize (Hpc34 ι3 ι4 eq_refl).
            unfold sub_comp; rewrite ?inst_subst.
            intuition.
        - intros [Σ3 ζ23 pc3 a3 s3]; cbn.
          rewrite outcome_satisfy_bind; cbn.
          apply f_vac.
          intros [Σ4 ζ34 pc4 a4 s4]; cbn.
          intros.
          now apply P_vac.
        - intros [Σ3 ζ23 pc3 a3 s3]; unfold resultprop_specialize_pc; cbn.
          rewrite ?outcome_satisfy_bind; cbn.
          intros [Hpc23 Hpost]; revert Hpost.
          eapply f_dcl; try apply geq_refl.
          + apply geqpc_refl.
          + clear - Hζ12 Hpc23. intros ? ι3 <- Hpc3.
            rewrite inst_sub_id.
            pose (inst ι3 ζ23) as ι2.
            pose (inst ι2 ζ12) as ι1.
            specialize (Hpc23 ι2 ι3 eq_refl).
            specialize (Hζ12 ι1 ι2 eq_refl).
            unfold sub_comp. rewrite ?inst_subst.
            intuition.
          + unfold resultprop_downwards_closed.
            intros [] [] Hgeq; cbn - [dmutres_geq].
            apply P_dcl. revert Hgeq. apply dmutres_geq_pre_comp.
          + unfold resultprop_vacuous.
            intros [] Hpc; cbn in *. now apply P_vac.
          + intros [Σ4 ζ34 pc4 b4 s4]; unfold resultprop_specialize_pc; cbn.
            intros [Hpc34 Hpost]. split.
            apply geqpc_trans with ζ23 ζ34 pc3; auto. now apply geq_syntactic.
            now rewrite sub_comp_id_left, sub_comp_assoc in Hpost.
      Qed.

      Lemma dmut_sub_dcl {Γ1 Γ2 AT A Σ0} {instA : Inst AT A} (d : DynamicMutator Γ1 Γ2 AT Σ0) (d_dcl : dmut_dcl d) :
        forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), dmut_dcl (dmut_sub ζ1 d).
      Proof.
        unfold dmut_dcl, dmut_sub.
        intros * Hpc12 Hs12 Hζ12 P P_dcl Q PQ.
        eapply d_dcl; eauto. now apply geq_pre_comp.
      Qed.

      Lemma dmut_bind_right_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
        (d1 : DynamicMutator Γ1 Γ2 AT Σ0) (d2 : DynamicMutator Γ2 Γ3 BT Σ0)
        (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) (d2_vac : dmut_vac d2) :
        dmut_dcl (dmut_bind_right d1 d2).
      Proof.
        unfold dmut_bind_right.
        apply dmut_bind_dcl; auto.
        - unfold dmut_arrow_dcl.
          intros until Q. intros PQ.
          unfold dmut_sub; cbn.
          rewrite ?sub_comp_id_right.
          eapply d2_dcl; eauto.
        - unfold dmut_arrow_vac.
          intros.
          now apply dmut_sub_vac.
      Qed.

      Lemma dmut_demonic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (d_wf1 : dmut_dcl d1) (d_wf2 : dmut_dcl d2) :
        dmut_dcl (dmut_demonic_binary d1 d2).
      Proof.
        unfold dmut_dcl, dmut_demonic_binary; cbn.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ [H1 H2].
        split.
        - revert PQ H1. apply d_wf1; auto.
        - revert PQ H2. apply d_wf2; auto.
      Qed.

      Lemma dmut_angelic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A} (d1 d2 : DynamicMutator Γ1 Γ2 AT Σ0) (d1_dcl : dmut_dcl d1) (d2_dcl : dmut_dcl d2) :
        dmut_dcl (dmut_angelic_binary d1 d2).
      Proof.
        unfold dmut_dcl, dmut_angelic_binary. cbn.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac Q PQ [H1|H1].
        - left. revert PQ H1. apply d1_dcl; auto.
        - right. revert PQ H1. apply d2_dcl; auto.
      Qed.

      Lemma dmut_assume_formula_dcl {Γ Σ} (f : Formula Σ) :
        dmut_dcl (@dmut_assume_formula Γ Σ f).
      Proof.
        apply dmut_dcl_dcl'. unfold dmut_assume_formula, dmut_dcl'.
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac H.
        remember (dmutres_assume_formula pc2 (subst ζ02 f) s2) as r.
        destruct (try_solve_formula_spec (subst ζ01 f));
        destruct (try_solve_formula_spec (subst ζ02 f)); cbn in *.
        - clear r Heqr. destruct a, a0; cbn in *; auto.
          + split; cbn. apply geqpc_refl.
            revert H. apply P_dcl.
            exists ζ12. rewrite sub_comp_id_right.
            repeat split; auto. intros ? ? <-; now rewrite inst_sub_id.
          + apply resultprop_specialize_pc_vac; cbn; auto.
            intros ι Hpc2. specialize (Hζ12 _ ι eq_refl Hpc2).
            specialize (H0 (inst ι ζ12)). specialize (H1 ι).
            rewrite inst_subst in H0. rewrite inst_subst in H1.
            rewrite Hζ12 in H0. clear - H0 H1. intuition.
        - clear H1. destruct a; cbn in *; auto.
          + subst r. pose proof (dmutres_assume_formula_geq pc2 (subst ζ02 f) s2) as Hgeq.
            destruct (dmutres_assume_formula pc2 (subst ζ02 f) s2) as [Σ3 ζ23 pc3 [] s3]; cbn in *.
            destruct Hgeq as [Hpc23 Hs23].
            split; cbn.
            * intros ι2 ι3 rel23 Hpc3. specialize (Hpc23 ι2 ι3 rel23 Hpc3).
              rewrite inst_pathcondition_cons in Hpc23. now destruct Hpc23.
            * revert H. apply P_dcl. apply dmutres_geq_low_equiv. exists (sub_comp ζ12 ζ23).
              intros ι1 ι3 rel13 Hpc3. rewrite inst_sub_id.
              apply syminstance_rel_comp in rel13.
              pose (inst ι3 ζ23) as ι2.
              specialize (Hpc23 ι2 ι3 eq_refl Hpc3).
              specialize (Hs23 ι2 ι3 eq_refl Hpc3).
              rewrite inst_pathcondition_cons in Hpc23. destruct Hpc23 as [Hfml Hpc2].
              specialize (Hpc12 ι1 ι2 rel13 Hpc2).
              specialize (Hs12 ι1 ι2 rel13 Hpc2).
              specialize (Hζ12 ι1 ι2 rel13 Hpc2).
              unfold sub_comp. rewrite inst_subst.
              cbn. repeat split; auto.
              now transitivity (inst ι2 s2).
          + subst r. pose proof (dmutres_assume_formula_geq pc2 (subst ζ02 f) s2) as Hgeq.
            destruct (dmutres_assume_formula pc2 (subst ζ02 f) s2) as [Σ3 ζ23 pc3 [] s3]; cbn in *.
            destruct Hgeq as [Hpc23 Hs23].
            split; cbn.
            * intros ι2 ι3 rel23 Hpc3. specialize (Hpc23 ι2 ι3 rel23 Hpc3).
              rewrite inst_pathcondition_cons in Hpc23. now destruct Hpc23.
            * clear - H0 Hpc23 Hpc12. admit.
        - clear H0 r Heqr. destruct a; cbn; auto. split; cbn.
          apply geqpc_refl. rewrite sub_comp_id_right.
          apply (dmutres_assume_formula_spec pc1 (subst ζ01 f) s1) in H; auto.
          revert H. apply P_dcl. apply dmutres_geq_low_equiv.
          exists ζ12. intros ι1 ι2 <- Hpc2.
          rewrite inst_pathcondition_cons, inst_sub_id, ?inst_subst; cbn.
          intuition.
          specialize (Hζ12 _ ι2 eq_refl Hpc2). rewrite Hζ12.
          rewrite <- inst_subst. now apply H1.
        - clear H0 H1. subst r.
          pose proof (dmutres_assume_formula_geq pc2 (subst ζ02 f) s2) as Hgeq.
          destruct (dmutres_assume_formula pc2 (subst ζ02 f) s2) as [Σ3 ζ23 pc3 [] s3]; cbn in *.
          destruct Hgeq as [Hpc23 Hs23].
          split; cbn.
          * intros ι2 ι3 rel23 Hpc3. specialize (Hpc23 ι2 ι3 rel23 Hpc3).
            rewrite inst_pathcondition_cons in Hpc23. now destruct Hpc23.
          * apply (dmutres_assume_formula_spec pc1 (subst ζ01 f) s1) in H; auto.
            revert H. apply P_dcl. apply dmutres_geq_low_equiv.
            exists (sub_comp ζ12 ζ23). intros ι1 ι3 <- Hpc3.
            rewrite inst_pathcondition_cons, inst_sub_id.
            unfold sub_comp; rewrite ?inst_subst; cbn.
            repeat split; auto.
            admit.
            admit.
            admit.
      Admitted.

      Lemma dmut_produce_chunk_dcl {Γ Σ} (c : Chunk Σ) :
        dmut_dcl (@dmut_produce_chunk Γ Σ c).
      Proof. Admitted.

      Lemma dmut_fresh_dcl {AT A} `{Inst AT A} {Γ Σ σ x} (d : DynamicMutator Γ Γ AT (Σ ▻ (x :: σ))) (d_dcl : dmut_dcl d) :
        dmut_dcl (dmut_fresh (x :: σ) d).
      Proof. Admitted.

      Lemma dmut_freshtermvar_dcl {Γ Σ σ x} :
        dmut_dcl (@dmut_freshtermvar Γ Σ σ x).
      Proof.
        apply dmut_dcl_dcl'. unfold dmut_dcl', dmut_freshtermvar; cbn - [dmut_fresh].
        intros * Hpc12 Hs12 Hζ12 P P_dcl P_vac.
        eapply dmut_fresh_dcl; eauto.
        apply dmut_pure_dcl.
      Qed.

      Lemma dmut_produce_dcl {Γ Σ} (asn : Assertion Σ) :
        dmut_dcl (@dmut_produce Γ Σ asn).
      Proof.
        induction asn; cbn [dmut_produce]; unfold dmut_assume_term.
        - apply dmut_assume_formula_dcl.
        - apply dmut_produce_chunk_dcl.
        - apply dmut_demonic_binary_dcl.
          apply dmut_bind_right_dcl;
            auto using dmut_assume_formula_dcl, dmut_produce_vac.
          apply dmut_bind_right_dcl;
            auto using dmut_assume_formula_dcl, dmut_produce_vac.
        - admit.
        - admit.
        - apply dmut_fail_dcl.
        - admit.
        - apply dmut_fail_dcl.
        - admit.
        - admit.
        - apply dmut_bind_right_dcl; auto using dmut_produce_vac.
        - now apply dmut_fresh_dcl.
      Admitted.

      Lemma dmut_exec_dcl {Γ Σ τ} (s : Stm Γ τ) :
        dmut_vac (@dmut_exec Γ τ Σ s).
      Proof. Admitted.

    End DownwardsClosure.

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

    Definition dmut_wp {Γ1 Γ2 Σ0 A}
      (m : DynamicMutator Γ1 Γ2 A Σ0)
      (POST : StateProperty Γ2 A Σ0)
      (pc0 : PathCondition Σ0)
      (s1 : SymbolicState Γ1 Σ0) : Prop :=
      forall Σ1 (ζ1 : Sub Σ0 Σ1),
        outcome_satisfy
          (* SK: There is still some wiggle room here. We can generalize to
             oathconditions in Σ1 that are stronger than pc0. *)
          (m Σ1 ζ1 (subst ζ1 pc0) (subst ζ1 s1))
          (fun '(MkDynMutResult ζ2 pc2 a2 s2) =>
             POST _ (sub_comp ζ1 ζ2) pc2 a2 s2).

    Lemma dmut_wp_monotonic {Γ1 Γ2 Σ0 A} (m : DynamicMutator Γ1 Γ2 A Σ0)
          (P Q : StateProperty Γ2 A Σ0) (HYP : stateprop_impl P Q) :
      forall (pc : PathCondition Σ0) (s : SymbolicState Γ1 Σ0),
        dmut_wp m P pc s -> dmut_wp m Q pc s.
    Proof.
      unfold dmut_wp; cbn; intros pc1 s1 H Σ1 ζ1.
      specialize (H Σ1 ζ1). revert H.
      apply outcome_satisfy_monotonic.
      intros [Σ2 ζ2 pc2 a2 s2]; cbn.
      intuition.
    Qed.

    Definition APPROX Γ1 Γ2 AT A {instA : Inst AT A} : Type :=
      forall Σ (ι : SymInstance Σ),
        DynamicMutator Γ1 Γ2 AT Σ -> SCMut Γ1 Γ2 A -> Prop.
    Arguments APPROX _ _ _ _ {_}.

    Definition box {Γ1 Γ2 AT A} {instA : Inst AT A} (R : APPROX Γ1 Γ2 AT A) : APPROX Γ1 Γ2 AT A :=
      fun Σ ι dm sm =>
        forall Σ1 (ζ1 : Sub Σ Σ1) (ι1 : SymInstance Σ1),
          syminstance_rel ζ1 ι ι1 ->
          R Σ1 ι1 (dmut_sub ζ1 dm) sm.

    Lemma box_proj {Γ1 Γ2 AT A} {instA : Inst AT A} (R : APPROX Γ1 Γ2 AT A) :
      forall Σ (ι : SymInstance Σ) dm sm,
        box R ι dm sm -> R _ ι dm sm.
    Proof.
      intros ? ? ? ? b.
      unfold box in b.
      inster b by apply syminstance_rel_refl.
      unfold dmut_sub in b.
      (* apply b. *)
    Admitted.

    Definition box_box {Γ1 Γ2 AT A} {instA : Inst AT A} (R : APPROX Γ1 Γ2 AT A) :
      forall Σ (ι : SymInstance Σ) dm sm,
        box R ι dm sm -> box (box R) ι dm sm.
    Proof.
      intros ? ? ? ?. unfold box. intros bb Σ1 ζ1 ι1 ? Σ2 ζ2 ι2 ?.
      specialize (bb Σ2 (sub_comp ζ1 ζ2) ι2).
      inster bb by eapply syminstance_rel_trans; eauto.
      (* apply bb. *)
    Admitted.

    Definition approximates {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
      fun Σ ι dm sm =>
        forall pc (s__sym : SymbolicState Γ1 Σ),
        forall (POST : A -> SCState Γ2 -> Prop),
          dmut_wp dm (stateprop_lift ι POST) pc s__sym ->
          (inst ι pc : Prop) ->
          scmut_wp sm POST (inst ι s__sym).

    Lemma approximates_proj {Γ1 Γ2 AT A} {instA : Inst AT A} {Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (sm : SCMut Γ1 Γ2 A) :
      box approximates ι dm sm -> approximates ι dm sm.
    Proof.
      unfold approximates, box. intros Happrox * Hdwp Hpc.
      inster Happrox by apply syminstance_rel_refl.
      specialize (Happrox pc). apply Happrox; auto.
      unfold dmut_wp, dmut_sub. intros Σ1 ζ1.
      rewrite sub_comp_id_left. apply Hdwp.
    Qed.

    Lemma approximates_box_box {Γ1 Γ2 AT A} {instA : Inst AT A} {Σ} (ι : SymInstance Σ)
      (dm : DynamicMutator Γ1 Γ2 AT Σ) (sm : SCMut Γ1 Γ2 A) :
      box approximates ι dm sm -> box (box approximates) ι dm sm.
    Proof.
      unfold approximates, box, dmut_wp, dmut_sub. intros.
      inster H by eapply syminstance_rel_trans; eauto.
      specialize (H pc). apply H; auto.
      intros. now rewrite sub_comp_assoc.
    Qed.

    Lemma approximates_sub {Γ Σ Σ1} (ζ1 : Sub Σ Σ1) (ι : SymInstance Σ) (ι1 : SymInstance Σ1)
      (relι1 : syminstance_rel ζ1 ι ι1) (d : DynamicMutator Γ Γ Unit Σ) (s : SCMut Γ Γ unit) :
      box approximates ι d s -> box approximates ι1 (dmut_sub ζ1 d) s.
    Proof. intros H. eapply approximates_box_box; eauto. Qed.

    Lemma approximates_fail `{Inst AT A} {D Γ1 Γ2 Σ} func msg data ι s :
      box approximates ι (@dmut_fail Γ1 Γ2 AT Σ D func msg data) s.
    Proof. Admitted.

    Lemma approximates_block `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) :
      box approximates ι (@dmut_block Γ1 Γ2 AT Σ) (@scmut_block Γ1 Γ2 A).
    Proof. Admitted.

    Lemma scmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic_binary sm1 sm2) POST s__sc <->
      scmut_wp sm1 POST s__sc /\ scmut_wp sm2 POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic_binary; cbn; intuition. Qed.

    Lemma dmut_wp_demonic_binary {Γ1 Γ2 Σ A} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ)
      (POST : StateProperty Γ2 A Σ) pc (s : SymbolicState Γ1 Σ) :
        dmut_wp (dmut_demonic_binary m1 m2) POST pc s <->
        dmut_wp m1 POST pc s /\ dmut_wp m2 POST pc s.
    Proof. unfold dmut_wp, dmut_demonic_binary; cbn; intuition. Qed.

    Lemma dmut_wp_sub_demonic_binary {Γ1 Γ2 Σ A Σ1} (ζ1 : Sub Σ Σ1) (m1 m2 : DynamicMutator Γ1 Γ2 A Σ)
      (POST : StateProperty Γ2 A Σ1) pc (s : SymbolicState Γ1 Σ1) :
        dmut_wp (dmut_sub ζ1 (dmut_demonic_binary m1 m2)) POST pc s <->
        dmut_wp (dmut_sub ζ1 m1) POST pc s /\ dmut_wp (dmut_sub ζ1 m2) POST pc s.
    Proof. unfold dmut_wp, dmut_demonic_binary; cbn; intuition. Qed.

    Lemma approximates_demonic_binary {Γ1 Γ2 Σ} (ι : SymInstance Σ)
          (dm1 dm2 : DynamicMutator Γ1 Γ2 Unit Σ) (sm1 sm2 : SCMut Γ1 Γ2 unit) :
      box approximates ι dm1 sm1 ->
      box approximates ι dm2 sm2 ->
      box approximates ι (dmut_demonic_binary dm1 dm2) (scmut_demonic_binary sm1 sm2).
    Proof.
      unfold box. intros H1 H2 Σ1 ζ1 ι1 H__ι.
      specialize (H1 Σ1 ζ1 ι1 H__ι). specialize (H2 Σ1 ζ1 ι1 H__ι).
      intros pc s1 POST Hwp Hpc. apply dmut_wp_sub_demonic_binary in Hwp.
      destruct Hwp as [Hwp1 Hwp2].
      specialize (H1 pc s1 POST Hwp1 Hpc). specialize (H2 pc s1 POST Hwp2 Hpc).
      apply scmut_wp_demonic_binary. split; auto.
    Qed.

    Lemma scmut_wp_demonic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
      scmut_wp (scmut_demonic sm) POST s__sc <-> forall v, scmut_wp (sm v) POST s__sc.
    Proof. unfold scmut_wp, scmut_demonic; cbn; intuition. Qed.

    Lemma dmut_wp_demonic {Γ1 Γ2 Σ A B} (m : B -> DynamicMutator Γ1 Γ2 A Σ)
      (POST : StateProperty Γ2 A Σ) pc (s : SymbolicState Γ1 Σ) :
        dmut_wp (dmut_demonic m) POST pc s <->
        forall b, dmut_wp (m b) POST pc s.
    Proof. unfold dmut_wp, dmut_demonic; cbn; intuition. Qed.

    Lemma subst_symbolicstate_produce_chunk {Γ Σ Σ1} (ζ1 : Sub Σ Σ1) (c : Chunk Σ) (s : SymbolicState Γ Σ) :
      subst ζ1 (symbolicstate_produce_chunk c s) = symbolicstate_produce_chunk (subst ζ1 c) (subst ζ1 s).
    Proof. now destruct s. Qed.

    Lemma dmut_wp_produce_chunk {Γ Σ Σ1} (ζ1 : Sub Σ Σ1) (c : Chunk _) pc (s__sym : SymbolicState Γ _)
          (POST : StateProperty Γ Unit _) (POST_dcl : stateprop_downwards_closed POST) :
      dmut_wp (dmut_sub ζ1 (dmut_produce_chunk c)) POST pc s__sym <->
      POST Σ1 (sub_id Σ1) pc tt (symbolicstate_produce_chunk (subst ζ1 c) s__sym).
    Proof.
      split.
      - intros dwp.
        specialize (dwp Σ1 (sub_id Σ1)). cbn in dwp.
        now rewrite ?sub_comp_id_right, ?subst_sub_id in dwp.
      - intros p Σ2 ζ2. cbn. rewrite subst_sub_comp. revert p.
        apply POST_dcl. apply dmutres_geq_syntactic.
        exists ζ2.
        rewrite sub_comp_id_right, sub_comp_id_left.
        now rewrite subst_symbolicstate_produce_chunk.
    Qed.

    Lemma dmut_produce_chunk_sound {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce_chunk c)
        (scmut_produce_chunk (inst ι c)).
    Proof.
      intros ? ? ? <- ? ? ? Hwp Hpc. cbn.
      apply dmut_wp_produce_chunk in Hwp.
      - specialize (Hwp ι1). inster Hwp by apply syminstance_rel_refl.
        specialize (Hwp Hpc). destruct s__sym as [δ h]; cbn.
        now rewrite <- inst_subst.
      - apply stateprop_lift_dcl.
    Qed.

    Lemma dmut_wp_sub {Γ1 Γ2 A Σ0} (d : DynamicMutator Γ1 Γ2 A Σ0)
          (POST : StateProperty Γ2 A Σ0) pc (s : SymbolicState Γ1 Σ0) Σ1 (ζ : Sub Σ0 Σ1) :
        dmut_wp d POST pc s ->
        dmut_wp (dmut_sub ζ d) (stateprop_specialize ζ POST) (subst ζ pc) (subst ζ s).
    Proof.
      unfold dmut_sub, dmut_wp. intros * Hpost *.
      specialize (Hpost Σ2 (sub_comp ζ ζ1)).
      rewrite ?subst_sub_comp in Hpost. revert Hpost.
      apply outcome_satisfy_monotonic. clear. intros [Σ3 ζ3 pc3 a3 s3].
      unfold stateprop_specialize. now rewrite sub_comp_assoc.
    Qed.

    Opaque subst.
    Opaque sub_up1.
    Opaque sub_snoc.
    Opaque wk1.
    Opaque SubstEnv.

    Lemma dmut_wp_bind {AT A BT B} {instA : Inst AT A} {substB : Subst BT} {instB : Inst BT B}
          {Γ1 Γ2 Γ3 Σ0} (ma : DynamicMutator Γ1 Γ2 AT Σ0)
          (f : forall Σ', Sub Σ0 Σ' -> AT Σ' -> DynamicMutator Γ2 Γ3 BT Σ')
          (f_dcl : dmut_arrow_dcl f)
          (POST : StateProperty Γ3 BT Σ0) (POST_dcl : stateprop_downwards_closed POST) :
      forall pc (s0 : SymbolicState Γ1 Σ0),
        dmut_wp (dmut_bind ma f) POST pc s0 <->
        dmut_wp ma (fun Σ1 ζ1 pc1 a1 => dmut_wp (f Σ1 ζ1 a1) (stateprop_specialize ζ1 POST) pc1) pc s0.
    Proof.
      (* unfold DynamicMutator, dmut_bind, dmut_wp, dmut_dcl in *; cbn; intros pc0 s0. *)
      (* split; intros H Σ1 ζ1; specialize (H Σ1 ζ1). revert H. *)
      (* - rewrite outcome_satisfy_bind. apply outcome_satisfy_monotonic. *)
      (*   intros [Σ2 ζ2 pc2 a2 s2] H Σ3 ζ3. revert H. *)
      (*   rewrite outcome_satisfy_bind. *)
      (*   eapply f_dcl. *)

      (* OLD: *)
      (*   apply (f_wf Σ2 (sub_comp ζ1 ζ2) a2 Σ2 Σ3 (sub_id Σ2) ζ3) in H. *)
      (*   + revert H. rewrite sub_comp_id_left. *)
      (*     apply outcome_satisfy_monotonic. *)
      (*     intros [Σ4 ζ4 pc4 b4 s4]. cbn. *)
      (*     now rewrite <- sub_comp_assoc. *)
      (*   + clear f_wf H. *)
      (*     unfold resultprop_downwards_closed. *)
      (*     intros [Σ4 ζ4 pc4 b4 s4] [Σ5 ζ5 pc5 b5 s5]. cbn - [dmutres_geq]. *)
      (*     intros Hgeq. apply POST_dcl. rewrite <- ?sub_comp_assoc. *)
      (*     revert Hgeq. apply dmutres_geq_pre_comp. *)
      (* - rewrite outcome_satisfy_bind. revert H. *)
      (*   apply outcome_satisfy_monotonic. *)
      (*   intros [Σ2 ζ2 pc2 a2 s2] H. specialize (H Σ2 (sub_id _)). *)
      (*   revert H. rewrite outcome_satisfy_bind, ?subst_sub_id. *)
      (*   apply outcome_satisfy_monotonic. *)
      (*   intros [Σ3 ζ3 pc3 b3 s3]. cbn. *)
      (*   unfold stateprop_specialize. *)
      (*   now rewrite sub_comp_id_left, sub_comp_assoc. *)
    Admitted.

    Lemma dmut_wp_sub_bind {AT A BT B} {instA : Inst AT A} {instB : Inst BT B} {subB: Subst BT}
          {Γ1 Γ2 Γ3 Σ0 Σ1} (ζ1 : Sub Σ0 Σ1)
          (ma : DynamicMutator Γ1 Γ2 AT Σ0)
          (f : forall Σ', Sub Σ0 Σ' -> AT Σ' -> DynamicMutator Γ2 Γ3 BT Σ')
          (f_dcl : dmut_arrow_dcl f)
          (POST : StateProperty Γ3 BT Σ1) (POST_dcl : stateprop_downwards_closed POST) :
      forall pc1 s1,
        dmut_wp (dmut_sub ζ1 (dmut_bind ma f)) POST pc1 s1 <->
        dmut_wp
          (dmut_sub ζ1 ma)
          (fun Σ2 ζ2 pc2 a2 => dmut_wp (f Σ2 (sub_comp ζ1 ζ2) a2) (stateprop_specialize ζ2 POST) pc2)
          pc1 s1.
    Proof.
      (* unfold DynamicMutator, dmut_bind, dmut_sub, dmut_wp, dmut_dcl in *; cbn; intros pc1 s1. *)
      (* split; intros H Σ2 ζ2; specialize (H Σ2 ζ2). revert H. *)
      (* - rewrite outcome_satisfy_bind. apply outcome_satisfy_monotonic. *)
      (*   intros [Σ3 ζ3 pc3 a3 s3] H Σ4 ζ4. revert H. *)
      (*   rewrite outcome_satisfy_bind. *)
      (*   eapply f_dcl. *)

      (* OLD: *)
      (*   apply (f_wf Σ3 (sub_comp (sub_comp ζ1 ζ2) ζ3) a3 Σ3 Σ4 (sub_id Σ3) ζ4) in H. *)
      (*   + revert H. rewrite sub_comp_id_left, sub_comp_assoc. *)
      (*     apply outcome_satisfy_monotonic. *)
      (*     intros [Σ5 ζ5 b5 s5]. cbn. *)
      (*     now rewrite <- sub_comp_assoc. *)
      (*   + revert POST_dcl. clear. intros. *)
      (*     unfold resultprop_downwards_closed. *)
      (*     intros [Σ4 ζ4 b4 s4] [Σ5 ζ5 b5 s5] Hgeq. *)
      (*     cbn. apply POST_dcl. rewrite <- ?sub_comp_assoc. *)
      (*     revert Hgeq. apply dmutres_geq_sem_pre_comp. *)
      (* - rewrite outcome_satisfy_bind. revert H. *)
      (*   apply outcome_satisfy_monotonic. *)
      (*   intros [Σ3 ζ3 a3 s3] H. specialize (H Σ3 (sub_id _)). *)
      (*   revert H. rewrite outcome_satisfy_bind, subst_sub_id, sub_comp_assoc. *)
      (*   apply outcome_satisfy_monotonic. *)
      (*   intros [Σ4 ζ4 b4 s4]. cbn. *)
      (*   unfold stateprop_specialize. *)
      (*   now rewrite sub_comp_id_left, sub_comp_assoc. *)
    Admitted.


    Lemma inst_snoc_wk1 {Σ2 x τ} {ι0 : SymInstance (Σ2 ▻ (x :: τ))} {ι1} `{Subst AT} {substLawsA : SubstLaws AT} `{Inst AT A} {instLaws : InstLaws AT A} {t : AT Σ2} {v} :
      syminstance_rel (sub_id Σ2 ► (x :: τ ↦ v)) ι0 ι1 -> inst ι0 (wk1 t) = inst ι1 t.
    Proof.
      unfold syminstance_rel.
      intros; subst ι0.
      change (wk1 t) with (subst (sub_wk1 (b := x :: τ)) t).
      rewrite inst_subst.
      f_equal.
      rewrite <-inst_subst.
      replace (subst (sub_id Σ2 ► (x :: τ ↦ v)) sub_wk1) with (sub_id Σ2); [now rewrite inst_sub_id|].
      change (subst (sub_id Σ2 ► (x :: τ ↦ v)) sub_wk1) with (sub_comp sub_wk1 (sub_id Σ2 ► (x :: τ ↦ v))).
      rewrite sub_comp_wk1_tail.
      now cbn.
    Qed.

    Lemma dmut_wp_fresh {Γ Σ0 AT A x τ} `{Subst AT, Inst AT A}
          (d : DynamicMutator Γ Γ AT (Σ0 ▻ (x,τ))%ctx) (d_dcl : dmut_dcl d)
          (POST : StateProperty Γ AT Σ0)
          (POST_dcl : stateprop_downwards_closed POST)
          (POST_vac : stateprop_vacuous POST)
          (pc : PathCondition Σ0) (s : SymbolicState Γ Σ0) :
      dmut_wp (dmut_fresh (x,τ) d) POST pc s <->
      dmut_wp d (stateprop_specialize sub_wk1 POST) (subst sub_wk1 pc) (subst sub_wk1 s).
    Proof.
      unfold dmut_wp, dmut_fresh; cbn; split; intros HYP ? ?.
      - dependent elimination ζ1 as [@env_snoc Σ0 ζ1 _ v]; cbn in v.
        rewrite <- subst_sub_comp, sub_comp_wk1_tail; cbn.
        specialize (HYP Σ1 ζ1).
        rewrite outcome_satisfy_map in HYP; cbn in *.
        refine (@d_dcl _ Σ1 _ _ _ (env_snoc (sub_id _) (_,τ) v) _ _ _ _ _ _ _ _ _ _ _ HYP); clear d_dcl HYP.
        + unfold geqpc.
          intros.
          now rewrite (inst_snoc_wk1 H1).
        + unfold geq.
          intros.
          rewrite (inst_snoc_wk1 H1).
          f_equal.
          now rewrite <-subst_sub_comp, sub_comp_wk1_tail.
        + unfold geq, syminstance_rel.
          intros. subst ι0.
          rewrite <-inst_subst.
          f_equal.
          change (subst _ _) with (sub_comp (sub_up1 ζ1) (sub_id Σ1 ► (x :: τ ↦ v))).
          now rewrite <- (sub_snoc_comp ζ1),  sub_comp_id_right.
        + revert POST_dcl. clear. intros.
          unfold resultprop_downwards_closed.
          intros [Σ3 ζ3 pc3 a3 s3] [Σ4 ζ4 pc4 a4 s4] Hgeq.
          cbn. apply POST_dcl. rewrite <- ?sub_comp_assoc.
          revert Hgeq. apply dmutres_geq_pre_comp.
        + unfold resultprop_vacuous.
          intros [Σ3 ζ3 pc3 a3 s3].
          cbn.
          eapply POST_vac.
        + intros [Σ3 ζ3 pc3 a3 s3].
          unfold resultprop_specialize_pc. cbn.
          intros [geqpc post].
          rewrite <-(sub_comp_assoc sub_wk1), sub_comp_wk1_tail in post.
          cbn in post.
          rewrite sub_comp_id_left in post.
          unfold stateprop_specialize.
          now rewrite <-(sub_comp_assoc sub_wk1), sub_comp_wk1_tail.
      - rewrite outcome_satisfy_map.
        specialize (HYP (Σ1 ▻ (x,τ)) (sub_up1 ζ1)).
        rewrite <- ?subst_sub_comp, ?sub_comp_wk1_comm in HYP.
        change (wk1 (b := (x,τ)) (subst ζ1 ?t)) with (subst (sub_wk1 (b := (x,τ))) (subst ζ1 t)).
        rewrite <- ?subst_sub_comp. revert HYP.
        apply outcome_satisfy_monotonic.
        intros [Σ2 ζ2 pc2 a2 s2]. clear.
        dependent elimination ζ2 as [@env_snoc Σ1 ζ2 _ t].
        unfold stateprop_specialize. cbn.
        now rewrite <- ?sub_comp_assoc, <- sub_comp_wk1_comm.
    Qed.

    Lemma dmut_wp_sub_fresh {Γ Σ0 Σ1 AT A x τ} `{Subst AT, Inst AT A}
          (ζ1 : Sub Σ0 Σ1)
          (d : DynamicMutator Γ Γ AT (Σ0 ▻ (x,τ))%ctx)
          (POST : StateProperty Γ AT Σ1)
          (POST_dcl : stateprop_downwards_closed POST)
          (POST_vac : stateprop_vacuous POST)
          (pc : PathCondition Σ1)
          (s : SymbolicState Γ Σ1) (wfd : dmut_dcl d) :
      dmut_wp (dmut_sub ζ1 (dmut_fresh (x,τ) d)) POST pc s <->
      dmut_wp (dmut_sub (sub_up1 ζ1) d) (stateprop_specialize sub_wk1 POST) (subst sub_wk1 pc) (subst sub_wk1 s).
    Proof.
      (* OLD: *)
      unfold dmut_wp, dmut_sub, dmut_fresh; cbn; split; intros HYP Σ2 ζ2.
      - dependent elimination ζ2 as [@env_snoc Σ1 ζ2 _ v]; cbn in v.
        rewrite <- ?subst_sub_comp, ?sub_comp_wk1_tail; cbn.
        specialize (HYP Σ2 ζ2).
        rewrite outcome_satisfy_map in HYP; cbn in *.
        Print dmut_dcl.
        refine (wfd _ Σ2 _ _ _ (env_snoc (sub_id _) (_,τ) v) _ _ _ _ _ _ _ _ _ _ _ HYP); clear wfd.
        + unfold geqpc.
          intros.
          now rewrite (inst_snoc_wk1 H1).
        + unfold geq.
          intros.
          now rewrite (inst_snoc_wk1 H1).
        + unfold geq, syminstance_rel.
          intros. subst ι0.
          rewrite <-inst_subst.
          f_equal.
          rewrite sub_up_comp.
          change (subst _ (sub_comp _ _)) with (sub_comp (sub_comp (sub_up1 ζ1) (sub_up1 ζ2)) (sub_id Σ2 ► (x :: τ ↦ v))).
          rewrite (sub_comp_assoc (sub_up1 ζ1)).
          f_equal.
          now rewrite <- (sub_snoc_comp ζ2),  sub_comp_id_right.
        + revert POST_dcl. clear. intros.
          unfold resultprop_downwards_closed.
          intros [Σ3 ζ3 pc3 a3 s3] [Σ4 ζ4 pc4 a4 s4] Hgeq.
          cbn. apply POST_dcl. rewrite <- ?sub_comp_assoc.
          revert Hgeq. apply dmutres_geq_pre_comp.
        + unfold resultprop_vacuous.
          intros [Σ3 ζ3 pc3 a3 s3].
          cbn.
          eapply POST_vac.
        + intros [Σ3 ζ3 pc3 a3 s3].
          unfold resultprop_specialize_pc. cbn.
          intros [geqpc post].
          rewrite <-(sub_comp_assoc sub_wk1), sub_comp_wk1_tail in post.
          cbn in post.
          rewrite sub_comp_id_left in post.
          unfold stateprop_specialize.
          now rewrite <-(sub_comp_assoc sub_wk1), sub_comp_wk1_tail.
      - rewrite outcome_satisfy_map.
        specialize (HYP (Σ2 ▻ (x,τ)) (sub_up1 ζ2)).
        rewrite <- ?subst_sub_comp, ?sub_comp_wk1_comm in HYP.
        change (wk1 (b := (x,τ)) (subst ζ2 ?t)) with (subst (sub_wk1 (b := (x,τ))) (subst ζ2 t)).
        rewrite ?sub_up_comp, <- ?subst_sub_comp.
        revert HYP. apply outcome_satisfy_monotonic.
        intros [Σ3 ζ3 pc3 a3 s3]. clear.
        dependent elimination ζ3 as [@env_snoc Σ2 ζ3 _ t].
        unfold stateprop_specialize. cbn.
        now rewrite <- ?sub_comp_assoc, <- sub_comp_wk1_comm.
    Qed.

    Lemma dmut_bind_sound {Γ1 Γ2 Γ3 Σ0 AT A BT B}
      `{Subst AT, Inst AT A, InstLaws BT B} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (dm_dcl : dmut_dcl dma)
      (sma : SCMut Γ1 Γ2 A)
      (dmf : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> DynamicMutator Γ2 Γ3 BT Σ1)
      (dmf_dcl : dmut_arrow_dcl dmf)
      (smf : A -> SCMut Γ2 Γ3 B) :
      box approximates ι0 dma sma ->
      (forall Σ1 (ζ1 : Sub Σ0 Σ1) (a1 : AT Σ1) (ι1 : SymInstance Σ1),
          syminstance_rel ζ1 ι0 ι1 ->
          box approximates ι1 (dmf Σ1 ζ1 a1) (smf (inst ι1 a1))) ->
      box approximates ι0 (dmut_bind dma dmf) (scmut_bind sma smf).
    Proof.
      intros H__a H__f.
      intros Σ1 ζ1 ι1 relι1 pc1 s__sym1 POST H__wp Hpc.
      apply scmut_wp_bind. revert Hpc.
      apply dmut_wp_sub_bind in H__wp; auto using stateprop_lift_dcl.
      specialize (H__a Σ1 ζ1 ι1 relι1).
      apply H__a. revert H__wp. apply dmut_wp_monotonic.
      intros Σ2 ζ2 pc2 a2 s2 Hwp2 ι2 rel12 Hpc2. revert Hpc2.
      specialize (H__f Σ2 (sub_comp ζ1 ζ2) a2 ι2).
      inster H__f by eapply syminstance_rel_trans; eauto.
      apply approximates_proj in H__f. apply H__f.
      revert Hwp2. apply dmut_wp_monotonic.
      intros Σ3 ζ3 pc3 b3 s__sym3 H__post ι3 rel23 Hpc3.
      apply H__post. apply (syminstance_rel_trans rel12 rel23). assumption.
    Qed.

    Lemma dmut_bind_right_sound {Γ1 Γ2 Γ3 Σ0 AT A BT B}
      `{Subst AT, Inst AT A, InstLaws BT B} (ι0 : SymInstance Σ0)
      (dma : DynamicMutator Γ1 Γ2 AT Σ0) (dm_dcl : dmut_dcl dma) (sma : SCMut Γ1 Γ2 A)
      (dmb : DynamicMutator Γ2 Γ3 BT Σ0) (dmb_dcl : dmut_dcl dmb) (smb : SCMut Γ2 Γ3 B) :
      box approximates ι0 dma sma ->
      box approximates ι0 dmb smb ->
      box approximates ι0 (dmut_bind_right dma dmb) (scmut_bind_right sma smb).
    Proof.
    Admitted.

    Lemma dmut_fresh_sound {Γ Σ ς τ} (ι : SymInstance Σ)
          (dm : DynamicMutator Γ Γ Unit (Σ ▻ (ς,τ))) (dm_dcl : dmut_dcl dm)
          (sm : Lit τ -> SCMut Γ Γ unit) :
      (forall v, box approximates (env_snoc ι _ v) dm (sm v)) ->
      box approximates ι
        (dmut_fresh (ς,τ) dm)
        (scmut_demonic sm).
    Proof.
      intros HYP. unfold box, approximates.
      intros * <- pc1 s1 POST Hwp Hpc.
      apply scmut_wp_demonic. intros v.
      specialize (HYP v (Σ1 ▻ (ς,τ)) (sub_up1 ζ1) (env_snoc ι1 (ς,τ) v)).
      inster HYP by apply syminstance_rel_up; auto.
      unfold approximates in HYP.
      specialize (HYP (subst sub_wk1 pc1) (subst (sub_wk1) s1) POST).
      rewrite ?inst_subst, ?inst_sub_wk1 in HYP. apply HYP; auto.
      apply dmut_wp_sub_fresh in Hwp; auto.
      - revert Hwp.
        apply dmut_wp_monotonic; cbn.
        unfold stateprop_impl, stateprop_specialize, stateprop_lift.
        intros ? ζ * Hpost ι0 rel10.
        dependent elimination ζ as [@env_snoc Σ0 ζ _ t].
        apply syminstance_rel_snoc in rel10.
        apply Hpost. now rewrite sub_comp_wk1_tail.
      - apply stateprop_lift_dcl.
      - eapply stateprop_lift_vac.
    Qed.

    Lemma dmut_assume_formula_sound {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_assume_formula fml)
        (scmut_assume_formula ι fml).
    Proof.
      unfold box, approximates.
      intros * <- ? ? POST Hwp Hpc.
      unfold dmut_wp, dmut_sub, dmut_assume_formula in Hwp.
      specialize (Hwp Σ1 (sub_id Σ1)).
      rewrite sub_comp_id_right in Hwp.
      unfold scmut_wp, scmut_assume_formula. cbn.
      intros Hfml. rewrite ?subst_sub_id in Hwp.
      destruct (try_solve_formula_spec (subst ζ1 fml)).
      - specialize (H ι1). rewrite inst_subst in H.
        apply H in Hfml. clear H.
        unfold is_true in Hfml. subst a.
        cbn in Hwp.
        rewrite ?sub_comp_id_left in Hwp.
        unfold stateprop_lift in Hwp.
        inster Hwp by apply syminstance_rel_refl.
        now apply Hwp.
      - clear H.
        destruct (dmutres_assume_formula pc (subst ζ1 fml) s__sym) as [Σ2 ζ2 [] s2] eqn:?.
        + cbn in Hwp. rewrite sub_comp_id_left in Hwp.
          assert (resultprop_lift ι1 POST (dmutres_assume_formula pc (subst ζ1 fml) s__sym))
            by (rewrite Heqd; apply Hwp).
          apply dmutres_assume_formula_spec in H; auto using resultprop_lift_dcl.
          unfold resultprop_lift, stateprop_lift in H.
          inster H by apply syminstance_rel_refl. apply H.
          rewrite inst_pathcondition_cons.
          rewrite inst_subst. auto.
        + cbn in Hwp. rewrite sub_comp_id_left in Hwp.
          assert (resultprop_lift ι1 POST (dmutres_assume_formula pc (subst ζ1 fml) s__sym))
            by (rewrite Heqd; apply Hwp).
          apply dmutres_assume_formula_spec in H; auto using resultprop_lift_dcl.
          unfold resultprop_lift, stateprop_lift in H.
          inster H by apply syminstance_rel_refl. apply H.
          rewrite inst_pathcondition_cons.
          rewrite inst_subst. auto.
    Qed.

    Opaque dmut_assume_formula.

    Lemma dmut_produce_sound {Γ Σ} (asn : Assertion Σ) (ι : SymInstance Σ) :
      box approximates
        (Γ1 := Γ) (Γ2 := Γ) ι
        (dmut_produce asn)
        (scmut_produce ι asn).
    Proof.
      induction asn; cbn.
      - apply dmut_assume_formula_sound.
      - apply dmut_produce_chunk_sound.
      - apply approximates_demonic_binary.
        + unfold dmut_assume_term, scmut_assume_term.
          apply dmut_bind_right_sound;
            auto using dmut_assume_formula_dcl, dmut_produce_dcl, dmut_assume_formula_sound.
        + unfold dmut_assume_term, scmut_assume_term.
          apply dmut_bind_right_sound;
            auto using dmut_assume_formula_dcl, dmut_produce_dcl, dmut_assume_formula_sound.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply dmut_bind_right_sound; auto using dmut_produce_dcl.
      - apply dmut_fresh_sound; auto using dmut_produce_dcl.
    Admitted.

    Lemma dmut_exec_sound {Γ Σ σ} (s : Stm Γ σ) (ι : SymInstance Σ) :
      box approximates ι (dmut_exec s) (scmut_exec s).
    Proof. (* induction s; cbn [dmut_exec scmut_exec]. *) Admitted.

    Section Leftovers.

      Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

      Definition interpret_heap {Σ} (ι : SymInstance Σ) (h : SymbolicHeap Σ) : L :=
        List.fold_right (fun c h => ASS.inst_chunk ι c ∧ h) ltrue h.

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

    End Leftovers.

  End DynMutV1Soundness.

End Soundness.
