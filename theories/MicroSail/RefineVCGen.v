(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Relations.Relation_Definitions
     Lists.List
     NArith.NArith
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Coq Require
     Classes.CRelationClasses.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Bitvector
     Signature
     Refinement.MonadInstances
     MicroSail.RefineExecutor
     MicroSail.ShallowVCGen
     MicroSail.SymbolicVCGen
     Symbolic.Replay
     Specification
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Module Type RefineVCGenOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import CVCG : ShallowVCGen B SIG PROG SPEC)
  (Import SOLV : SolverKit B SIG)
  (Import SVCG : SymbolicVCGen B SIG SOLV PROG SPEC)
  (Import MINST : RefinementMonadInstancesOn B SIG SOLV CVCG SVCG)
  (Import REXEC : RefineExecutorOn B SIG PROG CVCG SVCG).

  Section LRs.
    Import logicalrelation logicalrelation.notations.

    Lemma rexec_call_foreign [Δ τ] (f : 𝑭𝑿 Δ τ) :
      ℛ⟦RNEnv Δ -> RHeapSpec (RVal τ)⟧
        (SVCG.Symbolic.exec_call_foreign f)
        (CVCG.exec_call_foreign Δ τ f).
    Proof.
      unfold SVCG.Symbolic.exec_call_foreign, CVCG.exec_call_foreign.
      intros w0 ι0 Hpc0 sδ cδ rδ. apply refine_call_contract; auto.
    Qed.

    Lemma rexec_lemma [Δ] (lem : 𝑳 Δ) :
      ℛ⟦RNEnv Δ -> RHeapSpec RUnit⟧
        (SVCG.Symbolic.exec_lemma lem)
        (CVCG.exec_lemma Δ lem).
    Proof.
      unfold SVCG.Symbolic.exec_lemma, CVCG.exec_lemma.
      intros w0 ι0 Hpc0 sδ cδ rδ. apply refine_call_lemma; auto.
    Qed.

    Lemma rexec_call n :
      forall [Δ τ] (f : 𝑭 Δ τ),
      ℛ⟦RNEnv Δ -> RHeapSpec (RVal τ)⟧
        (SVCG.Symbolic.exec_call n f)
        (CVCG.exec_call n Δ τ f).
    Proof.
      induction n; intros Δ τ f w0 ι0 Hpc0 sδ cδ rδ;
        cbn [SVCG.Symbolic.exec_call CVCG.exec_call].
      - destruct CEnv.
        + apply refine_call_contract; auto.
        + easy.
      - destruct CEnv.
        + apply refine_call_contract; auto.
        + unfold evalStoreT, evalCStoreT.
          eapply rel_bind; auto with typeclass_instances.
          apply rexec_aux; auto using rexec_call_foreign, rexec_lemma.
          intros w1 θ1 ι1 Heq1 Hpc1 [sv sδ1] [cv cδ1] [rv rδ1].
          apply rel_pure; auto with typeclass_instances.
    Qed.

    Lemma rexec n [Γ τ] (s : Stm Γ τ) :
      ℛ⟦RStoreT Γ Γ (RVal τ)⟧
        (SVCG.Symbolic.exec n s)
        (CVCG.exec n Γ τ s).
    Proof.
      unfold SVCG.Symbolic.exec, CVCG.exec.
      apply rexec_aux; eauto using rexec_call_foreign, rexec_lemma, rexec_call.
    Qed.

    Lemma rvcgen n [Δ τ] (c : SepContract Δ τ) (s : Stm Δ τ) :
      ℛ⟦ℙ⟧
        (SVCG.Symbolic.vcgen n c s)
        (CVCG.shallow_vcgen n c s).
    Proof.
      intros w0 ι0 Hpc0.
      unfold SVCG.Symbolic.vcgen, CVCG.shallow_vcgen.
      apply RHeapSpec.refine_run; auto.
      apply rexec_contract; auto using rexec.
    Qed.

  End LRs.

  Import SymProp.

  Lemma shallow_replay_sound {Σ} (s : 𝕊 Σ) (ι : Valuation Σ) :
    creplay (M := CPureSpec) s ι (fun _ => True) -> safe s ι.
  Proof.
    induction s; cbn; unfold FALSE.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - apply ex_impl_morphism. intros v H. now apply IHs.
    - apply all_impl_morphism. intros v H. now apply IHs.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
  Qed.

  Lemma symbolic_replay_sound {w : World} (s : 𝕊 w) (ι : Valuation w) (Hpc : instprop (wco w) ι) :
    safe (Symbolic.runreplay s) ι -> safe s ι.
  Proof.
    unfold Symbolic.runreplay, SPureSpec.run.
    intros H%safe_debug_safe%wsafe_safe.
    apply shallow_replay_sound. revert H.
    apply (rel_replay (RM := RPureSpec) s Hpc); [|easy].
    cbn. now rewrite inst_sub_id.
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel.
    unfold Shallow.ValidContractWithFuel.
    intros [Hwp].
    apply postprocess_sound in Hwp.
    apply (symbolic_replay_sound (w := wnil)) in Hwp; [|easy].
    apply postprocess_sound, safe_debug_safe, wsafe_safe in Hwp.
    revert Hwp.
    now apply rvcgen.
  Qed.

End RefineVCGenOn.
