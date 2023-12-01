(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
  Program.Basics
  Program.Tactics
  ZArith.ZArith
  Strings.String
  Classes.Morphisms
  Classes.RelationClasses
  Classes.Morphisms_Prop
  Classes.Morphisms_Relations.

From Coq Require Lists.List.

From Equations Require Import
  Equations.

From Katamaran Require Import
  Signature
  MicroSail.ShallowExecutor
  MicroSail.SymbolicExecutor
  Program
  Tactics.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Soundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SHAL : ShallowExecOn B SIG PROG)
  (Import SYMB : SymbolicExecOn B SIG PROG).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation.
  Import logicalrelation.notations.

  Section Exec.

    Context {MT M} {spureMT : SPureSpecM MT} {cpureM : CPureSpecM M}.
    Context {sheapM : SHeapSpecM MT} {cheapM : CHeapSpecM M}.
    Context {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}.
    Context {rpureM : RPureSpecM RM} {rheapM : RHeapSpecM RM}.

    #[export] Instance RStoreT Γ1 Γ2 {AT A} (RA : Rel AT A) :
      Rel (SStoreT MT Γ1 Γ2 AT) (CStoreT M Γ1 Γ2 A) :=
      RInst _ _ -> RM (RProd RA (RInst _ _)).

    Lemma rliftM {Γ} `{RA : Rel AT A} :
      ℛ⟦RM RA -> RStoreT Γ Γ RA⟧ SYMB.liftM SHAL.liftM.
    Proof.
      unfold SYMB.liftM, SHAL.liftM.
      intros w0 ι0 Hpc0 sm cm rm sδ cδ rδ.
      eapply rel_bind; auto.
      intros w1 θ1 ι1 Heq1 Hpc1 sa ca ra.
      apply rel_pure; auto.
      constructor; auto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma rpure {Γ} `{RA : Rel AT A} :
      ℛ⟦RA -> RStoreT Γ Γ RA⟧ SYMB.pure SHAL.pure.
    Proof.
      unfold SYMB.pure, SHAL.pure.
      intros w0 ι0 Hpc0 sa ca ra.
      apply rliftM; auto.
      apply rel_pure; auto.
    Qed.

    Context (sexec_call_foreign : SYMB.ExecCallForeign MT).
    Context (sexec_lemma : SYMB.ExecLemma MT).
    Context (sexec_call : SYMB.ExecCall MT).

    Context (cexec_call_foreign : SHAL.ExecCallForeign M).
    Context (cexec_lemma : SHAL.ExecLemma M).
    Context (cexec_call : SHAL.ExecCall M).

    Context (rexec_call_foreign : forall [Δ τ] (f : 𝑭𝑿 Δ τ),
               ℛ⟦RNEnv Δ -> RM (RVal τ)⟧
                 (sexec_call_foreign f)
                 (cexec_call_foreign f)).
    Context (rexec_call_lemma : forall [Δ] (lem : 𝑳 Δ),
               ℛ⟦RNEnv Δ -> RM (RUnit)⟧
                 (sexec_lemma lem)
                 (cexec_lemma lem)).

    Lemma rexec_aux [Γ τ] (s : Stm Γ τ) :
      ℛ⟦RStoreT Γ Γ (RVal τ)⟧
        (SYMB.exec_aux sexec_call_foreign sexec_lemma sexec_call s)
        (SHAL.exec_aux cexec_call_foreign cexec_lemma cexec_call s).
    Proof.
      induction s; cbn [SYMB.exec_aux SHAL.exec_aux]; intros w0 ι0 Hpc0.
      - apply rpure; auto. easy.
      - admit.
    Admitted.


    (* Lemma refine_exec_aux {cfg} srec crec (HYP : ExecRefine srec crec) : *)
    (*   ExecRefine (@SStoreSpec.exec_aux cfg srec) (@CHeapSpecM.exec_aux crec). *)
    (* Proof. *)
    (*   unfold ExecRefine. *)
    (*   induction s; cbn; intros * w0 ι0 Hpc0. *)
    (*   - apply refine_pure; auto. reflexivity. *)
    (*   - now apply refine_eval_exp. *)
    (*   - apply refine_bind; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros t v Htv. *)
    (*     apply refine_pushpop; auto. *)
    (*   - apply refine_pushspops; auto. *)
    (*     apply refine_lift. *)
    (*   - apply refine_bind; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros t v ->. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_assign; auto. *)
    (*     reflexivity. *)
    (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
    (*     apply refine_pure; auto. *)
    (*     hnf in H. now rewrite <- inst_persist in H. *)
    (*   - apply refine_bind; auto. *)
    (*     apply refine_eval_exps; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros args__s args__c Hargs. *)
    (*     destruct (CEnv f). *)
    (*     + unfold SStoreSpec.call_contract_debug. *)
    (*       destruct (config_debug_function cfg f). *)
    (*       apply refine_debug; auto. *)
    (*       apply refine_call_contract; auto. *)
    (*       apply refine_call_contract; auto. *)
    (*     + intros POST__s POST__c HPOST. *)
    (*       intros δs1 δc1 ->. *)
    (*       apply HYP; auto. *)
    (*       intros w2 ω12 ι2 -> Hpc2. *)
    (*       intros t v ->. *)
    (*       intros _ _ _. *)
    (*       apply HPOST; auto. *)
    (*       reflexivity. *)
    (*       rewrite <- inst_persist. *)
    (*       reflexivity. *)
    (*   - apply refine_bind; auto. *)
    (*     apply refine_get_local; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros δs1 δc1 ->. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_put_local; auto. *)
    (*     apply refine_lift. *)
    (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
    (*     apply refine_bind; auto. *)
    (*     intros w3 ω23 ι3 -> Hpc3. *)
    (*     intros t v ->. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_put_local; auto. *)
    (*     rewrite persist_subst. *)
    (*     hnf. rewrite sub_acc_trans, ?inst_subst; auto. *)
    (*     intros w4 ω34 ι4 -> Hpc4 _ _ _. *)
    (*     apply refine_pure; auto. *)
    (*     eapply refine_inst_persist; eauto. *)
    (*     reflexivity. *)
    (*   - apply refine_bind; auto. *)
    (*     apply refine_eval_exps; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros args__s args__c Hargs. *)
    (*     apply refine_call_contract; auto. *)
    (*   - apply refine_bind; auto. *)
    (*     apply refine_eval_exps; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1 δΔ ? ?. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_call_lemma; auto. *)
    (*     intros w2 ω12 ι2 -> Hpc2 _ _ _; auto. *)
    (*   - apply refine_bind; auto. *)
    (*     intros ? ? ? -> ? _ _ _; auto. *)
    (*   - apply refine_bind; auto. *)
    (*     apply (refine_eval_exp e1); auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros t v ->. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_assume_formula; auto. *)
    (*     cbn. reflexivity. *)
    (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
    (*     now apply IHs. *)
    (*   - apply refine_block; auto. *)
    (*   - apply refine_bind; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros t v Htv. *)
    (*     apply refine_demonic_pattern_match; auto. *)
    (*     intros pc w2 r12 ι2 -> Hpc2. *)
    (*     intros ts vs Htvs. *)
    (*     apply refine_pushspops; auto. *)
    (*     apply H; auto. *)
    (*   - apply refine_bind; auto. *)
    (*     apply refine_angelic; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1 t v Htv. hnf in Htv; subst. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_consume_chunk; auto. *)
    (*     cbn. reflexivity. *)
    (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_produce_chunk; auto. *)
    (*     rewrite <- inst_persist; auto. *)
    (*     cbn. reflexivity. *)
    (*     intros w3 ω23 ι3 -> Hpc3 _ _ _. *)
    (*     apply refine_pure; auto. *)
    (*     rewrite (persist_trans (A := STerm _)). *)
    (*     now rewrite <- ?inst_persist. *)
    (*   - apply refine_bind; auto. *)
    (*     apply refine_angelic; auto. *)
    (*     intros w1 ω01 ι1 -> Hpc1. *)
    (*     intros told v ->. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_consume_chunk; auto. *)
    (*     cbn. reflexivity. *)
    (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
    (*     apply refine_bind; auto. *)
    (*     apply (refine_eval_exp e); auto. *)
    (*     intros w3 ω23 ι3 -> Hpc3. *)
    (*     intros tnew v Htnew. hnf in Htnew. subst v. *)
    (*     apply refine_bind; auto. *)
    (*     apply refine_produce_chunk; auto. *)
    (*     cbn. reflexivity. *)
    (*     intros w4 ω34 ι4 -> Hpc4 _ _ _. *)
    (*     apply refine_pure; auto. *)
    (*     now rewrite <- inst_persist. *)
    (*   - apply refine_error; auto. *)
    (*   - apply refine_debug; auto. *)
    (* Qed. *)

    (* Lemma refine_exec {cfg n} : *)
    (*   ExecRefine (@SStoreSpec.exec cfg n) (@CHeapSpecM.exec n). *)
    (* Proof. *)
    (*   induction n; cbn. *)
    (*   - unfold ExecRefine. intros Γ τ s w ι Hpc. *)
    (*     apply refine_error; auto. *)
    (*   - now apply refine_exec_aux. *)
    (* Qed. *)

    (* Lemma refine_exec_contract {cfg : Config} n {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) : *)
    (*   let w0 := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |} in *)
    (*   forall (ι0 : Valuation w0), *)
    (*   ℛ⟦RStoreSpec Γ Γ RUnit⟧@{ι0} *)
    (*     (SStoreSpec.exec_contract cfg n c s) (CHeapSpecM.exec_contract n c s ι0). *)
    (* Proof. *)
    (*   unfold SStoreSpec.exec_contract, CHeapSpecM.exec_contract; *)
    (*                                    destruct c as [Σ δ pre result post]; cbn - [RSat] in *. *)
    (*   intros ι0. *)
    (*   apply refine_bind. *)
    (*   apply refine_produce; wsimpl; cbn; auto. *)
    (*   intros w1 ω01 ι1 -> Hpc1 _ _ _. *)
    (*   apply refine_bind; auto. *)
    (*   apply refine_exec; auto. *)
    (*   intros w2 ω12 ι2 -> Hpc2. *)
    (*   intros res__s res__c Hres. *)
    (*   apply refine_consume; cbn - [inst]; wsimpl; auto. *)
    (*   f_equal; auto. *)
    (* Qed. *)

    (* Lemma refine_demonic_close {w : World} (P : 𝕊 w) (p : Valuation w -> Prop) : *)
    (*   (forall (ι : Valuation w), ℛ⟦_⟧@{ι} P (p ι)) -> *)
    (*   RSat RProp (w := wnil) env.nil (demonic_close P) (ForallNamed p). *)
    (* Proof. *)
    (*   intros HYP Hwp. unfold ForallNamed. *)
    (*   rewrite env.Forall_forall. intros ι. *)
    (*   apply HYP. revert Hwp. clear. *)
    (*   rewrite ?wsafe_safe, ?safe_debug_safe. *)
    (*   intros Hwp. now apply safe_demonic_close. *)
    (* Qed. *)

    (* Lemma refine_vcgen {Γ τ} n (c : SepContract Γ τ) (body : Stm Γ τ) : *)
    (*   RSat RProp (w := wnil) env.nil (SStoreSpec.vcgen default_config n c body) (CHeapSpecM.vcgen n c body). *)
    (* Proof. *)
    (*   unfold SStoreSpec.vcgen, CHeapSpecM.vcgen. *)
    (*   apply (refine_demonic_close *)
    (*            (w := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |})). *)
    (*   intros ι. *)
    (*   apply refine_exec_contract; auto. *)
    (*   now intros w1 ω01 ι1 -> Hpc1. *)
    (*   reflexivity. *)
    (*   reflexivity. *)
    (* Qed. *)


    (* Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) : *)
    (*   Symbolic.ValidContract c body -> *)
    (*   Shallow.ValidContract c body. *)
    (* Proof. *)
    (*   unfold Symbolic.ValidContract. intros [Hwp%postprocess_sound]. *)
    (*   apply replay_sound_nil in Hwp. apply postprocess_sound in Hwp. *)
    (*   apply refine_vcgen. now rewrite wsafe_safe, safe_debug_safe. *)
    (* Qed. *)

    (* Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) : *)
    (*   Symbolic.ValidContractWithFuel fuel c body -> *)
    (*   Shallow.ValidContractWithFuel fuel c body. *)
    (* Proof. *)
    (*   unfold Symbolic.ValidContractWithFuel. intros [Hwp%postprocess_sound]. *)
    (*   apply replay_sound_nil in Hwp. apply postprocess_sound in Hwp. *)
    (*   apply refine_vcgen. now rewrite wsafe_safe, safe_debug_safe. *)
    (* Qed. *)

  End Exec.

End Soundness.

Module MakeSymbolicSoundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SHAL : ShallowExecOn B SIG PROG)
  (Import SYMB : SymbolicExecOn B SIG PROG).

  Include Soundness B SIG PROG SHAL SYMB.
End MakeSymbolicSoundness.
