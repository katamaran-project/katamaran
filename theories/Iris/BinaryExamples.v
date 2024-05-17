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
  Program.Equality.
From Equations Require Import
     Equations Signature.
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     base_logic.lib.fancy_updates
     base_logic.lib.gen_heap
     base_logic.lib.own
     bi.big_op
     bi.interface
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.tactics.

From Katamaran Require Import
     Iris.Model
     Iris.Instance
     Prelude
     Semantics
     Sep.Hoare
     Sep.Logic
     Signature
     SmallStep.Step
     Specification
     BinaryModel
     BinaryWP.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module ExamplesSymmetricBinaryWP (B : Base) (SIG : Signature B) (PROG : Program B)
       (SEM : Semantics B PROG) (IB : IrisBase2 B PROG SEM) (IPred : IrisPredicates2 B SIG PROG SEM IB).
  Import B SIG PROG SEM IB IPred.
  Include IrisBinaryWPSymmetric B SIG PROG SEM IB IPred.
  Include IrisSignatureRules2 B SIG PROG SEM IB IPred.

  Lemma constant_value : forall {τ} (v : Val τ),
      ⊢ semWp2 [env] [env] (stm_val τ v) (stm_val τ v)
          (λ v1 _ v2 _, ⌜v1 = v2⌝).
  Proof. iIntros; by rewrite fixpoint_semWp2_eq. Qed.

  Lemma constant_assignment : forall {τ} (reg : 𝑹𝑬𝑮 τ) (v : Val τ),
      ⊢ (∃ v1 v2, reg_pointsTo2 reg v1 v2) -∗
        semWp2 [env] [env]
          (stm_write_register reg (exp_val τ v))
          (stm_write_register reg (exp_val τ v))
          (λ v1 _ v2 _, reg_pointsTo2 reg v v).
  Proof.
    iIntros (τ reg v) "(%v1 & %v2 & Hptsl & Hptsr)".
    rewrite fixpoint_semWp2_eq.
    cbn.
    iIntros (γ1 γ2 μ1 μ2) "([Hregsl Hregsr] & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstepl & Hlc1 & %Hstepr & Hlc2)".
    destruct (smallinvstep Hstepl), (smallinvstep Hstepr); cbn.
    iFrame "Hmem".
    iIntros "!> !>".
    iModIntro.
    iMod (reg_update _ _ v1 v with "Hregsl Hptsl") as "[Hregsl Hptsl]".
    iMod (reg_update _ _ v2 v with "Hregsr Hptsr") as "[Hregsr Hptsr]".
    iMod "Hclose" as "_".
    iModIntro.
    iFrame "Hregsl Hregsr".
    rewrite fixpoint_semWp2_eq; cbn.
    iModIntro.
    iFrame "Hptsl Hptsr".
  Qed.

  Let N := nroot .@ "reg_public_inv".

  Definition reg_public_inv {τ} (reg : 𝑹𝑬𝑮 τ) : iProp Σ :=
    invariants.inv N (∃ v, reg_pointsTo2 reg v v).

  Lemma constant_assignment_inv : forall {τ} (reg : 𝑹𝑬𝑮 τ) (v : Val τ),
      ⊢ reg_public_inv reg -∗
        semWp2 [env] [env]
          (stm_write_register reg (exp_val τ v))
          (stm_write_register reg (exp_val τ v))
          (λ _ _ _ _, True).
  Proof.
    iIntros (τ reg v) "#Hreg".
    rewrite fixpoint_semWp2_eq; cbn.
    iIntros (γ1 γ2 μ1 μ2) "([Hregsl Hregsr] & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstepl & Hlc1 & %Hstepr & Hlc2)".
    destruct (smallinvstep Hstepl), (smallinvstep Hstepr); cbn.
    iIntros "!> !> !>".
    iMod "Hclose" as "_".
    iInv "Hreg" as "H".
    iMod (lc_fupd_elim_later with "Hlc1 H") as "(%v0 & Hptsl & Hptsr)".
    iMod (reg_update _ _ v0 v with "Hregsl Hptsl") as "[Hregsl Hptsl]".
    iMod (reg_update _ _ v0 v with "Hregsr Hptsr") as "[Hregsr Hptsr]".
    iModIntro.
    iSplitL "Hptsl Hptsr".
    { iModIntro.
      iExists v.
      iFrame "Hptsl Hptsr". }
    iModIntro.
    iFrame "Hregsl Hregsr Hmem".
    by rewrite fixpoint_semWp2_eq.
  Qed.

  Lemma diff_constant_assignment_inv : forall {τ} (reg : 𝑹𝑬𝑮 τ) (v1 v2 : Val τ),
      v1 ≠ v2 ->
      ⊢ reg_public_inv reg -∗
        semWp2 [env] [env]
          (stm_write_register reg (exp_val τ v1))
          (stm_write_register reg (exp_val τ v2))
          (λ _ _ _ _, True).
  Proof.
    iIntros (τ reg v1 v2 Hneq) "Hreg".
    rewrite fixpoint_semWp2_eq; cbn.
    iIntros (γ1 γ2 μ1 μ2) "([Hregsl Hregsr] & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstepl & Hlc1 & %Hstepr & Hlc2)".
    destruct (smallinvstep Hstepl), (smallinvstep Hstepr); cbn.
    iFrame "Hmem".
    iIntros "!> !> !>".
    iMod "Hclose" as "_".
    iInv "Hreg" as "H".
    iMod (lc_fupd_elim_later with "Hlc1 H") as "(%v0 & Hptsl & Hptsr)".
    iMod (reg_update _ _ v0 v1 with "Hregsl Hptsl") as "[Hregsl Hptsl]".
    iMod (reg_update _ _ v0 v2 with "Hregsr Hptsr") as "[Hregsr Hptsr]".
    iModIntro.
    iSplitL "Hptsl Hptsr".
    iModIntro.
    unfold reg_pointsTo2.
    (* We cannot prove that the invariant still holds here (expected). *)
  Abort.
End ExamplesSymmetricBinaryWP.
