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
     Iris.Base
     (* Iris.Instance *)
     Prelude
     Semantics
     Sep.Hoare
     Signature
     SmallStep.Step
     Specification
     BinaryResources
     BinaryWeakestPre
     BinaryAdequacy
.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type IrisInstance2 (B : Base) (SIG : Signature B) (PROG : Program B)
  (SEM : Semantics B PROG) (IB2 : IrisBase2 B PROG SEM) (IAP : IrisAdeqParameters2 B PROG SEM IB2 IB2 IB2) :=
  IrisPredicates2 B SIG PROG SEM IB2 <+ IrisSignatureRules2 B SIG PROG SEM IB2
    <+ IrisAdequacy2 B SIG PROG SEM IB2 IAP.

(*  * The following module defines the parts of the Iris model that must depend on the Specification, not just on the Signature. *)
(*  * This is kept to a minimum (see comment for the IrisPredicates module). *)
(*  *)
Module IrisInstanceWithContracts2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import SPEC  : Specification B SIG PROG)
  (Import IB2   : IrisBase2 B PROG SEM)
  (Import IAP   : IrisAdeqParameters2 B PROG SEM IB2 IB2 IB2)
  (Import II    : IrisInstance2 B SIG PROG SEM IB2 IAP)
  (Import PLOG  : ProgramLogicOn B SIG PROG SPEC).

  Section WithSailGS.
  Import ProgramLogic.
  Context `{sG : sailGS2 Σ}.

  Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
    (∀ σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | Some c => ValidContractSem (FunDef f) c
      | None => True
      end)%I.

  Definition ForeignSem :=
    ∀ (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ),
      ValidContractForeign (CEnvEx f) f.

  Definition LemmaSem : Prop :=
    forall (Δ : PCtx) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Lemma iris_rule_stm_call {Γ} (δ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ)
    (Q : Val σ -> CStore Γ -> iProp Σ) :
    CEnv f = Some c ->
    CTriple P c (evals es δ) (fun v => Q v δ) ->
    ⊢ ▷ ValidContractEnvSem CEnv -∗
       semTriple δ P (stm_call f es) Q.
  Proof.
    iIntros (ceq ctrip) "cenv P".
    iApply semWP2_call_inline_later.
    iModIntro.
    iSpecialize ("cenv" $! _ _ f).
    rewrite ceq. clear ceq.
    destruct c as [Σe δΔ req res ens]; cbn in *.
    iPoseProof (ctrip with "P") as (ι Heq) "[req consr]". clear ctrip.
    iPoseProof ("cenv" $! ι with "req") as "wpf0". rewrite Heq.
    iApply (semWP2_mono with "wpf0").
    iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
    repeat iSplitR; auto.
    by iApply "consr".
  Qed.

  Lemma iris_rule_stm_call_frame {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗
           semTriple δ P (stm_call_frame δΔ s) Q).
  Proof.
    iIntros "trips P".
    iSpecialize ("trips" with "P").
    iApply semWP2_call_frame.
    iApply (semWP2_mono with "trips").
    iIntros ([] ? ? ?) "(<- & <- & $)"; auto.
  Qed.

  Lemma iris_rule_stm_foreign
    {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ForeignSem ->
    CTriple P (CEnvEx f) (evals es δ) (λ v : Val τ, Q v δ) ->
    ⊢ semTriple δ P (stm_foreign f es) Q.
  Proof.
    iIntros (forSem ctrip) "P".
    specialize (forSem Δ τ f Γ es δ).
    destruct CEnvEx as [Σe δΔ req res ens]; cbn in *.
    iPoseProof (ctrip with "P") as "[%ι [%Heq [req consr]]]". clear ctrip.
    iPoseProof (forSem ι Heq with "req") as "WPf". clear forSem.
    iApply (semWP2_mono with "WPf").
    iIntros ([v|m] δΓ' ? ?) "(<- & <- & H)"; auto.
    repeat iSplitR; auto.
    iDestruct "H" as "(H & <-)".
    by iApply "consr".
  Qed.

  Lemma iris_rule_stm_lemmak
    {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
    (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
    LemmaSem ->
    LTriple (evals es δ) P Q (LEnv l) ->
    ⊢ semTriple δ Q k R -∗
      semTriple δ P (stm_lemmak l es k) R.
  Proof.
    iIntros (lemSem ltrip) "tripk P". iApply semWP2_lemmak. iApply "tripk".
    specialize (lemSem _ l). remember (LEnv l) as contractL.
    clear - lemSem ltrip.
    destruct ltrip as [Ψ' pats req ens ent]; cbn in lemSem.
    iPoseProof (ent with "P") as (ι Heq) "[req consr]".
    iApply "consr". by iApply lemSem.
  Qed.

  Lemma sound_stm
    {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
    forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ),
      ForeignSem ->
      LemmaSem ->
      ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ ->
      ⊢ (□ ▷ ValidContractEnvSem CEnv -∗
        semTriple δ PRE s POST)%I.
  Proof.
    iIntros (PRE POST extSem lemSem triple) "#vcenv".
    iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips".
    - by iApply iris_rule_consequence.
    - by iApply iris_rule_frame.
    - by iApply iris_rule_pull.
    - by iApply iris_rule_exist.
    - iApply iris_rule_stm_val.
      by iApply H.
    - iApply iris_rule_stm_exp.
      by iApply H.
    - by iApply iris_rule_stm_let.
    - by iApply iris_rule_stm_block.
    - by iApply iris_rule_stm_seq.
    - iApply iris_rule_stm_assertk.
      iIntros "H". by iApply "trips".
    - by iApply iris_rule_stm_fail.
    - by iApply iris_rule_stm_read_register.
    - by iApply iris_rule_stm_write_register.
    - by iApply iris_rule_stm_assign.
    - by iApply iris_rule_stm_call.
    - by iApply iris_rule_stm_call_inline.
    - by iApply iris_rule_stm_call_frame.
    - by iApply iris_rule_stm_foreign.
    - by iApply iris_rule_stm_lemmak.
    - by iApply iris_rule_stm_bind.
    - by iApply iris_rule_stm_debugk.
    - by iApply iris_rule_stm_pattern_match.
  Qed.

  Lemma sound :
    ForeignSem -> LemmaSem -> ValidContractCEnv ->
    ⊢ ValidContractEnvSem CEnv.
  Proof.
    intros extSem lemSem vcenv.
    iLöb as "IH".
    iIntros (σs σ f).
    specialize (vcenv σs σ f).
    destruct (CEnv f) as [[]|];[|trivial].
    iIntros (ι).
    specialize (vcenv _ eq_refl ι).
    iApply (sound_stm extSem lemSem); [|trivial].
    apply vcenv.
  Qed.

  End WithSailGS.
End IrisInstanceWithContracts2.
