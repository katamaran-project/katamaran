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
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Signature
     Sep.Hoare
     Sep.Logic
     Specification
     Prelude
     Program
     Shallow.Executor.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Type Soundness
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import EXEC : ShallowExecOn B SIG PROG SPEC)
  (Import HOAR : ProgramLogicOn B SIG PROG SPEC).

  Import CStoreSpec.
  Import ProgramLogic.

  Section Soundness.

    Import iris.proofmode.tactics.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    (* liftP converts the "proof theoretic" predicates (CStore Γ -> L), with L
       being a type of separation logic propositions, to the "model theoretic"
       heap predicates (CStore Γ -> SCHeap -> Prop) that are used as the type of
       postconditions in the shallow executor. *)
    Definition liftP {Γ} (POST : CStore Γ -> L) : CStore Γ -> SCHeap -> Prop :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Lemma call_contract_sound {Δ τ} (c : SepContract Δ τ) (args : CStore Δ)
      (Φ : Val τ → SCHeap → Prop) (h1 : SCHeap) :
      CHeapSpec.call_contract c args Φ h1 →
      CTriple (interpret_scheap h1) c args
        (fun v => ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v h'⌝)%I.
    Proof.
      destruct c as [Σe δe req result ens]. cbn.
      cbv [CHeapSpec.call_contract CHeapSpec.bind CHeapSpec.lift_purespec
           CHeapSpec.demonic CPureSpec.demonic].
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      rewrite CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls ->%CHeapSpec.consume_sound].
      apply bi.exist_intro' with ι.
      apply bi.and_intro; auto.
      apply bi.sep_mono'; auto.
      apply bi.exist_elim. intros h'.
      apply bi.pure_elim_r.
      intros Hwp. apply bi.forall_intro; intro v.
      specialize (Hwp v). now apply CHeapSpec.produce_sound in Hwp.
    Qed.

    Lemma call_lemma_sound [Δ] (l : Lemma Δ) (δ : CStore Δ)
      (Φ : () → SCHeap → Prop) (h : SCHeap)   :
      CHeapSpec.call_lemma l δ Φ h →
      LTriple δ (interpret_scheap h) (∃ h', interpret_scheap h' ∧ ⌜Φ tt h'⌝) l.
    Proof.
      destruct l as [Σe δe req ens].
      unfold CHeapSpec.call_lemma.
      unfold CHeapSpec.bind, CHeapSpec.lift_purespec.
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      rewrite CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls Hwp%CHeapSpec.consume_sound].
      constructor.
      apply bi.exist_intro' with ι.
      apply bi.and_intro; auto.
      rewrite Hwp. clear Hwp.
      apply bi.sep_mono'; auto.
      apply bi.exist_elim. intros h'.
      apply bi.pure_elim_r.
      apply CHeapSpec.produce_sound.
    Qed.

    Definition SoundExec (exec : Exec) :=
      forall
        Γ σ (s : Stm Γ σ) (Φ : Val σ → CStore Γ → SCHeap → Prop)
        (δ1 : CStore Γ) (h1 : SCHeap),
        exec _ _ s Φ δ1 h1 ->
        ⦃ interpret_scheap h1 ⦄
          s ; δ1
        ⦃ fun v δ' =>
            ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ v δ' h'⌝
        ⦄.

    Lemma exec_aux_sound rec (rec_mono : MonotonicExec rec) (rec_sound : SoundExec rec) :
      SoundExec (exec_aux rec).
    Proof.
      unfold SoundExec. intros ? ? s.
      induction s; intros ? ? ?; cbn;
        cbv [pure pushspops pushpop
             eval_exp get_local put_local
             bind];
        cbn; intros HYP.

      - (* stm_val *)
        apply rule_stm_val.
        apply bi.exist_intro' with h1.
        apply bi.and_intro.
        reflexivity.
        apply bi.pure_intro.
        auto.

      - (* stm_exp *)
        apply rule_stm_exp.
        apply bi.exist_intro' with h1.
        apply bi.and_intro.
        reflexivity.
        apply bi.pure_intro.
        auto.

      - (* stm_let *)
        eapply rule_stm_let.
        apply IHs1, HYP. clear IHs1 HYP.
        intros v1 δ2.
        apply rule_exist. intros h.
        apply rule_pull. intros HYP.
        now apply IHs2.

      - (* stm_block *)
        now apply rule_stm_block, IHs.

      - (* stm_assign *)
        now apply rule_stm_assign, IHs.

      - (* stm_call *)
        destruct (CEnv f) as [c|] eqn:Heq; cbn in HYP.
        + apply rule_stm_call with c.
          assumption.
          now apply call_contract_sound.
        + now apply rule_stm_call_inline, rec_sound.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_foreign *)
        apply rule_stm_foreign.
        now apply call_contract_sound.

      - (* stm_lemmak *)
        eapply rule_stm_lemmak.
        apply (call_lemma_sound _ _ _ _ HYP). clear HYP.
        apply rule_exist. intros h.
        apply rule_pull. intros HYP.
        now apply IHs.

      - (* stm_seq *)
        eapply rule_stm_seq.
        apply IHs1, HYP. clear IHs1 HYP.
        intros v1 δ2.
        apply rule_exist. intros h.
        apply rule_pull. intros HYP.
        now apply IHs2.

      - (* stm_assert *)
        apply rule_stm_assert; intro Heval.
        now apply IHs, HYP.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply bi.True_intro.

      - (* stm_match_newpattern *)
        eapply rule_stm_pattern_match.
        apply IHs, HYP. clear IHs HYP.
        intros pc δpc δΓ'. cbn.
        apply rule_exist. intros h.
        apply rule_pull. intros HYP.
        apply wp_demonic_pattern_match in HYP.
        rewrite pattern_match_val_inverse_right in HYP.
        now apply H.

      - (* stm_read_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_read_register_backwards (v := v)).
        apply CPureSpec.wp_consume_chunk in HYP.
        rewrite HYP. clear HYP. cbn.
        apply bi.sep_mono'. easy.
        apply bi.exist_elim. intros h2.
        apply bi.pure_elim_r.
        now intros ->%CPureSpec.wp_produce_chunk.

      - (* stm_write_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        apply CPureSpec.wp_consume_chunk in HYP.
        rewrite HYP. clear HYP. cbn.
        apply bi.sep_mono'. easy.
        apply bi.exist_elim. intros h2.
        apply bi.pure_elim_r.
        now intros ->%CPureSpec.wp_produce_chunk.

      - (* stm_bind *)
        eapply rule_stm_bind.
        apply IHs, HYP. clear IHs HYP.
        intros v1 δ2. cbn.
        apply rule_exist. intros h.
        apply rule_pull. intros HYP.
        now apply H.

      - (* stm_debug *)
        constructor. auto.
    Qed.

    Lemma exec_sound n : SoundExec (@exec n).
    Proof.
      induction n; cbn.
      - unfold SoundExec; cbn; contradiction.
      - apply exec_aux_sound; auto using mon_exec.
    Qed.

    Lemma vcgen_sound n {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      CStoreSpec.vcgen n c body ->
      ProgramLogic.ValidContract c body.
    Proof.
      unfold CStoreSpec.vcgen, ProgramLogic.ValidContract.
      unfold inst_contract_localstore.
      unfold exec_contract, bind.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      hnf in HYP.
      rewrite CPureSpec.wp_demonic_ctx in HYP.
      specialize (HYP ι). remember (inst δΣ ι) as δ.
      apply CHeapSpec.produce_sound, wand_sep_adjoint in HYP. cbn in HYP.
      rewrite bi.emp_sep in HYP.
      refine (rule_consequence_left _ _ HYP). clear HYP.
      apply rule_exist. intros h1.
      apply rule_pull. intros HΦ%exec_sound.
      apply (rule_consequence_right _ HΦ). clear HΦ. intros.
      apply bi.exist_elim. intros h2.
      apply bi.pure_elim_r. intros Hheap%CHeapSpec.consume_sound.
      rewrite Hheap.
      apply bi.sep_elim_l; auto with typeclass_instances.
    Qed.

    Lemma shallow_vcgen_soundness {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContract c body ->
      ProgramLogic.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    Lemma shallow_vcgen_fuel_soundness {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContractWithFuel fuel c body ->
      ProgramLogic.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    (* Print Assumptions shallow_vcgen_soundnes. *)

  End Soundness.

End Soundness.

Module MakeShallowSoundness
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import EXEC : ShallowExecOn B SIG PROG SPEC)
  (Import HOAR : ProgramLogicOn B SIG PROG SPEC).

  Include Soundness B SIG PROG SPEC EXEC HOAR.

End MakeShallowSoundness.
