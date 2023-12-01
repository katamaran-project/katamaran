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
Require Import
  Equations.Prop.Classes
  Equations.Prop.Equations.
From Katamaran Require Import
  Signature
  Sep.Hoare
  Sep.Logic
  Specification
  Prelude
  Program
  Shallow.MonadInterface
  Shallow.MonadInstances
  MicroSail.ShallowExecutor
  MicroSail.ShallowVCGen.

#[local] Set Equations With UIP.
#[local] Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Type VCGenSoundnessOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import SHAL : ShallowVCGen B SIG PROG SPEC)
  (Import HOAR : ProgramLogicOn B SIG PROG SPEC).

  Import ProgramLogic.

  Section WithBI.

    Import iris.bi.interface.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    Definition SExecCall (exec_call : ExecCall CHeapSpec) : Prop :=
      forall Γ Δ τ (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
             (Φ : Val τ → CStore Γ → L) (δ1 : CStore Γ) (h1 : SCHeap),
        exec_call _ _ f (evals es δ1)
          (fun v h2 => interpret_scheap h2 ⊢ Φ v δ1) h1 ->
        ⦃ interpret_scheap h1 ⦄ stm_call f es; δ1 ⦃ Φ ⦄.

    Definition SExecCallForeign (exec_call_foreign : ExecCallForeign CHeapSpec) : Prop :=
      forall Δ τ (f : 𝑭𝑿 Δ τ) (args : CStore Δ) (Φ : Val τ → L) (h1 : SCHeap),
        exec_call_foreign _ _ f args
          (fun v h2 => interpret_scheap h2 ⊢ Φ v) h1 ->
        CTriple (interpret_scheap h1) (CEnvEx f) args Φ.

    Definition SExecLemma (exec_lemma : ExecLemma CHeapSpec) : Prop :=
      forall Δ (lem : 𝑳 Δ) (args : CStore Δ) (Φ : L) (h : SCHeap),
        exec_lemma _ lem args (fun _ h' => interpret_scheap h' ⊢ Φ) h ->
        LTriple args (interpret_scheap h) Φ (LEnv lem).

    Definition SExec (rec : Exec CHeapSpec) : Prop :=
      forall
        Γ σ (s : Stm Γ σ) (Φ : Val σ -> CStore Γ -> L)
        (δ1 : CStore Γ) (h1 : SCHeap),
        rec Γ σ s δ1 (fun '(v,δ2) h2 => interpret_scheap h2 ⊢ Φ v δ2) h1 ->
        ⦃ interpret_scheap h1 ⦄ s ; δ1 ⦃ Φ ⦄.

    Section ExecAux.

      Context (exec_call_foreign : ExecCallForeign CHeapSpec)
        (exec_lemma : ExecLemma CHeapSpec)
        (exec_call : ExecCall CHeapSpec)
        (mexec_call_foreign : MonotonicExecCallForeign exec_call_foreign)
        (mexec_lemma : MonotonicExecLemma exec_lemma)
        (mexec_call : MonotonicExecCall exec_call)
        (sexec_call : SExecCall exec_call)
        (sexec_call_foreign : SExecCallForeign exec_call_foreign)
        (sexec_lemma : SExecLemma exec_lemma).

      Lemma sexec_aux :
        SExec (exec_aux exec_call_foreign exec_lemma exec_call).
      Proof.
        generalize (mon_exec_aux mexec_call_foreign mexec_lemma mexec_call).
        set (exec := exec_aux exec_call_foreign exec_lemma exec_call).
        intros mexec. unfold SExec. intros ? ? s.
        induction s; intros Φ ? ?; cbn; intros HYP.

        - (* stm_val *)
          now apply rule_stm_val.

        - (* stm_exp *)
          now apply rule_stm_exp.

        - (* stm_let *)
          eapply rule_consequence_left.
          eapply rule_stm_let; intros; apply rule_wp.
          apply bi.exist_intro' with (interpret_scheap h1).
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          apply IHs1; clear IHs1.
          revert HYP.
          apply mexec. reflexivity.
          intros [? ?] [v1 δ2] [Heq1 Heq2] h2 HYP.
          cbn in Heq1, Heq2. subst.
          apply bi.exist_intro' with (interpret_scheap h2).
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          apply IHs2.
          revert HYP. cbn.
          apply mexec. reflexivity.
          intros [? ?] [v2 δ3] [Heq1 Heq2] h3.
          cbn in Heq1, Heq2. now subst.

        - (* stm_block *)
          apply rule_stm_block, IHs.
          revert HYP. apply mexec. reflexivity.
          intros [? ?] [v2 δ3] [Heq1 Heq2] h3.
          cbn in Heq1, Heq2. now subst.

        - (* stm_assign *)
          apply rule_stm_assign, IHs.
          revert HYP. apply mexec. reflexivity.
          intros [? ?] [v2 δ3] [Heq1 Heq2] h3.
          cbn in Heq1, Heq2. now subst.

        - (* stm_call *)
          now apply sexec_call.

        - (* stm_call_frame *)
          apply rule_stm_call_frame, IHs.
          revert HYP. apply mexec. reflexivity.
          intros [? ?] [v2 δ3] [Heq1 Heq2] h3.
          cbn in Heq1, Heq2. now subst.

        - (* stm_foreign *)
          apply rule_stm_foreign.
          now apply sexec_call_foreign.

        - (* stm_lemmak *)
          eapply rule_stm_lemmak.
          2: apply rule_wp.
          eapply sexec_lemma. revert HYP.
          apply mexec_lemma. intros ? ? <- h2 HYP.
          apply bi.exist_intro' with (interpret_scheap h2).
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          now apply IHs.

        - (* stm_seq *)
          apply rule_stm_seq with (WP s2 Φ).
          + apply IHs1. revert HYP.
            apply mexec; auto.
            intros [? ?] [v1 δ2] [Heq1 Heq2] h2 HYP.
            cbn in Heq1, Heq2. subst.
            apply bi.exist_intro' with (interpret_scheap h2).
            apply bi.and_intro. reflexivity.
            apply bi.pure_intro. now apply IHs2.
          + apply rule_wp.

        - (* stm_assert *)
          apply rule_stm_assert; intro Heval.
          now apply IHs, HYP.

        - (* stm_fail *)
          eapply rule_consequence_left.
          apply rule_stm_fail.
          apply bi.True_intro.

        - (* stm_pattern_match *)
          apply
            (rule_consequence_left
               (WP s
                  (fun (vσ : Val σ) (δ2 : CStore Γ) =>
                     let 'existT pc δpc := pattern_match_val pat vσ in
                     WP (rhs pc)
                       (fun vτ δ3  => Φ vτ (env.drop (PatternCaseCtx pc) δ3))
                       (δ2 ►► δpc))
                  δ1)).
          + eapply rule_stm_pattern_match.
            apply rule_wp. intros.
            eapply rule_consequence_left.
            apply rule_wp.
            now rewrite pattern_match_val_inverse_right.
          + apply bi.exist_intro' with (interpret_scheap h1).
            apply bi.and_intro.
            reflexivity.
            apply bi.pure_intro.
            apply IHs; clear IHs.
            revert HYP.
            apply mexec; auto.
            intros [? ?] [v1 δ2] [Heq1 Heq2] h2 HYP.
            cbn in Heq1, Heq2. subst. cbn in HYP.
            rewrite CPureSpec.wp_demonic_pattern_match in HYP.
            destruct pattern_match_val. cbn in HYP.
            apply bi.exist_intro' with (interpret_scheap h2).
            apply bi.and_intro.
            reflexivity.
            apply bi.pure_intro.
            apply H. revert HYP.
            apply mexec. reflexivity.
            intros [? ?] [v2 δ3] [Heq1 Heq2] h3; cbn.
            cbn in Heq1, Heq2. now subst.

        - (* stm_read_register *)
          destruct HYP as [v HΦ%CHeapSpec.wp_consume_chunk].
          eapply rule_consequence_left.
          apply (rule_stm_read_register_backwards (v := v)).
          rewrite HΦ; clear HΦ.
          apply bi.sep_mono'; [easy|].
          apply bi.exist_elim. intros h2.
          apply bi.pure_elim_r.
          intros ->%CHeapSpec.wp_produce_chunk.
          apply bi.wand_mono'. reflexivity.
          apply bi.exist_elim. intros h3.
          now apply bi.pure_elim_r.

        - (* stm_write_register *)
          destruct HYP as [v HΦ%CHeapSpec.wp_consume_chunk].
          eapply rule_consequence_left.
          apply (rule_stm_write_register_backwards (v := v)).
          rewrite HΦ; clear HΦ.
          apply bi.sep_mono'; [easy|].
          apply bi.exist_elim. intros h2.
          apply bi.pure_elim_r.
          intros ->%CHeapSpec.wp_produce_chunk.
          apply bi.wand_mono'. reflexivity.
          apply bi.exist_elim. intros h3.
          now apply bi.pure_elim_r.

        - (* stm_bind *)
          eapply rule_consequence_left.
          eapply rule_stm_bind; intros; apply rule_wp.

          apply bi.exist_intro' with (interpret_scheap h1).
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          apply IHs; clear IHs.
          revert HYP. apply mexec; auto.
          intros [? ?] [v2 δ2] [Heq1 Heq2] h2 HYP.
          cbn in Heq1, Heq2. subst.
          apply bi.exist_intro' with (interpret_scheap h2).
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
          now apply H.
        - constructor. auto.
      Qed.

    End ExecAux.

    Section VCGen.

      Lemma call_contract_sound {Δ τ} (c : SepContract Δ τ) (args : CStore Δ)
        (h : SCHeap) (Φ : Val τ -> L) :
        ccall_contract c args (fun v h' => interpret_scheap h' ⊢ Φ v) h ->
        CTriple (interpret_scheap h) c args Φ.
      Proof.
        destruct c as [Σe δe req result ens]; cbn.
        rewrite CPureSpec.wp_angelic_ctx.
        intros [ι HΦ]; revert HΦ; cbn.
        rewrite CHeapSpec.wp_assert_eq_nenv.
        intros [Hfmls ->%CHeapSpec.cconsume_sound].
        apply bi.exist_intro' with ι.
        apply bi.and_intro; auto.
        apply bi.sep_mono'; [easy|].
        apply bi.forall_intro. intros v.
        apply bi.exist_elim. intros h2.
        apply bi.pure_elim_r. intros HΦ.
        specialize (HΦ v); cbn in HΦ.
        apply CHeapSpec.cproduce_sound in HΦ.
        rewrite HΦ.
        apply bi.wand_mono'. reflexivity.
        apply bi.exist_elim. intros h3.
        now apply bi.pure_elim_r.
      Qed.

      Lemma call_lemma_sound {Δ} (args : CStore Δ) (h : SCHeap) (Φ : L) (l : Lemma Δ) :
        ccall_lemma l args (fun _ h' => interpret_scheap h' ⊢ Φ) h ->
        LTriple args (interpret_scheap h) Φ l.
      Proof.
        destruct l as [Σe δe req ens]; cbn.
        rewrite CPureSpec.wp_angelic_ctx.
        intros [ι HΦ]; constructor; revert HΦ; cbn.
        rewrite CHeapSpec.wp_assert_eq_nenv.
        intros [Hfmls ->%CHeapSpec.cconsume_sound].
        apply bi.exist_intro' with ι.
        apply bi.and_intro; auto.
        apply bi.sep_mono'; [easy|].
        apply bi.exist_elim. intros h2.
        apply bi.pure_elim_r.
        intros ->%CHeapSpec.cproduce_sound.
        apply bi.wand_mono'. reflexivity.
        apply bi.exist_elim. intros h3.
        now apply bi.pure_elim_r.
      Qed.

      Lemma sexec_call_foreign :
        SExecCallForeign exec_call_foreign.
      Proof.
        unfold SExecCallForeign, exec_call_foreign. intros *.
        apply call_contract_sound.
      Qed.

      Lemma sexec_lemma : SExecLemma exec_lemma.
      Proof. intros Δ l args Φ h HΦ. now apply call_lemma_sound. Qed.

      Lemma sexec_call_error : SExecCall (exec_call_error (M:=CHeapSpec)).
      Proof. red; intros * []. Qed.

      Lemma sexec_call n : SExecCall (exec_call n).
      Proof.
        induction n; intros Γ Δ τ f args Φ δΓ h1;
          cbn - [exec CPureSpecM.bind evalCStoreT];
          destruct (CEnv f) eqn:Heqc.
        - intros HΦ%call_contract_sound.
          eapply rule_stm_call; eauto.
        - cbn. intros [].
        - intros HΦ%call_contract_sound.
          eapply rule_stm_call; eauto.
        - cbn. intros HΦ.
          apply rule_stm_call_inline.
          eapply sexec_aux;
            eauto using mon_exec_aux, mon_exec_call_foreign, mon_exec_lemma,
                   rexec_call, sexec_lemma, sexec_call_foreign.
          revert HΦ.
          apply (mon_exec_aux mon_exec_call_foreign mon_exec_lemma (rexec_call n)).
          reflexivity.
          intros [] [] [Heq1 Heq2] h2. cbn.
          cbn in Heq1, Heq2; now subst.
      Qed.

      Lemma sexec n : SExec (@exec n).
      Proof.
        apply sexec_aux; try typeclasses eauto;
          auto using sexec_call_foreign, sexec_lemma, sexec_call.
      Qed.

      Lemma sexec_wp n {Γ σ} (s : Stm Γ σ) (Φ : Val σ -> CStore Γ -> L) δ1 h1 :
        exec n Γ σ s δ1 (fun '(v,δ2) h2 => interpret_scheap h2 ⊢ Φ v δ2) h1 ->
        interpret_scheap h1 ⊢ WP s Φ δ1.
      Proof.
        cbn in *; intros.
        unfold WP.
        apply sexec in H.
        apply bi.exist_intro' with (interpret_scheap h1).
        apply bi.and_intro.
        reflexivity.
        now apply bi.pure_intro.
      Qed.

      Lemma shallow_vcgen_sound n {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
        shallow_vcgen n c body ->
        ProgramLogic.ValidContract c body.
      Proof.
        unfold shallow_vcgen, ProgramLogic.ValidContract.
        unfold inst_contract_localstore.
        unfold exec_contract.
        destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
        rewrite CPureSpec.wp_demonic_ctx in HYP.
        specialize (HYP ι). remember (inst δΣ ι) as δ.
        apply CHeapSpec.cproduce_sound, wand_sep_adjoint in HYP. cbn in HYP.
        rewrite bi.emp_sep in HYP.
        eapply rule_consequence_left.
        apply rule_wp. rewrite HYP. clear HYP.
        apply bi.exist_elim. intros h1.
        apply bi.pure_elim_r. intros HΦ.
        apply (sexec_wp n). revert HΦ.
        apply rexec. reflexivity.
        intros [v0 ?] [v δ1] [Heq1 Heq2] h2 HΦ.
        cbn in Heq1, Heq2, HΦ. subst.
        apply CHeapSpec.cconsume_sound in HΦ.
        rewrite HΦ.
        (* LEAK h' *)
        apply bi.sep_elim_l; typeclasses eauto.
      Qed.

      Lemma shallow_vcgen_soundness {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
        Shallow.ValidContract c body ->
        ProgramLogic.ValidContract c body.
      Proof. apply shallow_vcgen_sound. Qed.

      Lemma shallow_vcgen_fuel_soundness {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) :
        Shallow.ValidContractWithFuel fuel c body ->
        ProgramLogic.ValidContract c body.
      Proof. apply shallow_vcgen_sound. Qed.

    End VCGen.

  End WithBI.

End VCGenSoundnessOn.

Module MakeShallowSoundness (B : Base) (SIG : Signature B) (PROG : Program B)
  (SPEC : Specification B SIG PROG) (SHAL : ShallowVCGen B SIG PROG SPEC)
  (HOAR : ProgramLogicOn B SIG PROG SPEC).

  Include VCGenSoundnessOn B SIG PROG SPEC SHAL HOAR.

End MakeShallowSoundness.
