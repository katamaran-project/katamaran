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

  (* This section verifies the monotonicity of the calculated predicate
     transformers. Which is a necessity for the main soundness theorems. *)
  Section Monotonicity.

    Definition Monotonic {Γ1 Γ2 A} (m : CStoreSpec Γ1 Γ2 A) : Prop :=
      forall
        (P Q : A -> CStore Γ2 -> SCHeap -> Prop)
        (PQ : forall x δ h, P x δ h -> Q x δ h),
      forall δ h, m P δ h -> m Q δ h.

    (* Stronger version for those that do not change the store. *)
    Definition Monotonic' {Γ A} (m : CStoreSpec Γ Γ A) : Prop :=
      forall δ
        (P Q : A -> CStore Γ -> SCHeap -> Prop)
        (PQ : forall x h, P x δ h -> Q x δ h),
      forall h, m P δ h -> m Q δ h.

    Lemma consume_chunk_monotonic {Γ} (c : SCChunk) :
      Monotonic' (consume_chunk (Γ := Γ) c).
    Proof.
      unfold consume_chunk, Monotonic. intros δ P Q PQ.
      apply CHeapSpec.mon_consume_chunk. intros ? ? ->.
      unfold pointwise_relation, impl. apply PQ.
    Qed.

    Lemma produce_chunk_monotonic {Γ} (c : SCChunk) :
      Monotonic' (produce_chunk (Γ := Γ) c).
    Proof.
      unfold produce_chunk, Monotonic. intros δ P Q PQ.
      apply CHeapSpec.mon_produce_chunk. intros ? ? ->.
      unfold pointwise_relation, impl. apply PQ.
    Qed.

    Lemma consume_monotonic {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
      Monotonic' (consume (Γ := Γ) ι asn).
    Proof.
      unfold consume, Monotonic'. intros * PQ δ.
      apply CHeapSpec.mon_consume. intros ? ? ->.
      unfold pointwise_relation, impl. apply PQ.
    Qed.

    Lemma produce_monotonic {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
      Monotonic' (produce (Γ := Γ) ι asn).
    Proof.
      unfold produce, Monotonic'. intros * PQ.
      apply CHeapSpec.mon_produce. intros ? ? ->.
      unfold pointwise_relation, impl. apply PQ.
    Qed.

    Lemma read_register_monotonic {Γ τ} (r : 𝑹𝑬𝑮 τ) :
      Monotonic (read_register (Γ := Γ) r).
    Proof.
      unfold read_register, Monotonic. intros * PQ δ.
      apply CHeapSpec.mon_read_register. intros ? ? ->.
      unfold pointwise_relation, impl. apply PQ.
    Qed.

    Lemma write_register_monotonic {Γ τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) :
      Monotonic (write_register (Γ := Γ) r v).
    Proof.
      unfold write_register, Monotonic. intros * PQ δ.
      apply CHeapSpec.mon_write_register. intros ? ? ->.
      unfold pointwise_relation, impl. apply PQ.
    Qed.

    Lemma call_lemma_monotonic {Γ Δ} (lem : Lemma Δ) (δΔ : CStore Δ) :
      Monotonic (call_lemma (Γ := Γ) lem δΔ).
    Proof.
      destruct lem; intros P Q PQ δ h;
        cbv [call_lemma bind
               angelic_ctx lift_purem assert_formula
               CPureSpec.assert_formula].
      rewrite ?CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]. exists ι. revert Hwp.
      unfold assert_eq_nenv, lift_purem.
      rewrite ?CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls Hwp]; split; auto; revert Hwp.
      apply consume_monotonic. intros _ ?.
      apply produce_monotonic; auto.
    Qed.

    Lemma call_contract_monotonic {Γ Δ τ} (c : SepContract Δ τ) (δΔ : CStore Δ) :
      Monotonic (call_contract (Γ := Γ) c δΔ).
    Proof.
      destruct c; intros P Q PQ δ h;
        cbv [call_contract bind pure demonic
               angelic_ctx demonic lift_purem assert_formula
               CPureSpec.assert_formula].
      rewrite ?CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]. exists ι. revert Hwp.
      unfold assert_eq_nenv, lift_purem.
      rewrite ?CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls Hwp]; split; auto; revert Hwp.
      apply consume_monotonic. intros _ ? Hwp v.
      specialize (Hwp v); revert Hwp.
      apply produce_monotonic; auto.
    Qed.

    Definition MonotonicExec (ex : Exec) : Prop :=
      forall Γ τ (s : Stm Γ τ),
      Monotonic (ex _ _ s).

    Lemma exec_aux_monotonic rec (rec_mono : MonotonicExec rec) :
      MonotonicExec (@exec_aux rec).
    Proof.
      unfold MonotonicExec. intros ? ? s.
      induction s; cbn; intros P Q PQ *;
        cbv [pure bind angelic pushpop pushspops
               put_local get_local eval_exp eval_exps assign].
      - auto.
      - auto.
      - apply IHs1. intros *. apply IHs2. auto.
      - apply IHs. auto.
      - apply IHs. auto.
      - destruct (CEnv f); cbn; auto.
        + apply call_contract_monotonic; auto.
        + apply rec_mono; auto.
      - apply IHs. auto.
      - apply call_contract_monotonic; auto.
      - apply call_lemma_monotonic; intros ? ? ?.
        apply IHs. auto.
      - apply IHs1. intros ? ? ?. apply IHs2. auto.
      - intros HYP Heq. specialize (HYP Heq). revert HYP.
        apply IHs; auto.
      - auto.
      - apply IHs. intros ? ? ?.
        rewrite !wp_demonic_pattern_match.
        destruct pattern_match_val.
        apply H; auto.
      - now apply read_register_monotonic.
      - now apply write_register_monotonic.
      - apply IHs; intros *; apply H; auto.
      - apply IHs; auto.
    Qed.

    Lemma exec_monotonic n : MonotonicExec (@exec n).
    Proof.
      induction n; cbn.
      - unfold MonotonicExec, Monotonic; cbn; auto.
      - now apply exec_aux_monotonic.
    Qed.

  End Monotonicity.

  Section Soundness.

    Import iris.proofmode.tactics.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    (* liftP converts the "proof theoretic" predicates (CStore Γ -> L), with L
       being a type of separation logic propositions, to the "model theoretic"
       heap predicates (CStore Γ -> SCHeap -> Prop) that are used as the type of
       postconditions in the shallow executor. *)
    Definition liftP {Γ} (POST : CStore Γ -> L) : CStore Γ -> SCHeap -> Prop :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Lemma consume_chunk_sound {Γ} (c : SCChunk) (POST : CStore Γ -> L) :
      forall δ h,
        consume_chunk c (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_scchunk c ∗ POST δ.
    Proof.
      unfold consume_chunk. intros δ h ->%CPureSpec.wp_consume_chunk.
      apply bi.sep_mono'. easy.
      apply bi.exist_elim. intros h'.
      now apply bi.pure_elim_r.
    Qed.

    Lemma assert_formula_sound {Γ Σ} {ι : Valuation Σ} {fml : Formula Σ}
      (POST : CStore Γ -> L) :
      forall δ h,
        assert_formula (instprop fml ι)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ⊢ (⌜instprop fml ι⌝ ∧ emp) ∗ POST δ.
    Proof.
      intros ? ? [Hfml HP].
      transitivity (emp ∗ interpret_scheap h)%I; auto.
      apply bi.sep_mono'; auto.
    Qed.

    Lemma assume_formula_sound {Γ Σ} {ι : Valuation Σ} {fml : Formula Σ}
      (POST : CStore Γ -> L) :
      forall δ h,
        assume_formula (instprop fml ι)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ∗ (⌜instprop fml ι⌝ ∧ emp) ⊢ POST δ.
    Proof.
      iIntros (? ? HYP) "(Hh & %Hfml & _)".
      now iApply HYP.
    Qed.

    Lemma consume_sound {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        consume ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ asn.interpret asn ι ∗ POST δ.
    Proof.
      intros ? ? ->%CHeapSpec.consume_sound. apply bi.sep_mono'; [easy|].
      iIntros "(%h' & Hh' & %HΦ)". now iApply HΦ.
    Qed.

    Lemma produce_sound {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        (* Alternatively, we could write this as *)
        (* interpret_scheap h ⊢ interpret_assertion asn ι -∗ POST δ. *)
        (* which more closely resembles the assume guard. Why didn't we do this? *)
        interpret_scheap h ∗ asn.interpret asn ι ⊢ POST δ.
    Proof.
      intros ? ? ->%CHeapSpec.produce_sound.
      apply wand_sep_adjoint. apply bi.wand_mono'; [easy|].
      iIntros "(%h' & Hh' & %HΦ)". now iApply HΦ.
    Qed.

    Lemma produce_sound' {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        asn.interpret asn ι ⊢ interpret_scheap h -∗ POST δ.
    Proof.
      intros. apply wand_sep_adjoint. rewrite bi.sep_comm.
      now apply produce_sound.
    Qed.

    Lemma call_contract_sound {Γ Δ τ} (δΓ : CStore Γ) (δΔ : CStore Δ)
          (h : SCHeap) (POST : Val τ -> CStore Γ -> L)
          (c : SepContract Δ τ) :
      call_contract c δΔ (fun a => liftP (POST a)) δΓ h ->
      CTriple (interpret_scheap h) c δΔ  (fun v => POST v δΓ).
    Proof.
      destruct c as [Σe δe req result ens].
      unfold call_contract. unfold bind.
      unfold angelic_ctx, lift_purem.
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      unfold assert_eq_nenv, lift_purem.
      rewrite CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls Hwp]. cbn.
      apply bi.exist_intro' with ι.
      apply bi.and_intro; auto.
      apply (consume_sound (fun δ => ∀ v, asn.interpret ens (env.snoc ι (result∷_) v) -∗ POST v δ))%I.
      revert Hwp. apply consume_monotonic.
      intros _ h2. unfold demonic.
      intros HYP.
      apply bi.forall_intro; intro v.
      specialize (HYP v).
      now apply wand_sep_adjoint, produce_sound.
    Qed.

    Lemma call_lemma_sound {Γ Δ} (δΓ : CStore Γ) (δΔ : CStore Δ)
          (h : SCHeap) (POST : CStore Γ -> L)
          (lem : Lemma Δ) :
      call_lemma lem δΔ (fun _ : unit => liftP POST) δΓ h ->
      LTriple δΔ (interpret_scheap h) (POST δΓ) lem.
    Proof.
      destruct lem as [Σe δe req ens].
      unfold call_lemma. unfold bind.
      unfold angelic_ctx, lift_purem.
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      unfold assert_eq_nenv, lift_purem.
      rewrite CPureSpec.wp_assert_eq_nenv.
      intros [Hfmls Hwp]. constructor.
      apply bi.exist_intro' with ι.
      apply bi.and_intro; auto.
      transitivity (asn.interpret req ι ∗ (∀ _ : Val ty.unit, asn.interpret ens ι -∗ POST δΓ))%I.
      - apply (consume_sound (fun δ => ∀ v, asn.interpret ens ι -∗ POST δΓ) δΓ)%I.
        revert Hwp. apply consume_monotonic.
        intros _ h2. intros HYP.
        apply bi.forall_intro; intro v.
        now apply wand_sep_adjoint, produce_sound.
      - apply bi.sep_mono'; [easy|]. etransitivity.
        now apply (bi.forall_elim tt). auto.
    Qed.

    Definition SoundExec (rec : Exec) :=
      forall
        Γ σ (s : Stm Γ σ) (POST : Val σ -> CStore Γ -> L)
        (δ1 : CStore Γ) (h1 : SCHeap),
        rec _ _ s (fun v => liftP (POST v)) δ1 h1 ->
        ⦃ interpret_scheap h1 ⦄ s ; δ1 ⦃ POST ⦄.

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
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2. intros HYP.
        apply bi.exist_intro' with (interpret_scheap h2).
        apply bi.and_intro.
        reflexivity.
        apply bi.pure_intro.
        apply IHs2.
        auto.

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
        unfold eval_exps in HYP.
        eapply rule_stm_lemmak.
        2: apply rule_wp.
        eapply call_lemma_sound.
        revert HYP.
        eapply call_lemma_monotonic.
        intros _ δ2 h2 HYP.
        unfold liftP. unfold WP.
        apply bi.exist_intro' with (interpret_scheap h2).
        apply bi.and_intro.
        reflexivity.
        apply bi.pure_intro.
        now apply IHs.

      - (* stm_seq *)
        apply rule_stm_seq with (WP s2 POST).
        + apply IHs1. revert HYP.
          apply exec_aux_monotonic; auto.
          intros _ δ1' h1' H.
          specialize (IHs2 POST δ1' h1' H).
          unfold liftP, WP.
          apply bi.exist_intro' with (interpret_scheap h1').
          apply bi.and_intro. reflexivity.
          apply bi.pure_intro. assumption.
        + apply rule_wp.

      - (* stm_assert *)
        apply rule_stm_assert; intro Heval.
        now apply IHs, HYP.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply bi.True_intro.

      - (* stm_match_newpattern *)
        apply
          (rule_consequence_left
             (WP s
                (fun (vσ : Val σ) (δ2 : CStore Γ) =>
                   let 'existT pc δpc := pattern_match_val pat vσ in
                   WP (rhs pc)
                     (fun vτ δ3  => POST vτ (env.drop (PatternCaseCtx pc) δ3))
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
          revert HYP. apply exec_aux_monotonic; auto.
          intros v2 δ2 h2 HYP; cbn.
          rewrite wp_demonic_pattern_match in HYP.
          destruct pattern_match_val. cbn in HYP.
          apply bi.exist_intro' with (interpret_scheap h2).
          apply bi.and_intro.
          reflexivity.
          apply bi.pure_intro.
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
        intros ->%CPureSpec.wp_produce_chunk.
        apply bi.wand_mono'. easy.
        apply bi.exist_elim. intros h3.
        now apply bi.pure_elim_r.

      - (* stm_write_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        apply CPureSpec.wp_consume_chunk in HYP.
        rewrite HYP. clear HYP. cbn.
        apply bi.sep_mono'. easy.
        apply bi.exist_elim. intros h2.
        apply bi.pure_elim_r.
        intros ->%CPureSpec.wp_produce_chunk.
        apply bi.wand_mono'. easy.
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
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2 HYP; cbn.

        apply bi.exist_intro' with (interpret_scheap h2).
        apply bi.and_intro.
        reflexivity.
        apply bi.pure_intro.
        now apply H.
      - constructor. auto.
    Qed.

    Lemma exec_sound n : SoundExec (@exec n).
    Proof.
      induction n; cbn.
      - unfold SoundExec; cbn; contradiction.
      - apply exec_aux_sound; auto using exec_monotonic.
    Qed.

    Lemma exec_sound' n {Γ σ} (s : Stm Γ σ) (POST : Val σ -> CStore Γ -> L) :
      forall δ1 h1,
        exec n s (fun v2 => liftP (POST v2)) δ1 h1 ->
        liftP (WP s POST) δ1 h1.
    Proof.
      cbn in *; intros.
      unfold WP.
      apply exec_sound in H.
      apply bi.exist_intro' with (interpret_scheap h1).
      apply bi.and_intro.
      reflexivity.
      now apply bi.pure_intro.
    Qed.

    Lemma vcgen_sound n {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      CStoreSpec.vcgen n c body ->
      ProgramLogic.ValidContract c body.
    Proof.
      unfold CStoreSpec.vcgen, ProgramLogic.ValidContract.
      unfold inst_contract_localstore.
      unfold exec_contract, bind.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      rewrite env.Forall_forall in HYP.
      - specialize (HYP ι). remember (inst δΣ ι) as δ.
        eapply rule_consequence_left.
        apply rule_wp.
        transitivity (interpret_scheap nil -∗ WP body (fun (v : Val τ) (_ : CStore Δ) => asn.interpret ens (env.snoc ι (result∷τ) v)) δ)%I; [|now rewrite bi.emp_wand].
        apply produce_sound'.
        revert HYP. apply produce_monotonic.
        intros _ h2 HYP. apply exec_sound' with n.
        revert HYP. apply exec_monotonic.
        intros v3 δ3 h3 HYP.
        enough (interpret_scheap h3 ⊢ asn.interpret ens (env.snoc ι (result∷τ) v3) ∗ emp)
          by now rewrite bi.sep_emp in H.
        change emp%I with ((fun _ => @bi_emp L) δ3).
        apply (consume_sound (asn := ens)).
        revert HYP. apply consume_monotonic.
        intros _ h4 HYP. unfold liftP. auto.
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
