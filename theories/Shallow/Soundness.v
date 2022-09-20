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
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG)
  (Import EXEC : ShallowExecOn B PROG SIG SPEC)
  (Import HOAR : ProgramLogicOn B PROG SIG SPEC).

  Import sep.instances.
  Import sep.notations.
  Import CHeapSpecM.
  Import ProgramLogic.

  Section Soundness.

    Context {L} {PI : PredicateDef L}.

    (* This section verifies the monotonicity of the calculated predicate
       transformers. Which is a necessity for the main soundness theorems. *)
    Section Monotonicity.

      Definition Monotonic {Γ1 Γ2 A} (m : CHeapSpecM Γ1 Γ2 A) : Prop :=
        forall
          (P Q : A -> CStore Γ2 -> SCHeap -> Prop)
          (PQ : forall x δ h, P x δ h -> Q x δ h),
          forall δ h, m P δ h -> m Q δ h.

      (* Stronger version for those that do not change the store. *)
      Definition Monotonic' {Γ A} (m : CHeapSpecM Γ Γ A) : Prop :=
        forall δ
          (P Q : A -> CStore Γ -> SCHeap -> Prop)
          (PQ : forall x h, P x δ h -> Q x δ h),
          forall h, m P δ h -> m Q δ h.

      Lemma consume_chunk_monotonic {Γ} {c : SCChunk} :
        Monotonic' (consume_chunk (Γ := Γ) c).
      Proof.
        cbv [Monotonic' consume_chunk bind bind_right get_heap angelic_list
             lift_purem assert_formula put_heap CPureSpecM.assert_formula
             assert_eq_chunk].
        intros δ P Q PQ h. rewrite ?CPureSpecM.wp_angelic_list.
        intros [ch' Hwp]; exists ch'; revert Hwp. destruct ch'.
        rewrite ?CPureSpecM.wp_assert_eq_chunk. intuition.
      Qed.

      Lemma consume_monotonic {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        Monotonic' (consume (Γ := Γ) ι asn).
      Proof.
        intros δ. induction asn; cbn; intros * PQ *.
        - unfold assert_formula, lift_purem, CPureSpecM.assert_formula.
          intuition.
        - now apply consume_chunk_monotonic.
        - now apply consume_chunk_monotonic.
        - rewrite !wp_angelic_match_bool.
          destruct (inst b ι); cbn; eauto.
        - rewrite !wp_angelic_match_enum; eauto.
        - rewrite !wp_angelic_match_sum.
          destruct (inst s ι); cbn; eauto.
        - rewrite !wp_angelic_match_list.
          destruct (inst s ι); cbn; eauto.
        - rewrite !wp_angelic_match_prod.
          destruct (inst s ι); cbn; eauto.
        - rewrite !wp_angelic_match_tuple; eauto.
        - rewrite !wp_angelic_match_record; eauto.
        - rewrite !wp_angelic_match_union.
          destruct (unionv_unfold U (inst s ι)); eauto.
        - unfold bind.
          apply IHasn1; eauto.
        - intros [|].
          + left. apply IHasn1 with (P := P); assumption.
          + right. apply IHasn2 with (P := P); assumption.
        - unfold bind, angelic.
          intros [v ?]; exists v; eauto.
        - unfold pure; eauto.
      Qed.

      Lemma produce_monotonic {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        Monotonic' (produce (Γ := Γ) ι asn).
      Proof.
        intros δ. induction asn; cbn; intros * PQ *.
        - unfold assume_formula, lift_purem, CPureSpecM.assume_formula.
          intuition.
        - unfold produce_chunk; eauto.
        - unfold produce_chunk; eauto.
        - rewrite !wp_demonic_match_bool.
          destruct (inst b ι); cbn; eauto.
        - rewrite !wp_demonic_match_enum; eauto.
        - rewrite !wp_demonic_match_sum.
          destruct (inst s ι); cbn; eauto.
        - rewrite !wp_demonic_match_list.
          destruct (inst s ι); cbn; eauto.
        - rewrite !wp_demonic_match_prod.
          destruct (inst s ι); cbn; eauto.
        - rewrite !wp_demonic_match_tuple; eauto.
        - rewrite !wp_demonic_match_record; eauto.
        - rewrite !wp_demonic_match_union.
          destruct (unionv_unfold U (inst s ι)); eauto.
        - unfold bind.
          apply IHasn1; eauto.
        - intros [Hasn1 Hasn2].
          split.
          + apply IHasn1 with (P := P); assumption.
          + apply IHasn2 with (P := P); assumption.
        - unfold bind, demonic. eauto.
        - unfold pure; eauto.
      Qed.

      Lemma call_lemma_monotonic {Γ Δ} (lem : Lemma Δ) (δΔ : CStore Δ) :
        Monotonic (call_lemma (Γ := Γ) lem δΔ).
      Proof.
        destruct lem; intros P Q PQ δ h;
          cbv [call_lemma bind bind_right
               angelic_ctx lift_purem assert_formula
               CPureSpecM.assert_formula].
        rewrite ?CPureSpecM.wp_angelic_ctx.
        intros [ι Hwp]. exists ι. revert Hwp.
        unfold assert_eq_nenv, lift_purem.
        rewrite ?CPureSpecM.wp_assert_eq_nenv.
        intros [Hfmls Hwp]; split; auto; revert Hwp.
        apply consume_monotonic. intros _ ?.
        apply produce_monotonic; auto.
      Qed.

      Lemma call_contract_monotonic {Γ Δ τ} (c : SepContract Δ τ) (δΔ : CStore Δ) :
        Monotonic (call_contract (Γ := Γ) c δΔ).
      Proof.
        destruct c; intros P Q PQ δ h;
          cbv [call_contract bind_right bind pure demonic
               angelic_ctx demonic lift_purem assert_formula
               CPureSpecM.assert_formula].
        rewrite ?CPureSpecM.wp_angelic_ctx.
        intros [ι Hwp]. exists ι. revert Hwp.
        unfold assert_eq_nenv, lift_purem.
        rewrite ?CPureSpecM.wp_assert_eq_nenv.
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
               produce_chunk put_local get_local eval_exp eval_exps assign].
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
        - rewrite !wp_demonic_match_bool.
          destruct (eval e δ).
          apply IHs1; auto.
          apply IHs2; auto.
        - apply IHs1. intros ? ? ?. apply IHs2. auto.
        - intros HYP Heq. specialize (HYP Heq). revert HYP.
          apply IHs; auto.
        - auto.
        - apply IHs. intros ? ? ?.
          rewrite !wp_demonic_newpattern_match.
          apply H; auto.
        - apply IHs1. intros ? ? ?.
          rewrite !wp_demonic_match_pattern.
          apply IHs2; auto.
        - rewrite !wp_demonic_match_list.
          destruct (eval e δ).
          apply IHs1; auto.
          apply IHs2; auto.
        - rewrite !wp_demonic_match_sum.
          destruct (eval e δ); cbn.
          apply IHs1; auto.
          apply IHs2; auto.
        - rewrite !wp_demonic_match_enum.
          apply H; auto.
        - rewrite !wp_demonic_match_union.
          destruct (unionv_unfold U (eval e δ)).
          apply H; auto.
        - rewrite !wp_demonic_match_bvec.
          apply H; auto.
        - intros [v Hwp]; exists v; revert Hwp.
          apply consume_chunk_monotonic. auto.
        - intros [v Hwp]; exists v; revert Hwp.
          apply consume_chunk_monotonic. auto.
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

    Lemma scchunk_duplicate (c : SCChunk) :
      is_duplicable c = true -> interpret_scchunk c ⊢@{L} interpret_scchunk c ∗ interpret_scchunk c.
    Proof.
      destruct c; cbn; try discriminate.
      eauto using lduplicate.
    Qed.

    Lemma in_heap_extractions {h : SCHeap} {c1 h1} (hyp : List.In (c1 , h1) (heap_extractions h)) :
      interpret_scheap h ⊣⊢@{L} interpret_scchunk c1 ∗ interpret_scheap h1.
    Proof.
      revert c1 h1 hyp.
      induction h; cbn -[is_duplicable]; intros.
      - contradict hyp.
      - destruct hyp as [hyp|hyp].
        + destruct (is_duplicable a) eqn:Heqdup;
            inversion hyp; subst; clear hyp.
          { split.
            - transitivity ((interpret_scchunk c1 ∗ interpret_scchunk c1) ∗ interpret_scheap h).
              apply lsep_entails; [|reflexivity].
              apply scchunk_duplicate; assumption.
              rewrite <- lsep_assoc. reflexivity.
            - apply lsep_entails; [reflexivity|]. cbn.
              transitivity (lemp ∗ interpret_scheap h).
              apply lsep_entails; [|reflexivity].
              apply lsep_leak.
              now rewrite lsep_comm, lsep_emp.
          }
          { split; reflexivity. }
        + cbn in *.
          apply List.in_map_iff in hyp.
          destruct hyp as [[c2 h2] [H1 H2]].
          inversion H1; subst; clear H1.
          apply IHh in H2; rewrite H2; clear IHh H2.
          rewrite lsep_comm.
          rewrite <- lsep_assoc.
          split; apply lsep_entails; try reflexivity.
          apply lsep_comm.
          apply lsep_comm.
    Qed.

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
      cbv [bind bind_right get_heap consume_chunk angelic_list assert_eq_chunk
           CPureSpecM.assert_formula lift_purem assert_formula put_heap].
      intros δ h. rewrite CPureSpecM.wp_angelic_list.
      intros [[c' h'] [HIn Hwp]].
      rewrite CPureSpecM.wp_assert_eq_chunk in Hwp.
      destruct Hwp as [Hc HPOST]. subst c'.
      apply in_heap_extractions in HIn; rewrite HIn; clear HIn.
      apply lsep_entails. reflexivity. apply HPOST.
    Qed.

    Lemma assert_formula_sound {Γ Σ} {ι : Valuation Σ} {fml : Formula Σ}
      (POST : CStore Γ -> L) :
      forall δ h,
        assert_formula (inst fml ι)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ⊢ (!! inst fml ι ∧ lemp) ∗ POST δ.
    Proof.
      intros ? ? [Hfml HP].
      rewrite <- lsep_emp at 1.
      rewrite lsep_comm.
      apply lsep_entails; auto.
      apply land_right.
      apply lprop_right; assumption.
      reflexivity.
    Qed.

    Lemma assume_formula_sound {Γ Σ} {ι : Valuation Σ} {fml : Formula Σ}
      (POST : CStore Γ -> L) :
      forall δ h,
        assume_formula (inst fml ι)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ∗ (!! inst fml ι ∧ lemp) ⊢ POST δ.
    Proof.
      intros ? ? HYP.
      rewrite lsep_comm.
      apply lwand_sep_adjoint.
      apply limpl_and_adjoint.
      apply lprop_left. intros Hfml.
      apply limpl_and_adjoint.
      apply land_left2.
      apply lwand_sep_adjoint.
      rewrite lsep_comm.
      rewrite lsep_emp.
      now apply HYP.
    Qed.

    Lemma consume_sound {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        consume ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ asn.interpret asn ι ∗ POST δ.
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1 h1.
      - now apply assert_formula_sound.
      - intros Hc%consume_chunk_sound.
        now rewrite interpret_scchunk_inst in Hc.
      - intros Hc%consume_chunk_sound.
        now rewrite interpret_scchunk_inst in Hc.
      - rewrite wp_angelic_match_bool.
        destruct (inst b ι); auto.
      - rewrite wp_angelic_match_enum; auto.
      - rewrite wp_angelic_match_sum.
        destruct (inst s ι); auto.
      - rewrite wp_angelic_match_list.
        destruct (inst s ι); auto.
      - rewrite wp_angelic_match_prod.
        destruct (inst s ι); auto.
      - rewrite wp_angelic_match_tuple; auto.
      - rewrite wp_angelic_match_record; auto.
      - rewrite wp_angelic_match_union.
        destruct (unionv_unfold U (inst s ι)); auto.
      - unfold bind. intros Hwp. rewrite <- lsep_assoc.
        apply (IHasn1 ι (fun δ => asn.interpret asn2 ι ∗ POST δ) δ1 h1); clear IHasn1.
        revert Hwp. apply consume_monotonic. intros _ h2.
        now apply (IHasn2 ι POST δ1 h2).
      - intros []; rewrite lsep_disj_distr.
        + apply lor_right1; apply IHasn1; assumption.
        + apply lor_right2; apply IHasn2; assumption.
      - intros [v Hwp].
        transitivity (asn.interpret asn (env.snoc ι (ς∷τ) v) ∗ POST δ1).
        + now apply IHasn.
        + apply lsep_entails.
          apply lex_right with v.
          reflexivity.
          reflexivity.
      - now rewrite lsep_comm, lsep_emp.
    Qed.

    Lemma produce_sound {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ∗ asn.interpret asn ι ⊢ POST δ.
        (* Alternatively, we could write this as
             interpret_scheap h ⊢ interpret_assertion asn ι -∗ POST δ.
           which more closely resembles the assume guard. Why didn't we do this? *)
    Proof.
      revert POST. induction asn; cbn - [assume_formula]; intros POST δ1 h1.
      - now apply assume_formula_sound.
      - rewrite lsep_comm.
        unfold produce_chunk, liftP; cbn.
        now rewrite interpret_scchunk_inst.
      - rewrite lsep_comm.
        unfold produce_chunk, liftP; cbn.
        now rewrite interpret_scchunk_inst.
      - rewrite wp_demonic_match_bool.
        destruct (inst b ι); auto.
      - rewrite wp_demonic_match_enum; auto.
      - rewrite wp_demonic_match_sum.
        destruct (inst s ι); auto.
      - rewrite wp_demonic_match_list.
        destruct (inst s ι); auto.
      - rewrite wp_demonic_match_prod.
        destruct (inst s ι); auto.
      - rewrite wp_demonic_match_tuple; auto.
      - rewrite wp_demonic_match_record; auto.
      - rewrite wp_demonic_match_union.
        destruct (unionv_unfold U (inst s ι)); auto.
      - unfold bind. intros Hwp.
        rewrite lsep_assoc.
        apply lwand_sep_adjoint.
        apply (IHasn1 ι (fun δ => asn.interpret asn2 ι -∗ POST δ) δ1 h1 ); clear IHasn1.
        revert Hwp. apply produce_monotonic. intros _ h2 Hwp.
        unfold liftP. apply lwand_sep_adjoint.
        now apply (IHasn2 ι POST δ1 h2).
      - intros [].
        rewrite lsep_comm.
        rewrite lsep_disj_distr.
        apply lor_left; rewrite lsep_comm.
        + apply IHasn1; assumption.
        + apply IHasn2; assumption.
      - intros Hwp.
        rewrite lsep_comm.
        apply lwand_sep_adjoint.
        apply lex_left. intro v.
        apply lwand_sep_adjoint.
        rewrite lsep_comm.
        now apply IHasn.
      - now rewrite lsep_emp.
    Qed.

    Lemma produce_sound' {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        asn.interpret asn ι ⊢ interpret_scheap h -∗ POST δ.
    Proof.
      intros. apply lwand_sep_adjoint. rewrite lsep_comm.
      now apply produce_sound.
    Qed.

    Lemma call_contract_sound {Γ Δ τ} (δΓ : CStore Γ) (δΔ : CStore Δ)
          (h : SCHeap) (POST : Val τ -> CStore Γ -> L)
          (c : SepContract Δ τ) :
      call_contract c δΔ (fun a => liftP (POST a)) δΓ h ->
      CTriple (interpret_scheap h) c δΔ  (fun v => POST v δΓ).
    Proof.
      destruct c as [Σe δe req result ens].
      unfold call_contract. unfold bind_right, bind.
      unfold angelic_ctx, lift_purem.
      rewrite CPureSpecM.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      unfold assert_eq_nenv, lift_purem.
      rewrite CPureSpecM.wp_assert_eq_nenv.
      intros [Hfmls Hwp]. cbn.
      apply (lex_right ι). apply land_right.
      { now apply lprop_right. }
      apply (consume_sound (fun δ => ∀ v, asn.interpret ens (env.snoc ι (result∷_) v) -∗ POST v δ)).
      revert Hwp. apply consume_monotonic.
      intros _ h2. unfold demonic.
      intros HYP.
      apply lall_right; intro v.
      specialize (HYP v).
      now apply lwand_sep_adjoint, produce_sound.
    Qed.

    Lemma call_lemma_sound {Γ Δ} (δΓ : CStore Γ) (δΔ : CStore Δ)
          (h : SCHeap) (POST : CStore Γ -> L)
          (lem : Lemma Δ) :
      call_lemma lem δΔ (fun _ : unit => liftP POST) δΓ h ->
      LTriple δΔ (interpret_scheap h) (POST δΓ) lem.
    Proof.
      destruct lem as [Σe δe req ens].
      unfold call_lemma. unfold bind_right, bind.
      unfold angelic_ctx, lift_purem.
      rewrite CPureSpecM.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      unfold assert_eq_nenv, lift_purem.
      rewrite CPureSpecM.wp_assert_eq_nenv.
      intros [Hfmls Hwp]. constructor.
      apply (lex_right ι). apply land_right.
      { now apply lprop_right. }
      transitivity (asn.interpret req ι ∗ (∀ _ : Val ty.unit, asn.interpret ens ι -∗ POST δΓ)).
      - apply (consume_sound (fun δ => ∀ v, asn.interpret ens ι -∗ POST δΓ) δΓ).
        revert Hwp. apply consume_monotonic.
        intros _ h2. intros HYP.
        apply lall_right; intro v.
        now apply lwand_sep_adjoint, produce_sound.
      - apply proper_lsep_entails; [easy|].
        now apply (lall_left tt).
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

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        reflexivity.
        apply lprop_right.
        apply IHs1; clear IHs1.
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2. intros HYP.
        apply lex_right with (interpret_scheap h2).
        apply land_right.
        reflexivity.
        apply lprop_right.
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
        apply lex_right with (interpret_scheap h2).
        apply land_right.
        reflexivity.
        apply lprop_right.
        now apply IHs.

      - (* stm_if *)
        rewrite wp_demonic_match_bool in HYP.
        apply rule_stm_if; intro Heval; rewrite Heval in HYP; auto.

      - (* stm_seq *)
        apply rule_stm_seq with (WP s2 POST).
        + apply IHs1. revert HYP.
          apply exec_aux_monotonic; auto.
          intros _ δ1' h1' H.
          specialize (IHs2 POST δ1' h1' H).
          unfold liftP, WP.
          apply lex_right with (interpret_scheap h1').
          apply land_right. reflexivity.
          apply lprop_right. assumption.
        + apply rule_wp.

      - (* stm_assert *)
        apply rule_stm_assert; intro Heval.
        now apply IHs, HYP.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply ltrue_right.

      - (* stm_match_newpattern *)
        apply
          (rule_consequence_left
             (WP s
                (fun (vσ : Val σ) (δ2 : CStore Γ) =>
                   let 'existT pc δpc := newpattern_match_val pat vσ in
                   WP (rhs pc)
                     (fun vτ δ3  => POST vτ (env.drop (PatternCaseCtx pc) δ3))
                     (δ2 ►► δpc))
                δ1)).
        + eapply rule_stm_newpattern_match.
          apply rule_wp. intros.
          eapply rule_consequence_left.
          apply rule_wp.
          now rewrite newpattern_match_val_inverse_right.
        + apply lex_right with (interpret_scheap h1).
          apply land_right.
          reflexivity.
          apply lprop_right.
          apply IHs; clear IHs.
          revert HYP. apply exec_aux_monotonic; auto.
          intros v2 δ2 h2 HYP; cbn.
          rewrite wp_demonic_newpattern_match in HYP.
          destruct newpattern_match_val. cbn in HYP.
          apply lex_right with (interpret_scheap h2).
          apply land_right.
          reflexivity.
          apply lprop_right.
          now apply H.

      - (* stm_match_pattern *)
        eapply rule_consequence_left.
        eapply rule_stm_match_pattern; intros; apply rule_wp.
        apply lex_right with (interpret_scheap h1).
        apply land_right.
        reflexivity.
        apply lprop_right.
        apply IHs1; clear IHs1.
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2 HYP; cbn.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        reflexivity.
        apply lprop_right.
        rewrite wp_demonic_match_pattern in HYP.
        now apply IHs2.

      - (* stm_match_list *)
        rewrite wp_demonic_match_list in HYP.
        apply rule_stm_match_list; cbn; intros * Heval;
          rewrite Heval in HYP; auto.

      - (* stm_match_sum *)
        rewrite wp_demonic_match_sum in HYP.
        apply rule_stm_match_sum; cbn; intros * Heval;
          rewrite Heval in HYP; auto.

      - (* stm_match_enum *)
        rewrite wp_demonic_match_enum in HYP.
        now apply rule_stm_match_enum, H.

      - (* stm_match_union *)
        rewrite wp_demonic_match_union in HYP.
        apply rule_stm_match_union; cbn; intros * Heval;
          rewrite Heval, unionv_unfold_fold in HYP.
        now apply H.

      - (* stm_match_bvec *)
        rewrite wp_demonic_match_bvec in HYP.
        now apply rule_stm_match_bvec, H.

      - (* stm_read_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_read_register_backwards (v := v)).
        apply (@consume_chunk_sound Γ (scchunk_ptsreg reg v) (fun δ => _ -∗ POST _ δ)).
        revert HYP. apply consume_chunk_monotonic.
        intros _ h2.
        unfold produce_chunk, liftP. cbn.
        now rewrite lsep_comm, lwand_sep_adjoint.

      - (* stm_write_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        apply (@consume_chunk_sound Γ (scchunk_ptsreg reg v) (fun δ => _ -∗ POST _ δ)).
        revert HYP. apply consume_chunk_monotonic.
        intros _ h2.
        unfold produce_chunk, liftP. cbn.
        now rewrite lsep_comm, lwand_sep_adjoint.

      - (* stm_bind *)
        eapply rule_consequence_left.
        eapply rule_stm_bind; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        reflexivity.
        apply lprop_right.
        apply IHs; clear IHs.
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2 HYP; cbn.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        reflexivity.
        apply lprop_right.
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
      apply lex_right with (interpret_scheap h1).
      apply land_right.
      reflexivity.
      now apply lprop_right.
    Qed.

    Lemma vcgen_sound n {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      CHeapSpecM.vcgen n c body ->
      ProgramLogic.ValidContract c body.
    Proof.
      unfold CHeapSpecM.vcgen, ProgramLogic.ValidContract.
      unfold inst_contract_localstore.
      unfold exec_contract, bind.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      rewrite env.Forall_forall in HYP.
      - specialize (HYP ι). remember (inst δΣ ι) as δ.
        eapply rule_consequence_left.
        apply rule_wp.
        transitivity (interpret_scheap nil -∗ WP body (fun (v : Val τ) (_ : CStore Δ) => asn.interpret ens (env.snoc ι (result∷τ) v)) δ).
        apply produce_sound'.
        2: {
          rewrite <- lsep_emp.
          apply lwand_sep_adjoint.
          reflexivity.
        }
        revert HYP. apply produce_monotonic.
        intros _ h2 HYP. apply exec_sound' with n.
        revert HYP. apply exec_monotonic.
        intros v3 δ3 h3 HYP.
        enough (interpret_scheap h3 ⊢ asn.interpret ens (env.snoc ι (result∷τ) v3) ∗ lemp)
          by now rewrite lsep_emp in H.
        change lemp with ((fun _ => @lemp L) δ3).
        apply (consume_sound (asn := ens)).
        revert HYP. apply consume_monotonic.
        intros _ h4 HYP. unfold liftP.
        apply lsep_leak.
    Qed.

    Lemma shallow_vcgen_soundness {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContract c body ->
      ProgramLogic.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    (* Print Assumptions shallow_vcgen_soundnes. *)

  End Soundness.

End Soundness.

Module MakeShallowSoundness
  (Import B : Base)
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG)
  (Import EXEC : ShallowExecOn B PROG SIG SPEC)
  (Import HOAR : ProgramLogicOn B PROG SIG SPEC).

  Include Soundness B PROG SIG SPEC EXEC HOAR.

End MakeShallowSoundness.
