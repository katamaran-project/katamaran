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
     Classes.Morphisms
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Signature
     Sep.Hoare
     Sep.Logic
     Specification
     Prelude
     Program
     Staging.NewShallow.Executor.

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
          (P Q : A -> CStore Γ2 -> L)
          (PQ : forall x δ, P x δ ⊢ Q x δ),
          forall δ, m P δ ⊢ m Q δ.

      (* Stronger version for those that do not change the store. *)
      Definition Monotonic' {Γ A} (m : CHeapSpecM Γ Γ A) : Prop :=
        forall δ
          (P Q : A -> CStore Γ -> L)
          (PQ : forall x, P x δ ⊢ Q x δ),
          m P δ ⊢ m Q δ.

      Lemma consume_chunk_monotonic {Γ} {c : SCChunk} :
        Monotonic' (consume_chunk (Γ := Γ) c).
      Proof. intros δ P Q PQ. now apply proper_lsep_entails. Qed.

      Lemma produce_chunk_monotonic {Γ} {c : SCChunk} :
        Monotonic' (produce_chunk (Γ := Γ) c).
      Proof. intros δ P Q PQ. now apply proper_lwand_entails. Qed.

      Lemma consume_monotonic {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        Monotonic' (consume (Γ := Γ) ι asn).
      Proof.
        intros δ. induction asn; cbn; intros * PQ *.
        - now apply proper_land_entails.
        - now apply consume_chunk_monotonic.
        - now apply consume_chunk_monotonic.
        - rewrite ?wp_angelic_match_bool. destruct (inst b ι); cbn; auto.
        - rewrite ?wp_angelic_match_enum; auto.
        - rewrite ?wp_angelic_match_sum. destruct (inst s ι); cbn; auto.
        - rewrite ?wp_angelic_match_list. destruct (inst s ι); cbn; auto.
        - rewrite ?wp_angelic_match_prod. destruct (inst s ι); cbn; auto.
        - rewrite ?wp_angelic_match_tuple; auto.
        - rewrite ?wp_angelic_match_record; auto.
        - rewrite ?wp_angelic_match_union. destruct (unionv_unfold U (inst s ι)); auto.
        - unfold bind; auto.
        - apply proper_lor_entails; auto.
        - apply proper_lex_entails; intros v; auto.
        - unfold pure; auto.
      Qed.

      Lemma produce_monotonic {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        Monotonic' (produce (Γ := Γ) ι asn).
      Proof.
        intros δ. induction asn; cbn; intros * PQ *.
        - now apply proper_limpl_entails.
        - now apply produce_chunk_monotonic.
        - now apply produce_chunk_monotonic.
        - rewrite ?wp_demonic_match_bool. destruct (inst b ι); cbn; eauto.
        - rewrite ?wp_demonic_match_enum; eauto.
        - rewrite ?wp_demonic_match_sum. destruct (inst s ι); cbn; eauto.
        - rewrite ?wp_demonic_match_list. destruct (inst s ι); cbn; eauto.
        - rewrite ?wp_demonic_match_prod. destruct (inst s ι); cbn; eauto.
        - rewrite ?wp_demonic_match_tuple; eauto.
        - rewrite ?wp_demonic_match_record; eauto.
        - rewrite ?wp_demonic_match_union. destruct (unionv_unfold U (inst s ι)); eauto.
        - unfold bind; auto.
        - apply proper_land_entails; auto.
        - apply proper_lall_entails; intros v; auto.
        - unfold pure; eauto.
      Qed.

      Lemma call_lemma_monotonic {Γ Δ} (lem : Lemma Δ) (δΔ : CStore Δ) :
        Monotonic (call_lemma (Γ := Γ) lem δΔ).
      Proof.
        destruct lem; intros P Q PQ δ;
          cbv [call_lemma bind bind_right
               angelic_ctx lift_purem assert_formula
               CPureSpecM.assert_formula].
        rewrite ?CPureSpecM.wp_angelic_ctx.
        apply proper_lex_entails; intros ι.
        unfold assert_eq_nenv, lift_purem.
        rewrite ?CPureSpecM.wp_assert_eq_nenv.
        apply proper_land_entails; [easy|].
        apply consume_monotonic. intros _.
        apply produce_monotonic; auto.
      Qed.

      Lemma call_contract_monotonic {Γ Δ τ} (c : SepContract Δ τ) (δΔ : CStore Δ) :
        Monotonic (call_contract (Γ := Γ) c δΔ).
      Proof.
        destruct c; intros P Q PQ δ;
          cbv [call_contract bind_right bind pure demonic
               angelic_ctx demonic lift_purem assert_formula
               CPureSpecM.assert_formula].
        rewrite ?CPureSpecM.wp_angelic_ctx.
        apply proper_lex_entails; intros ι.
        unfold assert_eq_nenv, lift_purem.
        rewrite ?CPureSpecM.wp_assert_eq_nenv.
        apply proper_land_entails; [easy|].
        apply consume_monotonic. intros _.
        apply proper_lall_entails; intros v.
        apply produce_monotonic; auto.
      Qed.

      Definition MonotonicExec (ex : Exec) : Prop :=
        forall Γ τ (s : Stm Γ τ),
          Monotonic (ex _ _ s).

      Lemma exec_aux_monotonic rec (rec_mono : MonotonicExec rec) :
        MonotonicExec (exec_aux rec).
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
        - apply call_lemma_monotonic; intros ? ?.
          apply IHs. auto.
        - rewrite ?wp_demonic_match_bool.
          destruct (eval e δ); [apply IHs1|apply IHs2]; auto.
        - apply IHs1. intros ? ?. apply IHs2. auto.
        - apply proper_limpl_entails; [easy|]. now apply IHs.
        - easy.
        - rewrite ?wp_demonic_match_list.
          destruct (eval e δ); [apply IHs1|apply IHs2]; auto.
        - rewrite ?wp_demonic_match_sum.
          destruct (eval e δ); [apply IHs1|apply IHs2]; auto.
        - rewrite ?wp_demonic_match_prod.
          destruct (eval e δ); apply IHs; auto.
        - rewrite ?wp_demonic_match_enum.
          apply H; auto.
        - rewrite ?wp_demonic_match_tuple.
          apply IHs; auto.
        - rewrite ?wp_demonic_match_union.
          destruct (unionv_unfold U (eval e δ)).
          apply H; auto.
        - rewrite ?wp_demonic_match_record.
          apply IHs; auto.
        - rewrite ?wp_demonic_match_bvec.
          apply H; auto.
        - rewrite ?wp_demonic_match_bvec_split.
          destruct bv.appView. apply IHs; auto.
        - apply proper_lex_entails; intros v.
          apply consume_chunk_monotonic. intros _.
          now apply produce_chunk_monotonic.
        - apply proper_lex_entails; intros v.
          apply consume_chunk_monotonic. intros _.
          now apply produce_chunk_monotonic.
        - apply IHs; intros *; apply H; auto.
        - apply IHs; auto.
      Qed.

      Lemma exec_monotonic n : MonotonicExec (exec n).
      Proof.
        induction n; cbn.
        - unfold MonotonicExec, Monotonic, error; easy.
        - now apply exec_aux_monotonic.
      Qed.

    End Monotonicity.

    Lemma scchunk_duplicate (c : SCChunk) :
      is_duplicable c = true -> interpret_scchunk c ⊢@{L} interpret_scchunk c ∗ interpret_scchunk c.
    Proof.
      destruct c; cbn; try discriminate.
      eauto using lduplicate.
    Qed.

    Lemma assert_formula_sound {Γ Σ} {ι : Valuation Σ} {fml : Formula Σ} (POST : unit -> CStore Γ -> L) δ :
      assert_formula (inst fml ι) POST δ ⊣⊢ (!! inst fml ι ∧ lemp) ∗ POST tt δ.
    Proof. now rewrite lemp_true, land_true, lprop_sep_and. Qed.

    Lemma assume_formula_sound {Γ Σ} {ι : Valuation Σ} {fml : Formula Σ} (POST : unit -> CStore Γ -> L) δ :
      assume_formula (inst fml ι) POST δ ⊣⊢ ((!! inst fml ι ∧ lemp) -∗ POST tt δ).
    Proof. now rewrite lemp_true, land_true, lprop_wand_impl. Qed.

    Lemma interpret_scchunk_inst {Σ} (c : Chunk Σ) (ι : Valuation Σ) :
      interpret_scchunk (inst c ι) = interpret_chunk c ι.
    Proof.
      induction c; cbn [interpret_chunk];
        try rewrite <- IHc1, <- IHc2; reflexivity.
    Qed.

    Lemma consume_sound {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : unit -> CStore Γ -> L) :
      forall δ,
        consume ι asn POST δ ⊣⊢ asn.interpret asn ι ∗ POST tt δ.
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1.
      - apply assert_formula_sound.
      - unfold consume_chunk; now rewrite interpret_scchunk_inst.
      - unfold consume_chunk; now rewrite interpret_scchunk_inst.
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
      - unfold bind. now rewrite IHasn1, IHasn2, <- lsep_assoc.
      - rewrite lsep_disj_distr. now apply proper_lor_equiv.
      - rewrite lsep_exists_comm. now apply proper_lex_equiv.
      - now rewrite lsep_comm, lsep_emp.
    Qed.

    Lemma produce_sound {Γ Σ} {ι : Valuation Σ} {asn : Assertion Σ} (POST : unit -> CStore Γ -> L) :
      forall δ,
        produce ι asn POST δ ⊣⊢ (asn.interpret asn ι -∗ POST tt δ).
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1.
      - apply assume_formula_sound.
      - unfold produce_chunk; now rewrite interpret_scchunk_inst.
      - unfold produce_chunk; now rewrite interpret_scchunk_inst.
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
      - unfold bind. now rewrite IHasn1, IHasn2, lwand_curry.
      - unfold demonic_binary. now rewrite IHasn1, IHasn2, lwand_disj_distr.
      - unfold bind, demonic. rewrite lwand_exists_comm.
        now apply proper_lall_equiv.
      - now rewrite lwand_emp.
    Qed.

    Lemma call_contract_sound {Γ Δ τ} (δΓ : CStore Γ)
      (c : SepContract Δ τ) (δΔ : CStore Δ) (POST : Val τ -> CStore Γ -> L) :
      CTriple δΔ (call_contract c δΔ POST δΓ) (fun v => POST v δΓ) c.
    Proof.
      destruct c as [Σe δe req result ens]. constructor.
      cbv [call_contract bind_right bind pure
           angelic_ctx assert_eq_nenv lift_purem demonic].
      rewrite CPureSpecM.wp_angelic_ctx.
      apply proper_lex_entails. intros ι.
      rewrite CPureSpecM.wp_assert_eq_nenv.
      apply proper_land_entails.
      now apply proper_lprop_entails.
      rewrite consume_sound.
      apply proper_lsep_entails; [easy|].
      apply proper_lall_entails. intros v.
      now apply produce_sound.
    Qed.

    Lemma call_lemma_sound {Γ Δ} (δΓ : CStore Γ)
      (lem : Lemma Δ) (δΔ : CStore Δ) (POST : unit -> CStore Γ -> L) :
      LTriple δΔ (call_lemma lem δΔ POST δΓ) (POST tt δΓ) lem.
    Proof.
      destruct lem as [Σe δe req ens]. constructor.
      cbv [call_lemma bind_right bind angelic_ctx assert_eq_nenv lift_purem].
      rewrite CPureSpecM.wp_angelic_ctx.
      apply proper_lex_entails. intros ι.
      rewrite CPureSpecM.wp_assert_eq_nenv.
      apply proper_land_entails.
      now apply proper_lprop_entails.
      rewrite consume_sound.
      apply proper_lsep_entails; [easy|].
      now apply produce_sound.
    Qed.

    Definition SoundExec (rec : Exec) :=
      forall Γ σ (s : Stm Γ σ) (POST : Val σ -> CStore Γ -> L) (δ1 : CStore Γ),
        ⦃ rec _ _ s POST δ1 ⦄ s ; δ1 ⦃ POST ⦄.

    Lemma exec_aux_sound rec (rec_mono : MonotonicExec rec) (rec_sound : SoundExec rec) :
      SoundExec (exec_aux rec).
    Proof.
      unfold SoundExec. intros ? ? s.
      induction s; intros ? ?; cbn;
        cbv [pure pushspops pushpop
             eval_exp get_local put_local
             bind].

      - (* stm_val *)
        now apply rule_stm_val.

      - (* stm_exp *)
        now apply rule_stm_exp.

      - (* stm_let *)
        eapply rule_stm_let. apply IHs1. intros v2 δ2; cbn. apply IHs2.

      - (* stm_block *)
        now apply rule_stm_block, IHs.

      - (* stm_assign *)
        now apply rule_stm_assign_backwards, IHs.

      - (* stm_call *)
        destruct (CEnv f) as [c|] eqn:Heq.
        + apply rule_stm_call_backwards with c.
          assumption.
          now apply call_contract_sound.
        + unfold eval_exps.
          eapply rule_consequence_right.
          apply rule_stm_call_inline.
          apply rec_sound.
          intros v δ; cbn.
          rewrite lprop_float.
          apply land_prop_left; now intros ->.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_foreign *)
        apply rule_stm_foreign_backwards.
        apply call_contract_sound.

      - (* stm_lemmak *)
        unfold eval_exps.
        eapply rule_stm_lemmak.
        apply call_lemma_sound.
        apply IHs.

      - (* stm_if *)
        rewrite wp_demonic_match_bool.
        apply rule_stm_if; apply rule_pull; intro Heval; rewrite Heval in *; auto.

      - (* stm_seq *)
        eapply rule_stm_seq. apply IHs1. intros δ2. apply IHs2.

      - (* stm_assert *)
        apply rule_stm_assert, rule_pull;
          intro Heval; rewrite Heval.
        eapply rule_consequence_left. apply IHs.
        unfold assume_formula, lift_purem, CPureSpecM.assume_formula.
        now apply lentails_apply, lprop_right.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply ltrue_right.

      - (* stm_match_list *)
        rewrite wp_demonic_match_list.
        apply rule_stm_match_list; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_sum *)
        rewrite wp_demonic_match_sum.
        apply rule_stm_match_sum; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_prod *)
        rewrite wp_demonic_match_prod.
        apply rule_stm_match_prod; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval.
        now apply IHs.

      - (* stm_match_enum *)
        rewrite wp_demonic_match_enum.
        now apply rule_stm_match_enum, H.

      - (* stm_match_tuple *)
        rewrite wp_demonic_match_tuple.
        now apply rule_stm_match_tuple, IHs.

      - (* stm_match_union *)
        rewrite wp_demonic_match_union.
        apply rule_stm_match_union; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval, unionv_unfold_fold.
        now apply H.

      - (* stm_match_record *)
        rewrite wp_demonic_match_record.
        now apply rule_stm_match_record, IHs.

      - (* stm_match_bvec *)
        rewrite wp_demonic_match_bvec.
        now apply rule_stm_match_bvec, H.

      - (* stm_match_bvec_split *)
        rewrite wp_demonic_match_bvec_split.
        apply rule_stm_match_bvec_split; cbn; intros;
          apply rule_pull; intro Heval.
        now rewrite Heval, bv.appView_app.

      - (* stm_read_register *)
        apply rule_exist. intros v.
        apply (rule_stm_read_register_backwards (v := v)).

      - (* stm_write_register *)
        apply rule_exist. intros v.
        apply (rule_stm_write_register_backwards (v := v)).

      - (* stm_bind *)
        eapply rule_stm_bind. apply IHs. intros v2 δ2; cbn. apply H.
      - constructor. auto.
    Qed.

    Lemma exec_sound n : SoundExec (exec n).
    Proof.
      induction n; cbn.
      - unfold SoundExec. intros. apply rule_false.
      - apply exec_aux_sound; auto using exec_monotonic.
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
        rewrite produce_sound in HYP.
        apply lwand_sep_adjoint in HYP.
        rewrite lsep_true in HYP.
        eapply rule_consequence_left.
        apply exec_sound. rewrite HYP.
        apply exec_monotonic. intros v δ1.
        rewrite consume_sound.
        now rewrite lsep_comm, lsep_true.
    Qed.

    Lemma shallow_vcgen_soundness {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContract c body ->
      ProgramLogic.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    (* Print Assumptions shallow_vcgen_soundnes. *)

  End Soundness.

End Soundness.
