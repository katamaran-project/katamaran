(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     SemiConcrete.Mutator
     SemiConcrete.Outcome.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).

  Module MUT := SemiConcrete termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic termkit progkit assertkit contractkit.
  Import LOG.

  Local Open Scope logic.
  Import LogicNotations.

  Section Soundness.

    Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

    Definition interpret_scchunk (c : SCChunk) : L :=
      match c with
      | scchunk_user p vs => luser p vs
      | scchunk_ptsreg r v => lptsreg r v
      end.

    Definition interpret_scheap : SCHeap -> L :=
      List.fold_right (fun c h => interpret_scchunk c ✱ h) emp.
    Global Arguments interpret_scheap !h.

    Lemma in_heap_extractions {h c1 h1} (hyp : List.In (c1 , h1) (heap_extractions h)) :
      interpret_scheap h ⊣⊢s interpret_scchunk c1 ✱ interpret_scheap h1.
    Proof.
      revert c1 h1 hyp.
      induction h; cbn; intros.
      - contradict hyp.
      - destruct hyp as [hyp|hyp].
        + inversion hyp; subst.
          split; apply entails_refl.
        + cbn in *.
          apply List.in_map_iff in hyp.
          destruct hyp as [[c2 h2] [H1 H2]].
          inversion H1; subst; clear H1.
          apply IHh in H2; rewrite H2; clear IHh H2.
          rewrite sepcon_comm.
          rewrite sepcon_assoc.
          split; apply sepcon_entails; auto using entails_refl.
          apply sepcon_comm.
          apply sepcon_comm.
    Qed.

    Lemma cmut_wp_angelick_list {A B Γ1 Γ2} (msg : string) (xs : list A) (k : A -> CMut Γ1 Γ2 B) (POST : B -> SCProp Γ2) :
      forall δ h,
        cmut_wp (cmut_angelick_list msg xs k) POST δ h <->
        (exists x : A, List.In x xs /\ cmut_wp (k x) POST δ h).
    Proof.
      intros δ h. unfold cmut_wp, cmut_angelick_list; cbn.
      rewrite outcome_satisfy_angelick_list. intuition.
    Qed.

    Definition liftP {Γ} (POST : LocalStore Γ -> L) : SCProp Γ :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Lemma cmut_consume_chunk_sound {Γ} (c : SCChunk) (POST : LocalStore Γ -> L) :
      forall δ h,
        cmut_wp (cmut_consume_chunk c) (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_scchunk c ✱ POST δ.
    Proof.
      intros δ h.
      unfold cmut_consume_chunk, cmut_get_heap.
      rewrite cmut_wp_bind, cmut_wp_state, cmut_wp_angelick_list.
      intros (hr & H1 & H2). unfold extract_scchunk_eqb in H1.
      rewrite List.in_map_iff in H1. destruct H1 as [[c1 h1] [Heq H1]].
      rewrite List.filter_In in H1. destruct H1 as [HIn Hmatch].
      apply (Bool.reflect_iff _ _ (match_scchunk_eqb_spec _ _)) in Hmatch.
      cbn in Heq. subst.
      apply in_heap_extractions in HIn; rewrite HIn; clear HIn.
      apply sepcon_entails.
      apply entails_refl.
      assumption.
    Qed.

    Lemma cmut_assert_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : LocalStore Γ -> L) :
      forall δ h,
        cmut_wp
          (cmut_assert_formula ι fml)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ⊢ !! inst fml ι ∧ emp ✱ POST δ.
    Proof.
      intros ? ?. rewrite cmut_wp_assert_formula.
      intros [Hfml HP].
      rewrite <- sepcon_emp at 1.
      rewrite sepcon_comm.
      apply sepcon_entails; auto.
      apply land_right.
      apply lprop_right; assumption.
      apply entails_refl.
    Qed.

    Lemma cmut_assume_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : LocalStore Γ -> L) :
      forall δ h,
        cmut_wp
          (cmut_assume_formula ι fml)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ✱ !! inst fml ι ∧ emp ⊢ POST δ.
    Proof.
      intros ? ?. rewrite cmut_wp_assume_formula.
      intros HYP.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply limpl_and_adjoint.
      apply lprop_left. intros Hfml.
      apply limpl_and_adjoint.
      apply land_left2.
      apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      rewrite sepcon_emp.
      now apply HYP.
    Qed.

    Opaque cmut_assert_formula.
    Opaque cmut_assume_formula.
    Opaque cmut_consume_chunk.

    Lemma cmut_consume_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        cmut_wp (cmut_consume ι asn) (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_assertion asn ι ✱ POST δ.
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1 h1.
      - now apply cmut_assert_formula_sound.
      - destruct c; now apply cmut_consume_chunk_sound.
      - destruct (inst b ι); auto.
      - auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - auto.
      - auto.
      - destruct (𝑼_unfold (inst s ι)); auto.
      - rewrite cmut_wp_bind_right. intros Hwp.
        rewrite sepcon_assoc.
        apply (IHasn1 ι (fun δ => interpret_assertion asn2 ι ✱ POST δ) δ1 h1); clear IHasn1.
        revert Hwp. apply cmut_wp_monotonic. intros _ δ2 h2.
        now apply (IHasn2 ι POST δ2 h2).
      - rewrite cmut_wp_angelic. intros [v Hwp].
        apply (entails_trans (interpret_scheap h1) (interpret_assertion asn (env_snoc ι (ς , τ) v) ✱ POST δ1)).
        + now apply IHasn.
        + apply sepcon_entails.
          apply lex_right with v, entails_refl.
          apply entails_refl.
      - now rewrite cmut_wp_pure, sepcon_comm, sepcon_emp.
    Qed.

    Lemma cmut_produce_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        cmut_wp (cmut_produce ι asn) (fun _ => liftP POST) δ h ->
        interpret_scheap h ✱ interpret_assertion asn ι ⊢ POST δ.
    Proof.
      revert POST. induction asn; cbn - [cmut_assume_formula]; intros POST δ1 h1.
      - now apply cmut_assume_formula_sound.
      - rewrite sepcon_comm.
        destruct c; now cbn in *.
      - destruct (inst b ι); auto.
      - auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - auto.
      - auto.
      - destruct (𝑼_unfold (inst s ι)); auto.
      - rewrite cmut_wp_bind_right. intros Hwp.
        rewrite <- sepcon_assoc.
        apply wand_sepcon_adjoint.
        apply (IHasn1 ι (fun δ => interpret_assertion asn2 ι -✱ POST δ) δ1 h1 ); clear IHasn1.
        revert Hwp. apply cmut_wp_monotonic. intros _ δ2 h2 Hwp.
        unfold liftP. apply wand_sepcon_adjoint.
        now apply (IHasn2 ι POST δ2 h2).
      - rewrite cmut_wp_demonic. intros Hwp.
        rewrite sepcon_comm.
        apply wand_sepcon_adjoint.
        apply lex_left. intro v.
        apply wand_sepcon_adjoint.
        rewrite sepcon_comm.
        now apply IHasn.
      - now rewrite cmut_wp_pure, sepcon_emp.
    Qed.

    Lemma cmut_produce_sound' {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        cmut_wp (cmut_produce ι asn) (fun _ => liftP POST) δ h ->
        interpret_assertion asn ι ⊢ interpret_scheap h -✱ POST δ.
    Proof.
      intros. apply wand_sepcon_adjoint. rewrite sepcon_comm.
      now apply cmut_produce_sound.
    Qed.

    Lemma cmut_call_sound {Γ Δ τ} (δΓ : LocalStore Γ) (δΔ : LocalStore Δ)
          (h : SCHeap) (POST : Lit τ -> LocalStore Γ -> L)
          (c : SepContract Δ τ) :
      cmut_wp
        (cmut_call c δΔ)
        (fun a => liftP (POST a))
        δΓ h ->
      CTriple δΔ (interpret_scheap h) (fun v => POST v δΓ) c.
    Proof.
      destruct c as [Σe δe req result ens].
      unfold cmut_call. rewrite cmut_wp_angelic.
      intros [ι Hwp]; revert Hwp.
      rewrite cmut_wp_assert_formulask.
      intros [Hfmls Hwp]; revert Hwp.
      rewrite cmut_wp_bind_right.
      pose (fun δ => ∀ v, interpret_assertion ens (env_snoc ι (result,_) v) -✱ POST v δ) as frame.
      intros HYP.
      assert (interpret_scheap h ⊢ frame δΓ ✱ interpret_assertion req ι ).
      { rewrite sepcon_comm.
        apply (cmut_consume_sound frame).
        revert HYP. apply cmut_wp_monotonic.
        intros ? δ2 h2. rewrite cmut_wp_demonic.
        intros HYP.
        apply lall_right; intro v.
        specialize (HYP v).
        rewrite cmut_wp_bind_right in HYP.
        now apply wand_sepcon_adjoint, cmut_produce_sound.
      }
      constructor 1 with ι (frame δΓ); auto.
      - apply inst_formula_eqs in Hfmls.
        now rewrite inst_lift in Hfmls.
      - intro v.
        apply wand_sepcon_adjoint.
        apply lall_left with v.
        apply entails_refl.
    Qed.

    Lemma cmut_exec_sound {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> LocalStore Γ -> L) :
      forall (δ1 : LocalStore Γ) (h1 : SCHeap),
        cmut_wp (cmut_exec s) (fun v => liftP (POST v)) δ1 h1 ->
        δ1 ⊢ ⦃ interpret_scheap h1 ⦄ s ⦃ POST ⦄.
    Proof.
      induction s; intros ? ?; cbn;
        unfold cmut_pushspops, cmut_pushs_local, cmut_pops_local,
          cmut_pushpop, cmut_push_local, cmut_pop_local,
          cmut_eval_exp, cmut_get_local, cmut_put_local,
          cmut_bind_right, cmut_bind_left;
        repeat (rewrite ?cmut_wp_bind, ?cmut_wp_state; cbn); intros HYP.

      - (* stm_lit *)
        now apply rule_stm_lit.

      - (* stm_exp *)
        now apply rule_stm_exp.

      - (* stm_let *)
        eapply rule_consequence_left.
        eapply rule_stm_let; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs1; clear IHs1.
        revert HYP. apply cmut_wp_monotonic.
        intros v2 δ2 h2.
        rewrite ?cmut_wp_bind, ?cmut_wp_state. cbn.
        rewrite cmut_wp_bind. intros HYP.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs2.
        auto.

      - (* stm_block *)
        now apply rule_stm_block, IHs.

      - (* stm_assign *)
        now apply rule_stm_assign_backwards, IHs.

      - (* stm_call *)
        destruct (CEnv f) as [c|] eqn:Heq; cbn in HYP.
        + apply rule_stm_call_backwards with c.
          assumption.
          now apply cmut_call_sound.
        + contradict HYP.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_call_external *)
        apply rule_stm_call_external_backwards.
        now apply cmut_call_sound.

      - (* stm_if *)
        apply rule_stm_if; apply rule_pull; intro Heval; rewrite Heval in *; auto.

      - (* stm_seq *)
        eapply rule_consequence_left.
        eapply rule_stm_seq; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs1; clear IHs1.
        revert HYP; apply cmut_wp_monotonic.
        intros v2 δ2 h2 HYP.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        now apply IHs2.

      - (* stm_assert *)
        apply rule_stm_assert, rule_pull;
          intro Heval; rewrite Heval in HYP.
        now apply IHs.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply ltrue_right.

      - (* stm_match_list *)
        apply rule_stm_match_list; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP.
        + now apply IHs1.
        + rewrite cmut_wp_bind, cmut_wp_state in HYP; cbn in HYP.
          rewrite cmut_wp_bind in HYP.
          now apply IHs2.

      - (* stm_match_sum *)
        apply rule_stm_match_sum; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP;
            rewrite cmut_wp_bind, cmut_wp_state in HYP; cbn in HYP;
              rewrite cmut_wp_bind in HYP.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_pair *)
        apply rule_stm_match_pair; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP;
            rewrite cmut_wp_bind, cmut_wp_state in HYP; cbn in HYP;
              rewrite cmut_wp_bind in HYP.
        now apply IHs.

      - (* stm_match_enum *)
        now apply rule_stm_match_enum, H.

      - (* stm_match_tuple *)
        now apply rule_stm_match_tuple, IHs.

      - (* stm_match_union *)
        apply rule_stm_match_union; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval, 𝑼_unfold_fold in HYP;
            rewrite cmut_wp_bind, cmut_wp_state in HYP; cbn in HYP;
              rewrite cmut_wp_bind in HYP.
        now apply H.

      - (* stm_match_record *)
        now apply rule_stm_match_record, IHs.

      - (* stm_read_register *)
        rewrite cmut_wp_angelic in HYP.
        destruct HYP as [v HYP].
        rewrite cmut_wp_bind in HYP.
        eapply rule_consequence_left.
        apply (rule_stm_read_register_backwards (v := v)).
        unfold liftP, cmut_wp, cmut_pure, cmut_bind in HYP.
        setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP.
        setoid_rewrite sepcon_comm in HYP.
        setoid_rewrite wand_sepcon_adjoint in HYP.
        now apply (cmut_consume_chunk_sound _ (fun δ => _ -✱ POST _ δ)) in HYP.

      - (* stm_write_register *)
        rewrite cmut_wp_angelic in HYP.
        destruct HYP as [v HYP].
        rewrite cmut_wp_bind in HYP.
        unfold liftP, cmut_wp, cmut_pure, cmut_bind in HYP.
        setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP.
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        setoid_rewrite sepcon_comm in HYP.
        setoid_rewrite wand_sepcon_adjoint in HYP.
        now apply (cmut_consume_chunk_sound _ (fun δ => _ -✱ POST _ δ)) in HYP.

      - (* stm_bind *)
        eapply rule_consequence_left.
        eapply rule_stm_bind; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs; clear IHs.
        revert HYP. apply cmut_wp_monotonic.
        intros v2 δ2 h2 HYP; cbn.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        now apply H.
      - constructor. auto.
    Qed.

    Lemma cmut_exec_sound' {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> LocalStore Γ -> L) :
      forall δ1 h1,
        cmut_wp (cmut_exec s) (fun v2 => liftP (POST v2)) δ1 h1 ->
        liftP (WP s POST) δ1 h1.
    Proof.
      cbn in *; intros.
      unfold WP.
      apply cmut_exec_sound in H.
      apply lex_right with (interpret_scheap h1).
      apply land_right.
      reflexivity.
      now apply lprop_right.
    Qed.

    Lemma cmut_contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractCMut c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractCMut, ValidContract.
      unfold inst_contract_localstore.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      - specialize (HYP ι). remember (inst δΣ ι) as δ.
        rewrite cmut_wp_bind_right in HYP.
        eapply rule_consequence_left.
        apply rule_wp.
        apply entails_trans with
            (interpret_scheap nil -✱ WP body (fun (v : Lit τ) (_ : LocalStore Δ) => interpret_assertion ens (env_snoc ι (result,τ) v)) δ).
        apply cmut_produce_sound'.
        2: {
          rewrite <- sepcon_emp.
          apply wand_sepcon_adjoint.
          apply entails_refl.
        }
        revert HYP. apply cmut_wp_monotonic.
        intros _ δ2 h2 HYP. apply cmut_exec_sound'.
        revert HYP. rewrite cmut_wp_bind. apply cmut_wp_monotonic.
        intros v3 δ3 h3 HYP.
        enough (interpret_scheap h3 ⊢ interpret_assertion ens (env_snoc ι (result,τ) v3) ✱ emp)
          by now rewrite sepcon_emp in H.
        change emp with ((fun _ => emp) δ3).
        apply (cmut_consume_sound (asn := ens)).
        revert HYP. rewrite cmut_wp_bind_right.
        apply cmut_wp_monotonic.
        intros _ δ4 h4 HYP. unfold liftP.
    Admitted.

  End Soundness.

End Soundness.
