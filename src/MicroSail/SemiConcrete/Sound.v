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

    Definition liftP {Γ} (POST : LocalStore Γ -> L) : LocalStore Γ -> SCHeap -> Prop :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Import CMut.

    Lemma consume_chunk_sound {Γ} (c : SCChunk) (POST : LocalStore Γ -> L) :
      forall δ h,
        consume_chunk c (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_scchunk c ✱ POST δ.
    Proof.
      intros δ h.
      unfold consume_chunk.
      rewrite CDijk.wp_angelic_list.
      intros [h1 [HIn HPOST]].
      unfold extract_scchunk_eqb in HIn.
      rewrite List.in_map_iff in HIn.
      destruct HIn as [[c1 h1'] [Heq HIn]].
      cbn in Heq. subst h1'.
      rewrite List.filter_In in HIn.
      destruct HIn as [HIn Hmatch].
      apply (Bool.reflect_iff _ _ (match_scchunk_eqb_spec _ _)) in Hmatch.
      subst c1.
      apply in_heap_extractions in HIn; rewrite HIn; clear HIn.
      apply sepcon_entails.
      apply entails_refl.
      assumption.
    Qed.

    Lemma assert_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : LocalStore Γ -> L) :
      forall δ h,
        assert_formula ι fml
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ⊢ !! inst fml ι ∧ emp ✱ POST δ.
    Proof.
      intros ? ? [Hfml HP].
      rewrite <- sepcon_emp at 1.
      rewrite sepcon_comm.
      apply sepcon_entails; auto.
      apply land_right.
      apply lprop_right; assumption.
      apply entails_refl.
    Qed.

    Lemma assume_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : LocalStore Γ -> L) :
      forall δ h,
        assume_formula (inst fml ι)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ✱ !! inst fml ι ∧ emp ⊢ POST δ.
    Proof.
      intros ? ? HYP.
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

    Lemma consume_chunk_monotonic {Γ} {c : SCChunk}
      (P Q : unit -> LocalStore Γ -> SCHeap -> Prop)
      (PQ : forall x δ h, P x δ h -> Q x δ h) δ h :
      consume_chunk (Γ := Γ) c P δ h ->
      consume_chunk (Γ := Γ) c Q δ h.
    Proof.
      unfold consume_chunk.
      rewrite ?CDijk.wp_angelic_list.
      intros [h']; exists h'; intuition.
    Qed.

    Lemma consume_monotonic {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} :
      forall
        (P Q : unit -> LocalStore Γ -> SCHeap -> Prop)
        (PQ : forall x δ h, P x δ h -> Q x δ h) δ h,
        consume (Γ := Γ) ι asn P δ h ->
        consume (Γ := Γ) ι asn Q δ h.
    Proof.
      induction asn; cbn.
      - unfold assert_formula. intuition.
      - apply consume_chunk_monotonic.
      - destruct (inst b ι); cbn; eauto.
      - unfold match_enum. eauto.
      - destruct (inst s ι); cbn; eauto.
      - destruct (inst s ι); cbn; eauto.
      - destruct (inst s ι); cbn; eauto.
      - eauto.
      - unfold match_record. eauto.
      - destruct (𝑼_unfold (inst s ι)); eauto.
      - intros * PQ *. unfold bind_right, bind.
        apply IHasn1; eauto.
      - intros * PQ *. unfold bind, angelic.
        intros [v ?]; exists v; eauto.
      - unfold pure; eauto.
    Qed.

    Opaque assert_formula.
    Opaque assume_formula.
    Opaque consume_chunk.

    Lemma consume_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        consume ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_assertion asn ι ✱ POST δ.
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1 h1.
      - now apply assert_formula_sound.
      - destruct c; now apply consume_chunk_sound.
      - destruct (inst b ι); auto.
      - auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - auto.
      - auto.
      - destruct (𝑼_unfold (inst s ι)); auto.
      - unfold bind_right, bind. intros Hwp. rewrite sepcon_assoc.
        apply (IHasn1 ι (fun δ => interpret_assertion asn2 ι ✱ POST δ) δ1 h1); clear IHasn1.
        revert Hwp. apply consume_monotonic. intros _ δ2 h2.
        now apply (IHasn2 ι POST δ2 h2).
      - intros [v Hwp].
        apply (entails_trans (interpret_scheap h1) (interpret_assertion asn (env_snoc ι (ς , τ) v) ✱ POST δ1)).
        + now apply IHasn.
        + apply sepcon_entails.
          apply lex_right with v, entails_refl.
          apply entails_refl.
      - now rewrite sepcon_comm, sepcon_emp.
    Qed.

    Lemma produce_monotonic {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ}
      (P Q : unit -> LocalStore Γ -> SCHeap -> Prop)
      (PQ : forall x δ h, P x δ h -> Q x δ h) :
      forall δ h,
        produce (Γ := Γ) ι asn P δ h ->
        produce (Γ := Γ) ι asn Q δ h.
    Proof.
    Admitted.

    Lemma produce_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ✱ interpret_assertion asn ι ⊢ POST δ.
    Proof.
      revert POST. induction asn; cbn - [assume_formula]; intros POST δ1 h1.
      - now apply assume_formula_sound.
      - rewrite sepcon_comm.
        destruct c; now cbn in *.
      - (* rewrite cmut_wp_demonic_match_bool. *)
      (* destruct (inst b ι); auto. *)
        admit.
      - auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - auto.
      - auto.
      - destruct (𝑼_unfold (inst s ι)); auto.
      - unfold bind_right, bind. intros Hwp.
        rewrite <- sepcon_assoc.
        apply wand_sepcon_adjoint.
        apply (IHasn1 ι (fun δ => interpret_assertion asn2 ι -✱ POST δ) δ1 h1 ); clear IHasn1.
        revert Hwp. apply produce_monotonic. intros _ δ2 h2 Hwp.
        unfold liftP. apply wand_sepcon_adjoint.
        now apply (IHasn2 ι POST δ2 h2).
      - intros Hwp.
        rewrite sepcon_comm.
        apply wand_sepcon_adjoint.
        apply lex_left. intro v.
        apply wand_sepcon_adjoint.
        rewrite sepcon_comm.
        now apply IHasn.
      - now rewrite sepcon_emp.
    Admitted.

    Lemma produce_sound' {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        interpret_assertion asn ι ⊢ interpret_scheap h -✱ POST δ.
    Proof.
      intros. apply wand_sepcon_adjoint. rewrite sepcon_comm.
      now apply produce_sound.
    Qed.

    Lemma call_contract_sound {Γ Δ τ} (δΓ : LocalStore Γ) (δΔ : LocalStore Δ)
          (h : SCHeap) (POST : Lit τ -> LocalStore Γ -> L)
          (c : SepContract Δ τ) :
      call_contract c δΔ (fun a => liftP (POST a)) δΓ h ->
      CTriple δΔ (interpret_scheap h) (fun v => POST v δΓ) c.
    Proof.
      (* destruct c as [Σe δe req result ens]. *)
      (* unfold call_contract. unfold bind. rewrite cmut_wp_bind. *)
      (* rewrite cmut_wp_angelic_ctx. *)
      (* intros [ι Hwp]; revert Hwp. *)
      (* rewrite cmut_wp_bind_right. *)
      (* rewrite cmut_wp_assert_formulas. *)
      (* intros [Hfmls Hwp]; revert Hwp. *)
      (* rewrite cmut_wp_bind_right. *)
      (* pose (fun δ => ∀ v, interpret_assertion ens (env_snoc ι (result,_) v) -✱ POST v δ) as frame. *)
      (* intros HYP. *)
      (* assert (interpret_scheap h ⊢ frame δΓ ✱ interpret_assertion req ι ). *)
      (* { rewrite sepcon_comm. *)
      (*   apply (cmut_consume_sound frame). *)
      (*   revert HYP. apply cmut_wp_monotonic. *)
      (*   intros ? δ2 h2. *)
      (*   rewrite cmut_wp_bind, cmut_wp_demonic. *)
      (*   intros HYP. *)
      (*   apply lall_right; intro v. *)
      (*   specialize (HYP v). *)
      (*   rewrite cmut_wp_bind_right in HYP. *)
      (*   now apply wand_sepcon_adjoint, cmut_produce_sound. *)
      (* } *)
      (* constructor 1 with ι (frame δΓ); auto. *)
      (* - apply inst_formula_eqs in Hfmls. *)
      (*   now rewrite inst_lift in Hfmls. *)
      (* - intro v. *)
      (*   apply wand_sepcon_adjoint. *)
      (*   apply lall_left with v. *)
      (*   apply entails_refl. *)
    Admitted.

    Check @exec.

    Lemma exec_monotonic {Γ τ} (s : Stm Γ τ)
      (P Q : Lit τ -> LocalStore Γ -> SCHeap -> Prop)
      (PQ : forall x δ h, P x δ h -> Q x δ h) :
      forall δ h,
        exec s P δ h ->
        exec s Q δ h.
    Proof.
    Admitted.

    Lemma exec_sound {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> LocalStore Γ -> L) :
      forall (δ1 : LocalStore Γ) (h1 : SCHeap),
        exec s (fun v => liftP (POST v)) δ1 h1 ->
        δ1 ⊢ ⦃ interpret_scheap h1 ⦄ s ⦃ POST ⦄.
    Proof.
      induction s; intros ? ?; cbn;
        cbv [pushspops pushs_local pops_local
             pushpop push_local pop_local
             eval_exp get_local put_local
             bind_right bind_left bind];
        cbn; intros HYP.

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
        revert HYP. apply exec_monotonic.
        intros v2 δ2 h2. unfold state, pure. intros HYP.
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
          now apply call_contract_sound.
        + contradict HYP.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_call_external *)
        apply rule_stm_call_external_backwards.
        now apply call_contract_sound.

      - (* stm_if *)
        admit.
        (* rewrite cmut_wp_demonic_match_bool in HYP. *)
        (* apply rule_stm_if; apply rule_pull; intro Heval; rewrite Heval in *; auto. *)

      - (* stm_seq *)
        eapply rule_consequence_left.
        eapply rule_stm_seq; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs1; clear IHs1.
        revert HYP; apply exec_monotonic.
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
        + unfold state, pure in HYP.
          now apply IHs2.

      - (* stm_match_sum *)
        unfold state, pure in HYP.
        apply rule_stm_match_sum; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_prod *)
        unfold state, pure in HYP.
        apply rule_stm_match_prod; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP.
        now apply IHs.

      - (* stm_match_enum *)
        now apply rule_stm_match_enum, H.

      - (* stm_match_tuple *)
        now apply rule_stm_match_tuple, IHs.

      - (* stm_match_union *)
        unfold state, pure in HYP.
        apply rule_stm_match_union; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval, 𝑼_unfold_fold in HYP.
        now apply H.

      - (* stm_match_record *)
        now apply rule_stm_match_record, IHs.

      - (* stm_read_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_read_register_backwards (v := v)).
        apply (@consume_chunk_sound Γ (scchunk_ptsreg reg v) (fun δ => _ -✱ POST _ δ)).
        revert HYP. admit.
        (* apply cmut_wp_monotonic. intros _ δ2 h2. *)
        (* unfold cmut_produce_chunk. rewrite cmut_wp_bind, cmut_wp_state, cmut_wp_pure. *)
        (* unfold liftP; cbn. now rewrite sepcon_comm, wand_sepcon_adjoint. *)

      - (* stm_write_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        apply (@consume_chunk_sound Γ (scchunk_ptsreg reg v) (fun δ => _ -✱ POST _ δ)).
        revert HYP. admit.
        (* apply cmut_wp_monotonic. intros _ δ2 h2. *)
        (* unfold cmut_produce_chunk. rewrite cmut_wp_bind, cmut_wp_state, cmut_wp_pure. *)
        (* unfold liftP; cbn. now rewrite sepcon_comm, wand_sepcon_adjoint. *)

      - (* stm_bind *)
        eapply rule_consequence_left.
        eapply rule_stm_bind; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs; clear IHs.
        revert HYP. apply exec_monotonic.
        intros v2 δ2 h2 HYP; cbn.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        now apply H.
      - constructor. auto.
    Admitted.

    Lemma exec_sound' {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> LocalStore Γ -> L) :
      forall δ1 h1,
        exec s (fun v2 => liftP (POST v2)) δ1 h1 ->
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

    Lemma contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      CMut.ValidContract c body ->
      LOG.ValidContract c body.
    Proof.
      unfold CMut.ValidContract, LOG.ValidContract.
      unfold inst_contract_localstore.
      unfold exec_contract, bind_right, bind.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      - specialize (HYP ι). remember (inst δΣ ι) as δ.
        eapply rule_consequence_left.
        apply rule_wp.
        apply entails_trans with
            (interpret_scheap nil -✱ WP body (fun (v : Lit τ) (_ : LocalStore Δ) => interpret_assertion ens (env_snoc ι (result,τ) v)) δ).
        apply produce_sound'.
        2: {
          rewrite <- sepcon_emp.
          apply wand_sepcon_adjoint.
          apply entails_refl.
        }
        revert HYP. apply produce_monotonic.
        intros _ δ2 h2 HYP. apply exec_sound'.
        revert HYP. apply exec_monotonic.
        intros v3 δ3 h3 HYP.
        enough (interpret_scheap h3 ⊢ interpret_assertion ens (env_snoc ι (result,τ) v3) ✱ emp)
          by now rewrite sepcon_emp in H.
        change emp with ((fun _ => emp) δ3).
        apply (consume_sound (asn := ens)).
        revert HYP. apply consume_monotonic.
        intros _ δ4 h4 HYP. unfold liftP.
    Admitted.

  End Soundness.

End Soundness.
