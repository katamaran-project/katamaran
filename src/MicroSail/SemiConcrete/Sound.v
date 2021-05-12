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

    Lemma scmut_wp_angelick_list {A B Γ1 Γ2} (msg : string) (xs : list A) (k : A -> SCMut Γ1 Γ2 B) (POST : B -> SCProp Γ2) :
      forall δ h,
        scmut_wp (scmut_angelick_list msg xs k) POST δ h <->
        (exists x : A, List.In x xs /\ scmut_wp (k x) POST δ h).
    Proof.
      intros δ h. unfold scmut_wp, scmut_angelick_list; cbn.
      rewrite outcome_satisfy_angelick_list. intuition.
    Qed.

    Opaque env_tail.
    Opaque match_chunk_eqb.

    (* Local Ltac sound_inster := *)
    (*   match goal with *)
    (*   | [ IH: outcome_satisfy (scmut_exec ?s _) _ |- *)
    (*       outcome_satisfy (scmut_exec ?s _) _ ] => *)
    (*     refine (outcome_satisfy_monotonic _ _ IH); clear IH *)
    (*   | [ IH: outcome_satisfy (scmut_consume _ ?a _) _ |- *)
    (*       outcome_satisfy (scmut_consume _ ?a _) _ ] => *)
    (*     refine (outcome_satisfy_monotonic _ _ IH); clear IH *)
    (*   | [ IH: outcome_satisfy (scmut_produce _ ?a _) _ |- *)
    (*       outcome_satisfy (scmut_produce _ ?a _) _ ] => *)
    (*     refine (outcome_satisfy_monotonic _ _ IH); clear IH *)
    (*   | [ IH: outcome_satisfy ?o _ |- *)
    (*       outcome_satisfy ?o _ ] => *)
    (*     refine (outcome_satisfy_monotonic _ _ IH); clear IH *)
    (*   end. *)

    Definition liftP {Γ} (POST : LocalStore Γ -> L) : SCProp Γ :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Lemma scmut_consume_chunk_sound {Γ} (c : SCChunk) (POST : LocalStore Γ -> L) :
      forall δ h,
        scmut_wp (scmut_consume_chunk c) (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_scchunk c ✱ POST δ.
    Proof.
      intros δ h.
      unfold scmut_consume_chunk, scmut_get_heap.
      rewrite scmut_wp_bind, scmut_wp_state, scmut_wp_angelick_list.
      intros (hr & H1 & H2). unfold extract_chunk_eqb in H1.
      rewrite List.in_map_iff in H1. destruct H1 as [[c1 h1] [Heq H1]].
      rewrite List.filter_In in H1. destruct H1 as [HIn Hmatch].
      apply (Bool.reflect_iff _ _ (match_chunk_eqb_spec _ _)) in Hmatch.
      cbn in Heq. subst.
      apply in_heap_extractions in HIn; rewrite HIn; clear HIn.
      apply sepcon_entails.
      apply entails_refl.
      assumption.
    Qed.

    Lemma scmut_wp_bind_right {Γ1 Γ2 Γ3 A B} (ma : SCMut Γ1 Γ2 A) (mb : SCMut Γ2 Γ3 B)
      (POST : B -> SCProp Γ3) :
      forall δ h,
        scmut_wp (scmut_bind_right ma mb) POST δ h <->
        scmut_wp ma (fun _ => scmut_wp mb POST) δ h.
    Proof. intros δ h. unfold scmut_bind_right. now rewrite scmut_wp_bind. Qed.

    Lemma scmut_wp_assert_formula {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : unit -> SCProp Γ ) :
      forall δ h,
        scmut_wp (scmut_assert_formula ι fml) POST δ h <->
        inst ι fml /\ POST tt δ h.
    Proof. reflexivity. Qed.

    Lemma scmut_wp_assume_formula {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : unit -> SCProp Γ ) :
      forall δ h,
        scmut_wp (scmut_assume_formula ι fml) POST δ h <->
        (inst (A := Prop) ι fml -> POST tt δ h).
    Proof. reflexivity. Qed.

    Lemma scmut_wp_assert_formulak {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      {k : SCMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) :
      forall δ h,
        scmut_wp (scmut_assert_formulak ι fml k) POST δ h <->
        inst ι fml /\ scmut_wp k POST δ h.
    Proof. reflexivity. Qed.

    Lemma scmut_wp_assert_formulask {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fmls : list (Formula Σ)}
      {k : SCMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) :
      forall δ h,
        scmut_wp (scmut_assert_formulask ι fmls k) POST δ h <->
        inst (T := PathCondition) ι fmls /\ scmut_wp k POST δ h.
    Proof.
      intros δ h. unfold scmut_assert_formulask.
      induction fmls; cbn.
      - clear. intuition. constructor.
      - rewrite inst_pathcondition_cons, scmut_wp_assert_formulak, IHfmls.
        clear. intuition.
    Qed.

    Lemma scmut_assert_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : LocalStore Γ -> L) :
      forall δ h,
        scmut_wp
          (scmut_assert_formula ι fml)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ⊢ !! inst ι fml ∧ emp ✱ POST δ.
    Proof.
      intros ? ?. rewrite scmut_wp_assert_formula.
      intros [Hfml HP].
      rewrite <- sepcon_emp at 1.
      rewrite sepcon_comm.
      apply sepcon_entails; auto.
      apply land_right.
      apply lprop_right; assumption.
      apply entails_refl.
    Qed.

    Lemma scmut_assume_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : LocalStore Γ -> L) :
      forall δ h,
        scmut_wp
          (scmut_assume_formula ι fml)
          (fun _ => liftP POST) δ h ->
      interpret_scheap h ✱ !! inst ι fml ∧ emp ⊢ POST δ.
    Proof.
      intros ? ?. rewrite scmut_wp_assume_formula.
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

    Opaque scmut_assert_formula.
    Opaque scmut_assume_formula.
    Opaque scmut_consume_chunk.

    Lemma scmut_consume_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        scmut_wp (scmut_consume ι asn) (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_assertion ι asn ✱ POST δ.
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1 h1.
      - now apply scmut_assert_formula_sound.
      - destruct c; now apply scmut_consume_chunk_sound.
      - unfold scmut_assume_term.
        rewrite scmut_wp_demonic_binary, ?scmut_wp_bind_right,
          ?scmut_wp_assume_formula. cbn.
        change (inst_term ι b) with (inst ι b).
        intros [H1 H2]. destruct (inst ι b) eqn:?; auto.
      - auto.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - rewrite scmut_wp_bind_right. intros Hwp.
        rewrite sepcon_assoc.
        apply (IHasn1 ι (fun δ => interpret_assertion ι asn2 ✱ POST δ) δ1 h1); clear IHasn1.
        revert Hwp. apply scmut_wp_monotonic. intros _ δ2 h2.
        now apply (IHasn2 ι POST δ2 h2).
      - rewrite scmut_wp_angelic. intros [v Hwp].
        apply (entails_trans (interpret_scheap h1) (interpret_assertion (env_snoc ι (ς , τ) v) asn ✱ POST δ1)).
        + now apply IHasn.
        + apply sepcon_entails.
          apply lex_right with v, entails_refl.
          apply entails_refl.
      - admit.
    Admitted.

    Lemma scmut_produce_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        scmut_wp (scmut_produce ι asn) (fun _ => liftP POST) δ h ->
        interpret_scheap h ✱ interpret_assertion ι asn ⊢ POST δ.
    Proof.
      revert POST. induction asn; cbn - [scmut_assume_formula]; intros POST δ1 h1.
      - now apply scmut_assume_formula_sound.
      - rewrite sepcon_comm.
        destruct c; now cbn in *.
      - unfold scmut_assume_term.
        rewrite scmut_wp_demonic_binary, ?scmut_wp_bind_right,
          ?scmut_wp_assume_formula. cbn.
        change (inst_term ι b) with (inst ι b).
        intros [H1 H2]. destruct (inst ι b) eqn:?; auto.
      - auto.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - rewrite scmut_wp_bind_right. intros Hwp.
        rewrite <- sepcon_assoc.
        apply wand_sepcon_adjoint.
        apply (IHasn1 ι (fun δ => interpret_assertion ι asn2 -✱ POST δ) δ1 h1 ); clear IHasn1.
        revert Hwp. apply scmut_wp_monotonic. intros _ δ2 h2 Hwp.
        unfold liftP. apply wand_sepcon_adjoint.
        now apply (IHasn2 ι POST δ2 h2).
      - rewrite scmut_wp_demonic. intros Hwp.
        rewrite sepcon_comm.
        apply wand_sepcon_adjoint.
        apply lex_left. intro v.
        apply wand_sepcon_adjoint.
        rewrite sepcon_comm.
        now apply IHasn.
      - admit.
    Admitted.

    Lemma scmut_produce_sound' {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : LocalStore Γ -> L) :
      forall δ h,
        scmut_wp (scmut_produce ι asn) (fun _ => liftP POST) δ h ->
        interpret_assertion ι asn ⊢ interpret_scheap h -✱ POST δ.
    Proof.
      intros. apply wand_sepcon_adjoint. rewrite sepcon_comm.
      now apply scmut_produce_sound.
    Qed.

    Lemma scmut_call_sound {Γ Δ τ} (δΓ : LocalStore Γ) (δΔ : LocalStore Δ)
          (h : SCHeap) (POST : Lit τ -> LocalStore Γ -> L)
          (c : SepContract Δ τ) :
      scmut_wp
        (scmut_call c δΔ)
        (fun a => liftP (POST a))
        δΓ h ->
      CTriple δΔ (interpret_scheap h) (fun v => POST v δΓ) c.
    Proof.
      destruct c as [Σe δe req result ens] eqn:Heqc.
      unfold scmut_call. rewrite scmut_wp_angelic.
      intros [ι Hwp]; revert Hwp.
      rewrite scmut_wp_assert_formulask.
      intros [Hfmls Hwp]; revert Hwp.
      rewrite scmut_wp_bind_right.
      pose (fun δ => ∀ v, interpret_assertion (env_snoc ι (result,_) v) ens -✱ POST v δ) as frame.
      intros HYP.
      assert (interpret_scheap h ⊢ frame δΓ ✱ interpret_assertion ι req ).
      { rewrite sepcon_comm.
        apply (scmut_consume_sound frame).
        revert HYP. apply scmut_wp_monotonic.
        intros ? δ2 h2. rewrite scmut_wp_demonic.
        intros HYP.
        apply lall_right; intro v.
        specialize (HYP v).
        rewrite scmut_wp_bind_right in HYP.
        now apply wand_sepcon_adjoint, scmut_produce_sound.
      }
      constructor 1 with ι (frame δΓ); auto.
      - clear - Hfmls. admit.
      - intro v.
        apply wand_sepcon_adjoint.
        apply lall_left with v.
        apply entails_refl.
    Admitted.

    Lemma scmut_exec_sound {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> LocalStore Γ -> L) :
      forall (δ1 : LocalStore Γ) (h1 : SCHeap),
        scmut_wp (scmut_exec s) (fun v => liftP (POST v)) δ1 h1 ->
        δ1 ⊢ ⦃ interpret_scheap h1 ⦄ s ⦃ POST ⦄.
    Proof.
      induction s; intros ? ?; cbn;
        unfold scmut_pushspops, scmut_pushs_local, scmut_pops_local,
          scmut_pushpop, scmut_push_local, scmut_pop_local,
          scmut_eval_exp, scmut_get_local, scmut_put_local,
          scmut_bind_right, scmut_bind_left;
        repeat (rewrite ?scmut_wp_bind, ?scmut_wp_state; cbn); intros HYP.

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
        revert HYP. apply scmut_wp_monotonic.
        intros v2 δ2 h2.
        rewrite ?scmut_wp_bind, ?scmut_wp_state. cbn.
        rewrite scmut_wp_bind. intros HYP.

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
          now apply scmut_call_sound.
        + contradict HYP.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_call_external *)
        apply rule_stm_call_external_backwards.
        now apply scmut_call_sound.

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
        revert HYP; apply scmut_wp_monotonic.
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
        + rewrite scmut_wp_bind, scmut_wp_state in HYP; cbn in HYP.
          rewrite scmut_wp_bind in HYP.
          now apply IHs2.

      - (* stm_match_sum *)
        apply rule_stm_match_sum; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP;
            rewrite scmut_wp_bind, scmut_wp_state in HYP; cbn in HYP;
              rewrite scmut_wp_bind in HYP.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_pair *)
        apply rule_stm_match_pair; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP;
            rewrite scmut_wp_bind, scmut_wp_state in HYP; cbn in HYP;
              rewrite scmut_wp_bind in HYP.
        now apply IHs.

      - (* stm_match_enum *)
        now apply rule_stm_match_enum, H.

      - (* stm_match_tuple *)
        now apply rule_stm_match_tuple, IHs.

      - (* stm_match_union *)
        apply rule_stm_match_union; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval, 𝑼_unfold_fold in HYP;
            rewrite scmut_wp_bind, scmut_wp_state in HYP; cbn in HYP;
              rewrite scmut_wp_bind in HYP.
        now apply H.

      - (* stm_match_record *)
        now apply rule_stm_match_record, IHs.

      - (* stm_read_register *)
        rewrite scmut_wp_angelic in HYP.
        destruct HYP as [v HYP].
        rewrite scmut_wp_bind in HYP.
        eapply rule_consequence_left.
        apply (rule_stm_read_register_backwards (v := v)).
        unfold liftP, scmut_wp, scmut_pure, scmut_bind in HYP.
        setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP.
        setoid_rewrite sepcon_comm in HYP.
        setoid_rewrite wand_sepcon_adjoint in HYP.
        now apply (scmut_consume_chunk_sound _ (fun δ => _ -✱ POST _ δ)) in HYP.

      - (* stm_write_register *)
        rewrite scmut_wp_angelic in HYP.
        destruct HYP as [v HYP].
        rewrite scmut_wp_bind in HYP.
        unfold liftP, scmut_wp, scmut_pure, scmut_bind in HYP.
        setoid_rewrite outcome_satisfy_bind in HYP; cbn in HYP.
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        setoid_rewrite sepcon_comm in HYP.
        setoid_rewrite wand_sepcon_adjoint in HYP.
        now apply (scmut_consume_chunk_sound _ (fun δ => _ -✱ POST _ δ)) in HYP.

      - (* stm_bind *)
        eapply rule_consequence_left.
        eapply rule_stm_bind; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs; clear IHs.
        revert HYP. apply scmut_wp_monotonic.
        intros v2 δ2 h2 HYP; cbn.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        now apply H.
      - constructor. auto.
    Qed.

    Lemma scmut_exec_sound' {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> LocalStore Γ -> L) :
      forall δ1 h1,
        scmut_wp (scmut_exec s) (fun v2 => liftP (POST v2)) δ1 h1 ->
        liftP (WP s POST) δ1 h1.
    Proof.
      cbn in *; intros.
      unfold WP.
      apply scmut_exec_sound in H.
      apply lex_right with (interpret_scheap h1).
      apply land_right.
      reflexivity.
      now apply lprop_right.
    Qed.

    Lemma scmut_contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractSCMut c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractSCMut, ValidContract.
      unfold inst_contract_localstore.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      - specialize (HYP ι). remember (inst ι δΣ) as δ.
        rewrite scmut_wp_bind_right in HYP.
        eapply rule_consequence_left.
        apply rule_wp.
        apply entails_trans with
            (interpret_scheap nil -✱ WP body (fun (v : Lit τ) (_ : LocalStore Δ) => interpret_assertion (env_snoc ι (result,τ) v) ens) δ).
        apply scmut_produce_sound'.
        2: {
          rewrite <- sepcon_emp.
          apply wand_sepcon_adjoint.
          apply entails_refl.
        }
        revert HYP. apply scmut_wp_monotonic.
        intros _ δ2 h2 HYP. apply scmut_exec_sound'.
        revert HYP. rewrite scmut_wp_bind. apply scmut_wp_monotonic.
        intros v3 δ3 h3 HYP.
        enough (interpret_scheap h3 ⊢ interpret_assertion (env_snoc ι (result,τ) v3) ens ✱ emp)
          by now rewrite sepcon_emp in H.
        change emp with ((fun _ => emp) δ3).
        apply (scmut_consume_sound (asn := ens)).
        revert HYP. apply scmut_wp_monotonic.
        intros _ δ4 h4 HYP. unfold liftP.
    Admitted.

  End Soundness.

End Soundness.
