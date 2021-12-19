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
     Program.Equality
     Strings.String
     ZArith.ZArith.

From Katamaran Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     SemiConcrete.Mutator.

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

    Fixpoint interpret_scchunk (c : SCChunk) : L :=
      match c with
      | scchunk_user p vs => luser p vs
      | scchunk_ptsreg r v => lptsreg r v
      | scchunk_conj c1 c2 => sepcon (interpret_scchunk c1) (interpret_scchunk c2)
      | scchunk_wand c1 c2 => wand (interpret_scchunk c1) (interpret_scchunk c2)
      end.

    Definition interpret_scheap : SCHeap -> L :=
      List.fold_right (fun c h => interpret_scchunk c ✱ h) emp.
    Global Arguments interpret_scheap !h.

    Lemma scchunk_duplicate (c : SCChunk) :
      is_duplicable c = true -> interpret_scchunk c ⊢ interpret_scchunk c ✱ interpret_scchunk c.
    Proof.
      destruct c; cbn; try discriminate.
      eauto using lduplicate.
    Qed.

    Lemma in_heap_extractions {h : SCHeap} {c1 h1} (hyp : List.In (c1 , h1) (heap_extractions h)) :
      interpret_scheap h ⊣⊢s interpret_scchunk c1 ✱ interpret_scheap h1.
    Proof.
      revert c1 h1 hyp.
      induction h; cbn -[is_duplicable]; intros.
      - contradict hyp.
      - destruct hyp as [hyp|hyp].
        + destruct (is_duplicable a) eqn:Heqdup;
            inversion hyp; subst; clear hyp.
          { split.
            - transitivity (interpret_scchunk c1 ✱ interpret_scchunk c1 ✱ interpret_scheap h).
              apply sepcon_entails; [|reflexivity].
              apply scchunk_duplicate; assumption.
              rewrite sepcon_assoc. reflexivity.
            - apply sepcon_entails; [reflexivity|]. cbn.
              transitivity (emp ✱ interpret_scheap h).
              apply sepcon_entails; [|reflexivity].
              apply sep_leak.
              now rewrite sepcon_comm, sepcon_emp.
          }
          { split; apply entails_refl. }
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

    Definition liftP {Γ} (POST : CStore Γ -> L) : CStore Γ -> SCHeap -> Prop :=
      fun δ h => interpret_scheap h ⊢ POST δ.

    Import CMut.

    Lemma consume_chunk_sound {Γ} (c : SCChunk) (POST : CStore Γ -> L) :
      forall δ h,
        consume_chunk c (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_scchunk c ✱ POST δ.
    Proof.
      cbv [bind get_heap consume_chunk angelic_list CDijk.assert_formula
           dijkstra bind_right assert_formula put_heap].
      intros δ h.
      rewrite CDijk.wp_angelic_list.
      intros [[c' h'] [HIn [Heq HPOST]]]. subst c'.
      apply in_heap_extractions in HIn; rewrite HIn; clear HIn.
      apply sepcon_entails.
      apply entails_refl.
      apply HPOST.
    Qed.

    Lemma assert_formula_sound {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ}
      (POST : CStore Γ -> L) :
      forall δ h,
        assert_formula (inst fml ι)
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
      (POST : CStore Γ -> L) :
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

    Definition Monotonic {Γ1 Γ2 A} (m : CMut Γ1 Γ2 A) : Prop :=
      forall
        (P Q : A -> CStore Γ2 -> SCHeap -> Prop)
        (PQ : forall x δ h, P x δ h -> Q x δ h),
        forall δ h, m P δ h -> m Q δ h.

    (* Stronger version for those that do not change the store. *)
    Definition Monotonic' {Γ A} (m : CMut Γ Γ A) : Prop :=
      forall δ
        (P Q : A -> CStore Γ -> SCHeap -> Prop)
        (PQ : forall x h, P x δ h -> Q x δ h),
        forall h, m P δ h -> m Q δ h.

    Lemma consume_chunk_monotonic {Γ} {c : SCChunk} :
      Monotonic' (consume_chunk (Γ := Γ) c).
    Proof.
      cbv [Monotonic' consume_chunk bind get_heap angelic_list dijkstra
           bind_right assert_formula put_heap CDijk.assert_formula].
      intros δ P Q PQ h. rewrite ?CDijk.wp_angelic_list.
      intros [ch' Hwp]; exists ch'; revert Hwp.
      destruct ch'. intuition.
    Qed.

    Lemma consume_monotonic {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} :
      Monotonic' (consume (Γ := Γ) ι asn).
    Proof.
      intros δ. induction asn; cbn; intros * PQ *.
      - unfold assert_formula, dijkstra, CDijk.assert_formula.
        intuition.
      - now apply consume_chunk_monotonic.
      - rewrite ?wp_angelic_match_bool.
        destruct (inst b ι); cbn; eauto.
      - rewrite ?wp_angelic_match_enum; eauto.
      - rewrite ?wp_angelic_match_sum.
        destruct (inst s ι); cbn; eauto.
      - rewrite ?wp_angelic_match_list.
        destruct (inst s ι); cbn; eauto.
      - rewrite ?wp_angelic_match_prod.
        destruct (inst s ι); cbn; eauto.
      - rewrite ?wp_angelic_match_tuple; eauto.
      - rewrite ?wp_angelic_match_record; eauto.
      - rewrite ?wp_angelic_match_union.
        destruct (𝑼_unfold (inst s ι)); eauto.
      - unfold bind_right, bind.
        apply IHasn1; eauto.
      - intros [|].
        + left. apply IHasn1 with (P := P); assumption.
        + right. apply IHasn2 with (P := P); assumption.
      - unfold bind, angelic.
        intros [v ?]; exists v; eauto.
      - unfold pure; eauto.
    Qed.

    Lemma produce_monotonic {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} :
      Monotonic' (produce (Γ := Γ) ι asn).
    Proof.
      intros δ. induction asn; cbn; intros * PQ *.
      - unfold assume_formula, dijkstra, CDijk.assume_formula.
        intuition.
      - unfold produce_chunk; eauto.
      - rewrite ?wp_demonic_match_bool.
        destruct (inst b ι); cbn; eauto.
      - rewrite ?wp_demonic_match_enum; eauto.
      - rewrite ?wp_demonic_match_sum.
        destruct (inst s ι); cbn; eauto.
      - rewrite ?wp_demonic_match_list.
        destruct (inst s ι); cbn; eauto.
      - rewrite ?wp_demonic_match_prod.
        destruct (inst s ι); cbn; eauto.
      - rewrite ?wp_demonic_match_tuple; eauto.
      - rewrite ?wp_demonic_match_record; eauto.
      - rewrite ?wp_demonic_match_union.
        destruct (𝑼_unfold (inst s ι)); eauto.
      - unfold bind_right, bind.
        apply IHasn1; eauto.
      - intros [Hasn1 Hasn2].
        split.
        + apply IHasn1 with (P := P); assumption.
        + apply IHasn2 with (P := P); assumption.
      - unfold bind, demonic. eauto.
      - unfold pure; eauto.
    Qed.

    Lemma interpret_scchunk_inst {Σ} (c : Chunk Σ) (ι : SymInstance Σ) :
      interpret_scchunk (inst c ι) = interpret_chunk c ι.
    Proof.
      induction c; cbn [interpret_chunk];
        try rewrite <- IHc1, <- IHc2; reflexivity.
    Qed.

    Lemma consume_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        consume ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ⊢ interpret_assertion asn ι ✱ POST δ.
    Proof.
      revert POST. induction asn; cbn - [inst inst_term]; intros POST δ1 h1.
      - now apply assert_formula_sound.
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
        destruct (𝑼_unfold (inst s ι)); auto.
      - unfold bind_right, bind. intros Hwp. rewrite sepcon_assoc.
        apply (IHasn1 ι (fun δ => interpret_assertion asn2 ι ✱ POST δ) δ1 h1); clear IHasn1.
        revert Hwp. apply consume_monotonic. intros _ h2.
        now apply (IHasn2 ι POST δ1 h2).
      - intros []; rewrite sep_disj_distr.
        + apply lor_right1; apply IHasn1; assumption.
        + apply lor_right2; apply IHasn2; assumption.
      - intros [v Hwp].
        apply (entails_trans (interpret_scheap h1) (interpret_assertion asn (env_snoc ι (ς , τ) v) ✱ POST δ1)).
        + now apply IHasn.
        + apply sepcon_entails.
          apply lex_right with v, entails_refl.
          apply entails_refl.
      - now rewrite sepcon_comm, sepcon_emp.
    Qed.

    Lemma produce_sound {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        interpret_scheap h ✱ interpret_assertion asn ι ⊢ POST δ.
    Proof.
      revert POST. induction asn; cbn - [assume_formula]; intros POST δ1 h1.
      - now apply assume_formula_sound.
      - rewrite sepcon_comm.
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
        destruct (𝑼_unfold (inst s ι)); auto.
      - unfold bind_right, bind. intros Hwp.
        rewrite <- sepcon_assoc.
        apply wand_sepcon_adjoint.
        apply (IHasn1 ι (fun δ => interpret_assertion asn2 ι -✱ POST δ) δ1 h1 ); clear IHasn1.
        revert Hwp. apply produce_monotonic. intros _ h2 Hwp.
        unfold liftP. apply wand_sepcon_adjoint.
        now apply (IHasn2 ι POST δ1 h2).
      - intros [].
        rewrite sepcon_comm.
        rewrite sep_disj_distr.
        apply lor_left; rewrite sepcon_comm.
        + apply IHasn1; assumption.
        + apply IHasn2; assumption.
      - intros Hwp.
        rewrite sepcon_comm.
        apply wand_sepcon_adjoint.
        apply lex_left. intro v.
        apply wand_sepcon_adjoint.
        rewrite sepcon_comm.
        now apply IHasn.
      - now rewrite sepcon_emp.
    Qed.

    Lemma produce_sound' {Γ Σ} {ι : SymInstance Σ} {asn : Assertion Σ} (POST : CStore Γ -> L) :
      forall δ h,
        produce ι asn (fun _ => liftP POST) δ h ->
        interpret_assertion asn ι ⊢ interpret_scheap h -✱ POST δ.
    Proof.
      intros. apply wand_sepcon_adjoint. rewrite sepcon_comm.
      now apply produce_sound.
    Qed.

    Lemma call_contract_sound {Γ Δ τ} (δΓ : CStore Γ) (δΔ : CStore Δ)
          (h : SCHeap) (POST : Lit τ -> CStore Γ -> L)
          (c : SepContract Δ τ) :
      call_contract c δΔ (fun a => liftP (POST a)) δΓ h ->
      CTriple δΔ (interpret_scheap h) (fun v => POST v δΓ) c.
    Proof.
      destruct c as [Σe δe req result ens].
      unfold call_contract. unfold bind_right, bind.
      unfold angelic_ctx, dijkstra.
      rewrite CDijk.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      unfold assert_formula, dijkstra, CDijk.assert_formula.
      (* rewrite CDijk.wp_assert_formulas. *)
      intros [Hfmls Hwp]; revert Hwp.
      pose (fun δ => ∀ v, interpret_assertion ens (env_snoc ι (result,_) v) -✱ POST v δ) as frame.
      intros HYP.
      assert (interpret_scheap h ⊢ frame δΓ ✱ interpret_assertion req ι ).
      { rewrite sepcon_comm.
        apply (consume_sound frame).
        revert HYP. apply consume_monotonic.
        intros ? h2. unfold demonic.
        intros HYP.
        apply lall_right; intro v.
        specialize (HYP v).
        now apply wand_sepcon_adjoint, produce_sound.
      }
      constructor 1 with ι (frame δΓ); auto.
      (* - apply inst_formula_eqs in Hfmls. *)
      (*   now rewrite inst_lift in Hfmls. *)
      - intro v.
        apply wand_sepcon_adjoint.
        apply lall_left with v.
        apply entails_refl.
    Qed.

    Lemma call_contract_monotonic {Γ Δ τ} (c : SepContract Δ τ) (δΔ : CStore Δ) :
      Monotonic (call_contract (Γ := Γ) c δΔ).
    Proof.
      destruct c; intros P Q PQ δ h;
        cbv [call_contract bind_right bind pure demonic
             angelic_ctx demonic dijkstra assert_formula
             CDijk.assert_formula].
      rewrite ?CDijk.wp_angelic_ctx.
      intros [ι Hwp]. exists ι. revert Hwp.
      (* rewrite ?CDijk.wp_assert_formulas. *)
      intros [Hfmls Hwp]; split; auto; revert Hwp.
      apply consume_monotonic. intros _ ? Hwp v.
      specialize (Hwp v); revert Hwp.
      apply produce_monotonic; auto.
    Qed.

    Lemma call_lemma_sound {Γ Δ} (δΓ : CStore Γ) (δΔ : CStore Δ)
          (h : SCHeap) (POST : CStore Γ -> L)
          (lem : Lemma Δ) :
      call_lemma lem δΔ (fun _ : unit => liftP POST) δΓ h ->
      LTriple δΔ (interpret_scheap h) (POST δΓ) lem.
    Proof.
      destruct lem as [Σe δe req ens].
      unfold call_lemma. unfold bind_right, bind.
      unfold angelic_ctx, dijkstra.
      rewrite CDijk.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      unfold assert_formula, dijkstra, CDijk.assert_formula.
      intros [Hfmls HYP].
      pose (fun δ => interpret_assertion ens ι -✱ POST δ) as frame.
      assert (interpret_scheap h ⊢ frame δΓ ✱ interpret_assertion req ι ).
      { rewrite sepcon_comm.
        apply (consume_sound frame).
        revert HYP. apply consume_monotonic.
        intros _ h2 HYP. subst frame. unfold liftP.
        now apply wand_sepcon_adjoint, produce_sound.
      }
      constructor 1 with ι (frame δΓ); auto.
      - apply wand_sepcon_adjoint.
        apply entails_refl.
    Qed.

    Lemma call_lemma_monotonic {Γ Δ} (lem : Lemma Δ) (δΔ : CStore Δ) :
      Monotonic (call_lemma (Γ := Γ) lem δΔ).
    Proof.
      destruct lem; intros P Q PQ δ h;
        cbv [call_lemma bind_right bind
             angelic_ctx dijkstra assert_formula
             CDijk.assert_formula].
      rewrite ?CDijk.wp_angelic_ctx.
      intros [ι Hwp]. exists ι. revert Hwp.
      intros [Hfmls Hwp]; split; auto; revert Hwp.
      apply consume_monotonic. intros _ ?.
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
        cbv [pure bind_right bind angelic pushpop pushspops
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
      - rewrite ?wp_demonic_match_bool.
        destruct (eval e δ).
        apply IHs1; auto.
        apply IHs2; auto.
      - apply IHs1. intros ? ? ?. apply IHs2. auto.
      - intros HYP Heq. specialize (HYP Heq). revert HYP.
        apply IHs; auto.
      - auto.
      - rewrite ?wp_demonic_match_list.
        destruct (eval e δ).
        apply IHs1; auto.
        apply IHs2; auto.
      - rewrite ?wp_demonic_match_sum.
        destruct (eval e δ); cbn.
        apply IHs1; auto.
        apply IHs2; auto.
      - rewrite ?wp_demonic_match_prod.
        destruct (eval e δ); cbn.
        apply IHs; auto.
      - rewrite ?wp_demonic_match_enum.
        apply H; auto.
      - rewrite ?wp_demonic_match_tuple.
        apply IHs; auto.
      - rewrite ?wp_demonic_match_union.
        destruct (𝑼_unfold (eval e δ)).
        apply H; auto.
      - rewrite ?wp_demonic_match_record.
        apply IHs; auto.
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

    Definition SoundExec (rec : Exec) :=
      forall
        Γ σ (s : Stm Γ σ) (POST : Lit σ -> CStore Γ -> L)
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
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2. intros HYP.
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
        + unfold eval_exps in HYP.
          apply rec_sound in HYP.
          eapply rule_consequence_right.
          apply rule_stm_call_inline.
          apply HYP. cbn. intros v δ.
          rewrite lprop_float.
          apply limpl_and_adjoint.
          apply lprop_left. intros ->.
          apply limpl_and_adjoint.
          apply land_left2.
          apply entails_refl.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_foreign *)
        apply rule_stm_foreign_backwards.
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
        apply entails_refl.
        apply lprop_right.
        now apply IHs.

      - (* stm_if *)
        rewrite wp_demonic_match_bool in HYP.
        apply rule_stm_if; apply rule_pull; intro Heval; rewrite Heval in *; auto.

      - (* stm_seq *)
        eapply rule_consequence_left.
        eapply rule_stm_seq; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs1; clear IHs1.
        revert HYP; apply exec_aux_monotonic; auto.
        intros v2 δ2 h2 HYP.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        now apply IHs2.

      - (* stm_assert *)
        apply rule_stm_assert, rule_pull;
          intro Heval; rewrite Heval in HYP.
        specialize (HYP eq_refl). cbn in HYP.
        now apply IHs.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply ltrue_right.

      - (* stm_match_list *)
        rewrite wp_demonic_match_list in HYP.
        apply rule_stm_match_list; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_sum *)
        rewrite wp_demonic_match_sum in HYP.
        apply rule_stm_match_sum; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP.
        + now apply IHs1.
        + now apply IHs2.

      - (* stm_match_prod *)
        rewrite wp_demonic_match_prod in HYP.
        apply rule_stm_match_prod; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval in HYP; cbn in HYP.
        now apply IHs.

      - (* stm_match_enum *)
        rewrite wp_demonic_match_enum in HYP.
        now apply rule_stm_match_enum, H.

      - (* stm_match_tuple *)
        rewrite wp_demonic_match_tuple in HYP.
        now apply rule_stm_match_tuple, IHs.

      - (* stm_match_union *)
        rewrite wp_demonic_match_union in HYP.
        apply rule_stm_match_union; cbn; intros;
          apply rule_pull; intro Heval; rewrite Heval, 𝑼_unfold_fold in HYP.
        now apply H.

      - (* stm_match_record *)
        rewrite wp_demonic_match_record in HYP.
        now apply rule_stm_match_record, IHs.

      - (* stm_read_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_read_register_backwards (v := v)).
        apply (@consume_chunk_sound Γ (scchunk_ptsreg reg v) (fun δ => _ -✱ POST _ δ)).
        revert HYP. apply consume_chunk_monotonic.
        intros _ h2.
        unfold produce_chunk, liftP. cbn.
        now rewrite sepcon_comm, wand_sepcon_adjoint.

      - (* stm_write_register *)
        destruct HYP as [v HYP].
        eapply rule_consequence_left.
        apply (rule_stm_write_register_backwards (v := v)).
        apply (@consume_chunk_sound Γ (scchunk_ptsreg reg v) (fun δ => _ -✱ POST _ δ)).
        revert HYP. apply consume_chunk_monotonic.
        intros _ h2.
        unfold produce_chunk, liftP. cbn.
        now rewrite sepcon_comm, wand_sepcon_adjoint.

      - (* stm_bind *)
        eapply rule_consequence_left.
        eapply rule_stm_bind; intros; apply rule_wp.

        apply lex_right with (interpret_scheap h1).
        apply land_right.
        apply entails_refl.
        apply lprop_right.
        apply IHs; clear IHs.
        revert HYP. apply exec_aux_monotonic; auto.
        intros v2 δ2 h2 HYP; cbn.

        apply lex_right with (interpret_scheap h2).
        apply land_right.
        apply entails_refl.
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

    Lemma exec_sound' n {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> CStore Γ -> L) :
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

    Lemma contract_sound n {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      CMut.ValidContract n c body ->
      LOG.ValidContract c body.
    Proof.
      unfold CMut.ValidContract, LOG.ValidContract.
      unfold inst_contract_localstore.
      unfold exec_contract, bind_right, bind.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      rewrite Forall_forall in HYP.
      - specialize (HYP ι). remember (inst δΣ ι) as δ.
        eapply rule_consequence_left.
        apply rule_wp.
        apply entails_trans with
            (interpret_scheap nil -✱ WP body (fun (v : Lit τ) (_ : CStore Δ) => interpret_assertion ens (env_snoc ι (result,τ) v)) δ).
        apply produce_sound'.
        2: {
          rewrite <- sepcon_emp.
          apply wand_sepcon_adjoint.
          apply entails_refl.
        }
        revert HYP. apply produce_monotonic.
        intros _ h2 HYP. apply exec_sound' with n.
        revert HYP. apply exec_monotonic.
        intros v3 δ3 h3 HYP.
        enough (interpret_scheap h3 ⊢ interpret_assertion ens (env_snoc ι (result,τ) v3) ✱ emp)
          by now rewrite sepcon_emp in H.
        change emp with ((fun _ => emp) δ3).
        apply (consume_sound (asn := ens)).
        revert HYP. apply consume_monotonic.
        intros _ h4 HYP. unfold liftP.
        apply sep_leak.
    Qed.

    (* Print Assumptions contract_sound. *)

  End Soundness.

End Soundness.
