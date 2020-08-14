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
     Symbolic.Outcome.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit)
       (Import heapkit : HeapKit typekit termkit progkit assertkit contractkit).
  Module MUT := SemiConcrete typekit termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic typekit termkit progkit assertkit contractkit heapkit.
  Import LOG.

  Section Soundness.

    Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

    Definition inst_scchunk (c : SCChunk) : L :=
      match c with
      | scchunk_pred p vs => pred p vs
      | scchunk_ptsreg r v => ptsreg r v
      end.

    Definition inst_scheap (h : SCHeap) : L :=
      List.fold_right (fun c h => inst_scchunk c ∧ h) ltrue h.

    Local Opaque inst_scheap.

    Fixpoint outcome_satisfy_natded {A : Type} (o : Outcome A)
                (P : A -> L) {struct o} : L :=
      match o with
      | outcome_pure a => P a
      | @outcome_angelic _ I0 os =>
        ∃ i : I0, outcome_satisfy_natded (os i) P
      | @outcome_demonic _ IO os =>
        ∀ i : IO, outcome_satisfy_natded (os i) P
      | outcome_angelic_binary o1 o2 =>
        outcome_satisfy_natded o1 P ∨ outcome_satisfy_natded o2 P
      | outcome_demonic_binary o1 o2 =>
        outcome_satisfy_natded o1 P ∧ outcome_satisfy_natded o2 P
      | outcome_fail s => lfalse
    end.

    Axiom outcome_satisfy_natded_bind :
      forall {A B : Type} (o : Outcome A) (f : A -> Outcome B) (P : B -> L),
        outcome_satisfy_natded (outcome_bind o f) P ⊣⊢
        outcome_satisfy_natded o (fun a => outcome_satisfy_natded (f a) P).

    Lemma rule_outcome_satisfy {Γ σ} (δ : LocalStore Γ)
          {A : Type} (o : Outcome A) (P : A -> L) (Q : A -> Lit σ -> LocalStore Γ -> L)
          (s : Stm Γ σ) :
      (forall a, δ ⊢ ⦃ P a ⦄ s ⦃ Q a ⦄) ->
        δ ⊢
          ⦃ outcome_satisfy_natded o P ⦄ s
          ⦃ fun v δ' =>
              outcome_satisfy_natded o (fun a => Q a v δ')
          ⦄.
    Proof.
      intros hyp.
      induction o; cbn in *.
      - apply hyp.
      - apply rule_exist', H.
      - apply rule_forall'; auto. admit.
      - apply rule_disj'; auto.
      - apply rule_conj'; auto.
      - apply rule_false.
    Admitted.

    Lemma outcome_satisfy_natded_monotonic {A : Type} {o : Outcome A} {P Q : A -> L}
      (hyp : forall a, P a ⊢ Q a) :
      outcome_satisfy_natded o P ⊢ outcome_satisfy_natded o Q.
    Proof.
      induction o; cbn.
      - apply hyp.
      - apply lex_left; intro i.
        apply lex_right with i.
        apply H.
      - apply lall_right; intro i.
        apply lall_left with i.
        apply H.
      - apply lor_left.
        + apply lor_right1.
          apply IHo1.
        + apply lor_right2.
          apply IHo2.
      - apply land_right.
        + apply land_left1.
          apply IHo1.
        + apply land_left2.
          apply IHo2.
      - apply entails_refl.
    Qed.

    Opaque env_tail.
    Opaque extract_chunk_eqb.

    Lemma scmut_exec_sound {Γ σ} (s : Stm Γ σ) :
      forall (δ1 : LocalStore Γ) (h1 : SCHeap),
        δ1 ⊢
          ⦃ inst_scheap h1 ⦄ s
          ⦃ fun v δ =>
              outcome_satisfy_natded
                (scmut_exec s (MkSCState δ1 h1))
                (fun '(MkSCMutResult v2 (MkSCState δ2 h2)) =>
                   inst_scheap h2 ∧ !! (v = v2) ∧ !! (δ = δ2))
          ⦄.
    Proof.
      induction s.

      - (* stm_lit *)
        cbn; intros.
        apply rule_stm_lit.
        repeat apply land_right.
        + apply entails_refl.
        + apply lprop_right. reflexivity.
        + apply lprop_right. reflexivity.

      - (* stm_exp *)
        cbn; intros.
        apply rule_stm_exp.
        repeat apply land_right.
        + apply entails_refl.
        + apply lprop_right. reflexivity.
        + apply lprop_right. reflexivity.

      - (* stm_let *)
        cbn in *; intros.
        eapply rule_stm_let.
        + apply IHs1.
        + clear IHs1; cbn in *; intros.
          setoid_rewrite outcome_satisfy_natded_bind.
          apply rule_outcome_satisfy.
          intros [v2 [δ2 h2]]; cbn.
          apply rule_pull; intros; subst.
          apply rule_pull; intros; subst.
          setoid_rewrite outcome_satisfy_natded_bind.
          cbn.
          eapply rule_consequence_right.
          apply IHs2.
          cbn; intros.
          apply outcome_satisfy_natded_monotonic.
          intros [v3 [δ3 h3]].
          repeat apply land_intro2; try reflexivity.
          apply lprop_left; intros.
          apply lprop_right; now f_equal.

      - (* stm_block *)
        cbn in *; intros.
        setoid_rewrite outcome_satisfy_natded_bind.
        apply rule_stm_block.
        eapply rule_consequence_right.
        apply IHs.
        cbn; intros.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        repeat apply land_intro2; try reflexivity.
        apply lprop_left; intros.
        apply lprop_right; now f_equal.

      - (* stm_assign *)
        cbn in *; intros.
        setoid_rewrite outcome_satisfy_natded_bind.
        apply rule_stm_assign_backwards.
        eapply rule_consequence_right.
        apply IHs.
        cbn; intros.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        rewrite ?land_assoc.
        rewrite ?lprop_land_distr.
        apply land_intro2; try reflexivity.
        apply lprop_left; intros.
        apply lprop_right; intuition congruence.

      - (* stm_call *)
        admit.

      - (* stm_call_frame *)
        cbn in *; intros.
        apply rule_stm_call_frame.
        setoid_rewrite outcome_satisfy_natded_bind.
        eapply rule_consequence_right.
        apply IHs.
        cbn; intros.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        repeat apply land_intro2; try reflexivity.
        apply lprop_right; reflexivity.

      - (* stm_call_external *)
        admit.

      - (* stm_if *)
        cbn in *; intros.
        apply rule_stm_if. 
        + apply rule_pull. intros Heval. rewrite Heval. apply IHs1.
        + apply rule_pull. intros Heval. rewrite Heval. apply IHs2.

      - (* stm_seq *)
        cbn in *; intros.
        apply rule_stm_seq with
            (fun δ => outcome_satisfy_natded
                          (scmut_exec s1 {| scstate_localstore := δ1; scstate_heap := h1 |})
                          (fun pat : SCMutResult Γ (Lit τ) =>
                             inst_scheap (scstate_heap (scmutres_state pat)) ∧ !! (δ = scstate_localstore (scmutres_state pat)))).
        + cbn.
          eapply rule_consequence_right.
          apply IHs1.
          cbn; intros.
          apply outcome_satisfy_natded_monotonic.
          intros [v2 [δ2 h2]]; cbn.
          apply land_right.
          * apply land_left1.
            apply land_left1.
            apply entails_refl.
          * apply land_left2.
            apply entails_refl.

        + clear IHs1; cbn in *; intros.
          unfold scmut_bind.
          setoid_rewrite outcome_satisfy_natded_bind.
          apply rule_outcome_satisfy.
          intros [v2 [δ2 h2]]; cbn.
          apply rule_pull; intros; subst.
          eapply rule_consequence_right.
          apply IHs2.
          cbn; intros.
          apply outcome_satisfy_natded_monotonic.
          intros [v3 [δ3 h3]].
          apply entails_refl.

      - (* stm_assert *)
        cbn in *; intros.

        eapply rule_consequence_right.
        apply rule_stm_assert.
        cbn; intros.
        apply limpl_and_adjoint.
        apply lprop_left; intros; destruct_conjs; subst.
        apply limpl_and_adjoint.
        apply land_left2.
        rewrite H1; cbn.
        repeat apply land_right.
        + apply entails_refl.
        + apply lprop_right; reflexivity.
        + apply lprop_right; reflexivity.

      - (* stm_fail *)
        cbn; intros.
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply ltrue_right.

      - (* stm_match_list *)
        cbn in *; intros.
        apply rule_stm_match_list; cbn; intros.
        + apply rule_pull. intros Heval. rewrite Heval.
          apply IHs1.
        + apply rule_pull. intros Heval. rewrite Heval.
          unfold scmut_bind_left, scmut_bind; cbn.
          repeat setoid_rewrite outcome_satisfy_natded_bind.
          cbn.
          eapply rule_consequence_right.
          apply IHs2. cbn. intros.
          apply outcome_satisfy_natded_monotonic.
          intros [v2 [δ2 h2]].
          repeat apply land_intro2; try reflexivity.
          apply lprop_left. intros.
          apply lprop_right.
          congruence.

      - (* stm_match_sum *)
        cbn in *; intros.
        apply rule_stm_match_sum; cbn; intros.
        + apply rule_pull. intros Heval. rewrite Heval.
          unfold scmut_bind_left, scmut_bind; cbn.
          setoid_rewrite outcome_satisfy_natded_bind.
          cbn.
          eapply rule_consequence_right.
          apply IHs1. cbn. intros.
          apply outcome_satisfy_natded_monotonic.
          intros [v2 [δ2 h2]].
          repeat apply land_intro2; try reflexivity.
          apply lprop_left. intros.
          apply lprop_right.
          congruence.
        + apply rule_pull. intros Heval. rewrite Heval.
          unfold scmut_bind_left, scmut_bind; cbn.
          setoid_rewrite outcome_satisfy_natded_bind.
          cbn.
          eapply rule_consequence_right.
          apply IHs2. cbn. intros.
          apply outcome_satisfy_natded_monotonic.
          intros [v2 [δ2 h2]].
          repeat apply land_intro2; try reflexivity.
          apply lprop_left. intros.
          apply lprop_right.
          congruence.

      - (* stm_match_pair *)
        cbn in *; intros.
        apply rule_stm_match_pair; cbn; intros.
        unfold scmut_bind_left, scmut_bind; cbn.
        repeat setoid_rewrite outcome_satisfy_natded_bind.
        cbn.
        apply rule_pull. intros Heval. rewrite !Heval. cbn.
        eapply rule_consequence_right.
        apply IHs. cbn. intros.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        repeat apply land_intro2; try reflexivity.
        apply lprop_left. intros.
        apply lprop_right.
        congruence.

      - (* stm_match_enum *)
        cbn in *; intros.
        now apply rule_stm_match_enum.

      - (* stm_match_tuple *)
        cbn in *; intros.
        apply rule_stm_match_tuple; cbn; intros.
        unfold scmut_bind_left, scmut_bind; cbn.
        setoid_rewrite outcome_satisfy_natded_bind.
        cbn.
        eapply rule_consequence_right.
        apply IHs. cbn. intros.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        repeat apply land_intro2; try reflexivity.
        apply lprop_left. intros.
        apply lprop_right.
        congruence.

      - (* stm_match_union *)
        cbn in *; intros.
        apply rule_stm_match_union'.
        intros K. specialize (H K).
        remember (alts K) as alt.
        dependent elimination alt; cbn.
        intros.
        apply rule_pull. intro Heval. rewrite Heval.
        rewrite 𝑼_unfold_fold. cbn.
        unfold scmut_bind_left, scmut_bind; cbn.
        setoid_rewrite outcome_satisfy_natded_bind.
        cbn.
        eapply rule_consequence_right.
        apply H. cbn. intros.
        rewrite <- Heqalt. cbn.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        repeat apply land_intro2; try reflexivity.
        apply lprop_left. intros.
        apply lprop_right.
        congruence.

      - (* stm_match_record *)
        cbn in *; intros.
        apply rule_stm_match_record; cbn; intros.
        unfold scmut_bind_left, scmut_bind; cbn.
        setoid_rewrite outcome_satisfy_natded_bind.
        cbn.
        eapply rule_consequence_right.
        apply IHs. cbn. intros.
        apply outcome_satisfy_natded_monotonic.
        intros [v2 [δ2 h2]].
        repeat apply land_intro2; try reflexivity.
        apply lprop_left. intros.
        apply lprop_right.
        congruence.

      - (* stm_read_register *)
        cbn in *; intros.
        admit.

      - (* stm_write_register *)
        cbn in *; intros.
        admit.

      - (* stm_bind *)
        cbn in *; intros.
        eapply rule_stm_bind.
        apply IHs.
        cbn; intros.
        unfold scmut_bind.
        eapply rule_consequence_right.
        2: { intros; apply outcome_satisfy_natded_bind. }
        cbn.
        apply rule_outcome_satisfy.
        intros [v2 [δ2 h2]]; cbn.
        apply rule_pull; intros; subst.
        apply rule_pull; intros; subst.
        apply H.
    Admitted.

  End Soundness.

End Soundness.
