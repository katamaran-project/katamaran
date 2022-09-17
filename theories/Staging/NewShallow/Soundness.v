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
  (Import EXEC : NewShallowExecOn B PROG SIG SPEC)
  (Import HOAR : ProgramLogicOn B PROG SIG SPEC).

  Import sep.instances.
  Import sep.notations.
  Import CHeapSpecM.
  Import ProgramLogic.

  Section Soundness.

    Context {L} {PI : PredicateDef L}.

    Lemma call_contract_sound {Δ τ}
      (c : SepContract Δ τ) (δΔ : CStore Δ) (POST : Val τ -> L) :
      CTriple (CPureSpecM.call_contract c δΔ POST) c δΔ POST.
    Proof.
      unfold CTriple. destruct c as [Σe δe req result ens].
      now rewrite CPureSpecM.equiv_call_contract.
    Qed.

    Lemma call_lemma_sound {Δ}
      (lem : Lemma Δ) (δΔ : CStore Δ) (POST : unit -> L) :
      LTriple δΔ (CPureSpecM.call_lemma lem δΔ POST) (POST tt) lem.
    Proof.
      destruct lem as [Σe δe req ens]. constructor.
      now rewrite CPureSpecM.equiv_call_lemma.
    Qed.

    Definition SoundExec (rec : Exec) : Prop :=
      forall Γ σ (s : Stm Γ σ) (POST : Val σ -> CStore Γ -> L) (δ1 : CStore Γ),
        ⦃ rec _ _ s POST δ1 ⦄ s ; δ1 ⦃ POST ⦄.

    Lemma exec_aux_sound rec (rec_sound : SoundExec rec) :
      SoundExec (exec_aux (exec_call_with_contracts rec)).
    Proof.
      unfold SoundExec. intros ? ? s.
      induction s; intros ? ?; cbn.

      - (* stm_val *)
        now apply rule_stm_val.

      - (* stm_exp *)
        now apply rule_stm_exp.

      - (* stm_let *)
        eapply rule_stm_let. apply IHs1. intros v2 δ2; cbn. apply IHs2.

      - (* stm_block *)
        now apply rule_stm_block, IHs.

      - (* stm_assign *)
        now apply rule_stm_assign, IHs.

      - (* stm_call *)
        destruct (CEnv f) as [c|] eqn:Heq.
        + apply rule_stm_call with c.
          assumption.
          now apply call_contract_sound.
        + apply rule_stm_call_inline.
          apply rec_sound.

      - (* stm_call_frame *)
        now apply rule_stm_call_frame, IHs.

      - (* stm_foreign *)
        apply rule_stm_foreign.
        apply call_contract_sound.

      - (* stm_lemmak *)
        unfold eval_exps.
        eapply rule_stm_lemmak.
        apply call_lemma_sound.
        apply IHs.

      - (* stm_if *)
        apply rule_stm_if; intros ->; auto.

      - (* stm_seq *)
        eapply rule_stm_seq. apply IHs1. intros δ2. apply IHs2.

      - (* stm_assert *)
        apply rule_stm_assert; intro Heval.
        eapply rule_consequence_left. apply IHs.
        now apply lentails_apply, lprop_right.

      - (* stm_fail *)
        eapply rule_consequence_left.
        apply rule_stm_fail.
        apply ltrue_right.

      - (* stm_match_pattern *)
        eapply rule_stm_match_pattern. apply IHs1. cbn.
        intros v1 δ1'. now apply IHs2.

      - (* stm_match_list *)
        apply rule_stm_match_list; cbn; intros * ->; auto.

      - (* stm_match_sum *)
        apply rule_stm_match_sum; cbn; intros * ->; auto.

      - (* stm_match_enum *)
        now apply rule_stm_match_enum, H.

      - (* stm_match_tuple *)
        now apply rule_stm_match_tuple, IHs.

      - (* stm_match_union *)
        apply rule_stm_match_union; cbn; intros * ->.
        now rewrite unionv_unfold_fold.

      - (* stm_match_record *)
        now apply rule_stm_match_record, IHs.

      - (* stm_match_bvec *)
        now apply rule_stm_match_bvec, H.

      - (* stm_match_bvec_split *)
        apply rule_stm_match_bvec_split; cbn; intros * ->.
        now rewrite bv.appView_app.

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
      rewrite CHeapSpecM.vcgen_equiv.
      unfold CHeapSpecM.vcgen', ProgramLogic.ValidContract.
      unfold inst_contract_localstore.
      destruct c as [Σ δΣ req result ens]; cbn; intros HYP ι.
      eapply rule_consequence_left.
      apply exec_sound. apply HYP.
    Qed.

    Lemma shallow_vcgen_soundness {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      Shallow.ValidContract c body ->
      ProgramLogic.ValidContract c body.
    Proof. apply vcgen_sound. Qed.

    (* Print Assumptions shallow_vcgen_soundness. *)

  End Soundness.

End Soundness.
