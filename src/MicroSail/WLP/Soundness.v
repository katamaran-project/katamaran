(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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
     Strings.String.

From Equations Require Import
     Equations.

From MicroSail Require Import
     SmallStep.Inversion
     SmallStep.Step
     Syntax
     Tactics
     WLP.Spec.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import contkit : ContractKit typekit termkit progkit).
  Module WLP := WLP typekit termkit progkit contkit.
  Import WLP.
  Module SSI := Inversion typekit termkit progkit.
  Import SSI.
  Import SS.

  Lemma eval_prop_true_sound {Γ δ} (e : Exp Γ ty_bool) :
    forall k, eval_prop_true e δ k <-> (eval e δ = true -> k)
  with eval_prop_false_sound {Γ δ} (e : Exp Γ ty_bool) :
    forall k, eval_prop_false e δ k <-> (eval e δ = false -> k).
  Proof.
    all: dependent induction e; cbn; intros;
      repeat
        match goal with
        | [ IH: forall e, ?t = ?t -> ?e1 ~= e -> _ |- _ ] =>
          specialize (IH _ eq_refl JMeq_refl); cbn in *
        | [ |- context[match ?e with _ => _ end]] => dependent elimination e; cbn
        end;
      repeat rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_gt, ?Z.ltb_ge, ?Z.ltb_lt,
      ?Z.leb_le, ?Z.gtb_ltb, ?Bool.andb_true_iff, ?Bool.andb_false_iff,
      ?Bool.orb_true_iff, ?Bool.orb_false_iff, ?Bool.negb_true_iff,
      ?Bool.negb_false_iff, ?IHe1, ?IHe2 in *;
      try (intuition; fail); auto.
  Qed.

  Local Ltac wlp_sound_steps_inversion :=
    repeat
      match goal with
      | [ H: ResultNoFail _ _ |- _ ] =>
        apply result_no_fail_inversion in H; destruct_conjs; subst
      | [ H: ⟨ _, _, _, ?s ⟩ ---> ⟨ _, _, _, _ ⟩ |- _ ] =>
        microsail_stm_primitive_step s; dependent destruction H
      | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, ?t ⟩, HF: Final ?t |- _ ] =>
        first
          [ microsail_stm_primitive_step s; dependent destruction H; cbn in HF
          | match head s with
            | @stm_call_frame => apply (steps_inversion_call_frame HF) in H
            | @stm_let        => apply (steps_inversion_let        HF) in H
            | @stm_block      => apply (steps_inversion_block      HF) in H
            | @stm_seq        => apply (steps_inversion_seq        HF) in H
            | @stm_assign     => apply (steps_inversion_assign     HF) in H
            | @stm_bind       => apply (steps_inversion_bind       HF) in H
            end; destruct_conjs
          ]
      | _ => progress (cbn in *)
      end.

  Local Ltac wlp_sound_inst :=
    match goal with
    | [ IH: forall _ _ _ _ _ _ _, ⟨ _, _, _ , ?s ⟩ --->* ⟨ _, _, _ , _ ⟩ -> _,
        HS: ⟨ _, _, _ , ?s ⟩ --->* ⟨ _, _, _ , ?t ⟩, HF: Final ?t |- _ ] =>
      specialize (IH _ _ _ _ _ _ _ HS HF); clear HS HF
    | [ IH: forall _ _ _ _ _ _ _ _, ⟨ _, _, _ , _ ⟩ --->* ⟨ _, _, _ , _ ⟩ -> _,
        HS: ⟨ _, _, _ , _ ⟩ --->* ⟨ _, _, _ , ?t ⟩, HF: Final ?t |- _ ] =>
      specialize (IH _ _ _ _ _ _ _ _ HS HF); clear HS HF
    | [ IH: forall POST, WLP ?s POST ?δ ?γ -> _, WP: WLP ?s _ ?δ ?γ |- _ ] =>
      specialize (IH _ WP); clear WP
    end.

  Local Ltac wlp_sound_simpl :=
    repeat
      match goal with
      | [ H: True |- _ ] => clear H
      | [ H: False |- _ ] => destruct H
      | [ H: Env _ (ctx_snoc _ _) |- _ ] =>
        dependent destruction H
      | [ H: Env _ ctx_nil |- _ ] =>
        dependent destruction H
      | [ H: context[env_drop _ (_ ►► _)]|- _] =>
        rewrite env_drop_cat in H
      | [ _: context[match eval ?e ?δ with _ => _ end] |- _ ] =>
        destruct (eval e δ)
      | _ => progress (cbn in *; destruct_conjs; subst)
      end.

  Local Ltac wlp_sound_solve :=
    repeat
      (wlp_sound_steps_inversion;
       wlp_sound_simpl;
       try wlp_sound_inst); intuition.

  Definition ValidContractEnv' (cenv : ContractEnv) : Prop :=
    forall σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | ContractNoFail _ _ pre post =>
        forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore σs) (s' : Stm σs σ),
          ⟨ γ, μ, δ, Pi f ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
          Final s' ->
          uncurry pre δ γ ->
          ResultNoFail s' (fun v => uncurry post δ v γ')
      | ContractTerminateNoFail _ _ _ _ => False
      | ContractTerminate _ _ _ _ => False
      | ContractNone _ _ => True
      end.

  Section Soundness.

    Variable validCEnv : ValidContractEnv' CEnv.
    Variable validCEnvEx : ValidContractEnvEx CEnvEx.

    Lemma WLP_sound {Γ σ} (s : Stm Γ σ) :
    forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ),
      ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
      forall (POST : Lit σ -> LocalStore Γ -> RegStore -> Prop),
        WLP s POST δ γ -> ResultNoFail s' (fun v => POST v δ' γ').
    Proof.
      induction s; cbn; intros.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - pose proof (validCEnv f).
        destruct (CEnv f); wlp_sound_solve.
        intuition.
        wlp_sound_solve.
      - wlp_sound_solve.
      - pose proof (validCEnvEx f).
        destruct (CEnvEx f); wlp_sound_solve.
        specialize (H3 _ _ _ _ _ _ H H2).
        destruct res; wlp_sound_solve.
      - destruct_conjs. case_eq (eval e δ); intros.
        + apply eval_prop_true_sound in H1; wlp_sound_solve.
        + apply eval_prop_false_sound in H2; wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
        specialize (H _ _ eq_refl).
        wlp_sound_solve.
      - wlp_sound_solve.
        + specialize (H _ eq_refl).
          wlp_sound_solve.
        + specialize (H2 _ eq_refl).
          wlp_sound_solve.
      - wlp_sound_solve.
      - rewrite blast_sound in H2.
        wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
        destruct (𝑼_unfold (eval e δ)) as [K v] eqn:eq_eval.
        specialize (H3 K).
        rewrite blast_sound in H3.
        specialize (H3 v).
        assert (eval e δ = 𝑼_fold (existT K v)).
        { rewrite <- (𝑼_fold_unfold (eval e δ)); now f_equal. }
        intuition.
        rewrite 𝑼_unfold_fold in H4.
        wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
      - wlp_sound_solve.
    Qed.

  End Soundness.

End Soundness.
