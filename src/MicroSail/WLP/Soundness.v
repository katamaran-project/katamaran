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
     Program.Tactics.

From MicroSail Require Import
     SmallStep.Inversion
     SmallStep.Step
     Syntax
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

  Ltac wlp_sound_steps_inversion :=
    repeat
      match goal with
      | [ H: ⟨ _, stm_call _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
      | [ H: ⟨ _, stm_call _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             dependent destruction H
      | [ H: ⟨ _, stm_assert _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
      | [ H: ⟨ _, stm_assert _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           dependent destruction H
      | [ H: ⟨ _, stm_fail _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>             dependent destruction H
      | [ H: ⟨ _, stm_fail _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
      | [ H: ⟨ _, stm_exp _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>                 dependent destruction H
      | [ H: ⟨ _, stm_exp _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>                dependent destruction H
      | [ H: ⟨ _, stm_if _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
      | [ H: ⟨ _, stm_if _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             dependent destruction H
      | [ H: ⟨ _, stm_lit _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>               dependent destruction H
      | [ H: ⟨ _, stm_lit _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
      | [ H: ⟨ _, stm_match_sum _ _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>   dependent destruction H
      | [ H: ⟨ _, stm_match_sum _ _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
      | [ H: ⟨ _, stm_match_list _ _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
      | [ H: ⟨ _, stm_match_list _ _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => dependent destruction H
      | [ H: ⟨ _, stm_match_pair _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>    dependent destruction H
      | [ H: ⟨ _, stm_match_pair _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>   dependent destruction H
      | [ H: ⟨ _, stm_match_enum _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>      dependent destruction H
      | [ H: ⟨ _, stm_match_enum _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
      | [ H: ⟨ _, stm_match_tuple _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
      | [ H: ⟨ _, stm_match_tuple _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>    dependent destruction H
      | [ H: ⟨ _, stm_match_union _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>   dependent destruction H
      | [ H: ⟨ _, stm_match_union _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
      | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
      | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => dependent destruction H

      | [ H: ⟨ _, stm_call' _ _ _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] => dependent destruction H
      | [ H: ⟨ _, stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
      | [ H: ⟨ _, stm_let' _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
      | [ H: ⟨ _, stm_seq (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>      dependent destruction H
      | [ H: ⟨ _, stm_assign _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
      | [ H: ⟨ _, stm_bind (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H

      | [ H: ⟨ _, stm_call' _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] => apply (steps_inversion_call' HF) in H; destruct_conjs
      | [ H: ⟨ _, stm_let _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>  apply (steps_inversion_let HF) in H; destruct_conjs
      | [ H: ⟨ _, stm_let' _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>     apply (steps_inversion_let' HF) in H; destruct_conjs
      | [ H: ⟨ _, stm_seq _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>      apply (steps_inversion_seq HF) in H; destruct_conjs
      | [ H: ⟨ _, stm_assign _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>   apply (steps_inversion_assign HF) in H; destruct_conjs
      | [ H: ⟨ _, stm_bind _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>     apply (steps_inversion_bind HF) in H; destruct_conjs
      | [ H: IsLit _ _ _ |- _ ] => apply IsLit_inversion in H; destruct_conjs; subst
      end; cbn in *.

  Ltac wlp_sound_inst :=
    match goal with
    | [ IH: forall _ _ _, ⟨ _ , ?s ⟩ --->* ⟨ _ , _ ⟩ -> _,
        HS: ⟨ _ , ?s ⟩ --->* ⟨ _ , ?t ⟩, HF: Final ?t |- _ ] =>
      specialize (IH _ _ _ HS HF); clear HS HF
    | [ IH: forall _ _ _ _, ⟨ _ , _ ⟩ --->* ⟨ _ , _ ⟩ -> _,
        HS: ⟨ _ , _ ⟩ --->* ⟨ _ , ?t ⟩, HF: Final ?t |- _ ] =>
      specialize (IH _ _ _ _ HS HF); clear HS HF
    | [ IH: forall POST, WLP ?s POST ?δ -> _, WP: WLP ?s _ ?δ |- _ ] =>
      specialize (IH _ WP); clear WP
    end.

  Ltac wlp_sound_simpl :=
    repeat
      (cbn in *; destruct_conjs; subst;
       try match goal with
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
           end).

  Ltac wlp_sound_solve :=
    repeat
      (wlp_sound_steps_inversion;
       wlp_sound_simpl;
       try wlp_sound_inst); auto.

  Definition ValidContractEnv (cenv : ContractEnv) : Prop :=
    forall σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | ContractNoFail _ _ pre post =>
        forall (δ δ' : LocalStore σs) (s' : Stm σs σ),
          ⟨ δ, Pi f ⟩ --->* ⟨ δ', s' ⟩ ->
          Final s' ->
          uncurry pre δ ->
          IsLit δ s' (fun v δ => uncurry post δ v)
      | ContractTerminateNoFail _ _ _ _ => False
      | ContractTerminate _ _ _ _ => False
      | ContractNone _ _ => False
      end.

  Lemma WLP_sound (validCEnv : ValidContractEnv CEnv) {Γ σ} (s : Stm Γ σ) :
    forall (δ δ' : LocalStore Γ) (s' : Stm Γ σ), ⟨ δ, s ⟩ --->* ⟨ δ', s' ⟩ -> Final s' ->
      forall (POST : Lit σ -> Pred (LocalStore Γ)), WLP s POST δ -> IsLit δ' s' POST.
  Proof.
    induction s; cbn; intros.
    - wlp_sound_solve.
    - wlp_sound_solve.
    - wlp_sound_solve.
    - wlp_sound_solve.
    - wlp_sound_solve.
    - pose proof (validCEnv _ _ f).
      destruct (CEnv f); wlp_sound_solve.
      intuition.
      wlp_sound_solve.
    - wlp_sound_solve.
    - wlp_sound_solve.
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
    - wlp_sound_solve.
    - wlp_sound_solve.
  Qed.

End Soundness.
