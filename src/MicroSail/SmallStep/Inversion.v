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
From Equations Require Import
     Equations.
From MicroSail Require Import
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Inversion
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit).

  Module Import SS := SmallStep termkit progkit.

  Section StepInversionFinal.

    Lemma step_inversion_let {Γ x τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
          {δ1 δ3 : LocalStore Γ}
          {s : Stm Γ τ} {k : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final s)
          (step : ⟨ γ1, μ1, δ1, stm_let x τ s k ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
      γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\
      ((exists msg, s = stm_fail _ msg /\ t = stm_fail _ msg) \/
       (exists v,   s = stm_lit τ v    /\ t = stm_block (env_snoc env_nil (x,τ) v) k)
      ).
    Proof.
      dependent elimination step.
      - intuition. right. eexists. intuition.
      - intuition. left. eexists. intuition.
      - dependent elimination s2; contradiction.
    Qed.

    Lemma step_inversion_block {Γ Δ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
          {δ1 δ3 : LocalStore Γ}
          {δ : LocalStore Δ} {k : Stm (Γ ▻▻ Δ) σ} {t : Stm Γ σ} (final : Final k)
          (step : ⟨ γ1, μ1, δ1, stm_block δ k ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
      γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\
      ((exists msg, k = stm_fail _ msg /\ t = stm_fail _ msg) \/
       (exists v,   k = stm_lit σ v    /\ t = stm_lit σ v)
      ).
    Proof.
      dependent elimination step.
      - intuition. right. eexists. intuition.
      - intuition. left. eexists. intuition.
      - dependent destruction s3; cbn in *; try contradiction.
    Qed.

    Lemma step_inversion_seq {Γ τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
          {δ1 δ3 : LocalStore Γ}
          {s1 : Stm Γ τ} {s2 : Stm Γ σ} {t : Stm Γ σ} (final : Final s1)
          (step : ⟨ γ1, μ1, δ1, stm_seq s1 s2 ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
      γ3 = γ1 /\ μ3 = μ1 /\ δ3 = δ1 /\
      ((exists msg, s1 = stm_fail _ msg /\ t = stm_fail _ msg) \/
       (exists v,   s1 = stm_lit τ v    /\ t = s2)
      ).
    Proof.
      dependent elimination step.
      - dependent destruction s7; cbn in *; try contradiction.
      - intuition. right. eexists. intuition.
      - intuition. left. eexists. intuition.
    Qed.

    Lemma step_inversion_call_frame {Γ Δ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
          (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final k)
          (step : ⟨ γ1, μ1, δ1, stm_call_frame δΔ k ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
      γ3 = γ1 /\ μ3 = μ1 /\ δ3 = δ1 /\
      ((exists msg, k = stm_fail _ msg /\ t = stm_fail _ msg) \/
       (exists v,   k = stm_lit σ v    /\ t = stm_lit σ v)
      ).
    Proof.
      dependent elimination step.
      - dependent destruction s8; cbn in *; contradiction.
      - intuition. right. eexists. intuition.
      - intuition. left. eexists. intuition.
    Qed.

    Lemma step_inversion_assign {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
          {x : 𝑿} {xInΓ : InCtx (x,σ) Γ} {s1 t : Stm Γ σ} (final : Final s1)
          (step : ⟨ γ1, μ1, δ1, stm_assign x s1 ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
      γ3 = γ1 /\ μ3 = μ1 /\
      ((exists msg, s1 = stm_fail _ msg /\ t = stm_fail _ msg /\ δ3 = δ1) \/
       (exists v,   s1 = stm_lit σ v    /\ t = stm_lit σ v /\ δ3 = (δ1 ⟪ x ↦ v ⟫)%env)
      ).
    Proof.
      dependent elimination step.
      - intuition. right. eexists. intuition.
      - intuition. left. eexists. intuition.
      - dependent destruction s13; cbn in *; try contradiction.
    Qed.

    Lemma step_inversion_bind {Γ σ τ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
          {s : Stm Γ σ} {k : Lit σ -> Stm Γ τ} {t : Stm Γ τ} (final : Final s)
          (step : ⟨ γ1, μ1, δ1, stm_bind s k ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
      γ3 = γ1 /\ μ3 = μ1 /\ δ3 = δ1 /\
      ((exists msg, s = stm_fail _ msg /\ t = stm_fail _ msg) \/
       (exists v,   s = stm_lit σ v    /\ t = k v)
      ).
    Proof.
      dependent elimination step.
      - dependent destruction s17; cbn in *; try contradiction.
      - intuition. right. eexists. intuition.
      - intuition. left. eexists. intuition.
    Qed.

  End StepInversionFinal.

  Lemma steps_inversion_lit {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ} {v : Lit σ} (t : Stm Γ σ)
    (steps : ⟨ γ1, μ1, δ1, stm_lit σ v ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\ t = stm_lit σ v.
  Proof.
    dependent elimination steps.
    - auto.
    - dependent elimination s.
  Qed.

  Lemma steps_inversion_fail {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ} {msg : String.string} (t : Stm Γ σ)
    (steps : ⟨ γ1, μ1, δ1, stm_fail σ msg ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\ t = stm_fail σ msg.
  Proof.
    dependent elimination steps.
    - auto.
    - dependent elimination s.
  Qed.

  Lemma steps_inversion_exp {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ}
    {e : Exp Γ σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_exp e ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\ t = stm_lit σ (eval e δ1).
  Proof.
    dependent elimination steps; cbn in *.
    - contradiction.
    - dependent elimination s.
      apply steps_inversion_lit in s0.
      intuition.
  Qed.

  Lemma steps_inversion_read_register {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ}
    {r} {t : Stm Γ σ}
    (step : ⟨ γ1, μ1, δ1, stm_read_register r ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
    γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\ t = stm_lit σ (read_register γ1 r).
  Proof.
    dependent elimination step; intuition.
  Qed.

  Lemma steps_inversion_write_register {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ}
    {r} {t : Stm Γ σ} {e}
    (step : ⟨ γ1, μ1, δ1, stm_write_register r e ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
    γ3 = write_register γ1 r (eval e δ1) /\ μ1 = μ3 /\ δ1 = δ3 /\ t = stm_lit σ (eval e δ1).
  Proof.
    dependent elimination step; intuition.
  Qed.


  Local Ltac steps_inversion_simpl :=
    repeat
      match goal with
      | [ H: exists t, _ |- _ ] => destruct H
      | [ H: _ /\ _ |- _ ] => destruct H
      | [ H : False |- _ ] => destruct H
      | [ H : ⟨ _, _, _, stm_lit _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ] =>
        apply steps_inversion_lit in H;
        microsail_destruct_propositional H;
        subst
      | [ H : ⟨ _, _, _, stm_fail _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ] =>
        apply steps_inversion_fail in H;
        microsail_destruct_propositional H;
        subst
      | _ => progress (cbn in *; subst)
      end.

  Local Ltac steps_inversion_inster :=
    repeat
      match goal with
      | [ H : forall _, _ = _ -> _ |- _ ]
        => specialize (H _ eq_refl)
      | [ H : forall _ _, _ = _ -> _ |- _ ]
        => specialize (H _ _ eq_refl)
      | [ H : forall _ _ _, _ = _ -> _ |- _ ]
        => specialize (H _ _ _ eq_refl)
      | [ H : Final ?s -> _, H' : Final ?s |- _ ]
        => specialize (H H')
      | [ H1 : ⟨ _, _, _, _ ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s2 ⟩,
          H2 : ⟨ ?γ2, ?μ2, ?δ2, ?s2 ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ]
        => let H:=fresh in add_hypothesis H (step_trans H1 H2)
      | _ => progress steps_inversion_simpl
      end.

  Local Ltac steps_inversion_solve :=
    repeat
      match goal with
      | [ |- exists t, _ ] => eexists
      | [ |- _ /\ _ ] => constructor
      | [ |- True ] => constructor
      | [ |- ⟨ _, _, _, stm_lit _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ ] => constructor 1
      | [ |- ⟨ _, _, _, stm_fail _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ ] => constructor 1
      | [ |- ⟨ _, _, _, stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_let_value
      | [ |- ⟨ _, _, _, stm_let _ _ (stm_fail _ _) _ ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_let_fail
      | [ |- ⟨ _, _, _, stm_block _ (stm_lit _ _) ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_block_value
      | [ |- ⟨ _, _, _, stm_block _ (stm_fail _ _) ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_block_fail
      | [ |- ⟨ _, _, _, stm_seq (stm_lit _ _) _ ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_seq_value
      | [ |- ⟨ _, _, _, stm_seq (stm_fail _ _) _ ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_seq_fail
      | [ |- ⟨ _, _, _, stm_call_frame _ (stm_lit _ _) ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_call_frame_value
      | [ |- ⟨ _, _, _, stm_call_frame _ (stm_fail _ _) ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_call_frame_fail
      | [ |- ⟨ _, _, _, stm_assign _ (stm_lit _ _) ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_assign_value
      | [ |- ⟨ _, _, _, stm_assign _ (stm_fail _ _) ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_assign_fail
      | [ |- ⟨ _, _, _, stm_bind (stm_lit _ _) _ ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_bind_value
      | [ |- ⟨ _, _, _, stm_bind (stm_fail _ _) _ ⟩ ---> ⟨ _, _, _, _ ⟩ ] => apply step_stm_bind_fail
      | _ => progress cbn
      end; try eassumption.

  Local Ltac steps_inversion_induction :=
    let step := fresh in
    induction 1 as [|? ? ? ? ? ? ? ? ? ? ? ? step]; intros; subst;
      [ cbn in *; contradiction
      | dependent elimination step; steps_inversion_inster; steps_inversion_solve
      ].

  Lemma steps_inversion_let {Γ x τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ}
    {s1 : Stm Γ τ} {s2 : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_let x τ s1 s2 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    exists (γ2 : RegStore) (μ2 : Memory) (δ2 : LocalStore Γ) (s1' : Stm Γ τ),
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
          ⟨ γ2, μ2, δ2, stm_let x τ s1' s2 ⟩ ---> ⟨ γ2, μ2, δ2, s0 ⟩ /\
          ⟨ γ2, μ2, δ2, s0 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩.
  Proof.
    remember (stm_let x τ s1 s2) as s. revert steps s1 s2 Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_block {Γ Δ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    {δΔ : LocalStore Δ} {k : Stm (ctx_cat Γ Δ) σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_block δΔ k ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    exists δΔ' k',
      ⟨ γ1, μ1, env_cat δ1 δΔ , k ⟩ --->* ⟨ γ3, μ3, env_cat δ3 δΔ' , k' ⟩ /\ Final k' /\
      ⟨ γ3, μ3, δ3, stm_block δΔ' k' ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩.
  Proof.
    remember (stm_block δΔ k) as s. revert steps δΔ k Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_seq {Γ τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (s1 : Stm Γ τ) (s2 : Stm Γ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_seq s1 s2 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    exists γ2 μ2 δ2 s1',
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, μ2, δ2, stm_seq s1' s2 ⟩ ---> ⟨ γ2, μ2, δ2 , s0 ⟩ /\
        ⟨ γ2, μ2, δ2 , s0 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩.
  Proof.
    remember (stm_seq s1 s2) as s. revert steps s1 s2 Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_call_frame {Γ Δ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_call_frame δΔ k ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    exists μ2 γ2 δΔ' k',
      ⟨ γ1, μ1, δΔ , k ⟩ --->* ⟨ γ2, μ2, δΔ' , k' ⟩ /\ Final k' /\
      exists s0,
        ⟨ γ2, μ2, δ1, stm_call_frame δΔ' k' ⟩ ---> ⟨ γ2, μ2, δ1, s0 ⟩ /\
        ⟨ γ2, μ2, δ1, s0⟩ --->* ⟨ γ3, μ3, δ3, t ⟩.
  Proof.
    remember (stm_call_frame δΔ k) as s. revert steps δΔ k Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_assign {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (x : 𝑿) (xInΓ : InCtx (x,σ) Γ) (s1 t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_assign x s1 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    exists γ2 μ2 δ2 δ2' s1',
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, μ2, δ2, stm_assign x s1' ⟩ ---> ⟨ γ2, μ2, δ2' , s0 ⟩ /\
        ⟨ γ2, μ2, δ2' , s0 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩.
  Proof.
    remember (stm_assign x s1) as s. revert steps x xInΓ s1 Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_bind {Γ τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (s1 : Stm Γ τ) (k : Lit τ -> Stm Γ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_bind s1 k ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    exists γ2 μ2 δ2 s1',
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, μ2, δ2, stm_bind s1' k ⟩ ---> ⟨ γ2, μ2, δ2 , s0 ⟩ /\
        ⟨ γ2, μ2, δ2 , s0 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩.
  Proof.
    remember (stm_bind s1 k) as s. revert steps s1 k Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_ex_let {Γ x τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ}
    {s1 : Stm Γ τ} {s2 : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_let x τ s1 s2 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    (exists msg,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ3, μ3, δ3, stm_fail _ msg ⟩ /\
        t = stm_fail _ msg) \/
    (exists γ2 μ2 δ2 v,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, stm_lit _ v ⟩ /\
        ⟨ γ2, μ2, δ2, stm_block (env_snoc env_nil (x,τ) v) s2 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩).
  Proof.
    apply (steps_inversion_let final) in steps.
    microsail_destruct_propositional steps; subst.
    apply (step_inversion_let H5) in H7.
    microsail_destruct_propositional H7; subst.
    - apply steps_inversion_fail in H8; destruct_conjs; subst.
      left. steps_inversion_solve. auto.
    - right. steps_inversion_solve.
  Qed.

  Lemma steps_inversion_ex_block {Γ Δ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    {δΔ : LocalStore Δ} {k : Stm (ctx_cat Γ Δ) σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_block δΔ k ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    (exists δΔ' msg,
        ⟨ γ1, μ1, env_cat δ1 δΔ , k ⟩ --->* ⟨ γ3, μ3, env_cat δ3 δΔ' , stm_fail _ msg ⟩ /\
        t = stm_fail _ msg) \/
    (exists δΔ' v,
        ⟨ γ1, μ1, env_cat δ1 δΔ, k ⟩ --->* ⟨ γ3, μ3, env_cat δ3 δΔ', stm_lit _ v ⟩ /\
        t = stm_lit _ v).
  Proof.
    apply (steps_inversion_block final) in steps.
    microsail_destruct_propositional steps; subst.
    apply (step_inversion_block H3) in H4.
    microsail_destruct_propositional H4; subst.
    - left. steps_inversion_solve. auto.
    - right. steps_inversion_solve. auto.
  Qed.

  Lemma steps_inversion_ex_seq {Γ τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    {s1 : Stm Γ τ} {s2 : Stm Γ σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_seq s1 s2 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    (exists msg,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ3, μ3, δ3, stm_fail _ msg ⟩ /\
        t = stm_fail _ msg) \/
    (exists γ2 μ2 δ2 v,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, stm_lit _ v ⟩ /\
        ⟨ γ2, μ2, δ2, s2 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩).
  Proof.
    apply (steps_inversion_seq final) in steps.
    microsail_destruct_propositional steps; subst.
    apply (step_inversion_seq H5) in H7.
    microsail_destruct_propositional H7; subst.
    - apply steps_inversion_fail in H8; destruct_conjs; subst.
      left. steps_inversion_solve. auto.
    - right. steps_inversion_solve.
  Qed.

  Lemma steps_inversion_ex_call_frame {Γ Δ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_call_frame δΔ k ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    (exists δΔ' msg,
        ⟨ γ1, μ1, δΔ, k ⟩ --->* ⟨ γ3, μ3, δΔ', stm_fail _ msg ⟩ /\
        t = stm_fail _ msg /\ δ3 = δ1) \/
    (exists δΔ' v,
        ⟨ γ1, μ1, δΔ, k ⟩ --->* ⟨ γ3, μ3, δΔ', stm_lit _ v ⟩ /\
        t = stm_lit _ v /\ δ3 = δ1).
  Proof.
    apply (steps_inversion_call_frame final) in steps.
    microsail_destruct_propositional steps; subst.
    apply (step_inversion_call_frame H5) in H7.
    microsail_destruct_propositional H7; subst.
    - apply steps_inversion_fail in H8; destruct_conjs; subst.
      left. steps_inversion_solve. auto.
    - apply steps_inversion_lit in H8; destruct_conjs; subst.
      right. steps_inversion_solve; auto.
  Qed.

  Lemma steps_inversion_ex_assign {Γ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (x : 𝑿) (xInΓ : InCtx (x,σ) Γ) (s1 t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_assign x s1 ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    (exists msg,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ3, μ3, δ3, stm_fail _ msg ⟩ /\
        t = stm_fail _ msg) \/
    (exists δ2 v,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ3, μ3, δ2, stm_lit _ v ⟩ /\
        t = stm_lit _ v /\ δ3 = (δ2 ⟪ x ↦ v ⟫)%env).
  Proof.
    apply (steps_inversion_assign final) in steps.
    microsail_destruct_propositional steps; subst.
    eapply (step_inversion_assign H6) in H8.
    microsail_destruct_propositional H8; subst.
    - apply steps_inversion_fail in H9; destruct_conjs; subst.
      left. steps_inversion_solve. auto.
    - apply steps_inversion_lit in H9; destruct_conjs; subst.
      right. steps_inversion_solve; auto.
  Qed.

  Lemma steps_inversion_ex_bind {Γ τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory} {δ1 δ3 : LocalStore Γ}
    (s1 : Stm Γ τ) (k : Lit τ -> Stm Γ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, μ1, δ1, stm_bind s1 k ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩) :
    (exists msg,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ3, μ3, δ3, stm_fail _ msg ⟩ /\
        t = stm_fail _ msg) \/
    (exists γ2 μ2 δ2 v,
        ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, stm_lit _ v ⟩ /\
        ⟨ γ2, μ2, δ2, k v ⟩ --->* ⟨ γ3, μ3, δ3, t ⟩).
  Proof.
    apply (steps_inversion_bind final) in steps.
    microsail_destruct_propositional steps; subst.
    eapply (step_inversion_bind H5) in H7.
    microsail_destruct_propositional H7; subst.
    - apply steps_inversion_fail in H8; destruct_conjs; subst.
      left. steps_inversion_solve. auto.
    - right. steps_inversion_solve; auto.
  Qed.

  Lemma step_inversion_let_lit {Γ x τ σ} {γ1 γ3 : RegStore} {μ1 μ3 : Memory}
    {δ1 δ3 : LocalStore Γ}
    {v : Lit τ} {k : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ}
    (steps : ⟨ γ1, μ1, δ1, stm_let x τ (stm_lit τ v) k ⟩ ---> ⟨ γ3, μ3, δ3, t ⟩) :
    γ3 = γ1 /\ μ1 = μ3 /\ δ1 = δ3 /\ t = stm_block (env_snoc env_nil (x,τ) v) k.
  Proof.
    dependent elimination steps.
    - intuition.
    - dependent elimination s1.
  Qed.

End Inversion.
