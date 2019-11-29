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
     Program.Equality.
From MicroSail Require Import
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Inversion
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).
  Module SS := SmallStep typekit termkit progkit.
  Import SS.

  Local Ltac steps_inversion_simpl :=
    repeat
      (try match goal with
           | [ H: exists t, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: existT _ _ _ = existT _ _ _ |- _ ] => dependent destruction H
           | [ H : False |- _ ] => destruct H
           end;
       cbn in *).

  Local Ltac extend p :=
    let P := type of p in
    match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => pose proof p
    end.

  Local Ltac steps_inversion_inster :=
    repeat
      (try match goal with
           | [ H : forall _, _ = _ -> _ |- _ ]
             => specialize (H _ eq_refl)
           | [ H : forall _ _, _ = _ -> _ |- _ ]
             => specialize (H _ _ eq_refl)
           | [ H : forall _ _ _, _ = _ -> _ |- _ ]
             => specialize (H _ _ _ eq_refl)
           | [ H : Final ?s -> _, H' : Final ?s |- _ ]
             => specialize (H H')
           | [ H1 : ⟨ _, _, _ ⟩ ---> ⟨ ?γ2, ?δ2, ?s2 ⟩,
               H2 : ⟨ ?γ2, ?δ2, ?s2 ⟩ --->* ⟨ _, _, _ ⟩ |- _ ]
             => extend (step_trans H1 H2)
           end;
       steps_inversion_simpl).

  Local Ltac steps_inversion_solve :=
    repeat
      (match goal with
       | [ |- exists t, _ ] => eexists
       | [ |- _ /\ _ ] => constructor
       | [ |- True ] => constructor
       | [ |- ⟨ _, _, stm_lit _ _ ⟩ --->* ⟨ _, _, _ ⟩ ] => constructor 1
       | [ |- ⟨ _, _, stm_fail _ _ ⟩ --->* ⟨ _, _, _ ⟩ ] => constructor 1
       | [ |- ⟨ _, _, stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _, _ ⟩ ] => apply step_stm_let_value
       | [ |- ⟨ _, _, stm_let _ _ (stm_fail _ _) _ ⟩ ---> ⟨ _, _, _ ⟩ ] => apply step_stm_let_fail
       | [ |- ⟨ _, _, stm_assign _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _, _ ⟩ ] => apply step_stm_assign_value
       | [ |- ⟨ _, _, stm_assign _ (stm_fail _ _) _ ⟩ ---> ⟨ _, _, _ ⟩ ] => apply step_stm_assign_fail
       end; cbn); try eassumption.

  Local Ltac steps_inversion_induction :=
    let step := fresh in
    induction 1 as [|? ? ? ? ? ? ? ? ? step]; intros; subst;
      [ cbn in *; contradiction
      | inversion step; steps_inversion_inster; steps_inversion_solve
      ].

  Lemma steps_inversion_let {Γ x τ σ} {γ1 γ3 : RegStore} {δ1 δ3 : LocalStore Γ}
    {s1 : Stm Γ τ} {s2 : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, δ1, stm_let x τ s1 s2 ⟩ --->* ⟨ γ3, δ3, t ⟩) :
    exists (γ2 : RegStore) (δ2 : LocalStore Γ) (s1' : Stm Γ τ),
      ⟨ γ1, δ1, s1 ⟩ --->* ⟨ γ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
          ⟨ γ2, δ2, stm_let x τ s1' s2 ⟩ ---> ⟨ γ2, δ2, s0 ⟩ /\
          ⟨ γ2, δ2, s0 ⟩ --->* ⟨ γ3, δ3, t ⟩.
  Proof.
    remember (stm_let x τ s1 s2) as s. revert steps s1 s2 Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_let' {Γ Δ σ} {γ1 γ3 : RegStore} {δ1 δ3 : LocalStore Γ}
    {δΔ : LocalStore Δ} {k : Stm (ctx_cat Γ Δ) σ} {t : Stm Γ σ} (final : Final t)
    (steps : ⟨ γ1, δ1, stm_let' δΔ k ⟩ --->* ⟨ γ3, δ3, t ⟩) :
    exists γ2 δ2 δΔ' k',
      ⟨ γ1, env_cat δ1 δΔ , k ⟩ --->* ⟨ γ2, env_cat δ2 δΔ' , k' ⟩ /\ Final k' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, δ2, stm_let' δΔ' k' ⟩ ---> ⟨ γ2, δ2, s0 ⟩ /\
        ⟨ γ2, δ2, s0 ⟩ --->* ⟨ γ3, δ3, t ⟩.
  Proof.
    remember (stm_let' δΔ k) as s. revert steps δΔ k Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_seq {Γ τ σ} {γ1 γ3 : RegStore} {δ1 δ3 : LocalStore Γ}
    (s1 : Stm Γ τ) (s2 : Stm Γ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, δ1, stm_seq s1 s2 ⟩ --->* ⟨ γ3, δ3, t ⟩) :
    exists γ2 δ2 s1',
      ⟨ γ1, δ1, s1 ⟩ --->* ⟨ γ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, δ2, stm_seq s1' s2 ⟩ ---> ⟨ γ2, δ2 , s0 ⟩ /\
        ⟨ γ2, δ2 , s0 ⟩ --->* ⟨ γ3, δ3, t ⟩.
  Proof.
    remember (stm_seq s1 s2) as s. revert steps s1 s2 Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_call' {Γ Δ σ} {γ1 γ3 : RegStore} {δ1 δ3 : LocalStore Γ}
    (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, δ1, stm_call' Δ δΔ σ k ⟩ --->* ⟨ γ3, δ3, t ⟩) :
    exists γ2 δΔ' k',
      ⟨ γ1, δΔ , k ⟩ --->* ⟨ γ2, δΔ' , k' ⟩ /\ Final k' /\
      exists s0,
        ⟨ γ2, δ1, stm_call' Δ δΔ' σ k' ⟩ ---> ⟨ γ2, δ1, s0 ⟩ /\
        ⟨ γ2, δ1, s0⟩ --->* ⟨ γ3, δ3, t ⟩.
  Proof.
    remember (stm_call' Δ δΔ σ k) as s. revert steps δΔ k Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_assign {Γ σ} {γ1 γ3 : RegStore} {δ1 δ3 : LocalStore Γ}
    (x : 𝑿) (xInΓ : InCtx (x,σ) Γ) (s1 t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, δ1, stm_assign x s1 ⟩ --->* ⟨ γ3, δ3, t ⟩) :
    exists γ2 δ2 δ2' s1',
      ⟨ γ1, δ1, s1 ⟩ --->* ⟨ γ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, δ2, stm_assign x s1' ⟩ ---> ⟨ γ2, δ2' , s0 ⟩ /\
        ⟨ γ2, δ2' , s0 ⟩ --->* ⟨ γ3, δ3, t ⟩.
  Proof.
    remember (stm_assign x s1) as s. revert steps x xInΓ s1 Heqs.
    steps_inversion_induction.
  Qed.

  Lemma steps_inversion_bind {Γ τ σ} {γ1 γ3 : RegStore} {δ1 δ3 : LocalStore Γ}
    (s1 : Stm Γ τ) (k : Lit τ -> Stm Γ σ) (t : Stm Γ σ) (final : Final t)
    (steps : ⟨ γ1, δ1, stm_bind s1 k ⟩ --->* ⟨ γ3, δ3, t ⟩) :
    exists γ2 δ2 s1',
      ⟨ γ1, δ1, s1 ⟩ --->* ⟨ γ2, δ2, s1' ⟩ /\ Final s1' /\
      exists (s0 : Stm Γ σ),
        ⟨ γ2, δ2, stm_bind s1' k ⟩ ---> ⟨ γ2, δ2 , s0 ⟩ /\
        ⟨ γ2, δ2 , s0 ⟩ --->* ⟨ γ3, δ3, t ⟩.
  Proof.
    remember (stm_bind s1 k) as s. revert steps s1 k Heqs.
    steps_inversion_induction.
  Qed.

End Inversion.
