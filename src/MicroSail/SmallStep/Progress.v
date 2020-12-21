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
     Program.Tactics.
From MicroSail Require Import
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Module Progress
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit).
  Module Import SS := SmallStep termkit progkit.

  Lemma can_form_store_cat (Γ Δ : PCtx) (δ : LocalStore (ctx_cat Γ Δ)) :
    exists (δ1 : LocalStore Γ) (δ2 : LocalStore Δ), δ = env_cat δ1 δ2.
  Proof. pose (env_cat_split δ); eauto. Qed.

  (* Lemma can_form_store_snoc (Γ : PCtx) (x : 𝑿) (σ : Ty) (δ : LocalStore (Γ ▻ (x , σ))) : *)
  (*   exists (δ' : LocalStore Γ) (v : Lit σ), δ = env_snoc δ' x σ v. *)
  (* Admitted. *)

  (* Lemma can_form_store_nil (δ : LocalStore ε) : *)
  (*   δ = env_nil. *)
  (* Admitted. *)

  Local Ltac progress_can_form :=
    match goal with
    (* | [ H: LocalStore (ctx_snoc _ _) |- _ ] => pose proof (can_form_store_snoc H) *)
    (* | [ H: LocalStore ctx_nil |- _ ] => pose proof (can_form_store_nil H) *)
    | [ H: LocalStore (ctx_cat _ _) |- _ ] => pose proof (can_form_store_cat _ _ H)
    | [ H: Final ?s |- _ ] => destruct s; cbn in H
    end; destruct_conjs; subst; try contradiction.

  Local Ltac progress_simpl :=
    repeat
      (cbn in *; destruct_conjs; subst;
       try progress_can_form;
       try match goal with
           | [ |- True \/ _] => left; constructor
           | [ |- False \/ _] => right
           | [ |- forall _, _ ] => intro
           | [ H : True |- _ ] => clear H
           | [ H : _ \/ _ |- _ ] => destruct H
           end).

  Local Ltac progress_inst T :=
    match goal with
    | [ IH: (forall (γ : RegStore) (μ : Memory) (δ : LocalStore (ctx_cat ?Γ ?Δ)), _),
        γ : RegStore, μ : Memory, δ1: LocalStore ?Γ, δ2: LocalStore ?Δ |- _
      ] => specialize (IH γ μ (env_cat δ1 δ2)); T
    (* | [ IH: (forall (δ : LocalStore (ctx_snoc ctx_nil (?x , ?σ))), _), *)
    (*     v: Lit ?σ |- _ *)
    (*   ] => specialize (IH (env_snoc env_nil x σ v)); T *)
    | [ IH: (forall (γ : RegStore) (μ : Memory) (δ : LocalStore ?Γ), _),
        γ : RegStore, δ: LocalStore ?Γ |- _
      ] => solve [ specialize (IH γ μ δ); T | clear IH; T ]
    end.

  Lemma progress_call_external
    {Γ Δ : PCtx} {σ : Ty} (f : 𝑭𝑿 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (γ : RegStore) (μ : Memory) (δ : LocalStore Γ) :
    exists (γ' : RegStore) (μ' : Memory) (δ' : LocalStore Γ) (s' : Stm Γ σ),
      ⟨ γ, μ, δ, stm_call_external f es ⟩ ---> ⟨ γ', μ', δ', s' ⟩.
  Proof.
    destruct (ExternalProgress f (evals es δ) γ μ) as (γ' & μ' & res & p).
    exists γ', μ', δ. eexists; constructor; eauto.
  Qed.

  Local Ltac progress_tac :=
    auto using progress_call_external;
    progress_simpl;
    solve
      [ repeat eexists; constructor; eauto
      | progress_inst progress_tac
      ].

  Lemma progress {Γ σ} (s : Stm Γ σ) :
    Final s \/ forall γ μ δ, exists γ' μ' δ' s', ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩.
  Proof. induction s; intros; try progress_tac. Qed.

End Progress.
