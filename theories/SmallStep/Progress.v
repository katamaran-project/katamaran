(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Georgy Lukyanov                         *)
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
From Katamaran Require Import
     Notations
     SmallStep.Step
     Program.

Module ProgressOn (Import B : Base) (Import P : Program B) (Import STEP : SmallStepOn B P).

  Local Ltac progress_can_form :=
    match goal with
    (* | [ H: CStore (ctx_snoc _ _) |- _ ] => pose proof (can_form_store_snoc H) *)
    (* | [ H: CStore ctx_nil |- _ ] => pose proof (can_form_store_nil H) *)
    | [ H: CStore (ctx.cat _ _) |- _ ] => destruct (env.catView H)
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
    | [ IH: (forall (γ : RegStore) (μ : Memory) (δ : CStore (ctx.cat ?Γ ?Δ)), _),
        γ : RegStore, μ : Memory, δ1: CStore ?Γ, δ2: CStore ?Δ |- _
      ] => specialize (IH γ μ (env.cat δ1 δ2)); T
    (* | [ IH: (forall (δ : CStore (ctx_snoc ctx_nil (?x , ?σ))), _), *)
    (*     v: Val ?σ |- _ *)
    (*   ] => specialize (IH (env.snoc env.nil x σ v)); T *)
    | [ IH: (forall (γ : RegStore) (μ : Memory) (δ : CStore ?Γ), _),
        γ : RegStore, δ: CStore ?Γ |- _
      ] => solve [ specialize (IH γ μ δ); T | clear IH; T ]
    end.

  Lemma progress_foreign
    {Γ Δ : PCtx} {σ : Ty} (f : 𝑭𝑿 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (γ : RegStore) (μ : Memory) (δ : CStore Γ) :
    exists (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) (s' : Stm Γ σ),
      ⟨ γ, μ, δ, stm_foreign f es ⟩ ---> ⟨ γ', μ', δ', s' ⟩.
  Proof.
    destruct (ForeignProgress f (evals es δ) γ μ) as (γ' & μ' & res & p).
    exists γ', μ', δ. eexists; constructor; eauto.
  Qed.

  Local Ltac progress_tac :=
    auto using progress_foreign;
    progress_simpl;
    solve
      [ repeat eexists; constructor; eauto
      | progress_inst progress_tac
      ].

  Lemma progress {Γ σ} (s : Stm Γ σ) :
    Final s \/ forall γ μ δ, exists γ' μ' δ' s', ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩.
  Proof. induction s; intros; try progress_tac. Qed.

End ProgressOn.
