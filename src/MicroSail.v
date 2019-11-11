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
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith.

From MicroSail Require Import
     Context
     Environment
     Notation
     SmallStep.Inversion
     SmallStep.Progress
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Module Sail
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progkit : ProgramKit typekit termkit).
  Module SSI := Inversion typekit termkit progkit.
  Import SSI.
  Import SS.

  Import CtxNotations.
  Import EnvNotations.

  Section Predicates.

    Variable CEnv : ContractEnv.

    Definition Cont (R A : Type) : Type := (A -> R) -> R.

    Definition DST (Γ₁ Γ₂ : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      (A -> Pred (LocalStore Γ₂)) -> Pred (LocalStore Γ₁).

    Definition evalDST {Γ₁ Γ₂ A} (m : DST Γ₁ Γ₂ A) :
      LocalStore Γ₁ -> Cont Prop A :=
      fun δ₁ k => m (fun a δ₂ => k a) δ₁.

    Definition lift {Γ A} (m : Cont Prop A) : DST Γ Γ A :=
      fun k δ => m (fun a => k a δ).

    Definition pure {Γ A} (a : A) : DST Γ Γ A :=
      fun k => k a.
    Definition ap {Γ₁ Γ₂ Γ₃ A B} (mf : DST Γ₁ Γ₂ (A -> B))
               (ma : DST Γ₂ Γ₃ A) : DST Γ₁ Γ₃ B :=
      fun k => mf (fun f => ma (fun a => k (f a))).
    Definition abort {Γ₁ Γ₂ A} : DST Γ₁ Γ₂ A :=
      fun k δ => False.
    Definition assert {Γ} (b : bool) : DST Γ Γ bool :=
      fun k δ => Bool.Is_true b /\ k b δ.
    Definition bind {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (f : A -> DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ B :=
      fun k => ma (fun a => f a k).
    Definition bindright {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (mb : DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ B :=
      bind ma (fun _ => mb).
    Definition bindleft {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (mb : DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ A :=
      bind ma (fun a => bind mb (fun _ => pure a)).
    Definition get {Γ} : DST Γ Γ (LocalStore Γ) :=
      fun k δ => k δ δ.
    Definition put {Γ Γ'} (δ' : LocalStore Γ') : DST Γ Γ' unit :=
      fun k _ => k tt δ'.
    Definition modify {Γ Γ'} (f : LocalStore Γ -> LocalStore Γ') : DST Γ Γ' unit :=
      bind get (fun δ => put (f δ)).
    Definition meval {Γ σ} (e : Exp Γ σ) : DST Γ Γ (Lit σ) :=
      bind get (fun δ => pure (eval e δ)).
    Definition mevals {Γ Δ} (es : Env' (Exp Γ) Δ) : DST Γ Γ (Env' Lit Δ) :=
      bind get (fun δ => pure (evals es δ)).
    Definition push {Γ x σ} (v : Lit σ) : DST Γ (ctx_snoc Γ (x , σ)) unit :=
      modify (fun δ => env_snoc δ (x,σ) v).
    Definition pop {Γ x σ} : DST (ctx_snoc Γ (x , σ)) Γ unit :=
      modify (fun δ => env_tail δ).
    Definition pushs {Γ Δ} (δΔ : LocalStore Δ) : DST Γ (ctx_cat Γ Δ) unit :=
      modify (fun δΓ => env_cat δΓ δΔ).
    Definition pops {Γ} Δ : DST (ctx_cat Γ Δ) Γ unit :=
      modify (fun δΓΔ => env_drop Δ δΓΔ).

    Notation "ma >>= f" := (bind ma f) (at level 90, left associativity).
    Notation "ma *> mb" := (bindright ma mb) (at level 90, left associativity).
    Notation "ma <* mb" := (bindleft ma mb) (at level 90, left associativity).

    Fixpoint WLP {Γ τ} (s : Stm Γ τ) : DST Γ Γ (Lit τ) :=
      match s in (Stm _ τ) return (DST Γ Γ (Lit τ)) with
      | stm_lit _ l => pure l
      | stm_assign x e => meval e >>= fun v => modify (fun δ => δ [ x ↦ v ]) *> pure v
      | stm_let x σ s k => WLP s >>= push *> WLP k <* pop
      | stm_exp e => meval e
      | stm_assert e1 e2  => meval e1 >>= assert
      | stm_if e s1 s2 => meval e >>= fun b => if b then WLP s1 else WLP s2
      | stm_exit _ _  => abort
      | stm_seq s1 s2 => WLP s1 *> WLP s2
      | stm_app' Δ δ τ s => lift (evalDST (WLP s) δ)

      | stm_app f es =>
        mevals es >>= fun δf_in =>
        match CEnv f with
        | None => abort (* NOT IMPLEMENTED *)
        | Some c => fun POST δ =>
                      contract_pre_condition c δf_in
                      /\ (forall v, contract_post_condition c v δf_in -> POST v δ)
        end
      | stm_let' δ k => pushs δ *> WLP k <* pops _
      | stm_match_list e alt_nil xh xt alt_cons =>
        meval e >>= fun v =>
        match v with
        | nil => WLP alt_nil
        | cons vh vt => push vh *> @push _ _ (ty_list _) vt *> WLP alt_cons <* pop <* pop
        end
      | stm_match_sum e xinl altinl xinr altinr =>
        meval e >>= fun v =>
        match v with
        | inl v => push v *> WLP altinl <* pop
        | inr v => push v *> WLP altinr <* pop
        end
      | stm_match_pair e xl xr rhs =>
        meval e >>= fun v =>
        let (vl , vr) := v in
        push vl *> push vr *> WLP rhs <* pop <* pop
      | stm_match_tuple e p rhs =>
        meval e >>= fun v =>
        pushs (tuple_pattern_match p v) *> WLP rhs <* pops _
      | stm_match_union e xs rhs =>
        meval e >>= fun v =>
        let (K , tv) := v in
        push (untag tv) *> WLP (rhs K) <* pop
      | stm_match_record R e p rhs =>
        meval e >>= fun v =>
        pushs (record_pattern_match p v) *> WLP rhs <* pops _
      end.

    Section Soundness.

      Definition Triple {Γ τ}
        (PRE : Pred (LocalStore Γ)) (s : Stm Γ τ)
        (POST : Lit τ -> Pred (LocalStore Γ)) : Prop :=
        forall (δ δ' : LocalStore Γ) (v : Lit τ),
          ⟨ δ , s ⟩ --->* ⟨ δ' , stm_lit τ v ⟩ ->
          PRE δ ->
          POST v δ'.

      Ltac wlp_sound_steps_inversion :=
        repeat
          match goal with
          | [ H: ⟨ _, stm_app _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>               dependent destruction H
          | [ H: ⟨ _, stm_app _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
          | [ H: ⟨ _, stm_assert _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
          | [ H: ⟨ _, stm_assert _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           dependent destruction H
          | [ H: ⟨ _, stm_assign _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
          | [ H: ⟨ _, stm_assign _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           dependent destruction H
          | [ H: ⟨ _, stm_exit _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
          | [ H: ⟨ _, stm_exit _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             dependent destruction H
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
          | [ H: ⟨ _, stm_match_tuple _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
          | [ H: ⟨ _, stm_match_tuple _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>    dependent destruction H
          | [ H: ⟨ _, stm_match_union _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>       dependent destruction H
          | [ H: ⟨ _, stm_match_union _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>      dependent destruction H
          | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
          | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => dependent destruction H

          | [ H: ⟨ _, stm_app' _ _ _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] => dependent destruction H
          | [ H: ⟨ _, stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
          | [ H: ⟨ _, stm_let' _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
          | [ H: ⟨ _, stm_seq (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>      dependent destruction H

          | [ H: ⟨ _, stm_app' _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] => apply (steps_inversion_app' HF) in H
          | [ H: ⟨ _, stm_let _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>  apply (steps_inversion_let HF) in H
          | [ H: ⟨ _, stm_let' _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>     apply (steps_inversion_let' HF) in H
          | [ H: ⟨ _, stm_seq _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>      apply (steps_inversion_seq HF) in H
          | [ H: IsLit _ _ _ |- _ ] => apply IsLit_inversion in H
          end.

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
          | Some c=>
            forall (δ δ' : LocalStore σs) (s' : Stm σs σ),
              ⟨ δ, fun_body (Pi f) ⟩ --->* ⟨ δ', s' ⟩ ->
              Final s' ->
              contract_pre_condition c δ ->
              IsLit δ s' (contract_post_condition c)
          | None => True
          end.

      Variable validCEnv : ValidContractEnv CEnv.

      Lemma WLP_sound {Γ σ} (s : Stm Γ σ) :
        forall (δ δ' : LocalStore Γ) (s' : Stm Γ σ), ⟨ δ, s ⟩ --->* ⟨ δ', s' ⟩ -> Final s' ->
          forall (POST : Lit σ -> Pred (LocalStore Γ)), WLP s POST δ -> IsLit δ' s' POST.
      Proof.
        induction s; cbn; repeat unfold
          Triple, abort, assert, bind, bindleft, bindright, evalDST, get,
          lift, meval, mevals, modify, pop, pops, pure, push, pushs, put;
        intros.
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
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
      Qed.

    End Soundness.

  End Predicates.

End Sail.
