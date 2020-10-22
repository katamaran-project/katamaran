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
     Strings.String.
From Equations Require Import
     Equations.
From MicroSail Require Import
     Syntax
     Tactics.

Set Implicit Arguments.

Module SmallStep
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Import CtxNotations.
  Import EnvNotations.

  Inductive Step {Γ : Ctx (𝑿 * Ty)} {τ : Ty} (γ : RegStore) (μ : Memory) (δ : LocalStore Γ) :
    forall (γ2 : RegStore) (μ2 : Memory) (δ2 : LocalStore Γ) (s1 s2 : Stm Γ τ), Prop :=

  | step_stm_exp
      (e : Exp Γ τ) :
      ⟨ γ , μ , δ , (stm_exp e) ⟩ ---> ⟨ γ , μ , δ , stm_lit τ (eval e δ) ⟩

  | step_stm_let_value
      (x : 𝑿) (σ : Ty) (v : Lit σ) (k : Stm (Γ ▻ (x,σ)) τ) :
      ⟨ γ , μ , δ , stm_let x σ (stm_lit σ v) k ⟩ ---> ⟨ γ , μ , δ , stm_block (env_snoc env_nil (x,σ) v) k ⟩
  | step_stm_let_fail
      (x : 𝑿) (σ : Ty) (s : string) (k : Stm (Γ ▻ (x,σ)) τ) :
      ⟨ γ , μ , δ, stm_let x σ (stm_fail σ s) k ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_let_step
      (x : 𝑿) (σ : Ty) (s s' : Stm Γ σ) (k : Stm (Γ ▻ (x,σ)) τ)
      (γ' : RegStore) (μ' : Memory) (δ' : LocalStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_let x σ s k ⟩ ---> ⟨ γ', μ' , δ' , stm_let x σ s' k ⟩
  | step_stm_block_value
      (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (v : Lit τ) :
      ⟨ γ , μ , δ , stm_block δΔ (stm_lit τ v) ⟩ ---> ⟨ γ , μ , δ , stm_lit τ v ⟩
  | step_stm_block_fail
      (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (s : string) :
      ⟨ γ , μ , δ , stm_block δΔ (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_block_step
      (Δ : Ctx (𝑿 * Ty)) (δΔ δΔ' : LocalStore Δ) (k k' : Stm (Γ ▻▻ Δ) τ)
      (γ' : RegStore) (μ' : Memory) (δ' : LocalStore Γ) :
      ⟨ γ , μ , δ ►► δΔ , k ⟩ ---> ⟨ γ', μ' , δ' ►► δΔ' , k' ⟩ ->
      ⟨ γ , μ , δ , stm_block δΔ k ⟩ ---> ⟨ γ' , μ' , δ' , stm_block δΔ' k' ⟩

  | step_stm_seq_step
      (σ : Ty) (s s' : Stm Γ σ) (k : Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : LocalStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_seq s k ⟩ ---> ⟨ γ' , μ' , δ' , stm_seq s' k ⟩
  | step_stm_seq_value
      (σ : Ty) (v : Lit σ) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_seq (stm_lit σ v) k ⟩ ---> ⟨ γ , μ , δ , k ⟩
  | step_stm_seq_fail
      (σ : Ty) (s : string) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_seq (stm_fail σ s) k ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩

  | step_stm_call
      {Δ} {f : 𝑭 Δ τ} (es : NamedEnv (Exp Γ) Δ) :
      ⟨ γ , μ , δ , stm_call f es ⟩ --->
      ⟨ γ , μ , δ , stm_call_frame (evals es δ) (Pi f) ⟩
  | step_stm_call_frame_step
      (Δ : Ctx (𝑿 * Ty)) {δΔ δΔ' : LocalStore Δ} (s s' : Stm Δ τ)
      (γ' : RegStore) (μ' : Memory) :
      ⟨ γ , μ , δΔ , s ⟩ ---> ⟨ γ' , μ' , δΔ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_call_frame δΔ s ⟩ ---> ⟨ γ' , μ' , δ , stm_call_frame δΔ' s' ⟩
  | step_stm_call_frame_value
      (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (v : Lit τ) :
      ⟨ γ , μ , δ , stm_call_frame δΔ (stm_lit τ v) ⟩ ---> ⟨ γ , μ , δ , stm_lit τ v ⟩
  | step_stm_call_frame_fail
      (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (s : string) :
      ⟨ γ , μ , δ , stm_call_frame δΔ (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_call_external
      {Δ} {f : 𝑭𝑿 Δ τ} (es : NamedEnv (Exp Γ) Δ) (res : string + Lit τ)
      (γ' : RegStore) (μ' : Memory) :
      ExternalCall f (evals es δ) res γ γ' μ μ' ->
      ⟨ γ  , μ  , δ , stm_call_external f es ⟩ --->
      ⟨ γ' , μ' , δ , match res with
                      | inl msg => stm_fail τ msg
                      | inr v__σ  => stm_lit τ v__σ
                      end ⟩

  | step_stm_assign_value
      (x : 𝑿) {xInΓ : InCtx (x,τ) Γ} (v : Lit τ) :
      ⟨ γ , μ , δ , stm_assign x (stm_lit τ v) ⟩ ---> ⟨ γ , μ , δ ⟪ x ↦ v ⟫ , stm_lit τ v ⟩
  | step_stm_assign_fail
      (x : 𝑿) {xInΓ : InCtx (x,τ) Γ} (s : string) :
      ⟨ γ , μ , δ , stm_assign x (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | step_stm_assign_step
      (x : 𝑿) {xInΓ : InCtx (x,τ) Γ} (s s' : Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : LocalStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_assign x s ⟩ ---> ⟨ γ' , μ' , δ' , stm_assign x s' ⟩

  | step_stm_if
      (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_if e s1 s2 ⟩ ---> ⟨ γ , μ , δ , if eval e δ then s1 else s2 ⟩
  | step_stm_assertk
      (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_assertk e1 e2 k ⟩ --->
      ⟨ γ , μ , δ , if eval e1 δ then k else stm_fail τ (eval e2 δ) ⟩

  | step_stm_match_list
      {σ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
      (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh , σ) ▻ (xt , ty_list σ)) τ) :
      ⟨ γ , μ , δ , stm_match_list e alt_nil xh xt alt_cons ⟩ --->
      ⟨ γ , μ , δ , match eval e δ with
                | nil => alt_nil
                | cons vh vt => stm_block (env_snoc (env_snoc env_nil (xh,σ) vh) (xt,ty_list σ) vt) alt_cons
                end
      ⟩
  | step_stm_match_sum
      {σinl σinr : Ty} (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr , σinr)) τ) :
      ⟨ γ , μ , δ , stm_match_sum e xinl alt_inl xinr alt_inr ⟩ --->
      ⟨ γ , μ , δ , match eval e δ with
                | inl v => stm_block (env_snoc env_nil (xinl,σinl) v) alt_inl
                | inr v => stm_block (env_snoc env_nil (xinr,σinr) v) alt_inr
                end
      ⟩
  | step_stm_match_pair
      {σ1 σ2 : Ty} (e : Exp Γ (ty_prod σ1 σ2)) (xl xr : 𝑿)
      (rhs : Stm (Γ ▻ (xl , σ1) ▻ (xr , σ2)) τ) :
      ⟨ γ , μ , δ , stm_match_pair e xl xr rhs ⟩ --->
      ⟨ γ , μ , δ , let (vl , vr) := eval e δ in
                stm_block (env_snoc (env_snoc env_nil (xl,σ1) vl) (xr,σ2) vr) rhs
      ⟩
  | step_stm_match_enum
      {E : 𝑬} (e : Exp Γ (ty_enum E))
      (alts : forall (K : 𝑬𝑲 E), Stm Γ τ) :
      ⟨ γ , μ , δ , stm_match_enum E e alts ⟩ ---> ⟨ γ , μ , δ , alts (eval e δ) ⟩
  | step_stm_match_tuple
      {Δ σs} (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ) (rhs : Stm (ctx_cat Γ Δ) τ) :
      ⟨ γ , μ , δ , stm_match_tuple e p rhs ⟩ --->
      ⟨ γ , μ , δ , stm_block (tuple_pattern_match p (eval e δ)) rhs ⟩

  | step_stm_match_union
      {U : 𝑼} (e : Exp Γ (ty_union U))
      (alt__ctx : forall (K : 𝑼𝑲 U), Ctx (𝑿 * Ty))
      (alt__pat : forall (K : 𝑼𝑲 U), Pattern (alt__ctx K) (𝑼𝑲_Ty K))
      (alt__rhs : forall (K : 𝑼𝑲 U), Stm (Γ ▻▻ alt__ctx K) τ) :
      ⟨ γ , μ , δ , stm_match_union U e alt__pat alt__rhs ⟩ --->
      ⟨ γ , μ , δ , let (K , v) := 𝑼_unfold (eval e δ) in
                stm_block (pattern_match (alt__pat K) v) (alt__rhs K)
      ⟩
  | step_stm_match_record
      {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
      (p : RecordPat (𝑹𝑭_Ty R) Δ) (rhs : Stm (ctx_cat Γ Δ) τ) :
      ⟨ γ , μ , δ , stm_match_record R e p rhs ⟩ --->
      ⟨ γ , μ , δ , stm_block (record_pattern_match p (𝑹_unfold (eval e δ))) rhs ⟩

  | step_stm_read_register
      (r : 𝑹𝑬𝑮 τ) :
      ⟨ γ, μ , δ, stm_read_register r ⟩ ---> ⟨ γ, μ , δ, stm_lit τ (read_register γ r) ⟩
  | step_stm_write_register
      (r : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
      let v := eval e δ in
      ⟨ γ , μ , δ, stm_write_register r e ⟩ ---> ⟨ write_register γ r v , μ , δ , stm_lit τ v ⟩

  | step_stm_bind_step
      (σ : Ty) (s s' : Stm Γ σ) (k : Lit σ -> Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : LocalStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ', μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_bind s k ⟩ ---> ⟨ γ', μ' , δ' , stm_bind s' k ⟩
  | step_stm_bind_value
      (σ : Ty) (v : Lit σ) (k : Lit σ -> Stm Γ τ) :
      ⟨ γ , μ , δ , stm_bind (stm_lit σ v) k ⟩ ---> ⟨ γ , μ , δ , k v ⟩
  | step_stm_bind_fail
      (σ : Ty) (s : string) (k : Lit σ -> Stm Γ τ) :
      ⟨ γ , μ , δ , stm_bind (stm_fail σ s) k ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩

  where "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Step _ _ γ1%env μ1%env δ1%env γ2%env μ2%env δ2%env s1%stm s2%stm).

  Inductive Steps {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : LocalStore Γ) (s1 : Stm Γ σ) : RegStore -> Memory -> LocalStore Γ -> Stm Γ σ -> Prop :=
  | step_refl : Steps γ1 μ1 δ1 s1 γ1 μ1 δ1 s1
  | step_trans {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : LocalStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> Steps γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 -> Steps γ1 μ1 δ1 s1 γ3 μ3 δ3 s3.

  Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ --->* ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Steps _ _ γ1 μ1 δ1 s1 γ2 μ2 δ2 s2).

  Inductive StepsN {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : LocalStore Γ) (s1 : Stm Γ σ) : nat -> RegStore -> Memory -> LocalStore Γ -> Stm Γ σ -> Prop :=
  | stepsn_refl : StepsN γ1 μ1 δ1 s1 O γ1 μ1 δ1 s1
  | stepsn_trans {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : LocalStore Γ} {s2 s3 : Stm Γ σ} {n} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> StepsN γ2 μ2 δ2 s2 n γ3 μ3 δ3 s3 -> StepsN γ1 μ1 δ1 s1 (S n) γ3 μ3 δ3 s3.

  Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> n ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@StepsN _ _ γ1 μ1 δ1 s1 n γ2 μ2 δ2 s2).

  Lemma steps_stepsn {Γ σ γ1 μ1 δ1 s1 γ3 μ3 δ3 s3} :
    @Steps Γ σ γ1 μ1 δ1 s1 γ3 μ3 δ3 s3 <-> exists n, StepsN γ1 μ1 δ1 s1 n γ3 μ3 δ3 s3.
  Proof.
    split.
    - induction 1; destruct_conjs; eexists; econstructor; eauto.
    - intros [? steps]; induction steps; econstructor; eauto.
  Qed.

  (* Tests if a statement is a final one, i.e. a finished computation. *)
  Ltac microsail_stm_is_final s :=
    lazymatch s with
    | stm_lit _ _  => idtac
    | stm_fail _ _ => idtac
    end.

  (* Tests if a statement has a primitive step, i.e. it can be reduced
     by an axiom rule of the step relation instead of a congruence rule. *)
  Ltac microsail_stm_primitive_step s :=
    first
      [ lazymatch s with
        | stm_call_frame _ ?s' => microsail_stm_is_final s'
        | stm_let _ _ ?s' _    => microsail_stm_is_final s'
        | stm_block _ ?s'      => microsail_stm_is_final s'
        | stm_seq ?s' _        => microsail_stm_is_final s'
        | stm_assign _ ?s'     => microsail_stm_is_final s'
        | stm_bind ?s' _       => microsail_stm_is_final s'
        end
      | lazymatch head s with
        | @stm_call           => idtac
        | @stm_call_external  => idtac
        | @stm_assertk        => idtac
        | @stm_fail           => idtac
        | @stm_exp            => idtac
        | @stm_if             => idtac
        | @stm_lit            => idtac
        | @stm_match_sum      => idtac
        | @stm_match_list     => idtac
        | @stm_match_pair     => idtac
        | @stm_match_enum     => idtac
        | @stm_match_tuple    => idtac
        | @stm_match_union    => idtac
        | @stm_match_record   => idtac
        | @stm_read_register  => idtac
        | @stm_write_register => idtac
        end
      ].

  (* This 'Lemma' simply exists for testing that the above predicate on
     statements is complete with respect to the step relation. *)
  Lemma microsail_stm_primitive_step__complete {Γ σ γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ σ} :
    ⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩ -> True.
    intro step. remember s1 as s1'.
    dependent elimination step;
      match goal with
      | [ H: ⟨ _,_,_,_ ⟩ ---> ⟨ _,_,_,_ ⟩ |- _ ] =>
        (* If there is a step hypothesis then this case represents a congruence
           rule, not an axiom rule. *)
        constructor
      | [ H: ?s1' = s1 |- _ ] =>
        (* Otherwise, it's an axiom rule and the microsail_stm_primitive_step
           tactic should recognize it. *)
        microsail_stm_primitive_step s1'; constructor
      end; fail.
    Abort.

End SmallStep.
