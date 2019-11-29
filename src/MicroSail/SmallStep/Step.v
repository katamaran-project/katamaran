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
     Strings.String.
From MicroSail Require Import
     Syntax.

Set Implicit Arguments.

Module SmallStep
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Import CtxNotations.
  Import EnvNotations.

  Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (γ1 γ2 : RegStore) (δ1 δ2 : LocalStore Γ) (s1 s2 : Stm Γ σ), Prop :=

  | step_stm_exp
      (γ : RegStore) (δ : LocalStore Γ) (σ : Ty) (e : Exp Γ σ) :
      ⟨ γ , δ , stm_exp e ⟩ ---> ⟨ γ , δ , stm_lit σ (eval e δ) ⟩

  | step_stm_let_value
      (γ : RegStore) (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (v : Lit τ) (k : Stm (Γ ▻ (x , τ)) σ) :
      ⟨ γ , δ , stm_let x τ (stm_lit τ v) k ⟩ ---> ⟨ γ , δ , stm_let' (env_snoc env_nil (x,τ) v) k ⟩
  | step_stm_let_fail
      (γ : RegStore) (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (s : string) (k : Stm (Γ ▻ (x , τ)) σ) :
      ⟨ γ , δ , stm_let x τ (stm_fail τ s) k ⟩ ---> ⟨ γ , δ , stm_fail σ s ⟩
  | step_stm_let_step
      (γ γ' : RegStore) (δ δ' : LocalStore Γ) (x : 𝑿) (τ σ : Ty)
      (s : Stm Γ τ) (s' : Stm Γ τ) (k : Stm (Γ ▻ (x , τ)) σ) :
      ⟨ γ , δ , s ⟩ ---> ⟨ γ' , δ' , s' ⟩ ->
      ⟨ γ , δ , stm_let x τ s k ⟩ ---> ⟨ γ', δ' , stm_let x τ s' k ⟩
  | step_stm_let'_value
      (γ : RegStore) (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (v : Lit σ) :
      ⟨ γ , δ , stm_let' δΔ (stm_lit σ v) ⟩ ---> ⟨ γ , δ , stm_lit σ v ⟩
  | step_stm_let'_fail
      (γ : RegStore) (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (s : string) :
      ⟨ γ , δ , stm_let' δΔ (stm_fail σ s) ⟩ ---> ⟨ γ , δ , stm_fail σ s ⟩
  | step_stm_let'_step
      (γ γ' : RegStore) (δ δ' : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ δΔ' : LocalStore Δ) (σ : Ty) (k k' : Stm (Γ ▻▻ Δ) σ) :
      ⟨ γ , δ ►► δΔ , k ⟩ ---> ⟨ γ', δ' ►► δΔ' , k' ⟩ ->
      ⟨ γ , δ , stm_let' δΔ k ⟩ ---> ⟨ γ' , δ' , stm_let' δΔ' k' ⟩

  | step_stm_seq_step
      (γ γ' : RegStore) (δ δ' : LocalStore Γ) (τ σ : Ty) (s s' : Stm Γ τ) (k : Stm Γ σ) :
      ⟨ γ , δ , s ⟩ ---> ⟨ γ' , δ' , s' ⟩ ->
      ⟨ γ , δ , stm_seq s k ⟩ ---> ⟨ γ', δ' , stm_seq s' k ⟩
  | step_stm_seq_value
      (γ : RegStore) (δ : LocalStore Γ) (τ σ : Ty) (v : Lit τ) (k : Stm Γ σ) :
      ⟨ γ , δ , stm_seq (stm_lit τ v) k ⟩ ---> ⟨ γ , δ , k ⟩
  | step_stm_seq_fail
      (γ : RegStore) (δ : LocalStore Γ) (τ σ : Ty) (s : string) (k : Stm Γ σ) :
      ⟨ γ , δ , stm_seq (stm_fail τ s) k ⟩ ---> ⟨ γ , δ , stm_fail σ s ⟩

  | step_stm_call
      (γ : RegStore) (δ : LocalStore Γ) {σs σ} {f : 𝑭 σs σ} (es : Env' (Exp Γ) σs) :
      ⟨ γ , δ , stm_call f es ⟩ --->
      ⟨ γ , δ , stm_call' σs (evals es δ) σ (Pi f) ⟩
  | step_stm_call'_step
      (γ γ' : RegStore) (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) {δΔ δΔ' : LocalStore Δ} (τ : Ty)
      (s s' : Stm Δ τ) :
      ⟨ γ , δΔ , s ⟩ ---> ⟨ γ' , δΔ' , s' ⟩ ->
      ⟨ γ , δ , stm_call' Δ δΔ τ s ⟩ ---> ⟨ γ' , δ , stm_call' Δ δΔ' τ s' ⟩
  | step_stm_call'_value
      (γ : RegStore) (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (v : Lit τ) :
      ⟨ γ , δ , stm_call' Δ δΔ τ (stm_lit τ v) ⟩ ---> ⟨ γ , δ , stm_lit τ v ⟩
  | step_stm_call'_fail
      (γ : RegStore) (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (s : string) :
      ⟨ γ , δ , stm_call' Δ δΔ τ (stm_fail τ s) ⟩ ---> ⟨ γ , δ , stm_fail τ s ⟩

  | step_stm_assign_value
      (γ : RegStore) (δ : LocalStore Γ) (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} (v : Lit σ) :
      ⟨ γ , δ , stm_assign x (stm_lit σ v) ⟩ ---> ⟨ γ , δ ⟪ x ↦ v ⟫ , stm_lit σ v ⟩
  | step_stm_assign_fail
      (γ : RegStore) (δ : LocalStore Γ) (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} (s : string) :
      ⟨ γ , δ , stm_assign x (stm_fail σ s) ⟩ ---> ⟨ γ , δ , stm_fail σ s ⟩
  | step_stm_assign_step
      (γ γ' : RegStore) (δ δ' : LocalStore Γ) (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} (s s' : Stm Γ σ) :
      ⟨ γ , δ , s ⟩ ---> ⟨ γ' , δ' , s' ⟩ ->
      ⟨ γ , δ , stm_assign x s ⟩ ---> ⟨ γ' , δ' , stm_assign x s' ⟩

  | step_stm_if
      (γ : RegStore) (δ : LocalStore Γ) (e : Exp Γ ty_bool) (σ : Ty) (s1 s2 : Stm Γ σ) :
      ⟨ γ , δ , stm_if e s1 s2 ⟩ ---> ⟨ γ , δ , if eval e δ then s1 else s2 ⟩
  | step_stm_assert
      (γ : RegStore) (δ : LocalStore Γ) (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) :
      ⟨ γ , δ , stm_assert e1 e2 ⟩ --->
      ⟨ γ , δ , if eval e1 δ then stm_lit ty_bool true else stm_fail ty_bool (eval e2 δ) ⟩
  | step_stm_match_list
      (γ : RegStore) (δ : LocalStore Γ) {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
      (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh , σ) ▻ (xt , ty_list σ)) τ) :
      ⟨ γ , δ , stm_match_list e alt_nil xh xt alt_cons ⟩ --->
      ⟨ γ , δ , match eval e δ with
                | nil => alt_nil
                | cons vh vt => stm_let' (env_snoc (env_snoc env_nil (xh,σ) vh) (xt,ty_list σ) vt) alt_cons
                end
      ⟩
  | step_stm_match_sum
      (γ : RegStore) (δ : LocalStore Γ) {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr , σinr)) τ) :
      ⟨ γ , δ , stm_match_sum e xinl alt_inl xinr alt_inr ⟩ --->
      ⟨ γ , δ , match eval e δ with
                | inl v => stm_let' (env_snoc env_nil (xinl,σinl) v) alt_inl
                | inr v => stm_let' (env_snoc env_nil (xinr,σinr) v) alt_inr
                end
      ⟩
  | step_stm_match_pair
      (γ : RegStore) (δ : LocalStore Γ) {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2)) (xl xr : 𝑿)
      (rhs : Stm (Γ ▻ (xl , σ1) ▻ (xr , σ2)) τ) :
      ⟨ γ , δ , stm_match_pair e xl xr rhs ⟩ --->
      ⟨ γ , δ , let (vl , vr) := eval e δ in
                stm_let' (env_snoc (env_snoc env_nil (xl,σ1) vl) (xr,σ2) vr) rhs
      ⟩
  | step_stm_match_enum
      (γ : RegStore) (δ : LocalStore Γ) {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty}
      (alts : forall (K : 𝑬𝑲 E), Stm Γ τ) :
      ⟨ γ , δ , stm_match_enum E e alts ⟩ ---> ⟨ γ , δ , alts (eval e δ) ⟩
  | step_stm_match_tuple
      (γ : RegStore) (δ : LocalStore Γ) {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
      (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ)
      {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
      ⟨ γ , δ , stm_match_tuple e p rhs ⟩ --->
      ⟨ γ , δ , stm_let' (tuple_pattern_match p (eval e δ)) rhs ⟩

  | step_stm_match_union
      (γ : RegStore) (δ : LocalStore Γ) {U : 𝑼} (e : Exp Γ (ty_union U)) {τ : Ty}
      (altx : forall (K : 𝑼𝑲 U), 𝑿)
      (alts : forall (K : 𝑼𝑲 U), Stm (ctx_snoc Γ (altx K , 𝑼𝑲_Ty K)) τ) :
      ⟨ γ , δ , stm_match_union U e altx alts ⟩ --->
      ⟨ γ , δ , let (K , v) := eval e δ in
                stm_let' (env_snoc env_nil (altx K, 𝑼𝑲_Ty K) (untag v)) (alts K)
      ⟩
  | step_stm_match_record
      (γ : RegStore) (δ : LocalStore Γ) {R : 𝑹} {Δ : Ctx (𝑿 * Ty)}
      (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
      {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
      ⟨ γ , δ , stm_match_record R e p rhs ⟩ --->
      ⟨ γ , δ , stm_let' (record_pattern_match p (eval e δ)) rhs ⟩

  | step_stm_reg_register
      (γ : RegStore) (δ : LocalStore Γ) {σ : Ty} (r : 𝑹𝑬𝑮 σ) :
      ⟨ γ, δ, stm_read_register r ⟩ ---> ⟨ γ, δ, stm_lit σ (γ σ r) ⟩
  | step_stm_write_register
      (γ : RegStore) (δ : LocalStore Γ) {σ : Ty} (r : 𝑹𝑬𝑮 σ) (e : Exp Γ σ) :
      let v := eval e δ in
      ⟨ γ, δ, stm_write_register r e ⟩ ---> ⟨ write_register γ r v , δ , stm_lit σ v ⟩

  | step_stm_bind_step
      (γ γ' : RegStore) (δ δ' : LocalStore Γ) (σ τ : Ty) (s s' : Stm Γ σ) (k : Lit σ -> Stm Γ τ) :
      ⟨ γ , δ , s ⟩ ---> ⟨ γ', δ' , s' ⟩ ->
      ⟨ γ , δ , stm_bind s k ⟩ ---> ⟨ γ', δ' , stm_bind s' k ⟩
  | step_stm_bind_value
      (γ : RegStore) (δ : LocalStore Γ) (σ τ : Ty) (v : Lit σ) (k : Lit σ -> Stm Γ τ) :
      ⟨ γ , δ , stm_bind (stm_lit σ v) k ⟩ ---> ⟨ γ , δ , k v ⟩
  | step_stm_bind_fail
      (γ : RegStore) (δ : LocalStore Γ) (σ τ : Ty) (s : string) (k : Lit σ -> Stm Γ τ) :
      ⟨ γ , δ , stm_bind (stm_fail σ s) k ⟩ ---> ⟨ γ , δ , stm_fail τ s ⟩

  where "⟨ γ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , δ2 , s2 ⟩" := (@Step _ _ γ1%env γ2%env δ1%env δ2%env s1%stm s2%stm).

  Inductive Steps {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (γ1 : RegStore) (δ1 : LocalStore Γ) (s1 : Stm Γ σ) : RegStore -> LocalStore Γ -> Stm Γ σ -> Prop :=
  | step_refl : Steps γ1 δ1 s1 γ1 δ1 s1
  | step_trans {γ2 γ3 : RegStore} {δ2 δ3 : LocalStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 γ2 δ1 δ2 s1 s2 -> Steps γ2 δ2 s2 γ3 δ3 s3 -> Steps γ1 δ1 s1 γ3 δ3 s3.

  Notation "⟨ γ1 , δ1 , s1 ⟩ --->* ⟨ γ2 , δ2 , s2 ⟩" := (@Steps _ _ γ1 δ1 s1 γ2 δ2 s2).

End SmallStep.
