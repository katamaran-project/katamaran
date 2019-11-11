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

  Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (δ1 δ2 : LocalStore Γ) (s1 s2 : Stm Γ σ), Prop :=

  | step_stm_exp
      (δ : LocalStore Γ) (σ : Ty) (e : Exp Γ σ) :
      ⟨ δ , stm_exp e ⟩ ---> ⟨ δ , stm_lit σ (eval e δ) ⟩

  | step_stm_let_value
      (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (v : Lit τ) (k : Stm (Γ ▻ (x , τ)) σ) :
      ⟨ δ , stm_let x τ (stm_lit τ v) k ⟩ ---> ⟨ δ , stm_let' (env_snoc env_nil (x,τ) v) k ⟩
  | step_stm_let_exit
      (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (s : string) (k : Stm (Γ ▻ (x , τ)) σ) :
      ⟨ δ , stm_let x τ (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩
  | step_stm_let_step
      (δ : LocalStore Γ) (δ' : LocalStore Γ) (x : 𝑿) (τ σ : Ty)
      (s : Stm Γ τ) (s' : Stm Γ τ) (k : Stm (Γ ▻ (x , τ)) σ) :
      ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
      ⟨ δ , stm_let x τ s k ⟩ ---> ⟨ δ' , stm_let x τ s' k ⟩
  | step_stm_let'_value
      (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (v : Lit σ) :
      ⟨ δ , stm_let' δΔ (stm_lit σ v) ⟩ ---> ⟨ δ , stm_lit σ v ⟩
  | step_stm_let'_exit
      (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (s : string) :
      ⟨ δ , stm_let' δΔ (stm_exit σ s) ⟩ ---> ⟨ δ , stm_exit σ s ⟩
  | step_stm_let'_step
      (δ δ' : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ δΔ' : LocalStore Δ) (σ : Ty) (k k' : Stm (Γ ▻▻ Δ) σ) :
      ⟨ δ ►► δΔ , k ⟩ ---> ⟨ δ' ►► δΔ' , k' ⟩ ->
      ⟨ δ , stm_let' δΔ k ⟩ ---> ⟨ δ' , stm_let' δΔ' k' ⟩

  | step_stm_seq_step
      (δ δ' : LocalStore Γ) (τ σ : Ty) (s s' : Stm Γ τ) (k : Stm Γ σ) :
      ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
      ⟨ δ , stm_seq s k ⟩ ---> ⟨ δ' , stm_seq s' k ⟩
  | step_stm_seq_value
      (δ : LocalStore Γ) (τ σ : Ty) (v : Lit τ) (k : Stm Γ σ) :
      ⟨ δ , stm_seq (stm_lit τ v) k ⟩ ---> ⟨ δ , k ⟩
  | step_stm_seq_exit
      (δ : LocalStore Γ) (τ σ : Ty) (s : string) (k : Stm Γ σ) :
      ⟨ δ , stm_seq (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩

  | step_stm_app
      {δ : LocalStore Γ} {σs σ} {f : 𝑭 σs σ} (es : Env' (Exp Γ) σs) :
      ⟨ δ , stm_app f es ⟩ --->
      ⟨ δ , stm_app' σs (evals es δ) σ (fun_body (Pi f)) ⟩
  | step_stm_app'_step
      {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ δΔ' : LocalStore Δ} (τ : Ty)
      (s s' : Stm Δ τ) :
      ⟨ δΔ , s ⟩ ---> ⟨ δΔ' , s' ⟩ ->
      ⟨ δ , stm_app' Δ δΔ τ s ⟩ ---> ⟨ δ , stm_app' Δ δΔ' τ s' ⟩
  | step_stm_app'_value
      {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (v : Lit τ) :
      ⟨ δ , stm_app' Δ δΔ τ (stm_lit τ v) ⟩ ---> ⟨ δ , stm_lit τ v ⟩
  | step_stm_app'_exit
      {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (s : string) :
      ⟨ δ , stm_app' Δ δΔ τ (stm_exit τ s) ⟩ ---> ⟨ δ , stm_exit τ s ⟩
  | step_stm_assign
      (δ : LocalStore Γ) (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} (e : Exp Γ σ) :
      let v := eval e δ in
      ⟨ δ , stm_assign x e ⟩ ---> ⟨ δ [ x ↦ v ] , stm_lit σ v ⟩
  | step_stm_if
      (δ : LocalStore Γ) (e : Exp Γ ty_bool) (σ : Ty) (s1 s2 : Stm Γ σ) :
      ⟨ δ , stm_if e s1 s2 ⟩ ---> ⟨ δ , if eval e δ then s1 else s2 ⟩
  | step_stm_assert
      (δ : LocalStore Γ) (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) :
      ⟨ δ , stm_assert e1 e2 ⟩ --->
      ⟨ δ , if eval e1 δ then stm_lit ty_bool true else stm_exit ty_bool (eval e2 δ) ⟩
  (* | step_stm_while : *)
  (*   (δ : LocalStore Γ) (w : 𝑾 δ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> *)
  (*   ⟨ δ , stm_while w e s ⟩ ---> *)
  (*   ⟨ δ , stm_if e (stm_seq s (stm_while w e s)) (stm_lit tt) ⟩ *)
  | step_stm_match_list
      (δ : LocalStore Γ) {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
      (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh , σ) ▻ (xt , ty_list σ)) τ) :
      ⟨ δ , stm_match_list e alt_nil xh xt alt_cons ⟩ --->
      ⟨ δ , match eval e δ with
            | nil => alt_nil
            | cons vh vt => stm_let' (env_snoc (env_snoc env_nil (xh,σ) vh) (xt,ty_list σ) vt) alt_cons
            end
      ⟩
  | step_stm_match_sum
      (δ : LocalStore Γ) {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr , σinr)) τ) :
      ⟨ δ , stm_match_sum e xinl alt_inl xinr alt_inr ⟩ --->
      ⟨ δ , match eval e δ with
            | inl v => stm_let' (env_snoc env_nil (xinl,σinl) v) alt_inl
            | inr v => stm_let' (env_snoc env_nil (xinr,σinr) v) alt_inr
            end
      ⟩
  | step_stm_match_pair
      (δ : LocalStore Γ) {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2)) (xl xr : 𝑿)
      (rhs : Stm (Γ ▻ (xl , σ1) ▻ (xr , σ2)) τ) :
      ⟨ δ , stm_match_pair e xl xr rhs ⟩ --->
      ⟨ δ , let (vl , vr) := eval e δ in
            stm_let' (env_snoc (env_snoc env_nil (xl,σ1) vl) (xr,σ2) vr) rhs
      ⟩

  | step_stm_match_tuple
      (δ : LocalStore Γ) {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
      (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ)
      {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
      ⟨ δ , stm_match_tuple e p rhs ⟩ --->
      ⟨ δ , stm_let' (tuple_pattern_match p (eval e δ)) rhs ⟩

  | step_stm_match_union
      (δ : LocalStore Γ) {T : 𝑻} (e : Exp Γ (ty_union T)) {τ : Ty}
      (altx : forall (K : 𝑲 T), 𝑿)
      (alts : forall (K : 𝑲 T), Stm (ctx_snoc Γ (altx K , 𝑲_Ty K)) τ) :
      ⟨ δ , stm_match_union e altx alts ⟩ --->
      ⟨ δ , let (K , v) := eval e δ in
            stm_let' (env_snoc env_nil (altx K,𝑲_Ty K) (untag v)) (alts K)
      ⟩
  | step_stm_match_record
      (δ : LocalStore Γ) {R : 𝑹} {Δ : Ctx (𝑿 * Ty)}
      (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
      {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
      ⟨ δ , stm_match_record R e p rhs ⟩ --->
      ⟨ δ , stm_let' (record_pattern_match p (eval e δ)) rhs ⟩

  where "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).

  Inductive Steps {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (δ1 : LocalStore Γ) (s1 : Stm Γ σ) : LocalStore Γ -> Stm Γ σ -> Prop :=
  | step_refl : Steps δ1 s1 δ1 s1
  | step_trans {δ2 δ3 : LocalStore Γ} {s2 s3 : Stm Γ σ} :
      Step δ1 δ2 s1 s2 -> Steps δ2 s2 δ3 s3 -> Steps δ1 s1 δ3 s3.

  Notation "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).
  Notation "'⟨' δ1 ',' s1 '⟩' --->* '⟨' δ2 ',' s2 '⟩'" := (@Steps _ _ δ1 s1 δ2 s2).

End SmallStep.
