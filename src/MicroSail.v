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
     Syntax.

Set Implicit Arguments.

Module Sail
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Import CtxNotations.
  Import EnvNotations.

  Section SmallStep.

    Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (δ₁ δ₂ : LocalStore Γ) (s₁ s₂ : Stm Γ σ), Prop :=

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
        (δ : LocalStore Γ) (e : Exp Γ ty_bool) (σ : Ty) (s₁ s₂ : Stm Γ σ) :
        ⟨ δ , stm_if e s₁ s₂ ⟩ ---> ⟨ δ , if eval e δ then s₁ else s₂ ⟩
    | step_stm_assert
        (δ : LocalStore Γ) (e₁ : Exp Γ ty_bool) (e₂ : Exp Γ ty_string) :
        ⟨ δ , stm_assert e₁ e₂ ⟩ --->
        ⟨ δ , if eval e₁ δ then stm_lit ty_bool true else stm_exit ty_bool (eval e₂ δ) ⟩
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
        (δ : LocalStore Γ) {σ₁ σ₂ τ : Ty} (e : Exp Γ (ty_prod σ₁ σ₂)) (xl xr : 𝑿)
        (rhs : Stm (Γ ▻ (xl , σ₁) ▻ (xr , σ₂)) τ) :
        ⟨ δ , stm_match_pair e xl xr rhs ⟩ --->
        ⟨ δ , let (vl , vr) := eval e δ in
              stm_let' (env_snoc (env_snoc env_nil (xl,σ₁) vl) (xr,σ₂) vr) rhs
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

    Lemma can_form_store_cat (Γ Δ : Ctx (𝑿 * Ty)) (δ : LocalStore (Γ ▻▻ Δ)) :
      exists (δ₁ : LocalStore Γ) (δ₂ : LocalStore Δ), δ = env_cat δ₁ δ₂.
    Proof. pose (env_cat_split δ); eauto. Qed.

    (* Lemma can_form_store_snoc (Γ : Ctx (𝑿 * Ty)) (x : 𝑿) (σ : Ty) (δ : LocalStore (Γ ▻ (x , σ))) : *)
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
      | [ IH: (forall (δ : LocalStore (ctx_cat ?Γ ?Δ)), _),
          δ1: LocalStore ?Γ, δ2: LocalStore ?Δ |- _
        ] => specialize (IH (env_cat δ1 δ2)); T
      (* | [ IH: (forall (δ : LocalStore (ctx_snoc ctx_nil (?x , ?σ))), _), *)
      (*     v: Lit ?σ |- _ *)
      (*   ] => specialize (IH (env_snoc env_nil x σ v)); T *)
      | [ IH: (forall (δ : LocalStore ?Γ), _), δ: LocalStore ?Γ |- _
        ] => solve [ specialize (IH δ); T | clear IH; T ]
      end.

    Local Ltac progress_tac :=
      progress_simpl;
      solve
        [ repeat eexists; constructor; eauto
        | progress_inst progress_tac
        ].

    Lemma progress {Γ σ} (s : Stm Γ σ) :
      Final s \/ forall δ, exists δ' s', ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩.
    Proof. induction s; intros; try progress_tac. Qed.

  End SmallStep.

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

    Notation "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).
    Notation "'⟨' δ1 ',' s1 '⟩' --->* '⟨' δ2 ',' s2 '⟩'" := (@Steps _ _ δ1 s1 δ2 s2).

    Section Soundness.

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
               | [ H1 : ⟨ ?δ1, ?s1 ⟩ ---> ⟨ ?δ2, ?s2 ⟩,
                   H2 : ⟨ ?δ2, ?s2 ⟩ --->* ⟨ ?δ3, ?s3 ⟩ |- _ ]
                 => extend (step_trans H1 H2)
               end;
           steps_inversion_simpl).

      Local Ltac steps_inversion_solve :=
        repeat
          (match goal with
           | [ |- exists t, _ ] => eexists
           | [ |- _ /\ _ ] => constructor
           | [ |- True ] => constructor
           | [ |- ⟨ _ , stm_lit _ _ ⟩ --->* ⟨ _, _ ⟩ ] => constructor 1
           | [ |- ⟨ _ , stm_exit _ _ ⟩ --->* ⟨ _, _ ⟩ ] => constructor 1
           | [ |- ⟨ _ , stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _ , _ ⟩ ] => apply step_stm_let_value
           | [ |- ⟨ _ , stm_let _ _ (stm_exit _ _) _ ⟩ ---> ⟨ _ , _ ⟩ ] => apply step_stm_let_exit
           end; cbn); eauto.

      Local Ltac steps_inversion_induction :=
        let step := fresh in
        induction 1 as [|? ? ? ? ? ? step]; intros; subst;
          [ steps_inversion_simpl
          | inversion step; steps_inversion_inster; steps_inversion_solve
          ].

      Lemma steps_inversion_let {Γ x τ σ} {δ1 δ3 : LocalStore Γ}
        {s1 : Stm Γ τ} {s2 : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final t)
        (steps : ⟨ δ1, stm_let x τ s1 s2 ⟩ --->* ⟨ δ3, t ⟩) :
        exists (δ2 : LocalStore Γ) (s1' : Stm Γ τ),
        (⟨ δ1, s1 ⟩ --->* ⟨ δ2, s1' ⟩) /\ Final s1' /\
        (exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_let x τ s1' s2 ⟩ ---> ⟨ δ2, s0 ⟩) /\ ⟨ δ2, s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_let x τ s1 s2) as s. revert steps s1 s2 Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_let' {Γ Δ σ} (δ1 δ3 : LocalStore Γ)
        (δΔ : LocalStore Δ) (k : Stm (ctx_cat Γ Δ) σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_let' δΔ k ⟩ --->* ⟨ δ3, t ⟩) :
        exists δ2 δΔ' k',
          ⟨ env_cat δ1 δΔ , k ⟩ --->* ⟨ env_cat δ2 δΔ' , k' ⟩ /\ Final k' /\
          exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_let' δΔ' k' ⟩ ---> ⟨ δ2, s0 ⟩) /\ (⟨ δ2, s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_let' δΔ k) as s. revert steps δΔ k Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_seq {Γ τ σ} (δ1 δ3 : LocalStore Γ)
        (s1 : Stm Γ τ) (s2 : Stm Γ σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_seq s1 s2 ⟩ --->* ⟨ δ3, t ⟩) :
        exists δ2 s1',
          ⟨ δ1, s1 ⟩ --->* ⟨ δ2, s1' ⟩ /\ Final s1' /\
          exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_seq s1' s2 ⟩ ---> ⟨ δ2 , s0 ⟩) /\ (⟨ δ2 , s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_seq s1 s2) as s. revert steps s1 s2 Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_app' {Γ Δ σ} (δ1 δ3 : LocalStore Γ)
        (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_app' Δ δΔ σ k ⟩ --->* ⟨ δ3, t ⟩) :
        exists δΔ' k',
          ⟨ δΔ , k ⟩ --->* ⟨ δΔ' , k' ⟩ /\ Final k' /\
          exists s0,
          (⟨ δ1, stm_app' Δ δΔ' σ k' ⟩ ---> ⟨ δ1, s0 ⟩) /\ (⟨ δ1, s0⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_app' Δ δΔ σ k) as s. revert steps δΔ k Heqs.
        steps_inversion_induction.
      Qed.

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
