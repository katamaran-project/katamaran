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
     SmallStep.Inversion
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module WLP
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import contkit : ContractKit typekit termkit progkit).

  Definition Cont (R A : Type) : Type := (A -> R) -> R.

  Definition DST (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
    (A -> Pred (LocalStore Γ2)) -> Pred (LocalStore Γ1).

  Definition evalDST {Γ1 Γ2 A} (m : DST Γ1 Γ2 A) :
    LocalStore Γ1 -> Cont Prop A :=
    fun δ1 k => m (fun a δ2 => k a) δ1.

  Definition lift {Γ A} (m : Cont Prop A) : DST Γ Γ A :=
    fun k δ => m (fun a => k a δ).

  Definition pure {Γ A} (a : A) : DST Γ Γ A :=
    fun k => k a.
  Definition ap {Γ1 Γ2 Γ3 A B} (mf : DST Γ1 Γ2 (A -> B))
             (ma : DST Γ2 Γ3 A) : DST Γ1 Γ3 B :=
    fun k => mf (fun f => ma (fun a => k (f a))).
  Definition abort {Γ1 Γ2 A} : DST Γ1 Γ2 A :=
    fun k δ => False.
  Definition assert {Γ} (b : bool) : DST Γ Γ bool :=
    fun k δ => Bool.Is_true b /\ k b δ.
  Definition bind {Γ1 Γ2 Γ3 A B} (ma : DST Γ1 Γ2 A) (f : A -> DST Γ2 Γ3 B) : DST Γ1 Γ3 B :=
    fun k => ma (fun a => f a k).
  Definition bindright {Γ1 Γ2 Γ3 A B} (ma : DST Γ1 Γ2 A) (mb : DST Γ2 Γ3 B) : DST Γ1 Γ3 B :=
    bind ma (fun _ => mb).
  Definition bindleft {Γ1 Γ2 Γ3 A B} (ma : DST Γ1 Γ2 A) (mb : DST Γ2 Γ3 B) : DST Γ1 Γ3 A :=
    bind ma (fun a => bind mb (fun _ => pure a)).
  Definition bindblast {Γ1 Γ2 Γ3 A B} {blastA : Blastable A}
    (ma : DST Γ1 Γ2 A) (f : A -> DST Γ2 Γ3 B) : DST Γ1 Γ3 B :=
    fun k => ma (fun a δ2 => blast a (fun a' => f a' k δ2)).
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
  Definition ifthenelse {Γ1 Γ2 A} (b : bool) (t e : DST Γ1 Γ2 A) : DST Γ1 Γ2 A :=
    fun k δ => (b = true -> t k δ) /\ (b = false -> e k δ).

  Arguments abort {_ _ _} / _ _.
  Arguments assert {_} _ / _ _.
  Arguments bind {_ _ _ _ _} _ _ / _ _.
  Arguments bindblast {_ _ _ _ _ _} _ _ / _ _.
  Arguments bindleft {_ _ _ _ _} _ _ / _ _.
  Arguments bindright {_ _ _ _ _} _ _ / _ _.
  Arguments evalDST {_ _ _} _ / _ _.
  Arguments get {_} / _ _.
  Arguments lift {_ _} _ / _ _.
  Arguments meval {_ _} _ / _ _.
  Arguments mevals {_ _} _ / _ _.
  Arguments modify {_ _} _ / _ _.
  Arguments pop {_ _ _} / _ _.
  Arguments pops {_} _ / _ _.
  Arguments pure {_ _} _ / _ _.
  Arguments push {_ _ _} _ / _ _.
  Arguments pushs {_ _} _ / _ _.
  Arguments put {_} _ / _ _.
  Arguments ifthenelse {_ _ _} _ _ _ / _ _.

  Notation "ma >>= f" := (bind ma f) (at level 50, left associativity).
  Notation "ma !>>= f" := (bindblast ma f) (at level 50, left associativity).
  Notation "ma *> mb" := (bindright ma mb) (at level 50, left associativity).
  Notation "ma <* mb" := (bindleft ma mb) (at level 50, left associativity).

  Fixpoint WLP {Γ τ} (s : Stm Γ τ) : DST Γ Γ (Lit τ) :=
    match s in (Stm _ τ) return (DST Γ Γ (Lit τ)) with
    | stm_lit _ l => pure l
    | stm_assign x s => WLP s >>= fun v => modify (fun δ => δ [ x ↦ v ]) *> pure v
    | stm_let x σ s k => WLP s >>= push *> WLP k <* pop
    | stm_exp e => meval e
    | stm_assert e1 e2  => meval e1 >>= assert
    | stm_if e s1 s2 => meval e >>= fun b => ifthenelse b (WLP s1) (WLP s2)
    | stm_fail _ _ => abort
    | stm_seq s1 s2 => WLP s1 *> WLP s2
    | stm_call' Δ δ τ s => lift (evalDST (WLP s) δ)

    | stm_call f es =>
      mevals es >>= fun δf_in =>
      match CEnv f with
      | ContractNoFail _ _ pre post =>
        fun POST δ => uncurry' pre δf_in /\ forall v, uncurry' post δf_in v -> POST v δ
      | ContractTerminateNoFail _ _ pre post => abort (* NOT IMPLEMENTED *)
      | ContractTerminate _ _ pre post => abort (* NOT IMPLEMENTED *)
      | ContractNone _ _ => abort (* NOT IMPLEMENTED *)
      end
    | stm_let' δ k => pushs δ *> WLP k <* pops _
    | stm_match_list e alt_nil xh xt alt_cons =>
      meval e !>>= fun v =>
      match v with
      | nil => WLP alt_nil
      | cons vh vt => push vh *> @push _ _ (ty_list _) vt *> WLP alt_cons <* pop <* pop
      end
    | stm_match_sum e xinl altinl xinr altinr =>
      meval e !>>= fun v =>
      match v with
      | inl v => push v *> WLP altinl <* pop
      | inr v => push v *> WLP altinr <* pop
      end
    | stm_match_pair e xl xr rhs =>
      meval e !>>= fun v =>
      let (vl , vr) := v in
      push vl *> push vr *> WLP rhs <* pop <* pop
    | stm_match_enum E e alts =>
      meval e !>>= fun v =>
      WLP (alts v)
    | stm_match_tuple e p rhs =>
      meval e >>= fun v =>
      pushs (tuple_pattern_match p v) *> WLP rhs <* pops _
    | stm_match_union T e xs rhs =>
      meval e !>>= fun v =>
      let (K , tv) := v in
      push (untag tv) *> WLP (rhs K) <* pop
    | stm_match_record R e p rhs =>
      meval e >>= fun v =>
      pushs (record_pattern_match p v) *> WLP rhs <* pops _
    | stm_bind s k =>
      WLP s >>= fun v => WLP (k v)
    end.

  Definition ValidContract {Γ τ} (c : Contract Γ τ) (s : Stm Γ τ) : Prop :=
    match c with
    | ContractNoFail _ _ pre post =>
      @Forall' _ Ty Lit Γ
               (fun δin => uncurry pre δin ->
                           WLP s (fun vout δout => uncurry post δin vout) δin)
    | ContractTerminateNoFail _ _ _ _ => False
    | ContractTerminate _ _ _ _ => False
    | ContractNone _ _ => False
    end.

  Definition ValidContractEnv (cenv : ContractEnv) : Prop :=
    forall σs σ (f : 𝑭 σs σ), ValidContract (cenv σs σ f) (Pi f).

End WLP.
