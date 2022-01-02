(******************************************************************************)
(* Copyright (c) 2021 Steven Keuchel                                          *)
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
From Katamaran Require Import
     Syntax
     Tactics.

Set Implicit Arguments.

Module Type ProgramKit (termkit : TermKit).

  Module Export TM := Terms termkit.

  (* We choose to make [RegStore] a parameter so the users of the module would be able to
     instantiate it with their own data structure and [read_regsiter]/[write_register]
     functions *)
  Parameter RegStore : Type.
  (* Definition RegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Val σ. *)
  Parameter read_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ), Val σ.
  Parameter write_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ), RegStore.

  Parameter read_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Val σ),
            read_register (write_register γ r v) r = v.

  Parameter read_write_distinct :
    forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ) (v__σ : Val σ),
      existT _ r__σ <> existT _ r__τ ->
      read_register (write_register γ r__σ v__σ) r__τ = read_register γ r__τ.

  (* Parameter write_read : *)
  (*   forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ), *)
  (*     read_register (write_register γ r (read_register γ r)) r__τ = *)
  (*     read_register γ r__τ. *)

  (* Parameter write_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Val σ), *)
  (*     write_register (write_register γ r v1) r v2 = write_register γ r v2. *)

  (* Memory model *)
  Parameter Memory : Type.
  (* Step relation for calling an external function. The complete function call
     is done in one step. The result of an external call is either a failure
     with an error message msg (res = inl msg) or a successful computation with
     a result value v (res = inr v).
   *)
  Parameter ForeignCall :
    forall
      {Δ σ} (f : 𝑭𝑿 Δ σ)
      (args : CStore Δ)
      (res  : string + Val σ)
      (γ γ' : RegStore)
      (μ μ' : Memory), Prop.
  Parameter ForeignProgress :
    forall {Δ σ} (f : 𝑭𝑿 Δ σ) (args : CStore Δ) γ μ,
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.

  (* Bind Scope env_scope with Memory. *)
  (* Parameter read_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹), Val ty_int. *)
  (* Parameter write_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Val ty_int), Memory. *)

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), CStore Δ -> Command (Val τ).

End ProgramKit.

Module SmallStep
  (Import termkit : TermKit)
  (Import progKit : ProgramKit termkit).

  Import ctx.notations.
  Import env.notations.

  Reserved Notation "⟨ γ1 , μ1 , c1 ⟩ ---> ⟨ γ2 , μ2 , s2 ⟩" (at level 75, no associativity).

  Inductive Step {A} (γ : RegStore) (μ : Memory) :
    forall (γ2 : RegStore) (μ2 : Memory) (c1 c2 : Command A), Prop :=

  | step_call
      {Δ τ} {f : 𝑭 Δ τ} (vs : CStore Δ) (c : Val τ -> Command A) :
      ⟨ γ , μ , cmd_call f vs c ⟩ --->
      ⟨ γ , μ , cmd_bind (Pi f vs) c ⟩
  | step_foreign
      {Δ τ} {f : 𝑭𝑿 Δ τ} (vs : CStore Δ) (c : Val τ -> Command A)
      (γ' : RegStore) (μ' : Memory) (res : string + Val τ) :
      ForeignCall f vs res γ γ' μ μ' ->
      ⟨ γ  , μ  , cmd_foreign f vs c ⟩ --->
      ⟨ γ' , μ' , match res with
                  | inl msg => cmd_fail
                  | inr v   => c v
                  end ⟩
  | step_read_register
      {τ} (r : 𝑹𝑬𝑮 τ) (c : Val τ -> Command A) :
      ⟨ γ, μ , cmd_read_register r c ⟩ ---> ⟨ γ, μ , c (read_register γ r) ⟩
  | step_write_register
      {τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) (c : Command A) :
      ⟨ γ , μ , cmd_write_register r v c ⟩ ---> ⟨ write_register γ r v , μ , c ⟩

  where "⟨ γ1 , μ1 , c1 ⟩ ---> ⟨ γ2 , μ2 , c2 ⟩" := (@Step _ γ1%env μ1%env γ2%env μ2%env c1 c2).

  Module Mut.

    Definition Mut (Γ1 Γ2 : PCtx) (A : Type) : Type :=
      CStore Γ1 -> Command (CStore Γ2 * A).
    Definition exec_mut {Γ1 Γ2 A} (m : Mut Γ1 Γ2 A) (δ : CStore Γ1) : Command A :=
      cmd_map snd (m δ).

    Definition pure {Γ A} (a : A) : Mut Γ Γ A :=
      fun δ => cmd_return (δ , a).
    Definition bind {Γ1 Γ2 Γ3 A B} (m : Mut Γ1 Γ2 A) (f : A -> Mut Γ2 Γ3 B) : Mut Γ1 Γ3 B :=
      fun δ1 => cmd_bind (m δ1) (fun '(δ2,a) => f a δ2).
    Definition bind_right {Γ1 Γ2 Γ3 A B} (ma : Mut Γ1 Γ2 A) (mb : Mut Γ2 Γ3 B) : Mut Γ1 Γ3 B :=
      bind ma (fun _ => mb).
    Definition map {Γ1 Γ2 A B} (f : A -> B) (ma : Mut Γ1 Γ2 A) : Mut Γ1 Γ2 B :=
      bind ma (fun a => pure (f a )).
    Definition error {Γ1 Γ2 A} : Mut Γ1 Γ2 A :=
      fun _ => @cmd_fail _.
    Definition mcall {Γ Δ τ} (f : 𝑭 Δ τ) (args : CStore Δ) : Mut Γ Γ (Val τ) :=
      fun δ => cmd_call f args (fun v => cmd_return (δ,v)).
    Definition mforeign {Γ Δ τ} (f : 𝑭𝑿 Δ τ) (args : CStore Δ) : Mut Γ Γ (Val τ) :=
      fun δ => cmd_foreign f args (fun v => cmd_return (δ,v)).
    Definition mreadreg {Γ τ} (reg : 𝑹𝑬𝑮 τ) : Mut Γ Γ (Val τ) :=
      fun δ => cmd_read_register reg (fun v => cmd_return (δ,v)).
    Definition mwritereg {Γ τ} (reg : 𝑹𝑬𝑮 τ) (v : Val τ) : Mut Γ Γ unit :=
      fun δ => cmd_write_register reg v (cmd_return (δ,tt)).

    Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
      (d : Mut (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : Mut Γ1 Γ2 A :=
      fun δ1 => cmd_map (fun '(δ2,a) => (env.tail δ2 , a)) (d (δ1 ► (x∷σ ↦ v))).
    Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
      (d : Mut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : Mut Γ1 Γ2 A :=
      fun δ1 => cmd_map (fun '(δ2,a) => (env.drop Δ δ2 , a)) (d (δ1 ►► δΔ)).
    Definition get_local {Γ} : Mut Γ Γ (CStore Γ) :=
      fun δ => cmd_return (δ,δ).
    Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : Mut Γ1 Γ2 unit :=
      fun _ => cmd_return (δ,tt).

    Definition eval_exp {Γ σ} (e : Exp Γ σ) : Mut Γ Γ (Val σ) :=
      fun δ => cmd_return (δ,eval e δ).
    Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : Mut Γ Γ (CStore σs) :=
      fun δ => cmd_return (δ,evals es δ).
    Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : Mut Γ Γ unit :=
      fun δ => cmd_return (δ ⟪ x ↦ v ⟫ , tt).
    Global Arguments assign {Γ} x {σ xIn} v.

    Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity).
    Notation "m1 ;; m2" := (bind_right m1 m2).

  End Mut.
  Import Mut.

  Section Execution.

    Fixpoint exec {Γ τ} (s : Stm Γ τ) : Mut Γ Γ (Val τ) :=
      match s with
      | stm_val _ l => pure l
      | stm_exp e => eval_exp e
      | stm_let x σ s k =>
        v <- exec s ;;
        pushpop v (exec k)
      | stm_block δ k =>
        pushspops δ (exec k)
      | stm_assign x e =>
        v <- exec e ;;
        assign x v ;;
        pure v
      | stm_call f es =>
        bind (eval_exps es) (mcall f)
      | stm_foreign f es =>
        bind (eval_exps es) (mforeign f)
      | stm_lemmak l es k =>
        exec k
      | stm_call_frame δ' s =>
        δ <- get_local ;;
        put_local δ' ;;
        v <- exec s ;;
        put_local δ ;;
        pure v
      | stm_if e s1 s2 =>
        v <- eval_exp e ;;
        if v then exec s1 else exec s2
      | stm_seq s k => exec s ;; exec k
      | stm_assertk e1 _ k =>
        v <- eval_exp e1 ;;
        if v then exec k else error
      | stm_fail _ s =>
        error
      | stm_match_enum E e alts =>
        v <- eval_exp e ;;
        exec (alts v)
      | stm_read_register reg =>
        mreadreg reg
      | stm_write_register reg e =>
        v <- eval_exp e ;;
        mwritereg reg v ;;
        pure v
      | @stm_match_list _ _ σ e s1 xh xt s2 =>
        v <- eval_exp e ;;
        match v with
        | nil      => exec s1
        | cons h t =>
          pushspops
            (env.snoc (env.snoc env.nil (xh∷σ) h) (xt∷ty_list σ) t)
            (exec s2)
        end
      | stm_match_sum e xinl s1 xinr s2 =>
        v <- eval_exp e ;;
        match v with
        | inl v => pushpop v (exec s1)
        | inr v => pushpop v (exec s2)
        end
      | stm_match_prod e xl xr s =>
        v <- eval_exp e ;;
        match v with
        | (vl,vr) =>
          pushspops
            (env.snoc (env.snoc env.nil (xl∷_) vl) (xr∷_) vr)
            (exec s)
        end
      | stm_match_tuple e p rhs =>
        v <- eval_exp e ;;
        pushspops (tuple_pattern_match_val p v) (exec rhs)
      | stm_match_union U e alt__pat alt__rhs =>
        v <- eval_exp e ;;
        match 𝑼_unfold v with
        | existT K v =>
          pushspops (pattern_match_val (alt__pat K) v) (exec (alt__rhs K))
        end
      | stm_match_record R e p rhs =>
        v <- eval_exp e ;;
        pushspops (record_pattern_match_val p v) (exec rhs)
      | stm_bind s k =>
        v <- exec s ;;
        exec (k v)
      | stm_debugk k =>
        exec k
      end.

  End Execution.

End SmallStep.
