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
     Dijkstra
     Syntax.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.
Local Open Scope Z_scope.
Local Open Scope env_scope.

Module WLPPrograms (termkit : TermKit) (Export progkit : ProgramKit termkit).

  Inductive Contract (Δ : NCtx 𝑿 Ty) (τ : Ty) : Type :=
  | ContractNoFail
      (pre : abstract_named Lit Δ (RegStore -> Prop))
      (post: abstract_named Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractTerminateNoFail
      (pre : abstract_named Lit Δ (RegStore -> Prop))
      (post: abstract_named Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractTerminate
      (pre : abstract_named Lit Δ (RegStore -> Prop))
      (post: abstract_named Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractNone.

  Definition ContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), Contract Δ τ.
  Definition ContractEnvEx : Type :=
    forall Δ τ (f : 𝑭𝑿 Δ τ), Contract Δ τ.

End WLPPrograms.

Module Type WLPContractKit (termkit : TermKit) (Export progkit : ProgramKit termkit).

  Module WLPPM := WLPPrograms termkit progkit.
  Export WLPPM.

  Parameter Inline CEnv   : ContractEnv.
  Parameter Inline CEnvEx : ContractEnvEx.

End WLPContractKit.

Module WLP
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (Export contkit : WLPContractKit termkit progkit).

  Class Blastable (A : Type) : Type :=
    { blast : A -> (A -> Prop) -> Prop;
      blast_sound:
        forall (a : A) (k : A -> Prop),
          blast a k <-> k a
    } .

  Program Instance blastable_bool : Blastable bool :=
    {| blast b k := (b = true -> k true) /\ (b = false -> k false) |}.
  Solve All Obligations with intros []; intuition; congruence.

  Program Instance blastable_int : Blastable Z :=
    {| blast z k := k z |}.
  Solve All Obligations with intuition.

  Program Instance blastable_string : Blastable string :=
    {| blast s k := k s |}.
  Solve All Obligations with intuition.

  Program Instance blastable_unit : Blastable unit :=
    {| blast u k := k tt |}.
  Solve All Obligations with intros []; intuition; congruence.

  Program Instance blastable_list {A : Type} : Blastable (list A) :=
    {| blast xs k :=
         (forall (y : A) (ys : list A), xs = cons y ys -> k (cons y ys)) /\
         (xs = nil -> k nil)
    |}.
  Solve All Obligations with intros ? []; intuition; congruence.

  Program Instance blastable_prod {A B : Type} : Blastable (A * B) :=
    { blast ab k := k (fst ab , snd ab) }.
  Solve All Obligations with intuition.

  Program Instance blastable_sigt {A} {B : A -> Type} : Blastable (sigT B) :=
    {| blast ab k := k (existT (projT1 ab) (projT2 ab)) |}.
  Solve All Obligations with intros ? ? []; intuition; congruence.

  Program Instance blastable_sum {A B : Type} : Blastable (A + B) :=
    {| blast ab k :=
         (forall (a : A), ab = inl a -> k (inl a)) /\
         (forall (b : B), ab = inr b -> k (inr b))
    |}.
  Solve All Obligations with intros ? ? []; intuition; congruence.

  Program Instance blastable_bit : Blastable Bit :=
    {| blast b k := (b = bitzero -> k bitzero) /\ (b = bitone -> k bitone) |}.
  Solve All Obligations with intros []; intuition; congruence.

  Program Instance blastable_word {n} : Blastable (Word.word n) :=
    {| blast w k := k w |}.
  Solve All Obligations with intuition.

  Program Instance blastable_env {B D} {Γ : Ctx B} : Blastable (Env D Γ) :=
    {| blast :=
         (fix blast {Δ : Ctx B} (E : Env D Δ) {struct E} : (Env D Δ -> Prop) -> Prop :=
         match E in Env _ Δ return (Env D Δ -> Prop) -> Prop with
         | env_nil => fun k => k env_nil
         | env_snoc E b db => fun k => blast E (fun E' => k (env_snoc E' b db))
         end) Γ
    |}.
  Next Obligation.
    intros ? ? ? E; induction E; cbn.
    - reflexivity.
    - intro k; exact (IHE (fun E' : Env D Γ => k (env_snoc E' b db))).
  Defined.
  Instance blastable_env' {X T : Set} {D} {Δ : NCtx X T} : Blastable (NamedEnv D Δ) :=
    blastable_env.

  Program Instance Blastable_Finite `{finite.Finite A} : Blastable A :=
    {| blast a POST :=
         match finite.enum A with
         | nil       => True
         | cons x xs => List.fold_left (fun P y => P /\ (a = y -> POST y)) xs (a = x -> POST x)
         end
    |}.
  Admit Obligations.

  Program Instance blastable_union (U : 𝑼) : Blastable (𝑼𝑻 U) :=
    {| blast v k :=
         forall (K : 𝑼𝑲 U),
           blast K (fun K =>
                      forall p,
                        v = 𝑼_fold (existT K p) ->
                        k (𝑼_fold (existT K p)))
    |}.
  Admit Obligations.
  (* Next Obligation. *)
  (*   intros; cbn; constructor; intro hyp. *)
  (*   - rewrite <- (@𝑼_fold_unfold U a) in *. *)
  (*     destruct (𝑼_unfold a) as [K v] eqn:eq_a. *)
  (*     specialize (hyp K). *)
  (*     rewrite blast_sound in hyp. *)
  (*     now apply hyp. *)
  (*   - intros K. *)
  (*     rewrite blast_sound. *)
  (*     now intros; subst. *)
  (* Qed. *)

  Program Instance blastable_record (R : 𝑹) : Blastable (𝑹𝑻 R) :=
    {| blast v k := k (𝑹_fold (𝑹_unfold v)) |}.
  Next Obligation.
    cbn; intros; now rewrite 𝑹_fold_unfold.
  Qed.

  Instance blastable_lit {σ} : Blastable (Lit σ) :=
    match σ with
    | ty_int => blastable_int
    | ty_bool => blastable_bool
    | ty_bit => blastable_bit
    | ty_string => blastable_string
    | ty_list σ0 => @blastable_list (Lit σ0)
    | ty_prod σ1 σ2 => @blastable_prod (Lit σ1) (Lit σ2)
    | ty_sum σ1 σ2 => @blastable_sum (Lit σ1) (Lit σ2)
    | ty_unit => blastable_unit
    | ty_enum E => Blastable_Finite
    | ty_bvec n => blastable_word
    | ty_tuple σs => Ctx_rect
                       (fun σs => Blastable (Lit (ty_tuple σs)))
                       blastable_unit
                       (fun σs blast_σs σ => @blastable_prod (EnvRec Lit σs) (Lit σ))
                       σs
    | ty_union U => blastable_union U
    | ty_record R => blastable_record R
    end%type.

  Fixpoint eval_prop_true {Γ : PCtx} (e : Exp Γ ty_bool) (δ : LocalStore Γ) {struct e} : Prop -> Prop :=
    match e return Prop -> Prop -> Prop with
    | exp_binop binop_eq e1 e2 => fun _ k => eval e1 δ = eval e2 δ -> k
    | exp_binop binop_le e1 e2 => fun _ k => eval e1 δ <= eval e2 δ -> k
    | exp_binop binop_lt e1 e2 => fun _ k => eval e1 δ < eval e2 δ -> k
    | exp_binop binop_gt e1 e2 => fun _ k => eval e1 δ > eval e2 δ -> k
    | exp_binop binop_and e1 e2 => fun _ k => eval_prop_true e1 δ (eval_prop_true e2 δ k)
    | exp_binop binop_or e1 e2 => fun _ k => eval_prop_true e1 δ k /\ eval_prop_true e2 δ k
    | exp_not e => fun _ k => eval_prop_false e δ k
    | _ => fun e k => e -> k
    end (eval e δ = true)
  with eval_prop_false {Γ : PCtx} (e : Exp Γ ty_bool) (δ : LocalStore Γ) {struct e} : Prop -> Prop :=
    match e return Prop -> Prop -> Prop with
    | exp_binop binop_eq e1 e2 => fun _ k => eval e1 δ <> eval e2 δ -> k
    | exp_binop binop_le e1 e2 => fun _ k => eval e1 δ > eval e2 δ -> k
    | exp_binop binop_lt e1 e2 => fun _ k => eval e1 δ >= eval e2 δ -> k
    | exp_binop binop_gt e1 e2 => fun _ k => eval e1 δ <= eval e2 δ -> k
    | exp_binop binop_and e1 e2 => fun _ k => eval_prop_false e1 δ k /\ eval_prop_false e2 δ k
    | exp_binop binop_or e1 e2 => fun _ k => eval_prop_false e1 δ (eval_prop_false e2 δ k)
    | exp_not e => fun _ k => eval_prop_true e δ k
    | _ => fun e k => e -> k
    end (eval e δ = false).

  Definition bindblast {G I : Type} {L : I -> Type} {Γ1 Γ2 Γ3 A B} {blastA : Blastable A}
    (ma : DST G L Γ1 Γ2 A) (f : A -> DST G L Γ2 Γ3 B) : DST G L Γ1 Γ3 B :=
    fun k => ma (fun a δ2 s2 => blast a (fun a' => f a' k δ2 s2)).
  Definition meval {G Γ σ} (e : Exp Γ σ) : DST G LocalStore Γ Γ (Lit σ) :=
    bind get_local (fun δ => pure (eval e δ)).
  Definition mevals {G Γ Δ} (es : NamedEnv (Exp Γ) Δ) : DST G LocalStore Γ Γ (LocalStore Δ) :=
    bind get_local (fun δ => pure (evals es δ)).

  Arguments bindblast {_ _ _ _ _ _ _ _ _} _ _ / _ _ _.
  Arguments meval {_ _ _} _ / _ _ _.
  Arguments mevals {_ _ _} _ / _ _ _.

  Local Arguments uncurry_named /.

  (* Notation "ma >>= f" := (bind ma f) (at level 50, left associativity). *)
  Notation "ma !>>= f" := (bindblast ma f) (at level 50, left associativity).
  (* Notation "ma *> mb" := (bindright ma mb) (at level 50, left associativity). *)
  (* Notation "ma <* mb" := (bindleft ma mb) (at level 50, left associativity). *)

  Local Open Scope monad_scope.

  Definition WLPCall {Δ σ} (c : Contract Δ σ) δf_in : Cont (RegStore -> Prop) (Lit σ) :=
    Eval cbn [uncurry_named] in
    match c with
    | ContractNoFail _ _ pre post =>
      fun POST γin => uncurry_named pre δf_in γin /\
                      forall v γout, uncurry_named post δf_in v γout -> POST v γout
    | ContractTerminateNoFail _ _ pre post => fun _ _ => False (* NOT IMPLEMENTED *)
    | ContractTerminate _ _ pre post => fun _ _ => False (* NOT IMPLEMENTED *)
    | ContractNone _ _ => fun _ _ => False (* NOT IMPLEMENTED *)
    end.

  Definition WLP : forall {Γ τ} (s : Stm Γ τ), DST RegStore LocalStore Γ Γ (Lit τ) :=
    Eval cbn [Lit WLPCall abort assert bind bindblast bindleft bindright evalDST
              get_local lift_cont lift_cont_global meval mevals modify_local pop
              pops pure push pushs put_local uncurry_named ] in
    fix WLP {Γ τ} (s : Stm Γ τ) : DST RegStore LocalStore Γ Γ (Lit τ) :=
    match s with
    | stm_lit _ l => pure l
    | stm_assign x s => WLP s >>= fun v => modify_local (fun δ => δ ⟪ x ↦ v ⟫) *> pure v
    | stm_let x σ s k => WLP s >>= fun v => push σ v *> WLP k <* pop
    | stm_exp e => meval e
    | stm_assertk e1 e2 k  => meval e1 >>= fun v => assert v *> WLP k
    | stm_if e s1 s2 => fun POST δ γ =>
                          eval_prop_true e δ (WLP s1 POST δ γ) /\
                          eval_prop_false e δ (WLP s2 POST δ γ)
    | stm_fail _ _ => abort
    | stm_seq s1 s2 => WLP s1 *> WLP s2
    | stm_call_frame δ s => lift_cont_global (evalDST (WLP s) δ)
    | stm_call f es => mevals es >>= fun δf_in => lift_cont_global (WLPCall (CEnv f) δf_in)
    | stm_call_external f es => mevals es >>= fun δf_in => lift_cont_global (WLPCall (CEnvEx f) δf_in)
    | stm_block δ k => pushs δ *> WLP k <* pops _
    | stm_match_list e alt_nil xh xt alt_cons =>
      meval e !>>= fun v =>
      match v with
      | nil => WLP alt_nil
      | cons vh vt => push _ vh *> push (ty_list _) vt *> WLP alt_cons <* pop <* pop
      end
    | stm_match_sum e xinl altinl xinr altinr =>
      meval e !>>= fun v =>
      match v with
      | inl v => push _ v *> WLP altinl <* pop
      | inr v => push _ v *> WLP altinr <* pop
      end
    | stm_match_pair e xl xr rhs =>
      meval e !>>= fun v =>
      let (vl , vr) := v in
      push _ vl *> push _ vr *> WLP rhs <* pop <* pop
    | stm_match_enum E e alts =>
      meval e !>>= fun v =>
      WLP (alts v)
    | stm_match_tuple e p rhs =>
      meval e >>= fun v =>
      pushs (tuple_pattern_match p v) *> WLP rhs <* pops _
    | stm_match_union T e alt__pat alt__rhs =>
      meval e !>>= fun v =>
      let (K , tv) := 𝑼_unfold v in
      pushs (pattern_match (alt__pat K) tv) *> WLP (alt__rhs K) <* pops _
    | stm_match_record R e p rhs =>
      meval e >>= fun v =>
      pushs (record_pattern_match p (𝑹_unfold v)) *> WLP rhs <* pops _
    | stm_read_register r => get_global >>= (fun γ => pure (read_register γ r))
    | stm_write_register r e => meval e >>=
        (fun v => modify_global (fun γ => write_register γ r v) *> pure v)
    | stm_bind s k => WLP s >>= fun v => WLP (k v)
    | stm_debugk k => WLP k
    end.

  Definition ValidContract {Γ τ} (c : Contract Γ τ) (s : Stm Γ τ) : Prop :=
    match c with
    | ContractNoFail _ _ pre post =>
      Forall (fun δin => forall γin,
                  uncurry pre δin γin ->
                  WLP s (fun vout δout => uncurry post δin vout) δin γin)
    | ContractTerminateNoFail _ _ _ _ => False
    | ContractTerminate _ _ _ _ => False
    | ContractNone _ _ => True
    end.

  Definition ValidContractEnv (cenv : ContractEnv) : Prop :=
    forall Δ σ (f : 𝑭 Δ σ), ValidContract (cenv Δ σ f) (Pi f).

  Definition ValidContractEnvEx (cenv : ContractEnvEx) : Prop :=
    forall Δ σ (f : 𝑭𝑿 Δ σ),
      match cenv Δ σ f with
      | ContractNoFail _ _ pre post =>
        forall (δ : LocalStore Δ) (γ γ' : RegStore) (μ μ' : Memory) (res : string + Lit σ),
          ExternalCall f δ res γ γ' μ μ' ->
          uncurry pre δ γ ->
          match res with
          | inl _ => False
          | inr v => uncurry post δ v γ'
          end
      | ContractTerminateNoFail _ _ _ _ => False
      | ContractTerminate _ _ _ _ => False
      | ContractNone _ _ => True
      end.

End WLP.
