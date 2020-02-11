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
     Syntax.

Set Implicit Arguments.

Delimit Scope outcome_scope with out.
Delimit Scope mutator_scope with mut.

Section Outcome.

  Inductive Outcome (A: Type) : Type :=
  | single (a: A)
  | demonic {I : Set} (os: I -> Outcome A)
  | angelic {I : Set} (os: I -> Outcome A).

  Definition outcome_fail {A : Type} : Outcome A :=
    angelic (fun i : Empty_set => match i with end).
  Definition outcome_block {A : Type} : Outcome A :=
    demonic (fun i : Empty_set => match i with end).

  Fixpoint outcome_map {A B : Type} (f : A -> B) (o : Outcome A) : Outcome B :=
    match o with
    | single a => single (f a)
    | demonic os => demonic (fun i => outcome_map f (os i))
    | angelic os => angelic (fun i => outcome_map f (os i))
    end.

  Fixpoint outcome_bind {A B : Type} (o : Outcome A) (f : A -> Outcome B) : Outcome B :=
    match o with
    | single a => f a
    | demonic os => demonic (fun i => outcome_bind (os i) f)
    | angelic os => angelic (fun i => outcome_bind (os i) f)
    end.

  Definition outcome_demonic_binary {A : Type} (o1 o2 : Outcome A) : Outcome A :=
    demonic (fun b : bool => if b then o1 else o2).
  Definition outcome_angelic_binary {A : Type} (o1 o2 : Outcome A) : Outcome A :=
    angelic (fun b : bool => if b then o1 else o2).

  Fixpoint outcome_satisfy {A : Type} (P : A -> Prop) (o : Outcome A) : Prop :=
    match o with
    | single a   => P a
    | demonic os => forall i, outcome_satisfy P (os i)
    | angelic os => exists i, outcome_satisfy P (os i)
    end.

  Definition outcome_safe {A : Type} (o : Outcome A) : Prop :=
    outcome_satisfy (fun a => True) o.

  Inductive outcome_satisfy_ind {A : Type} (P : A -> Prop) : Outcome A -> Prop :=
  | outcome_satisfy_single  a    :
      P a ->
      outcome_satisfy_ind P (single a)
  | outcome_satisfy_demonic {I os} :
      (forall i, outcome_satisfy_ind P (os i)) ->
      outcome_satisfy_ind P (@demonic _ I os)
  | outcome_satisfy_angelic {I i os} :
      outcome_satisfy_ind P (os i) ->
      outcome_satisfy_ind P (@angelic _ I os).

  Inductive outcome_in {A : Type} (a : A) : Outcome A -> Prop :=
  | outcome_in_single :
      outcome_in a (single a)
  | outcome_in_demonic {I os i} :
      outcome_in a (os i) ->
      outcome_in a (@demonic _ I os)
  | outcome_in_angelic {I os i} :
      outcome_in a (os i) ->
      outcome_in a (@angelic _ I os).

End Outcome.
Bind Scope outcome_scope with Outcome.

Module OutcomeNotations.

  Notation "'⨂' i : I => F" := (demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : outcome_scope.
  Notation "'⨁' i : I => F" := (angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : outcome_scope.

  Infix "⊗" := outcome_demonic_binary (at level 40, left associativity) : outcome_scope.
  Infix "⊕" := outcome_angelic_binary (at level 50, left associativity) : outcome_scope.

  Notation "ma >>= f" := (outcome_bind ma f) (at level 50, left associativity) : outcome_scope.

End OutcomeNotations.

Module Symbolic
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Parameter Inline 𝑺 : Set. (* input: \MIS *)
  Parameter Inline 𝑿to𝑺 : 𝑿 -> 𝑺.

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.

  Import CtxNotations.
  Import EnvNotations.

  Inductive Term (Σ : Ctx (𝑺 * Ty)) : Ty -> Type :=
  | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς , σ) Σ} : Term Σ σ
  | term_lit     (σ : Ty) : Lit σ -> Term Σ σ
  | term_plus    (e1 e2 : Term Σ ty_int) : Term Σ ty_int
  | term_times   (e1 e2 : Term Σ ty_int) : Term Σ ty_int
  | term_minus   (e1 e2 : Term Σ ty_int) : Term Σ ty_int
  | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
  | term_eq      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_le      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_lt      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_gt      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_and     (e1 e2 : Term Σ ty_bool) : Term Σ ty_bool
  | term_or      (e1 e2 : Term Σ ty_bool) : Term Σ ty_bool
  | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
  | term_pair    {σ1 σ2 : Ty} (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ (ty_prod σ1 σ2)
  | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
  | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
  | term_list    {σ : Ty} (es : list (Term Σ σ)) : Term Σ (ty_list σ)
  | term_cons    {σ : Ty} (h : Term Σ σ) (t : Term Σ (ty_list σ)) : Term Σ (ty_list σ)
  | term_nil     {σ : Ty} : Term Σ (ty_list σ)
  (* Experimental features *)
  | term_tuple   {σs : Ctx Ty} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs)
  | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                {p : ctx_nth_is σs n σ} : Term Σ σ
  | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
  | term_record  (R : 𝑹) (es : Env' (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R)
  | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Term Σ σ
  | term_builtin {σ τ : Ty} (f : Lit σ -> Lit τ) (e : Term Σ σ) : Term Σ τ.
  Bind Scope exp_scope with Term.

  Global Arguments term_var {_} _ {_ _}.
  Global Arguments term_tuple {_ _} _%exp.
  Global Arguments term_union {_} _ _.
  Global Arguments term_record {_} _ _.
  Global Arguments term_projrec {_ _} _ _ {_ _}.

  Definition Sub (Σ1 Σ2 : Ctx (𝑺 * Ty)) : Type :=
    forall {ς σ}, InCtx (ς , σ) Σ1 -> Term Σ2 σ.
  (* Hint Unfold Sub. *)

  Section WithSub.
    Context {Σ1 Σ2 : Ctx (𝑺 * Ty)}.
    Variable (ζ : Sub Σ1 Σ2).

    Fixpoint sub_term {σ} (t : Term Σ1 σ) {struct t} : Term Σ2 σ :=
      match t in (Term _ t0) return (Term Σ2 t0) with
      | @term_var _ ς σ0 ςInΣ     => ζ ςInΣ
      | term_lit _ σ0 l           => term_lit Σ2 σ0 l
      | term_plus t1 t2           => term_plus (sub_term t1) (sub_term t2)
      | term_times t1 t2          => term_times (sub_term t1) (sub_term t2)
      | term_minus t1 t2          => term_minus (sub_term t1) (sub_term t2)
      | term_neg t0               => term_neg (sub_term t0)
      | term_eq t1 t2             => term_eq (sub_term t1) (sub_term t2)
      | term_le t1 t2             => term_le (sub_term t1) (sub_term t2)
      | term_lt t1 t2             => term_lt (sub_term t1) (sub_term t2)
      | term_gt t1 t2             => term_gt (sub_term t1) (sub_term t2)
      | term_and t1 t2            => term_and (sub_term t1) (sub_term t2)
      | term_or t1 t2             => term_or (sub_term t1) (sub_term t2)
      | term_not t0               => term_not (sub_term t0)
      | @term_pair _ σ1 σ2 t1 t2  => term_pair (sub_term t1) (sub_term t2)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term t0)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term t0)
      | @term_list _ σ es         => term_list
                                       ((fix sub_terms (ts : list (Term Σ1 σ)) : list (Term Σ2 σ) :=
                                           match ts with
                                           | nil       => nil
                                           | cons t ts => cons (sub_term t) (sub_terms ts)
                                           end) es)
      | term_cons t1 t2           => term_cons (sub_term t1) (sub_term t2)
      | term_nil _                => term_nil Σ2
      | term_tuple es             => term_tuple
                                       ((fix sub_terms {σs} (ts : Env (Term Σ1) σs) : Env (Term Σ2) σs :=
                                           match ts with
                                           | env_nil           => env_nil
                                           | env_snoc ts' _ t' => env_snoc (sub_terms ts') _ (sub_term t')
                                           end
                                        ) _ es)
      | @term_projtup _ _ t _ n p => @term_projtup _ _ (sub_term t) _ n p
      | term_union U K t0         => term_union U K (sub_term t0)
      | term_record R es          => term_record R
                                       ((fix sub_terms {σs} (ts : Env' (Term Σ1) σs) : Env' (Term Σ2) σs :=
                                           match ts with
                                           | env_nil           => env_nil
                                           | env_snoc ts' _ t' => env_snoc (sub_terms ts') _ (sub_term t')
                                           end
                                        ) _ es)
      | term_projrec t rf         => term_projrec (sub_term t) rf
      | term_builtin f t          => term_builtin f (sub_term t)
      end.

  End WithSub.

  Definition SymbolicLocalStore (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type := Env' (Term Σ) Γ.
  Bind Scope env_scope with SymbolicLocalStore.
  Definition SymbolicRegStore (Σ : Ctx (𝑺 * Ty))  : Type := forall σ, 𝑹𝑬𝑮 σ -> Term Σ σ.

  Fixpoint symbolic_eval_exp {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : SymbolicLocalStore Σ Γ) : Term Σ σ :=
    match e in (Exp _ t) return (Term Σ t) with
    | exp_var ς                       => (δ ! ς)%lit
    | exp_lit _ σ0 l                  => term_lit _ σ0 l
    | exp_plus e1 e2                  => term_plus (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_times e1 e2                 => term_times (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_minus e1 e2                 => term_minus (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_neg e0                      => term_neg (symbolic_eval_exp  e0 δ)
    | exp_eq e1 e2                    => term_eq (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_le e1 e2                    => term_le (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_lt e1 e2                    => term_lt (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_gt e1 e2                    => term_gt (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_and e1 e2                   => term_and (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_or e1 e2                    => term_or (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | exp_not e0                      => term_not (symbolic_eval_exp  e0 δ)
    | exp_pair e1 e2                  => term_pair (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | @exp_inl _ σ1 σ2 e0             => @term_inl _ σ1 σ2 (symbolic_eval_exp  e0 δ)
    | @exp_inr _ σ1 σ2 e0             => @term_inr _ σ1 σ2 (symbolic_eval_exp  e0 δ)
    | @exp_list _ σ0 es               => term_list (List.map (fun e : Exp Γ σ0 => symbolic_eval_exp  e δ) es)
    | exp_cons e1 e2                  => term_cons (symbolic_eval_exp  e1 δ) (symbolic_eval_exp  e2 δ)
    | @exp_nil _ σ0                   => term_nil _
    | @exp_tuple _ σs es              =>
      let symbolic_eval_exps := fix symbolic_eval_exps {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Env (Term Σ) σs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (symbolic_eval_exps es) σ (symbolic_eval_exp e δ)
                      end
      in @term_tuple _ σs (symbolic_eval_exps es)
    | @exp_projtup _ σs e0 n σ0 p     => @term_projtup _ σs (symbolic_eval_exp e0 δ) n σ0 p
    | @exp_union _ T K e0             => @term_union _ T K (symbolic_eval_exp e0 δ)
    | exp_record R es                 =>
      let symbolic_eval_exps := fix symbolic_eval_exps {rfs : Ctx (𝑹𝑭 * Ty)} (es : Env' (Exp Γ) rfs) : Env' (Term Σ) rfs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (symbolic_eval_exps es) σ (symbolic_eval_exp e δ)
                      end
      in term_record R (symbolic_eval_exps es)
    | @exp_projrec _ R e0 rf σ0 rfInR => @term_projrec _ R (symbolic_eval_exp e0 δ) rf σ0 rfInR
    | @exp_builtin _ σ0 τ f e0        => @term_builtin _ σ0 τ f (symbolic_eval_exp e0 δ)
    end.

  Inductive Formula (Σ : Ctx (𝑺 * Ty)) : Type :=
  | formula_bool (t : Term Σ ty_bool)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).

  Inductive Assertion (Σ : Ctx (𝑺 * Ty)) : Type :=
  | asn_bool (b : Term Σ ty_bool)
  | asn_pred (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | asn_if   (b : Term Σ ty_bool) (a1 a2 : Assertion Σ)
  | asn_sep  (a1 a2 : Assertion Σ).

  Inductive SepContract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
  | sep_contract Σ (δ : SymbolicLocalStore Σ Δ) (req : Assertion Σ) (ens : Assertion Σ).

  Definition SepContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), SepContract Δ τ.
  Parameter Inline CEnv : SepContractEnv.

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    Ctx (Formula Σ).
  Bind Scope ctx_scope with PathCondition.
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    Ctx { p : 𝑷 & Env (Term Σ) (𝑷_Ty p) }.
  Bind Scope ctx_scope with SymbolicHeap.

  Section SymbolicState.

    Record SymbolicState (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type :=
      MkSymbolicState
        { symbolicstate_pathcondition : PathCondition Σ;
          symbolicstate_localstore    : SymbolicLocalStore Σ Γ;
          symbolicstate_heap          : SymbolicHeap Σ
        }.

    Definition symbolic_assume_formula {Σ Γ} (fml : Formula Σ) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (Φ ▻ fml) ŝ ĥ.
    Definition symbolic_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (Φ ▻ formula_bool (symbolic_eval_exp e ŝ)) ŝ ĥ.
    Definition symbolic_push_local {Σ Γ x} σ (v : Term Σ σ) : SymbolicState Σ Γ -> SymbolicState Σ (Γ ▻ (x , σ)) :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_snoc ŝ (x , σ) v) ĥ.
    Definition symbolic_pop_local {Σ Γ x σ} : SymbolicState Σ (Γ ▻ (x , σ)) -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_tail ŝ) ĥ.

  End SymbolicState.

  Section SymbolicExecution.

    Import OutcomeNotations.

    Inductive sexec {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} (st : SymbolicState Σ Γ) : forall (σ : Ty), Stm Γ σ -> Outcome (Term Σ σ * SymbolicState Σ Γ) -> Prop :=
    | sexc_lit {σ : Ty} (v : Lit σ)   : sexec st (stm_lit σ v) (single (term_lit _ σ v, st))
    | sexc_exp {τ : Ty} (e : Exp Γ τ) : sexec st (stm_exp e)   (single (symbolic_eval_exp e (symbolicstate_localstore st), st))
    | sexc_if  {τ : Ty} (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) (o1 o2 : Outcome (Term Σ τ * SymbolicState Σ Γ)) :
        sexec (symbolic_assume_exp e           st) s1               o1 ->
        sexec (symbolic_assume_exp (exp_not e) st) s2               o2 ->
        sexec st                                   (stm_if e s1 s2) (o1 ⊗ o2)%out
    | sexc_seq {τ σ : Ty}
        (s1 : Stm Γ τ) (o1 : Outcome (Term Σ τ * SymbolicState Σ Γ))
        (s2 : Stm Γ σ) (o2 : SymbolicState Σ Γ -> Outcome (Term Σ σ * SymbolicState Σ Γ)) :
        sexec st s1 o1 ->
        (forall (* t1 *) st', (* outcome_in (t1 , st') o1 ->  *) sexec st' s2 (o2 st')) ->
        (* outcome_satisfy (fun '(t1 , st') => sexec s2 st' (o2 st')) o1 -> *)
        sexec st (stm_seq s1 s2) (o1 >>= fun '(_ , st') => o2 st')
    | sexc_let {x : 𝑿} {τ σ : Ty}
        (s : Stm Γ τ)             (o1 : Outcome _)
        (k : Stm (Γ ▻ (x , τ)) σ) (o2 : SymbolicState Σ (Γ ▻ _) -> Outcome (Term Σ σ * SymbolicState Σ (Γ ▻ _))) :
        sexec st s o1 ->
        (forall (* t1 *) st', (* outcome_in (t1 , st') o1 ->  *) @sexec _ (Γ ▻ _) st' _ k (o2 st')) ->
        sexec st (stm_let x τ s k)
              (o1 >>= fun '(t1 , st1) =>
               o2 (symbolic_push_local t1 st1) >>= fun '(t2 , st2) =>
                                                     single (t2 , symbolic_pop_local st2))%out
    | sexc_call {Δ σ} (f : 𝑭 Δ σ) (es : Env' (Exp Γ) Δ) {Σ' δ req ens} :
        CEnv f = @sep_contract _ _ Σ' δ req ens ->
        sexec st (stm_call f es) (outcome_fail).

  End SymbolicExecution.

  Section Mutator.

    Import OutcomeNotations.
    Definition Mutator (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Σ Γ1 -> Outcome (A * SymbolicState Σ Γ2).
    Bind Scope mutator_scope with Mutator.

    Definition mutator_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Set} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨂ i : I => ms i s)%out.
    Definition mutator_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Set} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨁ i : I => ms i s)%out.
    Definition mutator_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_demonic (fun b : bool => if b then m1 else m2).
    Definition mutator_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_angelic (fun b : bool => if b then m1 else m2).

    Definition mutator_pure {Σ Γ A} (a : A) : Mutator Σ Γ Γ A :=
      fun s => single (a , s).
    Definition mutator_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      fun s1 => outcome_bind (ma s1) (fun '(a , s2) => f a s2).
    Definition mutator_bind_right {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      mutator_bind ma (fun _ => mb).
    Definition mutator_bind_left {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 A :=
      mutator_bind ma (fun a => mutator_bind mb (fun _ => mutator_pure a)).

    Definition mutator_get {Σ Γ} : Mutator Σ Γ Γ (SymbolicState Σ Γ) :=
      fun s => single (s , s).
    Definition mutator_put {Σ Γ Γ'} (s : SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun _ => single (tt , s).
    Definition mutator_modify {Σ Γ Γ'} (f : SymbolicState Σ Γ -> SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_bind mutator_get (fun δ => mutator_put (f δ)).
    Definition mutator_get_local {Σ Γ} : Mutator Σ Γ Γ (SymbolicLocalStore Σ Γ) :=
      fun s => single (symbolicstate_localstore s , s).
    Definition mutator_put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun '(MkSymbolicState Φ _ ĥ) => single (tt , MkSymbolicState Φ δ' ĥ).
    Definition mutator_modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_bind mutator_get_local (fun δ => mutator_put_local (f δ)).
    Definition mutator_eval_exp {Σ Γ σ} (e : Exp Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      mutator_bind mutator_get_local (fun δ => mutator_pure (symbolic_eval_exp e δ)).

    Definition mutator_pop_local {Σ Γ x σ} : Mutator Σ (Γ ▻ (x , σ)) Γ unit :=
      mutator_modify_local (fun δ => env_tail δ).
    Definition mutator_pops_local {Σ Γ} Δ : Mutator Σ (Γ ▻▻ Δ) Γ unit :=
      mutator_modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition mutator_push_local {Σ Γ x} σ (v : Term Σ σ) : Mutator Σ Γ (Γ ▻ (x , σ)) unit :=
      mutator_modify_local (fun δ => env_snoc δ (x , σ) v).
    (* Definition pushs {Σ Γ Δ} (δΔ : @Env' X T D Δ) : DST G (@Env' X T D) Γ (ctx_cat Γ Δ) unit := *)
    (*   mutator_modify_local (fun δΓ => env_cat δΓ δΔ). *)

    Definition mutator_assume_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify (symbolic_assume_formula fml).
    Definition mutator_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_bind (mutator_eval_exp e) (fun t => mutator_assume_formula (formula_bool t)).

  End Mutator.

  Module MutatorNotations.

    Notation "'⨂' i : I => F" := (mutator_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : mutator_scope.
    Notation "'⨁' i : I => F" := (mutator_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : mutator_scope.

    Infix "⊗" := mutator_demonic_binary (at level 40, left associativity) : mutator_scope.
    Infix "⊕" := mutator_angelic_binary (at level 50, left associativity) : mutator_scope.

    Notation "ma >>= f" := (mutator_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (mutator_bind m1 (fun _ => m2)) : mutator_scope.
    Notation "ma *> mb" := (mutator_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (mutator_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.

End Symbolic.
