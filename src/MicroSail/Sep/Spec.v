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

Delimit Scope out_scope with out.
Delimit Scope mut_scope with mut.

Section Outcomes.

  Inductive Outcome (A: Type) : Type :=
  | single (a: A)
  | demonic {I : Set} (os: I -> Outcome A)
  | angelic {I : Set} (os: I -> Outcome A).

  Fixpoint map_outcome {A B : Type} (f : A -> B) (o : Outcome A) : Outcome B :=
    match o with
    | single a => single (f a)
    | demonic os => demonic (fun i => map_outcome f (os i))
    | angelic os => angelic (fun i => map_outcome f (os i))
    end.

  Fixpoint bind_outcome {A B : Type} (o : Outcome A) (f : A -> Outcome B) : Outcome B :=
    match o with
    | single a => f a
    | demonic os => demonic (fun i => bind_outcome (os i) f)
    | angelic os => angelic (fun i => bind_outcome (os i) f)
    end.

  Definition outcome_demonic_binary {A : Type} (o1 o2 : Outcome A) : Outcome A :=
    demonic (fun b : bool => if b then o1 else o2).
  Definition outcome_angelic_binary {A : Type} (o1 o2 : Outcome A) : Outcome A :=
    angelic (fun b : bool => if b then o1 else o2).

End Outcomes.

Bind Scope out_scope with Outcome.

Notation "'⨂' i : I => F" := (demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : out_scope.
Notation "'⨁' i : I => F" := (angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : out_scope.

Infix "⊗" := outcome_demonic_binary (at level 40, left associativity) : out_scope.
Infix "⊕" := outcome_angelic_binary (at level 50, left associativity) : out_scope.

Module Symbolic
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Parameter Inline 𝑺 : Set. (* input: \MIS *)

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

  Definition SymbolicLocalStore (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type := Env' (Term Σ) Γ.
  Bind Scope env_scope with SymbolicLocalStore.
  Definition SymbolicRegStore (Σ : Ctx (𝑺 * Ty))  : Type := forall σ, 𝑹𝑬𝑮 σ -> Term Σ σ.

  Fixpoint seval {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : SymbolicLocalStore Σ Γ) : Term Σ σ :=
    match e in (Exp _ t) return (Term Σ t) with
    | exp_var ς                       => (δ ! ς)%lit
    | exp_lit _ σ0 l                  => term_lit _ σ0 l
    | exp_plus e1 e2                  => term_plus (seval e1 δ) (seval e2 δ)
    | exp_times e1 e2                 => term_times (seval e1 δ) (seval e2 δ)
    | exp_minus e1 e2                 => term_minus (seval e1 δ) (seval e2 δ)
    | exp_neg e0                      => term_neg (seval e0 δ)
    | exp_eq e1 e2                    => term_eq (seval e1 δ) (seval e2 δ)
    | exp_le e1 e2                    => term_le (seval e1 δ) (seval e2 δ)
    | exp_lt e1 e2                    => term_lt (seval e1 δ) (seval e2 δ)
    | exp_gt e1 e2                    => term_gt (seval e1 δ) (seval e2 δ)
    | exp_and e1 e2                   => term_and (seval e1 δ) (seval e2 δ)
    | exp_or e1 e2                    => term_or (seval e1 δ) (seval e2 δ)
    | exp_not e0                      => term_not (seval e0 δ)
    | exp_pair e1 e2                  => term_pair (seval e1 δ) (seval e2 δ)
    | @exp_inl _ σ1 σ2 e0             => @term_inl _ σ1 σ2 (seval e0 δ)
    | @exp_inr _ σ1 σ2 e0             => @term_inr _ σ1 σ2 (seval e0 δ)
    | @exp_list _ σ0 es               => term_list (List.map (fun e : Exp Γ σ0 => seval e δ) es)
    | exp_cons e1 e2                  => term_cons (seval e1 δ) (seval e2 δ)
    | @exp_nil _ σ0                   => term_nil _
    | @exp_tuple _ σs es              =>
      let sevals := fix sevals {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Env (Term Σ) σs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (sevals es) σ (seval e δ)
                      end
      in @term_tuple _ σs (sevals es)
    | @exp_projtup _ σs e0 n σ0 p     => @term_projtup _ σs (seval e0 δ) n σ0 p
    | @exp_union _ T K e0             => @term_union _ T K (seval e0 δ)
    | exp_record R es                 =>
      let sevals := fix sevals {rfs : Ctx (𝑹𝑭 * Ty)} (es : Env' (Exp Γ) rfs) : Env' (Term Σ) rfs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (sevals es) σ (seval e δ)
                      end
      in term_record R (sevals es)
    | @exp_projrec _ R e0 rf σ0 rfInR => @term_projrec _ R (seval e0 δ) rf σ0 rfInR
    | @exp_builtin _ σ0 τ f e0        => @term_builtin _ σ0 τ f (seval e0 δ)
    end.

  Inductive Formula (Σ : Ctx (𝑺 * Ty)) : Type :=
  | formula_bool (t : Term Σ ty_bool)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    Ctx (Formula Σ).
  Bind Scope ctx_scope with PathCondition.
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    Ctx { p : 𝑷 & Env (Term Σ) (𝑷_Ty p) }.
  Bind Scope ctx_scope with SymbolicHeap.

  Record SymbolicState (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type :=
    MkSymbolicState
      { symbolicstate_pathcondition : PathCondition Σ;
        symbolicstate_localstore    : SymbolicLocalStore Σ Γ;
        symbolicstate_heap          : SymbolicHeap Σ
      }.

  Section MutatorSem.

    Definition Mutator (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Σ Γ1 -> Outcome (A * SymbolicState Σ Γ2).
    Bind Scope mut_scope with Mutator.

    Definition mutator_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Set} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨂ i : I => ms i s)%out.
    Definition mutator_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Set} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨁ i : I => ms i s)%out.
    Definition mutator_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_demonic (fun b : bool => if b then m1 else m2).
    Definition mutator_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_angelic (fun b : bool => if b then m1 else m2).

    Notation "'⨂' i : I => F" := (mutator_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : mut_scope.
    Notation "'⨁' i : I => F" := (mutator_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : mut_scope.

    Infix "⊗" := mutator_demonic_binary (at level 40, left associativity) : mut_scope.
    Infix "⊕" := mutator_angelic_binary (at level 50, left associativity) : mut_scope.

    Definition pure {Σ Γ A} (a : A) : Mutator Σ Γ Γ A :=
      fun s => single (a , s).
    Definition bind {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      fun s1 => bind_outcome (ma s1) (fun '(a , s2) => f a s2).
    Definition bindright {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      bind ma (fun _ => mb).
    Definition bindleft {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 A :=
      bind ma (fun a => bind mb (fun _ => pure a)).

    Definition get_local {Σ Γ} : Mutator Σ Γ Γ (SymbolicLocalStore Σ Γ) :=
      fun s => single (symbolicstate_localstore s , s).
    Definition put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun '(MkSymbolicState Φ _ ĥ) => single (tt , MkSymbolicState Φ δ' ĥ).
    Definition modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      bind get_local (fun δ => put_local (f δ)).
    Definition meval {Σ Γ σ} (e : Exp Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      bind get_local (fun δ => pure (seval e δ)).

    Definition pop {Σ Γ x σ} : Mutator Σ (Γ ▻ (x , σ)) Γ unit :=
      modify_local (fun δ => env_tail δ).
    Definition pops {Σ Γ} Δ : Mutator Σ (Γ ▻▻ Δ) Γ unit :=
      modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition push {Σ Γ x} σ (v : Term Σ σ) : Mutator Σ Γ (Γ ▻ (x , σ)) unit :=
      modify_local (fun δ => env_snoc δ (x , σ) v).
    (* Definition pushs {Σ Γ Δ} (δΔ : @Env' X T D Δ) : DST G (@Env' X T D) Γ (ctx_cat Γ Δ) unit := *)
    (*   modify_local (fun δΓ => env_cat δΓ δΔ). *)

    Definition sassume_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      fun '(MkSymbolicState Φ ŝ ĥ) => single (tt , MkSymbolicState (Φ ▻ fml) ŝ ĥ).
    Definition sassume_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      bind (meval e) (fun t => sassume_formula (formula_bool t)).

    Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : mut_scope.
    Notation "m1 ;; m2" := (bind m1 (fun _ => m2)) : mut_scope.
    Notation "ma *> mb" := (bindright ma mb) (at level 50, left associativity) : mut_scope.
    Notation "ma <* mb" := (bindleft ma mb) (at level 50, left associativity) : mut_scope.

    Section SymbolicExecution.

      Context {Σ : Ctx (𝑺 * Ty)}.

      Inductive sexec {Γ : Ctx (𝑿 * Ty)} : forall (σ : Ty), Stm Γ σ -> Mutator Σ Γ Γ (Term Σ σ) -> Prop :=
      | sexc_lit {σ : Ty} (v : Lit σ)   : sexec (stm_lit σ v) (pure (term_lit _ σ v))
      | sexc_exp {τ : Ty} (e : Exp Γ τ) : sexec (stm_exp e)   (meval e)
      | sexc_if  {τ : Ty} (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) (m1 m2 : Mutator Σ Γ Γ (Term Σ τ)) :
          sexec s1 m1 ->
          sexec s2 m2 ->
          sexec (stm_if e s1 s2) ((sassume_exp e ;; m1) ⊗ (sassume_exp (exp_not e) ;; m2))%mut
      | sexc_seq {τ σ : Ty} (s1 : Stm Γ τ) (s2 : Stm Γ σ) m1 m2 :
          sexec s1 m1 ->
          sexec s2 m2 ->
          sexec (stm_seq s1 s2) (m1 ;; m2)
      | sexc_let (x : 𝑿) (τ : Ty) (s : Stm Γ τ) ms {σ : Ty} (k : Stm (Γ ▻ (x , τ)) σ) mk :
          sexec s ms ->
          @sexec _ _ k mk ->
          sexec (stm_let x τ s k) (ms >>= fun t => push t *> mk <* pop)%mut.

    End SymbolicExecution.

  End MutatorSem.

End Symbolic.
