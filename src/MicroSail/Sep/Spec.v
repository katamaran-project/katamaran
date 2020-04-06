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
     Bool.Bool
     Lists.List
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     Arith.PeanoNat
     ZArith.ZArith.

From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Outcome
     Syntax.

From stdpp Require Import base option.

Import CtxNotations.
Import EnvNotations.
Import OutcomeNotations.
Import ListNotations.

Local Open Scope ctx_scope.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.

Module Type AssertionKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).
  Module PM := Programs typekit termkit progkit.
  Export PM.

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Parameter Inline 𝑷_eq_dec : forall (p : 𝑷) (q : 𝑷), {p = q}+{~ p = q}.

End AssertionKit.

Module Assertions
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit)
       (assertkit : AssertionKit typekit termkit progkit).
  Export assertkit.

  Inductive Chunk (Σ : Ctx (𝑺 * Ty)) : Type :=
  | chunk_pred   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).
  Arguments chunk_pred [_] _ _.

  Inductive Assertion (Σ : Ctx (𝑺 * Ty)) : Type :=
  | asn_bool (b : Term Σ ty_bool)
  | asn_prop (P : abstract_named Lit Σ Prop)
  | asn_chunk (c : Chunk Σ)
  | asn_if   (b : Term Σ ty_bool) (a1 a2 : Assertion Σ)
  | asn_match_enum {E : 𝑬} (k : Term Σ (ty_enum E)) (alts : forall (K : 𝑬𝑲 E), Assertion Σ)
  | asn_sep  (a1 a2 : Assertion Σ)
  | asn_exist (ς : 𝑺) (τ : Ty) (a : Assertion (Σ ▻ (ς , τ))).

  Definition asn_true {Σ} : Assertion Σ :=
    asn_bool (term_lit ty_bool true).
  Definition asn_false {Σ} : Assertion Σ :=
    asn_bool (term_lit ty_bool false).

  Arguments asn_prop {_} _.
  Arguments asn_match_enum [_] _ _ _.
  Arguments asn_exist [_] _ _ _.

  Definition sub_chunk {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (c : Chunk Σ1) : Chunk Σ2 :=
    match c with
    | chunk_pred p ts => chunk_pred p (env_map (fun _ => sub_term ζ) ts)
    | chunk_ptsreg r t => chunk_ptsreg r (sub_term ζ t)
    end.

  (* Fixpoint sub_assertion {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (a : Assertion Σ1) {struct a} : Assertion Σ2 := *)
  (*   match a with *)
  (*   | asn_bool b => asn_bool (sub_term ζ b) *)
  (*   | asn_chunk c => asn_chunk (sub_chunk ζ c) *)
  (*   | asn_if b a1 a2 => asn_if (sub_term ζ b) (sub_assertion ζ a1) (sub_assertion ζ a2) *)
  (*   | asn_match_enum k alts => *)
  (*     asn_match_enum (sub_term ζ k) (fun z => sub_assertion ζ (alts z)) *)
  (*   | asn_sep a1 a2 => asn_sep (sub_assertion ζ a1) (sub_assertion ζ a2) *)
  (*   | asn_exist ς τ a => asn_exist ς τ (sub_assertion (sub_up1 ζ) a) *)
  (*   end. *)

  Definition SymbolicLocalStore (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type := NamedEnv (Term Σ) Γ.
  Bind Scope env_scope with SymbolicLocalStore.
  (* Definition SymbolicRegStore (Σ : Ctx (𝑺 * Ty))  : Type := forall σ, 𝑹𝑬𝑮 σ -> Term Σ σ. *)

  Fixpoint symbolic_eval_exp {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : SymbolicLocalStore Σ Γ) : Term Σ σ :=
    match e in (Exp _ t) return (Term Σ t) with
    | exp_var ς                       => (δ ‼ ς)%lit
    | exp_lit _ σ l                   => term_lit σ l
    | exp_binop op e1 e2              => term_binop op (symbolic_eval_exp e1 δ) (symbolic_eval_exp e2 δ)
    | exp_neg e0                      => term_neg (symbolic_eval_exp e0 δ)
    | exp_not e0                      => term_not (symbolic_eval_exp e0 δ)
    | @exp_inl _ σ1 σ2 e0             => @term_inl _ σ1 σ2 (symbolic_eval_exp e0 δ)
    | @exp_inr _ σ1 σ2 e0             => @term_inr _ σ1 σ2 (symbolic_eval_exp e0 δ)
    | @exp_list _ σ0 es               => term_list (List.map (fun e => symbolic_eval_exp e δ) es)
    | @exp_tuple _ σs es              => @term_tuple _ σs (env_map (fun _ e => symbolic_eval_exp e δ) es)
    | @exp_projtup _ σs e0 n σ0 p     => @term_projtup _ σs (symbolic_eval_exp e0 δ) n σ0 p
    | @exp_union _ T K e0             => @term_union _ T K (symbolic_eval_exp e0 δ)
    | exp_record R es                 => term_record R (env_map (fun _ e => symbolic_eval_exp e δ) es)
    | @exp_projrec _ R e0 rf σ0 rfInR => @term_projrec _ R (symbolic_eval_exp e0 δ) rf σ0 rfInR
    end.

  Inductive SepContract (Δ : Ctx (𝑿 * Ty)) : Ty -> Type :=
  | sep_contract_unit   {Σ}
    (δ : SymbolicLocalStore Σ Δ)
    (req : Assertion Σ) (ens : Assertion Σ) : SepContract Δ ty_unit
  | sep_contract_result_pure {Σ τ}
    (δ : SymbolicLocalStore Σ Δ)
    (result : Term Σ τ)
    (req : Assertion Σ) (ens : Assertion Σ) : SepContract Δ τ
  | sep_contract_result {Σ τ}
    (δ : SymbolicLocalStore Σ Δ) (result : 𝑺)
    (req : Assertion Σ) (ens : Assertion (Σ ▻ (result , τ))) : SepContract Δ τ
  | sep_contract_none {τ} : SepContract Δ τ.

  Definition SepContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), SepContract Δ τ.

End Assertions.

Module Type SymbolicContractKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit).

  Module ASS := Assertions typekit termkit progkit assertkit.
  Export ASS.

  Parameter Inline CEnv : SepContractEnv.

End SymbolicContractKit.

Module SymbolicContracts
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit)
       (assertkit : AssertionKit typekit termkit progkit)
       (symcontractkit : SymbolicContractKit typekit termkit progkit assertkit).

  Export symcontractkit.

  Inductive Formula (Σ : Ctx (𝑺 * Ty)) : Type :=
  | formula_bool (t : Term Σ ty_bool)
  | formula_prop {Σ'} (ζ : Sub Σ' Σ) (P : abstract_named Lit Σ' Prop)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).

  Equations(noeqns) formula_eqs {Δ : Ctx (𝑿 * Ty)} {Σ : Ctx (𝑺 * Ty)}
    (δ δ' : NamedEnv (Term Σ) Δ) : list (Formula Σ) :=
    formula_eqs env_nil          env_nil            := nil;
    formula_eqs (env_snoc δ _ t) (env_snoc δ' _ t') :=
      formula_eq t t' :: formula_eqs δ δ'.

  Definition interpret_formula {Σ} (δ : NamedEnv Lit Σ) (fml : Formula Σ) : Prop :=
    match fml with
    | formula_bool t    => is_true (eval_term t δ)
    | formula_prop ζ P  => uncurry_named P (env_map (fun _ t => eval_term t δ) ζ)
    | formula_eq t1 t2  => eval_term t1 δ =  eval_term t2 δ
    | formula_neq t1 t2 => eval_term t1 δ <> eval_term t2 δ
    end.

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Formula Σ).
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Chunk Σ).

  Inductive Obligation : Type :=
  | obligation {Σ} (pc : PathCondition Σ) (fml : Formula Σ).

  Definition valid_obligation : Obligation -> Prop :=
    fun '(obligation pc fml) =>
      ForallNamed (fun δ => List.Forall (interpret_formula δ) pc -> interpret_formula δ fml).
  Definition valid_obligations (os : list Obligation) : Prop :=
    List.Forall valid_obligation os.
  Hint Unfold valid_obligation : core.
  Hint Unfold valid_obligations : core.


  Definition sub_formula {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (fml : Formula Σ1) : Formula Σ2 :=
    match fml with
    | formula_bool t    => formula_bool (sub_term ζ t)
    | formula_prop ζ' P => formula_prop (sub_comp ζ' ζ) P
    | formula_eq t1 t2  => formula_eq (sub_term ζ t1) (sub_term ζ t2)
    | formula_neq t1 t2 => formula_neq (sub_term ζ t1) (sub_term ζ t2)
    end.

  Definition sub_pathcondition {Σ1 Σ2} (ζ : Sub Σ1 Σ2) : PathCondition Σ1 -> PathCondition Σ2 :=
    map (sub_formula ζ).
  Definition sub_localstore {Σ1 Σ2 Γ} (ζ : Sub Σ1 Σ2) : SymbolicLocalStore Σ1 Γ -> SymbolicLocalStore Σ2 Γ :=
    env_map (fun _ => sub_term ζ).
  Definition sub_heap {Σ1 Σ2} (ζ : Sub Σ1 Σ2) : SymbolicHeap Σ1 -> SymbolicHeap Σ2 :=
    map (sub_chunk ζ).

  Section SymbolicState.

    Record SymbolicState (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type :=
      MkSymbolicState
        { symbolicstate_pathcondition : PathCondition Σ;
          symbolicstate_localstore    : SymbolicLocalStore Σ Γ;
          symbolicstate_heap          : SymbolicHeap Σ
        }.
    Global Arguments symbolicstate_pathcondition {_ _} _.
    Global Arguments symbolicstate_localstore {_ _} _.
    Global Arguments symbolicstate_heap {_ _} _.

    Definition symbolicstate_initial {Γ Σ} (δ : SymbolicLocalStore Γ Σ) : SymbolicState Γ Σ :=
      MkSymbolicState nil δ nil.

    Definition symbolic_assume_formula {Σ Γ} (fml : Formula Σ) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (fml :: Φ) ŝ ĥ.
    Definition symbolic_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (formula_bool (symbolic_eval_exp e ŝ) :: Φ) ŝ ĥ.
    Definition symbolic_push_local {Σ Γ x} σ (v : Term Σ σ) : SymbolicState Σ Γ -> SymbolicState Σ (Γ ▻ (x , σ)) :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_snoc ŝ (x , σ) v) ĥ.
    Definition symbolic_pop_local {Σ Γ x σ} : SymbolicState Σ (Γ ▻ (x , σ)) -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_tail ŝ) ĥ.

    Definition sub_symbolicstate {Σ1 Σ2 Γ} (ζ : Sub Σ1 Σ2) : SymbolicState Σ1 Γ -> SymbolicState Σ2 Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (sub_pathcondition ζ Φ) (sub_localstore ζ ŝ) (sub_heap ζ ĥ).
    Definition wk1_symbolicstate {Σ Γ b} : SymbolicState Σ Γ -> SymbolicState (Σ ▻ b) Γ :=
      sub_symbolicstate sub_wk1.

  End SymbolicState.

  Equations(noeqns) try_solve_formula {Σ} (fml : Formula Σ) : option bool :=
    try_solve_formula (formula_bool (term_lit _ b)) := Some b;
    try_solve_formula (formula_bool _)              := None;
    try_solve_formula (formula_prop _ _)            := None;
    try_solve_formula (formula_eq t1 t2)            := if Term_eqb t1 t2
                                                       then Some true
                                                       else None;
    try_solve_formula (formula_neq t1 t2)           := None.

  Section SolverSoundness.

    Hypothesis Term_eqb_spec :
      forall Σ (σ : Ty) (t1 t2 : Term Σ σ),
        reflect (t1 = t2) (Term_eqb t1 t2).

    Lemma try_solve_formula_spec {Σ} (fml : Formula Σ) (b : bool) :
      try_solve_formula fml = Some b ->
      forall δ, reflect (interpret_formula δ fml) b.
    Proof.
      destruct fml; cbn.
      - dependent destruction t; cbn; inversion 1.
        destruct b; constructor; congruence.
      - discriminate.
      - destruct (Term_eqb_spec t1 t2); cbn; inversion 1.
        constructor; congruence.
      - discriminate.
    Qed.

  End SolverSoundness.

  Definition GhostEnv (Σe Σr : Ctx (𝑺 * Ty)) : Type := Env (fun b => option (Term Σr (snd b))) Σe.

  Definition create_ghost_env (Σe Σr : Ctx (𝑺 * Ty)) : GhostEnv Σe Σr :=
    env_tabulate (fun _ _ => None).

  Let comp {S : Type} (f : S -> option S) (g : S -> option S) : S -> option S :=
    fun s => ssrfun.Option.bind g (f s).
  Infix ">=>" := comp (at level 80, right associativity).

  Section TraverseList.

    Context `{MRet M, MBind M} {A B : Type} (f : A -> M B).

    Fixpoint traverse_list (xs : list A) : M (list B) :=
      match xs with
      | nil       => mret nil
      | cons x xs => b ← f x ; bs ← traverse_list xs ; mret (cons b bs)
      end.

  End TraverseList.

  Section TraverseEnv.

    Context `{MRet M, MBind M} {I : Set} {A B : I -> Type} (f : forall i : I, A i -> M (B i)).

    Fixpoint traverse_env {Γ : Ctx I} (xs : Env A Γ) : M (Env B Γ) :=
      match xs with
      | env_nil => mret (env_nil)
      | env_snoc Ea i a => Eb ← traverse_env Ea ; b ← f a ; mret (env_snoc Eb i b)
      end.

  End TraverseEnv.

  Section WithGhostScope.
    Context {Σe Σr} (δ : GhostEnv Σe Σr).

    Fixpoint eval_term_ghost {σ : Ty} (t : Term Σe σ) {struct t} : option (Term Σr σ) :=
      match t in Term _ σ return option (Term Σr σ) with
      | @term_var _ x _      => (δ ‼ x)%lit
      | term_lit _ l         => Some (term_lit _ l)
      | term_binop op t1 t2  => t1 ← eval_term_ghost t1 ;
                                t2 ← eval_term_ghost t2 ;
                                Some (term_binop op t1 t2)
      | term_neg t           => term_neg <$> eval_term_ghost t
      | term_not t           => term_not <$> eval_term_ghost t
      | term_inl t           => term_inl <$> eval_term_ghost t
      | term_inr t           => term_inr <$> eval_term_ghost t
      | term_list ts         => term_list <$> traverse_list eval_term_ghost ts
      | term_tuple ts        => term_tuple <$> traverse_env (@eval_term_ghost) ts
      | @term_projtup _ _ t n _ p     => (fun t => term_projtup t n (p:=p)) <$> eval_term_ghost t
      | term_union U K t     => term_union U K <$> eval_term_ghost t
      | term_record R ts     => term_record R <$> traverse_env (fun b => @eval_term_ghost (snd b)) ts
      | term_projrec t rf    => (fun t => term_projrec t rf) <$> eval_term_ghost t
      end.

    Section WithMatchTerm.

      Variable match_term : forall {σ}, Term Σe σ -> Term Σr σ -> GhostEnv Σe Σr -> option (GhostEnv Σe Σr).

      Equations(noeqns) match_env'  {σs} (te : Env (Term Σe) σs) (tr : Env (Term Σr) σs) :
        GhostEnv Σe Σr -> option (GhostEnv Σe Σr) :=
        match_env' env_nil env_nil := Some;
        match_env' (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) := match_env' E1 E2 >=> match_term t1 t2.

    End WithMatchTerm.

    (* The match_term function tries to match the term te from the callee
       contract against a term tr from the caller environment. NOTE(!): This
       function tries not to do anything intelligent with constructs that have
       non-trivial equalities (like plus, projections, ..). It is therefore
       necessarily incomplete. Potentially it can later be replaced by something
       that simply assumes the equality and checks if this is still consistent
       with the path condition.
     *)
    Equations(noeqns) match_term {σ} (te : Term Σe σ) (tr : Term Σr σ) :
      GhostEnv Σe Σr -> option (GhostEnv Σe Σr) :=
      match_term (@term_var ς σ ςInΣe) tr :=
        fun L =>
          match (L ‼ ς)%lit with
          (* There's already a binding for ς in the ghost environment. Make sure
             it corresponds to the term tr. *)
          | Some tr' => if Term_eqb tr' tr then Some L else None
          (* There's no binding for ς in the ghost environment. Create a new one by
             inserting tr. *)
          | None     => Some (L ⟪ ς ↦ Some tr ⟫)%env
          end;
      match_term (term_lit ?(σ) l1) (term_lit σ l2) :=
        if Lit_eqb σ l1 l2 then Some else fun _ => None;
      match_term (term_inl t1) (term_inl t2) := match_term t1 t2;
      match_term (term_inl t1) (term_lit (inl l2)) := match_term t1 (term_lit _ l2);
      match_term (term_tuple ts1) (term_tuple ts2) := match_env' (@match_term) ts1 ts2;
      (* Obviously more matchings can be added here. *)
      match_term _ _ := fun _ => None.

    Definition match_env := @match_env' (@match_term).

    Equations(noeqns) match_chunk (ce : Chunk Σe) (cr : Chunk Σr) :
      GhostEnv Σe Σr -> option (GhostEnv Σe Σr) :=
      match_chunk (chunk_pred p1 ts1) (chunk_pred p2 ts2)
      with 𝑷_eq_dec p1 p2 => {
        match_chunk (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) := match_env ts1 ts2;
        match_chunk (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _) := fun _ => None
      };
      match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with 𝑹𝑬𝑮_eq_dec r1 r2 => {
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left (@teq_refl eq_refl eq_refl)) := match_term t1 t2;
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk _ _  := fun _ => None.

    Fixpoint extract_chunk (ce : Chunk Σe) (h : SymbolicHeap Σr) (L : GhostEnv Σe Σr) :
      list (GhostEnv Σe Σr * SymbolicHeap Σr) :=
      match h with
      | nil      => nil
      | cr :: h' => let rec := List.map
                                 (prod_curry (fun L' h'' => (L' , cons cr h'')))
                                 (extract_chunk ce h' L) in
                    match match_chunk ce cr L with
                    | Some L' => cons (L' , h') rec
                    | None    => rec
                    end
      end.

  End WithGhostScope.

  Definition ghost_env_to_option_sub {Σe Σr} (δ : GhostEnv Σe Σr) : option (Sub Σe Σr) :=
    traverse_env (fun b mt => mt) δ.

  Lemma eval_term_ghost_refines_sub_term {Σe Σr} (δ : GhostEnv Σe Σr) (ζ : Sub Σe Σr) :
    ghost_env_to_option_sub δ = Some ζ ->
    forall σ (t : Term _ σ), eval_term_ghost δ t = Some (sub_term ζ t).
  Proof.
    intros hyp.
    induction t; cbn in *.
    - admit.
    - reflexivity.
    - rewrite IHt1, IHt2; reflexivity.
    - rewrite IHt; reflexivity.
    - rewrite IHt; reflexivity.
    - rewrite IHt; reflexivity.
    - rewrite IHt; reflexivity.
    - apply fmap_Some_2.
      induction es as [|t ts]; cbn in *.
      + reflexivity.
      + destruct X as [Xt Xts].
        rewrite Xt, (IHts Xts); reflexivity.
    - admit.
    - rewrite IHt; reflexivity.
    - rewrite IHt; reflexivity.
    - admit.
    - rewrite IHt; reflexivity.
  Admitted.

  Section Mutator.

    Definition Mutator (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Σ Γ1 -> Outcome (A * SymbolicState Σ Γ2 * list Obligation).
    Bind Scope mutator_scope with Mutator.

    Definition mutator_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨂ i : I => ms i s)%out.
    Definition mutator_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨁ i : I => ms i s)%out.
    (* There are two kinds of failures of the symbolic execution. mutator_fail
       is an unconditional fail: the current branch of choices is deemed invalid
       and the executor should backtrack. mutator_contradiction is more liberal.
       Instead of completely failing, it allows the current choices but requires
       the path condition to be inconsistent. Essentially, this is should be a
       mutator_block, but the execution engine could not derive the
       inconsistency automatically. If in doubt, be more conservative and use
       mutator_fail, because it allows for pruning of branches. Change to
       mutator_contradiction if you're convinced that you require it for a
       completeness issue. *)
    Definition mutator_fail {Σ Γ1 Γ2} {A : Type} (msg : string) : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_fail msg.
    Definition mutator_contradiction {Σ Γ1 Γ2} {A : Type} (msg : string) : Mutator Σ Γ1 Γ2 A :=
      fun s =>
        (⨂ δ : NamedEnv Lit Σ =>
         ⨂ _ : List.Forall (interpret_formula δ) (symbolicstate_pathcondition s) =>
         outcome_fail msg)%out.
    Definition mutator_block {Σ Γ1 Γ2} {A : Type} : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_block.

    Definition mutator_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_demonic (fun b : bool => if b then m1 else m2).
    Definition mutator_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_angelic_binary (m1 s) (m2 s).

    Definition mutator_pure {Σ Γ A} (a : A) : Mutator Σ Γ Γ A :=
      fun s => outcome_pure (a, s, nil).
    Definition mutator_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      fun s0 => outcome_bind (ma s0) (fun '(a , s1 , w1) => outcome_bind (f a s1) (fun '(b , s2 , w2) => outcome_pure (b , s2 , w1 ++ w2))).
    Definition mutator_bind_right {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      mutator_bind ma (fun _ => mb).
    Definition mutator_bind_left {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 A :=
      mutator_bind ma (fun a => mutator_bind mb (fun _ => mutator_pure a)).
    Definition mutator_map {Σ Γ1 Γ2 A B} (f : A -> B) (ma : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 B :=
      mutator_bind ma (fun a => mutator_pure (f a)).

    Section AngelicList.
      Context {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {A : Type}.
      Variable (msg : string).

      Fixpoint mutator_angelic_list (xs : list A)  {struct xs} : Mutator Σ Γ Γ A :=
        match xs with
        | []      => mutator_contradiction msg
        | x :: [] => mutator_pure x
        | x :: xs => mutator_angelic_binary (mutator_pure x) (mutator_angelic_list xs)
        end.

    End AngelicList.

    Global Arguments mutator_bind {_ _ _ _ _ _} _ _ /.
    Global Arguments mutator_bind_right {_ _ _ _ _ _} _ _ /.

  End Mutator.
  Bind Scope mutator_scope with Mutator.

  Module MutatorNotations.

    Notation "'⨂' x .. y => F" :=
      (mutator_demonic (fun x => .. (mutator_demonic (fun y => F)) .. )) : mutator_scope.

    Notation "'⨁' x .. y => F" :=
      (mutator_angelic (fun x => .. (mutator_angelic (fun y => F)) .. )) : mutator_scope.

    Infix "⊗" := mutator_demonic_binary (at level 40, left associativity) : mutator_scope.
    Infix "⊕" := mutator_angelic_binary (at level 50, left associativity) : mutator_scope.

    Notation "x <- ma ;; mb" := (mutator_bind ma (fun x => mb)) (at level 100, right associativity, ma at next level) : mutator_scope.
    Notation "ma >>= f" := (mutator_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (mutator_bind m1 (fun _ => m2)) : mutator_scope.
    Notation "ma *> mb" := (mutator_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (mutator_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.
  Import MutatorNotations.

  Section MutatorOperations.

    Local Open Scope mutator_scope.

    Definition mutator_get {Σ Γ} : Mutator Σ Γ Γ (SymbolicState Σ Γ) :=
      fun s => outcome_pure (s , s , nil).
    Definition mutator_put {Σ Γ Γ'} (s : SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun _ => outcome_pure (tt , s, nil).
    Definition mutator_modify {Σ Γ Γ'} (f : SymbolicState Σ Γ -> SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_get >>= fun δ => mutator_put (f δ).
    Definition mutator_get_local {Σ Γ} : Mutator Σ Γ Γ (SymbolicLocalStore Σ Γ) :=
      fun s => outcome_pure (symbolicstate_localstore s , s , nil).
    Definition mutator_put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun '(MkSymbolicState Φ _ ĥ) => outcome_pure (tt , MkSymbolicState Φ δ' ĥ , nil).
    Definition mutator_modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_get_local >>= fun δ => mutator_put_local (f δ).
    Definition mutator_pop_local {Σ Γ x σ} : Mutator Σ (Γ ▻ (x , σ)) Γ unit :=
      mutator_modify_local (fun δ => env_tail δ).
    Definition mutator_pops_local {Σ Γ} Δ : Mutator Σ (Γ ▻▻ Δ) Γ unit :=
      mutator_modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition mutator_push_local {Σ Γ x} σ (v : Term Σ σ) : Mutator Σ Γ (Γ ▻ (x , σ)) unit :=
      mutator_modify_local (fun δ => env_snoc δ (x , σ) v).
    Definition mutator_pushs_local {Σ Γ Δ} (δΔ : NamedEnv (Term Σ) Δ) : Mutator Σ Γ (Γ ▻▻ Δ) unit :=
      mutator_modify_local (fun δΓ => env_cat δΓ δΔ).

    Definition mutator_get_heap {Σ Γ} : Mutator Σ Γ Γ (SymbolicHeap Σ) :=
      mutator_map symbolicstate_heap mutator_get.
    Definition mutator_put_heap {Σ Γ} (h : SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      fun '(MkSymbolicState Φ δ _) => outcome_pure (tt , MkSymbolicState Φ δ h , nil).
    Definition mutator_modify_heap {Σ Γ} (f : SymbolicHeap Σ -> SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify (fun '(MkSymbolicState Φ δ h) => MkSymbolicState Φ δ (f h)).

    Definition mutator_eval_exp {Σ Γ σ} (e : Exp Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      mutator_get_local >>= fun δ => mutator_pure (symbolic_eval_exp e δ).
    Definition mutator_eval_exps {Σ Γ} {σs : Ctx (𝑿 * Ty)} (es : NamedEnv (Exp Γ) σs) : Mutator Σ Γ Γ (NamedEnv (Term Σ) σs) :=
      mutator_get_local >>= fun δ => mutator_pure (env_map (fun _ e => symbolic_eval_exp e δ) es).

    Definition mutator_assume_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      match try_solve_formula fml with
      | Some true  => mutator_pure tt
      | Some false => mutator_block
      | None       => mutator_modify (symbolic_assume_formula fml)
      end.
    (* Definition mutator_assume_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit := *)
    (*   mutator_modify (symbolic_assume_formula fml). *)
    Definition mutator_assume_term {Σ Γ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assume_formula (formula_bool t).
    Definition mutator_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assume_term.

    Definition mutator_assert_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      match try_solve_formula fml with
      | Some true  => mutator_pure tt
      | Some false => mutator_fail "Err [mutator_assert_formula]: unsatisfiable"
      | None       => fun δ => outcome_pure (tt , δ , obligation (symbolicstate_pathcondition δ) fml :: nil)
      end.
    Definition mutator_assert_formulas {Σ Γ} (fmls : list (Formula Σ)) : Mutator Σ Γ Γ unit :=
      fold_right
        (fun fml m => mutator_assert_formula fml ;; m)
        (mutator_pure tt)
        fmls.
    (* Definition mutator_assert_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit := *)
    (*   fun δ => outcome_pure (tt , δ , obligation (symbolicstate_pathcondition δ) fml :: nil). *)

    Definition mutator_assert_term {Σ Γ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assert_formula (formula_bool t).
    Definition mutator_assert_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assert_term.

    Definition mutator_produce_chunk {Σ Γ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify_heap (fun h => c :: h).

    Equations(noeqns) chunk_eqb {Σ} (c1 c2 : Chunk Σ) : bool :=
      chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2)
      with 𝑷_eq_dec p1 p2 => {
        chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) :=
          env_beq (@Term_eqb _) ts1 ts2;
        chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _) := false
      };
      chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with 𝑹𝑬𝑮_eq_dec r1 r2 => {
        chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left (@teq_refl eq_refl eq_refl)) := Term_eqb t1 t2;
        chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := false
      };
      chunk_eqb _ _ := false.

    Fixpoint option_consume_chunk {Σ} (c : Chunk Σ) (h : SymbolicHeap Σ) : option (SymbolicHeap Σ) :=
      match h with
      | nil      => None
      | c' :: h' => if chunk_eqb c c'
                    then Some h'
                    else option_map (cons c') (option_consume_chunk c h')
      end.

    Fixpoint heap_extractions {Σ} (h : SymbolicHeap Σ) : list (Chunk Σ * SymbolicHeap Σ) :=
      match h with
      | []     => []
      | c :: h => (c , h) :: map (fun '(c', h') => (c' , c :: h')) (heap_extractions h)
      end.

    Equations(noeqns) mutator_chunk_eqb {Σ Γ} (c1 c2 : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2)
      with 𝑷_eq_dec p1 p2 => {
        mutator_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) :=
          mutator_assert_formula (formula_eq (term_tuple ts1) (term_tuple ts2));
        mutator_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _) :=
          mutator_fail "Err [mutator_chunk_eqb]: No matching"
      };
      mutator_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with 𝑹𝑬𝑮_eq_dec r1 r2 => {
        mutator_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left (@teq_refl eq_refl eq_refl)) :=
          mutator_assert_formula (formula_eq t1 t2);
        mutator_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _) :=
          mutator_fail "Err [mutator_chunk_eqb]: No matching"
      };
      mutator_chunk_eqb _ _ := mutator_fail "Err [mutator_chunk_eqb]: No matching".

    Definition mutator_consume_chunk {Σ Γ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_get_heap >>= fun h =>
      mutator_angelic_list
        "Err [mutator_consume_chunk]: empty extraction"
        (heap_extractions h) >>= fun '(c' , h') =>
        mutator_chunk_eqb c c' *>
        mutator_put_heap h'.

    Fixpoint mutator_produce {Σ Σ' Γ} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Mutator Σ' Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assume_term (sub_term ζ b)
      | asn_prop P      => mutator_assume_formula (formula_prop ζ P)
      | asn_chunk c     => mutator_produce_chunk (sub_chunk ζ c)
      | asn_if b a1 a2  => (mutator_assume_term (sub_term ζ b)            *> mutator_produce ζ a1) ⊗
                           (mutator_assume_term (sub_term ζ (term_not b)) *> mutator_produce ζ a2)
      | @asn_match_enum _ E k1 alts =>
        ⨂ k2 : 𝑬𝑲 E => mutator_assume_formula
                         (formula_eq (sub_term ζ k1) (term_enum E k2)) ;;
                       mutator_produce ζ (alts k2)
      | asn_sep a1 a2   => mutator_produce ζ a1 *> mutator_produce ζ a2
      | asn_exist ς τ a => mutator_fail
                             "Err [mutator_produce]: case [asn_exist] not implemented"
      end.

    Section MutatorConsumeGhost.
      Context {Σr : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)}.

      Definition mutator_consume_chunk_ghost {Σe} (c : Chunk Σe) (L : GhostEnv Σe Σr) : Mutator Σr Γ Γ (GhostEnv Σe Σr) :=
        mutator_get_heap >>= fun h =>
        mutator_angelic_list
          "Err [mutator_consume_chunk_ghost]: empty extraction"
          (extract_chunk c h L) >>= fun '(L' , h') =>
        mutator_put_heap h' *> mutator_pure L'.

      Fixpoint mutator_consume_ghost {Σe} (asn : Assertion Σe) (L : GhostEnv Σe Σr) : Mutator Σr Γ Γ (GhostEnv Σe Σr) :=
        match asn with
        | asn_bool tb =>
          match eval_term_ghost L tb with
          | Some tb' => mutator_assert_term tb' *> mutator_pure L
          | None     => mutator_fail "Err [mutator_consume_ghost]: uninstantiated variables when consuming bool assertion"
          end
        | asn_prop P =>
          match ghost_env_to_option_sub L with
          | Some ζ => mutator_assert_formula (formula_prop ζ P) *> mutator_pure L
          | None   => mutator_fail "Err [mutator_consume_ghost]: uninstantiated variables when consuming prop assertion"
          end
        | asn_chunk c => mutator_consume_chunk_ghost c L
        | asn_if tb a1 a2 =>
          match eval_term_ghost L tb with
          | Some tb' => (mutator_assume_term tb'            *> mutator_consume_ghost a1 L) ⊗
                        (mutator_assume_term (term_not tb') *> mutator_consume_ghost a2 L)
          | None     => mutator_fail "Err [mutator_consume_ghost]: uninstantiated variables when consuming if assertion"
          end
        | @asn_match_enum _ E k1 alts =>
          match eval_term_ghost L k1 with
          | Some k1' => ⨁ k2 : 𝑬𝑲 E =>
            mutator_assert_formula (formula_eq k1' (term_enum E k2)) ;;
            mutator_consume_ghost (alts k2) L
          | None => mutator_fail "Err [mutator_consume_ghost]: uninstantiated variables when consuming match enum assertion"
          end
        | asn_sep a1 a2 => mutator_consume_ghost a1 L >>= mutator_consume_ghost a2
        | asn_exist ς τ a =>
          mutator_consume_ghost a (env_snoc L _ None) >>= fun La' =>
          match env_unsnoc La' with
          | (L', Some a) => mutator_pure L'
          | _            => mutator_fail "Err [mutator_consume_ghost]: uninstantiated existential variable"
          end
        end.

      Definition mutator_assert_term_eq_ghost {Σe σ} (te : Term Σe σ) (tr : Term Σr σ) (L : GhostEnv Σe Σr) : Mutator Σr Γ Γ (GhostEnv Σe Σr) :=
        match match_term te tr L with
        | Some L' => mutator_pure L'
        | None    => match eval_term_ghost L te with
                     | Some te' => mutator_assert_formula (formula_eq te' tr) *> mutator_pure L
                     | None     => mutator_fail "Err [mutator_consume_ghost]: uninstantiated existential variable"
                     end
        end.

      Equations(noeqns) mutator_assert_namedenv_eq_ghost {X Σe σs} (te : NamedEnv (X:=X) (Term Σe) σs) (tr : NamedEnv (Term Σr) σs) :
        GhostEnv Σe Σr -> Mutator Σr Γ Γ (GhostEnv Σe Σr) :=
        mutator_assert_namedenv_eq_ghost env_nil env_nil := mutator_pure;
        mutator_assert_namedenv_eq_ghost (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) :=
          fun L => mutator_assert_namedenv_eq_ghost E1 E2 L >>= mutator_assert_term_eq_ghost t1 t2.

    End MutatorConsumeGhost.

    Fixpoint mutator_consume {Σ Σ' Γ} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Mutator Σ' Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assert_term (sub_term ζ b)
      | asn_prop P      => mutator_assert_formula (formula_prop ζ P)
      | asn_chunk c     => mutator_consume_chunk (sub_chunk ζ c)
      | asn_if b a1 a2  => (mutator_assume_term (sub_term ζ b)            *> mutator_consume ζ a1) ⊗
                           (mutator_assume_term (sub_term ζ (term_not b)) *> mutator_consume ζ a2)
      | @asn_match_enum _ E k1 alts =>
        ⨁ k2 : 𝑬𝑲 E => mutator_assert_formula
                         (formula_eq (sub_term ζ k1) (term_enum E k2)) ;;
                       mutator_consume ζ (alts k2)
      | asn_sep a1 a2   => mutator_consume ζ a1 *> mutator_consume ζ a2
      | asn_exist ς τ a => ⨁ t : Term Σ' τ => mutator_consume (sub_snoc ζ (ς , τ) t) a
      end.

    Section WithCont.
      Context {Σ Γ E R} (cont : forall K : 𝑬𝑲 E, Mutator Σ Γ Γ R).

      Equations(noeqns) mutator_exec_match_enum (t : Term Σ (ty_enum E)) : Mutator Σ Γ Γ R :=
        mutator_exec_match_enum (term_lit _ l) := cont l;
        mutator_exec_match_enum t :=
          ⨂ K : 𝑬𝑲 E =>
            mutator_assume_formula (formula_eq t (term_lit (ty_enum E) K)) *>
            cont K.

    End WithCont.

    Context {Σr : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)}.

    (* TODO: The code should be rewritten so this variable can be removed. *)
    Parameter dummy : 𝑺.
    Fixpoint mutator_exec {Σ Γ σ} (s : Stm Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      match s with
      | stm_lit τ l => mutator_pure (term_lit τ l)
      | stm_exp e => mutator_eval_exp e
      | stm_let x τ s k =>
        mutator_exec s >>= fun v =>
        mutator_push_local v *>
        mutator_exec k              <*
        mutator_pop_local
      | stm_let' δ k =>
        mutator_pushs_local (env_map (fun _ => term_lit _) δ) *>
        mutator_exec k <*
        mutator_pops_local _
      | stm_assign x e => mutator_exec e >>= fun v =>
        mutator_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *>
        mutator_pure v
      | stm_call f es =>
        mutator_eval_exps es >>= fun ts : NamedEnv (Term Σ) _ =>
        match CEnv f with
        | @sep_contract_unit _ Σe δ req ens =>
          mutator_consume_ghost req (create_ghost_env Σe Σ) >>= fun L1 =>
          mutator_assert_namedenv_eq_ghost δ ts L1 >>= fun L2 =>
          match ghost_env_to_option_sub L2 with
          | Some ζ => mutator_produce ζ ens *>
                      mutator_pure (term_lit ty_unit tt)
          | None   => mutator_fail "Err [mutator_exec]: uninstantiated variables after consuming precondition"
          end
        | @sep_contract_result_pure _ Σe τ δ result req ens =>
          mutator_consume_ghost req (create_ghost_env Σe Σ) >>= fun L1 =>
          mutator_assert_namedenv_eq_ghost δ ts L1 >>= fun L2 =>
          match ghost_env_to_option_sub L2 with
          | Some ζ => mutator_produce ζ ens *>
                      mutator_pure (sub_term ζ result)
          | None   => mutator_contradiction "Err [mutator_exec]: uninstantiated variables after consuming precondition"
          end
        | @sep_contract_result _ _ Σ' δ result req ens => mutator_fail "Err [mutator_exec]: stm_call of sep_contract_none_result function not implemented"
        | sep_contract_none _ => mutator_fail "Err [mutator_exec]: stm_call of sep_contract_none function"
        end
      | stm_call' Δ δ' τ s =>
        mutator_get_local                                      >>= fun δ =>
        mutator_put_local (env_map (fun _ => term_lit _) δ') >>= fun _ =>
        mutator_exec s                                                >>= fun t =>
        mutator_put_local δ                                    >>= fun _ =>
        mutator_pure t
      | stm_if e s1 s2 =>
        (mutator_assume_exp e ;; mutator_exec s1) ⊗
        (mutator_assume_exp (exp_not e) ;; mutator_exec s2)
      | stm_seq e k => mutator_exec e ;; mutator_exec k
      | stm_assert e1 _ => mutator_eval_exp e1 >>= fun t =>
                           mutator_assert_term t ;;
                           mutator_pure t
      | stm_fail τ s => mutator_fail "Err [mutator_exec]: [stm_fail] reached"
      | stm_match_list e alt_nil xh xt alt_cons => mutator_fail "Err [mutator_exec]: stm_match_list not implemented"
        (* mutator_eval_exp e >>= fun t => *)
        (*                          (* (formula_term_eq t nil) *) *)
        (* (mutator_assume_formula _ ;; mutator_exec alt_nil) ⊗ _ *)
        (* (* mutator_exists (fun ςh ςt => *) *)
        (* (*                   mutator_assume_formula (weaken t (ςh , ςt) = cons ςh ςt) ;; *) *)
        (* (*                   xh  ↦ ςh ;; *) *)
        (* (*                   xt  ↦ ςt ;; *) *)
        (* (*                   mutator_exec alt_cons ;; *) *)
        (* (*                   pop ;; *) *)
        (* (*                   pop) *) *)
      | stm_match_sum e xinl alt_inl xinr alt_inr => mutator_fail "Err [mutator_exec]: stm_match_sum not implemented"
      | stm_match_pair e xl xr rhs => mutator_fail "Err [mutator_exec]: stm_match_pair not implemented"
      | stm_match_enum E e alts =>
        mutator_eval_exp e >>=
        mutator_exec_match_enum (fun K => mutator_exec (alts K))
      | stm_match_tuple e p rhs => mutator_fail "Err [mutator_exec]: stm_match_tuple not implemented"
      | stm_match_union U e alts => mutator_fail "Err [mutator_exec]: stm_match_union not implemented"
      | stm_match_record R e p rhs => mutator_fail "Err [mutator_exec]: stm_match_record not implemented"
      | @stm_read_register _ τ reg =>
        mutator_consume_chunk_ghost (chunk_ptsreg reg (@term_var _ dummy τ (MkInCtx [dummy ∶ τ] 0 eq_refl))) [None]%arg >>= fun L =>
        match env_unsnoc L with
        | (_ , Some t) => mutator_produce_chunk (chunk_ptsreg reg t) *>
                          mutator_pure t
        (* Extracting the points to chunk should never fail here. Because there is exactly one binding
           in the ghost environment and the chunk matching will always instantiate it. *)
        | _            => mutator_fail "Err [mutator_exec]: You have found a unicorn."
        end
      | @stm_write_register _ τ reg e => mutator_eval_exp e >>= fun v =>
        mutator_consume_chunk_ghost (chunk_ptsreg reg (@term_var _ dummy τ (MkInCtx [dummy ∶ τ] 0 eq_refl))) [None]%arg ;;
        mutator_produce_chunk (chunk_ptsreg reg v) *>
        mutator_pure v
      | stm_bind s k => mutator_fail "Err [mutator_exec]: stm_bind not implemented"
      | stm_read_memory _ => mutator_fail "Err [mutator_exec]: stm_read_memory not implemented"
      | stm_write_memory _ _ => mutator_fail "Err [mutator_exec]: stm_write_memory not implemented"
      end.

    Definition mutator_leakcheck {Σ Γ} : Mutator Σ Γ Γ unit :=
      mutator_get_heap >>= fun h =>
      match h with
      | nil => mutator_pure tt
      | _   => mutator_fail "Err [mutator_leakcheck]: heap leak"
      end.

  End MutatorOperations.

  Definition outcome_contract {Δ : Ctx (𝑿 * Ty)} {τ : Ty} (c : SepContract Δ τ) :
    Stm Δ τ -> Outcome ({ Σ & SymbolicState Σ Δ } * list Obligation) :=
    match c with
    | @sep_contract_unit _ Σ δ req ens =>
      fun s =>
        let mut := (mutator_produce (sub_id Σ) req ;;
                    mutator_exec s                 ;;
                    mutator_consume (sub_id Σ) ens ;;
                    mutator_leakcheck)%mut in
        let out := mut (symbolicstate_initial δ) in
        outcome_map (fun '((tt , s) , w) => (existT Σ s,w)) out
    | @sep_contract_result _ Σ _ _ _ _ _ =>
      fun s => outcome_block
    | @sep_contract_result_pure _ Σ _ δ result' req ens =>
      fun s =>
        let mut := (mutator_produce (sub_id Σ) req ;;
                    mutator_exec s >>= fun result =>
                    mutator_consume (sub_id Σ) ens;;
                    mutator_assert_formula (formula_eq result result') ;;
                    mutator_leakcheck)%mut in
        let out := mut (symbolicstate_initial δ) in
        outcome_map (fun '((tt , s) , w) => (existT Σ s,w)) out
    | @sep_contract_none _ _ =>
      fun s => outcome_block
    end.

  Definition ValidContract (Δ : Ctx (𝑿 * Ty)) (τ : Ty)
             (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    outcome_satisfy (outcome_contract c body) (fun '(_,w) => valid_obligations w).

  Definition ValidContractEnv (cenv : SepContractEnv) : Prop :=
    forall (Δ : Ctx (𝑿 * Ty)) (τ : Ty) (f : 𝑭 Δ τ),
      ValidContract (cenv Δ τ f) (Pi f).

End SymbolicContracts.
