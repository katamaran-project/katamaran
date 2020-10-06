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
     Sep.Spec
     Symbolic.Outcome
     Syntax.

From stdpp Require Import base list option.

Import CtxNotations.
Import EnvNotations.
Import ListNotations.
Import OutcomeNotations.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.
Delimit Scope dmut_scope with dmut.

Module Mutators
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

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Formula Σ).
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Chunk Σ).

  Definition inst_formula {Σ} (ι : SymInstance Σ) (fml : Formula Σ) : Prop :=
    match fml with
    | formula_bool t    => is_true (inst_term ι t)
    | formula_prop ζ P  => uncurry_named P (env_map (fun _ => inst_term ι) ζ)
    | formula_eq t1 t2  => inst_term ι t1 =  inst_term ι t2
    | formula_neq t1 t2 => inst_term ι t1 <> inst_term ι t2
    end.

  Definition inst_pathcondition {Σ} (ι : SymInstance Σ) (pc : PathCondition Σ) : Prop :=
    List.fold_right (fun fml pc => inst_formula ι fml /\ pc) True pc.

  Inductive Obligation : Type :=
  | obligation {Σ} (pc : PathCondition Σ) (fml : Formula Σ).

  Definition valid_obligation : Obligation -> Prop :=
    fun '(obligation pc fml) =>
      ForallNamed (fun ι => all_list (inst_formula ι) pc -> inst_formula ι fml).
  Definition valid_obligations (os : list Obligation) : Prop :=
    all_list valid_obligation os.
  Hint Unfold valid_obligation : core.
  Hint Unfold valid_obligations : core.

  Global Instance sub_formula : Subst Formula :=
    fun Σ1 Σ2 ζ fml =>
      match fml with
      | formula_bool t    => formula_bool (sub_term ζ t)
      | formula_prop ζ' P => formula_prop (sub_comp ζ' ζ) P
      | formula_eq t1 t2  => formula_eq (sub_term ζ t1) (sub_term ζ t2)
      | formula_neq t1 t2 => formula_neq (sub_term ζ t1) (sub_term ζ t2)
      end.

  Global Instance sub_localstore {Γ} : Subst (SymbolicLocalStore Γ) :=
    fun Σ1 Σ2 ζ => env_map (fun _ => sub_term ζ).

  Section SymbolicState.

    (* Local Set Primitive Projections. *)

    Record SymbolicState (Γ : Ctx (𝑿 * Ty)) (Σ : Ctx (𝑺 * Ty)) : Type :=
      MkSymbolicState
        { symbolicstate_pathcondition : PathCondition Σ;
          symbolicstate_localstore    : SymbolicLocalStore Γ Σ;
          symbolicstate_heap          : SymbolicHeap Σ
        }.
    Global Arguments symbolicstate_pathcondition {_ _} _.
    Global Arguments symbolicstate_localstore {_ _} _.
    Global Arguments symbolicstate_heap {_ _} _.

    Definition symbolicstate_initial {Γ Σ} (δ : SymbolicLocalStore Γ Σ) : SymbolicState Γ Σ :=
      MkSymbolicState nil δ nil.

    Global Instance sub_symbolicstate {Γ} : Subst (SymbolicState Γ) :=
      fun Σ1 Σ2 ζ '(MkSymbolicState Φ ŝ ĥ) =>
        MkSymbolicState (subst ζ Φ) (subst ζ ŝ) (subst ζ ĥ).

    Definition symbolic_assume_formula {Γ Σ} (fml : Formula Σ) : SymbolicState Γ Σ -> SymbolicState Γ Σ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (fml :: Φ) ŝ ĥ.
    Definition symbolic_assume_exp {Γ Σ} (e : Exp Γ ty_bool) : SymbolicState Γ Σ -> SymbolicState Γ Σ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (formula_bool (symbolic_eval_exp ŝ e) :: Φ) ŝ ĥ.
    Definition symbolic_push_local {Γ x σ Σ} (v : Term Σ σ) : SymbolicState Γ Σ -> SymbolicState (Γ ▻ (x , σ)) Σ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_snoc ŝ (x , σ) v) ĥ.
    Definition symbolic_pop_local {Γ x σ Σ} : SymbolicState (Γ ▻ (x , σ)) Σ -> SymbolicState Γ Σ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_tail ŝ) ĥ.
    Definition wk1_symbolicstate {Γ b Σ} : SymbolicState Γ Σ -> SymbolicState Γ (Σ ▻ b) :=
      subst sub_wk1.

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
      forall ι, reflect (inst_formula ι fml) b.
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

  Let comp {S : Type} (f : S -> option S) (g : S -> option S) : S -> option S :=
    fun s => ssrfun.Option.bind g (f s).
  Infix ">=>" := comp (at level 80, right associativity).

  Section ChunkExtraction.
    Context {Σ : Ctx (𝑺 * Ty)}.

    Fixpoint heap_extractions (h : SymbolicHeap Σ) : list (Chunk Σ * SymbolicHeap Σ) :=
      match h with
      | []     => []
      | c :: h => (c , h) :: map (fun '(c', h') => (c' , c :: h')) (heap_extractions h)
      end.

    Section WithMatchTerm.

      Variable match_term_eqb : forall {σ}, Term Σ σ -> Term Σ σ -> PathCondition Σ -> option (PathCondition Σ).

      Equations(noeqns) match_env_eqb' {σs} (te : Env (Term Σ) σs) (tr : Env (Term Σ) σs) :
        PathCondition Σ -> option (PathCondition Σ) :=
        match_env_eqb' env_nil env_nil := Some;
        match_env_eqb' (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) := match_env_eqb' E1 E2 >=> match_term_eqb t1 t2.

    End WithMatchTerm.

    Equations(noeqns) match_term_eqb {σ} (te : Term Σ σ) (tr : Term Σ σ) :
      PathCondition Σ -> option (PathCondition Σ) :=
      match_term_eqb (term_lit ?(σ) l1) (term_lit σ l2) :=
        if Lit_eqb σ l1 l2 then Some else fun _ => None;
      match_term_eqb (term_inl t1) (term_inl t2) := match_term_eqb t1 t2;
      match_term_eqb (term_inl t1) (term_lit (inl l2)) := match_term_eqb t1 (term_lit _ l2);
      match_term_eqb (term_inr t1) (term_inr t2) := match_term_eqb t1 t2;
      match_term_eqb (term_inr t1) (term_lit (inr l2)) := match_term_eqb t1 (term_lit _ l2);
      match_term_eqb (term_tuple ts1) (term_tuple ts2) := match_env_eqb' (@match_term_eqb) ts1 ts2;
      match_term_eqb te tr :=
        if Term_eqb te tr
        then Some
        else fun pc => Some(formula_eq te tr :: pc).

    Definition match_env_eqb := @match_env_eqb' (@match_term_eqb).

    Equations(noeqns) match_chunk_eqb (ce : Chunk Σ) (cr : Chunk Σ) :
      PathCondition Σ -> option (PathCondition Σ) :=
      match_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2)
      with 𝑷_eq_dec p1 p2 => {
        match_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) := match_env_eqb ts1 ts2;
        match_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _) := fun _ => None
      };
      match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with 𝑹𝑬𝑮_eq_dec r1 r2 => {
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left (@teq_refl eq_refl eq_refl)) := match_term_eqb t1 t2;
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk_eqb _ _  := fun _ => None.

    Definition extract_chunk_eqb (ce : Chunk Σ) (h : SymbolicHeap Σ) (pc : PathCondition Σ) :
      list (PathCondition Σ * SymbolicHeap Σ) :=
      omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk_eqb ce cr pc))
        (heap_extractions h).

  End ChunkExtraction.

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

  Definition GhostEnv (Σe Σr : Ctx (𝑺 * Ty)) : Type := Env (fun b => option (Term Σr (snd b))) Σe.

  Definition create_ghost_env (Σe Σr : Ctx (𝑺 * Ty)) : GhostEnv Σe Σr :=
    env_tabulate (fun _ _ => None).

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

    Definition extract_chunk (ce : Chunk Σe) (h : SymbolicHeap Σr) (L : GhostEnv Σe Σr) :
      list (GhostEnv Σe Σr * SymbolicHeap Σr) :=
      omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk ce cr L))
        (heap_extractions h).

  End WithGhostScope.

  Definition ghost_env_to_option_sub {Σe Σr} (δ : GhostEnv Σe Σr) : option (Sub Σe Σr) :=
    traverse_env (M := option) (fun b mt => mt) δ.

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

  Section MutatorResult.

    (* Local Set Primitive Projections. *)
    Local Set Maximal Implicit Insertion.

    Record MutatorResult (Γ : Ctx (𝑿 * Ty)) (Σ : Ctx (𝑺 * Ty)) (A : Type) : Type :=
      MkMutResult {
          mutator_result_value : A;
          mutator_result_state : SymbolicState Γ Σ;
          mutator_result_obligations : list Obligation;
        }.

  End MutatorResult.

  Section Mutator.

    Definition Mutator (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Γ1 Σ -> Outcome (MutatorResult Γ2 Σ A).
    Bind Scope mutator_scope with Mutator.

    Definition mutator_demonic {Γ1 Γ2 I A Σ} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Γ1 Σ) => (⨂ i : I => ms i s)%out.
    Definition mutator_angelic {Γ1 Γ2 I A Σ} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Γ1 Σ) => (⨁ i : I => ms i s)%out.
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
    Definition mutator_fail {Γ1 Γ2 A Σ} (msg : string) : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_fail msg.
    Definition mutator_contradiction {Γ1 Γ2 A Σ} (msg : string) : Mutator Σ Γ1 Γ2 A :=
      fun s =>
        (⨂ ι : SymInstance Σ =>
         ⨂ _ : all_list (inst_formula ι) (symbolicstate_pathcondition s) =>
         outcome_fail msg)%out.
    Definition mutator_block {Γ1 Γ2 A Σ} : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_block.

    Definition mutator_demonic_binary {Γ1 Γ2 A Σ} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_demonic_binary (m1 s) (m2 s).
    Definition mutator_angelic_binary {Γ1 Γ2 A Σ} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun s => outcome_angelic_binary (m1 s) (m2 s).

    Definition mutator_pure {Γ A Σ} (a : A) : Mutator Σ Γ Γ A :=
      fun s => outcome_pure (MkMutResult a s nil).
    Definition mutator_bind {Γ1 Γ2 Γ3 A B Σ} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      fun s0 => outcome_bind (ma s0) (fun '(MkMutResult a s1 w1) => outcome_bind (f a s1) (fun '(MkMutResult b s2 w2) => outcome_pure (MkMutResult b s2 (w1 ++ w2)))).
    Definition mutator_bind_right {Γ1 Γ2 Γ3 A B Σ} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      mutator_bind ma (fun _ => mb).
    Definition mutator_bind_left {Γ1 Γ2 Γ3 A B Σ} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 A :=
      mutator_bind ma (fun a => mutator_bind mb (fun _ => mutator_pure a)).
    Definition mutator_map {Γ1 Γ2 A B Σ} (f : A -> B) (ma : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 B :=
      mutator_bind ma (fun a => mutator_pure (f a)).
    Definition mutator_angelic_list {Γ A Σ} (msg : string) :
      list A -> Mutator Σ Γ Γ A :=
      fix mutator_angelic_list (xs : list A) :=
        match xs with
        | []      => mutator_contradiction msg
        | x :: [] => mutator_pure x
        | x :: xs => mutator_angelic_binary (mutator_pure x) (mutator_angelic_list xs)
        end.

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

    Notation "x <- ma ;; mb" :=
      (mutator_bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity) : mutator_scope.
    Notation "ma >>= f" := (mutator_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (mutator_bind m1 (fun _ => m2)) : mutator_scope.
    Notation "ma *> mb" := (mutator_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (mutator_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.
  Import MutatorNotations.

  Section MutatorOperations.

    Local Open Scope mutator_scope.

    Definition mutator_state {Γ Γ' Σ A} (f : SymbolicState Γ Σ -> (SymbolicState Γ' Σ * A)) : Mutator Σ Γ Γ' A :=
      fun s => outcome_pure (let (s1,a) := f s in MkMutResult a s1 nil).
    Definition mutator_modify {Γ Γ' Σ} (f : SymbolicState Γ Σ -> SymbolicState Γ' Σ) : Mutator Σ Γ Γ' unit :=
      mutator_state (fun s => (f s,tt)).
    Definition mutator_put {Γ Γ' Σ} (s : SymbolicState Γ' Σ) : Mutator Σ Γ Γ' unit :=
      mutator_state (fun _ => (s,tt)).
    Definition mutator_get {Γ Σ} : Mutator Σ Γ Γ (SymbolicState Γ Σ) :=
      mutator_state (fun s => (s,s)).

    Definition mutator_state_local {Γ Γ' Σ A} (f : SymbolicLocalStore Γ Σ -> (SymbolicLocalStore Γ' Σ * A)) : Mutator Σ Γ Γ' A :=
      mutator_state (fun '(MkSymbolicState Φ δ ĥ) => let (δ',a) := f δ in (MkSymbolicState Φ δ' ĥ,a)).
    Definition mutator_modify_local {Γ Γ' Σ} (f : SymbolicLocalStore Γ Σ -> SymbolicLocalStore Γ' Σ) : Mutator Σ Γ Γ' unit :=
      mutator_state_local (fun δ => (f δ,tt)).
    Definition mutator_put_local {Γ Γ' Σ} (δ : SymbolicLocalStore Γ' Σ) : Mutator Σ Γ Γ' unit :=
      mutator_state_local (fun _ => (δ,tt)).
    Definition mutator_get_local {Γ Σ} : Mutator Σ Γ Γ (SymbolicLocalStore Γ Σ) :=
      mutator_state_local (fun δ => (δ,δ)).
    Definition mutator_gets_local {Γ Σ A} (f : SymbolicLocalStore Γ Σ -> A) : Mutator Σ Γ Γ A :=
      mutator_state_local (fun δ => (δ,f δ)).
    Definition mutator_pop_local {Γ x σ Σ} : Mutator Σ (Γ ▻ (x , σ)) Γ unit :=
      mutator_modify_local (fun δ => env_tail δ).
    Definition mutator_pops_local {Γ Σ} Δ : Mutator Σ (Γ ▻▻ Δ) Γ unit :=
      mutator_modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition mutator_push_local {Γ x σ Σ} (t : Term Σ σ) : Mutator Σ Γ (Γ ▻ (x , σ)) unit :=
      mutator_modify_local (fun δ => env_snoc δ (x , σ) t).
    Definition mutator_pushs_local {Γ Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) : Mutator Σ Γ (Γ ▻▻ Δ) unit :=
      mutator_modify_local (fun δΓ => env_cat δΓ δΔ).

    Definition mutator_state_heap {Γ Σ A} (f : SymbolicHeap Σ -> (SymbolicHeap Σ * A)) : Mutator Σ Γ Γ A :=
      mutator_state (fun '(MkSymbolicState Φ δ h) => let (h',a) := f h in (MkSymbolicState Φ δ h',a)).
    Definition mutator_modify_heap {Γ Σ} (f : SymbolicHeap Σ -> SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      mutator_state_heap (fun h => (f h,tt)).
    Definition mutator_get_heap {Γ Σ} : Mutator Σ Γ Γ (SymbolicHeap Σ) :=
      mutator_state_heap (fun h => (h,h)).
    Definition mutator_put_heap {Γ Σ} (h : SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      mutator_state_heap (fun _ => (h,tt)).

    Definition mutator_state_pathcondition {Γ Σ A} (f : PathCondition Σ -> (PathCondition Σ * A)) : Mutator Σ Γ Γ A :=
      mutator_state (fun '(MkSymbolicState Φ δ h) => let (Φ',a) := f Φ in (MkSymbolicState Φ' δ h,a)).
    Definition mutator_modify_pathcondition {Γ Σ} (f : PathCondition Σ -> PathCondition Σ) : Mutator Σ Γ Γ unit :=
      mutator_state_pathcondition (fun Φ => (f Φ,tt)).
    Definition mutator_get_pathcondition {Γ Σ} : Mutator Σ Γ Γ (PathCondition Σ) :=
      mutator_state_pathcondition (fun Φ => (Φ,Φ)).
    Definition mutator_put_pathcondition {Γ Σ} (Φ : PathCondition Σ) : Mutator Σ Γ Γ unit :=
      mutator_state_pathcondition (fun _ => (Φ,tt)).

    Definition mutator_eval_exp {Γ σ Σ} (e : Exp Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      mutator_gets_local (fun δ => symbolic_eval_exp δ e).
    Definition mutator_eval_exps {Γ Σ} {σs : Ctx (𝑿 * Ty)} (es : NamedEnv (Exp Γ) σs) : Mutator Σ Γ Γ (NamedEnv (Term Σ) σs) :=
      mutator_gets_local (fun δ => env_map (fun _ => symbolic_eval_exp δ) es).

    Definition mutator_assume_formula {Γ Σ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      match try_solve_formula fml with
      | Some true  => mutator_pure tt
      | Some false => mutator_block
      | None       => mutator_modify (symbolic_assume_formula fml)
      end.
    (* Definition mutator_assume_formula {Γ Σ} (fml : Formula Σ) : Mutator Σ Γ Γ unit := *)
    (*   mutator_modify (symbolic_assume_formula fml). *)
    Definition mutator_assume_term {Γ Σ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assume_formula (formula_bool t).
    Definition mutator_assume_exp {Γ Σ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assume_term.

    Definition mutator_assert_formula {Γ Σ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      match try_solve_formula fml with
      | Some true  => mutator_pure tt
      | Some false => mutator_fail "Err [mutator_assert_formula]: unsatisfiable"
      | None       => fun δ => outcome_pure (MkMutResult tt δ (obligation (symbolicstate_pathcondition δ) fml :: nil))
      end.
    Definition mutator_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) : Mutator Σ Γ Γ unit :=
      mutator_state_pathcondition (fun pc => (fmls ++ pc , tt)).
    (* Definition mutator_assert_formula {Γ Σ} (fml : Formula Σ) : Mutator Σ Γ Γ unit := *)
    (*   fun δ => outcome_pure (tt , δ , obligation (symbolicstate_pathcondition δ) fml :: nil). *)

    Definition mutator_assert_term {Γ Σ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assert_formula (formula_bool t).
    Definition mutator_assert_exp {Γ Σ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assert_term.

    Definition mutator_produce_chunk {Γ Σ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify_heap (fun h => c :: h).

    Definition mutator_consume_chunk {Γ Σ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_get_heap >>= fun h =>
      mutator_get_pathcondition >>= fun pc =>
      mutator_angelic_list
        "Err [mutator_consume_chunk]: empty extraction"
        (extract_chunk_eqb c h pc) >>= fun '(pc' , h') =>
        mutator_put_heap h' ;;
        mutator_put_pathcondition pc'.

    Global Arguments mutator_push_local {Γ _ _} [Σ] _.
    Global Arguments mutator_assume_formula {Γ} [Σ] _.
    Global Arguments mutator_assume_term {Γ} [Σ] _.
    Global Arguments mutator_assert_formula {Γ} [Σ] _.
    Global Arguments mutator_assert_formulas {Γ} [Σ] _.
    Global Arguments mutator_produce_chunk {Γ} [Σ] _.
    Global Arguments mutator_consume_chunk {Γ} [Σ] _.

    Fixpoint mutator_produce {Γ Σ Σ'} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Mutator Σ' Γ Γ unit :=
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

    Fixpoint mutator_consume {Γ Σ Σ'} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Mutator Σ' Γ Γ unit :=
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
      Context {Γ Σ E R} (cont : forall K : 𝑬𝑲 E, Mutator Σ Γ Γ R).

      Equations(noeqns) mutator_exec_match_enum (t : Term Σ (ty_enum E)) : Mutator Σ Γ Γ R :=
        mutator_exec_match_enum (term_lit _ l) := cont l;
        mutator_exec_match_enum t :=
          ⨂ K : 𝑬𝑲 E =>
            mutator_assume_formula (formula_eq t (term_lit (ty_enum E) K)) *>
            cont K.

    End WithCont.

    (* TODO: The code should be rewritten so this variable can be removed. *)
    Parameter dummy : 𝑺.

    (* Definition mutator_call {Σ Γ Δ τ} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) : Mutator Σ Γ Γ (Term Σ τ) := *)
    (*   match contract with *)
    (*   (* | @sep_contract_unit _ Σe δ req ens => *) *)
    (*   (*   mutator_consume_ghost req (create_ghost_env Σe Σ) >>= fun L1 => *) *)
    (*   (*   mutator_assert_namedenv_eq_ghost δ ts L1 >>= fun L2 => *) *)
    (*   (*   match ghost_env_to_option_sub L2 with *) *)
    (*   (*   | Some ζ => mutator_produce ζ ens *> *) *)
    (*   (*               mutator_pure (term_lit ty_unit tt) *) *)
    (*   (*   | None   => mutator_fail "Err [mutator_exec]: uninstantiated variables after consuming precondition" *) *)
    (*   (*   end *) *)
    (*   | @sep_contract_result_pure _ _ Σe δ result req ens => *)
    (*     mutator_consume_ghost req (create_ghost_env Σe Σ) >>= fun L1 => *)
    (*     mutator_assert_namedenv_eq_ghost δ ts L1 >>= fun L2 => *)
    (*     match ghost_env_to_option_sub L2 with *)
    (*     | Some ζ => mutator_produce ζ ens *> *)
    (*                 mutator_pure (sub_term ζ result) *)
    (*     | None   => mutator_contradiction "Err [mutator_exec]: uninstantiated variables after consuming precondition" *)
    (*     end *)
    (*   | @sep_contract_result _ _ Σ' δ result req ens => mutator_fail "Err [mutator_exec]: stm_call of sep_contract_none_result function not implemented" *)
    (*   | sep_contract_none _ _ => mutator_fail "Err [mutator_exec]: stm_call of sep_contract_none function" *)
    (*   end. *)

    Fixpoint mutator_exec {Σ Γ σ} (s : Stm Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      match s with
      | stm_lit τ l => mutator_pure (term_lit τ l)
      | stm_exp e => mutator_eval_exp e
      | stm_let x τ s k =>
        mutator_exec s >>= fun v =>
        mutator_push_local v *>
        mutator_exec k              <*
        mutator_pop_local
      | stm_block δ k =>
        mutator_pushs_local (lift_localstore δ) *>
        mutator_exec k <*
        mutator_pops_local _
      | stm_assign x e => mutator_exec e >>= fun v =>
        mutator_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *>
        mutator_pure v
      | stm_call f es => mutator_fail "Err [mutator_exec]: stm_call not supported"
      | stm_call_external f es => mutator_fail "Err [mutator_exec]: stm_call not supported"
      | stm_call_frame Δ δ' τ s =>
        mutator_get_local                                      >>= fun δ =>
        mutator_put_local (lift_localstore δ') >>= fun _ =>
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
      | stm_fail τ s => mutator_contradiction "Err [mutator_exec]: [stm_fail] reached"
      | stm_match_enum E e alts =>
        mutator_eval_exp e >>=
        mutator_exec_match_enum (fun K => mutator_exec (alts K))
      | @stm_read_register _ τ reg =>
        mutator_consume_chunk_ghost (chunk_ptsreg reg (@term_var _ dummy τ (MkInCtx [(dummy,τ)] 0 eq_refl))) [None]%arg >>= fun L =>
        match env_unsnoc L with
        | (_ , Some t) => mutator_produce_chunk (chunk_ptsreg reg t) *>
                          mutator_pure t
        (* Extracting the points to chunk should never fail here. Because there is exactly one binding
           in the ghost environment and the chunk matching will always instantiate it. *)
        | _            => mutator_fail "Err [mutator_exec]: You have found a unicorn."
        end
      | @stm_write_register _ τ reg e => mutator_eval_exp e >>= fun v =>
        mutator_consume_chunk_ghost (chunk_ptsreg reg (@term_var _ dummy τ (MkInCtx [(dummy,τ)] 0 eq_refl))) [None]%arg ;;
        mutator_produce_chunk (chunk_ptsreg reg v) *>
        mutator_pure v
      | stm_match_list e alt_nil xh xt alt_cons =>
        mutator_fail "Err [mutator_exec]: stm_match_list not supported. use dynamic mutators"
      | stm_match_sum e xinl alt_inl xinr alt_inr =>
        mutator_fail "Err [mutator_exec]: stm_match_sum not supported. use dynamic mutators"
      | stm_match_pair e xl xr rhs =>
        mutator_fail "Err [mutator_exec]: stm_match_pair not supported. use dynamic mutators"
      | stm_match_tuple e p rhs =>
        mutator_fail "Err [mutator_exec]: stm_match_tuple not supported. use dynamic mutators"
      | stm_match_union U e alts =>
        mutator_fail "Err [mutator_exec]: stm_match_union not supported. use dynamic mutators"
      | stm_match_record R e p rhs =>
        mutator_fail "Err [mutator_exec]: stm_match_record not supported. use dynamic mutators"
      | stm_bind s k => mutator_fail "Err [mutator_exec]: stm_bind not supported"
      end.

    Definition mutator_leakcheck {Γ Σ} : Mutator Σ Γ Γ unit :=
      mutator_get_heap >>= fun h =>
      match h with
      | nil => mutator_pure tt
      | _   => mutator_fail "Err [mutator_leakcheck]: heap leak"
      end.

  End MutatorOperations.

  Definition mutator_outcome_contract {Δ : Ctx (𝑿 * Ty)} {τ : Ty} (c : SepContract Δ τ) :
    Stm Δ τ -> Outcome (list Obligation) :=
    match c with
    | MkSepContract _ _ Σe δ req result ens =>
      fun s =>
        let mut := (mutator_produce (sub_id Σe) req ;;
                    mutator_exec s >>= fun v =>
                    mutator_consume (env_snoc (sub_id Σe) (result,τ) v) ens;;
                    mutator_leakcheck)%mut in
        let out := mut (symbolicstate_initial δ) in
        outcome_map mutator_result_obligations out
    end.

  Definition ValidContractMut (Δ : Ctx (𝑿 * Ty)) (τ : Ty)
             (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    outcome_satisfy (mutator_outcome_contract c body) valid_obligations.

  Section DynamicMutatorResult.

    (* Local Set Primitive Projections. *)
    Local Set Maximal Implicit Insertion.

    Record DynamicMutatorResult (Γ : Ctx (𝑿 * Ty)) (A : Ctx (𝑺 * Ty) -> Type) (Σ : Ctx (𝑺 * Ty)) : Type :=
      MkDynMutResult {
          dmutres_context      : Ctx (𝑺 * Ty);
          dmutres_substitution : Sub Σ dmutres_context;
          dmutres_result       : MutatorResult Γ dmutres_context (A dmutres_context);
        }.

    Global Arguments MkDynMutResult {_ _ _ _} _ _.

  End DynamicMutatorResult.

  Section DynamicMutator.

    Definition Unit : Ctx (𝑺 * Ty) -> Type := fun _ => unit.
    Global Instance SubstUnit : Subst Unit :=
      fun _ _ _ _ => tt.

    Definition DynamicMutator (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Ctx (𝑺 * Ty) -> Type) (Σ : Ctx (𝑺 * Ty)) : Type :=
      forall Σ', Sub Σ Σ' -> SymbolicState Γ1 Σ' -> Outcome (DynamicMutatorResult Γ2 A Σ').
    Bind Scope dmut_scope with DynamicMutator.

    Definition dmut_pure {Γ A} `{Subst A} {Σ} (a : A Σ) : DynamicMutator Γ Γ A Σ :=
      fun Σ' ζ s => outcome_pure (MkDynMutResult (sub_id Σ') (MkMutResult (subst ζ a) s [])).
    Definition dmut_map {Γ1 Γ2 A B} (f : forall {Σ}, A Σ -> B Σ) {Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 B Σ :=
      fun Σ1 ζ1 s1 => outcome_map (fun '(MkDynMutResult ζ2 (MkMutResult a s2 w)) => MkDynMutResult ζ2 (MkMutResult (f a) s2 w)) (ma Σ1 ζ1 s1).
    Definition dmut_bind {Γ1 Γ2 Γ3 A B Σ}
      (ma : DynamicMutator Γ1 Γ2 A Σ) (f : forall Σ', Sub Σ Σ' -> A Σ' -> DynamicMutator Γ2 Γ3 B Σ') : DynamicMutator Γ1 Γ3 B Σ :=
      fun Σ0 ζ0 s0 =>
        outcome_bind (ma Σ0 ζ0 s0)                            (fun '(MkDynMutResult ζ1 (MkMutResult a s1 w1)) =>
        outcome_bind (f _ (sub_comp ζ0 ζ1) a _ (sub_id _) s1) (fun '(MkDynMutResult ζ2 (MkMutResult b s2 w2)) =>
        outcome_pure (MkDynMutResult (sub_comp ζ1 ζ2) (MkMutResult b s2 (w1 ++ w2))))).
    Definition dmut_join {Γ1 Γ2 Γ3 A Σ} (mm : DynamicMutator Γ1 Γ2 (DynamicMutator Γ2 Γ3 A) Σ) :
      DynamicMutator Γ1 Γ3 A Σ := dmut_bind mm (fun _ _ m => m).

    Global Instance dmut_sub {Γ1 Γ2 A} : Subst (DynamicMutator Γ1 Γ2 A) :=
      fun _ _ ζ1 p _ ζ2 => p _ (sub_comp ζ1 ζ2).
    Global Arguments dmut_sub {_ _ _ _ _} ζ1 p.
    Definition dmut_bind_right {Γ1 Γ2 Γ3 A B Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) : DynamicMutator Γ1 Γ3 B Σ :=
      dmut_bind ma (fun _ ζ _ => dmut_sub ζ mb).
    Definition dmut_bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} {Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) : DynamicMutator Γ1 Γ3 A Σ :=
      dmut_bind ma (fun _ ζ a => dmut_bind_right (dmut_sub ζ mb) (dmut_pure a)) .

    Definition dmut_lift {Γ1 Γ2 A} {Σ} (m : forall Σ', Sub Σ Σ' -> Mutator Σ' Γ1 Γ2 (A Σ')) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 s => outcome_map (MkDynMutResult (sub_id _)) (m Σ1 ζ1 s).
    Definition dmut_lift_kleisli {Γ1 Γ2 A B} `{Subst A} (m : forall Σ, A Σ -> Mutator Σ Γ1 Γ2 (B Σ)) :
      forall Σ, A Σ -> DynamicMutator Γ1 Γ2 B Σ :=
      fun _ a => dmut_lift (fun _ ζ => m _ (subst ζ a)).
    Definition dmut_fail {Γ1 Γ2 A Σ} (msg : string) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_lift (fun _ _ => mutator_fail msg).
    Definition dmut_contradiction {Γ1 Γ2 A Σ} (msg : string) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_lift (fun _ _ => mutator_contradiction msg).
    Definition dmut_block {Γ1 Γ2 A Σ} : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_lift (fun _ _ => mutator_block).

    Definition dmut_angelic {Γ1 Γ2 I A Σ} (ms : I -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 s1 => outcome_angelic (fun i => ms i Σ1 ζ1 s1).
    Definition dmut_demonic {Γ1 Γ2 I A Σ} (ms : I -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 s1 => outcome_demonic (fun i => ms i Σ1 ζ1 s1).
    Definition dmut_angelic_binary {Γ1 Γ2 A Σ} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 s1 => outcome_angelic_binary (m1 Σ1 ζ1 s1) (m2 Σ1 ζ1 s1).
    Definition dmut_demonic_binary {Γ1 Γ2 A Σ} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 s1 => outcome_demonic_binary (m1 Σ1 ζ1 s1) (m2 Σ1 ζ1 s1).
    Definition dmut_angelic_list {Γ A} `{Subst A} {Σ} (msg : string) :
      list (A Σ) -> DynamicMutator Γ Γ A Σ :=
      fix dmut_angelic_list (xs : list (A Σ)) :=
        match xs with
        | []      => dmut_contradiction msg
        | x :: [] => dmut_pure x
        | x :: xs => dmut_angelic_binary (dmut_pure x) (dmut_angelic_list xs)
        end.
    Definition dmut_demonic_list {Γ A} `{Subst A} {Σ} :
      list (A Σ) -> DynamicMutator Γ Γ A Σ :=
      fix dmut_demonic_list (xs : list (A Σ)) :=
        match xs with
        | []      => dmut_block
        | x :: [] => dmut_pure x
        | x :: xs => dmut_demonic_binary (dmut_pure x) (dmut_demonic_list xs)
        end.

    Definition dmut_fresh {Γ A Σ} b (ma : DynamicMutator Γ Γ A (Σ ▻ b)) : DynamicMutator Γ Γ A Σ :=
      fun Σ1 ζ1 s1 =>
        outcome_map
          (fun '(MkDynMutResult ζ r) => MkDynMutResult (sub_comp sub_wk1 ζ) r)
          (ma _ (sub_up1 ζ1) (wk1_symbolicstate s1)).
    Global Arguments dmut_fresh {_ _ _} _ _.

  End DynamicMutator.
  Bind Scope dmut_scope with DynamicMutator.

  Module Proper.

    Definition Mor (Σ : Ctx (𝑺 * Ty)) (A B : Ctx (𝑺 * Ty) -> Type) : Type :=
      forall Σ', Sub Σ Σ' -> A Σ' -> B Σ'.

    Definition DynamicMutator (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Ctx (𝑺 * Ty) -> Type) (Σ : Ctx (𝑺 * Ty)) : Type :=
      SymbolicState Γ1 Σ -> Outcome (DynamicMutatorResult Γ2 A Σ).

    Definition dmut_pure {Γ A} {Σ} : Mor Σ A (DynamicMutator Γ Γ A) :=
      fun Σ' ζ' a s =>
        outcome_pure (MkDynMutResult (sub_id Σ') (MkMutResult a s nil)).
    Definition dmut_map {Γ1 Γ2 A B Σ} (f : Mor Σ A B) : Mor Σ (DynamicMutator Γ1 Γ2 A) (DynamicMutator Γ1 Γ2 B) :=
      fun Σ1 ζ1 ma s1 =>
        outcome_map (fun '(MkDynMutResult ζ2 (MkMutResult a s2 w)) => MkDynMutResult ζ2 (MkMutResult (f _ (sub_comp ζ1 ζ2) a) s2 w)) (ma s1).
    Definition dmut_bind {Γ1 Γ2 Γ3 A B Σ} (f : Mor Σ A (DynamicMutator Γ2 Γ3 B)) :
      Mor Σ (DynamicMutator Γ1 Γ2 A) (DynamicMutator Γ1 Γ3 B) :=
      fun Σ0 ζ0 m0 s0 =>
        outcome_bind (m0 s0) (fun '(MkDynMutResult ζ1 (MkMutResult a s1 w1)) =>
        outcome_bind (f _ (sub_comp ζ0 ζ1) a s1) (fun '(MkDynMutResult ζ2 (MkMutResult b s2 w2)) =>
        outcome_pure (MkDynMutResult (sub_comp ζ1 ζ2) (MkMutResult b s2 (w1 ++ w2))))).
    Definition dmut_join {Γ1 Γ2 Γ3 A Σ} :
      Mor Σ (DynamicMutator Γ1 Γ2 (DynamicMutator Γ2 Γ3 A)) (DynamicMutator Γ1 Γ3 A) :=
      fun Σ1 ζ1 => dmut_bind (fun _ _ m => m) ζ1.

    Definition dmut_sub {A B Σ1 Σ2} (ζ2 : Sub Σ1 Σ2) : Mor Σ1 A B -> Mor Σ2 A B :=
      fun m Σ3 ζ3 => m Σ3 (sub_comp ζ2 ζ3).
    Global Arguments dmut_sub {_ _ _ _} ζ2 m.

    Definition dmut_lift {Γ1 Γ2 A} {Σ} (m : Mutator Σ Γ1 Γ2 (A Σ)) : DynamicMutator Γ1 Γ2 A Σ :=
      fun s => outcome_map (MkDynMutResult (sub_id Σ)) (m s).
    Definition dmut_lift_kleisli {Γ1 Γ2 A B Σ} (m : A Σ -> Mutator Σ Γ1 Γ2 (B Σ)) :
      A Σ -> DynamicMutator Γ1 Γ2 B Σ :=
      fun a => dmut_lift (m a).
    Definition dmut_fail {Γ1 Γ2 A Σ} (msg : string) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_lift (mutator_fail msg).
    Definition dmut_contradiction {Γ1 Γ2 A Σ} (msg : string) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_lift (mutator_contradiction msg).
    Definition dmut_block {Γ1 Γ2 A Σ} : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_lift (mutator_block).

    Definition dmut_angelic {Γ1 Γ2 I A Σ} (ms : I -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun s1 => outcome_angelic (fun i => ms i s1).
    Definition dmut_demonic {Γ1 Γ2 I A Σ} (ms : I -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun s1 => outcome_demonic (fun i => ms i s1).
    Definition dmut_angelic_binary {Γ1 Γ2 A Σ} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_angelic (fun b : bool => if b then m1 else m2).
    Definition dmut_demonic_binary {Γ1 Γ2 A Σ} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_demonic (fun b : bool => if b then m1 else m2).

    Definition dmut_fresh {Γ A Σ} b (m : Mor (Σ ▻ b) Unit (DynamicMutator Γ Γ A)) :
      Mor Σ Unit (DynamicMutator Γ Γ A) :=
      fun Σ1 ζ1 _ s1 =>
        outcome_map
          (fun '(MkDynMutResult ζ r) =>
             MkDynMutResult (sub_comp sub_wk1 ζ) r)
          (m _ (sub_up1 ζ1) tt (wk1_symbolicstate s1)).
    Global Arguments dmut_fresh {_ _ _} _ _.

  End Proper.

  Module DynamicMutatorNotations.

    Notation "'⨂' x .. y => F" :=
      (dmut_demonic (fun x => .. (dmut_demonic (fun y => F)) .. )) : dmut_scope.

    Notation "'⨁' x .. y => F" :=
      (dmut_angelic (fun x => .. (dmut_angelic (fun y => F)) .. )) : dmut_scope.

    Infix "⊗" := dmut_demonic_binary (at level 40, left associativity) : dmut_scope.
    Infix "⊕" := dmut_angelic_binary (at level 50, left associativity) : dmut_scope.

    Notation "x <- ma ;; mb" := (dmut_bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : dmut_scope.
    Notation "ma >>= f" := (dmut_bind ma f) (at level 50, left associativity) : dmut_scope.
    Notation "m1 ;; m2" := (dmut_bind_right m1 m2) : dmut_scope.

  End DynamicMutatorNotations.
  Import DynamicMutatorNotations.
  Local Open Scope dmut_scope.

  (* Definition dmut_get {Γ Σ} : DynamicMutator Γ Γ (SymbolicState Γ) Σ := *)
  (*   dmut_lift (fun _ _ => mutator_get). *)
  (* Definition dmut_put {Γ Γ' Σ} (s : SymbolicState Γ' Σ) : DynamicMutator Γ Γ' Unit Σ := *)
  (*   dmut_lift (fun _ ζ => mutator_put (subst ζ s)). *)
  (* Definition dmut_modify {Γ Γ' Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicState Γ Σ' -> SymbolicState Γ' Σ') : DynamicMutator Γ Γ' Unit Σ := *)
  (*   dmut_lift (fun _ ζ => mutator_modify (f _ ζ)). *)
  Definition dmut_get_local {Γ Σ} : DynamicMutator Γ Γ (fun Σ => SymbolicLocalStore Γ Σ) Σ :=
    dmut_lift (fun _ _ => mutator_get_local).
  Definition dmut_put_local {Γ Γ' Σ} (δ' : SymbolicLocalStore Γ' Σ) : DynamicMutator Γ Γ' Unit Σ :=
    dmut_lift (fun _ ζ => mutator_put_local (subst ζ δ')).
  Definition dmut_modify_local {Γ Γ' Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicLocalStore Γ Σ' -> SymbolicLocalStore Γ' Σ') : DynamicMutator Γ Γ' Unit Σ :=
    dmut_lift (fun _ ζ => mutator_modify_local (f _ ζ)).
  Definition dmut_pop_local {Γ x σ Σ} : DynamicMutator (Γ ▻ (x , σ)) Γ Unit Σ :=
    dmut_lift (fun _ _ => mutator_pop_local).
  Definition dmut_pops_local {Γ} Δ {Σ} : DynamicMutator (Γ ▻▻ Δ) Γ Unit Σ :=
    dmut_lift (fun _ _ => mutator_pops_local Δ).
  Definition dmut_push_local {Γ x σ Σ} (t : Term Σ σ) : DynamicMutator Γ (Γ ▻ (x , σ)) Unit Σ :=
    dmut_lift_kleisli mutator_push_local t.
  Definition dmut_pushs_local {Γ Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) : DynamicMutator Γ (Γ ▻▻ Δ) Unit Σ :=
    dmut_lift (fun _ ζ => mutator_pushs_local (env_map (fun _ => sub_term ζ) δΔ)).
  Definition dmut_get_heap {Γ Σ} : DynamicMutator Γ Γ SymbolicHeap Σ :=
    dmut_lift (fun _ _ => mutator_get_heap).
  (* Definition dmut_modify_heap {Γ Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicHeap Σ' -> SymbolicHeap Σ') : DynamicMutator Γ Γ Unit Σ := *)
  (*   dmut_lift (fun _ ζ => mutator_modify_heap (f _ ζ)). *)
  (* Definition dmut_put_heap {Γ Σ} (h : SymbolicHeap Σ) : DynamicMutator Γ Γ Unit Σ := *)
  (*   dmut_lift (fun _ ζ => mutator_put_heap (subst ζ h)). *)
  Definition dmut_eval_exp {Γ σ} (e : Exp Γ σ) {Σ} : DynamicMutator Γ Γ (fun Σ => Term Σ σ) Σ :=
    dmut_lift (fun _ _ => mutator_eval_exp e).
  Definition dmut_eval_exps {Γ Σ} {σs : Ctx (𝑿 * Ty)} (es : NamedEnv (Exp Γ) σs) : DynamicMutator Γ Γ (fun Σ => NamedEnv (Term Σ) σs) Σ :=
    dmut_lift (fun _ _ => mutator_eval_exps es).

  Definition dmut_assume_formula {Γ Σ} (fml : Formula Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift_kleisli mutator_assume_formula fml.
  Definition dmut_assume_term {Γ Σ} (t : Term Σ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift_kleisli mutator_assume_term t.
  Definition dmut_assume_exp {Γ Σ} (e : Exp Γ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift (fun _ _ => mutator_assume_exp e).
  Definition dmut_assume_prop {Γ Σ} (P : abstract_named Lit Σ Prop) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift (fun _ ζ => mutator_assume_formula (formula_prop ζ P)).

  Definition dmut_assert_formula {Γ Σ} (fml : Formula Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift_kleisli mutator_assert_formula fml.
  Definition dmut_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift_kleisli mutator_assert_formulas fmls.
  Definition dmut_assert_term {Γ Σ} (t : Term Σ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_assert_formula (formula_bool t).
  Definition dmut_assert_exp {Γ Σ} (e : Exp Γ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift (fun _ _ => mutator_assert_exp e).
  Definition dmut_produce_chunk {Γ Σ} (c : Chunk Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift_kleisli mutator_produce_chunk c.
  Definition dmut_consume_chunk {Γ Σ} (c : Chunk Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift_kleisli mutator_consume_chunk c.

  Fixpoint dmut_produce {Γ Σ} (asn : Assertion Σ) : DynamicMutator Γ Γ Unit Σ :=
    match asn with
    | asn_bool b      => dmut_assume_term b
    | asn_prop P      => dmut_assume_prop P
    | asn_chunk c     => dmut_produce_chunk c
    | asn_if b a1 a2  => (dmut_assume_term b ;; dmut_produce a1) ⊗
                         (dmut_assume_term (term_not b) ;; dmut_produce a2)
    | asn_match_enum E k1 alts =>
      ⨂ k2 : 𝑬𝑲 E =>
      dmut_assume_formula (formula_eq k1 (term_enum E k2)) ;;
      dmut_produce (alts k2)
    | asn_sep a1 a2   => dmut_produce a1 ;; dmut_produce a2
    | asn_exist ς τ a => dmut_fresh (ς,τ) (dmut_produce a)
    end.

  Fixpoint dmut_consume {Γ Σ} (asn : Assertion Σ) : DynamicMutator Γ Γ Unit Σ :=
    match asn with
    | asn_bool b      => dmut_assert_term b
    | asn_prop P      => dmut_assert_formula (formula_prop (sub_id _) P)
    | asn_chunk c     => dmut_consume_chunk c
    | asn_if b a1 a2  => (dmut_assume_term b ;; dmut_consume a1) ⊗
                         (dmut_assume_term (term_not b) ;; dmut_consume a2)
    | @asn_match_enum _ E k1 alts =>
      ⨁ k2 : 𝑬𝑲 E =>
      dmut_assert_formula (formula_eq k1 (term_enum E k2)) ;;
      dmut_consume (alts k2)
    | asn_sep a1 a2   => dmut_consume a1 ;; dmut_consume a2
    | asn_exist ς τ a =>
      ⨁ t : Term Σ τ =>
      dmut_sub (sub_snoc (sub_id _) (ς , τ) t) (dmut_consume a)
    end.

  Definition dmut_consume' {Γ Σ} (asn : Assertion Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_lift (fun _ ζ => mutator_consume ζ asn).

  Definition dmut_call {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σr :=
    match contract with
    | MkSepContract _ _ Σe δ req result ens =>
      ⨁ ξ : Sub Σe Σr =>
      dmut_assert_formulas (formula_eqs ts (env_map (fun b => sub_term ξ) δ)) ;;
      dmut_sub ξ
        (dmut_consume req ;;
         dmut_fresh (result,τ)
           (dmut_produce ens ;;
            dmut_pure (@term_var _ result _ inctx_zero)))
    end.

  Fixpoint dmut_exec {Γ σ Σ} (s : Stm Γ σ) {struct s} :
    DynamicMutator Γ Γ (fun Σ => Term Σ σ) Σ :=
    match s with
    | stm_lit τ l => dmut_pure (term_lit τ l)
    | stm_exp e => dmut_eval_exp e
    | stm_let x τ s1 s2 =>
      t1 <- dmut_exec s1 ;;
      dmut_push_local t1 ;;
      t2 <- dmut_exec s2 ;;
      dmut_pop_local ;;
      dmut_pure t2
    | stm_block δ s =>
      dmut_pushs_local (lift_localstore δ) ;;
      t <- dmut_exec s ;;
      dmut_pops_local _ ;;
      dmut_pure t
    | stm_assign x s =>
      t <- dmut_exec s ;;
      dmut_modify_local (fun _ ζ δ => δ ⟪ x ↦ subst ζ t ⟫)%env ;;
      dmut_pure t
    | stm_call f es =>
      match CEnv f with
      | Some c =>
        ts <- dmut_eval_exps es ;;
        dmut_call c ts
      | None   => dmut_fail "Err [dmut_exec]: Function call without contract"
      end
    | stm_call_frame Δ δ τ s =>
      δr <- dmut_get_local ;;
      dmut_put_local (lift_localstore δ) ;;
      dmut_bind_left (dmut_exec s) (dmut_put_local δr)
    | stm_call_external f es =>
      ts <- dmut_eval_exps es ;;
      dmut_call (CEnvEx f) ts
    | stm_if e s1 s2 =>
        (dmut_assume_exp e ;; dmut_exec s1) ⊗
        (dmut_assume_exp (exp_not e) ;; dmut_exec s2)
    | stm_seq s1 s2 => dmut_exec s1 ;; dmut_exec s2
    | stm_assert e1 _ =>
      t <- dmut_eval_exp e1 ;;
      dmut_assert_term t ;;
      dmut_pure t
    | stm_fail τ _ =>
      dmut_contradiction "Err [dmut_exec]: [stm_fail] reached"
    | stm_match_list e s1 xh xt s2 =>
      t <- dmut_eval_exp e ;;
      (dmut_assume_formula
         (formula_eq t (term_lit (ty_list _) nil));;
       dmut_exec s1) ⊗
      (dmut_fresh
         (𝑿to𝑺 xh,_) (dmut_fresh (𝑿to𝑺 xt,_)
         (dmut_assume_formula
            (formula_eq (sub_term (sub_comp sub_wk1 sub_wk1) t)
                        (term_binop binop_cons (@term_var _ _ _ (inctx_succ inctx_zero)) (@term_var _ _ _ inctx_zero)));;
          dmut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
          dmut_push_local (@term_var _ _ _ inctx_zero);;
          t2 <- dmut_exec s2 ;;
          dmut_pop_local ;;
          dmut_pop_local ;;
          dmut_pure t2)))
    | stm_match_sum e xinl s1 xinr s2 =>
      t <- dmut_eval_exp e ;;
      dmut_fresh _
        (dmut_assume_formula
           (formula_eq (sub_term sub_wk1 t) (term_inl (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero)));;
         dmut_push_local (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero);;
         dmut_bind_left (dmut_exec s1) dmut_pop_local) ⊗
      dmut_fresh _
        (dmut_assume_formula
           (formula_eq (sub_term sub_wk1 t) (term_inr (@term_var _ (𝑿to𝑺 xinr) _ inctx_zero)));;
         dmut_push_local (@term_var _ (𝑿to𝑺 xinr) _ inctx_zero);;
         dmut_bind_left (dmut_exec s2) dmut_pop_local)
    | stm_match_pair e xl xr s =>
      t <- dmut_eval_exp e ;;
      dmut_fresh (𝑿to𝑺 xl,_) (dmut_fresh (𝑿to𝑺 xr,_)
        (dmut_assume_formula
           (formula_eq
              (sub_term (sub_comp sub_wk1 sub_wk1) t)
              (term_binop binop_pair (@term_var _ (𝑿to𝑺 xl) _ (inctx_succ inctx_zero)) (@term_var _ (𝑿to𝑺 xr) _ inctx_zero)));;
         dmut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
         dmut_push_local (@term_var _ _ _ inctx_zero);;
         t <- dmut_exec s ;;
         dmut_pop_local ;;
         dmut_pop_local ;;
         dmut_pure t))
    | @stm_match_enum _ E e τ alts =>
      t <- dmut_eval_exp e ;;
      ⨂ K : 𝑬𝑲 E =>
        dmut_assume_formula (formula_eq t (term_enum E K));;
        dmut_exec (alts K)
    | stm_match_tuple e p s =>
      dmut_fail "Err [dmut_exec]: [stm_match_tuple] not implemented"
    | @stm_match_union _ _ _ τ _ =>
      dmut_fail "Err [dmut_exec]: [stm_match_union] not implemented"
    | @stm_match_record _ _ _ _ _ τ _ =>
      dmut_fail "Err [dmut_exec]: [stm_match_record] not implemented"
    | stm_read_register reg =>
      ⨁ t =>
        dmut_consume_chunk (chunk_ptsreg reg t);;
        dmut_produce_chunk (chunk_ptsreg reg t);;
        dmut_pure t
    | stm_write_register reg e =>
      tnew <- dmut_eval_exp e ;;
      ⨁ told =>
        dmut_consume_chunk (chunk_ptsreg reg told);;
        dmut_produce_chunk (chunk_ptsreg reg tnew);;
        dmut_pure tnew
    | stm_bind _ _ =>
      dmut_fail "Err [dmut_exec]: [stm_bind] not supported"
    end.

  Definition dmut_leakcheck {Γ Σ} : DynamicMutator Γ Γ Unit Σ :=
    dmut_get_heap >>= fun _ _ h =>
    match h with
    | nil => dmut_pure tt
    | _   => dmut_fail "Err [dmut_leakcheck]: heap leak"
    end.

  Definition dmut_contract {Δ : Ctx (𝑿 * Ty)} {τ : Ty} (c : SepContract Δ τ) :
    Stm Δ τ -> Outcome (list Obligation) :=
    match c with
    | MkSepContract _ _ Σ δ req result ens =>
      fun s =>
        let mut := (dmut_produce req ;;
                    dmut_exec s      >>= fun Σ1 ζ1 t =>
                    dmut_sub (sub_snoc ζ1 (result,τ) t) (dmut_consume ens) ;;
                    dmut_leakcheck)%dmut in
        let out := mut Σ (sub_id Σ) (symbolicstate_initial δ) in
        outcome_map (fun x => mutator_result_obligations (dmutres_result x)) out
    end.

  Definition ValidContractDynMut (Δ : Ctx (𝑿 * Ty)) (τ : Ty)
    (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    outcome_satisfy (dmut_contract c body) valid_obligations.

End Mutators.
