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
From Coq Require
     Vector.
From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Spec
     Symbolic.Outcome
     Syntax.

From stdpp Require
     base finite list option.

Import CtxNotations.
Import EnvNotations.
Import ListNotations.
Import OutcomeNotations.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.
Delimit Scope dmut_scope with dmut.

Module Mutators
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (assertkit : AssertionKit termkit progkit)
       (symcontractkit : SymbolicContractKit termkit progkit assertkit).

  Export symcontractkit.

  (* The path condition expresses a set of constraints on the logic variables
     that encode the path taken during execution. *)
  Section PathCondition.

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

    Definition inst_formula {Σ} (ι : SymInstance Σ) (fml : Formula Σ) : Prop :=
      match fml with
      | formula_bool t    => is_true (inst (A := Lit ty_bool) ι t)
      | formula_prop ζ P  => uncurry_named P (inst ι ζ)
      | formula_eq t1 t2  => inst ι t1 =  inst ι t2
      | formula_neq t1 t2 => inst ι t1 <> inst ι t2
      end.

    Global Instance sub_formula : Subst Formula :=
      fun Σ1 Σ2 ζ fml =>
        match fml with
        | formula_bool t    => formula_bool (subst ζ t)
        | formula_prop ζ' P => formula_prop (subst ζ ζ') P
        | formula_eq t1 t2  => formula_eq (subst ζ t1) (subst ζ t2)
        | formula_neq t1 t2 => formula_neq (subst ζ t1) (subst ζ t2)
        end.

    Global Instance substlaws_formula : SubstLaws Formula.
    Proof.
      constructor.
      { intros ? []; cbn; f_equal; apply subst_sub_id. }
      { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
    Qed.

    Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
      list (Formula Σ).
    Definition inst_pathcondition {Σ} (ι : SymInstance Σ) (pc : PathCondition Σ) : Prop :=
      List.fold_right (fun fml pc => inst_formula ι fml /\ pc) True pc.

  End PathCondition.

  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Chunk Σ).

  Inductive Obligation : Type :=
  | obligation {Σ} (pc : PathCondition Σ) (fml : Formula Σ).

  Definition valid_obligation : Obligation -> Prop :=
    fun '(obligation pc fml) =>
      ForallNamed (fun ι => all_list (inst_formula ι) pc -> inst_formula ι fml).
  Definition valid_obligations (os : list Obligation) : Prop :=
    all_list valid_obligation os.
  Hint Unfold valid_obligation : core.
  Hint Unfold valid_obligations : core.

  Definition outcome_valid_obligations (os : list Obligation) : Outcome Prop :=
    match os with
    | nil => outcome_block
    | _   => outcome_pure (all_list valid_obligation os)
    end.

  Instance subst_localstore {Γ} : Subst (SymbolicLocalStore Γ) :=
    SubstEnv.
  Instance substlaws_localstore {Γ} : SubstLaws (SymbolicLocalStore Γ) :=
    SubstLawsEnv.

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

    Global Instance subst_symbolicstate {Γ} : Subst (SymbolicState Γ) :=
      fun Σ1 Σ2 ζ '(MkSymbolicState Φ ŝ ĥ) =>
        MkSymbolicState (subst ζ Φ) (subst ζ ŝ) (subst ζ ĥ).
    Global Instance substlaws_symbolicstate {Γ} : SubstLaws (SymbolicState Γ).
    Proof.
      constructor.
      { intros ? []; cbn; f_equal; now rewrite subst_sub_id. }
      { intros ? ? ? ? ? []; cbn; f_equal; now rewrite subst_sub_comp. }
    Qed.

    Definition symbolic_assume_formula {Γ Σ} (fml : Formula Σ) : SymbolicState Γ Σ -> SymbolicState Γ Σ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (fml :: Φ) ŝ ĥ.

  End SymbolicState.

  Section TrySolve.

    (* Check if the given formula is always true or always false for any
       assignments of the logic variables. *)
    Definition try_solve_formula {Σ} (fml : Formula Σ) : option bool :=
      match fml with
      | formula_bool t =>
        match t in Term _ σ return option (Lit σ)
        with
        | term_lit _ b => Some b
        | _            => None
        end
      | formula_prop _ _ => None
      | formula_eq t1 t2 =>
        if Term_eqb t1 t2
        then Some true
        else Term_eqvb t1 t2
      | formula_neq t1 t2 =>
        if Term_eqb t1 t2
        then Some false
        else option_map negb (Term_eqvb t1 t2)
      end.

    Lemma try_solve_formula_spec {Σ} (fml : Formula Σ) (b : bool) :
      try_solve_formula fml = Some b ->
      forall ι, reflect (inst_formula ι fml) b.
    Proof.
      destruct fml; cbn.
      - dependent elimination t; cbn; inversion 1.
        destruct b; constructor; congruence.
      - discriminate.
      - destruct (Term_eqb_spec t1 t2); cbn; intros H ι.
        + inversion H; subst. constructor; congruence.
        + now apply Term_eqvb_spec.
      - destruct (Term_eqb_spec t1 t2); cbn; intros H ι.
        + inversion H; subst. constructor; congruence.
        + destruct (Term_eqvb t1 t2) eqn:?; cbn in *; try discriminate.
          inversion H; subst b. clear H.
          apply (@Term_eqvb_spec _ ι σ) in Heqo.
          inversion Heqo; subst; cbn; constructor; intuition.
    Qed.

  End TrySolve.

  Infix ">=>" := ssrfun.pcomp (at level 80, right associativity).

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
      with eq_dec p1 p2 => {
        match_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) := match_env_eqb ts1 ts2;
        match_chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _)      := fun _ => None
      };
      match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := match_term_eqb t1 t2;
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk_eqb _ _  := fun _ => None.

    Definition extract_chunk_eqb (ce : Chunk Σ) (h : SymbolicHeap Σ) (pc : PathCondition Σ) :
      list (PathCondition Σ * SymbolicHeap Σ) :=
      stdpp.base.omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk_eqb ce cr pc))
        (heap_extractions h).

  End ChunkExtraction.

  Definition EvarEnv (Σe Σr : Ctx (𝑺 * Ty)) : Type := Env (fun b => option (Term Σr (snd b))) Σe.

  Definition create_evarenv (Σe Σr : Ctx (𝑺 * Ty)) : EvarEnv Σe Σr :=
    env_tabulate (fun _ _ => None).

  Section WithEvarEnv.

    Import stdpp.base stdpp.option.

    Context {Σe Σr} (δ : EvarEnv Σe Σr).

    Fixpoint eval_term_evar {σ : Ty} (t : Term Σe σ) {struct t} : option (Term Σr σ) :=
      match t in Term _ σ return option (Term Σr σ) with
      | @term_var _ x _      => δ ‼ x
      | term_lit _ l         => Some (term_lit _ l)
      | term_binop op t1 t2  => t1 ← eval_term_evar t1 ;
                                t2 ← eval_term_evar t2 ;
                                Some (term_binop op t1 t2)
      | term_neg t           => term_neg <$> eval_term_evar t
      | term_not t           => term_not <$> eval_term_evar t
      | term_inl t           => term_inl <$> eval_term_evar t
      | term_inr t           => term_inr <$> eval_term_evar t
      | term_list ts         => term_list <$> traverse_list eval_term_evar ts
      | term_bvec ts         => term_bvec <$> traverse_vector eval_term_evar ts
      | term_tuple ts        => term_tuple <$> traverse_env (@eval_term_evar) ts
      | @term_projtup _ _ t n _ p     => (fun t => term_projtup t n (p:=p)) <$> eval_term_evar t
      | term_union U K t     => term_union U K <$> eval_term_evar t
      | term_record R ts     => term_record R <$> traverse_env (fun b => @eval_term_evar (snd b)) ts
      | term_projrec t rf    => (fun t => term_projrec t rf) <$> eval_term_evar t
      end%exp.

    Section WithMatchTerm.

      Variable match_term : forall {σ}, Term Σe σ -> Term Σr σ -> EvarEnv Σe Σr -> option (EvarEnv Σe Σr).

      Equations(noeqns) match_env'  {σs} (te : Env (Term Σe) σs) (tr : Env (Term Σr) σs) :
        EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
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
      EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
      match_term (@term_var ς σ ςInΣe) tr :=
        fun L =>
          match (L ‼ ς)%exp with
          (* There's already a binding for ς in the evar environment. Make sure
             it corresponds to the term tr. *)
          | Some tr' => if Term_eqb tr' tr then Some L else None
          (* There's no binding for ς in the evar environment. Create a new one by
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
      EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
      match_chunk (chunk_pred p1 ts1) (chunk_pred p2 ts2)
      with eq_dec p1 p2 => {
        match_chunk (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) := match_env ts1 ts2;
        match_chunk (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _)      := fun _ => None
      };
      match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := match_term t1 t2;
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk _ _  := fun _ => None.

    Definition extract_chunk (ce : Chunk Σe) (h : SymbolicHeap Σr) (L : EvarEnv Σe Σr) :
      list (EvarEnv Σe Σr * SymbolicHeap Σr) :=
      omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk ce cr L))
        (heap_extractions h).

    Definition evarenv_to_option_sub : option (Sub Σe Σr) :=
      traverse_env (M := option) (fun b mt => mt) δ.

    Lemma eval_term_evar_refines_sub_term (ζ : Sub Σe Σr) :
      evarenv_to_option_sub = Some ζ ->
      forall σ (t : Term _ σ), eval_term_evar t = Some (sub_term ζ t).
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
      - admit.
      - rewrite IHt; reflexivity.
      - rewrite IHt; reflexivity.
      - admit.
      - rewrite IHt; reflexivity.
    Admitted.

  End WithEvarEnv.

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
    Definition mutator_demonic_list {Γ A Σ} :
      list A -> Mutator Σ Γ Γ A :=
      fix mutator_demonic_list (xs : list A) :=
        match xs with
        | []      => mutator_block
        | x :: [] => mutator_pure x
        | x :: xs => mutator_demonic_binary (mutator_pure x) (mutator_demonic_list xs)
        end.
    Definition mutator_angelic_finite {Γ Σ} (msg : string) A `{finite.Finite A} :
      Mutator Σ Γ Γ A := mutator_angelic_list msg (finite.enum A).
    Definition mutator_demonic_finite {Γ Σ} A `{finite.Finite A} :
      Mutator Σ Γ Γ A := mutator_demonic_list (finite.enum A).

    Global Arguments mutator_bind {_ _ _ _ _ _} _ _ /.
    Global Arguments mutator_bind_right {_ _ _ _ _ _} _ _ /.
    Global Arguments mutator_angelic_finite {_ _} msg%string A {_ _} /.
    Global Arguments mutator_demonic_finite {_ _} A {_ _} /.

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
      fold_right (fun fml m => mutator_assert_formula fml ;; m) (mutator_pure tt) fmls.
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
        k2 <- mutator_demonic_finite (𝑬𝑲 E) ;;
        mutator_assume_formula
          (formula_eq (sub_term ζ k1) (term_enum E k2)) ;;
        mutator_produce ζ (alts k2)
      | asn_sep a1 a2   => mutator_produce ζ a1 *> mutator_produce ζ a2
      | asn_exist ς τ a => mutator_fail
                             "Err [mutator_produce]: case [asn_exist] not implemented"
      end.

    Section MutatorConsumeEvar.
      Context {Σr : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)}.

      Definition mutator_consume_chunk_evar {Σe} (c : Chunk Σe) (L : EvarEnv Σe Σr) : Mutator Σr Γ Γ (EvarEnv Σe Σr) :=
        mutator_get_heap >>= fun h =>
        mutator_angelic_list
          "Err [mutator_consume_chunk_evar]: empty extraction"
          (extract_chunk c h L) >>= fun '(L' , h') =>
        mutator_put_heap h' *> mutator_pure L'.

      Fixpoint mutator_consume_evar {Σe} (asn : Assertion Σe) (L : EvarEnv Σe Σr) : Mutator Σr Γ Γ (EvarEnv Σe Σr) :=
        match asn with
        | asn_bool tb =>
          match eval_term_evar L tb with
          | Some tb' => mutator_assert_term tb' *> mutator_pure L
          | None     => mutator_fail "Err [mutator_consume_evar]: uninstantiated variables when consuming bool assertion"
          end
        | asn_prop P =>
          match evarenv_to_option_sub L with
          | Some ζ => mutator_assert_formula (formula_prop ζ P) *> mutator_pure L
          | None   => mutator_fail "Err [mutator_consume_evar]: uninstantiated variables when consuming prop assertion"
          end
        | asn_chunk c => mutator_consume_chunk_evar c L
        | asn_if tb a1 a2 =>
          match eval_term_evar L tb with
          | Some tb' => (mutator_assume_term tb'            *> mutator_consume_evar a1 L) ⊗
                        (mutator_assume_term (term_not tb') *> mutator_consume_evar a2 L)
          | None     => mutator_fail "Err [mutator_consume_evar]: uninstantiated variables when consuming if assertion"
          end
        | @asn_match_enum _ E k1 alts =>
          match eval_term_evar L k1 with
          | Some k1' => ⨁ k2 : 𝑬𝑲 E =>
            mutator_assert_formula (formula_eq k1' (term_enum E k2)) ;;
            mutator_consume_evar (alts k2) L
          | None => mutator_fail "Err [mutator_consume_evar]: uninstantiated variables when consuming match enum assertion"
          end
        | asn_sep a1 a2 => mutator_consume_evar a1 L >>= mutator_consume_evar a2
        | asn_exist ς τ a =>
          mutator_consume_evar a (env_snoc L _ None) >>= fun La' =>
          match env_unsnoc La' with
          | (L', Some a) => mutator_pure L'
          | _            => mutator_fail "Err [mutator_consume_evar]: uninstantiated existential variable"
          end
        end.

      Definition mutator_assert_term_eq_evar {Σe σ} (te : Term Σe σ) (tr : Term Σr σ) (L : EvarEnv Σe Σr) : Mutator Σr Γ Γ (EvarEnv Σe Σr) :=
        match match_term te tr L with
        | Some L' => mutator_pure L'
        | None    => match eval_term_evar L te with
                     | Some te' => mutator_assert_formula (formula_eq te' tr) *> mutator_pure L
                     | None     => mutator_fail "Err [mutator_consume_evar]: uninstantiated existential variable"
                     end
        end.

      Equations(noeqns) mutator_assert_namedenv_eq_evar {X Σe σs} (te : NamedEnv (X:=X) (Term Σe) σs) (tr : NamedEnv (Term Σr) σs) :
        EvarEnv Σe Σr -> Mutator Σr Γ Γ (EvarEnv Σe Σr) :=
        mutator_assert_namedenv_eq_evar env_nil env_nil := mutator_pure;
        mutator_assert_namedenv_eq_evar (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) :=
          fun L => mutator_assert_namedenv_eq_evar E1 E2 L >>= mutator_assert_term_eq_evar t1 t2.

    End MutatorConsumeEvar.

    Fixpoint mutator_consume {Γ Σ Σ'} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Mutator Σ' Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assert_term (sub_term ζ b)
      | asn_prop P      => mutator_assert_formula (formula_prop ζ P)
      | asn_chunk c     => mutator_consume_chunk (sub_chunk ζ c)
      | asn_if b a1 a2  => (mutator_assume_term (sub_term ζ b)            *> mutator_consume ζ a1) ⊗
                           (mutator_assume_term (sub_term ζ (term_not b)) *> mutator_consume ζ a2)
      | @asn_match_enum _ E k1 alts =>
        k2 <- mutator_angelic_finite
                "Err [mutator_consume]: case asn_match_enum failed"
                (𝑬𝑲 E) ;;
        mutator_assert_formula
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
          K <- mutator_demonic_finite (𝑬𝑲 E) ;;
          mutator_assume_formula (formula_eq t (term_lit (ty_enum E) K)) ;;
          cont K.

    End WithCont.

    (* TODO: The code should be rewritten so this variable can be removed. *)
    Parameter dummy : 𝑺.

    (* Definition mutator_call {Σ Γ Δ τ} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) : Mutator Σ Γ Γ (Term Σ τ) := *)
    (*   match contract with *)
    (*   (* | @sep_contract_unit _ Σe δ req ens => *) *)
    (*   (*   mutator_consume_evar req (create_evarenv Σe Σ) >>= fun L1 => *) *)
    (*   (*   mutator_assert_namedenv_eq_evar δ ts L1 >>= fun L2 => *) *)
    (*   (*   match ghost_env_to_option_sub L2 with *) *)
    (*   (*   | Some ζ => mutator_produce ζ ens *> *) *)
    (*   (*               mutator_pure (term_lit ty_unit tt) *) *)
    (*   (*   | None   => mutator_fail "Err [mutator_exec]: uninstantiated variables after consuming precondition" *) *)
    (*   (*   end *) *)
    (*   | @sep_contract_result_pure _ _ Σe δ result req ens => *)
    (*     mutator_consume_evar req (create_evar_env Σe Σ) >>= fun L1 => *)
    (*     mutator_assert_namedenv_eq_evar δ ts L1 >>= fun L2 => *)
    (*     match ghost_env_to_option_sub L2 with *)
    (*     | Some ζ => mutator_produce ζ ens *> *)
    (*                 mutator_pure (sub_term ζ result) *)
    (*     | None   => mutator_contradiction "Err [mutator_exec]: uninstantiated variables after consuming precondition" *)
    (*     end *)
    (*   | @sep_contract_result _ _ Σ' δ result req ens => mutator_fail "Err [mutator_exec]: stm_call of sep_contract_none_result function not implemented" *)
    (*   | sep_contract_none _ _ => mutator_fail "Err [mutator_exec]: stm_call of sep_contract_none function" *)
    (*   end. *)

    Fixpoint mutator_exec {Σ Γ τ} (s : Stm Γ τ) : Mutator Σ Γ Γ (Term Σ τ) :=
      match s with
      | stm_lit _ l => mutator_pure (term_lit τ l)
      | stm_exp e => mutator_eval_exp e
      | stm_let x τ s k =>
        mutator_exec s >>= fun v =>
        mutator_push_local v *>
        mutator_exec k              <*
        mutator_pop_local
      | stm_block δ k =>
        mutator_pushs_local (lift δ) *>
        mutator_exec k <*
        mutator_pops_local _
      | stm_assign x e => mutator_exec e >>= fun v =>
        mutator_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *>
        mutator_pure v
      | stm_call f es => mutator_fail "Err [mutator_exec]: stm_call not supported"
      | stm_call_external f es => mutator_fail "Err [mutator_exec]: stm_call not supported"
      | stm_call_frame δ' s =>
        δ <- mutator_get_local ;;
        mutator_put_local (lift δ') ;;
        t <- mutator_exec s ;;
        mutator_put_local δ ;;
        mutator_pure t
      | stm_if e s1 s2 =>
        (mutator_assume_exp e ;; mutator_exec s1) ⊗
        (mutator_assume_exp (exp_not e) ;; mutator_exec s2)
      | stm_seq e k => mutator_exec e ;; mutator_exec k
      | stm_assertk e1 _ k =>
        t <- mutator_eval_exp e1 ;;
        mutator_assert_term t ;;
        mutator_exec k
      | stm_fail _ s => mutator_block
      | stm_match_enum E e alts =>
        mutator_eval_exp e >>=
        mutator_exec_match_enum (fun K => mutator_exec (alts K))
      | stm_read_register reg =>
        mutator_consume_chunk_evar (chunk_ptsreg reg (@term_var _ dummy τ inctx_zero)) [None]%arg >>= fun L =>
        match env_unsnoc L with
        | (_ , Some t) => mutator_produce_chunk (chunk_ptsreg reg t) *>
                          mutator_pure t
        (* Extracting the points to chunk should never fail here. Because there is exactly one binding
           in the ghost environment and the chunk matching will always instantiate it. *)
        | _            => mutator_fail "Err [mutator_exec]: You have found a unicorn."
        end
      | stm_write_register reg e =>
        mutator_eval_exp e >>= fun v =>
        mutator_consume_chunk_evar (chunk_ptsreg reg (@term_var _ dummy τ inctx_zero)) [None]%arg ;;
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
      | stm_match_union U e alt__pat alt__rhs =>
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
    Definition dmut_bind {Γ1 Γ2 Γ3 A B Σ}
      (ma : DynamicMutator Γ1 Γ2 A Σ) (f : forall Σ', Sub Σ Σ' -> A Σ' -> DynamicMutator Γ2 Γ3 B Σ') : DynamicMutator Γ1 Γ3 B Σ :=
      fun Σ0 ζ0 s0 =>
        outcome_bind (ma Σ0 ζ0 s0)                            (fun '(MkDynMutResult ζ1 (MkMutResult a s1 w1)) =>
        outcome_bind (f _ (sub_comp ζ0 ζ1) a _ (sub_id _) s1) (fun '(MkDynMutResult ζ2 (MkMutResult b s2 w2)) =>
        outcome_pure (MkDynMutResult (sub_comp ζ1 ζ2) (MkMutResult b s2 (w1 ++ w2))))).
    Definition dmut_join {Γ1 Γ2 Γ3 A Σ} (mm : DynamicMutator Γ1 Γ2 (DynamicMutator Γ2 Γ3 A) Σ) :
      DynamicMutator Γ1 Γ3 A Σ := dmut_bind mm (fun _ _ m => m).

    Definition dmut_sub {Γ1 Γ2 A Σ1 Σ2} (ζ1 : Sub Σ1 Σ2) (p : DynamicMutator Γ1 Γ2 A Σ1) :
      DynamicMutator Γ1 Γ2 A Σ2 := fun Σ3 ζ2 => p _ (sub_comp ζ1 ζ2).
    Global Arguments dmut_sub {_ _ _ _ _} ζ1 p.
    Definition dmut_bind_right {Γ1 Γ2 Γ3 A B Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) : DynamicMutator Γ1 Γ3 B Σ :=
      dmut_bind ma (fun _ ζ _ => dmut_sub ζ mb).
    Definition dmut_bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} {Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) : DynamicMutator Γ1 Γ3 A Σ :=
      dmut_bind ma (fun _ ζ a => dmut_bind_right (dmut_sub ζ mb) (dmut_pure a)) .
    Definition dmut_fmap {Γ1 Γ2 Σ A B} `{Subst A, Subst B}
      (ma : DynamicMutator Γ1 Γ2 A Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ') :
      DynamicMutator Γ1 Γ2 B Σ :=
      dmut_bind ma (fun Σ1 ζ1 a => dmut_pure (f Σ1 ζ1 a)).
    Definition dmut_fmap2 {Γ1 Γ2 Γ3 Σ A B C} `{Subst A, Subst B, Subst C}
      (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ' -> C Σ') :
      DynamicMutator Γ1 Γ3 C Σ :=
      dmut_bind ma (fun Σ1 ζ1 a =>
        dmut_bind (dmut_sub ζ1 mb) (fun Σ2 ζ2 b =>
          dmut_pure (f Σ2 (sub_comp ζ1 ζ2) (subst ζ2 a) b))).
    Definition dmut_pair {Γ1 Γ2 Γ3 Σ A B} `{Subst A, Subst B}
      (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) :
      DynamicMutator Γ1 Γ3 (fun Σ => A Σ * B Σ)%type Σ :=
      dmut_fmap2 ma mb (fun _ _ => pair).

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
    Definition dmut_angelic_list {Γ1 Γ2 A Σ} (msg : string) :
      list (DynamicMutator Γ1 Γ2 A Σ) -> DynamicMutator Γ1 Γ2 A Σ :=
      fix dmut_angelic_list (xs : list (DynamicMutator Γ1 Γ2 A Σ)) :=
        match xs with
        | []      => dmut_contradiction msg
        | x :: [] => x
        | x :: xs => dmut_angelic_binary x (dmut_angelic_list xs)
        end.
    Definition dmut_demonic_list {Γ1 Γ2 A Σ} :
      list (DynamicMutator Γ1 Γ2 A Σ) -> DynamicMutator Γ1 Γ2 A Σ :=
      fix dmut_demonic_list (xs : list (DynamicMutator Γ1 Γ2 A Σ)) :=
        match xs with
        | []      => dmut_block
        | x :: [] => x
        | x :: xs => dmut_demonic_binary x (dmut_demonic_list xs)
        end.

    Definition dmut_angelic_finite {Γ A} F `{finite.Finite F, Subst A} {Σ}
               (cont : F -> DynamicMutator Γ Γ A Σ) :
      DynamicMutator Γ Γ A Σ :=
      dmut_angelic_list "Err [dmut_angelic_finite] failed" (map cont (finite.enum F)).
    Definition dmut_demonic_finite {Γ A} F `{finite.Finite F, Subst A} {Σ}
               (cont : F -> DynamicMutator Γ Γ A Σ) :
      DynamicMutator Γ Γ A Σ :=
      dmut_demonic_list (map cont (finite.enum F)).
    Global Arguments dmut_angelic_finite {_ _} _ {_ _ _ _} _.
    Global Arguments dmut_demonic_finite {_ _} _ {_ _ _ _} _.

    Definition dmut_fresh {Γ A Σ} b (ma : DynamicMutator Γ Γ A (Σ ▻ b)) : DynamicMutator Γ Γ A Σ :=
      fun Σ1 ζ1 s1 =>
        outcome_map
          (fun '(MkDynMutResult ζ r) => MkDynMutResult (sub_comp sub_wk1 ζ) r)
          (ma _ (sub_up1 ζ1) (wk1 s1)).
    Global Arguments dmut_fresh {_ _ _} _ _.
    Definition dmut_freshtermvar {Γ Σ σ} (x : 𝑺) : DynamicMutator Γ Γ (fun Σ => Term Σ σ) Σ :=
      dmut_fresh (x,σ) (dmut_pure (@term_var _ _ _ inctx_zero)).
    Global Arguments dmut_freshtermvar {_ _ _} _.

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
          (m _ (sub_up1 ζ1) tt (wk1 s1)).
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

  Fixpoint dmut_freshen_tuplepat' {σs Δ} (p : TuplePat σs Δ) {Γ Σ} :
    DynamicMutator Γ Γ (fun Σ => Env (Term Σ) σs * NamedEnv (Term Σ) Δ)%type Σ :=
    match p with
    | tuplepat_nil =>
      dmut_pure (env_nil, env_nil)
    | tuplepat_snoc p x =>
      dmut_fmap2
        (dmut_freshen_tuplepat' p)
        (dmut_freshtermvar (𝑿to𝑺 x))
        (fun _ _ '(ts__σs, ts__Δ) t__x => (env_snoc ts__σs _ t__x, env_snoc ts__Δ (x,_) t__x))
    end.

  Definition dmut_freshen_tuplepat {σs Δ} (p : TuplePat σs Δ) {Γ Σ} :
    DynamicMutator Γ Γ (fun Σ => Term Σ (ty_tuple σs) * NamedEnv (Term Σ) Δ)%type Σ :=
    dmut_fmap
      (dmut_freshen_tuplepat' p)
      (fun _ _ '(t__σs, t__Δ) => (term_tuple t__σs, t__Δ)).

  Fixpoint dmut_freshen_recordpat' {σs Δ} (p : RecordPat σs Δ) {Γ Σ} :
    DynamicMutator Γ Γ (fun Σ => NamedEnv (Term Σ) σs * NamedEnv (Term Σ) Δ)%type Σ :=
    match p with
    | recordpat_nil =>
      dmut_pure (env_nil, env_nil)
    | recordpat_snoc p rf x =>
      dmut_fmap2
        (dmut_freshen_recordpat' p)
        (dmut_freshtermvar (𝑿to𝑺 x))
        (fun _ _ '(ts__σs, ts__Δ) t__x => (env_snoc ts__σs (rf,_) t__x, env_snoc ts__Δ (x,_) t__x))
    end.

  Definition dmut_freshen_recordpat {R Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) {Γ Σ} :
    DynamicMutator Γ Γ (fun Σ => Term Σ (ty_record R) * NamedEnv (Term Σ) Δ)%type Σ :=
    dmut_fmap
      (dmut_freshen_recordpat' p)
      (fun _ _ '(t__σs, t__Δ) => (term_record R t__σs, t__Δ)).

  Definition dmut_freshen_pattern {Γ Σ Δ σ} (p : Pattern Δ σ) :
    DynamicMutator Γ Γ (fun Σ => Term Σ σ * NamedEnv (Term Σ) Δ)%type Σ :=
    match p with
    | pat_var x =>
      dmut_fmap
        (dmut_freshtermvar (𝑿to𝑺 x))
        (fun _ _ t => (t,[t]%arg))
    | pat_unit =>
      dmut_pure (term_lit ty_unit tt,env_nil)
    | pat_pair x y =>
      dmut_fmap2
        (dmut_freshtermvar (𝑿to𝑺 x))
        (dmut_freshtermvar (𝑿to𝑺 y))
        (fun _ _ t__x t__y => (term_binop binop_pair t__x t__y, [t__x,t__y]%arg))
    | pat_tuple p =>
      dmut_freshen_tuplepat p
    | pat_record p =>
      dmut_freshen_recordpat p
    end.

  Definition dmutres_assume_eq {Γ Σ σ} (s : SymbolicState Γ Σ) (t1 t2 : Term Σ σ) :
    option (DynamicMutatorResult Γ Unit Σ) :=
    match t1 with
    | @term_var _ ς σ ςInΣ =>
      fun t2 : Term Σ σ =>
        match occurs_check ςInΣ t2 with
        | Some t =>
          let ζ := sub_single ςInΣ t in
          Some
            {|
              dmutres_context := Σ - (ς,σ);
              dmutres_substitution := ζ;
              dmutres_result :=
                {| mutator_result_value := tt;
                   mutator_result_state := subst ζ s;
                   mutator_result_obligations := []
                |}
            |}
        | None => None
        end
    | _ => fun _ => None
    end t2.

  Definition dmut_try_assume_eq {Γ Σ} (s : SymbolicState Γ Σ) (fml : Formula Σ) :
    option (DynamicMutatorResult Γ Unit Σ) :=
    match fml with
    | formula_eq t1 t2 =>
      match dmutres_assume_eq s t1 t2 with
      | Some r => Some r
      | None => dmutres_assume_eq s t2 t1
      end
    | _ => None
    end.

  (* Add the provided formula to the path condition. *)
  Definition dmut_assume_formula {Γ Σ} (fml : Formula Σ) : DynamicMutator Γ Γ Unit Σ :=
    fun Σ1 ζ1 s1 =>
      let fml := sub_formula ζ1 fml in
      match try_solve_formula fml with
      | Some true =>
        (* The formula is always true. Just skip it. *)
        outcome_pure
          {| dmutres_context := Σ1;
             dmutres_substitution := sub_id Σ1;
             dmutres_result :=
               {|
                 mutator_result_value := tt;
                 mutator_result_state := s1;
                 mutator_result_obligations := []
               |}
          |}
      | Some false =>
        (* The formula is always false, so the path condition with it would become
           inconsistent. Prune this path. *)
        outcome_block
      | None =>
        outcome_pure
          (* Check if the formula is an equally that can be propagated. *)
          match dmut_try_assume_eq s1 fml with
          | Some r => r
          | None =>
            (* If everything fails, we simply add the formula to the path
               condition verbatim. *)
            {| dmutres_context := Σ1;
               dmutres_substitution := sub_id Σ1;
               dmutres_result :=
                 {|
                   mutator_result_value := tt;
                   mutator_result_state := symbolic_assume_formula fml s1;
                   mutator_result_obligations := [] |}
            |}
          end
      end.

  Definition dmut_assume_term {Γ Σ} (t : Term Σ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_assume_formula (formula_bool t).
  Definition dmut_assume_exp {Γ Σ} (e : Exp Γ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_eval_exp e >>= fun _ _ => dmut_assume_term.
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

  Definition dmut_leakcheck {Γ Σ} : DynamicMutator Γ Γ Unit Σ :=
    dmut_get_heap >>= fun _ _ h =>
    match h with
    | nil => dmut_pure tt
    | _   => dmut_fail "Err [dmut_leakcheck]: heap leak"
    end.

  Module DynMutV1.

    Fixpoint dmut_produce {Γ Σ} (asn : Assertion Σ) : DynamicMutator Γ Γ Unit Σ :=
      match asn with
      | asn_bool b      => dmut_assume_term b
      | asn_prop P      => dmut_assume_prop P
      | asn_chunk c     => dmut_produce_chunk c
      | asn_if b a1 a2  => (dmut_assume_term b ;; dmut_produce a1) ⊗
                           (dmut_assume_term (term_not b) ;; dmut_produce a2)
      | asn_match_enum E k1 alts =>
        dmut_demonic_finite
          (𝑬𝑲 E)
          (fun k2 =>
             dmut_assume_formula (formula_eq k1 (term_enum E k2)) ;;
             dmut_produce (alts k2))
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
        dmut_angelic_finite
          (𝑬𝑲 E)
          (fun k2 =>
             dmut_assert_formula (formula_eq k1 (term_enum E k2)) ;;
             dmut_consume (alts k2))
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

    Fixpoint dmut_exec {Γ τ Σ} (s : Stm Γ τ) {struct s} :
      DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σ :=
      match s with
      | stm_lit _ l => dmut_pure (term_lit τ l)
      | stm_exp e => dmut_eval_exp e
      | stm_let x τ s1 s2 =>
        t1 <- dmut_exec s1 ;;
        dmut_push_local t1 ;;
        t2 <- dmut_exec s2 ;;
        dmut_pop_local ;;
        dmut_pure t2
      | stm_block δ s =>
        dmut_pushs_local (lift δ) ;;
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
      | stm_call_frame δ s =>
        δr <- dmut_get_local ;;
        dmut_put_local (lift δ) ;;
        dmut_bind_left (dmut_exec s) (dmut_put_local δr)
      | stm_call_external f es =>
        ts <- dmut_eval_exps es ;;
        dmut_call (CEnvEx f) ts
      | stm_if e s1 s2 =>
          (dmut_assume_exp e ;; dmut_exec s1) ⊗
          (dmut_assume_exp (exp_not e) ;; dmut_exec s2)
      | stm_seq s1 s2 => dmut_exec s1 ;; dmut_exec s2
      | stm_assertk e1 _ k =>
        t <- dmut_eval_exp e1 ;;
        dmut_assert_term t ;;
        dmut_exec k
      | stm_fail _ _ =>
        dmut_block
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
      | stm_match_enum E e alts =>
        t <- dmut_eval_exp e ;;
        ⨂ K : 𝑬𝑲 E =>
          dmut_assume_formula (formula_eq t (term_enum E K));;
          dmut_exec (alts K)
      | stm_match_tuple e p s =>
        dmut_fail "Err [dmut_exec]: [stm_match_tuple] not implemented"
      | stm_match_union U e alt__ctx alt__pat =>
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

  End DynMutV1.

  Module DynMutV2.

    Section CallerContext.

      Context {Σr : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)}.

      Definition dmut_consume_chunk_evar {Σe} (c : Chunk Σe) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr.
      Proof.
        apply dmut_lift.
        intros Σ1 ζ1.
        apply mutator_consume_chunk_evar.
        exact c.
        refine (env_map _ L).
        intros ?.
        apply option_map.
        exact (sub_term ζ1).
      Defined.

      Definition dmut_consume_evar {Σe} (asn : Assertion Σe) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr.
      Proof.
        apply dmut_lift.
        intros Σ1 ζ1.
        apply mutator_consume_evar.
        exact asn.
        refine (env_map _ L).
        intros ?.
        apply option_map.
        exact (sub_term ζ1).
      Defined.

      Definition dmut_assert_term_eq_evar {Σe σ} (te : Term Σe σ) (tr : Term Σr σ) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr.
      Proof.
        apply dmut_lift.
        intros Σ1 ζ1.
        apply (mutator_assert_term_eq_evar te (sub_term ζ1 tr)).
        refine (env_map _ L).
        intros ?.
        apply option_map.
        exact (sub_term ζ1).
      Defined.

      Definition dmut_assert_namedenv_eq_evar {X Σe σs} (te : NamedEnv (X:=X) (Term Σe) σs) (tr : NamedEnv (Term Σr) σs) :
        EvarEnv Σe Σr -> DynamicMutator Γ Γ (EvarEnv Σe) Σr.
      Proof.
        intros L.
        apply dmut_lift.
        intros Σ1 ζ1.
        apply (mutator_assert_namedenv_eq_evar te).
        refine (env_map _ tr).
        intros ?.
        exact (sub_term ζ1).
        refine (env_map _ L).
        intros ?.
        apply option_map.
        exact (sub_term ζ1).
      Defined.

    End CallerContext.

    Definition dmut_call_evar {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σr :=
      match contract with
      | MkSepContract _ _ Σe δ req result ens =>
         dmut_consume_evar req (create_evarenv Σe Σr) >>= fun Σr1 ζ1 E1 =>
         dmut_assert_namedenv_eq_evar δ (env_map (fun _ => sub_term ζ1) ts) E1 >>= fun Σr2 ζ2 E2 =>
         match evarenv_to_option_sub E2 with
         | Some ξ => dmut_sub ξ (dmut_fresh (result,τ) (DynMutV1.dmut_produce ens ;; dmut_pure (@term_var _ result _ inctx_zero)))
         | None => dmut_fail "Err [dmut_call_evar]: uninstantiated variables after consuming precondition"
         end
      end.

    Fixpoint dmut_exec_evar {Γ τ Σ} (s : Stm Γ τ) {struct s} :
      DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σ :=
      match s with
      | stm_lit _ l => dmut_pure (term_lit τ l)
      | stm_exp e => dmut_eval_exp e
      | stm_let x τ s1 s2 =>
        t1 <- dmut_exec_evar s1 ;;
        dmut_push_local t1 ;;
        t2 <- dmut_exec_evar s2 ;;
        dmut_pop_local ;;
        dmut_pure t2
      | stm_block δ s =>
        dmut_pushs_local (lift δ) ;;
        t <- dmut_exec_evar s ;;
        dmut_pops_local _ ;;
        dmut_pure t
      | stm_assign x s =>
        t <- dmut_exec_evar s ;;
        dmut_modify_local (fun _ ζ δ => δ ⟪ x ↦ subst ζ t ⟫)%env ;;
        dmut_pure t
      | stm_call f es =>
        match CEnv f with
        | Some c =>
          ts <- dmut_eval_exps es ;;
          dmut_call_evar c ts
        | None   => dmut_fail "Err [dmut_exec_evar]: Function call without contract"
        end
      | stm_call_frame δ s =>
        δr <- dmut_get_local ;;
        dmut_put_local (lift δ) ;;
        dmut_bind_left (dmut_exec_evar s) (dmut_put_local δr)
      | stm_call_external f es =>
        ts <- dmut_eval_exps es ;;
        dmut_call_evar (CEnvEx f) ts
      | stm_if e s1 s2 =>
        t__sc <- dmut_eval_exp e ;;
        match term_get_lit t__sc with
        | Some b =>
          if b
          then dmut_exec_evar s1
          else dmut_exec_evar s2
        | None =>
          (dmut_assume_term t__sc ;; dmut_exec_evar s1) ⊗
          (dmut_assume_term (term_not t__sc) ;; dmut_exec_evar s2)
        end
      | stm_seq s1 s2 => dmut_exec_evar s1 ;; dmut_exec_evar s2
      | stm_assertk e1 _ k =>
        t <- dmut_eval_exp e1 ;;
        dmut_assert_term t ;;
        dmut_exec_evar k
      | stm_fail _ _ =>
        dmut_block
      | stm_match_list e s1 xh xt s2 =>
        t <- dmut_eval_exp e ;;
        (dmut_assume_formula
           (formula_eq t (term_lit (ty_list _) nil));;
         dmut_exec_evar s1) ⊗
        (dmut_fresh
           (𝑿to𝑺 xh,_) (dmut_fresh (𝑿to𝑺 xt,_)
           (dmut_assume_formula
              (formula_eq (sub_term (sub_comp sub_wk1 sub_wk1) t)
                          (term_binop binop_cons (@term_var _ _ _ (inctx_succ inctx_zero)) (@term_var _ _ _ inctx_zero)));;
            dmut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
            dmut_push_local (@term_var _ _ _ inctx_zero);;
            t2 <- dmut_exec_evar s2 ;;
            dmut_pop_local ;;
            dmut_pop_local ;;
            dmut_pure t2)))
      | stm_match_sum e xinl s1 xinr s2 =>
        t__sc <- dmut_eval_exp e ;;
        match term_get_sum t__sc with
        | Some (inl t) =>
          dmut_push_local t;;
          dmut_bind_left (dmut_exec_evar s1) dmut_pop_local
        | Some (inr t) =>
          dmut_push_local t;;
          dmut_bind_left (dmut_exec_evar s2) dmut_pop_local
        | None =>
          dmut_fresh _
            (dmut_assume_formula
               (formula_eq (sub_term sub_wk1 t__sc) (term_inl (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero)));;
             dmut_push_local (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero);;
             dmut_bind_left (dmut_exec_evar s1) dmut_pop_local) ⊗
          dmut_fresh _
            (dmut_assume_formula
               (formula_eq (sub_term sub_wk1 t__sc) (term_inr (@term_var _ (𝑿to𝑺 xinr) _ inctx_zero)));;
             dmut_push_local (@term_var _ (𝑿to𝑺 xinr) _ inctx_zero);;
             dmut_bind_left (dmut_exec_evar s2) dmut_pop_local)
        end
      | stm_match_pair e xl xr s =>
        t__sc <- dmut_eval_exp e ;;
        match term_get_pair t__sc with
        | Some (t1,t2) =>
          dmut_push_local t1;;
          dmut_push_local t2;;
          t <- dmut_exec_evar s ;;
          dmut_pop_local ;;
          dmut_pop_local ;;
          dmut_pure t
        | None =>
          dmut_fresh (𝑿to𝑺 xl,_) (dmut_fresh (𝑿to𝑺 xr,_)
            (dmut_assume_formula
               (formula_eq
                  (sub_term (sub_comp sub_wk1 sub_wk1) t__sc)
                  (term_binop binop_pair (@term_var _ (𝑿to𝑺 xl) _ (inctx_succ inctx_zero)) (@term_var _ (𝑿to𝑺 xr) _ inctx_zero)));;
             dmut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
             dmut_push_local (@term_var _ _ _ inctx_zero);;
             t <- dmut_exec_evar s ;;
             dmut_pop_local ;;
             dmut_pop_local ;;
             dmut_pure t))
        end
      | stm_match_enum E e alts =>
        t__sc <- dmut_eval_exp e ;;
        match term_get_lit t__sc with
        | Some K => dmut_exec_evar (alts K)
        | None =>
          dmut_demonic_finite
            (𝑬𝑲 E)
            (fun K =>
               dmut_assume_formula (formula_eq t__sc (term_enum E K));;
               dmut_exec_evar (alts K))
        end
      | stm_match_tuple e p s =>
        ts <- dmut_pair (dmut_eval_exp e) (dmut_freshen_tuplepat p) ;;
        let '(t__sc,(t__p,t__Δ)) := ts in
        dmut_assume_formula (formula_eq t__sc t__p) ;;
        dmut_pushs_local t__Δ ;;
        t <- dmut_exec_evar s ;;
        dmut_pops_local _ ;;
        dmut_pure t
      | stm_match_union U e alt__pat alt__rhs =>
        t__sc <- dmut_eval_exp e ;;
        match term_get_union t__sc with
        | Some (existT K t__field) =>
          dmut_freshen_pattern (alt__pat K) >>= (fun Σ2 ζ2 '(t__pat, δ__Δ) =>
            dmut_assume_formula (formula_eq t__pat (sub_term ζ2 t__field));;
            dmut_pushs_local δ__Δ;;
            t__rhs <- dmut_sub ζ2 (dmut_exec_evar (alt__rhs K));;
            dmut_pops_local _;;
            dmut_pure t__rhs)
        | None =>
          dmut_demonic_finite
            (𝑼𝑲 U)
            (fun K =>
               dmut_freshen_pattern (alt__pat K) >>= (fun Σ2 ζ2 '(t__pat, δ__Δ) =>
               dmut_assume_formula (formula_eq (sub_term ζ2 t__sc) (term_union U K t__pat));;
               dmut_pushs_local δ__Δ;;
               t__rhs <- dmut_sub ζ2 (dmut_exec_evar (alt__rhs K));;
               dmut_pops_local _;;
               dmut_pure t__rhs))
        end
      | stm_match_record R e p s =>
        ts <- dmut_pair (dmut_eval_exp e) (dmut_freshen_recordpat p) ;;
        let '(t__sc,(t__p,t__Δ)) := ts in
        dmut_assume_formula (formula_eq t__sc t__p) ;;
        dmut_pushs_local t__Δ ;;
        t <- dmut_exec_evar s ;;
        dmut_pops_local _ ;;
        dmut_pure t
      | stm_read_register reg =>
        dmut_consume_chunk_evar (chunk_ptsreg reg (@term_var [(dummy,_)] dummy _ inctx_zero)) [None]%arg >>= fun Σ1 _ E1 =>
        match snd (env_unsnoc E1) with
        | Some t => dmut_produce_chunk (chunk_ptsreg reg t) ;; dmut_pure t
        (* Extracting the points to chunk should never fail here. Because there is exactly one binding
           in the ghost environment and the chunk matching will always instantiate it. *)
        | None => dmut_fail "Err [dmut_exec_evar]: You have found a unicorn."
        end
      | stm_write_register reg e =>
        tnew <- dmut_eval_exp e ;;
        dmut_consume_chunk_evar (chunk_ptsreg reg (@term_var _ dummy _ inctx_zero)) [None]%arg ;;
        dmut_produce_chunk (chunk_ptsreg reg tnew) ;;
        dmut_pure tnew
      | stm_bind _ _ =>
        dmut_fail "Err [dmut_exec_evar]: [stm_bind] not supported"
      end.

    Definition dmut_contract_evar {Δ : Ctx (𝑿 * Ty)} {τ : Ty} (c : SepContract Δ τ) :
      Stm Δ τ -> Outcome (list Obligation) :=
      match c with
      | MkSepContract _ _ Σ δ req result ens =>
        fun s =>
          let mut := (DynMutV1.dmut_produce req ;;
                      dmut_exec_evar s      >>= fun Σ1 ζ1 t =>
                      dmut_sub (sub_snoc ζ1 (result,τ) t) (DynMutV1.dmut_consume ens) ;;
                      dmut_leakcheck)%dmut in
          let out := mut Σ (sub_id Σ) (symbolicstate_initial δ) in
          outcome_map (fun x => mutator_result_obligations (dmutres_result x)) out
      end.

    Definition ValidContractDynMut (Δ : Ctx (𝑿 * Ty)) (τ : Ty)
               (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      outcome_satisfy
        (outcome_bind (dmut_contract_evar c body) outcome_valid_obligations)
        (fun P => P).

    Definition ValidContractDynMutReflect (Δ : Ctx (𝑿 * Ty)) (τ : Ty)
               (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      is_true
        (outcome_ok
           (outcome_bind
              (dmut_contract_evar c body)
              outcome_valid_obligations)).

    Lemma dynmutevarreflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractDynMutReflect c body ->
      ValidContractDynMut c body.
    Proof. apply outcome_ok_spec. Qed.

  End DynMutV2.

End Mutators.
