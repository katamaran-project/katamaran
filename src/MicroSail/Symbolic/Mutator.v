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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Lists.List
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Relations.Relation_Definitions
     Relations.Relation_Operators
     Strings.String
     ZArith.ZArith.
From Coq Require
     Vector.
From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Spec
     SemiConcrete.Outcome
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

    Import stdpp.base.

    Global Instance OccursCheckFormula : OccursCheck Formula :=
      fun Σ x xIn fml =>
            match fml with
            | formula_bool t    => option_map formula_bool (occurs_check xIn t)
            | formula_prop ζ P  => option_map (fun ζ' => formula_prop ζ' P) (occurs_check xIn ζ)
            | formula_eq t1 t2  => t1' ← occurs_check xIn t1;
                                   t2' ← occurs_check xIn t2;
                                   Some (formula_eq t1' t2')
            | formula_neq t1 t2 => t1' ← occurs_check xIn t1;
                                   t2' ← occurs_check xIn t2;
                                   Some (formula_neq t1' t2')
              end.

    Global Instance OccursCheckLawsFormula : OccursCheckLaws Formula.
    Proof.
      constructor.
      - intros ? ? ? ? []; cbn; unfold mbind, option.option_bind;
          now rewrite ?occurs_check_shift.
      - intros ? ? ? [] fml' Heq; cbn in *.
        + apply option_map_eq_some' in Heq; destruct_conjs; subst; cbn.
          f_equal. now apply (occurs_check_sound (T := fun Σ => Term Σ _)).
        + apply option_map_eq_some' in Heq; destruct_conjs; subst; cbn.
          f_equal. now apply occurs_check_sound.
        + apply option_bind_eq_some in Heq; destruct Heq as (a & Heq1 & Heq2).
          apply option_bind_eq_some in Heq2; destruct Heq2 as (b & Heq2 & Heq3).
          apply noConfusion_inv in Heq3; cbn in Heq3; subst fml'; cbn.
          f_equal; now apply (occurs_check_sound (T := fun Σ => Term Σ _)).
        + apply option_bind_eq_some in Heq; destruct Heq as (a & Heq1 & Heq2).
          apply option_bind_eq_some in Heq2; destruct Heq2 as (b & Heq2 & Heq3).
          apply noConfusion_inv in Heq3; cbn in Heq3; subst fml'; cbn.
          f_equal; now apply (occurs_check_sound (T := fun Σ => Term Σ _)).
    Qed.

    Definition PathCondition (Σ : LCtx) : Type :=
      list (Formula Σ).
    Fixpoint fold_right1 {A R} (cns : A -> R -> R) (sing : A -> R) (v : A) (l : list A) : R :=
      match l with
        nil => sing v
      | cons v' vs => cns v (fold_right1 cns sing v' vs)
      end.
    Fixpoint fold_right10 {A R} (cns : A -> R -> R) (sing : A -> R) (nl : R) (l : list A) : R :=
      match l with
        nil => nl
      | cons v vs => fold_right1 cns sing v vs
      end.

    Lemma fold_right_1_10 {A} {cns : A -> Prop -> Prop} {sing : A -> Prop} {nl : Prop}
          (consNilIffSing : forall v, sing v <-> cns v nl)
          (v : A) (l : list A) :
          fold_right1 cns sing v l <-> cns v (fold_right10 cns sing nl l).
    Proof.
      induction l; cbn; auto.
    Qed.

    Lemma fold_right_1_10_prop {A} {P : A -> Prop}
          (v : A) (l : list A) :
          fold_right1 (fun v acc => P v /\ acc) P v l <-> P v /\ (fold_right10 (fun v acc => P v /\ acc) P True l).
    Proof.
      refine (fold_right_1_10 _ v l).
      intuition.
    Qed.

    (* Note: we use fold_right10 instead of fold_right to make inst_lift hold. *)
    Definition inst_pathcondition {Σ} (ι : SymInstance Σ) (pc : PathCondition Σ) : Prop :=
      fold_right10 (fun fml pc => inst ι fml /\ pc) (fun fml => inst ι fml) True pc.
    Global Arguments inst_pathcondition : simpl never.

    Lemma inst_subst1 {Σ Σ' } (ζ : Sub Σ Σ') (ι : SymInstance Σ') (f : Formula Σ) (pc : list (Formula Σ)) :
      fold_right1 (fun fml pc => inst ι fml /\ pc) (fun fml => inst ι fml) (subst ζ f) (subst ζ pc) =
      fold_right1 (fun fml pc => inst (inst ι ζ) fml /\ pc) (fun fml => inst (inst ι ζ) fml) f pc.
    Proof.
      revert f.
      induction pc; intros f; cbn.
      - apply inst_subst.
      - f_equal.
        + apply inst_subst.
        + apply IHpc.
    Qed.

    Lemma inst_subst10 {Σ Σ' } (ζ : Sub Σ Σ') (ι : SymInstance Σ') (pc : list (Formula Σ)) :
      fold_right10 (fun fml pc => inst ι fml /\ pc) (fun fml => inst ι fml) True (subst ζ pc) =
      fold_right10 (fun fml pc => inst (inst ι ζ) fml /\ pc) (fun fml => inst (inst ι ζ) fml) True pc.
    Proof.
      destruct pc.
      - reflexivity.
      - apply inst_subst1.
    Qed.

    Global Instance instantiate_pathcondition : Inst PathCondition Prop :=
      {| inst Σ := inst_pathcondition;
         lift Σ P := cons (lift P : Formula Σ) nil
      |}.

    Global Instance instantiate_pathcondition_laws : InstLaws PathCondition Prop.
    Proof.
      constructor.
      - reflexivity.
      - intros Σ Σ' ζ ι pc.
        eapply inst_subst10.
    Qed.

    Lemma inst_pathcondition_cons {Σ} (ι : SymInstance Σ) (f : Formula Σ) (pc : PathCondition Σ) :
      inst ι (cons f pc) <-> inst ι f /\ inst ι pc.
    Proof.
      apply fold_right_1_10_prop.
    Qed.

  End PathCondition.

  (* UNUSED *)
  Section Rewrite.

    Class Rewrite (T : LCtx -> Type) : Type :=
      par_rewrite_once : forall Σ, PathCondition Σ -> T Σ -> T Σ -> Prop.

    Definition rewrite {T} `{Rewrite T} {Σ} (pc : PathCondition Σ) : relation (T Σ) :=
      clos_refl_sym_trans (T Σ) (par_rewrite_once pc).

    Inductive RewriteTerm {Σ} (pc : PathCondition Σ) : forall σ, Term Σ σ -> Term Σ σ -> Prop :=
    | rew_eq
        {σ} {s t : Term Σ σ} :
        In (formula_eq s t) pc ->
        RewriteTerm pc s t
    | rew_refl_var (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς ∶ σ) Σ} :
        RewriteTerm pc (term_var ς) (term_var ς)
    | rew_refl_lit (σ : Ty) (l : Lit σ) :
        RewriteTerm pc (term_lit σ l) (term_lit σ l)
    | rew_cong_binop
        {σ1 σ2 σ3 : Ty}
        (op : BinOp σ1 σ2 σ3) (s1 t1 : Term Σ σ1) (s2 t2 : Term Σ σ2) :
        RewriteTerm pc s1 t1 -> RewriteTerm pc s2 t2 ->
        RewriteTerm pc (term_binop op s1 s2) (term_binop op t1 t2)
    | rew_cong_neg
        (s t : Term Σ ty_int) :
        RewriteTerm pc s t ->
        RewriteTerm pc (term_neg s) (term_neg t)
    | rew_cong_not
        (s t : Term Σ ty_bool) :
        RewriteTerm pc s t ->
        RewriteTerm pc (term_not s) (term_not t)
    | rew_cong_inl
        {σ1 σ2 : Ty} (s t : Term Σ σ1) :
        RewriteTerm pc s t ->
        RewriteTerm pc (@term_inl _ σ1 σ2 s) (term_inl t)
    | rew_cong_inr
        {σ1 σ2 : Ty} (s t : Term Σ σ2) :
        RewriteTerm pc s t ->
        RewriteTerm pc (@term_inr _ σ1 σ2 s) (term_inr t)
    | rew_cong_list
        {σ} (ss ts : list (Term Σ σ)) :
        (forall n s t, nth_error ss n = Some s -> nth_error ts n = Some t -> RewriteTerm pc s t) ->
        RewriteTerm pc (term_list ss) (term_list ts)
    | rew_cong_bvec
        {n} (ss ts : Vector.t (Term Σ ty_bit) n) :
        (forall n, RewriteTerm pc (Vector.nth ss n) (Vector.nth ts n)) ->
        RewriteTerm pc (term_bvec ss) (term_bvec ts)
    | rew_cong_tuple
        {σs : Ctx Ty} (ss ts : Env (Term Σ) σs) :
        (forall σ (σIn : σ ∈ σs), RewriteTerm pc (env_lookup ss σIn) (env_lookup ts σIn)) ->
        RewriteTerm pc (term_tuple ss) (term_tuple ts)
    | rew_cong_projtup
        {σs : Ctx Ty} (s t : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
        {p : ctx_nth_is σs n σ} :
        RewriteTerm pc (@term_projtup _ _ s n σ p) (@term_projtup _ _ t n σ p)
    | rew_cong_union
        {U : 𝑼} (K : 𝑼𝑲 U) (s t : Term Σ (𝑼𝑲_Ty K)) :
        RewriteTerm pc s t ->
        RewriteTerm pc (term_union U K s) (term_union U K t)
    | rew_cong_record
        {R : 𝑹} (ss ts : NamedEnv (Term Σ) (𝑹𝑭_Ty R)) :
        (forall rf σ (rfIn : rf :: σ ∈ (𝑹𝑭_Ty R)), RewriteTerm pc (env_lookup ss rfIn) (env_lookup ts rfIn)) ->
        RewriteTerm pc (term_record R ss) (term_record R ts).

    Instance rew_term {σ} : Rewrite (fun Σ => Term Σ σ) :=
      fun Σ pc => @RewriteTerm Σ pc σ.

  End Rewrite.

  Instance subst_localstore {Γ} : Subst (SymbolicLocalStore Γ) :=
    SubstEnv.
  Instance substlaws_localstore {Γ} : SubstLaws (SymbolicLocalStore Γ) :=
    SubstLawsEnv.

  Section Messages.

    (* A record to collect information passed to the user. *)
    Record Message (Σ : LCtx) : Type :=
      MkMessage
        { msg_function        : string;
          msg_message         : string;
          msg_program_context : PCtx;
          msg_localstore      : SymbolicLocalStore msg_program_context Σ;
          msg_heap            : SymbolicHeap Σ;
          msg_pathcondition   : PathCondition Σ;
        }.
    Global Arguments MkMessage {Σ} _ _ _ _ _ _.

    Global Instance SubstMessage : Subst Message :=
      fun Σ1 Σ2 ζ12 err =>
        match err with
        | MkMessage f m Γ δ h pc => MkMessage f m Γ (subst ζ12 δ) (subst ζ12 h) (subst ζ12 pc)
        end.

    Global Instance SubstLawsMessage : SubstLaws Message.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Inductive Error (Σ : LCtx) (msg : Message Σ) : Prop :=.

  End Messages.

  Section Obligations.

    Inductive Obligation {Σ} (ι : SymInstance Σ) (msg : Message Σ) (fml : Formula Σ) : Prop :=
    | obligation (p : inst ι fml : Prop).

  End Obligations.

  Section SymbolicState.

    (* Local Set Primitive Projections. *)

    Record SymbolicState (Γ : PCtx) (Σ : LCtx) : Type :=
      MkSymbolicState
        { symbolicstate_localstore    : SymbolicLocalStore Γ Σ;
          symbolicstate_heap          : SymbolicHeap Σ
        }.
    Global Arguments symbolicstate_localstore {_ _} _.
    Global Arguments symbolicstate_heap {_ _} _.

    Definition symbolicstate_initial {Γ Σ} (δ : SymbolicLocalStore Γ Σ) : SymbolicState Γ Σ :=
      MkSymbolicState δ nil.

    Global Instance subst_symbolicstate {Γ} : Subst (SymbolicState Γ) :=
      fun Σ1 Σ2 ζ '(MkSymbolicState ŝ ĥ) =>
        MkSymbolicState (subst ζ ŝ) (subst ζ ĥ).
    Global Instance substlaws_symbolicstate {Γ} : SubstLaws (SymbolicState Γ).
    Proof.
      constructor.
      { intros ? []; cbn; f_equal; now rewrite subst_sub_id. }
      { intros ? ? ? ? ? []; cbn; f_equal; now rewrite subst_sub_comp. }
    Qed.

    Definition symbolicstate_produce_chunk {Γ Σ} (c : Chunk Σ) : SymbolicState Γ Σ -> SymbolicState Γ Σ :=
      fun '(MkSymbolicState δ h) => MkSymbolicState δ (cons c h).

  End SymbolicState.

  Section TrySolve.

    Definition try_solve_eq {Σ σ} (t1 t2 : Term Σ σ) : option bool :=
      if Term_eqb t1 t2
      then Some true
      else
        (* If the terms are literals, we can trust the negative result. *)
        match t1 , t2 with
        | term_lit _ _ , term_lit _ _ => Some false
        | _            , _            => None
        end.

    Lemma try_solve_eq_spec {Σ σ} (t1 t2 : Term Σ σ) :
      OptionSpec
        (fun b => forall ι, inst ι t1 = inst ι t2 <-> is_true b)
        True
        (try_solve_eq t1 t2).
    Proof.
      unfold try_solve_eq.
      destruct (Term_eqb_spec t1 t2).
      - constructor. intros. apply reflect_iff.
        constructor. congruence.
      - destruct t1; dependent elimination t2; constructor; auto.
        intros. apply reflect_iff. constructor. cbn. congruence.
    Qed.

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
      | formula_eq t1 t2 => try_solve_eq t1 t2
        (* else Term_eqvb t1 t2 *)
      | formula_neq t1 t2 => option_map negb (try_solve_eq t1 t2)
        (* else option_map negb (Term_eqvb t1 t2) *)
      end.

    Lemma try_solve_formula_spec {Σ} (fml : Formula Σ) :
      OptionSpec
        (fun b => forall ι, inst ι fml <-> is_true b)
        True
        (try_solve_formula fml).
    Proof.
      destruct fml; cbn.
      - dependent elimination t; constructor; auto.
      - constructor; auto.
      - destruct (try_solve_eq_spec t1 t2); now constructor.
      - destruct (try_solve_eq_spec t1 t2); constructor; auto.
        intros ι. specialize (H ι). destruct a; intuition.
    Qed.

  End TrySolve.

  Infix ">=>" := ssrfun.pcomp (at level 80, right associativity).

  Section ChunkExtraction.
    Context {Σ : LCtx}.

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
        else fun pc => Some (cons (formula_eq te tr) pc).

    Definition match_env_eqb := @match_env_eqb' (@match_term_eqb).

    Equations(noeqns) match_chunk_eqb (ce : Chunk Σ) (cr : Chunk Σ) :
      PathCondition Σ -> option (PathCondition Σ) :=
      match_chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2)
      with eq_dec p1 p2 => {
        match_chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) (left eq_refl) := match_env_eqb ts1 ts2;
        match_chunk_eqb (chunk_user p1 ts1) (chunk_user p2 ts2) (right _)      := fun _ => None
      };
      match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := match_term_eqb t1 t2;
        match_chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk_eqb _ _  := fun _ => None.

    Definition extract_chunk_eqb (ce : Chunk Σ) (h : SymbolicHeap Σ) :
      List (Pair PathCondition SymbolicHeap) Σ :=
      stdpp.base.omap
        (fun '(cr,h') => option_map (fun L' => (L',h')) (match_chunk_eqb ce cr nil))
        (heap_extractions h).

  End ChunkExtraction.

  Definition EvarEnv (Σe Σr : LCtx) : Type := Env (fun b => option (Term Σr (snd b))) Σe.

  Global Instance SubstEvarEnv {Σe} : Subst (EvarEnv Σe) :=
    fun Σ1 Σ2 ζ => env_map (fun _ => option_map (subst ζ)).

  Definition create_evarenv (Σe Σr : LCtx) : EvarEnv Σe Σr :=
    env_tabulate (fun _ _ => None).
  Definition create_evarenv_id (Σ : LCtx) : EvarEnv Σ Σ :=
    env_tabulate (fun '(x::σ) xIn => Some (term_var x)).

  Record EvarError (Σe Σr : LCtx) (D : Type) : Type :=
    { evarerror_env  : EvarEnv Σe Σr;
      evarerror_data : D;
    }.

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
      | term_bvec ts         => term_bvec <$> traverse_vector eval_term_evar ts
      | term_tuple ts        => term_tuple <$> traverse_env (@eval_term_evar) ts
      | @term_projtup _ _ t n _ p     => (fun t => term_projtup t n (p:=p)) <$> eval_term_evar t
      | term_union U K t     => term_union U K <$> eval_term_evar t
      | term_record R ts     => term_record R <$> traverse_env (fun b => @eval_term_evar (snd b)) ts
      (* | term_projrec t rf    => (fun t => term_projrec t rf) <$> eval_term_evar t *)
      end%exp.

    Definition eval_chunk_evar (c : Chunk Σe) : option (Chunk Σr) :=
      match c with
      | chunk_user p ts => chunk_user p <$> traverse_env (@eval_term_evar) ts
      | chunk_ptsreg r t => chunk_ptsreg r <$> eval_term_evar t
      end.

    Section WithMatchTerm.

      Variable match_term : forall {σ}, Term Σe σ -> Term Σr σ -> EvarEnv Σe Σr -> option (EvarEnv Σe Σr).

      Equations(noeqns) match_env' {σs} (te : Env (Term Σe) σs) (tr : Env (Term Σr) σs) :
        EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
        match_env' env_nil env_nil := Some;
        match_env' (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) := match_env' E1 E2 >=> match_term t1 t2.

      Equations(noeqns) match_nenv' {N : Set} {Δ : NCtx N Ty} (te : NamedEnv (Term Σe) Δ) (tr : NamedEnv (Term Σr) Δ) :
        EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
        match_nenv' env_nil env_nil := Some;
        match_nenv' (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) := match_nenv' E1 E2 >=> match_term t1 t2.

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
      match_term (term_inr t1) (term_inr t2) := match_term t1 t2;
      match_term (term_inr t1) (term_lit (inr l2)) := match_term t1 (term_lit _ l2);
      match_term (term_tuple ts1) (term_tuple ts2) := match_env' (@match_term) ts1 ts2;
      match_term (term_record _ ts1) (term_record _ ts2) := match_nenv' (@match_term) ts1 ts2;
      (* Obviously more matchings can be added here. *)
      match_term _ _ := fun _ => None.

    Definition match_env := @match_env' (@match_term).
    Definition match_nenv := @match_nenv' (@match_term).

    Equations(noeqns) match_chunk (ce : Chunk Σe) (cr : Chunk Σr) :
      EvarEnv Σe Σr -> option (EvarEnv Σe Σr) :=
      match_chunk (chunk_user p1 ts1) (chunk_user p2 ts2)
      with eq_dec p1 p2 => {
        match_chunk (chunk_user p1 ts1) (chunk_user p2 ts2) (left eq_refl) := match_env ts1 ts2;
        match_chunk (chunk_user p1 ts1) (chunk_user p2 ts2) (right _)      := fun _ => None
      };
      match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left eq_refl) := match_term t1 t2;
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := fun _ => None
      };
      match_chunk _ _  := fun _ => None.

    Definition extract_chunk (ce : Chunk Σe) (h : SymbolicHeap Σr) (L : EvarEnv Σe Σr) :
      List (Pair (EvarEnv Σe) SymbolicHeap) Σr :=
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
      - admit.
      - admit.
      - rewrite IHt; reflexivity.
      - rewrite IHt; reflexivity.
      - admit.
      (* - rewrite IHt; reflexivity. *)
    Admitted.

  End WithEvarEnv.

  Section SymbolicUnit.

    Definition Unit : LCtx -> Type := fun _ => unit.
    Global Instance SubstUnit : Subst Unit :=
      fun _ _ _ t => t.
    Global Instance SubstLawsUnit : SubstLaws Unit.
    Proof. constructor; reflexivity. Qed.
    Global Instance InstUnit : Inst Unit unit :=
      @Build_Inst Unit unit (fun _ _ x => x) (fun _ x  => x).
    Global Instance InstLawsUnit : InstLaws Unit unit.
    Proof. constructor; reflexivity. Qed.

  End SymbolicUnit.

  Record Config : Type :=
    MkConfig
      { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
      }.

  Definition default_config : Config :=
    {| config_debug_function _ _ f := false;
    |}.

  Section SymbolicOutcomes.

    Inductive SymOutcome (A : LCtx -> Type) (Σ : NCtx 𝑺 Ty) : Type :=
    | sout_pure (a: A Σ)
    | sout_angelic {I : Type} (os: I -> SymOutcome A Σ)
    (* | sout_demonic {I : Type} (os: I -> SymOutcome A Σ) *)
    | sout_angelic_binary (o1 o2 : SymOutcome A Σ)
    | sout_demonic_binary (o1 o2 : SymOutcome A Σ)
    | sout_fail (msg : Message Σ)
    | sout_block
    | sout_assertk (P : Formula Σ) (msg : Message Σ) (k : SymOutcome A Σ)
    | sout_assumek (P : Formula Σ) (k : SymOutcome A Σ)
    | sout_demonicv b (k : SymOutcome A (Σ ▻ b))
    (* | sout_subst {Σ'} (ζ : Sub Σ Σ') (k : SymOutcome A Σ'). *)
    | sout_subst x σ (xIn : (x,σ) ∈ Σ) (t : Term (Σ - (x,σ)) σ) (k : SymOutcome A (Σ - (x,σ)))
    | sout_debug {BT B} {subB : Subst BT} {instB : Inst BT B}
       (b : BT Σ) (k : SymOutcome A Σ).

    Global Arguments sout_pure {_ _} _.
    Global Arguments sout_fail {_ _} _.
    Global Arguments sout_block {_ _}.
    Global Arguments sout_demonicv {_ _} _ _.
    Global Arguments sout_subst {_ _} x {_ _} t k.

    Fixpoint sout_multisub {AT Σ1 Σ2} (ζ : MultiSub Σ1 Σ2) : SymOutcome AT Σ2 -> SymOutcome AT Σ1.
    Proof.
      destruct ζ; intros o.
      - exact o.
      - eapply sout_subst.
        apply t.
        eapply sout_multisub.
        apply ζ.
        apply o.
    Defined.

    Fixpoint subst_symoutcome {A} `{Subst A} {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (o : SymOutcome A Σ1) : SymOutcome A Σ2 :=
      match o with
      | sout_pure a => sout_pure (subst ζ a)
      | sout_angelic os => sout_angelic (fun i => subst_symoutcome ζ (os i))
      (* | sout_demonic os => sout_demonic (fun i => subst_symoutcome ζ (os i)) *)
      | sout_angelic_binary o1 o2 => sout_angelic_binary (subst_symoutcome ζ o1) (subst_symoutcome ζ o2)
      | sout_demonic_binary o1 o2 => sout_demonic_binary (subst_symoutcome ζ o1) (subst_symoutcome ζ o2)
      | sout_fail msg => sout_fail (subst ζ msg)
      | sout_block => sout_block
      | sout_assertk P msg o => sout_assertk (subst ζ P) (subst ζ msg) (subst_symoutcome ζ o)
      | sout_assumek P o => sout_assumek (subst ζ P) (subst_symoutcome ζ o)
      | sout_demonicv b k => sout_demonicv b (subst_symoutcome (sub_up1 ζ) k)
      (* | sout_subst ζ2 k => _ *)
      | @sout_subst _ _ x σ xIn t k =>
        let ζ' := sub_comp (sub_shift _) ζ in
        sout_assumek
          (formula_eq (env_lookup ζ xIn) (subst (T := fun Σ => Term Σ _) ζ' t))
          (subst_symoutcome ζ' k)
      | sout_debug d k => sout_debug (subst ζ d) (subst_symoutcome ζ k)
      end.

    Instance SubstSymOutcome {E A} `{Subst E, Subst A} : Subst (SymOutcome A) :=
      fun Σ1 Σ2 ζ o => subst_symoutcome ζ o.

    Fixpoint inst_symoutcome {AT A} `{Inst AT A} {Σ} (ι : SymInstance Σ) (o : SymOutcome AT Σ) : Outcome A :=
      match o with
      | sout_pure a                   => outcome_pure (inst ι a)
      | sout_angelic os               => outcome_angelic (fun i => inst_symoutcome ι (os i))
      | sout_angelic_binary o1 o2     => outcome_angelic_binary (inst_symoutcome ι o1) (inst_symoutcome ι o2)
      | sout_demonic_binary o1 o2     => outcome_demonic_binary (inst_symoutcome ι o1) (inst_symoutcome ι o2)
      | sout_fail msg                 => outcome_fail msg
      | sout_block                    => outcome_block
      | sout_assertk fml msg o        => outcome_assertk
                                           (Obligation ι msg fml)
                                           (inst_symoutcome ι o)
      | sout_assumek fml o            => outcome_assumek (inst ι fml) (inst_symoutcome ι o)
      | sout_demonicv b k             => outcome_demonic (fun v : Lit (snd b) => inst_symoutcome (env_snoc ι b v) k)
      | @sout_subst _ _ x σ xIn t k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assumek
          (env_lookup ι xIn = inst ι' t)
          (inst_symoutcome ι' k)
      | sout_debug d k                => outcome_debug (inst ι d) (inst_symoutcome ι k)
      end.

    Definition sout_mapping AT BT Σ : Type :=
      forall Σ', Sub Σ Σ' -> (* PathCondition Σ' -> *) AT Σ' -> BT Σ'.
    Definition sout_arrow AT BT Σ : Type :=
      forall Σ', Sub Σ Σ' -> PathCondition Σ' -> AT Σ' -> SymOutcome BT Σ'.

    (* Definition sout_arrow_dcl {ET E AT A BT B} `{Subst ET, Subst BT, Inst ET E, Inst AT A, Inst BT B} {Σ} (f : sout_arrow ET AT BT Σ) : Prop := *)
    (*   forall Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2, *)
    (*     (forall ι1 ι2, ι1 = inst ι2 ζ12 -> inst ι1 a1 = inst ι2 a2) -> *)
    (*     sout_geq (subst ζ12 (f Σ1 ζ1 a1)) (f Σ2 ζ2 a2). *)

    Fixpoint sout_map {A B Σ} (f : sout_mapping A B Σ) (ma : SymOutcome A Σ) : SymOutcome B Σ :=
      match ma with
      | sout_pure a                   => sout_pure (f Σ (sub_id Σ) a)
      | @sout_angelic _ _ I0 os     => sout_angelic (fun i : I0 => sout_map f (os i))
      | sout_angelic_binary o1 o2     => sout_angelic_binary (sout_map f o1) (sout_map f o2)
      | sout_demonic_binary o1 o2     => sout_demonic_binary (sout_map f o1) (sout_map f o2)
      | sout_fail msg                 => sout_fail msg
      | sout_block                    => sout_block
      | sout_assertk fml msg k        => sout_assertk fml msg (sout_map f k)
      | sout_assumek fml k            => sout_assumek fml (sout_map f k)
      | sout_demonicv b k             => sout_demonicv b (sout_map (fun Σ' ζ a => f Σ' (env_tail ζ) a) k)
      | @sout_subst _ _ x σ xIn t k =>
        let ζ' := sub_single xIn t in
        sout_subst x t (sout_map (fun Σ' ζ => f Σ' (sub_comp ζ' ζ)) k)
      | sout_debug d k                => sout_debug d (sout_map f k)
      end.

    Fixpoint sout_bind {A B Σ} (pc : PathCondition Σ) (ma : SymOutcome A Σ) (f : forall Σ', Sub Σ Σ' -> PathCondition Σ' -> A Σ' -> SymOutcome B Σ') {struct ma} : SymOutcome B Σ :=
      match ma with
      | sout_pure a                   => f Σ (sub_id Σ) pc a
      | @sout_angelic _ _ I0 os     => sout_angelic (fun i : I0 => sout_bind pc (os i) f)
      | sout_angelic_binary o1 o2     => sout_angelic_binary (sout_bind pc o1 f) (sout_bind pc o2 f)
      | sout_demonic_binary o1 o2     => sout_demonic_binary (sout_bind pc o1 f) (sout_bind pc o2 f)
      | sout_fail msg                 => sout_fail msg
      | sout_block                    => sout_block
      | sout_assertk fml msg k        => sout_assertk fml msg (sout_bind (cons fml pc) k f)
      | sout_assumek fml k            => sout_assumek fml (sout_bind (cons fml pc) k f)
      | sout_demonicv b k             => sout_demonicv b (sout_bind (subst sub_wk1 pc) k (fun Σ' ζ a => f Σ' (env_tail ζ) a))
      | @sout_subst _ _ x σ xIn t k =>
        let ζ' := sub_single xIn t in
        sout_subst x t (sout_bind (subst ζ' pc) k (fun Σ' ζ => f Σ' (sub_comp ζ' ζ)))
      | sout_debug d k                => sout_debug d (sout_bind pc k f)
      end.

    (* Poor man's unification *)
    Definition try_unify {Σ σ} (t1 t2 : Term Σ σ) :
      option { Σ' & MultiSub Σ Σ' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term Σ σ =>
          match occurs_check ςInΣ t2 with
          | Some t => Some (existT _ (multisub_cons ς t multisub_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_propagate {Σ} (fml : Formula Σ) :
      option { Σ' & MultiSub Σ Σ' } :=
      match fml with
      | formula_eq t1 t2 =>
        match try_unify t1 t2 with
        | Some r => Some r
        | None => try_unify t2 t1
        end
      | _ => None
      end.

    Definition sout_assume_formula {Σ} (pc : PathCondition Σ) (fml : Formula Σ) :
      SymOutcome Unit Σ :=
      (* Check if the formula is an equality that can be propagated. *)
      match try_propagate fml with
      | Some (existT Σ2 ζ) => sout_multisub ζ (sout_pure tt)
      | None =>
        (* If everything fails, we simply add the formula to the path
           condition verbatim. *)
        sout_assumek fml (sout_pure tt)
      end.

    Definition sout_assert_formula {Σ} (msg : Message Σ) (pc : PathCondition Σ) (fml : Formula Σ) :
      SymOutcome Unit Σ :=
        match try_solve_formula fml with
        | Some true => sout_pure tt
        | Some false => sout_fail msg
        | None =>
          sout_assertk fml msg
            (* We also want to assume the formula for the continuation. *)
            (sout_assume_formula pc fml)
        end.

    Fixpoint sout_wp {AT A Σ} `{Inst AT A} (o : SymOutcome AT Σ) (ι : SymInstance Σ) (POST : A -> Prop) : Prop :=
      match o with
      | sout_pure a                               => POST (inst ι a)
      | sout_angelic os                           => exists i, sout_wp (os i) ι POST
      | sout_angelic_binary o1 o2                 => (sout_wp o1 ι POST) \/ (sout_wp o2 ι POST)
      | sout_demonic_binary o1 o2                 => (sout_wp o1 ι POST) /\ (sout_wp o2 ι POST)
      | sout_fail msg                             => Error msg
      | sout_block                                => True
      | sout_assertk fml msg o                    => inst ι fml /\ sout_wp o ι POST
      | sout_assumek fml o                        => (inst ι fml : Prop) -> sout_wp o ι POST
      | sout_demonicv b k                         => forall (v : Lit (snd b)), sout_wp k (env_snoc ι b v) POST
      | @sout_subst _ _ x σ xIn t k             =>
        let ι' := env_remove' _ ι xIn in
        env_lookup ι xIn = inst ι' t -> sout_wp k ι' POST
      | sout_debug d k                            => Debug (inst ι d) (sout_wp k ι POST)
      end.

    Definition sout_wp' {AT A Σ} `{Inst AT A} (o : SymOutcome AT Σ) (ι : SymInstance Σ) (POST : A -> Prop) : Prop :=
      outcome_satisfy (inst_symoutcome ι o) POST.

    Lemma sout_wp_wp' {AT A Σ} `{Inst AT A} (o : SymOutcome AT Σ) (ι : SymInstance Σ) (POST : A -> Prop) :
      sout_wp o ι POST <-> sout_wp' o ι POST.
    Proof.
      unfold sout_wp'.
      induction o; cbn; auto.
      - split; intros [i HYP]; exists i; revert HYP; apply H0.
      - specialize (IHo1 ι). specialize (IHo2 ι). intuition.
      - specialize (IHo1 ι). specialize (IHo2 ι). intuition.
      - split; intros [].
      - specialize (IHo ι). intuition.
        constructor; auto.
      - specialize (IHo ι). intuition.
      - split; intros HYP v; specialize (HYP v); specialize (IHo (env_snoc ι b v)); intuition.
      - specialize (IHo (env_remove' (x :: σ) ι xIn)). intuition.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Lemma sout_wp_monotonic {AT A} `{Inst AT A} {Σ}
      (o : SymOutcome AT Σ) (ι : SymInstance Σ)
      (P Q : A -> Prop) (PQ : forall a, P a -> Q a) :
      sout_wp o ι P ->
      sout_wp o ι Q.
    Proof. rewrite ?sout_wp_wp'. now apply outcome_satisfy_monotonic. Qed.

    Global Instance proper_sout_wp {AT A} `{Inst AT A} {Σ} (o : SymOutcome AT Σ) (ι : SymInstance Σ) :
      Proper
        (pointwise_relation A iff ==> iff)
        (sout_wp o ι).
    Proof.
      unfold Proper, respectful, pointwise_relation, Basics.impl.
      intros P Q PQ; split; apply sout_wp_monotonic; intuition.
    Qed.

    Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

    Definition sout_mapping_dcl {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} (f : sout_mapping AT BT Σ0) : Prop :=
      forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) (ζ02 : Sub Σ0 Σ2) (a1 : AT Σ1) (a2 : AT Σ2) (ζ12 : Sub Σ1 Σ2),
      forall ι1 ι2,
        ι1 = inst ι2 ζ12 ->
        inst ι1 ζ01 = inst ι2 ζ02 ->
        inst ι1 a1 = inst ι2 a2 ->
        inst ι1 (f Σ1 ζ01 a1) = inst ι2 (f Σ2 ζ02 a2).

    Definition sout_arrow_dcl {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Σ} (f : sout_arrow AT BT Σ) : Prop :=
      forall Σ1 Σ2 ζ1 ζ2 pc1 pc2 ζ12 a1 a2 (P Q : B -> Prop) (PQ : forall b, P b -> Q b),
       forall (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2),
         ι1 = inst ι2 ζ12 ->
         instpc ι1 pc1 ->
         instpc ι2 pc2 ->
         inst ι1 ζ1 = inst ι2 ζ2 ->
         inst ι1 a1 = inst ι2 a2 ->
         sout_wp (f Σ1 ζ1 pc1 a1) ι1 P ->
         sout_wp (f Σ2 ζ2 pc2 a2) ι2 Q.

    (* Lemma sout_arrow_dcl_dcl' {ET E AT A BT B} `{InstLaws ET E, Inst AT A, InstLaws BT B} {Σ} (f : sout_arrow ET AT BT Σ) : *)
    (*   sout_arrow_dcl f <-> sout_arrow_dcl' f. *)
    (* Proof. *)
    (*   unfold sout_arrow_dcl, sout_arrow_dcl', sout_geq. *)
    (*   setoid_rewrite sout_wp_subst. *)
    (*   split; intros HYP Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2; *)
    (*     specialize (HYP Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2). *)
    (*   - intros F P Q PQ ι1 ι2 -> Hζ Ha. apply HYP; auto. *)
    (*     intros ι1' ι2'.  *)
    (* Qed. *)


    Lemma inst_sub_shift {Σ} (ι : SymInstance Σ) {b} (bIn : b ∈ Σ) :
      inst ι (sub_shift bIn) = env_remove' b ι bIn.
    Proof.
      unfold env_remove', sub_shift, inst; cbn.
      apply env_lookup_extensional. intros [y τ] yIn.
      now rewrite env_lookup_map, ?env_lookup_tabulate.
    Qed.

    Lemma sout_wp_subst {AT A} `{InstLaws AT A} {Σ1 Σ2} (ζ12 : Sub Σ1 Σ2)
      (o : SymOutcome AT Σ1) (ι : SymInstance Σ2) (POST : A -> Prop) :
      sout_wp (subst ζ12 o) ι POST <-> sout_wp o (inst ι ζ12) POST.
    Proof.
      cbv [subst SubstSymOutcome]. revert Σ2 ι ζ12.
      induction o; cbn; intros.
      - now rewrite inst_subst.
      - split; intros [i HYP]; exists i; revert HYP; apply (H3 i Σ2 ι ζ12).
      - now rewrite IHo1, IHo2.
      - now rewrite IHo1, IHo2.
      - split; intros [].
      - reflexivity.
      - now rewrite IHo, inst_subst.
      - now rewrite IHo, inst_subst.
      - destruct b as [x τ].
        split; intros HYP v; specialize (HYP v); revert HYP;
          rewrite (IHo _ (env_snoc ι (x :: τ) v) (sub_up1 ζ12));
          unfold sub_up1, sub_comp;
          now rewrite inst_sub_snoc, inst_subst, inst_sub_wk1.
      - rewrite IHo. unfold sub_comp.
        now rewrite ?inst_subst, inst_sub_shift, <- inst_lookup.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Definition sout_geq {AT A} `{Inst AT A} {Σ} (o1 o2 : SymOutcome AT Σ) : Prop :=
      forall (P Q : A -> Prop) (PQ : forall a, P a -> Q a) ι,
        sout_wp o1 ι P ->
        sout_wp o2 ι Q.

    Global Instance preorder_sout_geq {AT A} `{Inst AT A} {Σ} : PreOrder (sout_geq (Σ := Σ)).
    Proof.
      constructor.
      - unfold sout_geq; intros o * PQ *.
        now apply sout_wp_monotonic.
      - intros x y z. unfold sout_geq.
        intros Rxy Ryz P Q PQ ι.
        specialize (Rxy P Q PQ ι).
        specialize (Ryz Q Q (fun _ p => p) ι).
        auto.
    Qed.

    Fixpoint sout_safe {AT Σ} (ι : SymInstance Σ) (o : SymOutcome AT Σ) {struct o} : Prop :=
      match o with
      | sout_pure a => True
      | sout_angelic os => exists i, sout_safe ι (os i)
      (* | sout_demonic os => forall i, sout_safe ι (os i) POST *)
      | sout_angelic_binary o1 o2 => sout_safe ι o1 \/ sout_safe ι o2
      | sout_demonic_binary o1 o2 => sout_safe ι o1 /\ sout_safe ι o2
      | sout_fail msg => False
      | sout_block => True
      | sout_assertk fml msg o =>
        Obligation ι msg fml /\ sout_safe ι o
      | sout_assumek fml o => (inst ι fml : Prop) -> sout_safe ι o
      | sout_demonicv b k => forall v, sout_safe (env_snoc ι b v) k
      | @sout_subst _ _ x σ xIn t k =>
        let ι' := env_remove' (x,σ) ι xIn in
        env_lookup ι xIn = inst ι' t ->
        sout_safe ι' k
      | sout_debug d k => Debug (inst ι d) (sout_safe ι k)
      end.
    Global Arguments sout_safe {_} Σ ι o.

    Lemma inversion_eq_env_snoc {B D} {Γ : Ctx B} {b : B} (E1 E2 : Env D Γ) (v1 v2 : D b) :
      env_snoc E1 b v1 = env_snoc E2 b v2 ->
      E1 = E2 /\ v1 = v2.
    Proof. intros H. now dependent elimination H. Qed.

    Lemma sout_wp_map {AT A BT B} `{InstLaws AT A, Inst BT B} {Σ} (ma : SymOutcome AT Σ)
      (f : sout_mapping AT BT Σ) (f_dcl : sout_mapping_dcl f) :
      forall (ι : SymInstance Σ) POST,
        sout_wp (sout_map f ma) ι POST <->
        sout_wp ma ι (fun a => POST (inst ι (f Σ (sub_id Σ) (lift a)))).
    Proof.
      intros ι. induction ma; cbn; intros POST; auto.
      - assert (inst ι (f Σ (sub_id Σ) a) =
                inst ι (f Σ (sub_id Σ) (lift (inst ι a)))) as ->; auto.
        eapply f_dcl; eauto; now rewrite ?inst_sub_id, ?inst_lift.
      - split; intros [i HYP]; exists i; revert HYP; rewrite H4; eauto.
      - rewrite IHma1, IHma2; eauto.
      - rewrite IHma1, IHma2; eauto.
      - rewrite IHma; auto.
      - rewrite IHma; auto.
      - destruct b as [x σ]; cbn. setoid_rewrite IHma.
        split; (intros Hwp v; specialize (Hwp v); revert Hwp; apply sout_wp_monotonic; intros a;
                match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
        + eapply (f_dcl _ _ _ _ _ _ (sub_snoc (sub_id _) (x :: σ) (term_lit σ v)));
            rewrite ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
          rewrite <- sub_comp_wk1_tail; unfold sub_comp.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
        + eapply (f_dcl _ _ _ _ _ _ sub_wk1);
            rewrite ?inst_sub_wk1, ?inst_lift; auto.
          rewrite <- sub_comp_wk1_tail; unfold sub_comp.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
        + unfold sout_mapping_dcl. intros. eapply f_dcl; eauto.
          rewrite <- ?sub_comp_wk1_tail; unfold sub_comp.
          rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
          intuition.
      - rewrite IHma.
        split; (intros Hwp Heq; specialize (Hwp Heq); revert Hwp; apply sout_wp_monotonic; intros a;
                match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
        + apply (f_dcl _ _ _ _ _ _ (sub_shift xIn)); unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_shift; auto.
          now rewrite inst_sub_single.
        + apply (f_dcl _ _ _ _ _ _ (sub_single xIn t)); unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_single; auto.
        + unfold sout_mapping_dcl. intros.
          eapply f_dcl; unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_shift; auto.
          intuition.
      - split; intros [HYP]; constructor; revert HYP; now apply IHma.
    Qed.

    Lemma sout_wp_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Σ} (pc : PathCondition Σ) (ma : SymOutcome AT Σ)
          (f : forall Σ', Sub Σ Σ' -> PathCondition Σ' -> AT Σ' -> SymOutcome BT Σ') (f_dcl : sout_arrow_dcl f) :
      forall (ι : SymInstance Σ) (Hpc : instpc ι pc) POST,
        sout_wp (sout_bind pc ma f) ι POST <->
        sout_wp ma ι (fun a => sout_wp (f Σ (sub_id _) pc (lift a)) ι POST).
    Proof.
      intros ι Hpc. induction ma; cbn; intros POST; auto.
      - split; eapply f_dcl with (sub_id _); eauto; rewrite ?inst_sub_id, ?inst_lift; auto.
      - split; intros [i HYP]; exists i; revert HYP; now rewrite H7.
      - now rewrite IHma1, IHma2.
      - now rewrite IHma1, IHma2.
      - split; (intros [HP Hwp]; split; [exact HP | ]; revert Hwp);
          rewrite IHma; eauto; try (rewrite inst_pathcondition_cons; intuition; fail);
            apply sout_wp_monotonic; intros a; eapply f_dcl; eauto.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
      - split; (intros Hwp HP; specialize (Hwp HP); revert Hwp);
          rewrite IHma; eauto; try (rewrite inst_pathcondition_cons; intuition; fail);
            apply sout_wp_monotonic; intros a; eapply f_dcl; eauto.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
      - destruct b as [x σ]; cbn.
        split; (intros Hwp v; specialize (Hwp v); revert Hwp).
        + rewrite IHma.
          * apply sout_wp_monotonic. intros a.
            unfold sout_arrow_dcl in f_dcl.
            eapply (f_dcl _ _ _ _ _ _ (sub_snoc (sub_id _) (x :: σ) (term_lit σ v))); eauto.
            now rewrite inst_sub_snoc, inst_sub_id.
            now rewrite inst_subst, inst_sub_wk1.
            rewrite <- sub_up1_id. unfold sub_up1.
            rewrite sub_comp_id_left. cbn [env_tail sub_snoc].
            now rewrite inst_sub_wk1, inst_sub_id.
            now rewrite ?inst_lift.
          * unfold sout_arrow_dcl. intros. revert H12.
            destruct (snocView ζ1), (snocView ζ2).
            cbn in H10. apply inversion_eq_env_snoc in H10.
            destruct H10. eapply f_dcl; eauto.
          * now rewrite inst_subst, inst_sub_wk1.
        + rewrite IHma.
          * apply sout_wp_monotonic. intros a.
            unfold sout_arrow_dcl in f_dcl.
            eapply (f_dcl _ _ _ _ _ _ sub_wk1); eauto.
            now rewrite inst_sub_wk1.
            now rewrite inst_subst, inst_sub_wk1.
            rewrite <- sub_up1_id. unfold sub_up1.
            rewrite sub_comp_id_left. cbn [env_tail sub_snoc].
            now rewrite inst_sub_wk1, inst_sub_id.
            now rewrite ?inst_lift.
          * unfold sout_arrow_dcl. intros. revert H12.
            destruct (snocView ζ1), (snocView ζ2).
            cbn in H10. apply inversion_eq_env_snoc in H10.
            destruct H10. eapply f_dcl; eauto.
          * now rewrite inst_subst, inst_sub_wk1.
      - split; (intros Hwp Heq; specialize (Hwp Heq); revert Hwp).
        + rewrite IHma.
          * apply sout_wp_monotonic. intros a.
            apply (f_dcl _ _ _ _ _ _ (sub_shift xIn)); auto.
            now rewrite inst_sub_shift.
            now rewrite inst_subst, inst_sub_single.
            now rewrite sub_comp_id_right, inst_sub_id, inst_sub_single.
            now rewrite ?inst_lift.
          * unfold sout_arrow_dcl. intros. revert H12.
            apply (f_dcl _ _ _ _ _ _ ζ12); auto.
            unfold sub_comp. rewrite ?inst_subst.
            congruence.
          * now rewrite inst_subst, inst_sub_single.
        + rewrite IHma.
          * apply sout_wp_monotonic. intros a.
            apply (f_dcl _ _ _ _ _ _ (sub_single xIn t)); auto.
            now rewrite inst_sub_single.
            now rewrite inst_subst, inst_sub_single.
            now rewrite sub_comp_id_right, inst_sub_id, inst_sub_single.
            now rewrite ?inst_lift.
          * unfold sout_arrow_dcl. intros. revert H12.
            apply (f_dcl _ _ _ _ _ _ ζ12); auto.
            unfold sub_comp. rewrite ?inst_subst.
            congruence.
          * now rewrite inst_subst, inst_sub_single.
      - split; intros [HYP]; constructor; revert HYP; now apply IHma.
    Qed.

    Lemma sout_wp_assumek_subst {AT A} `{InstLaws AT A} {Σ x σ} (xIn : (x,σ) ∈ Σ) (t : Term (Σ - (x,σ)) σ)
          (k : SymOutcome AT Σ) :
      forall ι POST,
        sout_wp (sout_assumek (formula_eq (term_var x) (subst (T := fun Σ => Term Σ _) (sub_shift xIn) t)) k) ι POST <->
        sout_wp (sout_subst x t (subst (sub_single xIn t) k)) ι POST.
    Proof.
      cbn. intros *. rewrite inst_subst. rewrite inst_sub_shift, sout_wp_subst.
      split; intros Hwp HYP; specialize (Hwp HYP); revert Hwp; now rewrite inst_sub_single.
    Qed.

    Fixpoint inst_multisub {Σ0 Σ1} (ι : SymInstance Σ0) (ζ : MultiSub Σ0 Σ1) : Prop :=
      match ζ with
      | multisub_id => True
      | @multisub_cons _ Σ' x σ xIn t ζ0 =>
        let ι' := env_remove' (x :: σ) ι xIn in
        env_lookup ι xIn = inst ι' t /\ inst_multisub ι' ζ0
      end.

    Lemma inst_multi {Σ1 Σ2} (ι1 : SymInstance Σ1) (ζ : MultiSub Σ1 Σ2) :
      inst_multisub ι1 ζ ->
      inst (inst ι1 (sub_multishift ζ)) (sub_multi ζ) = ι1.
    Proof.
      intros Hζ. induction ζ; cbn.
      - now rewrite ?inst_sub_id.
      - cbn in Hζ. destruct Hζ as [? Hζ]. rewrite <- inst_sub_shift in Hζ.
        unfold sub_comp. rewrite ?inst_subst.
        rewrite IHζ; auto. rewrite inst_sub_shift.
        now rewrite inst_sub_single.
    Qed.

    Lemma sout_wp_multisub {AT A} `{InstLaws AT A} {Σ0 Σ1} (ζ : MultiSub Σ0 Σ1)
      (o : SymOutcome AT Σ1) (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1) (P : A -> Prop) :
      ι0 = inst ι1 (sub_multi ζ) ->
      sout_wp (sout_multisub ζ o) ι0 P <-> (inst_multisub ι0 ζ -> sout_wp o ι1 P).
    Proof.
      intros Heqι. induction ζ; cbn in *.
      - rewrite inst_sub_id in Heqι. subst. intuition.
      - unfold sub_comp in Heqι. rewrite inst_subst in Heqι.
        rewrite IHζ. intuition. rewrite <- inst_sub_shift. subst.
        rewrite <- inst_subst. pose proof (sub_comp_shift_single xIn t) as Hid.
        unfold sub_comp in Hid. now rewrite Hid, inst_sub_id.
    Qed.

    Lemma sout_wp_multisub' {AT A} `{InstLaws ET E, InstLaws AT A} {Σ0 Σ1} (ζ : MultiSub Σ0 Σ1)
      (o : SymOutcome AT Σ1) (ι0 : SymInstance Σ0) (F : E -> Prop) (P : A -> Prop) :
      sout_wp (sout_multisub ζ o) ι0 P <-> (inst_multisub ι0 ζ -> sout_wp o (inst ι0 (sub_multishift ζ)) P).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id. intuition.
      - unfold sub_comp. rewrite inst_subst.
        rewrite IHζ. rewrite inst_sub_shift.
        intuition.
    Qed.

    Lemma try_unify_spec {Σ σ} (t1 t2 : Term Σ σ) :
      OptionSpec (fun '(existT Σ' ζ) => forall ι, inst ι t1 = inst ι t2 <-> inst_multisub ι ζ) True (try_unify t1 t2).
    Proof.
      unfold try_unify. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:Heq; constructor; auto.
      apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq. subst.
      intros ι. rewrite inst_subst, inst_sub_shift.
      cbn. intuition.
    Qed.

    Lemma try_propagate_spec {Σ} (fml : Formula Σ) :
      OptionSpec (fun '(existT Σ' ζ) => forall ι, (inst ι fml : Prop) <-> inst_multisub ι ζ) True (try_propagate fml).
    Proof.
      unfold try_propagate; destruct fml; cbn; try (constructor; auto; fail).
      destruct (try_unify_spec t1 t2) as [[Σ' ζ] HYP|_]. constructor. auto.
      destruct (try_unify_spec t2 t1) as [[Σ' ζ] HYP|_]. constructor.
      intros ι. specialize (HYP ι). intuition.
      now constructor.
    Qed.

    Lemma sout_wp_assume_formula {Σ} (pc : PathCondition Σ) (fml : Formula Σ) (ι : SymInstance Σ) :
      forall (P : unit -> Prop),
        (* instpc ι pc -> *)
        sout_wp (sout_assume_formula pc fml) ι P <->
        ((inst ι fml : Prop) -> P tt).
    Proof.
      unfold sout_assume_formula. intros ?.
      destruct (try_propagate_spec fml) as [[Σ' ζ] HYP|_]; cbn; auto.
      now rewrite HYP, sout_wp_multisub'.
    Qed.

    Lemma sout_wp_assert_formula {Σ} (msg : Message Σ) (pc : PathCondition Σ) (fml : Formula Σ) (ι : SymInstance Σ) :
      forall (P : unit -> Prop),
        (* instpc ι pc -> *)
        sout_wp (sout_assert_formula msg pc fml) ι P <->
        (inst ι fml /\ P tt).
    Proof.
      unfold sout_assert_formula. intros ?.
      destruct (try_solve_formula_spec fml) as [b HYP|].
      - rewrite HYP. destruct b; cbn; intuition.
      - cbn. rewrite sout_wp_assume_formula.
        intuition.
    Qed.

    Definition sout_angelic_binary_prune {AT Σ} (o1 o2 : SymOutcome AT Σ) : SymOutcome AT Σ :=
      match o1 , o2 with
      | sout_block  , _           => sout_block
      | _           , sout_block  => sout_block
      | sout_fail _ , _           => o2
      | _           , sout_fail _ => o1
      | _           , _           => sout_angelic_binary o1 o2
      end.

    Definition sout_demonic_binary_prune {AT Σ} (o1 o2 : SymOutcome AT Σ) : SymOutcome AT Σ :=
      match o1 , o2 with
      | sout_block  , _           => o2
      | _           , sout_block  => o1
      | sout_fail s , _           => sout_fail s
      | _           , sout_fail s => sout_fail s
      | _           , _           => sout_demonic_binary o1 o2
      end.

    Definition sout_assertk_prune {AT Σ} (fml : Formula Σ) (msg : Message Σ) (o : SymOutcome AT Σ) : SymOutcome AT Σ :=
      match o with
      | sout_fail s => sout_fail s
      | _           => sout_assertk fml msg o
      end.

    Definition sout_assumek_prune {AT Σ} (fml : Formula Σ) (o : SymOutcome AT Σ) : SymOutcome AT Σ :=
      match o with
      | sout_block => sout_block
      | _          => sout_assumek fml o
      end.

    Definition sout_demonicv_prune {AT Σ} b (o : SymOutcome AT (Σ ▻ b)) : SymOutcome AT Σ :=
      match o with
      | sout_block => sout_block
      | @sout_subst _ _ x σ (MkInCtx n p) t k =>
        match n return
              forall (p : ctx_nth_is (ctx_snoc Σ b) n (pair x σ)),
                SymOutcome AT (ctx_remove (MkInCtx n p)) -> SymOutcome AT Σ
        with
        | O   => fun p k => k
        | S n => fun _ _ => sout_demonicv b o
        end p k
      | _ => sout_demonicv b o
      end.

    Definition sout_subst_prune {AT Σ x σ} {xIn : (x,σ) ∈ Σ} (t : Term (Σ - (x,σ)) σ) (k : SymOutcome AT (Σ - (x,σ))) : SymOutcome AT Σ :=
      match k with
      | sout_block => sout_block
      | _          => sout_subst x t k
      end.

    Fixpoint sout_prune {AT Σ} (o : SymOutcome AT Σ) : SymOutcome AT Σ :=
      match o with
      | sout_pure a => sout_pure a
      | sout_fail msg => sout_fail msg
      | sout_block => sout_block
      | sout_angelic os =>
        sout_angelic (fun i => sout_prune (os i))
      | sout_angelic_binary o1 o2 =>
        sout_angelic_binary_prune (sout_prune o1) (sout_prune o2)
      | sout_demonic_binary o1 o2 =>
        sout_demonic_binary_prune (sout_prune o1) (sout_prune o2)
      | sout_assertk P msg o =>
        sout_assertk_prune P msg (sout_prune o)
      | sout_assumek P o =>
        sout_assumek_prune P (sout_prune o)
      | sout_demonicv b o =>
        sout_demonicv_prune (sout_prune o)
      | sout_subst x t k =>
        sout_subst_prune t (sout_prune k)
      | sout_debug d k => sout_debug d (sout_prune k)
      end.

    Definition sout_ok {AT Σ} (o : SymOutcome AT Σ) : bool :=
      match sout_prune o with
      | sout_block  => true
      | _           => false
      end.

  End SymbolicOutcomes.

  Section VerificationConditions.

    Inductive VerificationCondition {AT Σ} (p : SymOutcome AT Σ) : Prop :=
    | vc (P : ForallNamed (fun ι : SymInstance Σ => sout_safe _ ι p)).

  End VerificationConditions.

  Section EvarExplanation.

    (* We currently avoid introducing existential variables into the
       underlying symbolic path monad, because this would make the system more
       complicated. Instead we avoid using existential quantification of the
       path monad altogether and deal with it in the mutator instead.

       This is achieved by temporarily creating an [EvarEnv] when needed, i.e.
       when *consuming* the post-condition at the end of a function, or the
       pre-condition of a called function. An [EvarEnv] can be understood as a
       system of equations between existential variables and term in which
       those existentials are fresh (c.f. solved forms for Hindley-Milner
       constraint-based type checking).

       Effectively, we have something like this

           [∀ᾱ∃β̄, (βᵢ = tᵢ) ∧ ..]

       All existential variables β̄ (angelic choice) come after the universal
       variables ᾱ (demonic choice). We also avoid introducing new universals
       during consume to keep this order. In this setting the [EvarEnv] can be
       interpreted as a set of equations between a subset of existential
       variables [βᵢ] and terms [tᵢ] such that [freevars (tᵢ) ⊆ ᾱ`].

       Equations are discovered by semi-unification and added to the EvarEnv.
       See [dmut_consume_formula_evar] and [dmut_consume_chunk_evar] for
       details.
     *)

    Lemma exists_distr A P Q :
      (exists a : A, P a \/ Q a) <->
      (exists a : A, P a) \/ (exists a, Q a).
    Proof. firstorder. Qed.

    Lemma exists_distr_conj A P Q :
      (exists a : A, P /\ Q a) <->
      P /\ (exists a : A, Q a).
    Proof. firstorder. Qed.

    Lemma if_demonic (b : bool) (P Q : Prop) :
      (if b then P else Q) <->
      (b = true -> P) /\ (b = false -> Q).
    Proof. destruct b; intuition. Qed.

    Lemma if_angelic (b : bool) (P Q : Prop) :
      (if b then P else Q) <->
      (b = true /\ P) \/ (b = false /\ Q).
    Proof. destruct b; intuition. Qed.

  End EvarExplanation.

  Section DynamicMutatorResult.

    (* Local Set Primitive Projections. *)
    Local Set Maximal Implicit Insertion.

    Record DynamicMutatorResult (Γ : PCtx) (A : LCtx -> Type) (Σ : LCtx) : Type :=
      MkDynMutResult {
          dmutres_result_value : A Σ;
          dmutres_result_state : SymbolicState Γ Σ;
        }.

    Global Arguments MkDynMutResult {_ _ _} _ _.

    Global Instance SubstDynamicMutatorResult {Γ A} `{Subst A} : Subst (DynamicMutatorResult Γ A).
    Proof.
      intros Σ1 Σ2 ζ [a s].
      constructor.
      apply (subst ζ a).
      apply (subst ζ s).
    Defined.

    Global Instance SubstLawsDynamicMutatorResult {Γ A} `{SubstLaws A} : SubstLaws (DynamicMutatorResult Γ A).
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

  End DynamicMutatorResult.

  Section DynamicMutator.

    Definition DynamicMutator (Γ1 Γ2 : PCtx) (A : LCtx -> Type) (Σ : LCtx) : Type :=
      forall Σ', Sub Σ Σ' -> PathCondition Σ' -> SymbolicState Γ1 Σ' -> SymOutcome (DynamicMutatorResult Γ2 A) Σ'.
    Bind Scope dmut_scope with DynamicMutator.

    Definition dmut_pure {Γ A} `{Subst A} {Σ} (a : A Σ) : DynamicMutator Γ Γ A Σ.
      intros Σ1 ζ1 pc1 δ.
      apply sout_pure.
      constructor.
      apply (subst ζ1 a).
      apply δ.
    Defined.

    Definition dmut_bind {Γ1 Γ2 Γ3 A B Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (f : forall Σ', Sub Σ Σ' -> A Σ' -> DynamicMutator Γ2 Γ3 B Σ') : DynamicMutator Γ1 Γ3 B Σ.
    Proof.
      intros Σ1 ζ1 pc1 δ1.
      apply (sout_bind pc1 (ma Σ1 ζ1 pc1 δ1)).
      intros Σ2 ζ2 pc2 [a2 δ2].
      eapply (sout_bind pc2).
      apply (f Σ2 (sub_comp ζ1 ζ2) a2 _ (sub_id _) pc2 δ2).
      intros Σ3 ζ3 pc3 [b3 δ3].
      apply sout_pure.
      constructor.
      apply b3.
      apply δ3.
    Defined.
    (* Definition dmut_join {Γ1 Γ2 Γ3 A Σ} (mm : DynamicMutator Γ1 Γ2 (DynamicMutator Γ2 Γ3 A) Σ) : *)
    (*   DynamicMutator Γ1 Γ3 A Σ := dmut_bind mm (fun _ _ m => m). *)

    Definition dmut_sub {Γ1 Γ2 A Σ1 Σ2} (ζ1 : Sub Σ1 Σ2) (p : DynamicMutator Γ1 Γ2 A Σ1) :
      DynamicMutator Γ1 Γ2 A Σ2 := fun Σ3 ζ2 => p _ (sub_comp ζ1 ζ2).
    Global Arguments dmut_sub {_ _ _ _ _} ζ1 p.
    Definition dmut_strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : DynamicMutator Γ1 Γ2 A Σ) (b : B Σ) :
      DynamicMutator Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ :=
      dmut_bind ma (fun _ ζ a => dmut_pure (a, subst ζ b)).
    Definition dmut_bind_right {Γ1 Γ2 Γ3 A B Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) : DynamicMutator Γ1 Γ3 B Σ :=
      dmut_bind ma (fun _ ζ _ => dmut_sub ζ mb).
    Definition dmut_bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} {Σ} (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) : DynamicMutator Γ1 Γ3 A Σ :=
      dmut_bind ma (fun _ ζ a => dmut_bind_right (dmut_sub ζ mb) (dmut_pure a)) .
    Definition dmut_fmap {Γ1 Γ2 Σ A B} `{Subst A, Subst B}
      (ma : DynamicMutator Γ1 Γ2 A Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ') :
      DynamicMutator Γ1 Γ2 B Σ :=
      fun Σ1 ζ01 pc1 s1 =>
        @sout_map (DynamicMutatorResult Γ2 A) (DynamicMutatorResult Γ2 B) Σ1
        (fun Σ2 ζ12 '(MkDynMutResult a2 s2) => MkDynMutResult (f Σ2 (sub_comp ζ01 ζ12) a2) s2)
        (ma Σ1 ζ01 pc1 s1).
    Definition dmut_fmap2 {Γ1 Γ2 Γ3 Σ A B C} `{Subst A, Subst B, Subst C}
      (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ' -> C Σ') :
      DynamicMutator Γ1 Γ3 C Σ :=
      dmut_bind ma (fun Σ1 ζ01 a1 =>
        dmut_fmap (dmut_sub ζ01 mb) (fun Σ2 ζ12 =>
          f Σ2 (sub_comp ζ01 ζ12) (subst ζ12 a1))).
    Definition dmut_pair {Γ1 Γ2 Γ3 Σ A B} `{Subst A, Subst B}
      (ma : DynamicMutator Γ1 Γ2 A Σ) (mb : DynamicMutator Γ2 Γ3 B Σ) :
      DynamicMutator Γ1 Γ3 (fun Σ => A Σ * B Σ)%type Σ :=
      dmut_fmap2 ma mb (fun _ _ => pair).

    Definition dmut_fail {Γ1 Γ2 A Σ D} (func : string) (msg : string) (data:D) : DynamicMutator Γ1 Γ2 A Σ.
      intros Σ1 ζ1 pc1 [δ1 h1].
      apply sout_fail.
      apply (@MkMessage _ func msg Γ1); assumption.
    Defined.

    Definition dmut_block {Γ1 Γ2 A Σ} : DynamicMutator Γ1 Γ2 A Σ :=
      fun _ _ _ _ => sout_block.

    Definition dmut_angelic {Γ1 Γ2 I A Σ} (ms : I -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 s1 => sout_angelic (fun i => ms i Σ1 ζ1 pc1 s1).
    (* Definition dmut_demonic {Γ1 Γ2 I A Σ} (ms : I -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ := *)
    (*   fun Σ1 ζ1 s1 => sout_demonic (fun i => ms i Σ1 ζ1 s1). *)
    Definition dmut_angelic_binary {Γ1 Γ2 A Σ} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 s1 => sout_angelic_binary (m1 Σ1 ζ1 pc1 s1) (m2 Σ1 ζ1 pc1 s1).
    Definition dmut_demonic_binary {Γ1 Γ2 A Σ} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 s1 => sout_demonic_binary (m1 Σ1 ζ1 pc1 s1) (m2 Σ1 ζ1 pc1 s1).
    Fixpoint dmut_angelic_list {AT D} `{Subst AT} {Γ Σ} (func : string) (msg : string) (data:D) (xs : List AT Σ) :
      DynamicMutator Γ Γ AT Σ :=
      match xs with
      | nil        => dmut_fail func msg data
      | cons x nil => dmut_pure x
      | cons x xs  => dmut_angelic_binary (dmut_pure x) (dmut_angelic_list func msg data xs)
      end.
    Fixpoint dmut_demonic_list {AT} `{Subst AT} {Γ Σ} (xs : List AT Σ) : DynamicMutator Γ Γ AT Σ :=
      match xs with
      | nil        => dmut_block
      | cons x nil => dmut_pure x
      | cons x xs  => dmut_demonic_binary (dmut_pure x) (dmut_demonic_list xs)
      end.

    Definition dmut_angelic_finite {Γ1 Γ2 A} F `{finite.Finite F} {Σ}
      (cont : F -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_bind
        (dmut_angelic_list "dmut_angelic_finite" "All branches failed" tt (finite.enum F))
        (fun (Σ' : LCtx) (ζ : Sub Σ Σ') (x : F) => dmut_sub ζ (cont x)).

    Definition dmut_demonic_finite {Γ1 Γ2 A} F `{finite.Finite F} {Σ}
      (cont : F -> DynamicMutator Γ1 Γ2 A Σ) : DynamicMutator Γ1 Γ2 A Σ :=
      dmut_bind
        (dmut_demonic_list (finite.enum F))
        (fun (Σ' : LCtx) (ζ : Sub Σ Σ') (x : F) => dmut_sub ζ (cont x)).
    Global Arguments dmut_angelic_finite {_ _ _} _ {_ _ _} _.
    Global Arguments dmut_demonic_finite {_ _ _} _ {_ _ _} _.

    Definition dmut_fresh {Γ1 Γ2 A Σ} x τ (ma : DynamicMutator Γ1 Γ2 A (Σ ▻ (x :: τ))) : DynamicMutator Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 s1 =>
        let x'  := fresh Σ1 (Some x) in
        let ζ1x := sub_snoc (sub_comp ζ1 sub_wk1) (x :: τ) (@term_var _ x' τ inctx_zero) in
        sout_demonicv (x' :: τ) (ma (Σ1 ▻ (x' :: τ)) ζ1x (subst sub_wk1 pc1) (subst sub_wk1 s1)).
    Global Arguments dmut_fresh {_ _ _ _} _ _ _.
    Definition dmut_freshtermvar {Γ Σ σ} (x : 𝑺) : DynamicMutator Γ Γ (fun Σ => Term Σ σ) Σ :=
      dmut_fresh x σ (dmut_pure (@term_var _ _ _ inctx_zero)).
    Global Arguments dmut_freshtermvar {_ _ _} _.

    Definition dmut_debug {AT DT D} `{Subst DT, Inst DT D} {Σ0 Γ1 Γ2}
      (d : forall Σ1, Sub Σ0 Σ1 -> PathCondition Σ1 -> SymbolicState Γ1 Σ1 -> DT Σ1)
      (m : DynamicMutator Γ1 Γ2 AT Σ0) : DynamicMutator Γ1 Γ2 AT Σ0 :=
      fun Σ1 ζ01 pc1 s1 => sout_debug (d Σ1 ζ01 pc1 s1) (m Σ1 ζ01 pc1 s1).

    Record DebugCall : Type :=
      MkDebugCall
        { debug_call_logic_context          : LCtx;
          debug_call_instance               : SymInstance debug_call_logic_context;
          debug_call_function_parameters    : PCtx;
          debug_call_function_result_type   : Ty;
          debug_call_function_name          : 𝑭 debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_arguments     : SymbolicLocalStore debug_call_function_parameters debug_call_logic_context;
          debug_call_function_contract      : SepContract debug_call_function_parameters debug_call_function_result_type;
          debug_call_pathcondition          : PathCondition debug_call_logic_context;
          debug_call_program_context        : PCtx;
          debug_call_localstore             : SymbolicLocalStore debug_call_program_context debug_call_logic_context;
          debug_call_heap                   : SymbolicHeap debug_call_logic_context;
        }.

    Record DebugStm : Type :=
      MkDebugStm
        { debug_stm_program_context        : PCtx;
          debug_stm_statement_type         : Ty;
          debug_stm_statement              : Stm debug_stm_program_context debug_stm_statement_type;
          debug_stm_logic_context          : LCtx;
          debug_stm_instance               : SymInstance debug_stm_logic_context;
          debug_stm_pathcondition          : PathCondition debug_stm_logic_context;
          debug_stm_localstore             : SymbolicLocalStore debug_stm_program_context debug_stm_logic_context;
          debug_stm_heap                   : SymbolicHeap debug_stm_logic_context;
        }.

    Record DebugAsn : Type :=
      MkDebugAsn
        { debug_asn_logic_context          : LCtx;
          debug_asn_instance               : SymInstance debug_asn_logic_context;
          debug_asn_pathcondition          : PathCondition debug_asn_logic_context;
          debug_asn_program_context        : PCtx;
          debug_asn_localstore             : SymbolicLocalStore debug_asn_program_context debug_asn_logic_context;
          debug_asn_heap                   : SymbolicHeap debug_asn_logic_context;
        }.

    Record SDebugCall (Σ : LCtx) : Type :=
      MkSDebugCall
        { sdebug_call_function_parameters    : PCtx;
          sdebug_call_function_result_type   : Ty;
          sdebug_call_function_name          : 𝑭 sdebug_call_function_parameters sdebug_call_function_result_type;
          sdebug_call_function_arguments     : SymbolicLocalStore sdebug_call_function_parameters Σ;
          sdebug_call_function_contract      : SepContract sdebug_call_function_parameters sdebug_call_function_result_type;
          sdebug_call_pathcondition          : PathCondition Σ;
          sdebug_call_program_context        : PCtx;
          sdebug_call_localstore             : SymbolicLocalStore sdebug_call_program_context Σ;
          sdebug_call_heap                   : SymbolicHeap Σ;
        }.

    Record SDebugStm (Σ : LCtx) : Type :=
      MkSDebugStm
        { sdebug_stm_program_context        : PCtx;
          sdebug_stm_statement_type         : Ty;
          sdebug_stm_statement              : Stm sdebug_stm_program_context sdebug_stm_statement_type;
          sdebug_stm_pathcondition          : PathCondition Σ;
          sdebug_stm_localstore             : SymbolicLocalStore sdebug_stm_program_context Σ;
          sdebug_stm_heap                   : SymbolicHeap Σ;
        }.

    Record SDebugAsn (Σ : LCtx) : Type :=
      MkSDebugAsn
        { sdebug_asn_pathcondition          : PathCondition Σ;
          sdebug_asn_program_context        : PCtx;
          sdebug_asn_localstore             : SymbolicLocalStore sdebug_asn_program_context Σ;
          sdebug_asn_heap                   : SymbolicHeap Σ;
        }.

    Global Instance SubstDebugCall : Subst SDebugCall :=
      fun (Σ0 Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) (d : SDebugCall Σ0) =>
        match d with
        | MkSDebugCall f ts c pc δ h =>
          MkSDebugCall f (subst ζ01 ts) c (subst ζ01 pc) (subst ζ01 δ) (subst ζ01 h)
        end.

    Global Instance InstDebugCall : Inst SDebugCall DebugCall :=
      {| inst Σ ι d :=
           match d with
           | MkSDebugCall f ts c pc δ h =>
             MkDebugCall ι f ts c pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugCall ι f ts c pc δ h =>
             MkSDebugCall f (lift (inst ι ts)) c (lift (inst ι pc)) (lift (inst ι δ)) (lift (inst ι h))
           end;
      |}.

    Global Instance SubstDebugStm : Subst SDebugStm :=
      fun (Σ0 Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) (d : SDebugStm Σ0) =>
        match d with
        | MkSDebugStm s pc δ h =>
          MkSDebugStm s (subst ζ01 pc) (subst ζ01 δ) (subst ζ01 h)
        end.

    Global Instance InstDebugStm : Inst SDebugStm DebugStm :=
      {| inst Σ ι d :=
           match d with
           | MkSDebugStm s pc δ h =>
             MkDebugStm s ι pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugStm s ι pc δ h =>
             MkSDebugStm s (lift (inst ι pc)) (lift (inst ι δ)) (lift (inst ι h))
           end
      |}.

    Global Instance SubstDebugAsn : Subst SDebugAsn :=
      fun (Σ0 Σ1 : LCtx) (ζ01 : Sub Σ0 Σ1) (d : SDebugAsn Σ0) =>
        match d with
        | MkSDebugAsn pc δ h =>
          MkSDebugAsn (subst ζ01 pc) (subst ζ01 δ) (subst ζ01 h)
        end.

    Global Instance InstDebugAsn : Inst SDebugAsn DebugAsn :=
      {| inst Σ ι d :=
           match d with
           | MkSDebugAsn pc δ h =>
             MkDebugAsn ι pc δ h
           end;
         lift Σ d :=
           match d with
           | MkDebugAsn ι pc δ h =>
             MkSDebugAsn (lift (inst ι pc)) (lift (inst ι δ)) (lift (inst ι h))
           end
      |}.

  End DynamicMutator.
  Bind Scope dmut_scope with DynamicMutator.

  Module DynamicMutatorNotations.

    (* Notation "'⨂' x .. y => F" := *)
    (*   (dmut_demonic (fun x => .. (dmut_demonic (fun y => F)) .. )) : dmut_scope. *)

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

  Definition dmut_state {Γ Γ' A Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicState Γ Σ' -> A Σ' * SymbolicState Γ' Σ') :
    DynamicMutator Γ Γ' A Σ.
  Proof.
    intros Σ1 ζ1 pc1 s1.
    destruct (f Σ1 ζ1 s1) as [a1 s1'].
    apply sout_pure.
    constructor.
    apply a1.
    apply s1'.
  Defined.
  Definition dmut_gets {Γ Σ A} (f : forall Σ1, Sub Σ Σ1 -> SymbolicState Γ Σ1 -> A Σ1) :
    DynamicMutator Γ Γ A Σ :=
    dmut_state (fun Σ1 ζ1 s1 => (f Σ1 ζ1 s1,s1)).
  Definition dmut_get {Γ Σ} : DynamicMutator Γ Γ (SymbolicState Γ) Σ :=
    dmut_gets (fun _ _ s => s).
  Definition dmut_modify {Γ Γ' Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicState Γ Σ' -> SymbolicState Γ' Σ') :
    DynamicMutator Γ Γ' Unit Σ :=
    dmut_state (fun Σ1 ζ1 s1 => (tt, f Σ1 ζ1 s1)).
  Definition dmut_put {Γ Γ' Σ} (s : SymbolicState Γ' Σ) : DynamicMutator Γ Γ' Unit Σ :=
    dmut_modify (fun Σ1 ζ1 _ => subst ζ1 s).

  Definition dmut_state_local {Γ Γ' A Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicLocalStore Γ Σ' -> A Σ' * SymbolicLocalStore Γ' Σ') :
    DynamicMutator Γ Γ' A Σ :=
    dmut_state (fun Σ1 ζ1 '(MkSymbolicState δ1 h1) => let (a, δ2) := f Σ1 ζ1 δ1 in (a,MkSymbolicState δ2 h1)).
  Definition dmut_gets_local {Γ Σ A} (f : forall Σ1, Sub Σ Σ1 -> SymbolicLocalStore Γ Σ1 -> A Σ1) :
    DynamicMutator Γ Γ A Σ :=
    dmut_gets (fun Σ1 ζ1 s1 => f Σ1 ζ1 (symbolicstate_localstore s1)).
  Definition dmut_get_local {Γ Σ} : DynamicMutator Γ Γ (fun Σ => SymbolicLocalStore Γ Σ) Σ :=
    dmut_gets_local (fun _ _ δ => δ).
  Definition dmut_modify_local {Γ Γ' Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicLocalStore Γ Σ' -> SymbolicLocalStore Γ' Σ') : DynamicMutator Γ Γ' Unit Σ :=
    dmut_state_local (fun Σ1 ζ1 δ1 => (tt,f Σ1 ζ1 δ1)).
  Definition dmut_put_local {Γ Γ' Σ} (δ' : SymbolicLocalStore Γ' Σ) : DynamicMutator Γ Γ' Unit Σ :=
    dmut_modify_local (fun Σ1 ζ1 _ => subst ζ1 δ').
  Definition dmut_pop_local {Γ x σ Σ} : DynamicMutator (Γ ▻ (x , σ)) Γ Unit Σ :=
    dmut_modify_local (fun Σ1 ζ1 => env_tail).
  Definition dmut_pops_local {Γ} Δ {Σ} : DynamicMutator (Γ ▻▻ Δ) Γ Unit Σ :=
    dmut_modify_local (fun Σ1 ζ1 => env_drop Δ).
  Definition dmut_push_local {Γ x σ Σ} (t : Term Σ σ) : DynamicMutator Γ (Γ ▻ (x , σ)) Unit Σ :=
    dmut_modify_local (fun Σ1 ζ1 δ1 => env_snoc δ1 (x,σ) (subst (T:= fun Σ => Term Σ σ) ζ1 t)).
  Definition dmut_pushs_local {Γ Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) : DynamicMutator Γ (Γ ▻▻ Δ) Unit Σ :=
    dmut_modify_local (fun Σ1 ζ1 δ1 => δ1 ►► subst (T := SymbolicLocalStore Δ) ζ1 δΔ).
  Definition dmut_pushpop {AT} `{Subst AT} {Γ1 Γ2 x σ Σ} (t : Term Σ σ) (d : DynamicMutator (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) :
    DynamicMutator Γ1 Γ2 AT Σ :=
    dmut_push_local t ;; dmut_bind_left d dmut_pop_local.
  Definition dmut_pushspops {AT} `{Subst AT} {Γ1 Γ2 Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) (d : DynamicMutator (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT Σ) :
    DynamicMutator Γ1 Γ2 AT Σ :=
    dmut_pushs_local δΔ ;; dmut_bind_left d (dmut_pops_local Δ).
  Definition dmut_get_heap {Γ Σ} : DynamicMutator Γ Γ SymbolicHeap Σ :=
    dmut_state (fun _ _ s1 => (symbolicstate_heap s1,s1)).
  Definition dmut_modify_heap {Γ Σ} (f : forall Σ', Sub Σ Σ' -> SymbolicHeap Σ' -> SymbolicHeap Σ') : DynamicMutator Γ Γ Unit Σ :=
    dmut_modify (fun Σ1 ζ1 '(MkSymbolicState δ1 h1) => MkSymbolicState δ1 (f Σ1 ζ1 h1)).
  Definition dmut_put_heap {Γ Σ} (h : SymbolicHeap Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_modify_heap (fun Σ1 ζ1 _ => subst ζ1 h).
  Definition dmut_eval_exp {Γ σ} (e : Exp Γ σ) {Σ} : DynamicMutator Γ Γ (fun Σ => Term Σ σ) Σ :=
    dmut_gets_local (fun Σ1 ζ1 δ1 => symbolic_eval_exp δ1 e).
  Definition dmut_eval_exps {Γ Σ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : DynamicMutator Γ Γ (fun Σ => NamedEnv (Term Σ) σs) Σ :=
    dmut_gets_local (fun Σ1 ζ1 δ1 => env_map (fun _ => symbolic_eval_exp δ1) es).

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

  Fixpoint dmut_freshen_recordpat' {N : Set} (inj__N : N -> 𝑺) {σs} {Δ : NCtx N Ty} (p : RecordPat σs Δ) {Γ Σ} :
    DynamicMutator Γ Γ (fun Σ => NamedEnv (Term Σ) σs * NamedEnv (Term Σ) Δ)%type Σ :=
    match p with
    | recordpat_nil =>
      dmut_pure (env_nil, env_nil)
    | recordpat_snoc p rf x =>
      dmut_fmap2
        (dmut_freshen_recordpat' inj__N p)
        (dmut_freshtermvar (inj__N x))
        (fun _ _ '(ts__σs, ts__Δ) t__x => (env_snoc ts__σs (rf::_) t__x, env_snoc ts__Δ (x::_) t__x))
    end.

  Definition dmut_freshen_recordpat {N : Set} (inj__N : N -> 𝑺) {R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) {Γ Σ} :
    DynamicMutator Γ Γ (fun Σ => Term Σ (ty_record R) * NamedEnv (Term Σ) Δ)%type Σ :=
    dmut_fmap
      (dmut_freshen_recordpat' inj__N p)
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
      dmut_freshen_recordpat 𝑿to𝑺 p
    end.

  (* Add the provided formula to the path condition. *)
  Definition dmut_assume_formula {Γ Σ} (fml : Formula Σ) : DynamicMutator Γ Γ Unit Σ :=
    fun Σ1 ζ1 pc1 s1 =>
      sout_bind pc1
        (sout_assume_formula pc1 (subst ζ1 fml))
        (fun Σ2 ζ12 pc2 v => sout_pure {| dmutres_result_value := v; dmutres_result_state := subst ζ12 s1 |}).

  Definition dmut_assume_term {Γ Σ} (t : Term Σ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_assume_formula (formula_bool t).
  Definition dmut_assume_exp {Γ Σ} (e : Exp Γ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_eval_exp e >>= fun _ _ => dmut_assume_term.
  Definition dmut_assume_prop {Γ Σ} (P : abstract_named Lit Σ Prop) : DynamicMutator Γ Γ Unit Σ :=
    dmut_assume_formula (formula_prop (sub_id Σ) P).
  Definition dmut_assume_formulas {Γ Σ} (fmls : list (Formula Σ)) : DynamicMutator Γ Γ Unit Σ :=
    fold_right (fun fml => dmut_bind_right (dmut_assume_formula fml)) (dmut_pure tt) fmls.

  Definition dmut_assert_formula {Γ Σ} (fml : Formula Σ) : DynamicMutator Γ Γ Unit Σ :=
    fun Σ1 ζ1 pc1 s1 =>
      sout_bind pc1
        (sout_assert_formula
           {| msg_function        := "dmut_assert_formula";
              msg_message         := "Proof obligation";
              msg_program_context := Γ;
              msg_pathcondition   := pc1;
              msg_localstore      := symbolicstate_localstore s1;
              msg_heap            := symbolicstate_heap s1;
           |}
           pc1 (subst ζ1 fml))
        (fun Σ2 ζ12 pc2 v => sout_pure {| dmutres_result_value := v; dmutres_result_state := subst ζ12 s1 |}).

  Definition dmut_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) : DynamicMutator Γ Γ Unit Σ :=
    fold_right (fun fml => dmut_bind_right (dmut_assert_formula fml)) (dmut_pure tt) fmls.
  Definition dmut_assert_term {Γ Σ} (t : Term Σ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_assert_formula (formula_bool t).
  Definition dmut_assert_exp {Γ Σ} (e : Exp Γ ty_bool) : DynamicMutator Γ Γ Unit Σ :=
    dmut_eval_exp e >>= fun _ _ t => dmut_assert_term t.
  Definition dmut_produce_chunk {Γ Σ} (c : Chunk Σ) : DynamicMutator Γ Γ Unit Σ :=
    dmut_modify_heap (fun _ ζ => cons (subst ζ c)).
  Definition dmut_consume_chunk {Γ Σ} (c : Chunk Σ) : DynamicMutator Γ Γ Unit Σ :=
     dmut_get_heap >>= fun Σ1 ζ1 h1 =>
     dmut_angelic_list "dmut_consume_chunk" "Empty extraction" c
       (extract_chunk_eqb (subst ζ1 c) h1) >>= fun Σ2 ζ2 '(Δpc2 , h2) =>
     dmut_assert_formulas Δpc2 ;;
     dmut_put_heap h2.

  Definition dmut_leakcheck {Γ Σ} : DynamicMutator Γ Γ Unit Σ :=
    dmut_get_heap >>= fun _ _ h =>
    match h with
    | nil => dmut_pure tt
    | _   => dmut_fail "dmut_leakcheck" "Heap leak" h
    end.

  Definition dmut_match_enum {AT E} {Γ1 Γ2 Σ} (t : Term Σ (ty_enum E))
    (d : 𝑬𝑲 E -> DynamicMutator Γ1 Γ2 AT Σ) : DynamicMutator Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_lit t' with
      | Some k => d k Σ1 ζ01
      | None => dmut_demonic_finite
                  (𝑬𝑲 E)
                  (fun k => dmut_assume_formula (formula_eq t' (term_enum E k));; dmut_sub ζ01 (d k)) _ (sub_id Σ1)
      end.

  Definition dmut_match_sum {AT} {Γ1 Γ2 Σ} (x y : 𝑺) {σ τ} (t : Term Σ (ty_sum σ τ))
    (dinl : DynamicMutator Γ1 Γ2 AT (Σ ▻ (x :: σ)))
    (dinr : DynamicMutator Γ1 Γ2 AT (Σ ▻ (y :: τ))) :
    DynamicMutator Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
      match term_get_sum (subst (T := fun Σ => Term Σ _) ζ01 t) with
      | Some (inl tl) => dinl Σ1 (sub_snoc ζ01 (x :: σ) tl)
      | Some (inr tr) => dinr Σ1 (sub_snoc ζ01 (y :: τ) tr)
      | None =>
        dmut_demonic_binary
          (dmut_fresh x σ
             (dmut_assume_formula
                (formula_eq
                   (subst (T := fun Σ => Term Σ _) sub_wk1 t)
                   (@term_inl _ σ τ (@term_var _ _ _ inctx_zero))) ;;
              dinl))
          (dmut_fresh y τ
             (dmut_assume_formula
                (formula_eq
                   (subst (T := fun Σ => Term Σ _) sub_wk1 t)
                   (@term_inr _ σ τ (@term_var _ _ _ inctx_zero))) ;;
              dinr)) ζ01
      end.

  Definition dmut_match_pair {AT} {Γ1 Γ2 Σ} (x y : 𝑺) {σ τ} (s : Term Σ (ty_prod σ τ))
    (d : DynamicMutator Γ1 Γ2 AT (Σ ▻ (x :: σ) ▻ (y :: τ))) : DynamicMutator Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
    match term_get_pair (subst (T := fun Σ => Term Σ _) ζ01 s) with
    | Some (tl,tr) => d Σ1 (sub_snoc (sub_snoc ζ01 (x :: σ) tl) (y :: τ) tr)
    | None =>
      dmut_fresh x σ (dmut_fresh y τ
        (dmut_assume_formula
           (formula_eq
              (subst (T := fun Σ => Term Σ _) (sub_comp sub_wk1 sub_wk1) s)
              (term_binop
                 binop_pair
                 (@term_var _ x σ (inctx_succ inctx_zero))
                 (@term_var _ y τ inctx_zero))) ;;
         d))
        Σ1 ζ01
    end.

  Definition dmut_match_record {AT R} {Γ1 Γ2 Σ Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) (t : Term Σ (ty_record R))
    (d : DynamicMutator Γ1 Γ2 AT (Σ ▻▻ Δ)) : DynamicMutator Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
    match term_get_record (subst (T := fun Σ => Term Σ _) ζ01 t) with
    | Some ts =>
      let ζ__R := record_pattern_match p ts in
      d Σ1 (ζ01 ►► ζ__R)
    | None =>
      (dmut_freshen_recordpat id p >>= fun _ ζ '(t__p,ζ__R) =>
      dmut_assume_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ t) t__p) ;;
      dmut_sub (ζ ►► ζ__R) d) ζ01
    end.

  Fixpoint dmut_produce {Γ Σ} (asn : Assertion Σ) : DynamicMutator Γ Γ Unit Σ :=
    match asn with
    | asn_formula fml => dmut_assume_formula fml
    | asn_chunk c     => dmut_produce_chunk c
    | asn_if b a1 a2  => (dmut_assume_term b ;; dmut_produce a1) ⊗
                         (dmut_assume_term (term_not b) ;; dmut_produce a2)
    | asn_match_enum E t alts =>
      dmut_match_enum t (fun k => dmut_produce (alts k))
    | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
      dmut_match_sum s (dmut_produce alt_inl) (dmut_produce alt_inr)
    | asn_match_list s alt_nil xh xt alt_cons =>
      dmut_fail "dmut_produce" "Not implemented" asn
    | asn_match_pair s xl xr rhs =>
      dmut_match_pair s (dmut_produce rhs)
    | asn_match_tuple s p rhs =>
      dmut_fail "dmut_produce" "Not implemented" asn
    | asn_match_record R s p rhs =>
      dmut_match_record p s (dmut_produce rhs)
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      match term_get_union s with
      | Some (existT K ts) =>
        dmut_fail "dmut_produce" "Not implemented" asn
      | None =>
        dmut_fail "dmut_produce" "Not implemented" asn
      end
    | asn_sep a1 a2   => dmut_produce a1 ;; dmut_produce a2
    | asn_exist ς τ a => dmut_fresh ς τ (dmut_produce a)
    | asn_debug =>
      dmut_debug
        (fun Σ1 ζ01 pc1 s1 =>
           {| sdebug_asn_pathcondition := pc1;
              sdebug_asn_program_context := Γ;
              sdebug_asn_localstore := symbolicstate_localstore s1;
              sdebug_asn_heap := symbolicstate_heap s1
           |})
        (dmut_pure tt)
    end.

  Fixpoint dmut_consume {Γ Σ} (asn : Assertion Σ) : DynamicMutator Γ Γ Unit Σ :=
    match asn with
    | asn_formula fml => dmut_assert_formula fml
    | asn_chunk c     => dmut_consume_chunk c
    | asn_if b a1 a2  => (dmut_assume_term b ;; dmut_consume a1) ⊗
                         (dmut_assume_term (term_not b) ;; dmut_consume a2)
    | asn_match_enum E t alts =>
      dmut_match_enum t (fun k => dmut_consume (alts k))
    | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
      dmut_match_sum s (dmut_consume alt_inl) (dmut_consume alt_inr)
    | asn_match_list s alt_nil xh xt alt_cons =>
      dmut_fail "dmut_consume" "Not implemented" asn
    | asn_match_pair s xl xr rhs =>
      dmut_match_pair s (dmut_consume rhs)
    | asn_match_tuple s p rhs =>
      dmut_fail "dmut_consume" "Not implemented" asn
    | asn_match_record R s p rhs =>
      dmut_match_record p s (dmut_consume rhs)
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      dmut_fail  "dmut_consume" "Not implemented" asn
    | asn_sep a1 a2   => dmut_consume a1 ;; dmut_consume a2
    | asn_exist ς τ a =>
      ⨁ t : Term Σ τ =>
      dmut_sub (sub_snoc (sub_id _) (ς , τ) t) (dmut_consume a)
    | asn_debug =>
      dmut_debug
        (fun Σ1 ζ01 pc1 s1 =>
           {| sdebug_asn_pathcondition := pc1;
              sdebug_asn_program_context := Γ;
              sdebug_asn_localstore := symbolicstate_localstore s1;
              sdebug_asn_heap := symbolicstate_heap s1
           |})
        (dmut_pure tt)
    end.

  Definition dmut_call {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σr :=
    match contract with
    | MkSepContract _ _ Σe δ req result ens =>
      ⨁ ξ : Sub Σe Σr =>
      dmut_assert_formulas (formula_eqs ts (subst ξ δ)) ;;
      dmut_sub ξ
        (dmut_consume req ;;
         dmut_fresh result τ
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
      dmut_pushpop t1 (dmut_exec s2)
    | stm_block δ s =>
      dmut_pushspops (lift δ) (dmut_exec s)
    | stm_assign x s =>
      t <- dmut_exec s ;;
      dmut_modify_local (fun _ ζ δ => δ ⟪ x ↦ subst ζ t ⟫)%env ;;
      dmut_pure t
    | stm_call f es =>
      ts <- dmut_eval_exps es ;;
      match CEnv f with
      | Some c => dmut_call c ts
      | None   => dmut_fail "dmut_exec" "Function call without contract" (f,ts)
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
      dmut_assume_term t ;;
      dmut_exec k
    | stm_fail _ _ =>
      dmut_block
    | stm_match_list e s1 xh xt s2 =>
      t <- dmut_eval_exp e ;;
      (dmut_assume_formula
         (formula_eq t (term_lit (ty_list _) nil));;
       dmut_exec s1) ⊗
      (dmut_fresh
         (𝑿to𝑺 xh) _ (dmut_fresh (𝑿to𝑺 xt) _
         (dmut_assume_formula
            (formula_eq (subst (sub_comp sub_wk1 sub_wk1) t)
                        (term_binop binop_cons (@term_var _ _ _ (inctx_succ inctx_zero)) (@term_var _ _ _ inctx_zero)));;
          dmut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
          dmut_push_local (@term_var _ _ _ inctx_zero);;
          t2 <- dmut_exec s2 ;;
          dmut_pop_local ;;
          dmut_pop_local ;;
          dmut_pure t2)))
    | stm_match_sum e xinl s1 xinr s2 =>
      t <- dmut_eval_exp e ;;
      dmut_match_sum t
        (dmut_pushpop (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero) (dmut_exec s1))
        (dmut_pushpop (@term_var _ (𝑿to𝑺 xinr) _ inctx_zero) (dmut_exec s2))
    | stm_match_pair e xl xr s =>
      t <- dmut_eval_exp e ;;
      dmut_match_pair
        t
        (dmut_pushspops
           (env_snoc (env_snoc env_nil
              (xl :: _) (@term_var _ (𝑿to𝑺 xl) _ (inctx_succ inctx_zero)))
              (xr :: _) (@term_var _ (𝑿to𝑺 xr) _ inctx_zero))
           (dmut_exec s))
    | stm_match_enum E e alts =>
      t <- dmut_eval_exp e ;;
      dmut_match_enum t (fun K => dmut_exec (alts K))
    | stm_match_tuple e p s =>
      dmut_fail "dmut_exec" "stm_match_tuple not implemented" tt
    | stm_match_union U e alt__ctx alt__pat =>
      dmut_fail "dmut_exec" "stm_match_union not implemented" tt
    | @stm_match_record _ _ R Δ e p rhs =>
      t <- dmut_eval_exp e ;;
      match term_get_record t with
      | Some ts =>
        let ζ__R := record_pattern_match p ts in
        dmut_pushspops ζ__R (dmut_exec rhs)
      | None =>
        dmut_freshen_recordpat 𝑿to𝑺 p >>= fun _ ζ '(t__p,ζ__R) =>
        dmut_assume_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ t) t__p) ;;
        dmut_pushspops ζ__R (dmut_exec rhs)
      end
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
      dmut_fail "dmut_exec" "stm_bind not supported" tt
    | stm_debugk k =>
      dmut_debug
        (fun Σ1 ζ01 pc1 s1 =>
           {| sdebug_stm_statement := k;
              sdebug_stm_pathcondition := pc1;
              sdebug_stm_localstore := symbolicstate_localstore s1;
              sdebug_stm_heap := symbolicstate_heap s1
           |})
        (dmut_exec k)
    end.

  Definition dmut_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : DynamicMutator Δ Δ Unit (sep_contract_logic_variables c) :=
    match c with
    | MkSepContract _ _ Σ δ req result ens =>
        dmut_produce req ;;
        dmut_exec s      >>= fun Σ1 ζ1 t =>
        dmut_sub (sub_snoc ζ1 (result,τ) t) (dmut_consume ens)
        (* dmut_leakcheck *)
    end.

  Definition dmut_contract_outcome {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) :
    SymOutcome Unit (sep_contract_logic_variables c) :=
    let δ    := sep_contract_localstore c in
    let s__sym := symbolicstate_initial δ in
    sout_bind nil (dmut_contract c s (sub_id _) nil s__sym) (fun _ _ _ _ => sout_block).

  Definition ValidContractNoEvar (Δ : PCtx) (τ : Ty) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ForallNamed (fun ι => sout_safe (sep_contract_logic_variables c) ι (dmut_contract_outcome c body)).

  Section CallerContext.

    Context {Γ : PCtx}.

    Definition dmut_consume_chunk_evar {Σe Σr} (c : Chunk Σe) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr.
      refine (dmut_get_heap >>= fun Σ1 ζ1 h1 => _).
      refine (let L1 := subst ζ1 L in _).
      eapply dmut_bind.
      apply (dmut_angelic_list
        "dmut_consume_chunk_evar"
        "Empty extraction"
        {| evarerror_env := L1;
           evarerror_data := c;
        |}
        (extract_chunk c h1 L1)).
      intros Σ2 ζ2 [L2 h2].
      refine (dmut_put_heap h2;; dmut_pure L2).
    Defined.

    (* This function tries to assert the equality between the terms `te` from
       a callee context and `tr` from the caller context. The callee context
       variables are all evars and if possible, it will fill in evars that are
       strictly necessary for the assertion to be true. *)
    Definition dmut_assert_term_eq_evar {Σe Σr σ} (te : Term Σe σ) (tr : Term Σr σ) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr :=
      (* Make sure we get the up to date substitution. *)
      dmut_pure tt >>= fun Σr1 ζ1 _ =>
      let tr1 := subst (T := fun Σ => Term Σ _) ζ1 tr in
      let L1  := subst ζ1 L in
      (* Try to fully match te against tr1, potentially filling in some evars. *)
      match match_term te tr1 L1 with
      | Some e => dmut_pure e
      | None =>
        (* The match failed. See if all evars in te are already known.*)
        match eval_term_evar L1 te with
        | Some te1 =>
          (* All evars are known. So assert the equality between the terms in
             the caller context. *)
          dmut_assert_formula (formula_eq te1 tr1);; dmut_pure L1
        | None =>
          (* Give up. This is currently missing some corner cases where a
             sub-term of te would already constrain all appearing evars, but
             which can't be fully unified with tr. match_term could be
             augmented to also handle this kind of case. *)
          dmut_fail
            "dmut_assert_term_eq_evar"
            "Uninstantiated evars variable"
            {| evarerror_env := L;
               evarerror_data := (te,tr)
            |}
        end
      end.

    Equations(noeqns) dmut_assert_namedenv_eq_evar {X Σe Σr σs} (te : NamedEnv (X:=X) (Term Σe) σs) (tr : NamedEnv (Term Σr) σs) :
      EvarEnv Σe Σr -> DynamicMutator Γ Γ (EvarEnv Σe) Σr :=
      dmut_assert_namedenv_eq_evar env_nil env_nil := dmut_pure;
      dmut_assert_namedenv_eq_evar (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) :=
        fun L => dmut_assert_namedenv_eq_evar E1 E2 L >>= fun _ ζ =>
                 dmut_assert_term_eq_evar t1 (subst (T := fun Σ => Term Σ _) ζ t2).

    Definition dmut_consume_formula_evar {Σe Σr} (fml : Formula Σe) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr :=
      match fml with
      | formula_bool b =>
        match eval_term_evar L b with
        | Some b' => dmut_assert_term b';; dmut_pure L
        | None    => dmut_fail
                       "dmut_consume_formula_evar"
                       "Uninstantiated evars when consuming formula"
                       {| evarerror_env := L;
                          evarerror_data := fml
                       |}
        end
      | formula_prop ζ P =>
        match evarenv_to_option_sub L with
        | Some ζ' => dmut_assert_formula (formula_prop (sub_comp ζ ζ') P);; dmut_pure L
        | None   => dmut_fail
                      "dmut_consume_formula_evar"
                      "Uninstantiated evars when consuming formula"
                      {| evarerror_env := L;
                         evarerror_data := fml
                      |}
        end
      | formula_eq t1 t2 =>
        match eval_term_evar L t1, eval_term_evar L t2 with
        | Some t1', Some t2' => dmut_assert_formula (formula_eq t1' t2') ;; dmut_pure L
        | Some t1', None     => dmut_assert_term_eq_evar t2 t1' L
        | None    , Some t2' => dmut_assert_term_eq_evar t1 t2' L
        | _       , _        => dmut_fail
                                  "dmut_consume_formula_evar"
                                  "Uninstantiated evars when consuming formula"
                                  {| evarerror_env := L;
                                     evarerror_data := fml
                                  |}
        end
      | formula_neq t1 t2 =>
        match eval_term_evar L t1, eval_term_evar L t2 with
        | Some t1', Some t2' => dmut_assert_formula (formula_neq t1' t2') ;; dmut_pure L
        (* | Some t1', None     => dmut_assert_term_neq_evar t2 t1' L *)
        (* | None    , Some t2' => dmut_assert_term_neq_evar t1 t2' L *)
        | _       , _        => dmut_fail
                                  "dmut_consume_formula_evar"
                                  "Uninstantiated evars when consuming formula"
                                  {| evarerror_env := L;
                                     evarerror_data := fml
                                  |}
        end
      end.

    Fixpoint dmut_consume_evar {Σe Σr} (asn : Assertion Σe) (L : EvarEnv Σe Σr) : DynamicMutator Γ Γ (EvarEnv Σe) Σr :=
      match asn with
      | asn_formula fml => dmut_consume_formula_evar fml L
      | asn_chunk c => dmut_consume_chunk_evar c L
      | asn_if b a1 a2 =>
        match eval_term_evar L b with
        | Some b' => (dmut_assert_term b';; dmut_consume_evar a1 L)
                       ⊕
                     (dmut_assert_term (term_not b');; dmut_consume_evar a2 L)
        | None    => dmut_fail
                       "dmut_consume_evar"
                       "Uninstantiated evars when consuming assertion"
                       {| evarerror_env := L;
                          evarerror_data := asn
                       |}
        end
      | asn_match_enum E k alts =>
        match eval_term_evar L k with
        | Some k1 =>
          dmut_angelic_finite
            (𝑬𝑲 E)
            (fun k2 =>
               dmut_assert_formula (formula_eq k1 (term_enum E k2)) ;;
               dmut_consume_evar (alts k2) L)
        | None => dmut_fail
                    "dmut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_sum σ τ scr xl alt_inl xr alt_inr =>
        match eval_term_evar L scr with
        | Some s =>
          match term_get_sum s with
          | Some (inl t) =>
            let Lxl := L ► (xl∶σ ↦ Some t) in
            Lxl' <- dmut_consume_evar alt_inl Lxl ;;
            dmut_pure (env_tail Lxl')
          | Some (inr t) =>
            let Lxr := L ► (xr∶τ ↦ Some t) in
            Lxr' <- dmut_consume_evar alt_inr Lxr ;;
            dmut_pure (env_tail Lxr')
          | None =>
            dmut_angelic_binary
              (let Lxl := L ► (xl∶σ ↦ None) in
                dmut_consume_evar alt_inl Lxl >>= fun _ ζ Lxl' =>
                  match env_unsnoc Lxl' with
                  | (L' , Some t) =>
                    (* TODO(2.0): This assert should move before the *)
                    (* consumption of the alternative. *)
                    (dmut_assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ s) (term_inl t)) ;;
                     dmut_pure L')
                  | (_ , None) =>
                    dmut_fail
                      "dmut_consume_evar"
                      "Uninstantiated evars when consuming assertion"
                      {| evarerror_env := Lxl;
                         evarerror_data := alt_inl
                      |}
                  end)
              (let Lxr := L ► (xr∶τ ↦ None) in
                dmut_consume_evar alt_inr Lxr >>= fun _ ζ Lxr' =>
                  match env_unsnoc Lxr' with
                  | (L' , Some t) =>
                    (* TODO(2.0): This assert should move before the *)
                    (* consumption of the alternative. *)
                    (dmut_assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ s) (term_inr t)) ;;
                     dmut_pure L')
                  | (_ , None) =>
                    dmut_fail
                      "dmut_consume_evar"
                      "Uninstantiated evars when consuming assertion"
                      {| evarerror_env := Lxr;
                         evarerror_data := alt_inr
                      |}
                  end)
          end
        | _ => dmut_fail
                 "dmut_consume_evar"
                 "Uninstantiated evars when consuming assertion"
                 {| evarerror_env := L;
                    evarerror_data := asn
                 |}
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        dmut_fail "dmut_consume_evar" "Not implemented" asn
      | asn_match_pair scr xl xr rhs =>
        match eval_term_evar L scr with
        | Some s =>
          match term_get_pair s with
          | Some (tl, tr) =>
            let Lrhs := L ► (xl∶_ ↦ Some tl) ► (xr∶_ ↦ Some tr) in
            Lrhs' <- dmut_consume_evar rhs Lrhs ;;
            dmut_pure (env_tail (env_tail Lrhs'))
          | None =>
            dmut_fail "dmut_consume_evar" "Not implemented" asn
          end
        | None => dmut_fail
                    "dmut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_tuple s p rhs =>
        dmut_fail "dmut_consume_evar" "Not implemented" asn
      | asn_match_record R scr p rhs =>
        match eval_term_evar L scr with
        | Some s =>
          match term_get_record s with
          | Some ts  =>
            let ζ__R := record_pattern_match p ts in
            let LR := L ►► env_map (fun _ t => Some t) ζ__R in
            LR' <- dmut_consume_evar rhs LR ;;
            dmut_pure (env_drop _ LR')
          | None =>
            dmut_fail "dmut_consume_evar" "Not implemented" asn
          end
        | None => dmut_fail
                    "dmut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        dmut_fail  "dmut_consume_evar" "Not implemented" asn
      | asn_sep a1 a2 =>
        dmut_consume_evar a1 L >>= fun _ _ => dmut_consume_evar a2
      | asn_exist ς τ a =>
        (* Dynamically allocate a new evar ς in the EvarEnv. *)
        let Lς := L ► (ς∶τ ↦ None) in
        dmut_consume_evar a Lς >>= fun _ _ Lς' =>
        (* Split off the last evar again. *)
        match env_unsnoc Lς' with
        | (L' , Some _) =>
          (* ς has been instantiated during execution. So we just return the
          final EvarEnv with ς stripped off. *)
          dmut_pure L'
        | (_  , None)   =>
          (* During execution the evar ς was never instantiated, so fail. *)
          dmut_fail
            "dmut_consume_evar"
            "Uninstantiated evars when consuming assertion"
            {| evarerror_env := L;
               evarerror_data := asn
            |}
        end
      | asn_debug =>
        dmut_debug
          (fun Σ1 ζ01 pc1 s1 =>
             {| sdebug_asn_pathcondition := pc1;
                sdebug_asn_program_context := Γ;
                sdebug_asn_localstore := symbolicstate_localstore s1;
                sdebug_asn_heap := symbolicstate_heap s1
             |})
          (dmut_pure L)
      end.

  End CallerContext.

  Definition dmut_call_evar {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σr :=
    match contract with
    | MkSepContract _ _ Σe δ req result ens =>
       dmut_consume_evar req (create_evarenv Σe Σr) >>= fun Σr1 ζ1 E1 =>
       dmut_assert_namedenv_eq_evar δ (env_map (fun _ => subst (T := fun Σ => Term Σ _) ζ1) ts) E1 >>= fun Σr2 ζ2 E2 =>
       match evarenv_to_option_sub E2 with
       | Some ξ => dmut_sub ξ (dmut_fresh result τ (dmut_produce ens ;; dmut_pure (@term_var _ result _ inctx_zero)))
       | None => dmut_fail
                   "dmut_call_evar"
                   "Uninstantiated evars after consuming precondition"
                   {| evarerror_env := E2;
                      evarerror_data := (contract,ts)
                   |}
       end
    end.

  Section WithConfig.

    Variable cfg : Config.

    Definition dmut_call_evar_debug {Γ Δ τ Σr} (f : 𝑭 Δ τ) (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : DynamicMutator Γ Γ (fun Σ => Term Σ τ) Σr :=
      fun Σ1 ζ1 pc1 s1 =>
        let o := dmut_call_evar contract ts ζ1 pc1 s1 in
        if config_debug_function cfg f
        then sout_debug
               {| sdebug_call_function_parameters    := Δ;
                  sdebug_call_function_result_type   := τ;
                  sdebug_call_function_name          := f;
                  sdebug_call_function_arguments     := subst ζ1 ts;
                  sdebug_call_function_contract      := contract;
                  sdebug_call_pathcondition          := pc1;
                  sdebug_call_program_context        := Γ;
                  sdebug_call_localstore             := symbolicstate_localstore s1;
                  sdebug_call_heap                   := symbolicstate_heap s1;
               |}
               o
        else o.

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
        ts <- dmut_eval_exps es ;;
        match CEnv f with
        | Some c => dmut_call_evar_debug f c ts
        | None   => dmut_fail "dmut_exec_evar" "Function call without contract" (f,ts)
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
        dmut_assume_term t ;;
        dmut_exec_evar k
      | stm_fail _ _ =>
        dmut_block
      | stm_match_list e s1 xh xt s2 =>
        t <- dmut_eval_exp e ;;
        (dmut_assume_formula
           (formula_eq t (term_lit (ty_list _) nil));;
         dmut_exec_evar s1) ⊗
        (dmut_fresh
           (𝑿to𝑺 xh) _ (dmut_fresh (𝑿to𝑺 xt) _
           (dmut_assume_formula
              (formula_eq (subst (T := fun Σ => Term Σ _) (sub_comp sub_wk1 sub_wk1) t)
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
          dmut_fresh _ _
            (dmut_assume_formula
               (formula_eq (subst (T := fun Σ => Term Σ _) sub_wk1 t__sc) (term_inl (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero)));;
             dmut_push_local (@term_var _ (𝑿to𝑺 xinl) _ inctx_zero);;
             dmut_bind_left (dmut_exec_evar s1) dmut_pop_local) ⊗
          dmut_fresh _ _
            (dmut_assume_formula
               (formula_eq (subst (T := fun Σ => Term Σ _) sub_wk1 t__sc) (term_inr (@term_var _ (𝑿to𝑺 xinr) _ inctx_zero)));;
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
          dmut_fresh (𝑿to𝑺 xl) _ (dmut_fresh (𝑿to𝑺 xr) _
            (dmut_assume_formula
               (formula_eq
                  (subst (T := fun Σ => Term Σ _) (sub_comp sub_wk1 sub_wk1) t__sc)
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
            dmut_assume_formula (formula_eq t__pat (subst (T := fun Σ => Term Σ _) ζ2 t__field));;
            dmut_pushs_local δ__Δ;;
            t__rhs <- dmut_sub ζ2 (dmut_exec_evar (alt__rhs K));;
            dmut_pops_local _;;
            dmut_pure t__rhs)
        | None =>
          dmut_demonic_finite
            (𝑼𝑲 U)
            (fun K =>
               dmut_freshen_pattern (alt__pat K) >>= (fun Σ2 ζ2 '(t__pat, δ__Δ) =>
               dmut_assume_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ2 t__sc) (term_union U K t__pat));;
               dmut_pushs_local δ__Δ;;
               t__rhs <- dmut_sub ζ2 (dmut_exec_evar (alt__rhs K));;
               dmut_pops_local _;;
               dmut_pure t__rhs))
        end
      | stm_match_record R e p s =>
        ts <- dmut_pair (dmut_eval_exp e) (dmut_freshen_recordpat 𝑿to𝑺 p) ;;
        let '(t__sc,(t__p,t__Δ)) := ts in
        dmut_assume_formula (formula_eq t__sc t__p) ;;
        dmut_pushs_local t__Δ ;;
        t <- dmut_exec_evar s ;;
        dmut_pops_local _ ;;
        dmut_pure t
      | stm_read_register reg =>
        let x := fresh Σ None in
        dmut_consume_chunk_evar (chunk_ptsreg reg (@term_var [(x,_)] x _ inctx_zero)) [None]%arg >>= fun Σ1 _ E1 =>
        match snd (env_unsnoc E1) with
        | Some t => dmut_produce_chunk (chunk_ptsreg reg t) ;; dmut_pure t
        (* Extracting the points to chunk should never fail here. Because there is exactly one binding
           in the ghost environment and the chunk matching will always instantiate it. *)
        | None => dmut_fail "dmut_exec_evar" "You have found a unicorn." tt
        end
      | stm_write_register reg e =>
        let x := fresh Σ None in
        tnew <- dmut_eval_exp e ;;
        dmut_consume_chunk_evar (chunk_ptsreg reg (@term_var _ x _ inctx_zero)) [None]%arg ;;
        dmut_produce_chunk (chunk_ptsreg reg tnew) ;;
        dmut_pure tnew
      | stm_bind _ _ =>
        dmut_fail "dmut_exec_evar" "stm_bind not supported" tt
      | stm_debugk k =>
        dmut_debug
          (fun Σ1 ζ01 pc1 s1 =>
             {| sdebug_stm_statement := k;
                sdebug_stm_pathcondition := pc1;
                sdebug_stm_localstore := symbolicstate_localstore s1;
                sdebug_stm_heap := symbolicstate_heap s1
             |})
          (dmut_exec_evar k)
      end.

    Definition dmut_contract_evar {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : DynamicMutator Δ Δ Unit (sep_contract_logic_variables c) :=
      match c with
      | MkSepContract _ _ Σ δ req result ens =>
          dmut_produce req ;;
          dmut_exec_evar s      >>= fun Σ1 ζ1 t =>
          dmut_consume_evar ens (subst (sub_snoc ζ1 (result,τ) t) (create_evarenv_id _)) ;;
          (* dmut_leakcheck *)
          dmut_block
      end.

    (* Definition dmut_contract_evar {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) : *)
    (*   Stm Δ τ -> SymOutcome Message Unit (sep_contract_logic_variables c) := *)
    (*   match c with *)
    (*   | MkSepContract _ _ Σ δ req result ens => *)
    (*     fun s => *)
    (*       let mut := (dmut_produce req ;; *)
    (*                   dmut_exec_evar s      >>= fun Σ1 ζ1 t => *)
    (*                   dmut_consume_evar ens (subst (sub_snoc ζ1 (result::τ) t) (create_evarenv_id _)) ;; *)
    (*                   dmut_pure tt (* dmut_leakcheck *))%dmut in *)
    (*       let out := mut Σ (sub_id Σ) nil (symbolicstate_initial δ) in *)
    (*       sout_bind nil out (fun _ _ _ _ => sout_block (A:=Unit)) *)
    (*   end. *)

    Definition dmut_contract_evar_outcome {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) :
      SymOutcome
        (DynamicMutatorResult Δ Unit)
        (sep_contract_logic_variables c) :=
      let δ    := sep_contract_localstore c in
      dmut_contract_evar c s (sub_id _) nil (symbolicstate_initial δ).

    Definition ValidContractWithConfig {Δ τ}
      (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (sout_prune (dmut_contract_evar_outcome c body)).

  End WithConfig.

  Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContractWithConfig default_config c body.

  (* Transitional old name. *)
  Definition ValidContractDynMut {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContract c body.

  Definition sout_ok_opaque {AT Σ} (o : SymOutcome AT Σ) : Prop :=
    is_true (sout_ok o).
  Global Arguments sout_ok_opaque {AT} Σ o.
  Global Opaque sout_ok_opaque.

  Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    is_true (sout_ok (sout_prune (dmut_contract_evar_outcome default_config c body))).

  (* Transitional old name. *)
  Definition ValidContractDynMutReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContractReflect c body.

  Lemma dynmutevarreflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
    ValidContractReflect c body ->
    ValidContract c body.
  Proof.
    (* intros H. *)
    (* apply (outcome_ok_spec _ (fun _ => True)) in H. *)
    (* now rewrite outcome_satisfy_bind in H. *)
  Admitted.

End Mutators.
