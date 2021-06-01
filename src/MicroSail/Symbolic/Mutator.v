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
Delimit Scope smut_scope with smut.

Module Mutators
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (assertkit : AssertionKit termkit progkit)
       (symcontractkit : SymbolicContractKit termkit progkit assertkit).

  Export symcontractkit.

  Declare Scope modal.
  Delimit Scope modal with modal.

  Import Entailment.

  Record World : Type :=
    MkWorld
      { wctx :> LCtx;
        wco  : PathCondition wctx;
      }.

  Record Acc (w1 w2 : World) : Type :=
    MkAcc
      { wsub :> Sub w1 w2;
        (* went :  wco w2 ⊢ subst (wco w1) wsub; *)
      }.

  Notation "w1 ⊒ w2" := (Acc w1 w2) (at level 80).

  Definition went {w0 w1} (ω01 : w0 ⊒ w1) : Prop :=
    wco w1 ⊢ subst (wco w0) (wsub ω01).

  Local Obligation Tactic := idtac.
  Definition wrefl {w} : w ⊒ w :=
    {| wsub := sub_id w |}.
  (* Next Obligation. *)
  (*   intros ?. now rewrite subst_sub_id. *)
  (* Qed. *)

  Lemma went_wrefl {w} :
    went (wrefl (w := w)).
  Proof.
    intros ι. cbn.
    now rewrite subst_sub_id.
  Qed.

  Definition wtrans {w0 w1 w2} : w0 ⊒ w1 -> w1 ⊒ w2 -> w0 ⊒ w2 :=
    fun ω01 ω12 => {| wsub := subst (T := Sub _) ω01 ω12 |}.
  (* Next Obligation. *)
  (*   intros *. *)
  (*   rewrite subst_sub_comp. *)
  (*   intros ι2 Hpc2. *)
  (*   rewrite inst_subst. *)
  (*   apply (went ω01 (inst (T := Sub _) ω12 ι2)). *)
  (*   rewrite <- inst_subst. *)
  (*   apply (went ω12 ι2 Hpc2). *)
  (* Defined. *)

  Lemma went_wtrans {w0 w1 w2} {ω01 : w0 ⊒ w1} {ω12 : w1 ⊒ w2} :
    went ω01 -> went ω12 -> went (wtrans ω01 ω12).
  Proof.
    intros Hω01 Hω12. unfold went, wtrans.
    cbn [wctx wco wsub].
    rewrite subst_sub_comp.
    transitivity (subst (wco w1) ω12).
    apply Hω12.
    apply proper_subst_entails.
    apply Hω01.
  Qed.

  Definition wnil : World := @MkWorld ctx_nil nil.
  Definition wsnoc (w : World) (b : 𝑺 * Ty) : World :=
    @MkWorld (wctx w ▻ b) (subst (wco w) sub_wk1).
  Definition wformula (w : World) (f : Formula w) : World :=
    @MkWorld (wctx w) (cons f (wco w)).
  Definition wsubst (w : World) x {σ} {xIn : x :: σ ∈ w} (t : Term (w - (x :: σ)) σ) : World.
  Proof.
    apply (@MkWorld (ctx_remove xIn)).
    refine (subst (wco w) _).
    apply sub_single.
    apply t.
  Defined.
  Global Arguments wsubst w x {σ xIn} t.

  Fixpoint wcat (w : World) (Σ : LCtx) : World :=
    match Σ with
    | ctx_nil      => w
    | ctx_snoc Σ b => wsnoc (wcat w Σ) b
    end.

  Definition wsnoc_sup {w : World} {b : 𝑺 * Ty} : w ⊒ wsnoc w b :=
    MkAcc w (wsnoc w b) sub_wk1.
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w b ι Hpc. apply Hpc. *)
  (* Qed. *)

  Lemma went_wsnoc_sup {w : World} {b : 𝑺 * Ty} :
    went (@wsnoc_sup w b).
  Proof.
    intros ι Hpc. apply Hpc.
  Qed.

  Definition wsnoc_sub {w1 w2 : World} (ω12 : w1 ⊒ w2) (b : 𝑺 * Ty) (t : Term w2 (snd b)) :
    wsnoc w1 b ⊒ w2 :=
    MkAcc (wsnoc w1 b) w2 (sub_snoc ω12 b t).

  Lemma went_wsnoc_sub {w1 w2 : World} (ω12 : w1 ⊒ w2) (b : 𝑺 * Ty) (t : Term w2 (snd b)) :
    went ω12 ->
    went (@wsnoc_sub w1 w2 ω12 b t).
  Proof.
    unfold went, entails. intros Hpc12 ι2 Hpc2.
    specialize (Hpc12 ι2 Hpc2).
    rewrite inst_subst in Hpc12.
    unfold wsnoc, wsnoc_sub. cbn - [subst inst].
    rewrite ?inst_subst.
    rewrite inst_sub_snoc.
    rewrite inst_sub_wk1.
    apply Hpc12.
  Qed.

  Fixpoint wcat_sub {w1 w2 : World} (ω12 : w1 ⊒ w2) {Δ : LCtx} :
    Sub Δ w2 ->
    wcat w1 Δ ⊒ w2.
  Proof.
    destruct Δ; cbn [wcat].
    - intros _. apply ω12.
    - intros ζ. destruct (snocView ζ).
      apply wsnoc_sub.
      apply wcat_sub.
      auto.
      auto.
      auto.
  Defined.

  (* Next Obligation. *)
  (* Proof. *)
  (* Qed. *)

  Definition wformula_sup {w : World} {f : Formula w} : w ⊒ wformula w f :=
    MkAcc w (wformula w f) (sub_id (wctx w)).
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w f ι. *)
  (*   rewrite subst_sub_id. cbn. *)
  (*   rewrite inst_pathcondition_cons. *)
  (*   now intros []. *)
  (* Qed. *)

  Lemma went_wformula_sup {w f} :
    went (@wformula_sup w f).
  Proof.
    intros ι.
    rewrite subst_sub_id. cbn.
    rewrite inst_pathcondition_cons.
    now intros [].
  Qed.

  Definition wformula_sub {w : World} {f : Formula w} : wformula w f ⊒ w :=
    MkAcc (wformula w f) w (sub_id (wctx w)).
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w f ι. *)
  (*   rewrite subst_sub_id. cbn. *)
  (*   rewrite inst_pathcondition_cons. *)
  (*   now intros []. *)
  (* Qed. *)

  Definition wformulas (w : World) (fmls : List Formula w) : World :=
    @MkWorld (wctx w) (app fmls (wco w)).

  Definition wformulas_sup (w : World) (fmls : List Formula w) :
    w ⊒ wformulas w fmls.
  Proof.
    constructor.
    apply (sub_id (wctx w)).
  Defined.

  Definition wred_sup {w : World} b (t : Term w (snd b)) :
    wsnoc w b ⊒ w :=
    MkAcc (wsnoc w b) w (sub_snoc (sub_id w) b t).

  Definition wsubst_sup {w : World} {x σ} {xIn : x :: σ ∈ w} {t : Term (w - (x :: σ)) σ} :
    w ⊒ wsubst w x t :=
    MkAcc w (wsubst w x t) (sub_single xIn t).
  (* Next Obligation. *)
  (* Proof. *)
  (*   intros w x σ xIn t ι Hpc. apply Hpc. *)
  (* Qed. *)

  Definition wacc_snoc {w0 w1 : World} (ω01 : w0 ⊒ w1) (b : 𝑺 * Ty) :
    wsnoc w0 b ⊒ wsnoc w1 b :=
    MkAcc (wsnoc w0 b) (wsnoc w1 b) (sub_up1 ω01).
  (* Next Obligation. *)
  (*   intros ? ? ? ?. *)
  (*   unfold wsnoc in *. *)
  (*   cbn [wco wctx] in *. *)
  (*   rewrite <- subst_sub_comp. *)
  (*   rewrite sub_comp_wk1_comm. *)
  (*   rewrite subst_sub_comp. *)
  (*   apply proper_subst_entails. *)
  (*   apply went. *)
  (* Qed. *)

  Lemma went_wacc_snoc {w0 w1} {ω01 : w0 ⊒ w1} {b : 𝑺 * Ty} :
    went ω01 ->
    went (wacc_snoc ω01 b).
  Proof.
    unfold wacc_snoc, wsnoc.
    intros Hω01 ι1 Hpc1. cbn - [inst] in *.
    specialize (Hω01 (inst sub_wk1 ι1)).
    rewrite <- subst_sub_comp.
    rewrite sub_comp_wk1_comm.
    cbn in *.
    rewrite inst_subst in Hω01.
    rewrite ?inst_subst.
    rewrite ?inst_subst in Hpc1.
    intuition.
  Qed.

  Definition wacc_formula {w0 w1} (ω01 : w0 ⊒ w1) (fml : Formula w0) :
    wformula w0 fml ⊒ wformula w1 (subst fml ω01) :=
    MkAcc (MkWorld (cons fml (wco w0))) (MkWorld (cons (subst fml ω01) (wco w1))) ω01.

  Lemma went_wacc_formula {w0 w1} {ω01 : w0 ⊒ w1} {fml : Formula w0} :
    went ω01 ->
    went (wacc_formula ω01 fml).
  Proof.
    unfold wacc_formula, wformula.
    intros Hω01 ι1 Hpc1. specialize (Hω01 ι1).
    cbn - [inst] in *.
    rewrite ?inst_pathcondition_cons, ?inst_subst in *.
    intuition.
  Qed.

  Notation WList A := (fun w : World => list (A w)).
  Notation STerm σ := (fun Σ => Term Σ σ).

  Module WorldInstance.

    Record WInstance (w : World) : Set :=
      MkWInstance
        { ιassign :> SymInstance w;
          ιvalid  : instpc (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : inst (A := Prop) fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof.
      intros. cbn.
      apply inst_pathcondition_cons. split; auto.
      apply ιvalid.
    Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : 𝑺 * Ty} (v : Lit (snd b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env_snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite inst_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    Fixpoint winstance_cat {Σ} (ι : WInstance Σ) {Δ} (ιΔ : SymInstance Δ) :
      WInstance (wcat Σ Δ).
    Proof.
      destruct ιΔ; cbn.
      - apply ι.
      - apply winstance_snoc.
        apply winstance_cat.
        apply ι.
        apply ιΔ.
        apply db.
    Defined.

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x :: σ ∈ w}
      (t : Term (w - (x :: σ)) σ) (p : inst t (env_remove (x :: σ) (ιassign ι) xIn) = env_lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env_remove _ (ιassign ι) xIn) _.
    Next Obligation.
      intros. cbn. rewrite inst_subst.
      rewrite inst_sub_single.
      apply ιvalid.
      apply p.
    Qed.

    Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) (Hω01 : went ω01) (ι : WInstance w1) : WInstance w0 :=
       {| ιassign := inst (wsub ω01) (ιassign ι) |}.
    Next Obligation.
    Proof.
      intros w0 w1 ω01 Hω01 ι.
      rewrite <- inst_subst.
      apply Hω01.
      apply ιvalid.
    Qed.

  End WorldInstance.

  Definition TYPE : Type := World -> Type.
  Bind Scope modal with TYPE.
  Definition Valid (A : TYPE) : Type :=
    forall w, A w.
  Definition Impl (A B : TYPE) : TYPE :=
    fun w => A w -> B w.
  Definition Box (A : TYPE) : TYPE :=
    fun w0 => forall w1, w0 ⊒ w1 -> A w1.
  Definition Snoc (A : TYPE) (b : 𝑺 * Ty) : TYPE :=
    fun w => A (wsnoc w b).
  Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
    fun w => forall i : I, A i w.
  Definition Cat (A : TYPE) (Δ : LCtx) : TYPE :=
    fun w => A (wcat w Δ).

  Module ModalNotations.

    Notation "⊢ A" := (Valid A%modal) (at level 100).
    Notation "A -> B" := (Impl A%modal B%modal) : modal.
    Notation "□ A" := (Box A%modal) (at level 9, format "□ A", right associativity) : modal.
    Notation "⌜ A ⌝" := (fun (w : World) => Const A%type w) (at level 0, format "⌜ A ⌝") : modal.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%modal)) ..))
        (at level 99, x binder, y binder, right associativity)
      : modal.

  End ModalNotations.
  Import ModalNotations.
  Open Scope modal.

  Definition K {A B} :
    ⊢ □(A -> B) -> (□A -> □B) :=
    fun w0 f a w1 ω01 =>
      f w1 ω01 (a w1 ω01).
  Definition T {A} :
    ⊢ □A -> A :=
    fun w0 a => a w0 wrefl.
  Definition four {A} :
    ⊢ □A -> □□A :=
    fun w0 a w1 ω01 w2 ω12 =>
      a w2 (wtrans ω01 ω12).
  Global Arguments four : simpl never.

  (* faster version of (four _ sub_wk1) *)
  (* Definition four_wk1 {A} : *)
  (*   ⊢ □A -> ∀ b, Snoc (□A) b := *)
  (*   fun w0 a b w1 ω01 => a w1 (env_tail ω01). *)
  (* Arguments four_wk1 {A Σ0} pc0 a b [Σ1] ζ01 : rename. *)

  Definition valid_box {A} :
    (⊢ A) -> (⊢ □A) :=
    fun a w0 w1 ω01 => a w1.
  Global Arguments valid_box {A} a {w} [w1].

  Definition map_box {A B} (f : ⊢ A -> B) : ⊢ □A -> □B :=
    fun w0 a w1 ω01 => f w1 (a w1 ω01).

  Notation "f <$> a" := (map_box f a) (at level 40, left associativity).
  Notation "f <*> a" := (K f a) (at level 40, left associativity).

  Definition PROP : TYPE :=
    fun _ => Prop.

  Definition comp {A B C} :
    ⊢ (B -> C) -> (A -> B) -> (A -> C) :=
    fun w0 => Basics.compose.

  Class Persistent (A : TYPE) (* `{LogicalRelation.LR A} *) : Type :=
    persist     : ⊢ A -> □A.
      (* persist_lr  : forall w0 (a : A w0) w1 (ω01 : w0 ⊒ w1), *)
      (*     LogicalRelation.lr ω01 a (persist a ω01); *)
      (* persist_dcl : *)
      (*   forall w (a : A w), *)
      (*     LogicalRelation.dcl (persist a) *)
  (* Global Arguments Persistent A {_}. *)

  Global Instance persist_subst {A} `{Subst A} : Persistent A :=
    fun w0 x w1 ω01 => subst x ω01.

  Notation persist__term t :=
    (@persist (STerm _) (@persist_subst (fun Σ => Term Σ _) (@SubstTerm _)) _ t).

  Section Obligations.

    Inductive Obligation {Σ} (msg : Message Σ) (fml : Formula Σ) (ι : SymInstance Σ) : Prop :=
    | obligation (p : inst fml ι : Prop).

  End Obligations.

  Section MultiSubs.

    Inductive MultiSub (w : World) : World -> Type :=
    | multisub_id        : MultiSub w w
    | multisub_cons {w' x σ} (xIn : (x::σ) ∈ w) (t : Term (wctx w - (x::σ)) σ)
                    (ν : MultiSub (wsubst w x t) w')
                    : MultiSub w w'.

    Global Arguments multisub_id {_}.
    Global Arguments multisub_cons {_ _} x {_ _} t ν.

    Fixpoint wmultisub_sup {w1 w2} (ν : MultiSub w1 w2) : w1 ⊒ w2 :=
      match ν with
      | multisub_id         => wrefl
      | multisub_cons _ _ ν => wtrans wsubst_sup (wmultisub_sup ν)
      end.

    Fixpoint sub_multishift {w1 w2} (ζ : MultiSub w1 w2) : Sub w2 w1 :=
      match ζ with
      | multisub_id         => sub_id _
      | multisub_cons x t ζ => subst (sub_multishift ζ) (sub_shift _)
      end.

    Fixpoint inst_multisub {w0 w1} (ζ : MultiSub w0 w1) (ι : SymInstance w0) : Prop :=
      match ζ with
      | multisub_id => True
      | @multisub_cons _ Σ' x σ xIn t ζ0 =>
        let ι' := env_remove (x :: σ) ι xIn in
        env_lookup ι xIn = inst t ι' /\ inst_multisub ζ0 ι'
      end.

    Lemma inst_multi {w1 w2 : World} (ι1 : SymInstance w1) (ζ : MultiSub w1 w2) :
      inst_multisub ζ ι1 ->
      inst (wsub (wmultisub_sup ζ)) (inst (sub_multishift ζ) ι1) = ι1.
    Proof.
      intros Hζ. induction ζ; cbn - [subst].
      - now rewrite ?inst_sub_id.
      - cbn in Hζ. destruct Hζ as [? Hζ].
        rewrite <- inst_sub_shift in Hζ.
        rewrite ?inst_subst.
        rewrite IHζ; auto. rewrite inst_sub_shift.
        now rewrite inst_sub_single.
    Qed.

    (* Forward entailment *)
    Lemma multishift_entails {w0 w1} (ν : MultiSub w0 w1) (ι0 : SymInstance w0) :
      inst_multisub ν ι0 ->
      instpc (wco w0) ι0 ->
      instpc (wco w1) (inst (sub_multishift ν) ι0).
    Proof.
      induction ν; cbn.
      - cbn. rewrite inst_sub_id. auto.
      - intros [Heqx Heq'] Hpc0.
        rewrite inst_subst, inst_sub_shift.
        apply IHν; cbn; auto.
        rewrite ?inst_subst, ?inst_sub_single; auto.
    Qed.

  End MultiSubs.

  Section Solver.

    Definition try_solve_eq {Σ σ} (t1 t2 : Term Σ σ) : option bool :=
      if Term_eqb t1 t2
      then Some true
      else
        (* If the terms are literals, we can trust the negative result. *)
        match t1 , t2 with
        | term_lit _ _ , term_lit _ _ => Some false
        | term_inr _   , term_inl _   => Some false
        | term_inl _   , term_inr _   => Some false
        | _            , _            => None
        end.

    Lemma try_solve_eq_spec {Σ σ} (t1 t2 : Term Σ σ) :
      OptionSpec
        (fun b => forall ι, inst t1 ι = inst t2 ι <-> is_true b)
        True
        (try_solve_eq t1 t2).
    Proof.
      unfold try_solve_eq.
      destruct (Term_eqb_spec t1 t2).
      - constructor. intros. apply reflect_iff.
        constructor. congruence.
      - destruct t1; dependent elimination t2; constructor; auto;
        intros; apply reflect_iff; constructor; cbn; congruence.
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
        (fun b => forall ι, inst fml ι <-> is_true b)
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

    (* Poor man's unification *)
    Definition try_unify {w : World} {σ} (t1 t2 : Term w σ) :
      option { w' & MultiSub w w' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term w σ =>
          match occurs_check ςInΣ t2 with
          | Some t => Some (existT _ (multisub_cons ς t multisub_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_propagate {w : World} (fml : Formula w) :
      option { w' & MultiSub w w' } :=
      match fml with
      | formula_eq t1 t2 =>
        match try_unify t1 t2 with
        | Some r => Some r
        | None => try_unify t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_spec {w : World} {σ} (t1 t2 : Term w σ) :
      OptionSpec (fun '(existT w' ν) => forall ι, inst t1 ι = inst t2 ι <-> inst_multisub ν ι) True (try_unify t1 t2).
    Proof.
      unfold try_unify. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check ςInΣ t2) eqn:Heq; constructor; auto.
      apply (occurs_check_sound (T := fun Σ => Term Σ _)) in Heq. subst.
      intros ι. rewrite inst_subst, inst_sub_shift.
      cbn. intuition.
    Qed.

    Lemma try_propagate_spec {w : World} (fml : Formula w) :
      OptionSpec (fun '(existT w' ν) => forall ι, (inst fml ι : Prop) <-> inst_multisub ν ι) True (try_propagate fml).
    Proof.
      unfold try_propagate; destruct fml; cbn; try (constructor; auto; fail).
      destruct (try_unify_spec t1 t2) as [[w' ν] HYP|_]. constructor. auto.
      destruct (try_unify_spec t2 t1) as [[w' ν] HYP|_]. constructor.
      intros ι. specialize (HYP ι). intuition.
      now constructor.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
       formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) (right _) := false
      };
      formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) (right _) := false
      };
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      induction f1; dependent elimination f2;
        simp formula_eqb;
        try (constructor; auto; fail).
      - destruct (Term_eqb_spec t t0); constructor; intuition.
      - destruct (eq_dec σ σ0); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
      - destruct (eq_dec σ σ1); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
    Qed.

    Fixpoint try_assumption {Σ} (pc : PathCondition Σ) (fml : Formula Σ) {struct pc} : bool :=
      match pc with
      | nil       => false
      | cons f pc => formula_eqb f fml ||| try_assumption pc fml
      end.

    Lemma try_assumption_spec {Σ} (pc : PathCondition Σ) (fml : Formula Σ) :
      BoolSpec (forall ι, instpc pc ι -> inst (A := Prop) fml ι) True (try_assumption pc fml).
    Proof.
      induction pc; cbn.
      - constructor; auto.
      - destruct (formula_eqb_spec a fml).
        + subst a. constructor. intros ι.
          rewrite inst_pathcondition_cons.
          intuition.
        + destruct IHpc.
          * constructor. intros ι.
            rewrite inst_pathcondition_cons.
            intuition.
          * constructor; auto.
    Qed.

    Definition solver {w0 : World} (fml : Formula w0) :
      option { w1 & MultiSub w0 w1 * List Formula w1 }%type :=
      match try_propagate fml with
      | Some (existT Σ1 vareqs) => Some (existT Σ1 (vareqs , nil))
      | None =>
        match try_solve_formula fml with
        | Some true => Some (existT w0 (multisub_id , nil))
        | Some false => None
        | None =>
          if try_assumption (wco w0) fml
          then Some (existT w0 (multisub_id , nil))
          else Some (existT w0 (multisub_id , (cons fml nil)))
        end
      end.

    Lemma inst_multisub_inst_sub_multi {w0 w1} (ζ01 : MultiSub w0 w1) (ι1 : SymInstance w1) :
      inst_multisub ζ01 (inst (wsub (wmultisub_sup ζ01)) ι1).
    Proof.
        induction ζ01; cbn - [subst]; auto.
        rewrite <- inst_sub_shift.
        rewrite <- ?inst_subst.
        rewrite <- inst_lookup.
        rewrite lookup_sub_comp.
        rewrite lookup_sub_single_eq.
        rewrite <- subst_sub_comp.
        rewrite <- sub_comp_assoc.
        rewrite sub_comp_shift_single.
        rewrite sub_comp_id_left.
        split; auto.
    Qed.

    Lemma solver_spec {w0 : World} (fml : Formula w0) :
      OptionSpec
        (fun '(existT Σ1 (ζ, fmls)) =>
           forall ι0,
             instpc (wco w0) ι0 ->
             (inst (A:= Prop) fml ι0 -> inst_multisub ζ ι0) /\
             (forall ι1,
                 ι0 = inst (wsub (wmultisub_sup ζ)) ι1 ->
                 inst fml ι0 <-> inst fmls ι1))
        (forall ι, instpc (wco w0) ι -> inst (A := Prop) fml ι -> False)
        (solver fml).
    Proof.
      unfold solver.
      destruct (try_propagate_spec fml) as [[Σ1 ζ01]|].
      { constructor. intros ι0 Hpc. specialize (H ι0).
        split. intuition. intros ι1 ->.
        intuition. constructor. clear H. apply H1.
        apply inst_multisub_inst_sub_multi.
      }
      clear H.
      destruct (try_solve_formula_spec fml) as [b|].
      { destruct b.
        - constructor. intros ι0 Hpc. cbn. split; auto.
          intros ? Hι. rewrite inst_sub_id in Hι. subst ι1.
          specialize (H ι0). intuition. constructor.
        - constructor. unfold is_true in H. intuition.
      }
      clear H.
      destruct (try_assumption_spec (wco w0) fml).
      { constructor. intros ι0 Hpc. specialize (H ι0).
        cbn. split; auto. intros ι1 ->.
        rewrite inst_sub_id in *. intuition.
        constructor.
      }
      clear H.
      { constructor. intros ι0 Hpc. split.
        cbn; auto. intros ι1 ->.
        rewrite inst_pathcondition_cons.
        cbn. rewrite inst_sub_id.
        intuition. constructor.
      }
    Qed.

  End Solver.

  Module SPath.

    Inductive SPath (w : World) : Type :=
    | angelic_binary (o1 o2 : SPath w)
    | demonic_binary (o1 o2 : SPath w)
    | error (msg : Message w)
    | block
    | assertk (fml : Formula w) (msg : Message w) (k : SPath (wformula w fml))
    | assumek (fml : Formula w) (k : SPath (wformula w fml))
    (* Don't use these two directly. Instead, use the HOAS versions 'angelic' *)
    (* and 'demonic' that will freshen names. *)
    | angelicv b (k : SPath (wsnoc w b))
    | demonicv b (k : SPath (wsnoc w b))
    | assert_vareq
        x σ (xIn : x::σ ∈ w)
        (t : Term (w - (x::σ)) σ)
        (msg : Message (w - (x::σ)))
        (k : SPath (wsubst w x t))
    | assume_vareq
        x σ (xIn : (x,σ) ∈ w)
        (t : Term (w - (x,σ)) σ)
        (k : SPath (wsubst w x t))
    | debug
        {BT B} {subB : Subst BT}
        {instB : Inst BT B}
        {occB: OccursCheck BT}
        (b : BT w) (k : SPath w).

    Global Arguments error {_} _.
    Global Arguments block {_}.
    Global Arguments assertk {_} fml msg k.
    Global Arguments assumek {_} fml k.
    Global Arguments angelicv {_} _ _.
    Global Arguments demonicv {_} _ _.
    Global Arguments assert_vareq {_} x {_ _} t msg k.
    Global Arguments assume_vareq {_} x {_ _} t k.

    Definition demonic_close :
      forall Σ, SPath {| wctx := Σ; wco := nil |} -> SPath wnil :=
      fix close Σ :=
        match Σ with
        | ctx_nil      => fun k => k
        | ctx_snoc Σ b => fun k => close Σ (@demonicv (@MkWorld Σ []) b k)
        end.

    Global Instance persistent_spath : Persistent SPath :=
      (* ⊢ SPath -> □SPath := *)
       fix pers {w0} p {w1} ω01 {struct p} : SPath w1 :=
         match p with
         | angelic_binary p1 p2 => angelic_binary (pers p1 ω01) (pers p2 ω01)
         | demonic_binary p1 p2 => demonic_binary (pers p1 ω01) (pers p2 ω01)
         | error msg            => error (subst msg (wsub ω01))
         | block                => block
         | assertk fml msg p0   =>
             assertk (subst fml (wsub ω01)) (subst msg (wsub ω01))
               (pers p0 (wacc_formula ω01 fml))
         | assumek fml p        =>
             assumek (subst fml (wsub ω01))
               (pers p (wacc_formula ω01 fml))
         | angelicv b p0        => angelicv b (pers p0 (wacc_snoc ω01 b))
         | demonicv b p0        => demonicv b (pers p0 (wacc_snoc ω01 b))
         | assert_vareq x t msg p =>
           let ζ := subst (sub_shift _) (wsub ω01) in
           assertk
             (formula_eq (env_lookup (wsub ω01) _) (subst t ζ))
             (subst msg ζ)
             (pers p
                (MkAcc (MkWorld (subst (wco w0) (sub_single _ t)))
                   (MkWorld
                      (cons (formula_eq (env_lookup (wsub ω01) _) (subst t ζ))
                         (wco w1))) ζ))
         | assume_vareq x t p =>
           let ζ := subst (sub_shift _) (wsub ω01) in
           assumek
             (formula_eq (env_lookup (wsub ω01) _) (subst t ζ))
             (pers p
                (MkAcc (MkWorld (subst (wco w0) (sub_single _ t)))
                   (MkWorld
                      (cons (formula_eq (env_lookup (wsub ω01) _) (subst t ζ))
                         (wco w1))) ζ))
         | debug d p => debug (subst d (wsub ω01)) (pers p ω01)
         end.

    Definition assume_formulas_without_solver {w : World} :
      forall (fmls : List Formula w), SPath (wformulas w fmls) -> SPath w :=
      match w with
      | @MkWorld Σ pc =>
        (fix assumes pc (fmls : List Formula Σ) {struct fmls} :
           SPath {| wctx := Σ; wco := app fmls pc |} ->
           SPath {| wctx := Σ; wco := pc |} :=
           match fmls with
           | nil => fun p => p
           | cons fml fmls =>
             fun p =>
               assumes pc fmls
                 (assumek (w:= {| wctx := Σ; wco := app fmls pc |}) fml p)
           end) pc
      end.
    Global Arguments assume_formulas_without_solver {_} fmls p.

    Definition assert_formulas_without_solver {w : World} :
      forall (msg : Message w) (fmls : List Formula w), SPath (wformulas w fmls) -> SPath w :=
      match w with
      | @MkWorld Σ pc =>
        fun msg =>
        (fix asserts pc (fmls : List Formula Σ) {struct fmls} :
           SPath {| wctx := Σ; wco := app fmls pc |} ->
           SPath {| wctx := Σ; wco := pc |} :=
           match fmls with
           | nil => fun p => p
           | cons fml fmls =>
             fun p =>
               asserts pc fmls
                 (assertk (w:= {| wctx := Σ; wco := app fmls pc |}) fml msg p)
           end) pc
      end.
    Global Arguments assert_formulas_without_solver {_} msg fmls p.

    Fixpoint assume_multisub {w1 w2} (ν : MultiSub w1 w2) :
      SPath w2 -> SPath w1.
    Proof.
      destruct ν; intros o; cbn in o.
      - exact o.
      - apply (@assume_vareq w1 x σ xIn t).
        eapply assume_multisub.
        apply ν.
        apply o.
    Defined.

    Fixpoint assert_multisub {w1 w2} (msg : Message (wctx w1)) (ζ : MultiSub w1 w2) :
      (Message w2 -> SPath w2) -> SPath w1.
    Proof.
      destruct ζ; intros o; cbn in o.
      - apply o. apply msg.
      - apply (@assert_vareq w1 x σ xIn t).
        apply (subst msg (sub_single xIn t)).
        refine (assert_multisub (wsubst w1 x t) _ (subst msg (sub_single xIn t)) ζ o).
    Defined.

    Definition safe :
      (* ⊢ SPath AT -> SymInstance -> PROP := *)
      forall w (o : SPath w) (ι : SymInstance w), Prop :=
      fix safe {w} o ι :=
        match o with
        | angelic_binary o1 o2 => safe o1 ι \/ safe o2 ι
        | demonic_binary o1 o2 => safe o1 ι /\ safe o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          Obligation msg fml ι /\ safe o ι
        | assumek fml o => (inst fml ι : Prop) -> safe o ι
        | angelicv b k => exists v, safe k (env_snoc ι b v)
        | demonicv b k => forall v, safe k (env_snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env_remove (x,σ) ι xIn in
          safe k ι')
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env_remove (x,σ) ι xIn in
          env_lookup ι xIn = inst t ι' ->
          safe k ι'
        | debug d k => Debug (inst d ι) (safe k ι)
        end%type.
    Global Arguments safe {w} o ι.

    Lemma obligation_equiv {Σ : LCtx} (msg : Message Σ) (fml : Formula Σ) (ι : SymInstance Σ) :
      Obligation msg fml ι <-> inst fml ι.
    Proof. split. now intros []. now constructor. Qed.

    Lemma debug_equiv {B : Type} {b : B} {P : Prop} :
      @Debug B b P <-> P.
    Proof. split. now intros []. now constructor. Qed.

    Lemma safe_persist  {w1 w2 : World} (ω12 : w1 ⊒ w2)
          (o : SPath w1) (ι2 : SymInstance w2) :
      safe (persist (A := SPath) o ω12) ι2 <->
      safe o (inst (T := Sub _) ω12 ι2).
    Proof.
      revert w2 ω12 ι2.
      induction o; cbn; intros.
      - now rewrite IHo1, IHo2.
      - now rewrite IHo1, IHo2.
      - split; intros [].
      - reflexivity.
      - rewrite ?obligation_equiv.
        now rewrite IHo, inst_subst.
      - now rewrite IHo, inst_subst.
      - split; intros [v HYP]; exists v; revert HYP;
          rewrite IHo; unfold wacc_snoc, wsnoc;
            cbn [wctx wsub]; now rewrite inst_sub_up1.
      - split; intros HYP v; specialize (HYP v); revert HYP;
          rewrite IHo; unfold wacc_snoc, wsnoc;
            cbn [wctx wsub]; now rewrite inst_sub_up1.
      - rewrite ?obligation_equiv.
        rewrite IHo; unfold wsubst; cbn [wctx wsub]. cbn.
        now rewrite ?inst_subst, ?inst_sub_shift, <- inst_lookup.
      - rewrite IHo; unfold wsubst; cbn [wctx wsub].
        now rewrite ?inst_subst, ?inst_sub_shift, <- inst_lookup.
      - now rewrite ?debug_equiv.
    Qed.

    Lemma safe_assume_formulas_without_solver {w0 : World}
      (fmls : List Formula w0) (o : SPath (wformulas w0 fmls))
      (ι0 : SymInstance w0) :
      safe (assume_formulas_without_solver fmls o) ι0 <->
      (instpc fmls ι0 -> safe o ι0).
    Proof.
      destruct w0. unfold assume_formulas_without_solver. cbn in fmls.
      induction fmls; unfold wformulas; cbn in *.
      - split; auto. intros HYP. apply HYP. constructor.
      - rewrite IHfmls, inst_pathcondition_cons. cbn.
        intuition.
    Qed.

    Lemma safe_assert_formulas_without_solver {w0 : World}
      (msg : Message w0) (fmls : List Formula w0) (o : SPath (wformulas w0 fmls))
      (ι0 : SymInstance w0) :
      safe (assert_formulas_without_solver msg fmls o) ι0 <->
      (instpc fmls ι0 /\ safe o ι0).
    Proof.
      destruct w0. unfold assert_formulas_without_solver. cbn in fmls.
      induction fmls; unfold wformulas; cbn in *.
      - split. intros HYP. split; auto. constructor. intros []; auto.
      - rewrite IHfmls, inst_pathcondition_cons; cbn.
        split; intros []; auto.
        + destruct H0. destruct H0. auto.
        + destruct H. split; auto. split; auto.
          constructor. auto.
    Qed.

    Lemma safe_assume_multisub {w0 w1} (ζ : MultiSub w0 w1)
      (o : SPath w1) (ι0 : SymInstance w0) :
      safe (assume_multisub ζ o) ι0 <->
      (inst_multisub ζ ι0 -> safe o (inst (sub_multishift ζ) ι0)).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        rewrite inst_subst.
        intuition.
    Qed.

    Lemma safe_assert_multisub {w0 w1} msg (ζ : MultiSub w0 w1)
      (o : Message w1 -> SPath w1) (ι0 : SymInstance w0) :
      safe (assert_multisub msg ζ o) ι0 <->
      (inst_multisub ζ ι0 /\ safe (o (subst msg (wmultisub_sup ζ))) (inst (sub_multishift ζ) ι0)).
    Proof.
      induction ζ.
      - cbn. rewrite inst_sub_id, subst_sub_id. intuition.
      - cbn [safe assert_multisub inst_multisub
                  sub_multishift wmultisub_sup wtrans wsub].
        rewrite obligation_equiv.
        rewrite subst_sub_comp. cbn.
        rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        rewrite ?inst_subst.
        intuition.
    Qed.

    Definition angelic_binary_prune :
      ⊢ SPath -> SPath -> SPath :=
      fun w o1 o2 =>
        match o1 , o2 with
        | block   , _       => block
        | _       , block   => block
        | error _ , _       => o2
        | _       , error _ => o1
        | _       , _       => angelic_binary o1 o2
        end.

    Definition demonic_binary_prune :
      ⊢ SPath -> SPath -> SPath :=
      fun w o1 o2 =>
        match o1 , o2 with
        | block   , _       => o2
        | _       , block   => o1
        | error s , _       => error s
        | _       , error s => error s
        | _       , _       => demonic_binary o1 o2
        end.

    Definition assertk_prune :
      (* ⊢ Formula -> Message -> SPath AT -> SPath AT. *)
      forall {w : World} (fml : Formula w), Message w -> SPath (wformula w fml) -> SPath w :=
      fun w fml msg o =>
        match o with
        | error s => @error w s
        | _       => assertk fml msg o
        end.
    Global Arguments assertk_prune {w} fml msg p.

    Definition assumek_prune :
      (* ⊢ Formula -> SPath AT -> SPath AT := *)
      forall {w : World} (fml : Formula w), SPath (wformula w fml) -> SPath w :=
      fun w fml o =>
        match o with
        | block => block
        | _     => assumek fml o
        end.
    Global Arguments assumek_prune {w} fml p.

    Definition angelicv_prune b :
      ⊢ Snoc (SPath) b -> SPath :=
      fun w o => angelicv b o.
        (* This is not good *)
        (* match o with *)
        (* | error s => error s *)
        (* | _           => angelicv b o *)
        (* end. *)

    Definition demonicv_prune b :
      ⊢ Snoc SPath b -> SPath :=
      fun w o =>
        (* match @occurs_check_spath AT _ (Σ ▻ b) b inctx_zero o with *)
        (* | Some o => o *)
        (* | None   => demonicv b o *)
        (* end. *)
        match o with
        | block => block
        | _  => demonicv b o
        end.

    Definition assume_vareq_prune {w}
      {x σ} {xIn : (x,σ) ∈ wctx w} (t : Term (w - (x,σ)) σ) (k : SPath (wsubst w x t)) : SPath w :=
      match k with
      | block => block
      | _          => assume_vareq x t k
      end.
    Global Arguments assume_vareq_prune {w} x {σ xIn} t k.

    Definition assert_vareq_prune {w}
      {x σ} {xIn : (x,σ) ∈ wctx w} (t : Term (w - (x,σ)) σ)
      (msg : Message (w - (x,σ))) (k : SPath (wsubst w x t)) : SPath w :=
      match k with
      (* | fail s => fail s *)
      | _          => assert_vareq x t msg k
      end.
    Global Arguments assert_vareq_prune {w} x {σ xIn} t msg k.

    Definition prune :
      ⊢ SPath -> SPath :=
      fix prune {w} o :=
        match o with
        | error msg => error msg
        | block => block
        | angelic_binary o1 o2 =>
          angelic_binary_prune (prune o1) (prune o2)
        | demonic_binary o1 o2 =>
          demonic_binary_prune (prune o1) (prune o2)
        | assertk fml msg o =>
          assertk_prune fml msg (prune o)
        | assumek fml o =>
          assumek_prune fml (prune o)
        | angelicv b o =>
          angelicv_prune (prune o)
        | demonicv b o =>
          demonicv_prune (prune o)
        | assert_vareq x t msg k =>
          assert_vareq_prune x t msg (prune k)
        | assume_vareq x t k =>
          assume_vareq_prune x t (prune k)
        | debug d k =>
          debug d (prune k)
        end.

    Lemma prune_angelic_binary_sound {w} (p1 p2 : SPath w) (ι : SymInstance w) :
      safe (angelic_binary_prune p1 p2) ι <-> safe (angelic_binary p1 p2) ι.
    Proof.
      destruct p1; cbn; auto.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
    Qed.

    Lemma prune_demonic_binary_sound {w} (p1 p2 : SPath w) (ι : SymInstance w) :
      safe (demonic_binary_prune p1 p2) ι <-> safe (demonic_binary p1 p2) ι.
    Proof.
      destruct p1; cbn; auto.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
    Qed.

    Lemma prune_assertk_sound {w} fml msg (p : SPath (wformula w fml)) (ι : SymInstance w) :
      safe (assertk_prune fml msg p) ι <-> safe (assertk fml msg p) ι.
    Proof. destruct p; cbn; rewrite ?obligation_equiv; auto; intuition. Qed.

    Lemma prune_assumek_sound {w} fml (p : SPath (wformula w fml)) (ι : SymInstance w) :
      safe (assumek_prune fml p) ι <-> safe (assumek fml p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_angelicv_sound {w b} (p : SPath (wsnoc w b)) (ι : SymInstance w) :
      safe (angelicv_prune p) ι <-> safe (angelicv b p) ι.
    Proof. reflexivity. Qed.

    Lemma prune_demonicv_sound {w b} (p : SPath (wsnoc w b)) (ι : SymInstance w) :
      safe (demonicv_prune p) ι <-> safe (demonicv b p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_assert_vareq_sound {w : World} {x σ} {xIn : x :: σ ∈ w}
      (t : Term (w - (x :: σ)) σ) (msg : Message (w - (x :: σ))) (p : SPath (wsubst w x t)) (ι : SymInstance w) :
      safe (assert_vareq_prune x t msg p) ι <-> safe (assert_vareq x t msg p) ι.
    Proof. reflexivity. Qed.

    Lemma prune_assume_vareq_sound {w : World} {x σ} {xIn : x :: σ ∈ w}
      (t : Term (w - (x :: σ)) σ) (p : SPath (wsubst w x t)) (ι : SymInstance w) :
      safe (assume_vareq_prune x t p) ι <-> safe (assume_vareq x t p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_sound {w} (p : SPath w) (ι : SymInstance w) :
      safe (prune p) ι <-> safe p ι.
    Proof.
      induction p; cbn [prune safe].
      - rewrite prune_angelic_binary_sound; cbn.
        now rewrite IHp1, IHp2.
      - rewrite prune_demonic_binary_sound; cbn.
        now rewrite IHp1, IHp2.
      - auto.
      - auto.
      - rewrite prune_assertk_sound; cbn.
        now rewrite IHp.
      - rewrite prune_assumek_sound; cbn.
        now rewrite IHp.
      - rewrite prune_angelicv_sound; cbn.
        apply base.exist_proper; intros.
        now rewrite IHp.
      - rewrite prune_demonicv_sound; cbn.
        apply base.forall_proper; intros.
        now rewrite IHp.
      - rewrite prune_assert_vareq_sound; cbn.
        now rewrite IHp.
      - rewrite prune_assume_vareq_sound; cbn.
        now rewrite IHp.
      - now rewrite ?debug_equiv.
    Qed.

    Definition ok :
      ⊢ SPath -> ⌜bool⌝ :=
      fun w o =>
        match prune o with
        | block => true
        | _     => false
        end.

  End SPath.
  Notation SPath := SPath.SPath.
  Import SPath.

  Section VerificationConditions.

    Inductive VerificationCondition (p : SPath wnil) : Prop :=
    | vc (P : safe p env_nil).

  End VerificationConditions.

  Definition SDijkstra (A : TYPE) : TYPE :=
    □(A -> SPath) -> SPath.

  Module SDijk.

    Definition pure {A : TYPE} :
      ⊢ A -> SDijkstra A :=
      fun w0 a POST => T POST a.

    Definition map {A B} :
      ⊢ □(A -> B) -> SDijkstra A -> SDijkstra B :=
      fun w0 f m POST => m (comp <$> POST <*> f).

    Definition bind {A B} :
      ⊢ SDijkstra A -> □(A -> SDijkstra B) -> SDijkstra B :=
      fun w0 m f POST => m (fun w1 ω01 a1 => f w1 ω01 a1 (four POST ω01)).

    Definition angelic (x : option 𝑺) σ :
      ⊢ SDijkstra (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        angelicv
          (y :: σ) (k (wsnoc w (y :: σ)) wsnoc_sup (@term_var _ y σ inctx_zero)).
    Global Arguments angelic x σ [w] k.

    Definition angelic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SDijkstra (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
        | ctx_nil             => fun k => T k env_nil
        | ctx_snoc Δ (x :: σ) =>
          fun k =>
            angelic (Some (n x)) σ (fun w1 ω01 t =>
              rec Δ (fun w2 ω12 EΔ =>
                k w2 (wtrans ω01 ω12) (EΔ ► (x :: σ ↦ subst t ω12))))
        end.
    Global Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic (x : option 𝑺) σ :
      ⊢ SDijkstra (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        demonicv
          (y :: σ) (k (wsnoc w (y :: σ)) wsnoc_sup (@term_var _ y σ inctx_zero)).
    Global Arguments demonic x σ [w] k.

    Definition demonic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SDijkstra (fun w => NamedEnv (Term w) Δ) :=
      fix demonic_ctx {w} Δ {struct Δ} :=
        match Δ with
        | ctx_nil             => fun k => T k env_nil
        | ctx_snoc Δ (x :: σ) =>
          fun k =>
            demonic (Some (n x)) σ (fun w1 ω01 t =>
              demonic_ctx Δ (fun w2 ω12 EΔ =>
                k w2 (wtrans ω01 ω12) (EΔ ► (x :: σ ↦ subst t ω12))))
        end.
    Global Arguments demonic_ctx {_} n [w] Δ : rename.

    Definition assume_formula :
      ⊢ Formula -> SDijkstra Unit :=
      fun w0 fml POST =>
        match solver fml with
        | Some (existT w1 (ν , fmls)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_multisub ν
            (assume_formulas_without_solver fmls
               (four POST (wmultisub_sup ν) (wformulas_sup w1 fmls) tt))
        | None =>
          (* The formula is inconsistent with the path constraints. *)
          block
        end.

    Definition assert_formula :
      ⊢ Message -> Formula -> SDijkstra Unit.
      refine (
      fun w0 msg fml POST =>
        match solver fml with
        | Some (existT w1 (ν , fmls)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_multisub msg ν
            (fun msg' => assert_formulas_without_solver msg' fmls _)
        | None =>
          (* The formula is inconsistent. *)
          error msg
        end).
      eapply (four POST); eauto.
      apply (wmultisub_sup ν).
      apply (wformulas_sup w1 fmls).
      constructor.
    Defined.

    Definition assume_formulas :
      ⊢ List Formula -> SDijkstra Unit.
      refine (
      fun w0 =>
        fix assumes fmls0 :=
        match fmls0 with
        | nil           => pure tt
        | cons fml fmls1 => _
          (* fun w1 ω01 => *)
            (* assume_formulak *)
            (*   (subst fml ω01) *)
            (*   (four (assumes fmls k) ω01) *)
        end).
      eapply bind.
      apply (assumes fmls1).
      intros w1 ω01 _.
      apply assume_formula.
      apply (subst fml ω01).
    Defined.

    Definition assert_formulas :
      ⊢ Message -> List Formula -> SDijkstra Unit.
      refine (
      fun w0 msg =>
        fix asserts fmls0 :=
        match fmls0 with
        | nil           => pure tt
        | cons fml fmls1 => _
          (* fun w1 ω01 => _ *)
            (* assert_formula *)
            (*   (subst msg ω01) *)
            (*   (subst fml ω01) *)
            (*   (four (asserts fmls k) ω01) *)
        end).
      eapply bind.
      apply (asserts fmls1).
      intros w1 ω01 _.
      apply assert_formula.
      apply (subst msg ω01).
      apply (subst fml ω01).
    Defined.

    Definition angelic_list {A} :
      ⊢ Message -> List A -> SDijkstra A :=
      fun w msg =>
        fix rec xs POST :=
        match xs with
        | nil        => error msg
        | cons x xs  => angelic_binary (T POST x) (rec xs POST)
        end.

    Definition demonic_list {A} :
      ⊢ List A -> SDijkstra A :=
      fun w =>
        fix rec xs POST :=
        match xs with
        | nil        => block
        | cons x xs  => demonic_binary (T POST x) (rec xs POST)
        end.

    Definition angelic_finite F `{finite.Finite F} :
      ⊢ Message -> SDijkstra ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SDijkstra ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).

    Definition angelic_match_bool {A} :
      ⊢ Message -> STerm ty_bool -> □(SDijkstra A) -> □(SDijkstra A) -> SDijkstra A.
      unfold SDijkstra in *.
      intros w0 msg t pt pf k.
      apply angelic_binary.
      - apply assert_formula.
        auto.
        apply (formula_bool t).
        intros w1 ω01 _.
        apply pt.
        auto.
        apply (four k ω01).
      - apply assert_formula.
        auto.
        apply (formula_bool (term_not t)).
        intros w1 ω01 _.
        apply pf.
        auto.
        apply (four k ω01).
    Defined.

    Definition demonic_match_bool {A} :
      ⊢ STerm ty_bool -> □(SDijkstra A) -> □(SDijkstra A) -> SDijkstra A.
      (* fun w0 t pt pf => *)
      (*   match term_get_lit t with *)
      (*   | Some true => T pt *)
      (*   | Some false => T pf *)
      (*   | None => *)
      (*     demonic_binary *)
      (*       (assume_formulak (formula_bool t) pt) *)
      (*       (assume_formulak (formula_bool (term_not t)) pf) *)
      (*   end. *)
    Admitted.

    (* Definition angelic_match_enum {AT E} : *)
    (*   ⊢ Message -> STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(SPath AT)) -> SPath AT := *)
    (*   fun w msg t k => *)
    (*     match term_get_lit t with *)
    (*     | Some v => T (k v) *)
    (*     | None => angelic_finite *)
    (*                 msg (fun v => assert_formulak msg (formula_eq t (term_enum E v)) (k v)) *)
    (*     end. *)

    (* Definition demonic_match_enum {AT E} : *)
    (*   ⊢ STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(SPath AT)) -> SPath AT := *)
    (*   fun w t k => *)
    (*     match term_get_lit t with *)
    (*     | Some v => T (k v) *)
    (*     | None => demonic_finite *)
    (*                 (fun v => assume_formulak (formula_eq t (term_enum E v)) (k v)) *)
    (*     end. *)

    (* Definition angelic_match_list {AT} (x y : 𝑺) (σ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_list σ) -> □(SPath AT) -> □(STerm σ -> STerm (ty_list σ) -> SPath AT) -> SPath AT := *)
    (*   fun w0 msg t knil kcons => *)
    (*     angelic_binary (assert_formulak msg (formula_eq (term_lit (ty_list σ) []) t) knil) *)
    (*       (angelic x σ *)
    (*          (fun w1 ω01 (th : Term w1 σ) => *)
    (*           angelic y (ty_list σ) *)
    (*             (fun w2 ω12 (tt : Term w2 (ty_list σ)) => *)
    (*              assert_formulak (subst msg (wtrans ω01 ω12)) *)
    (*                (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12))) *)
    (*                (fun w3 ω23 => *)
    (*                 four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))). *)

    (* Definition demonic_match_list {AT} (x y : 𝑺) (σ : Ty) : *)
    (*   ⊢ STerm (ty_list σ) -> □(SPath AT) -> □(STerm σ -> STerm (ty_list σ) -> SPath AT) -> SPath AT := *)
    (*   fun w0 t knil kcons => *)
    (*     demonic_binary (assume_formulak (formula_eq (term_lit (ty_list σ) []) t) knil) *)
    (*       (demonic x σ *)
    (*          (fun w1 ω01 (th : Term w1 σ) => *)
    (*           demonic y (ty_list σ) *)
    (*             (fun w2 ω12 (tt : Term w2 (ty_list σ)) => *)
    (*              assume_formulak *)
    (*                (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12))) *)
    (*                (fun w3 ω23 => *)
    (*                 four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))). *)

    Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A.
      intros w0 msg t kinl kinr POST.
      apply angelic_binary.
      - apply (angelic (Some x) σ).
        intros w1 ω01 t1.
        apply assert_formula. apply (subst msg ω01).
        apply (formula_eq (term_inl t1) (subst t ω01)).
        intros w2 ω12 _.
        apply (four kinl ω01). auto.
        apply (persist__term t1 ω12).
        apply (four (four POST ω01)).
        auto.
      - apply (angelic (Some y) τ).
        intros w1 ω01 t1.
        apply assert_formula. apply (subst msg ω01).
        apply (formula_eq (term_inr t1) (subst t ω01)).
        intros w2 ω12 _.
        apply (four kinr ω01). auto.
        apply (persist__term t1 ω12).
        apply (four (four POST ω01)).
        auto.
    Defined.

    (* Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A. *)
    (* Proof. *)
    (*   intros w0. *)
    (*   fun w0 msg t kinl kinr => *)
    (*     match term_get_sum t with *)
    (*     | Some (inl tσ) => T kinl tσ *)
    (*     | Some (inr tτ) => T kinr tτ *)
    (*     | None => angelic_match_sum' x y msg t kinl kinr *)
    (*     end. *)

    Definition demonic_match_sum' {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 t kinl kinr k.
      apply demonic_binary.
      - apply (demonic (Some x) σ).
        intros w1 ω01 t1.
        apply assume_formula.
        apply (formula_eq (term_inl t1) (subst t ω01)).
        intros w2 ω12 _.
        apply (four kinl ω01). auto.
        apply (persist__term t1 ω12).
        apply (four (four k ω01)).
        auto.
      - apply (demonic (Some y) τ).
        intros w1 ω01 t1.
        apply assume_formula.
        apply (formula_eq (term_inr t1) (subst t ω01)).
        intros w2 ω12 _.
        apply (four kinr ω01). auto.
        apply (persist__term t1 ω12).
        apply (four (four k ω01)).
        auto.
    Defined.

    Definition demonic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A :=
      fun w0 t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => demonic_match_sum' x y t kinl kinr
        end.

    Definition angelic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 msg t k POST.
      apply (angelic (Some x) σ).
      intros w1 ω01 t1.
      apply (angelic (Some y) τ).
      intros w2 ω12 t2.
      apply assert_formula. apply (subst msg (wtrans ω01 ω12)).
      refine (formula_eq _ (subst t (wtrans ω01 ω12))).
      eapply (term_binop binop_pair).
      apply (persist__term t1 ω12).
      apply t2.
      intros w3 ω23 _.
      apply (four k (wtrans ω01 ω12)).
      auto.
      apply (persist__term t1 (wtrans ω12 ω23)).
      apply (persist__term t2 ω23).
      apply (four POST).
      apply (wtrans ω01 (wtrans ω12 ω23)).
    Defined.

    (* Definition angelic_match_prod {AT} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SPath AT) -> SPath AT := *)
    (*   fun w0 msg t k => *)
    (*     match term_get_pair t with *)
    (*     | Some (tσ,tτ) => T k tσ tτ *)
    (*     | None => angelic_match_prod' x y msg t k *)
    (*     end. *)

    Definition demonic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 t k POST.
      apply (demonic (Some x) σ).
      intros w1 ω01 t1.
      apply (demonic (Some y) τ).
      intros w2 ω12 t2.
      apply assume_formula.
      refine (formula_eq _ (subst t (wtrans ω01 ω12))).
      eapply (term_binop binop_pair).
      apply (persist__term t1 ω12).
      apply t2.
      intros w3 ω23 _.
      apply (four k (wtrans ω01 ω12)).
      auto.
      apply (persist__term t1 (wtrans ω12 ω23)).
      apply (persist__term t2 ω23).
      apply (four POST).
      apply (wtrans ω01 (wtrans ω12 ω23)).
    Defined.

    (* Definition demonic_match_prod {AT} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SPath AT) -> SPath AT := *)
    (*   fun w0 t k => *)
    (*     match term_get_pair t with *)
    (*     | Some (tσ,tτ) => T k tσ tτ *)
    (*     | None => demonic_match_prod' x y t k *)
    (*     end. *)

    (* Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   apply (angelic_freshen_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assert_formulak. *)
    (*   apply (subst msg ω01). *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_record R (record_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (wtrans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   destruct (term_get_record t). *)
    (*   - apply (T k). *)
    (*     apply (record_pattern_match_env p n0). *)
    (*   - apply (angelic_match_record' n p msg t k). *)
    (* Defined. *)

    (* Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   apply (demonic_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assume_formulak. *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_record R (record_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (wtrans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   destruct (term_get_record t). *)
    (*   - apply (T k). *)
    (*     apply (record_pattern_match_env p n0). *)
    (*   - apply (demonic_match_record' n p t k). *)
    (* Defined. *)

    (* Definition angelic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   apply (angelic_freshen_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assert_formulak. *)
    (*   apply (subst msg ω01). *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_tuple (tuple_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (wtrans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   destruct (term_get_tuple t). *)
    (*   - apply (T k). *)
    (*     apply (tuple_pattern_match_env p e). *)
    (*   - apply (angelic_match_tuple' n p msg t k). *)
    (* Defined. *)

    (* Definition demonic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   apply (demonic_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assume_formulak. *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_tuple (tuple_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (wtrans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   destruct (term_get_tuple t). *)
    (*   - apply (T k). *)
    (*     apply (tuple_pattern_match_env p e). *)
    (*   - apply (demonic_match_tuple' n p t k). *)
    (* Defined. *)

    (* (* TODO: move to Syntax *) *)
    (* Definition pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   NamedEnv (Term Σ) Δ -> Term Σ σ := *)
    (*   match p with *)
    (*   | pat_var x    => fun Ex => match snocView Ex with isSnoc _ t => t end *)
    (*   | pat_unit     => fun _ => term_lit ty_unit tt *)
    (*   | pat_pair x y => fun Exy => match snocView Exy with *)
    (*                                  isSnoc Ex ty => *)
    (*                                  match snocView Ex with *)
    (*                                    isSnoc _ tx => term_binop binop_pair tx ty *)
    (*                                  end *)
    (*                                end *)
    (*   | pat_tuple p  => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ) *)
    (*   | pat_record p => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ) *)
    (*   end. *)

    (* Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   ⊢ Message -> STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT := *)
    (*   fun w0 msg t k => *)
    (*     angelic_freshen_ctx n Δ *)
    (*       (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) => *)
    (*        assert_formulak (subst msg ω01) (formula_eq (subst t ω01) (pattern_match_env_reverse p ts)) *)
    (*          (fun w2 ω12 => k w2 (wtrans ω01 ω12) (subst ts ω12))). *)

    (* Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   ⊢ STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> SPath AT) -> SPath AT := *)
    (*   fun w0 t k => *)
    (*     demonic_ctx n Δ *)
    (*       (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) => *)
    (*        assume_formulak (formula_eq (subst t ω01) (pattern_match_env_reverse p ts)) *)
    (*          (fun w2 ω12 => k w2 (wtrans ω01 ω12) (subst ts ω12))). *)

    (* Definition angelic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT := *)
    (*   fun w0 msg t k => *)
    (*     angelic_finite msg *)
    (*       (fun K : 𝑼𝑲 U => *)
    (*        angelic None (𝑼𝑲_Ty K) *)
    (*          (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) => *)
    (*           assert_formulak (subst msg ω01) (formula_eq (term_union U K t__field) (subst t ω01)) *)
    (*             (fun w2 ω12 => *)
    (*              let ω02 := wtrans ω01 ω12 in *)
    (*              angelic_match_pattern n (p K) (subst msg ω02) (subst t__field ω12) (four (k K) ω02)))). *)

    (* Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT := *)
    (*   fun w0 msg t k => *)
    (*     match term_get_union t with *)
    (*     | Some (existT K t__field) => angelic_match_pattern n (p K) msg t__field (k K) *)
    (*     | None => angelic_match_union' n p msg t k *)
    (*     end. *)

    (* Definition demonic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT := *)
    (*   fun w0 t k => *)
    (*     demonic_finite *)
    (*       (fun K : 𝑼𝑲 U => *)
    (*        demonic None (𝑼𝑲_Ty K) *)
    (*          (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) => *)
    (*           assume_formulak (formula_eq (term_union U K t__field) (subst t ω01)) *)
    (*             (fun w2 ω12 => *)
    (*              demonic_match_pattern n (p K) (subst t__field ω12) (four (k K) (wtrans ω01 ω12))))). *)

    (* Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> SPath AT)) -> SPath AT := *)
    (*   fun w0 t k => *)
    (*     match term_get_union t with *)
    (*     | Some (existT K t__field) => demonic_match_pattern n (p K) t__field (k K) *)
    (*     | None => demonic_match_union' n p t k *)
    (*     end. *)

    Lemma and_iff_compat_l' (A B C : Prop) :
      (A -> B <-> C) <-> (A /\ B <-> A /\ C).
    Proof. intuition. Qed.

    Lemma imp_iff_compat_l' (A B C : Prop) :
      (A -> B <-> C) <-> ((A -> B) <-> (A -> C)).
    Proof. intuition. Qed.

    Global Instance proper_debug {B} : Proper (eq ==> iff ==> iff) (@Debug B).
    Proof.
      unfold Proper, respectful.
      intros ? ? -> P Q PQ.
      split; intros []; constructor; intuition.
    Qed.

    (* Ltac wsimpl := *)
    (*   repeat *)
    (*     (try change (wctx (wsnoc ?w ?b)) with (ctx_snoc (wctx w) b); *)
    (*      try change (wsub (@wred_sup ?w ?b ?t)) with (sub_snoc (sub_id (wctx w)) b t); *)
    (*      try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b))); *)
    (*      try change (wsub (@wrefl ?w)) with (sub_id (wctx w)); *)
    (*      try change (wsub (@wsnoc_sup ?w ?b)) with (@sub_wk1 (wctx w) b); *)
    (*      try change (wctx (wformula ?w ?fml)) with (wctx w); *)
    (*      try change (wsub (wtrans ?ω1 ?ω2)) with (subst (wsub ω1) (wsub ω2)); *)
    (*      try change (wsub (@wformula_sup ?w ?fml)) with (sub_id (wctx w)); *)
    (*      try change (wco (wformula ?w ?fml)) with (cons fml (wco w)); *)
    (*      try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t)); *)
    (*      try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx_remove xIn); *)
    (*      try change (wsub (@wsubst_sup ?w _ _ ?xIn ?t)) with (sub_single xIn t); *)
    (*      rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id, *)
    (*        ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc, *)
    (*        ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons; *)
    (*      repeat *)
    (*        match goal with *)
    (*        | |- Debug _ _ <-> Debug _ _ => apply proper_debug *)
    (*        | |- (?A /\ ?B) <-> (?A /\ ?C) => apply and_iff_compat_l'; intro *)
    (*        | |- (?A -> ?B) <-> (?A -> ?C) => apply imp_iff_compat_l'; intro *)
    (*        | |- (exists x : ?X, _) <-> (exists y : ?X, _) => apply base.exist_proper; intro *)
    (*        | |- (forall x : ?X, _) <-> (forall y : ?X, _) => apply base.forall_proper; intro *)
    (*        | |- wp ?m _ ?ι -> wp ?m _ ?ι => apply wp_monotonic; intro *)
    (*        | |- wp ?m _ ?ι <-> wp ?m _ ?ι => apply wp_equiv; intro *)
    (*        | |- ?w ⊒ ?w => apply wrefl *)
    (*        | |- ?POST (@inst _ _ _ ?Σ1 ?x1 ?ι1) <-> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) => *)
    (*          assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto *)
    (*        | |- ?POST (?inst _ _ _ ?Σ1 ?x1 ?ι1) -> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) => *)
    (*          assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w ?ω _) _ = inst (?f ?w ?ω _) _ => *)
    (*          apply (Hdcl w ω w ω wrefl) *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w0 wrefl _) _ = inst (?f ?w1 ?ω01 _) _ => *)
    (*          apply (Hdcl w0 wrefl w1 ω01 ω01) *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w1 ?ω01 _) _ = inst (?f ?w0 wrefl _) _ => *)
    (*          symmetry; apply (Hdcl w0 wrefl w1 ω01 ω01) *)
    (*        | Hdcl : arrow_dcl ?f |- *)
    (*          wp (?f ?w ?ω _) _ _ -> wp (?f ?w ?ω _) _ _  => *)
    (*          apply (Hdcl w ω w ω wrefl) *)
    (*        end). *)

  End SDijk.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Definition SMut (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
    □(A -> SStore Γ2 -> SHeap -> SPath) -> SStore Γ1 -> SHeap -> SPath.
  Bind Scope smut_scope with SMut.

  Module SMut.

    Section Basic.

      Definition dijkstra {Γ} {A : TYPE} :
        ⊢ SDijkstra A -> SMut Γ Γ A.
      Proof.
        intros w0 m POST δ0 h0.
        apply m.
        intros w1 ω01 a1.
        apply POST; auto.
        apply (subst δ0 ω01).
        apply (subst h0 ω01).
      Defined.

      Definition pure {Γ} {A : TYPE} :
        ⊢ A -> SMut Γ Γ A.
      Proof.
        intros w0 a k.
        apply k; auto. apply wrefl.
      Defined.

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SMut Γ1 Γ2 A -> □(A -> SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B.
      Proof.
        intros w0 ma f k.
        unfold SMut, Impl, Box in *.
        apply ma; auto.
        intros w1 ω01 a1.
        apply f; auto.
        apply (four k ω01).
      Defined.

      (* Definition strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : SMut Γ1 Γ2 A Σ) (b : B Σ) : *)
      (*   SMut Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ := *)
      (*   bind ma (fun _ ζ a => pure (a, subst b ζ)). *)

      Definition bind_right {Γ1 Γ2 Γ3 A B} :
        ⊢ SMut Γ1 Γ2 A -> □(SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B.
      Proof.
        intros w0 m k POST.
        apply m.
        intros w1 ω01 a1.
        apply k. auto.
        intros w2 ω12 b2.
        apply (four POST ω01); auto.
      Defined.

      (* Definition bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} : *)
      (*   ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 A). *)
      (* Proof. *)
      (*   intros w0 ma mb. *)
      (*   apply (bbind ma). *)
      (*   intros w1 ω01 a1 δ1 h1. *)
      (*   apply (bind (mb w1 ω01 δ1 h1)). *)
      (*   intros w2 ω12 [_ δ2 h2]. *)
      (*   apply (pure). *)
      (*   apply (subst a1 ω12). *)
      (*   auto. *)
      (*   auto. *)
      (* Defined. *)

      (* Definition map {Γ1 Γ2 A B} `{Subst A, Subst B} : *)
      (*   ⊢ □(SMut Γ1 Γ2 A) -> □(A -> B) -> □(SMut Γ1 Γ2 B) := *)
      (*   fun w0 ma f Σ1 ζ01 pc1 δ1 h1 => *)
      (*     map pc1 *)
      (*       (fun Σ2 ζ12 pc2 '(MkSMutResult a2 δ2 h2) => *)
      (*          MkSMutResult (f Σ2 (subst ζ01 ζ12) pc2 a2) δ2 h2) *)
      (*        (ma Σ1 ζ01 pc1 δ1 h1). *)

      Definition error {Γ1 Γ2 A D} (func : string) (msg : string) (data:D) :
        ⊢ SMut Γ1 Γ2 A.
      Proof.
        intros w POST δ h.
        apply error.
        apply (@MkMessage _ func msg Γ1); auto.
        apply (wco w).
      Defined.
      Global Arguments error {_ _ _ _} func msg data {w} _ _.

      Definition block {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A.
      Proof.
        intros w0 POST δ h.
        apply block.
      Defined.

      Definition angelic_binary {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          angelic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).
      Definition demonic_binary {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          demonic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).

      Definition angelic_list {A Γ} :
        ⊢ (SStore Γ -> SHeap -> Message) -> List A -> SMut Γ Γ A :=
        fun w msg xs POST δ h => dijkstra (SDijk.angelic_list (msg δ h) xs) POST δ h.

      Definition angelic_finite {Γ} F `{finite.Finite F} :
        ⊢ (SStore Γ -> SHeap -> Message) -> SMut Γ Γ ⌜F⌝ :=
        fun w msg POST δ h => dijkstra (SDijk.angelic_finite (msg δ h)) POST δ h.

      Definition demonic_finite {Γ} F `{finite.Finite F} :
        ⊢ SMut Γ Γ ⌜F⌝ :=
        fun w => dijkstra (SDijk.demonic_finite (w:=w)).

      Definition angelic {Γ} (x : option 𝑺) σ :
        ⊢ SMut Γ Γ (STerm σ) :=
        fun w => dijkstra (SDijk.angelic x σ (w:=w)).
      Global Arguments angelic {Γ} x σ {w}.

      Definition demonic {Γ} (x : option 𝑺) σ :
        ⊢ SMut Γ Γ (STerm σ) :=
        fun w => dijkstra (SDijk.demonic x σ (w:=w)).
      Global Arguments demonic {Γ} x σ {w}.

      Definition debug {AT DT D} `{Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> DT) -> (SMut Γ1 Γ2 AT) -> (SMut Γ1 Γ2 AT).
      Proof.
        intros w0 d m POST δ h.
        eapply debug. eauto.
        eauto. eauto.
        apply d. auto. auto.
        apply m; auto.
      Defined.

      Definition angelic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 Δ. apply dijkstra.
        apply (SDijk.angelic_ctx n Δ).
      Defined.
      Global Arguments angelic_ctx {N} n {Γ} [w] Δ : rename.

      Definition demonic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 Δ. apply dijkstra.
        apply (SDijk.demonic_ctx n Δ).
      Defined.
      Global Arguments demonic_ctx {N} n {Γ} [w] Δ : rename.

    End Basic.

    Module SMutNotations.

      (* Notation "'⨂' x .. y => F" := *)
      (*   (smut_demonic (fun x => .. (smut_demonic (fun y => F)) .. )) : smut_scope. *)

      (* Notation "'⨁' x .. y => F" := *)
      (*   (smut_angelic (fun x => .. (smut_angelic (fun y => F)) .. )) : smut_scope. *)

      (* Infix "⊗" := smut_demonic_binary (at level 40, left associativity) : smut_scope. *)
      (* Infix "⊕" := smut_angelic_binary (at level 50, left associativity) : smut_scope. *)

      Notation "x <- ma ;; mb" := (bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : smut_scope.
      Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : smut_scope.
      Notation "ma >> mb" := (bind_right ma mb) (at level 50, left associativity) : smut_scope.
      (* Notation "m1 ;; m2" := (smut_bind_right m1 m2) : smut_scope. *)

    End SMutNotations.
    Import SMutNotations.
    Local Open Scope smut_scope.

    Section AssumeAssert.

      (* Add the provided formula to the path condition. *)
      Definition assume_formula {Γ} :
        ⊢ Formula -> SMut Γ Γ Unit.
      Proof.
        intros w0 fml. apply dijkstra.
        apply (SDijk.assume_formula fml).
      Defined.

      Definition box_assume_formula {Γ} :
        ⊢ Formula -> □(SMut Γ Γ Unit) :=
        fun w0 fml => assume_formula <$> persist fml.

      Definition assert_formula {Γ} :
        ⊢ Formula -> SMut Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          dijkstra
            (SDijk.assert_formula
               {| msg_function := "smut_assert_formula";
                  msg_message := "Proof obligation";
                  msg_program_context := Γ;
                  msg_localstore := δ0;
                  msg_heap := h0;
                  msg_pathcondition := wco w0
               |} fml)
            POST δ0 h0.

      Definition box_assert_formula {Γ} :
        ⊢ Formula -> □(SMut Γ Γ Unit) :=
        fun w0 fml => assert_formula <$> persist fml.

      Definition assert_formulas {Γ} :
        ⊢ List Formula -> SMut Γ Γ Unit.
      Proof.
        intros w0 fmls POST δ0 h0.
        eapply dijkstra.
        apply SDijk.assert_formulas.
        apply
          {| msg_function := "smut_assert_formula";
             msg_message := "Proof obligation";
             msg_program_context := Γ;
             msg_localstore := δ0;
             msg_heap := h0;
             msg_pathcondition := wco w0
          |}.
        apply fmls.
        apply POST.
        apply δ0.
        apply h0.
      Defined.

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kt kf.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "smut_angelic_match_bool"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_bool t).
          apply kt.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "smut_angelic_match_bool"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_bool (term_not t)).
          apply kf.
      Defined.

      Definition angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_lit t with
          | Some true => T kt
          | Some false => T kf
          | None => angelic_match_bool' t kt kf
          end.

      Definition box_angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          angelic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition demonic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kt kf.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_bool t).
          apply kt.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_bool (term_not t)).
          apply kf.
      Defined.

      Definition demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_lit t with
          | Some true => T kt
          | Some false => T kf
          | None => demonic_match_bool' t kt kf
          end.

      Definition box_demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          demonic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition angelic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := 𝑬𝑲 E)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_enum";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 EK.
        eapply bind_right.
        apply (assert_formula (formula_eq (subst t ω01) (term_enum E EK))).
        apply (four (cont EK)). auto.
      Defined.

      Definition demonic_match_enum {A E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 A)) -> SMut Γ1 Γ2 A.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := 𝑬𝑲 E)).
        intros w1 ω01 EK.
        eapply bind_right.
        apply (assume_formula (formula_eq (subst t ω01) (term_enum E EK))).
        apply (four (cont EK)). auto.
      Defined.

      Definition smutb_demonic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k =>
          demonic_match_enum
            <$> persist__term t
            <*> (fun (w1 : World) (ω01 : w0 ⊒ w1) (EK : 𝑬𝑲 E) => four (k EK) ω01).

      Definition angelic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr POST δ0 h0.
        apply SPath.angelic_binary.
        - apply (SDijk.angelic (Some x) σ).
          intros w1 ω01 t1.
          apply SDijk.assert_formula.
          apply
            {| msg_function        := "SMut.angelic_match_sum";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := subst δ0 ω01;
               msg_heap            := subst h0 ω01;
               msg_pathcondition   := wco w1;
            |}.
          apply (formula_eq (term_inl t1) (subst t ω01)).
          intros w2 ω12 _.
          apply (four kinl ω01). auto.
          apply (persist__term t1 ω12).
          apply (four (four POST ω01)).
          auto.
          apply (subst δ0 (wtrans ω01 ω12)).
          apply (subst h0 (wtrans ω01 ω12)).
        - apply (SDijk.angelic (Some y) τ).
          intros w1 ω01 t1.
          apply SDijk.assert_formula.
          apply
            {| msg_function        := "SMut.angelic_match_sum";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := subst δ0 ω01;
               msg_heap            := subst h0 ω01;
               msg_pathcondition   := wco w1;
            |}.
          apply (formula_eq (term_inr t1) (subst t ω01)).
          intros w2 ω12 _.
          apply (four kinr ω01). auto.
          apply (persist__term t1 ω12).
          apply (four (four POST ω01)).
          auto.
          apply (subst δ0 (wtrans ω01 ω12)).
          apply (subst h0 (wtrans ω01 ω12)).
      Defined.

      Definition demonic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr POST δ0 h0.
        apply SPath.demonic_binary.
        - apply (SDijk.demonic (Some x) σ).
          intros w1 ω01 t1.
          apply SDijk.assume_formula.
          apply (formula_eq (term_inl t1) (subst t ω01)).
          intros w2 ω12 _.
          apply (four kinl ω01). auto.
          apply (persist__term t1 ω12).
          apply (four (four POST ω01)).
          auto.
          apply (subst δ0 (wtrans ω01 ω12)).
          apply (subst h0 (wtrans ω01 ω12)).
        - apply (SDijk.demonic (Some y) τ).
          intros w1 ω01 t1.
          apply SDijk.assume_formula.
          apply (formula_eq (term_inr t1) (subst t ω01)).
          intros w2 ω12 _.
          apply (four kinr ω01). auto.
          apply (persist__term t1 ω12).
          apply (four (four POST ω01)).
          auto.
          apply (subst δ0 (wtrans ω01 ω12)).
          apply (subst h0 (wtrans ω01 ω12)).
      Defined.

      Definition demonic_match_sum_lifted {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr POST δ0 h0.
        eapply (SDijk.demonic_match_sum (A := fun w => SStore Γ2 w * SHeap w * AT w)%type x _ y _ _ t).
        - intros w1 ω01 t' POSTl.
          apply kinl. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTl. auto. auto.
          apply (subst δ0 ω01).
          apply (subst h0 ω01).
        - intros w1 ω01 t' POSTr.
          apply kinr. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTr. auto. auto.
          apply (subst δ0 ω01).
          apply (subst h0 ω01).
        - intros w1 ω01 [[δ1 h1] a1]. apply POST. auto. auto. auto. auto.
      Defined.

      Definition angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons POST δ0 h0.
        apply SPath.angelic_binary.
        - apply SDijk.assert_formula.
          apply
            {| msg_function        := "SMut.angelic_match_list";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ0;
               msg_heap            := h0;
               msg_pathcondition   := wco w0;
            |}.
          apply (formula_eq (term_lit (ty_list σ) []) t).
          intros w1 ω01 _.
          apply knil. auto.
          apply (four POST).
          auto.
          apply (subst δ0 ω01).
          apply (subst h0 ω01).
        - apply (SDijk.angelic (Some x) σ).
          intros w1 ω01 thead.
          apply (SDijk.angelic (Some y) (ty_list σ)).
          intros w2 ω12 ttail.
          apply SDijk.assert_formula.
          apply
            {| msg_function        := "SMut.angelic_match_list";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := subst δ0 (wtrans ω01 ω12);
               msg_heap            := subst h0 (wtrans ω01 ω12);
               msg_pathcondition   := wco w2;
            |}.
          apply (formula_eq (term_binop binop_cons (subst thead ω12) ttail) (subst t (wtrans ω01 ω12))).
          intros w3 ω23 _.
          apply (four kcons (wtrans ω01 ω12)). auto.
          apply (persist__term thead (wtrans ω12 ω23)).
          apply (persist__term ttail ω23).
          apply (four POST). apply (wtrans ω01 (wtrans ω12 ω23)).
          apply (subst δ0 (wtrans ω01 (wtrans ω12 ω23))).
          apply (subst h0 (wtrans ω01 (wtrans ω12 ω23))).
      Defined.

      Definition smutb_angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t knil kcons => angelic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons POST δ0 h0.
        apply SPath.demonic_binary.
        - apply SDijk.assume_formula.
          apply (formula_eq (term_lit (ty_list σ) []) t).
          intros w1 ω01 _.
          apply knil. auto.
          apply (four POST).
          auto.
          apply (subst δ0 ω01).
          apply (subst h0 ω01).
        - apply (SDijk.demonic (Some x) σ).
          intros w1 ω01 thead.
          apply (SDijk.demonic (Some y) (ty_list σ)).
          intros w2 ω12 ttail.
          apply SDijk.assume_formula.
          apply (formula_eq (term_binop binop_cons (subst thead ω12) ttail) (subst t (wtrans ω01 ω12))).
          intros w3 ω23 _.
          apply (four kcons (wtrans ω01 ω12)). auto.
          apply (persist__term thead (wtrans ω12 ω23)).
          apply (persist__term ttail ω23).
          apply (four POST). apply (wtrans ω01 (wtrans ω12 ω23)).
          apply (subst δ0 (wtrans ω01 (wtrans ω12 ω23))).
          apply (subst h0 (wtrans ω01 (wtrans ω12 ω23))).
      Defined.

      Definition smutb_demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t knil kcons => demonic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (angelic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (angelic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_prod"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (wtrans ω01 ω12); *)
          (*    msg_heap            := subst h0 (wtrans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_binop binop_pair (subst tσ ω12) tτ) (subst t (wtrans ω01 ω12))).
        intros w3 ω23.
        apply (four k (wtrans ω01 ω12)). auto.
        apply (persist__term tσ (wtrans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition smutb_angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_prod x y <$> persist__term t <*> four k.

      Definition demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (demonic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (demonic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_binop binop_pair (subst tσ ω12) tτ) (subst t (wtrans ω01 ω12))).
        intros w3 ω23.
        apply (four k (wtrans ω01 ω12)). auto.
        apply (persist__term tσ (wtrans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition smutb_demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_prod x y <$> persist__term t <*> four k.

      Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_record"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (wtrans ω01 ω12); *)
          (*    msg_heap            := subst h0 (wtrans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (subst t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (subst (T := fun Σ => NamedEnv (Term Σ) Δ) ts (wsub ω12)).
      Defined.

      Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (angelic_match_record' n p t k).
      Qed.

      Definition smutb_angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_record n p <$> persist__term t <*> four k.

      Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (subst t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (subst (T := fun Σ => NamedEnv (Term Σ) Δ) ts (wsub ω12)).
      Defined.

      Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (demonic_match_record' n p t k).
      Defined.

      Definition smutb_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_record n p <$> persist__term t <*> four k.

      Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_tuple"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (wtrans ω01 ω12); *)
          (*    msg_heap            := subst h0 (wtrans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
        (* |}. *)
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (subst t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (subst (T := fun Σ => NamedEnv (Term Σ) Δ) ts (wsub ω12)).
      Defined.

      Definition smutb_angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_tuple n p <$> persist__term t <*> four k.

      Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (subst t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (subst (T := fun Σ => NamedEnv (Term Σ) Δ) ts (wsub ω12)).
      Defined.

      Definition smutb_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_tuple n p <$> persist__term t <*> four k.

      Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ (SStore Γ -> SHeap -> Message) -> STerm σ -> SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 msg t.
        eapply (bind).
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply (bind_right).
        apply assert_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (subst t ω01)).
        intros w2 ω12.
        apply pure.
        apply (subst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ω12).
      Defined.

      Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ STerm σ -> SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 t.
        eapply (bind).
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply (bind_right).
        apply assume_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (subst t ω01)).
        intros w2 ω12.
        apply pure.
        apply (subst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ω12).
      Defined.

      Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := 𝑼𝑲 U)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 UK.
        eapply bind.
        apply (angelic None (𝑼𝑲_Ty UK)).
        intros w2 ω12 t__field.
        eapply bind_right.
        apply assert_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (wtrans ω01 ω12))).
        intros w3 ω23.
        eapply bind.
        apply (angelic_match_pattern n (p UK)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w3;
            |}.
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (wtrans ω01 (wtrans ω12 ω23)).
      Defined.

      Definition smutb_angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => angelic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

      Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := 𝑼𝑲 U)).
        intros w1 ω01 UK.
        eapply bind.
        apply (demonic None (𝑼𝑲_Ty UK)).
        intros w2 ω12 t__field.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (wtrans ω01 ω12))).
        intros w3 ω23.
        eapply bind.
        apply (demonic_match_pattern n (p UK)).
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (wtrans ω01 (wtrans ω12 ω23)).
      Defined.

      Definition smutb_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => demonic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

    End PatternMatching.

    Section State.

      Definition pushpop {AT Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t m POST δ h.
        apply m.
        intros w1 ω01 a1 δ1 h1.
        apply POST. auto. auto. apply (env_tail δ1). apply h1.
        apply env_snoc.
        apply δ.
        apply t.
        apply h.
      Defined.

      Definition pushspops {AT Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 δΔ m POST δ h.
        apply m.
        intros w1 ω01 a1 δ1 h1.
        apply POST. auto. auto. apply (env_drop Δ δ1). apply h1.
        apply env_cat.
        apply δ.
        apply δΔ.
        apply h.
      Defined.

      Definition get_local {Γ} : ⊢ SMut Γ Γ (SStore Γ) :=
        fun w0 POST δ => T POST δ δ.
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SMut Γ1 Γ2 Unit :=
        fun w0 δ POST _ => T POST tt δ.
      Definition get_heap {Γ} : ⊢ SMut Γ Γ SHeap :=
        fun w0 POST δ h => T POST h δ h.
      Definition put_heap {Γ} : ⊢ SHeap -> SMut Γ Γ Unit :=
        fun w0 h POST δ _ => T POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SMut Γ Γ (STerm σ).
        intros w POST δ h.
        apply POST.
        apply wrefl.
        apply (seval_exp δ e).
        auto.
        auto.
      Defined.

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SMut Γ Γ (SStore σs).
        intros w POST δ h.
        apply POST. apply wrefl.
        refine (env_map _ es).
        intros b. apply (seval_exp δ).
        auto.
        auto.
      Defined.

      Definition assign {Γ} x {σ} {xIn : x::σ ∈ Γ} : ⊢ STerm σ -> SMut Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn w} v.

    End State.

    Section ProduceConsume.

      Definition produce_chunk {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit.
      Proof.
        intros w0 c k δ h.
        apply k. apply wrefl.
        constructor. apply δ.
        apply (cons c h).
      Defined.

      Equations(noeqns) match_chunk {w : World} (c1 c2 : Chunk w) : List Formula w :=
        match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2)
        with eq_dec p1 p2 => {
          match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2) (left eq_refl) := formula_eqs_ctx vs1 vs2;
          match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2) (right _) :=
            cons (formula_bool (term_lit ty_bool false)) nil
        };
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
        with eq_dec_het r1 r2 => {
          match_chunk (chunk_ptsreg r1 v1) (chunk_ptsreg r2 v2) (left eq_refl) := cons (formula_eq v1 v2) nil;
          match_chunk (chunk_ptsreg r1 v1) (chunk_ptsreg r2 v2) (right _)      :=
            cons (formula_bool (term_lit ty_bool false)) nil
        };
        match_chunk _ _  := cons (formula_bool (term_lit ty_bool false)) nil.

      Lemma inst_match_chunk {w : World} (c1 c2 : Chunk w) (ι : SymInstance w) :
        instpc (match_chunk c1 c2) ι <-> inst c1 ι = inst c2 ι.
      Proof.
        split.
        - destruct c1, c2; cbn.
          + destruct (eq_dec p p0).
            * destruct e; cbn.
              rewrite inst_formula_eqs_ctx.
              intuition.
            * intros HYP; cbv in HYP. discriminate.
          + intros HYP; cbv in HYP. discriminate.
          + intros HYP; cbv in HYP. discriminate.
          + destruct (eq_dec_het r r0).
            * dependent elimination e; cbn.
              rewrite inst_pathcondition_cons.
              now intros [-> _].
            * intros HYP; cbv in HYP. discriminate.
        - destruct c1, c2; cbn; intros Heq.
          + remember (inst ts ι) as vs1.
            remember (inst ts0 ι) as vs2.
            dependent elimination Heq.
            rewrite EqDec.eq_dec_refl. cbn.
            rewrite inst_formula_eqs_ctx.
            subst. auto.
          + dependent elimination Heq.
          + dependent elimination Heq.
          + remember (inst t ι) as v1.
            remember (inst t0 ι) as v2.
            dependent elimination Heq.
            unfold eq_dec_het.
            rewrite EqDec.eq_dec_refl. cbn.
            rewrite inst_pathcondition_cons.
            subst. split; auto. constructor.
      Qed.

      Definition consume_chunk {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit.
      Proof.
        intros w0 c.
        eapply bind.
        apply get_heap.
        intros w1 ω01 h.
        eapply bind.
        apply (angelic_list
                 (A := Pair Chunk SHeap)
                 (fun δ h =>
                    {| msg_function := "consume_chunk";
                       msg_message := "Empty extraction";
                       msg_program_context := Γ;
                       msg_localstore := δ;
                       msg_heap := h;
                       msg_pathcondition := wco w1
                    |})
                 (heap_extractions h)).
        intros w2 ω12 [c' h'].
        eapply bind_right.
        apply assert_formulas.
        apply (match_chunk (subst c (wtrans ω01 ω12)) c').
        intros w3 ω23.
        apply put_heap.
        apply (subst h' ω23).
      Defined.

      (* Definition smut_leakcheck {Γ Σ} : SMut Γ Γ Unit Σ := *)
      (*   smut_get_heap >>= fun _ _ h => *)
      (*   match h with *)
      (*   | nil => smut_pure tt *)
      (*   | _   => smut_error "SMut.leakcheck" "Heap leak" h *)
      (*   end. *)

      Definition produce_fail_recursion {Γ} :
        ⊢ Assertion -> SMut Γ Γ Unit.
      Proof.
        refine
          (fix produce w0 asn {struct asn} :=
             match asn with
             | asn_sep asn1 asn2 =>
               bind_right
                 (produce w0 asn1)
                 (* Recursive call to produce has principal argument equal to "persist asn2 ω01" *)
                 (* instead of one of the following variables: "asn1" "asn2". *)
                 (produce <$> persist asn2)
             | _ => @block _ _ _ _
             end).
      Abort.

      Definition produce {Γ} :
        ⊢ Assertion -> □(SMut Γ Γ Unit).
      Proof.
        refine (fix produce w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assume_formula fml).
        - apply (produce_chunk <$> persist c).
        - apply (demonic_match_bool <$> persist__term b <*> four (produce _ asn1) <*> four (produce _ asn2)).
        - intros w1 ω01.
          apply (demonic_match_enum
                    (persist__term k ω01)
                    (fun EK : 𝑬𝑲 E => four (produce w0 (alts EK)) ω01)).
        - intros w1 ω01.
          eapply (demonic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr).
          apply (persist__term s). auto.
          + intros w2 ω12 t2.
            apply (produce (wsnoc w0 (xl :: σ)) asn1).
            apply (wsnoc_sub (wtrans ω01 ω12) (xl :: σ) t2).
          + intros w2 ω12 t2.
            apply (produce (wsnoc w0 (xr :: τ)) asn2).
            apply (wsnoc_sub (wtrans ω01 ω12) (xr :: τ) t2).
        - apply (smutb_demonic_match_list xh xt s).
          + apply (produce _ asn1).
          + intros w1 ω01 thead ttail.
            apply (produce (wsnoc (wsnoc w0 (xh :: _)) (xt :: _)) asn2 w1).
            apply (wsnoc_sub (wsnoc_sub ω01 (xh :: _) thead) (xt :: _) ttail).
        - apply (smutb_demonic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (produce (wsnoc (wsnoc w0 (xl :: σ1)) (xr :: σ2)) asn w1).
          apply (wsnoc_sub (wsnoc_sub ω01 (xl :: σ1) t1) (xr :: σ2) t2).
        - apply (smutb_demonic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (produce (MkWorld (subst (wco w0) (sub_cat_left Δ))) asn w1).
          apply (MkAcc (MkWorld (subst (wco w0) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)).
        - apply (smutb_demonic_match_record id p s).
          intros w1 ω01 ts.
          apply (produce (MkWorld (subst (wco w0) (sub_cat_left Δ))) asn w1).
          apply (MkAcc (MkWorld (subst (wco w0) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)).
        - apply (smutb_demonic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (produce (MkWorld (subst (wco w0) (sub_cat_left (alt__ctx UK)))) (alt__rhs UK) w1).
          apply (MkAcc (MkWorld (subst (wco w0) (sub_cat_left _))) w1 (wsub ω01 ►► ts)).
        - apply (bind_right <$> produce _ asn1 <*> four (produce _ asn2)).
        - intros w1 ω01.
          eapply bind.
          apply (@demonic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (produce (wsnoc w0 (ς :: τ)) asn w2).
          apply (wsnoc_sub (wtrans ω01 ω12) (ς :: τ) t2).
        - intros w1 ω01.
          apply debug.
          intros δ h.
          apply (MkSDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

      Definition consume {Γ} :
        ⊢ Assertion -> □(SMut Γ Γ Unit).
      Proof.
        refine (fix consume w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assert_formula fml).
        - apply (consume_chunk <$> persist c).
        - apply (angelic_match_bool <$> persist__term b <*> four (consume _ asn1) <*> four (consume _ asn2)).
        - intros w1 ω01.
          apply (angelic_match_enum
                    (persist__term k ω01)
                    (fun EK : 𝑬𝑲 E => four (consume w0 (alts EK)) ω01)).
        - intros w1 ω01.
          eapply (angelic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr).
          apply (persist__term s). auto.
          + intros w2 ω12 t2.
            apply (consume (wsnoc w0 (xl :: σ)) asn1).
            apply (wsnoc_sub (wtrans ω01 ω12) (xl :: σ) t2).
          + intros w2 ω12 t2.
            apply (consume (wsnoc w0 (xr :: τ)) asn2).
            apply (wsnoc_sub (wtrans ω01 ω12) (xr :: τ) t2).
        - apply (smutb_angelic_match_list xh xt s).
          + apply (consume _ asn1).
          + intros w1 ω01 thead ttail.
            apply (consume (wsnoc (wsnoc w0 (xh :: _)) (xt :: _)) asn2 w1).
            apply (wsnoc_sub (wsnoc_sub ω01 (xh :: _) thead) (xt :: _) ttail).
        - apply (smutb_angelic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (consume (wsnoc (wsnoc w0 (xl :: σ1)) (xr :: σ2)) asn w1).
          apply (wsnoc_sub (wsnoc_sub ω01 (xl :: σ1) t1) (xr :: σ2) t2).
        - apply (smutb_angelic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (consume (MkWorld (subst (wco w0) (sub_cat_left Δ))) asn w1).
          apply (MkAcc (MkWorld (subst (wco w0) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)).
        - apply (smutb_angelic_match_record id p s).
          intros w1 ω01 ts.
          apply (consume (MkWorld (subst (wco w0) (sub_cat_left Δ))) asn w1).
          apply (MkAcc (MkWorld (subst (wco w0) (sub_cat_left Δ))) w1 (wsub ω01 ►► ts)).
        - apply (smutb_angelic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (consume (MkWorld (subst (wco w0) (sub_cat_left (alt__ctx UK)))) (alt__rhs UK) w1).
          apply (MkAcc (MkWorld (subst (wco w0) (sub_cat_left _))) w1 (wsub ω01 ►► ts)).
        - apply (bind_right <$> consume _ asn1 <*> four (consume _ asn2)).
        - intros w1 ω01.
          eapply bind.
          apply (@angelic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (consume (wsnoc w0 (ς :: τ)) asn w2).
          apply (wsnoc_sub (wtrans ω01 ω12) (ς :: τ) t2).
        - intros w1 ω01.
          apply debug.
          intros δ h.
          apply (MkSDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

    End ProduceConsume.

    Section Exec.

      Variable cfg : Config.

      Definition call_contract {Γ Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SMut Γ Γ (STerm τ).
      Proof.
        refine
          (match c with
           | MkSepContract _ _ Σe δe req result ens => _
           end).
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind_right.
        apply (assert_formulas
                 (* {| *)
                 (*   msg_function := "SMut.call"; *)
                 (*   msg_message := "argument pattern match"; *)
                 (*   msg_program_context := Γ; *)
                 (*   msg_localstore := subst δ0 ω01; *)
                 (*   msg_heap := subst h0 ω01; *)
                 (*   msg_pathcondition := wco w1; *)
                 (* |} *) (formula_eqs_pctx (subst δe evars) (subst args ω01))).
        intros w2 ω12.
        eapply bind_right.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (wtrans _ ω12).
        constructor. cbn. apply evars.
        intros w3 ω23.
        eapply bind.
        apply (demonic (Some result)).
        intros w4 ω34 res.
        eapply bind_right.
        apply (produce
                 (w := @MkWorld (Σe ▻ (result::τ)) nil)
                 ens).
        constructor. cbn.
        apply sub_snoc; cbn.
        apply (subst (T := Sub _) evars).
        apply (wtrans ω12 (wtrans ω23 ω34)).
        apply res.
        intros w5 ω45. clear - res ω45.
        apply pure.
        apply (persist__term res ω45).
      Defined.

      Definition call_contract_debug {Γ Δ τ} (f : 𝑭 Δ τ) (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SMut Γ Γ (STerm τ) :=
        fun w0 δΔ =>
          let o := call_contract c δΔ in
          if config_debug_function cfg f
          then
            debug
              (fun δ h => {| sdebug_call_function_parameters := Δ;
                             sdebug_call_function_result_type := τ;
                             sdebug_call_function_name := f;
                             sdebug_call_function_contract := c;
                             sdebug_call_function_arguments := δΔ;
                             sdebug_call_program_context := Γ;
                             sdebug_call_pathcondition := wco w0;
                             sdebug_call_localstore := δ;
                             sdebug_call_heap := h|})
              o
          else o.

      Fixpoint exec {Γ τ} (s : Stm Γ τ) {struct s} :
        ⊢ SMut Γ Γ (STerm τ).
      Proof.
        intros w0; destruct s.
        - apply pure. apply (term_lit τ l).
        - apply (eval_exp e).
        - eapply bind. apply (exec _ _ s1).
          intros w1 ω01 t1.
          eapply (pushpop t1).
          apply (exec _ _ s2).
        - eapply (pushspops (lift δ)).
          apply (exec _ _ s).
        - eapply bind.
          apply (exec _ _ s).
          intros w1 ω01 t.
          eapply bind_right.
          apply (assign x t).
          intros w2 ω12.
          apply pure.
          apply (subst (T := STerm τ) t (wsub ω12)).
        - eapply bind.
          apply (eval_exps es).
          intros w1 ω01 args.
          destruct (CEnv f) as [c|].
          + apply (call_contract_debug f c args).
          + apply (error "SMut.exec" "Function call without contract" (f,args)).
        - rename δ into δΔ.
          eapply bind.
          apply get_local.
          intros w1 ω01 δ1.
          eapply bind_right.
          apply (put_local (lift δΔ)).
          intros w2 ω12.
          eapply bind.
          apply (exec _ _ s).
          intros w3 ω23 t.
          eapply bind_right.
          apply put_local.
          apply (subst δ1 (wtrans ω12 ω23)).
          intros w4 ω34.
          apply pure.
          apply (subst (T := STerm _) t ω34).
        - eapply bind.
          apply (eval_exps es).
          intros w1 ω01 args.
          apply (call_contract (CEnvEx f) args).
        - eapply bind. apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_bool t).
          + intros w2 ω12.
            apply (exec _ _ s1).
          + intros w2 ω12.
            apply (exec _ _ s2).
        - eapply bind_right.
          apply (exec _ _ s1).
          intros w1 ω01.
          apply (exec _ _ s2).
        - eapply bind. apply (eval_exp e1).
          intros w1 ω01 t.
          eapply bind_right.
          apply (assume_formula (formula_bool t)).
          intros w2 ω12.
          apply (exec _ _ s).
        - apply block.
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_list (𝑿to𝑺 xh) (𝑿to𝑺 xt) t).
          + intros w2 ω12.
            apply (exec _ _ s1).
          + intros w2 ω12 thead ttail.
            eapply (pushspops (env_snoc (env_snoc env_nil (xh,_) thead) (xt,_) ttail)).
            apply (exec _ _ s2).
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_sum (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t).
          + intros w2 ω12 tl.
            eapply (pushpop tl).
            apply (exec _ _ s1).
          + intros w2 ω12 tr.
            eapply (pushpop tr).
            apply (exec _ _ s2).
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_prod (𝑿to𝑺 xl) (𝑿to𝑺 xr) t).
          intros w2 ω12 t1 t2.
          eapply (pushspops (env_snoc (env_snoc env_nil (_,_) t1) (_,_) t2)).
          apply (exec _ _ s).
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_enum t).
          intros EK.
          intros w2 ω12.
          apply (exec _ _ (alts EK)).
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_tuple 𝑿to𝑺 p t).
          intros w2 ω12 ts.
          eapply (pushspops ts).
          apply (exec _ _ s).
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_union 𝑿to𝑺 alt__pat t).
          intros UK w2 ω12 ts.
          eapply (pushspops ts).
          apply (exec _ _ (alt__rhs UK)).
        - eapply bind.
          apply (eval_exp e).
          intros w1 ω01 t.
          apply (demonic_match_record 𝑿to𝑺 p t).
          intros w2 ω12 ts.
          eapply (pushspops ts).
          apply (exec _ _ s).
        - eapply bind.
          apply (angelic None τ).
          intros w1 ω01 t.
          eapply bind_right.
          apply (T (consume (asn_chunk (chunk_ptsreg reg t)))).
          intros w2 ω12.
          eapply bind_right.
          apply (T (produce (asn_chunk (chunk_ptsreg reg (subst t ω12))))).
          intros w3 ω23.
          apply pure.
          apply (subst (T := STerm _) t (wtrans ω12 ω23)).
        - eapply bind.
          eapply (angelic None τ).
          intros w1 ω01 told.
          eapply bind_right.
          apply (T (consume (asn_chunk (chunk_ptsreg reg told)))).
          intros w2 ω12.
          eapply bind.
          apply (eval_exp e).
          intros w3 ω23 tnew.
          eapply bind_right.
          apply (T (produce (asn_chunk (chunk_ptsreg reg tnew)))).
          intros w4 ω34.
          apply pure.
          apply (subst (T := STerm _) tnew ω34).
        - apply (error "SMut.exec" "stm_bind not supported" tt).
        - apply debug.
          intros δ0 h0.
          econstructor.
          apply (wco w0).
          apply δ0.
          apply h0.
          apply (exec _ _ s).
      Defined.
      Global Arguments exec {_ _} _ {w} _ _ _.

      Import Notations.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        SMut Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := [] |} :=
        match c with
        | MkSepContract _ _ Σ δ req result ens =>
          produce (w:=@MkWorld _ _) req wrefl >> fun w1 ω01 =>
          exec s >>= fun w2 ω12 res =>
          consume
            (w:=wsnoc (@MkWorld _ []) (result :: τ))
            ens
            (wsnoc_sub (wtrans ω01 ω12) (result :: τ) res)
        end.

      Definition exec_contract_path {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) : SPath wnil :=
        demonic_close (exec_contract c s (fun w1 ω01 _ δ1 h1 => SPath.block) (sep_contract_localstore c) nil).

      Definition ValidContractWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        VerificationCondition (prune (exec_contract_path c body)).

    End Exec.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (prune (exec_contract_path default_config c body)).

    (* Print Assumptions ValidContract. *)

    Section EvarEnv.

      Section CallerContext.

        Context {Γ : PCtx}.

        Definition consume_chunk_evarenv {Σe} (c : Chunk Σe) :
          ⊢ EvarEnv Σe -> SMut Γ Γ (EvarEnv Σe).
        Proof.
          intros w0 L0 POST δ0 h0.
          apply (SDijk.angelic_list (A := Pair (EvarEnv Σe) SHeap)).
          apply {| msg_function := "SMut.consume_chunk_evar";
                   msg_message := "Empty extraction";
                   msg_program_context := Γ;
                   msg_localstore := δ0;
                   msg_heap := h0;
                   msg_pathcondition := wco w0
                |}.
          apply (extract_chunk c h0 L0).
          intros w1 ω01 [L1 h1].
          apply POST. auto. auto.
          apply (subst δ0 ω01).
          auto.
        Defined.

        (* This function tries to assert the equality between the terms `te` from *)
        (*     a callee context and `tr` from the caller context. The callee context *)
        (*     variables are all evars and if possible, it will fill in evars that are *)
        (*     strictly necessary for the assertion to be true. *)
        Definition assert_term_eq_evar {Σe σ} (te : STerm σ Σe) :
          ⊢ STerm σ -> EvarEnv Σe -> SMut Γ Γ (EvarEnv Σe) :=
          fun w0 tr L0 =>
            (* Try to fully match te against tr1, potentially filling in some evars. *)
            match match_term te tr L0 with
            | Some L1 => pure L1
            | None =>
              (* The match failed. See if all evars in te are already known.*)
              match eval_term_evar L0 te with
              | Some te1 =>
                (* All evars are known. So assert the equality between the terms in *)
                (*            the caller context. *)
                bind
                  (assert_formula (formula_eq te1 tr))
                  (fun w1 ω01 _ => pure (subst L0 ω01))
              | None =>
                (* Give up. This is currently missing some corner cases where a *)
        (*            sub-term of te would already constrain all appearing evars, but *)
        (*            which can't be fully unified with tr. match_term could be *)
        (*            augmented to also handle this kind of case. *)
                error
                  "SMut.assert_term_eq_evar"
                  "Uninstantiated evars variable"
                  {| evarerror_env := L0;
                     evarerror_data := (te,tr)
                  |}
              end
            end.

        Equations(noeqns) assert_namedenv_eq_evar {X Σe σs}
                 (te : NamedEnv (X:=X) (Term Σe) σs) {w0 : World}
                 (tr : NamedEnv (Term w0) σs)
                 (L0 : EvarEnv Σe w0) : SMut Γ Γ (EvarEnv Σe) w0 :=
          assert_namedenv_eq_evar env_nil             env_nil L0 := pure L0;
          assert_namedenv_eq_evar (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) L0 :=
            bind (assert_namedenv_eq_evar E1 E2 L0)
              (fun w1 ω01 L1 =>
                 assert_term_eq_evar t1 (subst (T := STerm _) t2 ω01) L1).

        Definition consume_formula_evarenv {Σe} (fml : Formula Σe) :
          ⊢ EvarEnv Σe -> SMut Γ Γ (EvarEnv Σe) :=
          fun w0 L =>
            match fml with
            | formula_bool t =>
              match eval_term_evar L t with
              | Some t0 => bind
                             (assert_formula (formula_bool t0))
                             (fun w ω01 _ => pure (subst L ω01))
              | None => error
                          "SMut.consume_formula_evar"
                          "Uninstantiated evars when consuming formula"
                          {| evarerror_env := L; evarerror_data := fml |}
              end
            | formula_prop ζ P =>
              match evarenv_to_option_sub L with
              | Some s => bind
                            (assert_formula (formula_prop (subst ζ s) P))
                            (fun w1 ω01 _ => pure (subst L ω01))
              | None => error
                          "SMut.consume_formula_evar"
                          "Uninstantiated evars when consuming formula"
                          {| evarerror_env := L; evarerror_data := fml |}
              end
            | formula_eq t1 t2 =>
              match eval_term_evar L t1 , eval_term_evar L t2 with
              | Some t1' , Some t2' => bind
                                         (assert_formula (formula_eq t1' t2'))
                                         (fun w1 ω01 _ => pure (subst L ω01))
              | Some t1' , None     => assert_term_eq_evar t2 t1' L
              | None     , Some t2' => assert_term_eq_evar t1 t2' L
              | None     , None     => error
                                         "SMut.consume_formula_evar"
                                         "Uninstantiated evars when consuming formula"
                                         {| evarerror_env := L; evarerror_data := fml |}
              end
            | @formula_neq _ σ t1 t2 =>
              match eval_term_evar L t1 , eval_term_evar L t2 with
              | Some t1' , Some t2' => bind
                                         (assert_formula (formula_neq t1' t2'))
                                         (fun w1 ω01 _ => pure (subst L ω01))
              (* | Some t1' , None     => smut_assert_term_eq_evar t2 t1' L *)
              (* | None     , Some t2' => smut_assert_term_eq_evar t1 t2' L *)
              | _        , _        => error
                                         "SMut.consume_formula_evar"
                                         "Uninstantiated evars when consuming formula"
                                         {| evarerror_env := L; evarerror_data := fml |}
              end
            end.

        Fixpoint consume_evarenv {Σe : LCtx} (asn : Assertion Σe) {Σr: World} (L : EvarEnv Σe Σr) {struct asn} :
          SMut Γ Γ (EvarEnv Σe) Σr :=
          match asn with
          | asn_formula fml => consume_formula_evarenv fml L
          | asn_chunk c => consume_chunk_evarenv c L
          | asn_if b a1 a2 =>
            match eval_term_evar L b with
            | Some b' => angelic_match_bool b'
                           (fun w1 ω01 => consume_evarenv a1 (subst L ω01))
                           (fun w1 ω01 => consume_evarenv a2 (subst L ω01))
            | None    => error
                           "consume_evarenv"
                           "Uninstantiated evars when consuming assertion"
                           {| evarerror_env := L;
                              evarerror_data := asn
                           |}
            end
          | asn_match_enum E k alts =>
            match eval_term_evar L k with
            | Some k1 =>
              angelic_match_enum k1
                (fun K w1 ω01 => consume_evarenv (alts K) (subst L ω01))
            | None => error
                        "consume_evarenv"
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
                Lxl' <- consume_evarenv alt_inl Lxl ;;
                pure (env_tail Lxl')
              | Some (inr t) =>
                let Lxr := L ► (xr∶τ ↦ Some t) in
                Lxr' <- consume_evarenv alt_inr Lxr ;;
                pure (env_tail Lxr')
              | None =>
                angelic_binary
                  (let Lxl := L ► (xl∶σ ↦ None) in
                    consume_evarenv alt_inl Lxl >>= fun _ ζ Lxl' =>
                      match env_unsnoc Lxl' with
                      | (L' , Some t) =>
                        (* TODO(2.0): This assert should move before the *)
                        (* consumption of the alternative. *)
                        bind
                          (assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) s ζ) (term_inl t)))
                          (fun w1 ω01 _ => pure (subst L' ω01))
                      | (_ , None) =>
                        error
                          "consume_evarenv"
                          "Uninstantiated evars when consuming assertion"
                          {| evarerror_env := Lxl;
                             evarerror_data := alt_inl
                          |}
                      end)
                  (let Lxr := L ► (xr∶τ ↦ None) in
                    consume_evarenv alt_inr Lxr >>= fun _ ζ Lxr' =>
                      match env_unsnoc Lxr' with
                      | (L' , Some t) =>
                        (* TODO(2.0): This assert should move before the *)
                        (* consumption of the alternative. *)
                        bind
                          (assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) s ζ) (term_inr t)))
                          (fun w1 ω01 _ => pure (subst L' ω01))
                      | (_ , None) =>
                        error
                          "consume_evarenv"
                          "Uninstantiated evars when consuming assertion"
                          {| evarerror_env := Lxr;
                             evarerror_data := alt_inr
                          |}
                      end)
              end
            | _ => error
                     "consume_evarenv"
                     "Uninstantiated evars when consuming assertion"
                     {| evarerror_env := L;
                        evarerror_data := asn
                     |}
            end
          | asn_match_list s alt_nil xh xt alt_cons =>
            error "consume_evarenv" "Not implemented" asn
          | asn_match_prod scr xl xr rhs =>
            match eval_term_evar L scr with
            | Some s =>
              match term_get_pair s with
              | Some (tl, tr) =>
                let Lrhs := L ► (xl∶_ ↦ Some tl) ► (xr∶_ ↦ Some tr) in
                Lrhs' <- consume_evarenv rhs Lrhs ;;
                pure (env_tail (env_tail Lrhs'))
              | None =>
                error "consume_evarenv" "Not implemented" asn
              end
            | None => error
                        "consume_evarenv"
                        "Uninstantiated evars when consuming assertion"
                        {| evarerror_env := L;
                           evarerror_data := asn
                        |}
            end
          | asn_match_tuple s p rhs =>
            error "consume_evarenv" "Not implemented" asn
          | asn_match_record R scr p rhs =>
            match eval_term_evar L scr with
            | Some s =>
              match term_get_record s with
              | Some ts  =>
                let ζ__R := record_pattern_match_env p ts in
                let LR := L ►► env_map (fun _ t => Some t) ζ__R in
                bind
                  (consume_evarenv rhs LR)
                  (fun w1 ω01 LR' => pure (env_drop _ LR'))
              | None =>
                error "consume_evarenv" "Not implemented" asn
              end
            | None => error
                        "consume_evarenv"
                        "Uninstantiated evars when consuming assertion"
                        {| evarerror_env := L;
                           evarerror_data := asn
                        |}
            end
          | asn_match_union U s alt__ctx alt__pat alt__rhs =>
            error  "consume_evarenv" "Not implemented" asn
          | asn_sep a1 a2 =>
            consume_evarenv a1 L >>= fun _ _ => consume_evarenv a2
          | asn_exist ς τ a =>
            (* Dynamically allocate a new evar ς in the EvarEnv. *)
            let Lς := L ► (ς∶τ ↦ None) in
            consume_evarenv a Lς >>= fun _ _ Lς' =>
            (* Split off the last evar again. *)
            match env_unsnoc Lς' with
            | (L' , Some _) =>
              (* ς has been instantiated during execution. So we just return the
              final EvarEnv with ς stripped off. *)
              pure L'
            | (_  , None)   =>
              (* During execution the evar ς was never instantiated, so fail. *)
              error
                "consume_evarenv"
                "Uninstantiated evars when consuming assertion"
                {| evarerror_env := L;
                   evarerror_data := asn
                |}
            end
          | asn_debug =>
            debug
              (fun δ1 h1 =>
                 {| sdebug_asn_pathcondition := wco _;
                    sdebug_asn_program_context := Γ;
                    sdebug_asn_localstore := δ1;
                    sdebug_asn_heap := h1;
                 |})
              (pure L)
          end.

        Definition call_contract_evarenv {Δ τ} (c : SepContract Δ τ) :
          ⊢ SStore Δ -> SMut Γ Γ (STerm τ).
        Proof.
          refine
            (match c with
             | MkSepContract _ _ Σe δe req result ens => _
             end).
          intros w0 args.
          eapply bind.
          apply (consume_evarenv req).
          apply (create_evarenv Σe w0).
          intros w1 ω01 EE1.
          eapply bind.
          apply (assert_namedenv_eq_evar δe (subst args ω01) EE1).
          intros w2 ω12 EE2.
          destruct (evarenv_to_option_sub EE2) as [ζ|].
          - eapply bind.
            apply (demonic (Some result)).
            intros w3 ω23 res.
            eapply bind_right.
            apply (produce
                     (w := @MkWorld (Σe ▻ (result::τ)) nil)
                     ens).
            constructor. cbn.
            apply sub_snoc; cbn.
            apply (subst (T := Sub _) ζ ω23).
            apply res.
            intros w4 ω34.
            apply pure.
            apply (persist__term res ω34).
          - apply (error
                     "SMut.call_evar"
                     "Uninstantiated evars after consuming precondition"
                     {| evarerror_env := EE2;
                        evarerror_data := (c,args)
                     |}).
        Defined.

      End CallerContext.

      Section WithConfig.

        Variable cfg : Config.

        Definition call_contract_debug_evarenv {Γ Δ τ} (f : 𝑭 Δ τ) (c : SepContract Δ τ) :
          ⊢ SStore Δ -> SMut Γ Γ (STerm τ) :=
          fun w args =>
            let o := call_contract_evarenv c args in
            if config_debug_function cfg f
            then
              debug
                (fun δ h =>
                   {| sdebug_call_function_parameters := Δ;
                      sdebug_call_function_result_type := τ;
                      sdebug_call_function_name := f;
                      sdebug_call_function_contract := c;
                      sdebug_call_function_arguments := args;
                      sdebug_call_program_context := Γ;
                      sdebug_call_pathcondition := wco w;
                      sdebug_call_localstore := δ;
                      sdebug_call_heap := h
                   |})
                o
            else o.

        Fixpoint exec_evarenv {Γ τ} (s : Stm Γ τ) {struct s} :
          ⊢ SMut Γ Γ (STerm τ).
        Proof.
          intros w0; destruct s.
          - apply pure. apply (term_lit τ l).
          - apply (eval_exp e).
          - eapply bind. apply (exec_evarenv _ _ s1).
            intros w1 ω01 t1.
            eapply (pushpop t1).
            apply (exec_evarenv _ _ s2).
          - eapply (pushspops (lift δ)).
            apply (exec_evarenv _ _ s).
          - eapply bind.
            apply (exec_evarenv _ _ s).
            intros w1 ω01 t POST δ1 h1.
            apply POST. apply wrefl. apply t.
            apply (δ1 ⟪ x ↦ t ⟫)%env.
            apply h1.
          - eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            destruct (CEnv f) as [c|].
            + apply (call_contract_debug_evarenv f c args).
            + apply (error "SMut.exec_evarenv" "Function call without contract" (f,args)).
          - rename δ into δΔ.
            intros POST δ0 h0.
            apply (exec_evarenv _ _ s).
            intros w1 ω01 t δΔ' h1.
            apply POST. auto. auto.
            apply (subst δ0 ω01). auto.
            apply (lift δΔ). auto.
          - eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            apply (call_contract_evarenv (CEnvEx f) args).
          - eapply bind. apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_bool t).
            + intros w2 ω12.
              apply (exec_evarenv _ _ s1).
            + intros w2 ω12.
              apply (exec_evarenv _ _ s2).
          - eapply bind_right.
            apply (exec_evarenv _ _ s1).
            intros w1 ω01.
            apply (exec_evarenv _ _ s2).
          - eapply bind. apply (eval_exp e1).
            intros w1 ω01 t.
            eapply bind_right.
            apply (assume_formula (formula_bool t)).
            intros w2 ω12.
            apply (exec_evarenv _ _ s).
          - apply block.
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_list (𝑿to𝑺 xh) (𝑿to𝑺 xt) t).
            + intros w2 ω12.
              apply (exec_evarenv _ _ s1).
            + intros w2 ω12 thead ttail.
              eapply (pushspops (env_snoc (env_snoc env_nil (xh,_) thead) (xt,_) ttail)).
              apply (exec_evarenv _ _ s2).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_sum (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t).
            + intros w2 ω12 tl.
              eapply (pushpop tl).
              apply (exec_evarenv _ _ s1).
            + intros w2 ω12 tr.
              eapply (pushpop tr).
              apply (exec_evarenv _ _ s2).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_prod (𝑿to𝑺 xl) (𝑿to𝑺 xr) t).
            intros w2 ω12 t1 t2.
            eapply (pushspops (env_snoc (env_snoc env_nil (_,_) t1) (_,_) t2)).
            apply (exec_evarenv _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_enum t).
            intros EK.
            intros w2 ω12.
            apply (exec_evarenv _ _ (alts EK)).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_tuple 𝑿to𝑺 p t).
            intros w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_evarenv _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_union 𝑿to𝑺 alt__pat t).
            intros UK w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_evarenv _ _ (alt__rhs UK)).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_record 𝑿to𝑺 p t).
            intros w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_evarenv _ _ s).
          - eapply bind.
            apply
              (let x := fresh w0 None in
               consume_chunk_evarenv (chunk_ptsreg reg (@term_var [(x,_)] x _ inctx_zero)) [None]%arg).
            intros w1 ω01 EE1.
            destruct (snocView EE1). clear E.
            destruct v.
            + eapply bind_right.
              apply (produce_chunk (chunk_ptsreg reg t)).
              intros w2 ω12.
              apply pure.
              apply (persist__term t ω12).
            + apply (error "SMut.exec_evarenv" "You have found a unicorn." tt).
          - eapply bind.
            apply
              (let x := fresh w0 None in
               consume_chunk_evarenv (chunk_ptsreg reg (@term_var [(x,_)] x _ inctx_zero)) [None]%arg).
            intros w1 ω01 _.
            eapply bind.
            apply (eval_exp e).
            intros w2 ω12 tnew.
            eapply bind_right.
            apply (produce_chunk (chunk_ptsreg reg tnew)).
            intros w3 ω23.
            apply pure.
            apply (persist__term tnew ω23).
          - apply (error "SMut.exec_evarenv" "stm_bind not supported" tt).
          - apply debug.
            intros δ0 h0.
            econstructor.
            apply (wco w0).
            apply δ0.
            apply h0.
            apply (exec_evarenv _ _ s).
        Defined.
        Global Arguments exec_evarenv {_ _} _ {w} _ _ _.

        Definition exec_contract_evarenv {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
          SMut Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := [] |}.
        Proof.
          refine
            (
          match c with
          | MkSepContract _ _ Σ δ req result ens =>
            bind_right
              (produce (w:=@MkWorld _ _) req wrefl)
              (fun w1 ω01 =>
                 exec_evarenv s >>= fun w2 ω12 res => _)
            (* consume *)
            (*   (w:=wsnoc (@MkWorld _ []) (result :: τ)) *)
            (*   ens *)
            (*   (wsnoc_sub (wtrans ω01 ω12) (result :: τ) res) *)
          end).
          eapply bind_right.
          eapply (consume_evarenv ens).
          refine (subst (create_evarenv_id _) (sub_snoc (wtrans ω01 ω12) (result,τ) res)).
          intros w3 ω23. apply block.
        Defined.

        Definition exec_contract_evarenv_path {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) : SPath wnil :=
          demonic_close (exec_contract_evarenv c s (fun w1 ω01 _ δ1 h1 => SPath.block) (sep_contract_localstore c) nil).

        Definition ValidContractEvarEnvWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
          VerificationCondition (prune (prune (exec_contract_evarenv_path c body))).

      End WithConfig.

      Definition ValidContractEvarEnv {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        ValidContractEvarEnvWithConfig default_config c body.

      Definition ValidContractEvarEnvReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        is_true (ok (prune (exec_contract_evarenv_path default_config c body))).

      (* Print Assumptions ValidContractEvarEnv. *)
      (* Print Assumptions ValidContractEvarEnvReflect. *)

      Lemma validcontract_evarenv_reflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
        ValidContractEvarEnvReflect c body ->
        ValidContractEvarEnv c body.
      Proof.
        (* intros H. *)
        (* apply (outcome_ok_spec _ (fun _ => True)) in H. *)
        (* now rewrite outcome_satisfy_bind in H. *)
      Admitted.

    End EvarEnv.

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
         See [smut_consume_formula_evar] and [smut_consume_chunk_evar] for
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

  End SMut.

End Mutators.
