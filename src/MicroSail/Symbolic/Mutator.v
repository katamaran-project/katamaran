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

  Definition TYPE : Type := LCtx -> Type.
  Bind Scope modal with TYPE.
  Definition Valid (A : TYPE) : Type :=
    forall Σ, A Σ.
  Definition Impl (A B : TYPE) : TYPE :=
    fun Σ => A Σ -> B Σ.
  Definition Box (A : TYPE) : TYPE :=
    fun Σ0 => forall Σ1 (ζ01 : Sub Σ0 Σ1), A Σ1.
  Definition Snoc (A : TYPE) (b : 𝑺 * Ty) : TYPE :=
    fun Σ => A (Σ ▻ b).
  Definition Const (A : Type) : TYPE :=
    fun _ => A.
  Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
    fun Σ => forall i : I, A i Σ.
  Definition Cat (A : TYPE) (Δ : LCtx) : TYPE :=
    fun Σ => A (Σ ▻▻ Δ).

  Module ModalNotations.

    Notation "⊢ A" := (Valid A%modal) (at level 100).
    Notation "A -> B" := (Impl A%modal B%modal) : modal.
    Notation "□ A" := (Box A%modal) (at level 85, format "□ A", right associativity) : modal.
    Notation "⌜ A ⌝" := (Const A%type) : modal.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%modal)) ..))
        (at level 99, x binder, y binder, right associativity)
      : modal.

  End ModalNotations.
  Import ModalNotations.
  Open Scope modal.

  Definition K {A B} :
    ⊢ □(A -> B) -> (□A -> □B) :=
    fun Σ0 f a Σ1 ζ01 => f Σ1 ζ01 (a Σ1 ζ01).
  Definition T {A} :
    ⊢ □A -> A :=
    fun Σ0 a => a Σ0 (sub_id Σ0).
  Definition four {A} :
    ⊢ □A -> □□A :=
    fun Σ0 a Σ1 ζ01 Σ2 ζ12 => a Σ2 (sub_comp ζ01 ζ12).
  Global Arguments four : simpl never.

  Definition valid_box {A} :
    (⊢ A) -> (⊢ □A) :=
    fun a Σ0 Σ1 ζ01 => a Σ1.

  Definition persistent (A : TYPE) : Type :=
    ⊢ A -> □A.

  Definition PROP : TYPE :=
    fun _ => Prop.

  Section LogicalRelation.

    Class LR (T : TYPE) : Type :=
      lr : forall Σ0 Σ1, Sub Σ0 Σ1 -> T Σ0 -> T Σ1 -> Prop.

    Global Instance LRPROP : LR PROP :=
      fun Σ0 Σ1 ζ01 P Q => (P -> Q)%type.

    Global Instance LRFormula : LR Formula :=
      fun Σ0 Σ1 ζ01 f0 f1 =>
        forall ι1 : SymInstance Σ1,
          inst_formula (inst ι1 ζ01) f0 <-> inst_formula ι1 f1.

    Global Instance LRImpl {A B} `{LR A, LR B} : LR (A -> B) :=
      fun Σ0 Σ1 ζ01 f0 f1 =>
        forall a0 a1,
          lr ζ01 a0 a1 -> lr (T := B) ζ01 (f0 a0) (f1 a1).

    (* Instance LRPair {A B} `{LR A, LR B} : LR (Pair A B) := *)
    (*   fun Σ0 ab1 ab2 => *)
    (*     let (a1, b1) := ab1 in *)
    (*     let (a2, b2) := ab2 in *)
    (*     rel Σ0 a1 a2 /\ rel Σ0 b1 b2. *)

    Global Instance LRBox {A} `{LR A} : LR (□ A) :=
      fun Σ0 Σ1 ζ01 b1 b2 =>
        forall Σ2 (ζ02 : Sub Σ0 Σ2) (ζ12 : Sub Σ1 Σ2),
          (* lr ζ12 ζ01 ζ02 -> *)
          lr ζ12 (b1 _ ζ01) (b2 _ ζ12).

  End LogicalRelation.

  Section Obligations.

    Inductive Obligation {Σ} (ι : SymInstance Σ) (msg : Message Σ) (fml : Formula Σ) : Prop :=
    | obligation (p : inst ι fml : Prop).

  End Obligations.

  Section SymbolicPaths.

    Inductive SPath (A : LCtx -> Type) (Σ : LCtx) : Type :=
    | spath_pure (a: A Σ)
    | spath_angelic_binary (o1 o2 : SPath A Σ)
    | spath_demonic_binary (o1 o2 : SPath A Σ)
    | spath_fail (msg : Message Σ)
    | spath_block
    | spath_assertk (P : Formula Σ) (msg : Message Σ) (k : SPath A Σ)
    | spath_assumek (P : Formula Σ) (k : SPath A Σ)
    | spath_angelicv b (k : SPath A (Σ ▻ b))
    | spath_demonicv b (k : SPath A (Σ ▻ b))
    | spath_assert_vareq x σ (xIn : (x,σ) ∈ Σ) (t : Term (Σ - (x,σ)) σ) (msg : Message (Σ - (x,σ))) (k : SPath A (Σ - (x,σ)))
    | spath_assume_vareq x σ (xIn : (x,σ) ∈ Σ) (t : Term (Σ - (x,σ)) σ) (k : SPath A (Σ - (x,σ)))
    | spath_debug {BT B} {subB : Subst BT} {instB : Inst BT B} {occB: OccursCheck BT}
       (b : BT Σ) (k : SPath A Σ).

    Global Arguments spath_pure {_ _} _.
    Global Arguments spath_fail {_ _} _.
    Global Arguments spath_block {_ _}.
    Global Arguments spath_angelicv {_ _} _ _.
    Global Arguments spath_demonicv {_ _} _ _.
    Global Arguments spath_assert_vareq {_ _} x {_ _} t msg k.
    Global Arguments spath_assume_vareq {_ _} x {_ _} t k.

    Fixpoint spath_angelicvs {A Σ} Δ : SPath A (Σ ▻▻ Δ) -> SPath A Σ :=
      match Δ with
      | ε     => fun k => k
      | Δ ▻ b => fun k => spath_angelicvs Δ (spath_angelicv b k)
      end.

    Fixpoint spath_demonic_close {A} Σ : SPath A Σ -> SPath A ε :=
      match Σ with
      | ctx_nil      => fun k => k
      | ctx_snoc Σ b => fun k => spath_demonic_close (spath_demonicv b k)
      end.

    Fixpoint spath_assume_multisub {AT Σ1 Σ2} (ζ : MultiSub Σ1 Σ2) : SPath AT Σ2 -> SPath AT Σ1 :=
      match ζ with
      | multisub_id         =>
        fun p => p
      | multisub_cons x t ζ =>
        fun p => spath_assume_vareq x t (spath_assume_multisub ζ p)
      end.

    Fixpoint spath_assert_multisub {AT Σ1 Σ2} (msg : Message Σ1) (ζ : MultiSub Σ1 Σ2) : (Message Σ2 -> SPath AT Σ2) -> SPath AT Σ1 :=
      match ζ with
      | multisub_id         =>
        fun p => p msg
      | multisub_cons x t ζ =>
        let msg' := subst (sub_single _ t) msg in
        fun p => spath_assert_vareq x t msg' (spath_assert_multisub msg' ζ p)
      end.

    Fixpoint subst_spath {A} `{Subst A} {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (o : SPath A Σ1) : SPath A Σ2 :=
      match o with
      | spath_pure a => spath_pure (subst ζ a)
      | spath_angelic_binary o1 o2 => spath_angelic_binary (subst_spath ζ o1) (subst_spath ζ o2)
      | spath_demonic_binary o1 o2 => spath_demonic_binary (subst_spath ζ o1) (subst_spath ζ o2)
      | spath_fail msg => spath_fail (subst ζ msg)
      | spath_block => spath_block
      | spath_assertk P msg o => spath_assertk (subst ζ P) (subst ζ msg) (subst_spath ζ o)
      | spath_assumek P o => spath_assumek (subst ζ P) (subst_spath ζ o)
      | spath_angelicv b k => spath_angelicv b (subst_spath (sub_up1 ζ) k)
      | spath_demonicv b k => spath_demonicv b (subst_spath (sub_up1 ζ) k)
      | @spath_assert_vareq _ _ x σ xIn t msg k =>
        let ζ' := sub_comp (sub_shift _) ζ in
        spath_assertk
          (formula_eq (env_lookup ζ xIn) (subst (T := fun Σ => Term Σ _) ζ' t))
          (subst (T:=Message) ζ' msg)
          (subst_spath ζ' k)
      | @spath_assume_vareq _ _ x σ xIn t k =>
        let ζ' := sub_comp (sub_shift _) ζ in
        spath_assumek
          (formula_eq (env_lookup ζ xIn) (subst (T := fun Σ => Term Σ _) ζ' t))
          (subst_spath ζ' k)
      | spath_debug d k => spath_debug (subst ζ d) (subst_spath ζ k)
      end.

    Instance SubstSPath {E A} `{Subst E, Subst A} : Subst (SPath A) :=
      fun Σ1 Σ2 ζ o => subst_spath ζ o.

    Fixpoint occurs_check_spath {A} `{OccursCheck A} {Σ x} (xIn : x ∈ Σ) (o : SPath A Σ) :
      option (SPath A (Σ - x)) :=
      match o with
      | spath_pure a => option_map spath_pure (occurs_check xIn a)
      | spath_angelic_binary o1 o2 =>
        option_ap (option_map (spath_angelic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2)
      | spath_demonic_binary o1 o2 =>
        option_ap (option_map (spath_demonic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2)
      | spath_fail msg => option_map spath_fail (occurs_check xIn msg)
      | spath_block => Some spath_block
      | spath_assertk P msg o =>
        option_ap (option_ap (option_map (spath_assertk (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check xIn msg)) (occurs_check_spath xIn o)
      | spath_assumek P o => option_ap (option_map (spath_assumek (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check_spath xIn o)
      | spath_angelicv b o => option_map (spath_angelicv b) (occurs_check_spath (inctx_succ xIn) o)
      | spath_demonicv b o => option_map (spath_demonicv b) (occurs_check_spath (inctx_succ xIn) o)
      | @spath_assert_vareq _ _ y σ yIn t msg o =>
        match occurs_check_view yIn xIn with
        | Same _ => None
        | @Diff _ _ _ _ x xIn =>
          option_ap
            (option_ap
               (option_map
                  (fun (t' : Term (Σ - (y :: σ) - x) σ) (msg' : Message (Σ - (y :: σ) - x)) (o' : SPath A (Σ - (y :: σ) - x)) =>
                     let e := swap_remove yIn xIn in
                     spath_assert_vareq
                       y
                       (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e)
                       (eq_rect (Σ - (y :: σ) - x) Message msg' (Σ - x - (y :: σ)) e)
                       (eq_rect (Σ - (y :: σ) - x) (SPath A) o' (Σ - x - (y :: σ)) e))
                  (occurs_check xIn t))
               (occurs_check xIn msg))
            (occurs_check_spath xIn o)
        end
      | @spath_assume_vareq _ _ y σ yIn t o =>
        match occurs_check_view yIn xIn with
        | Same _ => Some o
        | @Diff _ _ _ _ x xIn =>
          option_ap
            (option_map
               (fun (t' : Term (Σ - (y :: σ) - x) σ) (o' : SPath A (Σ - (y :: σ) - x)) =>
                  let e := swap_remove yIn xIn in
                  spath_assume_vareq
                    y
                    (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e)
                    (eq_rect (Σ - (y :: σ) - x) (SPath A) o' (Σ - x - (y :: σ)) e))
               (occurs_check xIn t))
            (occurs_check_spath xIn o)
        end
      | spath_debug b o => option_ap (option_map (spath_debug (Σ := Σ - x)) (occurs_check xIn b)) (occurs_check_spath xIn o)
      end.

    Fixpoint inst_spath {AT A} `{Inst AT A} {Σ} (ι : SymInstance Σ) (o : SPath AT Σ) : Outcome A :=
      match o with
      | spath_pure a                   => outcome_pure (inst ι a)
      | spath_angelic_binary o1 o2     => outcome_angelic_binary (inst_spath ι o1) (inst_spath ι o2)
      | spath_demonic_binary o1 o2     => outcome_demonic_binary (inst_spath ι o1) (inst_spath ι o2)
      | spath_fail msg                 => outcome_fail msg
      | spath_block                    => outcome_block
      | spath_assertk fml msg o        => outcome_assertk
                                           (Obligation ι msg fml)
                                           (inst_spath ι o)
      | spath_assumek fml o            => outcome_assumek (inst ι fml) (inst_spath ι o)
      | spath_angelicv b k             => outcome_angelic (fun v : Lit (snd b) => inst_spath (env_snoc ι b v) k)
      | spath_demonicv b k             => outcome_demonic (fun v : Lit (snd b) => inst_spath (env_snoc ι b v) k)
      | @spath_assert_vareq _ _ x σ xIn t msg k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assertk
          (env_lookup ι xIn = inst ι' t)
          (inst_spath ι' k)
      | @spath_assume_vareq _ _ x σ xIn t k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assumek
          (env_lookup ι xIn = inst ι' t)
          (inst_spath ι' k)
      | spath_debug d k                => outcome_debug (inst ι d) (inst_spath ι k)
      end.

    Definition spath_mapping AT BT Σ : Type :=
      forall Σ', Sub Σ Σ' -> (* PathCondition Σ' -> *) AT Σ' -> BT Σ'.
    Definition spath_arrow AT BT Σ : Type :=
      forall Σ', Sub Σ Σ' -> PathCondition Σ' -> AT Σ' -> SPath BT Σ'.

    (* Definition spath_arrow_dcl {ET E AT A BT B} `{Subst ET, Subst BT, Inst ET E, Inst AT A, Inst BT B} {Σ} (f : spath_arrow ET AT BT Σ) : Prop := *)
    (*   forall Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2, *)
    (*     (forall ι1 ι2, ι1 = inst ι2 ζ12 -> inst ι1 a1 = inst ι2 a2) -> *)
    (*     spath_geq (subst ζ12 (f Σ1 ζ1 a1)) (f Σ2 ζ2 a2). *)

    Definition spath_angelic {AT Σ0} (x : option 𝑺) σ
      (k : forall Σ1, Sub Σ0 Σ1 -> PathCondition Σ1 -> Term Σ1 σ -> SPath AT Σ1)
      (pc0 : PathCondition Σ0) : SPath AT Σ0 :=
      let y := fresh Σ0 x in
      spath_angelicv
        (y :: σ) (k (Σ0 ▻ (y :: σ)) sub_wk1 (subst sub_wk1 pc0) (@term_var _ y σ inctx_zero)).
    Global Arguments spath_angelic {_ _} x σ k.

    Fixpoint spath_map {A B Σ} (f : spath_mapping A B Σ) (ma : SPath A Σ) : SPath B Σ :=
      match ma with
      | spath_pure a                   => spath_pure (f Σ (sub_id Σ) a)
      | spath_angelic_binary o1 o2     => spath_angelic_binary (spath_map f o1) (spath_map f o2)
      | spath_demonic_binary o1 o2     => spath_demonic_binary (spath_map f o1) (spath_map f o2)
      | spath_fail msg                 => spath_fail msg
      | spath_block                    => spath_block
      | spath_assertk fml msg k        => spath_assertk fml msg (spath_map f k)
      | spath_assumek fml k            => spath_assumek fml (spath_map f k)
      | spath_angelicv b k             => spath_angelicv b (spath_map (fun Σ' ζ a => f Σ' (env_tail ζ) a) k)
      | spath_demonicv b k             => spath_demonicv b (spath_map (fun Σ' ζ a => f Σ' (env_tail ζ) a) k)
      | @spath_assert_vareq _ _ x σ xIn t msg k =>
        let ζ' := sub_single xIn t in
        spath_assert_vareq x t msg (spath_map (fun Σ' ζ => f Σ' (sub_comp ζ' ζ)) k)
      | @spath_assume_vareq _ _ x σ xIn t k =>
        let ζ' := sub_single xIn t in
        spath_assume_vareq x t (spath_map (fun Σ' ζ => f Σ' (sub_comp ζ' ζ)) k)
      | spath_debug d k                => spath_debug d (spath_map f k)
      end.

    Fixpoint spath_bind {A B Σ} (pc : PathCondition Σ) (ma : SPath A Σ) (f : forall Σ', Sub Σ Σ' -> PathCondition Σ' -> A Σ' -> SPath B Σ') {struct ma} : SPath B Σ :=
      match ma with
      | spath_pure a                   => f Σ (sub_id Σ) pc a
      | spath_angelic_binary o1 o2     => spath_angelic_binary (spath_bind pc o1 f) (spath_bind pc o2 f)
      | spath_demonic_binary o1 o2     => spath_demonic_binary (spath_bind pc o1 f) (spath_bind pc o2 f)
      | spath_fail msg                 => spath_fail msg
      | spath_block                    => spath_block
      | spath_assertk fml msg k        => spath_assertk fml msg (spath_bind (cons fml pc) k f)
      | spath_assumek fml k            => spath_assumek fml (spath_bind (cons fml pc) k f)
      | spath_angelicv b k             => spath_angelicv b (spath_bind (subst sub_wk1 pc) k (fun Σ' ζ a => f Σ' (env_tail ζ) a))
      | spath_demonicv b k             => spath_demonicv b (spath_bind (subst sub_wk1 pc) k (fun Σ' ζ a => f Σ' (env_tail ζ) a))
      | @spath_assert_vareq _ _ x σ xIn t msg k =>
        let ζ' := sub_single xIn t in
        spath_assert_vareq x t msg (spath_bind (subst ζ' pc) k (fun Σ' ζ => f Σ' (sub_comp ζ' ζ)))
      | @spath_assume_vareq _ _ x σ xIn t k =>
        let ζ' := sub_single xIn t in
        spath_assume_vareq x t (spath_bind (subst ζ' pc) k (fun Σ' ζ => f Σ' (sub_comp ζ' ζ)))
      | spath_debug d k                => spath_debug d (spath_bind pc k f)
      end.

    Fixpoint spath_assume_formulas_without_solver {A Σ}
      (fmls : List Formula Σ) (k : SPath A Σ) {struct fmls} : SPath A Σ :=
      match fmls with
      | nil           => k
      | cons fml fmls =>
        spath_assumek
          fml
          (spath_assume_formulas_without_solver fmls k)
      end.

    Fixpoint spath_assert_formulas_without_solver {A Σ}
      (msg : Message Σ) (fmls : List Formula Σ) (k : SPath A Σ) {struct fmls} : SPath A Σ :=
      match fmls with
      | nil           => k
      | cons fml fmls =>
        spath_assertk
          fml
          msg
          (spath_assert_formulas_without_solver msg fmls k)
      end.

    Definition spath_assume_formula {Σ} (fml : Formula Σ) (pc : PathCondition Σ) :
      SPath Unit Σ :=
      match solver pc fml with
      | Some (existT Σ1 (ζ , fmls)) =>
        (* Assume variable equalities and the residual constraints *)
        spath_assume_multisub ζ
          (spath_assume_formulas_without_solver fmls (spath_pure tt))
      | None =>
        (* The formula is inconsistent with the path constraints. *)
        spath_block
      end.

    Fixpoint spath_assume_formulas {Σ} (fmls : List Formula Σ) (pc : PathCondition Σ) {struct fmls} :
      SPath Unit Σ :=
      match fmls with
      | nil => spath_pure tt
      | cons fml fmls =>
        spath_bind
          pc
          (spath_assume_formulas fmls pc)
          (fun Σ1 ζ01 pc1 _ => spath_assume_formula (subst ζ01 fml) pc1)
      end.

    Definition spath_assert_formula {Σ} (msg : Message Σ) (pc : PathCondition Σ) (fml : Formula Σ) :
      SPath Unit Σ :=
      match solver pc fml with
      | Some (existT Σ1 (ζ , fmls)) =>
        (* Assert variable equalities and the residual constraints *)
        spath_assert_multisub msg ζ
          (fun msg' => spath_assert_formulas_without_solver msg' fmls (spath_pure tt))
      | None =>
        (* The formula is inconsistent with the path constraints. *)
        spath_fail msg
      end.

    Fixpoint spath_wp {AT A Σ} `{Inst AT A} (o : SPath AT Σ) (ι : SymInstance Σ) (POST : A -> Prop) : Prop :=
      match o with
      | spath_pure a                               => POST (inst ι a)
      | spath_angelic_binary o1 o2                 => (spath_wp o1 ι POST) \/ (spath_wp o2 ι POST)
      | spath_demonic_binary o1 o2                 => (spath_wp o1 ι POST) /\ (spath_wp o2 ι POST)
      | spath_fail msg                             => Error msg
      | spath_block                                => True
      | spath_assertk fml msg o                    => inst ι fml /\ spath_wp o ι POST
      | spath_assumek fml o                        => (inst ι fml : Prop) -> spath_wp o ι POST
      | spath_angelicv b k                         => exists (v : Lit (snd b)), spath_wp k (env_snoc ι b v) POST
      | spath_demonicv b k                         => forall (v : Lit (snd b)), spath_wp k (env_snoc ι b v) POST
      | @spath_assert_vareq _ _ x σ xIn t msg k    =>
        let ι' := env_remove' _ ι xIn in
        env_lookup ι xIn = inst ι' t /\ spath_wp k ι' POST
      | @spath_assume_vareq _ _ x σ xIn t k        =>
        let ι' := env_remove' _ ι xIn in
        env_lookup ι xIn = inst ι' t -> spath_wp k ι' POST
      | spath_debug d k                            => Debug (inst ι d) (spath_wp k ι POST)
      end.

    Definition spath_wp' {AT A Σ} `{Inst AT A} (o : SPath AT Σ) (ι : SymInstance Σ) (POST : A -> Prop) : Prop :=
      outcome_satisfy (inst_spath ι o) POST.

    Lemma spath_wp_wp' {AT A Σ} `{Inst AT A} (o : SPath AT Σ) (ι : SymInstance Σ) (POST : A -> Prop) :
      spath_wp o ι POST <-> spath_wp' o ι POST.
    Proof.
      unfold spath_wp'.
      induction o; cbn; auto.
      - specialize (IHo1 ι). specialize (IHo2 ι). intuition.
      - specialize (IHo1 ι). specialize (IHo2 ι). intuition.
      - split; intros [].
      - specialize (IHo ι). intuition.
        constructor; auto.
      - specialize (IHo ι). intuition.
      - split; intros [v HYP]; exists v; specialize (IHo (env_snoc ι b v)); intuition.
      - split; intros HYP v; specialize (HYP v); specialize (IHo (env_snoc ι b v)); intuition.
      - specialize (IHo (env_remove' (x :: σ) ι xIn)). intuition.
      - specialize (IHo (env_remove' (x :: σ) ι xIn)). intuition.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Lemma spath_wp_monotonic {AT A} `{Inst AT A} {Σ}
      (o : SPath AT Σ) (ι : SymInstance Σ)
      (P Q : A -> Prop) (PQ : forall a, P a -> Q a) :
      spath_wp o ι P ->
      spath_wp o ι Q.
    Proof. rewrite ?spath_wp_wp'. now apply outcome_satisfy_monotonic. Qed.

    Global Instance proper_spath_wp {AT A} `{Inst AT A} {Σ} (o : SPath AT Σ) (ι : SymInstance Σ) :
      Proper
        (pointwise_relation A iff ==> iff)
        (spath_wp o ι).
    Proof.
      unfold Proper, respectful, pointwise_relation, Basics.impl.
      intros P Q PQ; split; apply spath_wp_monotonic; intuition.
    Qed.

    Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

    Global Instance LRSPath {AT A} `{LR AT, Inst AT A} : LR (SPath AT) :=
      fun Σ0 Σ1 ζ01 o0 o1 =>
        forall (ι1 : SymInstance Σ1) (POST : A -> Prop),
          spath_wp o0 (inst ι1 ζ01) POST <-> spath_wp o1 ι1 POST.

    Definition new_spath_mapping_dcl {AT BT} `{LR AT, LR BT} {Σ0} (f : (□ (AT -> BT)) Σ0) : Prop :=
      forall Σ1 (ζ01 : Sub Σ0 Σ1), lr ζ01 f (four f ζ01).

    Lemma new_spath_wp_map' {AT A BT B} `{LR AT, LR BT, InstLaws AT A, Inst BT B} {Σ} (ma : SPath AT Σ)
      (f : (□ (AT -> BT)) Σ) (f_dcl : new_spath_mapping_dcl f) :
      forall (ι : SymInstance Σ) POST,
        spath_wp (spath_map f ma) ι POST <->
        spath_wp ma ι (fun a => POST (inst ι (f Σ (sub_id Σ) (lift a)))).
    Proof.
    intros ι. induction ma; cbn; intros POST; auto.
    - assert (inst ι (f Σ (sub_id Σ) a) =
              inst ι (f Σ (sub_id Σ) (lift (inst ι a)))) as ->; auto.
      cbv [new_spath_mapping_dcl lr LRBox LRImpl] in f_dcl.
      admit.
    - rewrite IHma1, IHma2; eauto.
    - rewrite IHma1, IHma2; eauto.
    - rewrite IHma; auto.
    - rewrite IHma; auto.
    - admit.
    - destruct b as [x σ]; cbn. setoid_rewrite IHma.
      split; (intros Hwp v; specialize (Hwp v); revert Hwp; apply spath_wp_monotonic; intros a;
              match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
    Admitted.

    Definition spath_mapping_dcl {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} (f : spath_mapping AT BT Σ0) : Prop :=
      forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) (ζ02 : Sub Σ0 Σ2) (a1 : AT Σ1) (a2 : AT Σ2) (ζ12 : Sub Σ1 Σ2),
      forall ι1 ι2,
        ι1 = inst ι2 ζ12 ->
        inst ι1 ζ01 = inst ι2 ζ02 ->
        inst ι1 a1 = inst ι2 a2 ->
        inst ι1 (f Σ1 ζ01 a1) = inst ι2 (f Σ2 ζ02 a2).

    Definition spath_arrow_dcl {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Σ} (f : spath_arrow AT BT Σ) : Prop :=
      forall Σ1 Σ2 ζ1 ζ2 pc1 pc2 ζ12 a1 a2 (P Q : B -> Prop) (PQ : forall b, P b -> Q b),
       forall (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2),
         ι1 = inst ι2 ζ12 ->
         instpc ι1 pc1 ->
         instpc ι2 pc2 ->
         inst ι1 ζ1 = inst ι2 ζ2 ->
         inst ι1 a1 = inst ι2 a2 ->
         spath_wp (f Σ1 ζ1 pc1 a1) ι1 P ->
         spath_wp (f Σ2 ζ2 pc2 a2) ι2 Q.

    (* Lemma spath_arrow_dcl_dcl' {ET E AT A BT B} `{InstLaws ET E, Inst AT A, InstLaws BT B} {Σ} (f : spath_arrow ET AT BT Σ) : *)
    (*   spath_arrow_dcl f <-> spath_arrow_dcl' f. *)
    (* Proof. *)
    (*   unfold spath_arrow_dcl, spath_arrow_dcl', spath_geq. *)
    (*   setoid_rewrite spath_wp_subst. *)
    (*   split; intros HYP Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2; *)
    (*     specialize (HYP Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2). *)
    (*   - intros F P Q PQ ι1 ι2 -> Hζ Ha. apply HYP; auto. *)
    (*     intros ι1' ι2'.  *)
    (* Qed. *)

    Lemma spath_wp_subst {AT A} `{InstLaws AT A} {Σ1 Σ2} (ζ12 : Sub Σ1 Σ2)
      (o : SPath AT Σ1) (ι : SymInstance Σ2) (POST : A -> Prop) :
      spath_wp (subst ζ12 o) ι POST <-> spath_wp o (inst ι ζ12) POST.
    Proof.
      cbv [subst SubstSPath]. revert Σ2 ι ζ12.
      induction o; cbn; intros.
      - now rewrite inst_subst.
      - now rewrite IHo1, IHo2.
      - now rewrite IHo1, IHo2.
      - split; intros [].
      - reflexivity.
      - now rewrite IHo, inst_subst.
      - now rewrite IHo, inst_subst.
      - destruct b as [x τ].
        split; intros [v HYP]; exists v; revert HYP;
          rewrite (IHo _ (env_snoc ι (x :: τ) v) (sub_up1 ζ12));
          unfold sub_up1, sub_comp;
          now rewrite inst_sub_snoc, inst_subst, inst_sub_wk1.
      - destruct b as [x τ].
        split; intros HYP v; specialize (HYP v); revert HYP;
          rewrite (IHo _ (env_snoc ι (x :: τ) v) (sub_up1 ζ12));
          unfold sub_up1, sub_comp;
          now rewrite inst_sub_snoc, inst_subst, inst_sub_wk1.
      - rewrite IHo. unfold sub_comp.
        now rewrite ?inst_subst, inst_sub_shift, <- inst_lookup.
      - rewrite IHo. unfold sub_comp.
        now rewrite ?inst_subst, inst_sub_shift, <- inst_lookup.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Definition spath_geq {AT A} `{Inst AT A} {Σ} (o1 o2 : SPath AT Σ) : Prop :=
      forall (P Q : A -> Prop) (PQ : forall a, P a -> Q a) ι,
        spath_wp o1 ι P ->
        spath_wp o2 ι Q.

    Global Instance preorder_spath_geq {AT A} `{Inst AT A} {Σ} : PreOrder (spath_geq (Σ := Σ)).
    Proof.
      constructor.
      - unfold spath_geq; intros o * PQ *.
        now apply spath_wp_monotonic.
      - intros x y z. unfold spath_geq.
        intros Rxy Ryz P Q PQ ι.
        specialize (Rxy P Q PQ ι).
        specialize (Ryz Q Q (fun _ p => p) ι).
        auto.
    Qed.

    Fixpoint spath_safe {AT Σ} (ι : SymInstance Σ) (o : SPath AT Σ) {struct o} : Prop :=
      match o with
      | spath_pure a => True
      | spath_angelic_binary o1 o2 => spath_safe ι o1 \/ spath_safe ι o2
      | spath_demonic_binary o1 o2 => spath_safe ι o1 /\ spath_safe ι o2
      | spath_fail msg => False
      | spath_block => True
      | spath_assertk fml msg o =>
        Obligation ι msg fml /\ spath_safe ι o
      | spath_assumek fml o => (inst ι fml : Prop) -> spath_safe ι o
      | spath_angelicv b k => exists v, spath_safe (env_snoc ι b v) k
      | spath_demonicv b k => forall v, spath_safe (env_snoc ι b v) k
      | @spath_assert_vareq _ _ x σ xIn t msg k =>
        (let ζ := sub_shift xIn in
        Obligation ι (subst (T:=Message) ζ msg) (formula_eq (term_var x) (subst (T:=fun Σ => Term Σ σ) ζ t))) /\
        (let ι' := env_remove (x,σ) ι xIn in
        spath_safe ι' k)
      | @spath_assume_vareq _ _ x σ xIn t k =>
        let ι' := env_remove (x,σ) ι xIn in
        env_lookup ι xIn = inst ι' t ->
        spath_safe ι' k
      | spath_debug d k => Debug (inst ι d) (spath_safe ι k)
      end.
    Global Arguments spath_safe {_} Σ ι o.

    Lemma spath_wp_angelicvs {AT A} `{Inst AT A} Σ Δ (ma : SPath AT (Σ ▻▻ Δ)) :
      forall (ι : SymInstance Σ) POST,
        spath_wp (spath_angelicvs Δ ma) ι POST <->
        exists ιΔ : SymInstance Δ, spath_wp ma (env_cat ι ιΔ) POST.
    Proof.
      intros ι POST.
      induction Δ; cbn.
      - split.
        + intros Hwp. exists env_nil. apply Hwp.
        + intros [ιΔ Hwp]. destruct (nilView ιΔ). apply Hwp.
      - rewrite IHΔ. cbn.
        split; intros [ιΔ Hwp].
        + destruct Hwp as [v Hwp].
          exists (env_snoc ιΔ _ v).
          apply Hwp.
        + destruct (snocView ιΔ) as [ιΔ v].
          exists ιΔ, v. apply Hwp.
    Qed.

    Lemma spath_wp_angelic {AT A} `{InstLaws AT A} {Σ0} {x : option 𝑺} {σ : Ty}
          (k : forall Σ1 : LCtx, Sub Σ0 Σ1 -> PathCondition Σ1 -> Term Σ1 σ -> SPath AT Σ1) (k_dcl : spath_arrow_dcl k)
          (pc0 : PathCondition Σ0)
          (ι0 : SymInstance Σ0) (POST : A -> Prop) :
      instpc ι0 pc0 ->
      spath_wp (spath_angelic x σ k pc0) ι0 POST <->
      exists v : Lit σ, spath_wp (k _ (sub_id _) pc0 (lift v)) ι0 POST.
    Proof.
      cbn. split; intros [v Hwp]; exists v; revert Hwp.
      - apply (k_dcl _ _ sub_wk1 (sub_id Σ0) _ _ (sub_snoc (sub_id Σ0) (fresh Σ0 x :: σ) (term_lit σ v)));
          repeat rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc; auto.
      - apply (k_dcl _ _ (sub_id Σ0) sub_wk1 _ _ sub_wk1);
          repeat rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc; auto.
    Qed.

    Lemma spath_wp_map {AT A BT B} `{InstLaws AT A, Inst BT B} {Σ} (ma : SPath AT Σ)
      (f : spath_mapping AT BT Σ) (f_dcl : spath_mapping_dcl f) :
      forall (ι : SymInstance Σ) POST,
        spath_wp (spath_map f ma) ι POST <->
        spath_wp ma ι (fun a => POST (inst ι (f Σ (sub_id Σ) (lift a)))).
    Proof.
      intros ι. induction ma; cbn; intros POST; auto.
      - assert (inst ι (f Σ (sub_id Σ) a) =
                inst ι (f Σ (sub_id Σ) (lift (inst ι a)))) as ->; auto.
        eapply f_dcl; eauto; now rewrite ?inst_sub_id, ?inst_lift.
      - rewrite IHma1, IHma2; eauto.
      - rewrite IHma1, IHma2; eauto.
      - rewrite IHma; auto.
      - rewrite IHma; auto.
      - destruct b as [x σ]; cbn. setoid_rewrite IHma.
        split; (intros [v Hwp]; exists v; revert Hwp; apply spath_wp_monotonic; intros a;
                match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
        + eapply (f_dcl _ _ _ _ _ _ (sub_snoc (sub_id _) (x :: σ) (term_lit σ v)));
            rewrite ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
          rewrite <- sub_comp_wk1_tail; unfold sub_comp.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
        + eapply (f_dcl _ _ _ _ _ _ sub_wk1);
            rewrite ?inst_sub_wk1, ?inst_lift; auto.
          rewrite <- sub_comp_wk1_tail; unfold sub_comp.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
        + unfold spath_mapping_dcl. intros. eapply f_dcl; eauto.
          rewrite <- ?sub_comp_wk1_tail; unfold sub_comp.
          rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
          intuition.
      - destruct b as [x σ]; cbn. setoid_rewrite IHma.
        split; (intros Hwp v; specialize (Hwp v); revert Hwp; apply spath_wp_monotonic; intros a;
                match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
        + eapply (f_dcl _ _ _ _ _ _ (sub_snoc (sub_id _) (x :: σ) (term_lit σ v)));
            rewrite ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto.
          rewrite <- sub_comp_wk1_tail; unfold sub_comp.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
        + eapply (f_dcl _ _ _ _ _ _ sub_wk1);
            rewrite ?inst_sub_wk1, ?inst_lift; auto.
          rewrite <- sub_comp_wk1_tail; unfold sub_comp.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
        + unfold spath_mapping_dcl. intros. eapply f_dcl; eauto.
          rewrite <- ?sub_comp_wk1_tail; unfold sub_comp.
          rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_wk1.
          intuition.
      - rewrite IHma.
        split; (intros [Heq Hwp]; split; auto; revert Hwp; apply spath_wp_monotonic; intros a;
                match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
        + apply (f_dcl _ _ _ _ _ _ (sub_shift xIn)); unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_shift; auto.
          now rewrite inst_sub_single.
        + apply (f_dcl _ _ _ _ _ _ (sub_single xIn t)); unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_single; auto.
        + unfold spath_mapping_dcl. intros.
          eapply f_dcl; unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_shift; auto.
          intuition.
      - rewrite IHma.
        split; (intros Hwp Heq; specialize (Hwp Heq); revert Hwp; apply spath_wp_monotonic; intros a;
                match goal with | |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto end).
        + apply (f_dcl _ _ _ _ _ _ (sub_shift xIn)); unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_shift; auto.
          now rewrite inst_sub_single.
        + apply (f_dcl _ _ _ _ _ _ (sub_single xIn t)); unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_single; auto.
        + unfold spath_mapping_dcl. intros.
          eapply f_dcl; unfold sub_comp;
            rewrite ?inst_subst, ?inst_lift, ?inst_sub_id, ?inst_sub_shift; auto.
          intuition.
      - split; intros [HYP]; constructor; revert HYP; now apply IHma.
    Qed.

    Lemma spath_wp_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Σ} (pc : PathCondition Σ) (ma : SPath AT Σ)
          (f : forall Σ', Sub Σ Σ' -> PathCondition Σ' -> AT Σ' -> SPath BT Σ') (f_dcl : spath_arrow_dcl f) :
      forall (ι : SymInstance Σ) (Hpc : instpc ι pc) POST,
        spath_wp (spath_bind pc ma f) ι POST <->
        spath_wp ma ι (fun a => spath_wp (f Σ (sub_id _) pc (lift a)) ι POST).
    Proof.
      intros ι Hpc. induction ma; cbn; intros POST; auto.
      - split; eapply f_dcl with (sub_id _); eauto; rewrite ?inst_sub_id, ?inst_lift; auto.
      - now rewrite IHma1, IHma2.
      - now rewrite IHma1, IHma2.
      - split; (intros [HP Hwp]; split; [exact HP | ]; revert Hwp);
          rewrite IHma; eauto; try (rewrite inst_pathcondition_cons; intuition; fail);
            apply spath_wp_monotonic; intros a; eapply f_dcl; eauto.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
      - split; (intros Hwp HP; specialize (Hwp HP); revert Hwp);
          rewrite IHma; eauto; try (rewrite inst_pathcondition_cons; intuition; fail);
            apply spath_wp_monotonic; intros a; eapply f_dcl; eauto.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
        now rewrite inst_sub_id.
        now rewrite inst_pathcondition_cons.
      - destruct b as [x σ]; cbn.
        split; (intros [v Hwp]; exists v; revert Hwp).
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            unfold spath_arrow_dcl in f_dcl.
            eapply (f_dcl _ _ _ _ _ _ (sub_snoc (sub_id _) (x :: σ) (term_lit σ v))); eauto.
            now rewrite inst_sub_snoc, inst_sub_id.
            now rewrite inst_subst, inst_sub_wk1.
            rewrite <- sub_up1_id. unfold sub_up1.
            rewrite sub_comp_id_left. cbn [env_tail sub_snoc].
            now rewrite inst_sub_wk1, inst_sub_id.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            destruct (snocView ζ1), (snocView ζ2).
            cbn in H10. apply inversion_eq_env_snoc in H10.
            destruct H10. eapply f_dcl; eauto.
          * now rewrite inst_subst, inst_sub_wk1.
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            unfold spath_arrow_dcl in f_dcl.
            eapply (f_dcl _ _ _ _ _ _ sub_wk1); eauto.
            now rewrite inst_sub_wk1.
            now rewrite inst_subst, inst_sub_wk1.
            rewrite <- sub_up1_id. unfold sub_up1.
            rewrite sub_comp_id_left. cbn [env_tail sub_snoc].
            now rewrite inst_sub_wk1, inst_sub_id.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            destruct (snocView ζ1), (snocView ζ2).
            cbn in H10. apply inversion_eq_env_snoc in H10.
            destruct H10. eapply f_dcl; eauto.
          * now rewrite inst_subst, inst_sub_wk1.
      - destruct b as [x σ]; cbn.
        split; (intros Hwp v; specialize (Hwp v); revert Hwp).
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            unfold spath_arrow_dcl in f_dcl.
            eapply (f_dcl _ _ _ _ _ _ (sub_snoc (sub_id _) (x :: σ) (term_lit σ v))); eauto.
            now rewrite inst_sub_snoc, inst_sub_id.
            now rewrite inst_subst, inst_sub_wk1.
            rewrite <- sub_up1_id. unfold sub_up1.
            rewrite sub_comp_id_left. cbn [env_tail sub_snoc].
            now rewrite inst_sub_wk1, inst_sub_id.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            destruct (snocView ζ1), (snocView ζ2).
            cbn in H10. apply inversion_eq_env_snoc in H10.
            destruct H10. eapply f_dcl; eauto.
          * now rewrite inst_subst, inst_sub_wk1.
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            unfold spath_arrow_dcl in f_dcl.
            eapply (f_dcl _ _ _ _ _ _ sub_wk1); eauto.
            now rewrite inst_sub_wk1.
            now rewrite inst_subst, inst_sub_wk1.
            rewrite <- sub_up1_id. unfold sub_up1.
            rewrite sub_comp_id_left. cbn [env_tail sub_snoc].
            now rewrite inst_sub_wk1, inst_sub_id.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            destruct (snocView ζ1), (snocView ζ2).
            cbn in H10. apply inversion_eq_env_snoc in H10.
            destruct H10. eapply f_dcl; eauto.
          * now rewrite inst_subst, inst_sub_wk1.
      - split; (intros [Heq Hwp]; split; auto; revert Hwp).
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            apply (f_dcl _ _ _ _ _ _ (sub_shift xIn)); auto.
            now rewrite inst_sub_shift.
            now rewrite inst_subst, inst_sub_single.
            now rewrite sub_comp_id_right, inst_sub_id, inst_sub_single.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            apply (f_dcl _ _ _ _ _ _ ζ12); auto.
            unfold sub_comp. rewrite ?inst_subst.
            congruence.
          * now rewrite inst_subst, inst_sub_single.
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            apply (f_dcl _ _ _ _ _ _ (sub_single xIn t)); auto.
            now rewrite inst_sub_single.
            now rewrite inst_subst, inst_sub_single.
            now rewrite sub_comp_id_right, inst_sub_id, inst_sub_single.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            apply (f_dcl _ _ _ _ _ _ ζ12); auto.
            unfold sub_comp. rewrite ?inst_subst.
            congruence.
          * now rewrite inst_subst, inst_sub_single.
      - split; (intros Hwp Heq; specialize (Hwp Heq); revert Hwp).
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            apply (f_dcl _ _ _ _ _ _ (sub_shift xIn)); auto.
            now rewrite inst_sub_shift.
            now rewrite inst_subst, inst_sub_single.
            now rewrite sub_comp_id_right, inst_sub_id, inst_sub_single.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            apply (f_dcl _ _ _ _ _ _ ζ12); auto.
            unfold sub_comp. rewrite ?inst_subst.
            congruence.
          * now rewrite inst_subst, inst_sub_single.
        + rewrite IHma.
          * apply spath_wp_monotonic. intros a.
            apply (f_dcl _ _ _ _ _ _ (sub_single xIn t)); auto.
            now rewrite inst_sub_single.
            now rewrite inst_subst, inst_sub_single.
            now rewrite sub_comp_id_right, inst_sub_id, inst_sub_single.
            now rewrite ?inst_lift.
          * unfold spath_arrow_dcl. intros. revert H12.
            apply (f_dcl _ _ _ _ _ _ ζ12); auto.
            unfold sub_comp. rewrite ?inst_subst.
            congruence.
          * now rewrite inst_subst, inst_sub_single.
      - split; intros [HYP]; constructor; revert HYP; now apply IHma.
    Qed.

    Lemma spath_wp_assumek_subst {AT A} `{InstLaws AT A} {Σ x σ} (xIn : (x,σ) ∈ Σ) (t : Term (Σ - (x,σ)) σ)
          (k : SPath AT Σ) :
      forall ι POST,
        spath_wp (spath_assumek (formula_eq (term_var x) (subst (T := fun Σ => Term Σ _) (sub_shift xIn) t)) k) ι POST <->
        spath_wp (spath_assume_vareq x t (subst (sub_single xIn t) k)) ι POST.
    Proof.
      cbn. intros *. rewrite inst_subst. rewrite inst_sub_shift, spath_wp_subst.
      split; intros Hwp HYP; specialize (Hwp HYP); revert Hwp; now rewrite inst_sub_single.
    Qed.

    Lemma spath_wp_assume_multisub {AT A} `{InstLaws AT A} {Σ0 Σ1} (ζ : MultiSub Σ0 Σ1)
      (o : SPath AT Σ1) (ι0 : SymInstance Σ0) (P : A -> Prop) :
      spath_wp (spath_assume_multisub ζ o) ι0 P <->
      (inst_multisub ι0 ζ -> spath_wp o (inst ι0 (sub_multishift ζ)) P).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        unfold sub_comp. rewrite inst_subst.
        intuition.
    Qed.

    Lemma spath_wp_assert_multisub {AT A} `{InstLaws AT A} {Σ0 Σ1} (msg : Message _) (ζ : MultiSub Σ0 Σ1)
      (o : Message _ -> SPath AT Σ1) (ι0 : SymInstance Σ0) (P : A -> Prop) :
      spath_wp (spath_assert_multisub msg ζ o) ι0 P <->
      (inst_multisub ι0 ζ /\ spath_wp (o (subst (sub_multi ζ) msg)) (inst ι0 (sub_multishift ζ)) P).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id, subst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite subst_sub_comp.
        rewrite <- inst_sub_shift.
        unfold sub_comp. rewrite inst_subst.
        intuition.
    Qed.

    Lemma spath_wp_assume_formulas_without_solver {AT A} `{Inst AT A} {Σ0}
      (fmls : List Formula Σ0) (o : SPath AT Σ0) (ι0 : SymInstance Σ0) (POST : A -> Prop) :
      spath_wp (spath_assume_formulas_without_solver fmls o) ι0 POST <->
      (instpc ι0 fmls -> spath_wp o ι0 POST).
    Proof.
      induction fmls; cbn.
      - intuition. apply H0. constructor.
      - rewrite inst_pathcondition_cons.
        intuition.
    Qed.

    Lemma spath_wp_assert_formulas_without_solver {AT A} `{Inst AT A} {Σ0}
      (msg : Message Σ0) (fmls : List Formula Σ0) (o : SPath AT Σ0) (ι0 : SymInstance Σ0) (POST : A -> Prop) :
      spath_wp (spath_assert_formulas_without_solver msg fmls o) ι0 POST <->
      (instpc ι0 fmls /\ spath_wp o ι0 POST).
    Proof.
      induction fmls; cbn.
      - intuition. constructor.
      - rewrite inst_pathcondition_cons.
        intuition.
    Qed.

    Lemma spath_wp_assume_formula {Σ} (pc : PathCondition Σ) (fml : Formula Σ) (ι : SymInstance Σ) :
      forall (P : unit -> Prop),
        instpc ι pc ->
        spath_wp (spath_assume_formula fml pc) ι P <->
        ((inst ι fml : Prop) -> P tt).
    Proof.
      unfold spath_assume_formula. intros ? Hpc.
      destruct (solver_spec pc fml) as [[Σ1 [ζ fmls]]|].
      - specialize (H ι Hpc). destruct H as [Hζ Hfmls].
        specialize (Hfmls (inst ι (sub_multishift ζ))).
        rewrite spath_wp_assume_multisub, spath_wp_assume_formulas_without_solver.
        cbn. split.
        + intros HP ?. apply HP; auto.
          rewrite inst_multi in Hfmls; auto.
          apply Hfmls; auto.
        + intros HP ? ?. apply HP. apply Hfmls; auto.
          rewrite inst_multi; auto.
      - specialize (H _ Hpc).
        cbn; intuition.
    Qed.

    Lemma spath_wp_assert_formula {Σ} (msg : Message Σ) (pc : PathCondition Σ) (fml : Formula Σ) (ι : SymInstance Σ) :
      forall (P : unit -> Prop),
        instpc ι pc ->
        spath_wp (spath_assert_formula msg pc fml) ι P <->
        (inst ι fml /\ P tt).
    Proof.
      unfold spath_assert_formula. intros ? Hpc.
      destruct (solver_spec pc fml) as [[Σ1 [ζ fmls]]|].
      - specialize (H ι Hpc). destruct H as [Hζ Hfmls].
        specialize (Hfmls (inst ι (sub_multishift ζ))).
        rewrite spath_wp_assert_multisub, spath_wp_assert_formulas_without_solver.
        cbn. split.
        + intros [? [? HP]]. split; auto.
          apply Hfmls; auto.
          rewrite inst_multi; auto.
        + intros [? Hp]. split; auto.
          split; auto. apply Hfmls; auto.
          rewrite inst_multi; auto.
      - specialize (H _ Hpc). cbn.
        cbn; intuition.
    Qed.

    Definition spath_angelic_binary_prune {AT Σ} (o1 o2 : SPath AT Σ) : SPath AT Σ :=
      match o1 , o2 with
      | spath_block  , _           => spath_block
      | _           , spath_block  => spath_block
      | spath_fail _ , _           => o2
      | _           , spath_fail _ => o1
      | _           , _           => spath_angelic_binary o1 o2
      end.

    Definition spath_demonic_binary_prune {AT Σ} (o1 o2 : SPath AT Σ) : SPath AT Σ :=
      match o1 , o2 with
      | spath_block  , _           => o2
      | _           , spath_block  => o1
      | spath_fail s , _           => spath_fail s
      | _           , spath_fail s => spath_fail s
      | _           , _           => spath_demonic_binary o1 o2
      end.

    Definition spath_assertk_prune {AT Σ} (fml : Formula Σ) (msg : Message Σ) (o : SPath AT Σ) : SPath AT Σ :=
      match o with
      | spath_fail s => spath_fail s
      | _           => spath_assertk fml msg o
      end.

    Definition spath_assumek_prune {AT Σ} (fml : Formula Σ) (o : SPath AT Σ) : SPath AT Σ :=
      match o with
      | spath_block => spath_block
      | _          => spath_assumek fml o
      end.

    Definition spath_angelicv_prune {AT} `{OccursCheck AT} {Σ} b (o : SPath AT (Σ ▻ b)) : SPath AT Σ :=
      match o with
      (* This is not good *)
      (* | spath_fail s => spath_fail s *)
      | _           => spath_angelicv b o
      end.

    Definition spath_demonicv_prune {AT} `{OccursCheck AT} {Σ} b (o : SPath AT (Σ ▻ b)) : SPath AT Σ :=
      match @occurs_check_spath AT _ (Σ ▻ b) b inctx_zero o with
      | Some o => o
      | None   => spath_demonicv b o
      end.

    Definition spath_assert_vareq_prune {AT Σ x σ} {xIn : (x,σ) ∈ Σ} (t : Term (Σ - (x,σ)) σ) (msg : Message (Σ - (x,σ))) (k : SPath AT (Σ - (x,σ))) : SPath AT Σ :=
      match k with
      (* | spath_fail s => spath_fail s *)
      | _          => spath_assert_vareq x t msg k
      end.

    Definition spath_assume_vareq_prune {AT Σ x σ} {xIn : (x,σ) ∈ Σ} (t : Term (Σ - (x,σ)) σ) (k : SPath AT (Σ - (x,σ))) : SPath AT Σ :=
      match k with
      | spath_block => spath_block
      | _          => spath_assume_vareq x t k
      end.

    Fixpoint spath_prune {AT} `{OccursCheck AT} {Σ} (o : SPath AT Σ) : SPath AT Σ :=
      match o with
      | spath_pure a => spath_pure a
      | spath_fail msg => spath_fail msg
      | spath_block => spath_block
      | spath_angelic_binary o1 o2 =>
        spath_angelic_binary_prune (spath_prune o1) (spath_prune o2)
      | spath_demonic_binary o1 o2 =>
        spath_demonic_binary_prune (spath_prune o1) (spath_prune o2)
      | spath_assertk P msg o =>
        spath_assertk_prune P msg (spath_prune o)
      | spath_assumek P o =>
        spath_assumek_prune P (spath_prune o)
      | spath_angelicv b o =>
        spath_angelicv_prune (spath_prune o)
      | spath_demonicv b o =>
        spath_demonicv_prune (spath_prune o)
      | spath_assert_vareq x t msg k =>
        spath_assert_vareq_prune t msg (spath_prune k)
      | spath_assume_vareq x t k =>
        spath_assume_vareq_prune t (spath_prune k)
      | spath_debug d k => spath_debug d (spath_prune k)
      end.

    Definition spath_ok {AT} `{OccursCheck AT} {Σ} (o : SPath AT Σ) : bool :=
      match spath_prune o with
      | spath_block  => true
      | _           => false
      end.

  End SymbolicPaths.

  Section VerificationConditions.

    Inductive VerificationCondition {AT} (p : SPath AT ctx_nil) : Prop :=
    | vc (P : spath_safe _ env_nil p).

  End VerificationConditions.

  Section SMutatorResult.

    (* Local Set Primitive Projections. *)
    Local Set Maximal Implicit Insertion.

    Record SMutResult (Γ : PCtx) (A : LCtx -> Type) (Σ : LCtx) : Type :=
      MkSMutResult {
          smutres_value : A Σ;
          smutres_store : SStore Γ Σ;
          smutres_heap  : SHeap Σ;
        }.

    Global Arguments MkSMutResult {_ _ _} _ _ _.

    Global Instance SubstSMutResult {Γ A} `{Subst A} : Subst (SMutResult Γ A).
    Proof.
      intros Σ1 Σ2 ζ [a δ h].
      constructor.
      apply (subst ζ a).
      apply (subst ζ δ).
      apply (subst ζ h).
   Defined.

    Global Instance SubstLawsSMutResult {Γ A} `{SubstLaws A} : SubstLaws (SMutResult Γ A).
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

  End SMutatorResult.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Section SMutator.

    Definition SMut (Γ1 Γ2 : PCtx) (A : LCtx -> Type) (Σ : LCtx) : Type :=
      forall Σ', Sub Σ Σ' -> PathCondition Σ' -> SStore Γ1 Σ' -> SHeap Σ' -> SPath (SMutResult Γ2 A) Σ'.
    Bind Scope smut_scope with SMut.

    Definition smut_pure {Γ A} `{Subst A} {Σ} (a : A Σ) : SMut Γ Γ A Σ.
      intros Σ1 ζ1 pc1 δ h.
      apply spath_pure.
      constructor.
      apply (subst ζ1 a).
      apply δ.
      apply h.
    Defined.

    Definition smut_bind {Γ1 Γ2 Γ3 A B Σ} (ma : SMut Γ1 Γ2 A Σ) (f : forall Σ', Sub Σ Σ' -> A Σ' -> SMut Γ2 Γ3 B Σ') : SMut Γ1 Γ3 B Σ.
    Proof.
      intros Σ1 ζ1 pc1 δ1 h1.
      apply (spath_bind pc1 (ma Σ1 ζ1 pc1 δ1 h1)).
      intros Σ2 ζ2 pc2 [a2 δ2 h2].
      eapply (spath_bind pc2).
      apply (f Σ2 (sub_comp ζ1 ζ2) a2 _ (sub_id _) pc2 δ2 h2).
      intros Σ3 ζ3 pc3 [b3 δ3 h3].
      apply spath_pure.
      constructor.
      apply b3.
      apply δ3.
      apply h3.
    Defined.
    (* Definition smut_join {Γ1 Γ2 Γ3 A Σ} (mm : SMut Γ1 Γ2 (SMut Γ2 Γ3 A) Σ) : *)
    (*   SMut Γ1 Γ3 A Σ := smut_bind mm (fun _ _ m => m). *)

    Definition smut_sub {Γ1 Γ2 A Σ1 Σ2} (ζ1 : Sub Σ1 Σ2) (p : SMut Γ1 Γ2 A Σ1) :
      SMut Γ1 Γ2 A Σ2 := fun Σ3 ζ2 => p _ (sub_comp ζ1 ζ2).
    Global Arguments smut_sub {_ _ _ _ _} ζ1 p.
    Definition smut_strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : SMut Γ1 Γ2 A Σ) (b : B Σ) :
      SMut Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ :=
      smut_bind ma (fun _ ζ a => smut_pure (a, subst ζ b)).
    Definition smut_bind_right {Γ1 Γ2 Γ3 A B Σ} (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ) : SMut Γ1 Γ3 B Σ :=
      smut_bind ma (fun _ ζ _ => smut_sub ζ mb).
    Definition smut_bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} {Σ} (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ) : SMut Γ1 Γ3 A Σ :=
      smut_bind ma (fun _ ζ a => smut_bind_right (smut_sub ζ mb) (smut_pure a)) .
    Definition smut_fmap {Γ1 Γ2 Σ A B} `{Subst A, Subst B}
      (ma : SMut Γ1 Γ2 A Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ') :
      SMut Γ1 Γ2 B Σ :=
      fun Σ1 ζ01 pc1 δ1 h1 =>
        @spath_map (SMutResult Γ2 A) (SMutResult Γ2 B) Σ1
        (fun Σ2 ζ12 '(MkSMutResult a2 δ2 h2) => MkSMutResult (f Σ2 (sub_comp ζ01 ζ12) a2) δ2 h2)
        (ma Σ1 ζ01 pc1 δ1 h1).
    Definition smut_fmap2 {Γ1 Γ2 Γ3 Σ A B C} `{Subst A, Subst B, Subst C}
      (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ' -> C Σ') :
      SMut Γ1 Γ3 C Σ :=
      smut_bind ma (fun Σ1 ζ01 a1 =>
        smut_fmap (smut_sub ζ01 mb) (fun Σ2 ζ12 =>
          f Σ2 (sub_comp ζ01 ζ12) (subst ζ12 a1))).
    Definition smut_pair {Γ1 Γ2 Γ3 Σ A B} `{Subst A, Subst B}
      (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ) :
      SMut Γ1 Γ3 (fun Σ => A Σ * B Σ)%type Σ :=
      smut_fmap2 ma mb (fun _ _ => pair).

    Definition smut_fail {Γ1 Γ2 A Σ D} (func : string) (msg : string) (data:D) : SMut Γ1 Γ2 A Σ.
      intros Σ1 ζ1 pc1 δ1 h1.
      apply spath_fail.
      apply (@MkMessage _ func msg Γ1); assumption.
    Defined.

    Definition smut_block {Γ1 Γ2 A Σ} : SMut Γ1 Γ2 A Σ :=
      fun _ _ _ _ _ => spath_block.

    Definition smut_angelic_binary {Γ1 Γ2 A Σ} (m1 m2 : SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 => spath_angelic_binary (m1 Σ1 ζ1 pc1 δ1 h1) (m2 Σ1 ζ1 pc1 δ1 h1).
    Definition smut_demonic_binary {Γ1 Γ2 A Σ} (m1 m2 : SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 => spath_demonic_binary (m1 Σ1 ζ1 pc1 δ1 h1) (m2 Σ1 ζ1 pc1 δ1 h1).
    Fixpoint smut_angelic_list {AT D} `{Subst AT} {Γ Σ} (func : string) (msg : string) (data:D) (xs : List AT Σ) :
      SMut Γ Γ AT Σ :=
      match xs with
      | nil        => smut_fail func msg data
      | cons x nil => smut_pure x
      | cons x xs  => smut_angelic_binary (smut_pure x) (smut_angelic_list func msg data xs)
      end.
    Fixpoint smut_angelic_listk {AT D} {Γ1 Γ2 Σ} (func : string) (msg : string) (data:D) (xs : List AT Σ)
      {BT} (k : AT Σ -> SMut Γ1 Γ2 BT Σ) {struct xs} : SMut Γ1 Γ2 BT Σ :=
      match xs with
      | nil => smut_fail func msg data
      | cons x nil => k x
      | cons x xs => smut_angelic_binary (k x) (smut_angelic_listk func msg data xs k)
      end.
    Fixpoint smut_demonic_list {AT} `{Subst AT} {Γ Σ} (xs : List AT Σ) : SMut Γ Γ AT Σ :=
      match xs with
      | nil        => smut_block
      | cons x nil => smut_pure x
      | cons x xs  => smut_demonic_binary (smut_pure x) (smut_demonic_list xs)
      end.
    Fixpoint smut_demonic_listk {AT} {Γ1 Γ2 Σ} (xs : List AT Σ)
      {BT} (k : AT Σ -> SMut Γ1 Γ2 BT Σ) {struct xs} : SMut Γ1 Γ2 BT Σ :=
      match xs with
      | nil => smut_block
      | cons x nil => k x
      | cons x xs => smut_demonic_binary (k x) (smut_demonic_listk xs k)
      end.

    Definition smut_angelic_finite {Γ1 Γ2 A} F `{finite.Finite F} {Σ}
      (cont : F -> SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
      smut_angelic_listk "smut_angelic_finite" "All branches failed" tt (finite.enum F) cont.
    Definition smut_demonic_finite {Γ1 Γ2 A} F `{finite.Finite F} {Σ}
      (cont : F -> SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
      (smut_demonic_listk (finite.enum F)) cont.
    Global Arguments smut_angelic_finite {_ _ _} _ {_ _ _} _.
    Global Arguments smut_demonic_finite {_ _ _} _ {_ _ _} _.

    Definition smut_angelicv {Γ1 Γ2 A Σ} x τ (ma : SMut Γ1 Γ2 A (Σ ▻ (x :: τ))) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 =>
        let x'  := fresh Σ1 (Some x) in
        let ζ1x := sub_snoc (sub_comp ζ1 sub_wk1) (x :: τ) (@term_var _ x' τ inctx_zero) in
        spath_angelicv (x' :: τ) (ma (Σ1 ▻ (x' :: τ)) ζ1x (subst sub_wk1 pc1) (subst sub_wk1 δ1) (subst sub_wk1 h1)).
    Global Arguments smut_angelicv {_ _ _ _} _ _ _.

    Definition smut_demonicv {Γ1 Γ2 A Σ} x τ (ma : SMut Γ1 Γ2 A (Σ ▻ (x :: τ))) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 =>
        let x'  := fresh Σ1 (Some x) in
        let ζ1x := sub_snoc (sub_comp ζ1 sub_wk1) (x :: τ) (@term_var _ x' τ inctx_zero) in
        spath_demonicv (x' :: τ) (ma (Σ1 ▻ (x' :: τ)) ζ1x (subst sub_wk1 pc1) (subst sub_wk1 δ1) (subst sub_wk1 h1)).
    Global Arguments smut_demonicv {_ _ _ _} _ _ _.

    Definition smut_angelic {AT Γ1 Γ2 Σ0} (x : option 𝑺) σ
      (k : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1) :
      SMut Γ1 Γ2 AT Σ0 :=
      fun Σ1 ζ01 pc1 δ1 h1 =>
        spath_angelic x σ
          (fun Σ2 ζ12 pc2 t2 =>
             four k ζ01 ζ12 t2 Σ2
               (sub_id Σ2)
               pc2
               (subst ζ12 δ1)
               (subst ζ12 h1)) pc1.
    Global Arguments smut_angelic {_ _ _ _} x σ k.

    Definition smut_demonic_termvar {Γ Σ} (x : option 𝑺) σ : SMut Γ Γ (fun Σ => Term Σ σ) Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 =>
        let y := fresh Σ1 x in
        spath_demonicv (y :: σ)
          (spath_pure
             {|
               smutres_value := @term_var _ y σ inctx_zero;
               smutres_store := subst sub_wk1 δ1;
               smutres_heap := subst sub_wk1 h1;
             |}).
    Global Arguments smut_demonic_termvar {_ _} x σ.

    Definition smut_debug {AT DT D} `{Subst DT, Inst DT D, OccursCheck DT} {Σ0 Γ1 Γ2}
      (d : forall Σ1, Sub Σ0 Σ1 -> PathCondition Σ1 -> SStore Γ1 Σ1 -> SHeap Σ1 -> DT Σ1)
      (m : SMut Γ1 Γ2 AT Σ0) : SMut Γ1 Γ2 AT Σ0 :=
      fun Σ1 ζ01 pc1 δ1 h1 => spath_debug (d Σ1 ζ01 pc1 δ1 h1) (m Σ1 ζ01 pc1 δ1 h1).

  End SMutator.
  Bind Scope smut_scope with SMut.

  Module SMutatorNotations.

    (* Notation "'⨂' x .. y => F" := *)
    (*   (smut_demonic (fun x => .. (smut_demonic (fun y => F)) .. )) : smut_scope. *)

    (* Notation "'⨁' x .. y => F" := *)
    (*   (smut_angelic (fun x => .. (smut_angelic (fun y => F)) .. )) : smut_scope. *)

    Infix "⊗" := smut_demonic_binary (at level 40, left associativity) : smut_scope.
    Infix "⊕" := smut_angelic_binary (at level 50, left associativity) : smut_scope.

    Notation "x <- ma ;; mb" := (smut_bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : smut_scope.
    Notation "ma >>= f" := (smut_bind ma f) (at level 50, left associativity) : smut_scope.
    Notation "m1 ;; m2" := (smut_bind_right m1 m2) : smut_scope.

  End SMutatorNotations.
  Import SMutatorNotations.
  Local Open Scope smut_scope.

  Definition smut_state {Γ Γ' A Σ} (f : forall Σ', Sub Σ Σ' -> SStore Γ Σ' -> SHeap Σ' -> SMutResult Γ' A Σ') :
    SMut Γ Γ' A Σ.
  Proof.
    intros Σ1 ζ1 pc1 δ1 h1.
    destruct (f Σ1 ζ1 δ1 h1) as [a δ2 h2].
    apply spath_pure.
    constructor.
    apply a.
    apply δ2.
    apply h2.
  Defined.

  Definition smut_get_local {Γ Σ} : SMut Γ Γ (fun Σ => SStore Γ Σ) Σ :=
    smut_state (fun _ _ δ h => MkSMutResult δ δ h).
  Definition smut_put_local {Γ Γ' Σ} (δ' : SStore Γ' Σ) : SMut Γ Γ' Unit Σ :=
    smut_state (fun _ ζ _ h => MkSMutResult tt (subst ζ δ') h).
  Definition smut_pop_local {Γ x σ Σ} : SMut (Γ ▻ (x , σ)) Γ Unit Σ :=
    smut_state (fun _ _ δ h => MkSMutResult tt (env_tail δ) h).
  Definition smut_pops_local {Γ} Δ {Σ} : SMut (Γ ▻▻ Δ) Γ Unit Σ :=
    smut_state (fun _ _ δ h => MkSMutResult tt (env_drop Δ δ) h).
  Definition smut_push_local {Γ x σ Σ} (t : Term Σ σ) : SMut Γ (Γ ▻ (x , σ)) Unit Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult tt (env_snoc δ (x :: σ) (subst ζ t)) h).
  Definition smut_pushs_local {Γ Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) : SMut Γ (Γ ▻▻ Δ) Unit Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult tt (δ ►► (subst ζ δΔ)) h).
  Definition smut_pushpop {AT} `{Subst AT} {Γ1 Γ2 x σ Σ} (t : Term Σ σ) (d : SMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) :
    SMut Γ1 Γ2 AT Σ :=
    smut_push_local t ;; smut_bind_left d smut_pop_local.
  Definition smut_pushspops {AT} `{Subst AT} {Γ1 Γ2 Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) (d : SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT Σ) :
    SMut Γ1 Γ2 AT Σ :=
    smut_pushs_local δΔ ;; smut_bind_left d (smut_pops_local Δ).
  Definition smut_get_heap {Γ Σ} : SMut Γ Γ SHeap Σ :=
    smut_state (fun _ _ δ h => MkSMutResult h δ h).
  Definition smut_put_heap {Γ Σ} (h : SHeap Σ) : SMut Γ Γ Unit Σ :=
    smut_state (fun _ ζ δ _ => MkSMutResult tt δ (subst ζ h)).
  Definition smut_eval_exp {Γ σ} (e : Exp Γ σ) {Σ} : SMut Γ Γ (fun Σ => Term Σ σ) Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult (seval_exp δ e) δ h).
  Definition smut_eval_exps {Γ Σ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : SMut Γ Γ (SStore σs) Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult (env_map (fun _ => seval_exp δ) es) δ h).

  Fixpoint smut_demonic_freshen_ctx {N : Set} {Γ Σ0} (n : N -> 𝑺) (Δ : NCtx N Ty) :
    SMut Γ Γ (fun Σ => NamedEnv (Term Σ) Δ) Σ0 :=
   match Δ  with
   | ε            => smut_pure env_nil
   | Δ ▻ (x :: σ) =>
       smut_demonic_freshen_ctx n Δ        >>= fun _ _ δΔ =>
       smut_demonic_termvar (Some (n x)) σ >>= fun _ ζ12 t =>
       smut_pure (subst ζ12 δΔ ► (x :: σ ↦ t))
   end.

  (* Add the provided formula to the path condition. *)
  Definition smut_assume_formula {Γ Σ} (fml : Formula Σ) : SMut Γ Γ Unit Σ :=
    fun Σ1 ζ1 pc1 δ1 h1 =>
      spath_bind pc1
        (spath_assume_formula (subst ζ1 fml) pc1)
        (fun Σ2 ζ12 pc2 v => spath_pure (MkSMutResult v (subst ζ12 δ1) (subst ζ12 h1))).
  Definition smut_assume_formulas {Γ Σ} (fmls : list (Formula Σ)) : SMut Γ Γ Unit Σ :=
    fold_right (fun fml => smut_bind_right (smut_assume_formula fml)) (smut_pure tt) fmls.

  Definition smut_assert_formula {Γ Σ} (fml : Formula Σ) : SMut Γ Γ Unit Σ :=
    fun Σ1 ζ1 pc1 δ1 h1 =>
      spath_bind pc1
        (spath_assert_formula
           {| msg_function        := "smut_assert_formula";
              msg_message         := "Proof obligation";
              msg_program_context := Γ;
              msg_pathcondition   := pc1;
              msg_localstore      := δ1;
              msg_heap            := h1;
           |}
           pc1 (subst ζ1 fml))
        (fun Σ2 ζ12 pc2 v => spath_pure (MkSMutResult v (subst ζ12 δ1) (subst ζ12 h1))).

  Definition smut_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) : SMut Γ Γ Unit Σ :=
    fold_right (fun fml => smut_bind_right (smut_assert_formula fml)) (smut_pure tt) fmls.
  Definition smut_assert_term {Γ Σ} (t : Term Σ ty_bool) : SMut Γ Γ Unit Σ :=
    smut_assert_formula (formula_bool t).
  Definition smut_produce_chunk {Γ Σ} (c : Chunk Σ) : SMut Γ Γ Unit Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult tt δ (cons (subst ζ c) h)).
  Definition smut_consume_chunk {Γ Σ} (c : Chunk Σ) : SMut Γ Γ Unit Σ :=
     smut_get_heap >>= fun Σ1 ζ1 h1 =>
     smut_angelic_list "smut_consume_chunk" "Empty extraction" c
       (extract_chunk_eqb (subst ζ1 c) h1) >>= fun Σ2 ζ2 '(Δpc2 , h2) =>
     smut_assert_formulas Δpc2 ;;
     smut_put_heap h2.

  Definition smut_assert_formulak {A Γ1 Γ2 Σ} (fml : Formula Σ) (k : SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
    smut_bind_right (smut_assert_formula fml) k.
  Definition smut_assert_formulask {A Γ1 Γ2 Σ} (fmls : list (Formula Σ)) (k: SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
    fold_right smut_assert_formulak k fmls.

  Definition smut_leakcheck {Γ Σ} : SMut Γ Γ Unit Σ :=
    smut_get_heap >>= fun _ _ h =>
    match h with
    | nil => smut_pure tt
    | _   => smut_fail "smut_leakcheck" "Heap leak" h
    end.

  Definition smut_demonic_match_bool {AT} {Γ1 Γ2 Σ} (t : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_lit t' with
      | Some true => dt Σ1 ζ01
      | Some false => df Σ1 ζ01
      | None =>
        ((smut_assume_formula (formula_bool t') ;; smut_sub ζ01 dt) ⊗
         (smut_assume_formula (formula_bool (term_not t')) ;; smut_sub ζ01 df))
          (sub_id Σ1)
      end.

  Definition smut_angelic_match_bool {AT} {Γ1 Γ2 Σ} (t : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_lit t' with
      | Some true => dt Σ1 ζ01
      | Some false => df Σ1 ζ01
      | None =>
        ((smut_assert_formula (formula_bool t') ;; smut_sub ζ01 dt) ⊕
         (smut_assert_formula (formula_bool (term_not t')) ;; smut_sub ζ01 df))
          (sub_id Σ1)
      end.

  Definition smut_demonic_match_enum {AT E} {Γ1 Γ2 Σ} (t : Term Σ (ty_enum E))
    (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_lit t' with
      | Some k => d k Σ1 ζ01
      | None => smut_demonic_finite
                  (𝑬𝑲 E)
                  (fun k => smut_assume_formula (formula_eq t' (term_enum E k));; smut_sub ζ01 (d k)) _ (sub_id Σ1)
      end.

  Definition smut_demonic_match_sum' {AT Γ1 Γ2 Σ0} (x y : 𝑺) {σ τ} (t : Term Σ0 (ty_sum σ τ))
    (dinl : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1)
    (dinr : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 τ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_binary
      (smut_demonic_termvar (Some x) σ >>= fun _ ζ12 tσ =>
       smut_assume_formula
         (formula_eq (subst (T := fun Σ => Term Σ _) ζ12 t) (term_inl tσ)) ;;
          dinl _ ζ12 tσ)
      (smut_demonic_termvar (Some y) τ >>= fun _ ζ12 tτ =>
       smut_assume_formula
         (formula_eq (subst (T := fun Σ => Term Σ _) ζ12 t) (term_inr tτ)) ;;
          dinr _ ζ12 tτ).

  Definition smut_demonic_match_sum {AT Γ1 Γ2 Σ0} (x y : 𝑺) {σ τ} (t : Term Σ0 (ty_sum σ τ))
    (dinl : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1)
    (dinr : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 τ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_sum t' with
      | Some (inl tl) => dinl Σ1 ζ01 tl Σ1 (sub_id _)
      | Some (inr tr) => dinr Σ1 ζ01 tr Σ1 (sub_id _)
      | None => smut_demonic_match_sum' x y t' (four dinl ζ01) (four dinr ζ01) (sub_id _)
      end.

  Definition smut_demonic_match_pair {AT} {Γ1 Γ2 Σ} (x y : 𝑺) {σ τ} (s : Term Σ (ty_prod σ τ))
    (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ) ▻ (y :: τ))) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
    match term_get_pair (subst (T := fun Σ => Term Σ _) ζ01 s) with
    | Some (tl,tr) => d Σ1 (sub_snoc (sub_snoc ζ01 (x :: σ) tl) (y :: τ) tr)
    | None =>
      smut_demonicv x σ (smut_demonicv y τ
        (smut_assume_formula
           (formula_eq
              (subst (T := fun Σ => Term Σ _) (sub_comp sub_wk1 sub_wk1) s)
              (term_binop
                 binop_pair
                 (@term_var _ x σ (inctx_succ inctx_zero))
                 (@term_var _ y τ inctx_zero))) ;;
         d))
        Σ1 ζ01
    end.

  Definition smut_demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_freshen_ctx n Δ >>= fun _ ζ01 ts =>
    smut_assume_formula
      (formula_eq
         (subst ζ01 t)
         (term_record R (record_pattern_match_env_reverse p ts))) ;;
    d _ ζ01 ts.

  Definition smut_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_record t' with
      | Some ts =>
        let tsΔ := record_pattern_match_env p ts in
        d Σ1 ζ01 tsΔ Σ1 (sub_id _)
      | None =>
        smut_demonic_match_record' n t' p (four d ζ01) (sub_id _)
      end.

  Definition smut_demonic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_tuple σs)) (p : TuplePat σs Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_freshen_ctx n Δ >>= fun _ ζ01 ts =>
    smut_assume_formula
      (formula_eq
         (subst ζ01 t)
         (term_tuple (tuple_pattern_match_env_reverse p ts))) ;;
      d _ ζ01 ts.

  Definition smut_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_tuple σs)) (p : TuplePat σs Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_tuple t' with
      | Some ts =>
        let tsΔ := tuple_pattern_match_env p ts in
        d Σ1 ζ01 tsΔ Σ1 (sub_id _)
      | None => smut_demonic_match_tuple' n t' p (four d ζ01) (sub_id _)
      end.

  Definition pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
    NamedEnv (Term Σ) Δ -> Term Σ σ :=
    match p with
    | pat_var x    => fun Ex => match snocView Ex with isSnoc _ t => t end
    | pat_unit     => fun _ => term_lit ty_unit tt
    | pat_pair x y => fun Exy => match snocView Exy with
                                   isSnoc Ex ty =>
                                   match snocView Ex with
                                     isSnoc _ tx => term_binop binop_pair tx ty
                                   end
                                 end
    | pat_tuple p  => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ)
    | pat_record p => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ)
    end.

  Definition smut_demonic_match_pattern {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 σ Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 σ) (p : Pattern Δ σ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_freshen_ctx n Δ >>= fun _ ζ01 ts =>
    smut_assume_formula
      (formula_eq
         (subst ζ01 t)
         (pattern_match_env_reverse p ts)) ;;
    d _ ζ01 ts.

  Definition smut_demonic_match_union' {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U Σ0} {Δ : 𝑼𝑲 U -> NCtx N Ty}
    (t : Term Σ0 (ty_union U)) (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K))
    (d : forall (K : 𝑼𝑲 U) Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) (Δ K) -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_finite (𝑼𝑲 U)
      (fun K =>
         smut_demonic_termvar None (𝑼𝑲_Ty K) >>= fun Σ1 ζ01 t__field =>
         smut_assume_formula (formula_eq (term_union U K t__field) (subst ζ01 t)) ;;
         smut_demonic_match_pattern n t__field (p K) (four (d K) ζ01)).

  Definition smut_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U Σ0} {Δ : 𝑼𝑲 U -> NCtx N Ty}
    (t : Term Σ0 (ty_union U)) (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K))
    (d : forall (K : 𝑼𝑲 U) Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) (Δ K) -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) ζ01 t in
      match term_get_union t' with
      | Some (existT K t__field) =>
        smut_demonic_match_pattern n t__field (p K) (four (d K) ζ01) (sub_id _)
      | None =>
        smut_demonic_match_union' n t' p (fun K => four (d K) ζ01) (sub_id _)
      end.

  Fixpoint smut_produce {Γ Σ} (asn : Assertion Σ) : SMut Γ Γ Unit Σ :=
    match asn with
    | asn_formula fml => smut_assume_formula fml
    | asn_chunk c     => smut_produce_chunk c
    | asn_if b a1 a2  =>
      smut_demonic_match_bool b (smut_produce a1) (smut_produce a2)
    | asn_match_enum E t alts =>
      smut_demonic_match_enum t (fun k => smut_produce (alts k))
    | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
      smut_demonic_match_sum xl xr s
        (fun Σ1 ζ01 t => smut_sub (sub_snoc ζ01 (xl :: _) t) (smut_produce alt_inl))
        (fun Σ1 ζ01 t => smut_sub (sub_snoc ζ01 (xr :: _) t) (smut_produce alt_inr))
    | asn_match_list s alt_nil xh xt alt_cons =>
      smut_fail "smut_produce" "Not implemented" asn
    | asn_match_pair s xl xr rhs =>
      smut_demonic_match_pair s (smut_produce rhs)
    | asn_match_tuple s p rhs =>
      smut_demonic_match_tuple id s p (fun Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_produce rhs))
    | asn_match_record R s p rhs =>
      smut_demonic_match_record id s p (fun Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_produce rhs))
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      smut_demonic_match_union id s alt__pat (fun K Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_produce (alt__rhs K)))
    | asn_sep a1 a2   => smut_produce a1 ;; smut_produce a2
    | asn_exist ς τ a => smut_demonicv ς τ (smut_produce a)
    | asn_debug =>
      smut_debug
        (fun Σ1 ζ01 pc1 δ1 h1 =>
           {| sdebug_asn_pathcondition := pc1;
              sdebug_asn_program_context := Γ;
              sdebug_asn_localstore := δ1;
              sdebug_asn_heap := h1;
           |})
        (smut_pure tt)
    end.

  Fixpoint smut_producek {Γ1 Γ2 Σ} (asn : Assertion Σ) {AT} (k : SMut Γ1 Γ2 AT Σ) {struct asn} : SMut Γ1 Γ2 AT Σ :=
    match asn with
    | asn_formula fml => smut_assume_formula fml;; k
    | asn_chunk c => smut_produce_chunk c;; k
    | asn_if b asn1 asn2 =>
      smut_demonic_match_bool b (smut_producek asn1 k) (smut_producek asn2 k)
    | asn_match_enum E k0 alts => smut_demonic_match_enum k0 (fun k1 : 𝑬𝑲 E => smut_producek (alts k1) k)
    | asn_match_sum σ τ s xl asn1 xr asn2 =>
      smut_fail "smut_produce" "Not implemented" asn
    | asn_match_list s alt_nil xh xt alt_cons =>
      smut_fail "smut_produce" "Not implemented" asn
    | asn_match_pair s xl xr asn =>
      smut_demonic_match_pair s (smut_producek asn (smut_sub (sub_cat_left (ε ▻ (xl,_) ▻ (xr,_))) k))
    | asn_match_tuple s p asn =>
      smut_demonic_match_tuple id s p
        (fun Σ1 ζ01 ts => smut_sub (env_cat ζ01 ts) (smut_producek asn (smut_sub (sub_cat_left _) k)))
    | asn_match_record R s p asn =>
      smut_demonic_match_record id s p
        (fun Σ1 ζ01 ts => smut_sub (env_cat ζ01 ts) (smut_producek asn (smut_sub (sub_cat_left _) k)))
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      smut_fail "smut_produce" "Not implemented" asn
    | asn_sep asn1 asn2 => smut_producek asn1 (smut_producek asn2 k)
    | asn_exist ς τ asn => smut_demonicv ς τ (smut_producek asn (smut_sub sub_wk1 k))
    | asn_debug =>
      smut_debug
        (fun Σ1 ζ01 pc1 δ1 h1 =>
           {| sdebug_asn_program_context := Γ1;
              sdebug_asn_pathcondition := pc1;
              sdebug_asn_localstore := δ1;
              sdebug_asn_heap := h1
           |})
        k
    end.

  Fixpoint smut_consume {Γ Σ} (asn : Assertion Σ) : SMut Γ Γ Unit Σ :=
    match asn with
    | asn_formula fml => smut_assert_formula fml
    | asn_chunk c     => smut_consume_chunk c
    | asn_if b a1 a2  =>
      smut_demonic_match_bool b (smut_consume a1) (smut_consume a2)
    | asn_match_enum E t alts =>
      smut_demonic_match_enum t (fun k => smut_consume (alts k))
    | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
      smut_demonic_match_sum xl xr s
        (fun Σ1 ζ01 t => smut_sub (sub_snoc ζ01 (xl :: _) t) (smut_consume alt_inl))
        (fun Σ1 ζ01 t => smut_sub (sub_snoc ζ01 (xr :: _) t) (smut_consume alt_inr))
    | asn_match_list s alt_nil xh xt alt_cons =>
      smut_fail "smut_consume" "Not implemented" asn
    | asn_match_pair s xl xr rhs =>
      smut_demonic_match_pair s (smut_consume rhs)
    | asn_match_tuple s p rhs =>
      smut_demonic_match_tuple id s p (fun Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_consume rhs))
    | asn_match_record R s p rhs =>
      smut_demonic_match_record id s p (fun Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_consume rhs))
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      smut_fail  "smut_consume" "Not implemented" asn
    | asn_sep a1 a2   => smut_consume a1 ;; smut_consume a2
    | asn_exist ς τ a =>
      smut_angelicv ς τ (smut_consume a)
    | asn_debug =>
      smut_debug
        (fun Σ1 ζ01 pc1 δ1 h1 =>
           {| sdebug_asn_pathcondition := pc1;
              sdebug_asn_program_context := Γ;
              sdebug_asn_localstore := δ1;
              sdebug_asn_heap := h1;
           |})
        (smut_pure tt)
    end.

  Definition smut_angelicvs {A Γ1 Γ2 Σ} Δ (k : SMut Γ1 Γ2 A (Σ ▻▻ Δ)) : SMut Γ1 Γ2 A Σ :=
    fun Σ1 ζ01 pc1 δ1 h1 =>
      let ζl   := sub_cat_left Δ in
      let ζ01' := sub_comp ζ01 ζl ►► sub_cat_right Δ in
      spath_angelicvs Δ (k (Σ1 ▻▻ Δ) ζ01' (subst ζl pc1) (subst ζl δ1) (subst ζl h1)).

  Definition smut_call {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : SMut Γ Γ (fun Σ => Term Σ τ) Σr :=
    match contract with
    | MkSepContract _ _ Σe δ req result ens =>
      let ζleft := sub_cat_left Σe in
      let ζright := sub_cat_right Σe in
      smut_angelicvs Σe
        (smut_assert_formulask
           (formula_eqs (subst ζright δ) (subst (T:=fun Σ => NamedEnv (Term Σ) Δ) ζleft ts))
           (smut_sub ζright
              (smut_consume req ;;
               smut_demonicv result τ
                 (smut_produce ens ;;
                  smut_pure (@term_var _ result _ inctx_zero)))))
    end.

  Definition smut_exec_match_record {AT} `{Subst AT} {R Γ Δ Σ0}
    (t : Term Σ0 (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
    (d : SMut (Γ ▻▻ Δ) (Γ ▻▻ Δ) AT Σ0) : SMut Γ Γ AT Σ0 :=
    smut_demonic_match_record 𝑿to𝑺 t p
      (fun Σ1 ζ01 ts => smut_pushspops ts (smut_sub ζ01 d)).

  Definition smut_exec_match_tuple {AT} `{Subst AT} {σs Γ Δ Σ0}
    (t : Term Σ0 (ty_tuple σs)) (p : TuplePat σs Δ)
    (d : SMut (Γ ▻▻ Δ) (Γ ▻▻ Δ) AT Σ0) : SMut Γ Γ AT Σ0 :=
    smut_demonic_match_tuple 𝑿to𝑺 t p
      (fun Σ1 ζ01 ts => smut_pushspops ts (smut_sub ζ01 d)).

  Definition smut_exec_match_pattern {AT} `{Subst AT} {Γ Δ σ Σ0}
    (t : Term Σ0 σ) (p : Pattern Δ σ)
    (rhs : SMut (Γ ▻▻ Δ) (Γ ▻▻ Δ) AT Σ0) :
    SMut Γ Γ AT Σ0 :=
      smut_demonic_freshen_ctx 𝑿to𝑺 Δ >>= fun _ ζ01 ts =>
      smut_assume_formula
        (formula_eq
           (subst ζ01 t)
           (pattern_match_env_reverse p ts)) ;;
      smut_pushspops ts (smut_sub ζ01 rhs).

  Definition smut_exec_match_union {AT} `{Subst AT} {U Γ Σ0} {Δ : 𝑼𝑲 U -> PCtx}
    (t : Term Σ0 (ty_union U))
    (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K))
    (rhs : forall K : 𝑼𝑲 U, SMut (Γ ▻▻ Δ K) (Γ ▻▻ Δ K) AT Σ0) :
    SMut Γ Γ AT Σ0 :=
    smut_demonic_match_union
      𝑿to𝑺 t p
      (fun K Σ1 ζ01 ts => smut_pushspops ts (smut_sub ζ01 (rhs K))).

  Fixpoint smut_exec {Γ τ Σ} (s : Stm Γ τ) {struct s} :
    SMut Γ Γ (fun Σ => Term Σ τ) Σ :=
    match s with
    | stm_lit _ l => smut_pure (term_lit τ l)
    | stm_exp e => smut_eval_exp e
    | stm_let x τ s1 s2 =>
      t1 <- smut_exec s1 ;;
      smut_pushpop t1 (smut_exec s2)
    | stm_block δ s =>
      smut_pushspops (lift δ) (smut_exec s)
    | stm_assign x s =>
      t <- smut_exec s ;;
      smut_state (fun _ ζ δ h => MkSMutResult tt (δ ⟪ x ↦ subst ζ t ⟫)%env h) ;;
      smut_pure t
    | stm_call f es =>
      ts <- smut_eval_exps es ;;
      match CEnv f with
      | Some c => smut_call c ts
      | None   => smut_fail "smut_exec" "Function call without contract" (f,ts)
      end
    | stm_call_frame δ s =>
      δr <- smut_get_local ;;
      smut_put_local (lift δ) ;;
      smut_bind_left (smut_exec s) (smut_put_local δr)
    | stm_call_external f es =>
      ts <- smut_eval_exps es ;;
      smut_call (CEnvEx f) ts
    | stm_if e s1 s2 =>
      t <- smut_eval_exp e ;;
      smut_demonic_match_bool t (smut_exec s1) (smut_exec s2)
    | stm_seq s1 s2 => smut_exec s1 ;; smut_exec s2
    | stm_assertk e1 _ k =>
      t <- smut_eval_exp e1 ;;
      smut_assume_formula (formula_bool t) ;;
      smut_exec k
    | stm_fail _ _ =>
      smut_block
    | stm_match_list e s1 xh xt s2 =>
      t <- smut_eval_exp e ;;
      (smut_assume_formula
         (formula_eq t (term_lit (ty_list _) nil));;
       smut_exec s1) ⊗
      (smut_demonicv
         (𝑿to𝑺 xh) _ (smut_demonicv (𝑿to𝑺 xt) _
         (smut_assume_formula
            (formula_eq (subst (sub_comp sub_wk1 sub_wk1) t)
                        (term_binop binop_cons (@term_var _ _ _ (inctx_succ inctx_zero)) (@term_var _ _ _ inctx_zero)));;
          smut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
          smut_push_local (@term_var _ _ _ inctx_zero);;
          t2 <- smut_exec s2 ;;
          smut_pop_local ;;
          smut_pop_local ;;
          smut_pure t2)))
    | stm_match_sum e xinl s1 xinr s2 =>
      t <- smut_eval_exp e ;;
      smut_demonic_match_sum
        (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t
        (fun _ _ tl => smut_pushpop tl (smut_exec s1))
        (fun _ _ tr => smut_pushpop tr (smut_exec s2))
    | stm_match_pair e xl xr s =>
      t <- smut_eval_exp e ;;
      smut_demonic_match_pair
        t
        (smut_pushspops
           (env_snoc (env_snoc env_nil
              (xl :: _) (@term_var _ (𝑿to𝑺 xl) _ (inctx_succ inctx_zero)))
              (xr :: _) (@term_var _ (𝑿to𝑺 xr) _ inctx_zero))
           (smut_exec s))
    | stm_match_enum E e alts =>
      t <- smut_eval_exp e ;;
      smut_demonic_match_enum t (fun K => smut_exec (alts K))
    | stm_match_tuple e p rhs =>
      t <- smut_eval_exp e ;;
      smut_exec_match_tuple t p (smut_exec rhs)
    | stm_match_union U e alt__pat alt__rhs =>
      t <- smut_eval_exp e ;;
      smut_exec_match_union t alt__pat (fun K => smut_exec (alt__rhs K))
    | @stm_match_record _ _ R Δ e p rhs =>
      t <- smut_eval_exp e ;;
      smut_exec_match_record t p (smut_exec rhs)
    | stm_read_register reg =>
      smut_angelic None τ
        (fun _ _ t =>
           smut_consume_chunk (chunk_ptsreg reg t);;
           smut_produce_chunk (chunk_ptsreg reg t);;
           smut_pure t)
    | stm_write_register reg e =>
      tnew <- smut_eval_exp e ;;
      smut_angelic None τ
        (fun _ ζ told =>
           let tnew := subst ζ tnew in
           smut_consume_chunk (chunk_ptsreg reg told) ;;
           smut_produce_chunk (chunk_ptsreg reg tnew) ;;
           smut_pure tnew)
    | stm_bind _ _ =>
      smut_fail "smut_exec" "stm_bind not supported" tt
    | stm_debugk k =>
      smut_debug
        (fun Σ1 ζ01 pc1 δ1 h1 =>
           {| sdebug_stm_statement := k;
              sdebug_stm_pathcondition := pc1;
              sdebug_stm_localstore := δ1;
              sdebug_stm_heap := h1
           |})
        (smut_exec k)
    end.

  Definition smut_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : SMut Δ Δ Unit (sep_contract_logic_variables c) :=
    match c with
    | MkSepContract _ _ Σ δ req result ens =>
        smut_produce req ;;
        smut_exec s      >>= fun Σ1 ζ1 t =>
        smut_sub (sub_snoc ζ1 (result,τ) t) (smut_consume ens) ;;
        (* smut_leakcheck *)
        smut_block
    end.

  Definition smut_contract_outcome {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) :
    SPath Unit ε :=
    let δ    := sep_contract_localstore c in
    spath_demonic_close
      (spath_map
         (fun _ _ _ => tt)
         (smut_contract c s (sub_id _) nil δ nil)).

  Definition ValidContractNoEvar {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    VerificationCondition (spath_prune (spath_prune (smut_contract_outcome c body))).

  Section CallerContext.

    Context {Γ : PCtx}.

    Definition smut_consume_chunk_evar {Σe Σr} (c : Chunk Σe) (L : EvarEnv Σe Σr) : SMut Γ Γ (EvarEnv Σe) Σr.
      refine (smut_get_heap >>= fun Σ1 ζ1 h1 => _).
      refine (let L1 := subst ζ1 L in _).
      apply (smut_angelic_listk
        "smut_consume_chunk_evar"
        "Empty extraction"
        {| evarerror_env := L1;
           evarerror_data := c;
        |}
        (extract_chunk c h1 L1)).
      intros [L2 h2].
      refine (smut_put_heap h2;; smut_pure L2).
    Defined.

    (* This function tries to assert the equality between the terms `te` from
       a callee context and `tr` from the caller context. The callee context
       variables are all evars and if possible, it will fill in evars that are
       strictly necessary for the assertion to be true. *)
    Definition smut_assert_term_eq_evar {Σe Σr σ} (te : Term Σe σ) (tr : Term Σr σ) (L : EvarEnv Σe Σr) : SMut Γ Γ (EvarEnv Σe) Σr :=
      (* Make sure we get the up to date substitution. *)
      smut_pure tt >>= fun Σr1 ζ1 _ =>
      let tr1 := subst (T := fun Σ => Term Σ _) ζ1 tr in
      let L1  := subst ζ1 L in
      (* Try to fully match te against tr1, potentially filling in some evars. *)
      match match_term te tr1 L1 with
      | Some e => smut_pure e
      | None =>
        (* The match failed. See if all evars in te are already known.*)
        match eval_term_evar L1 te with
        | Some te1 =>
          (* All evars are known. So assert the equality between the terms in
             the caller context. *)
          smut_assert_formula (formula_eq te1 tr1);; smut_pure L1
        | None =>
          (* Give up. This is currently missing some corner cases where a
             sub-term of te would already constrain all appearing evars, but
             which can't be fully unified with tr. match_term could be
             augmented to also handle this kind of case. *)
          smut_fail
            "smut_assert_term_eq_evar"
            "Uninstantiated evars variable"
            {| evarerror_env := L;
               evarerror_data := (te,tr)
            |}
        end
      end.

    Equations(noeqns) smut_assert_namedenv_eq_evar {X Σe Σr σs} (te : NamedEnv (X:=X) (Term Σe) σs) (tr : NamedEnv (Term Σr) σs) :
      EvarEnv Σe Σr -> SMut Γ Γ (EvarEnv Σe) Σr :=
      smut_assert_namedenv_eq_evar env_nil env_nil := smut_pure;
      smut_assert_namedenv_eq_evar (env_snoc E1 b1 t1) (env_snoc E2 b2 t2) :=
        fun L => smut_assert_namedenv_eq_evar E1 E2 L >>= fun _ ζ =>
                 smut_assert_term_eq_evar t1 (subst (T := fun Σ => Term Σ _) ζ t2).

    Definition smut_consume_formula_evar {Σe Σr} (fml : Formula Σe) (L : EvarEnv Σe Σr) : SMut Γ Γ (EvarEnv Σe) Σr :=
      match fml with
      | formula_bool b =>
        match eval_term_evar L b with
        | Some b' => smut_assert_term b';; smut_pure L
        | None    => smut_fail
                       "smut_consume_formula_evar"
                       "Uninstantiated evars when consuming formula"
                       {| evarerror_env := L;
                          evarerror_data := fml
                       |}
        end
      | formula_prop ζ P =>
        match evarenv_to_option_sub L with
        | Some ζ' => smut_assert_formula (formula_prop (sub_comp ζ ζ') P);; smut_pure L
        | None   => smut_fail
                      "smut_consume_formula_evar"
                      "Uninstantiated evars when consuming formula"
                      {| evarerror_env := L;
                         evarerror_data := fml
                      |}
        end
      | formula_eq t1 t2 =>
        match eval_term_evar L t1, eval_term_evar L t2 with
        | Some t1', Some t2' => smut_assert_formula (formula_eq t1' t2') ;; smut_pure L
        | Some t1', None     => smut_assert_term_eq_evar t2 t1' L
        | None    , Some t2' => smut_assert_term_eq_evar t1 t2' L
        | _       , _        => smut_fail
                                  "smut_consume_formula_evar"
                                  "Uninstantiated evars when consuming formula"
                                  {| evarerror_env := L;
                                     evarerror_data := fml
                                  |}
        end
      | formula_neq t1 t2 =>
        match eval_term_evar L t1, eval_term_evar L t2 with
        | Some t1', Some t2' => smut_assert_formula (formula_neq t1' t2') ;; smut_pure L
        (* | Some t1', None     => smut_assert_term_neq_evar t2 t1' L *)
        (* | None    , Some t2' => smut_assert_term_neq_evar t1 t2' L *)
        | _       , _        => smut_fail
                                  "smut_consume_formula_evar"
                                  "Uninstantiated evars when consuming formula"
                                  {| evarerror_env := L;
                                     evarerror_data := fml
                                  |}
        end
      end.

    Fixpoint smut_consume_evar {Σe Σr} (asn : Assertion Σe) (L : EvarEnv Σe Σr) : SMut Γ Γ (EvarEnv Σe) Σr :=
      match asn with
      | asn_formula fml => smut_consume_formula_evar fml L
      | asn_chunk c => smut_consume_chunk_evar c L
      | asn_if b a1 a2 =>
        match eval_term_evar L b with
        | Some b' => (smut_assert_term b';; smut_consume_evar a1 L)
                       ⊕
                     (smut_assert_term (term_not b');; smut_consume_evar a2 L)
        | None    => smut_fail
                       "smut_consume_evar"
                       "Uninstantiated evars when consuming assertion"
                       {| evarerror_env := L;
                          evarerror_data := asn
                       |}
        end
      | asn_match_enum E k alts =>
        match eval_term_evar L k with
        | Some k1 =>
          smut_angelic_finite
            (𝑬𝑲 E)
            (fun k2 =>
               smut_assert_formula (formula_eq k1 (term_enum E k2)) ;;
               smut_consume_evar (alts k2) L)
        | None => smut_fail
                    "smut_consume_evar"
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
            Lxl' <- smut_consume_evar alt_inl Lxl ;;
            smut_pure (env_tail Lxl')
          | Some (inr t) =>
            let Lxr := L ► (xr∶τ ↦ Some t) in
            Lxr' <- smut_consume_evar alt_inr Lxr ;;
            smut_pure (env_tail Lxr')
          | None =>
            smut_angelic_binary
              (let Lxl := L ► (xl∶σ ↦ None) in
                smut_consume_evar alt_inl Lxl >>= fun _ ζ Lxl' =>
                  match env_unsnoc Lxl' with
                  | (L' , Some t) =>
                    (* TODO(2.0): This assert should move before the *)
                    (* consumption of the alternative. *)
                    (smut_assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ s) (term_inl t)) ;;
                     smut_pure L')
                  | (_ , None) =>
                    smut_fail
                      "smut_consume_evar"
                      "Uninstantiated evars when consuming assertion"
                      {| evarerror_env := Lxl;
                         evarerror_data := alt_inl
                      |}
                  end)
              (let Lxr := L ► (xr∶τ ↦ None) in
                smut_consume_evar alt_inr Lxr >>= fun _ ζ Lxr' =>
                  match env_unsnoc Lxr' with
                  | (L' , Some t) =>
                    (* TODO(2.0): This assert should move before the *)
                    (* consumption of the alternative. *)
                    (smut_assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) ζ s) (term_inr t)) ;;
                     smut_pure L')
                  | (_ , None) =>
                    smut_fail
                      "smut_consume_evar"
                      "Uninstantiated evars when consuming assertion"
                      {| evarerror_env := Lxr;
                         evarerror_data := alt_inr
                      |}
                  end)
          end
        | _ => smut_fail
                 "smut_consume_evar"
                 "Uninstantiated evars when consuming assertion"
                 {| evarerror_env := L;
                    evarerror_data := asn
                 |}
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        smut_fail "smut_consume_evar" "Not implemented" asn
      | asn_match_pair scr xl xr rhs =>
        match eval_term_evar L scr with
        | Some s =>
          match term_get_pair s with
          | Some (tl, tr) =>
            let Lrhs := L ► (xl∶_ ↦ Some tl) ► (xr∶_ ↦ Some tr) in
            Lrhs' <- smut_consume_evar rhs Lrhs ;;
            smut_pure (env_tail (env_tail Lrhs'))
          | None =>
            smut_fail "smut_consume_evar" "Not implemented" asn
          end
        | None => smut_fail
                    "smut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_tuple s p rhs =>
        smut_fail "smut_consume_evar" "Not implemented" asn
      | asn_match_record R scr p rhs =>
        match eval_term_evar L scr with
        | Some s =>
          match term_get_record s with
          | Some ts  =>
            let ζ__R := record_pattern_match_env p ts in
            let LR := L ►► env_map (fun _ t => Some t) ζ__R in
            LR' <- smut_consume_evar rhs LR ;;
            smut_pure (env_drop _ LR')
          | None =>
            smut_fail "smut_consume_evar" "Not implemented" asn
          end
        | None => smut_fail
                    "smut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        smut_fail  "smut_consume_evar" "Not implemented" asn
      | asn_sep a1 a2 =>
        smut_consume_evar a1 L >>= fun _ _ => smut_consume_evar a2
      | asn_exist ς τ a =>
        (* Dynamically allocate a new evar ς in the EvarEnv. *)
        let Lς := L ► (ς∶τ ↦ None) in
        smut_consume_evar a Lς >>= fun _ _ Lς' =>
        (* Split off the last evar again. *)
        match env_unsnoc Lς' with
        | (L' , Some _) =>
          (* ς has been instantiated during execution. So we just return the
          final EvarEnv with ς stripped off. *)
          smut_pure L'
        | (_  , None)   =>
          (* During execution the evar ς was never instantiated, so fail. *)
          smut_fail
            "smut_consume_evar"
            "Uninstantiated evars when consuming assertion"
            {| evarerror_env := L;
               evarerror_data := asn
            |}
        end
      | asn_debug =>
        smut_debug
          (fun Σ1 ζ01 pc1 δ1 h1 =>
             {| sdebug_asn_pathcondition := pc1;
                sdebug_asn_program_context := Γ;
                sdebug_asn_localstore := δ1;
                sdebug_asn_heap := h1;
             |})
          (smut_pure L)
      end.

  End CallerContext.

  Definition smut_call_evar {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : SMut Γ Γ (fun Σ => Term Σ τ) Σr :=
    match contract with
    | MkSepContract _ _ Σe δ req result ens =>
       smut_consume_evar req (create_evarenv Σe Σr) >>= fun Σr1 ζ1 E1 =>
       smut_assert_namedenv_eq_evar δ (env_map (fun _ => subst (T := fun Σ => Term Σ _) ζ1) ts) E1 >>= fun Σr2 ζ2 E2 =>
       match evarenv_to_option_sub E2 with
       | Some ξ => smut_sub ξ (smut_demonicv result τ (smut_produce ens ;; smut_pure (@term_var _ result _ inctx_zero)))
       | None => smut_fail
                   "smut_call_evar"
                   "Uninstantiated evars after consuming precondition"
                   {| evarerror_env := E2;
                      evarerror_data := (contract,ts)
                   |}
       end
    end.

  Section WithConfig.

    Variable cfg : Config.

    Definition smut_call_evar_debug {Γ Δ τ Σr} (f : 𝑭 Δ τ) (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : SMut Γ Γ (fun Σ => Term Σ τ) Σr :=
      fun Σ1 ζ1 pc1 δ1 h1 =>
        let o := smut_call_evar contract ts ζ1 pc1 δ1 h1 in
        if config_debug_function cfg f
        then spath_debug
               {| sdebug_call_function_parameters    := Δ;
                  sdebug_call_function_result_type   := τ;
                  sdebug_call_function_name          := f;
                  sdebug_call_function_arguments     := subst ζ1 ts;
                  sdebug_call_function_contract      := contract;
                  sdebug_call_pathcondition          := pc1;
                  sdebug_call_program_context        := Γ;
                  sdebug_call_localstore             := δ1;
                  sdebug_call_heap                   := h1;
               |}
               o
        else o.

    Fixpoint smut_exec_evar {Γ τ Σ} (s : Stm Γ τ) {struct s} :
      SMut Γ Γ (fun Σ => Term Σ τ) Σ :=
      match s with
      | stm_lit _ l => smut_pure (term_lit τ l)
      | stm_exp e => smut_eval_exp e
      | stm_let x τ s1 s2 =>
        t1 <- smut_exec_evar s1 ;;
        smut_push_local t1 ;;
        t2 <- smut_exec_evar s2 ;;
        smut_pop_local ;;
        smut_pure t2
      | stm_block δ s =>
        smut_pushs_local (lift δ) ;;
        t <- smut_exec_evar s ;;
        smut_pops_local _ ;;
        smut_pure t
      | stm_assign x s =>
        t <- smut_exec_evar s ;;
        smut_state (fun _ ζ δ h => MkSMutResult tt (δ ⟪ x ↦ subst ζ t ⟫)%env h) ;;
        smut_pure t
      | stm_call f es =>
        ts <- smut_eval_exps es ;;
        match CEnv f with
        | Some c => smut_call_evar_debug f c ts
        | None   => smut_fail "smut_exec_evar" "Function call without contract" (f,ts)
        end
      | stm_call_frame δ s =>
        δr <- smut_get_local ;;
        smut_put_local (lift δ) ;;
        smut_bind_left (smut_exec_evar s) (smut_put_local δr)
      | stm_call_external f es =>
        ts <- smut_eval_exps es ;;
        smut_call_evar (CEnvEx f) ts
      | stm_if e s1 s2 =>
        t__sc <- smut_eval_exp e ;;
        match term_get_lit t__sc with
        | Some b =>
          if b
          then smut_exec_evar s1
          else smut_exec_evar s2
        | None =>
          (smut_assume_formula (formula_bool t__sc) ;; smut_exec_evar s1) ⊗
          (smut_assume_formula (formula_bool (term_not t__sc)) ;; smut_exec_evar s2)
        end
      | stm_seq s1 s2 => smut_exec_evar s1 ;; smut_exec_evar s2
      | stm_assertk e1 _ k =>
        t <- smut_eval_exp e1 ;;
        smut_assume_formula (formula_bool t) ;;
        smut_exec_evar k
      | stm_fail _ _ =>
        smut_block
      | stm_match_list e s1 xh xt s2 =>
        t <- smut_eval_exp e ;;
        (smut_assume_formula
           (formula_eq t (term_lit (ty_list _) nil));;
         smut_exec_evar s1) ⊗
        (smut_demonicv
           (𝑿to𝑺 xh) _ (smut_demonicv (𝑿to𝑺 xt) _
           (smut_assume_formula
              (formula_eq (subst (T := fun Σ => Term Σ _) (sub_comp sub_wk1 sub_wk1) t)
                          (term_binop binop_cons (@term_var _ _ _ (inctx_succ inctx_zero)) (@term_var _ _ _ inctx_zero)));;
            smut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
            smut_push_local (@term_var _ _ _ inctx_zero);;
            t2 <- smut_exec_evar s2 ;;
            smut_pop_local ;;
            smut_pop_local ;;
            smut_pure t2)))
      | stm_match_sum e xinl s1 xinr s2 =>
        t <- smut_eval_exp e ;;
        smut_demonic_match_sum
          (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t
          (fun _ _ tl => smut_pushpop tl (smut_exec s1))
          (fun _ _ tr => smut_pushpop tr (smut_exec s2))
      | stm_match_pair e xl xr s =>
        t__sc <- smut_eval_exp e ;;
        match term_get_pair t__sc with
        | Some (t1,t2) =>
          smut_push_local t1;;
          smut_push_local t2;;
          t <- smut_exec_evar s ;;
          smut_pop_local ;;
          smut_pop_local ;;
          smut_pure t
        | None =>
          smut_demonicv (𝑿to𝑺 xl) _ (smut_demonicv (𝑿to𝑺 xr) _
            (smut_assume_formula
               (formula_eq
                  (subst (T := fun Σ => Term Σ _) (sub_comp sub_wk1 sub_wk1) t__sc)
                  (term_binop binop_pair (@term_var _ (𝑿to𝑺 xl) _ (inctx_succ inctx_zero)) (@term_var _ (𝑿to𝑺 xr) _ inctx_zero)));;
             smut_push_local (@term_var _ _ _ (inctx_succ inctx_zero));;
             smut_push_local (@term_var _ _ _ inctx_zero);;
             t <- smut_exec_evar s ;;
             smut_pop_local ;;
             smut_pop_local ;;
             smut_pure t))
        end
      | stm_match_enum E e alts =>
        t__sc <- smut_eval_exp e ;;
        match term_get_lit t__sc with
        | Some K => smut_exec_evar (alts K)
        | None =>
          smut_demonic_finite
            (𝑬𝑲 E)
            (fun K =>
               smut_assume_formula (formula_eq t__sc (term_enum E K));;
               smut_exec_evar (alts K))
        end
      | stm_match_tuple e p rhs =>
        t <- smut_eval_exp e ;;
        smut_exec_match_tuple t p (smut_exec_evar rhs)
      | stm_match_union U e alt__pat alt__rhs =>
        t <- smut_eval_exp e ;;
        smut_exec_match_union t alt__pat (fun K => smut_exec_evar (alt__rhs K))
      | stm_match_record R e p rhs =>
        t <- smut_eval_exp e ;;
        smut_exec_match_record t p (smut_exec_evar rhs)
      | stm_read_register reg =>
        let x := fresh Σ None in
        smut_consume_chunk_evar (chunk_ptsreg reg (@term_var [(x,_)] x _ inctx_zero)) [None]%arg >>= fun Σ1 _ E1 =>
        match snd (env_unsnoc E1) with
        | Some t => smut_produce_chunk (chunk_ptsreg reg t) ;; smut_pure t
        (* Extracting the points to chunk should never fail here. Because there is exactly one binding
           in the ghost environment and the chunk matching will always instantiate it. *)
        | None => smut_fail "smut_exec_evar" "You have found a unicorn." tt
        end
      | stm_write_register reg e =>
        let x := fresh Σ None in
        tnew <- smut_eval_exp e ;;
        smut_consume_chunk_evar (chunk_ptsreg reg (@term_var _ x _ inctx_zero)) [None]%arg ;;
        smut_produce_chunk (chunk_ptsreg reg tnew) ;;
        smut_pure tnew
      | stm_bind _ _ =>
        smut_fail "smut_exec_evar" "stm_bind not supported" tt
      | stm_debugk k =>
        smut_debug
          (fun Σ1 ζ01 pc1 δ1 h1 =>
             {| sdebug_stm_statement := k;
                sdebug_stm_pathcondition := pc1;
                sdebug_stm_localstore := δ1;
                sdebug_stm_heap := h1;
             |})
          (smut_exec_evar k)
      end.

    Definition smut_contract_evar {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : SMut Δ Δ Unit (sep_contract_logic_variables c) :=
      match c with
      | MkSepContract _ _ Σ δ req result ens =>
          smut_produce req ;;
          smut_exec_evar s      >>= fun Σ1 ζ1 t =>
          smut_consume_evar ens (subst (sub_snoc ζ1 (result,τ) t) (create_evarenv_id _)) ;;
          (* smut_leakcheck *)
          smut_block
      end.

    (* Definition smut_contract_evar {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) : *)
    (*   Stm Δ τ -> SPath Message Unit (sep_contract_logic_variables c) := *)
    (*   match c with *)
    (*   | MkSepContract _ _ Σ δ req result ens => *)
    (*     fun s => *)
    (*       let mut := (smut_produce req ;; *)
    (*                   smut_exec_evar s      >>= fun Σ1 ζ1 t => *)
    (*                   smut_consume_evar ens (subst (sub_snoc ζ1 (result::τ) t) (create_evarenv_id _)) ;; *)
    (*                   smut_pure tt (* smut_leakcheck *))%dmut in *)
    (*       let out := mut Σ (sub_id Σ) nil (symbolicstate_initial δ) in *)
    (*       spath_bind nil out (fun _ _ _ _ => spath_block (A:=Unit)) *)
    (*   end. *)

    Definition smut_contract_evar_outcome {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) :
      SPath Unit ε :=
      let δ    := sep_contract_localstore c in
      spath_demonic_close
        (spath_map
           (fun _ _ _ => tt)
           (smut_contract_evar c s (sub_id _) nil δ nil)).

    Definition ValidContractWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (spath_prune (spath_prune (smut_contract_evar_outcome c body))).

  End WithConfig.

  Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContractWithConfig default_config c body.

  (* Transitional old name. *)
  Definition ValidContractDynMut {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContract c body.

  Definition spath_ok_opaque {AT} `{OccursCheck AT} {Σ} (o : SPath AT Σ) : Prop :=
    is_true (spath_ok o).
  Global Arguments spath_ok_opaque {AT _} Σ o.
  Global Opaque spath_ok_opaque.

  Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    is_true (spath_ok (spath_prune (smut_contract_evar_outcome default_config c body))).

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

End Mutators.
