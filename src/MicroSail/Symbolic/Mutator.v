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
    forall Σ (pc : PathCondition Σ), A Σ.
  Definition Impl (A B : TYPE) : TYPE :=
    fun Σ => A Σ -> B Σ.
  Definition Box (A : TYPE) : TYPE :=
    fun Σ0 => forall Σ1 (ζ01 : Sub Σ0 Σ1), PathCondition Σ1 -> A Σ1.
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
    Notation "⌜ A ⌝" := (fun (_ : LCtx) => A%type) (at level 0, format "⌜ A ⌝") : modal.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%modal)) ..))
        (at level 99, x binder, y binder, right associativity)
      : modal.

  End ModalNotations.
  Import ModalNotations.
  Open Scope modal.

  Definition K {A B} :
    ⊢ □(A -> B) -> (□A -> □B) :=
    fun Σ0 pc0 f a Σ1 ζ01 pc1 =>
      f Σ1 ζ01 pc1 (a Σ1 ζ01 pc1).
  Definition T {A} :
    ⊢ □A -> A :=
    fun Σ0 pc0 a => a Σ0 (sub_id Σ0) pc0.
  Definition four {A} :
    ⊢ □A -> □□A :=
    fun Σ0 pc0 a Σ1 ζ01 pc1 Σ2 ζ12 pc2 =>
      a Σ2 (subst ζ01 ζ12) pc2.
  Global Arguments four : simpl never.

  (* faster version of (four _ sub_wk1) *)
  Definition four_wk1 {A} :
    ⊢ □A -> ∀ b, Snoc (□A) b :=
    fun Σ0 pc0 a b Σ1 ζ01 => a Σ1 (env_tail ζ01).
  Arguments four_wk1 {A Σ0} pc0 a b [Σ1] ζ01 : rename.

  Definition valid_box {A} :
    (⊢ A) -> (⊢ □A) :=
    fun a Σ0 pc0 Σ1 ζ01 pc1 => a Σ1 pc1.

  Definition persistent (A : TYPE) : Type :=
    ⊢ A -> □A.

  Definition PROP : TYPE :=
    fun _ => Prop.

  Notation STerm σ := (fun Σ => Term Σ σ).

  Module LogicalRelation.

    Import Entailment.

    Class LR (A : TYPE) : Type :=
      lr : forall Σ0 (pc0 : PathCondition Σ0) Σ1,
        Sub Σ0 Σ1 -> PathCondition Σ1 -> A Σ0 -> A Σ1 -> Prop.

    Class LRRefl (A : TYPE) `{LR A} : Prop :=
      { lr_refl :
          forall Σ0 (pc0 : PathCondition Σ0) (a : A Σ0),
            lr pc0 (sub_id _) pc0 a a;
      }.
    Global Arguments LRRefl A {_}.

    Global Instance LRPROP : LR PROP :=
      fun Σ0 pc0 Σ1 ζ01 pc1 (P : PROP Σ0) (Q : PROP Σ1) => (P -> Q)%type.
    Global Instance LRReflPROP : LRRefl PROP :=
      {| lr_refl Σ0 pc0 (P : PROP Σ0) (HP : P) := HP;
      |}.

    Global Instance LRFormula : LR Formula :=
      fun Σ0 pc0 Σ1 ζ01 pc1 f0 f1 =>
        forall ι1 : SymInstance Σ1,
          instpc pc1 ι1 ->
          inst (A := Prop) f0 (inst ζ01 ι1) -> inst (A := Prop) f1 ι1.
    Global Instance LRReflFormula : LRRefl Formula.
    Proof.
      constructor. unfold lr, LRFormula.
      intros *. now rewrite inst_sub_id.
    Qed.

    Global Instance LRImpl {A B} `{LR A, LR B} : LR (A -> B) :=
      fun Σ0 pc0 Σ1 ζ01 pc1 f0 f1 =>
           forall a0 a1,
             lr pc0 ζ01 pc1 a0 a1 ->
             lr pc0 ζ01 pc1 (f0 a0) (f1 a1).

    (* Instance LRPair {A B} `{LR A, LR B} : LR (Pair A B) := *)
    (*   fun Σ0 pc0 Σ1 ζ01 pc1 ab1 ab2 => *)
    (*     let (a1, b1) := ab1 in *)
    (*     let (a2, b2) := ab2 in *)
    (*     lr pc0 ζ01 pc1 a1 a2 /\ lr pc0 ζ01 pc1 b1 b2. *)

    Global Instance LRBox {A} `{LR A} : LR (Box A) :=
      fun Σ0 pc0 Σ1 ζ01 pc1 b1 b2 =>
        forall Σ2 (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2),
          entails pc2 (subst pc1 ζ12) ->
          lr pc1 ζ12 pc2 (b1 _ ζ01 pc1) (b2 _ ζ12 pc2).

    Global Instance LRReflBox {A} `{LR A} : LRRefl (Box A).
    Proof.
      constructor. unfold lr, LRBox.
      intros Σ0 pc0 a0 Σ1 ζ01 pc1 Hpc01.
      (* Downwards close is LRRefl for Box right!? *)
    Abort.

    Global Instance LRInstance : LR SymInstance :=
      fun Σ0 pc0 Σ1 ζ01 pc1 ι0 ι1 =>
        (* instpc ι1 pc1 /\ instpc ι0 pc0 /\ *)
        ι0 = inst ζ01 ι1.

    Global Instance LRReflInstance : LRRefl SymInstance.
    Proof.
      constructor. unfold lr, LRInstance.
      intros Σ0 pc0 ι0.
      now rewrite inst_sub_id.
    Qed.

    Definition dcl {A} `{LR A} : ⊢ □A -> PROP :=
      fun Σ0 pc0 a =>
        forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1,
          entails pc1 (subst pc0 ζ01) ->
          lr pc0 ζ01 pc1 a (four pc0 a ζ01 pc1).

    Lemma dcl_four {A} `{LR A} {Σ0} (pc0 : PathCondition Σ0) (a : Box A Σ0) (a_dcl : dcl pc0 a) :
      forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1,
        entails pc1 (subst pc0 ζ01) ->
        dcl pc1 (four pc0 a ζ01 pc1).
    Proof.
      unfold dcl, four, lr, LRBox in *.
      intros Σ1 ζ01 pc1 Hpc01.
      intros Σ2 ζ12 pc2 Hpc12.
      intros Σ3 ζ23 pc3 Hpc23.
      rewrite <- sub_comp_assoc.
      apply a_dcl; auto.
      rewrite subst_sub_comp.
      transitivity (subst pc1 ζ12); auto.
      now apply proper_subst_entails.
    Qed.

    Lemma dcl_four_wk1 {A} `{LR A} {Σ0} (pc0 : PathCondition Σ0) (a : Box A Σ0) (a_dcl : dcl pc0 a) :
      forall (b : 𝑺 * Ty),
        dcl (subst pc0 sub_wk1) (four_wk1 pc0 a b).
    Proof.
      unfold dcl, four_wk1, four, lr, LRBox.
      intros b.
      intros Σ1 ζ01 pc1 Σ2 ζ12 pc2 Hpc23.
      rewrite <- ?sub_comp_wk1_tail.
      rewrite <- sub_comp_assoc.
      apply a_dcl; auto.
      now rewrite subst_sub_comp.
    Qed.

    Lemma dcl_four_cons {A} `{LR A} {Σ} (pc : PathCondition Σ)
      (fml : Formula Σ) (a : Box A Σ) (a_dcl : dcl pc a) :
      dcl (cons fml pc) a.
    Proof.
      intros Σ1 ζ01 pc1 Hpc01. cbn in Hpc01.
      apply entails_cons in Hpc01. destruct Hpc01.
      now apply a_dcl.
    Qed.

    Global Hint Resolve dcl_four : dcl.
    Global Hint Resolve dcl_four_wk1 : dcl.
    Global Hint Resolve dcl_four_cons : dcl.

  End LogicalRelation.

  Section Obligations.

    Inductive Obligation {Σ} (msg : Message Σ) (fml : Formula Σ) (ι : SymInstance Σ) : Prop :=
    | obligation (p : inst fml ι : Prop).

  End Obligations.

  Module Path.

    Inductive SPath (A : TYPE) (Σ : LCtx) : Type :=
    | pure (a: A Σ)
    | angelic_binary (o1 o2 : SPath A Σ)
    | demonic_binary (o1 o2 : SPath A Σ)
    | error (msg : Message Σ)
    | block
    | assertk (P : Formula Σ) (msg : Message Σ) (k : SPath A Σ)
    | assumek (P : Formula Σ) (k : SPath A Σ)
    (* Don't use these two directly. Instead, use the HOAS versions 'angelic' *)
    (* and 'demonic' that will freshen names. *)
    | angelicv b (k : SPath A (Σ ▻ b))
    | demonicv b (k : SPath A (Σ ▻ b))
    | assert_vareq
        x σ (xIn : x::σ ∈ Σ)
        (t : Term (Σ - (x::σ)) σ)
        (msg : Message (Σ - (x::σ)))
        (k : SPath A (Σ - (x::σ)))
    | assume_vareq
        x σ (xIn : (x,σ) ∈ Σ)
        (t : Term (Σ - (x,σ)) σ)
        (k : SPath A (Σ - (x,σ)))
    | debug
        {BT B} {subB : Subst BT}
        {instB : Inst BT B}
        {occB: OccursCheck BT}
        (b : BT Σ) (k : SPath A Σ).

    Global Arguments pure {_ _} _.
    Global Arguments error {_ _} _.
    Global Arguments block {_ _}.
    Global Arguments angelicv {_ _} _ _.
    Global Arguments demonicv {_ _} _ _.
    Global Arguments assert_vareq {_ _} x {_ _} t msg k.
    Global Arguments assume_vareq {_ _} x {_ _} t k.

    (* TODO: KILL
       This doesn't freshen the names in Δ. *)
    Definition angelicvs {A} :
      ⊢ ∀ Δ, Cat (SPath A) Δ -> SPath A :=
      fix angelics {Σ} pc Δ :=
        match Δ with
        | ε     => fun k => k
        | Δ ▻ b => fun k => angelics pc Δ (angelicv b k)
        end.
    Global Arguments angelicvs {A Σ} pc Δ : rename.

    Definition demonic_close {A} :
      forall Σ, SPath A Σ -> SPath A ε :=
      fix close Σ :=
        match Σ with
        | ctx_nil      => fun k => k
        | ctx_snoc Σ b => fun k => close Σ (demonicv b k)
        end.

    Fixpoint assume_multisub {AT Σ1 Σ2} (ζ : MultiSub Σ1 Σ2) : SPath AT Σ2 -> SPath AT Σ1 :=
      match ζ with
      | multisub_id         =>
        fun p => p
      | multisub_cons x t ζ =>
        fun p => assume_vareq x t (assume_multisub ζ p)
      end.

    Fixpoint assert_multisub {AT Σ1 Σ2} (msg : Message Σ1) (ζ : MultiSub Σ1 Σ2) : (Message Σ2 -> SPath AT Σ2) -> SPath AT Σ1 :=
      match ζ with
      | multisub_id         =>
        fun p => p msg
      | multisub_cons x t ζ =>
        let msg' := subst msg (sub_single _ t) in
        fun p => assert_vareq x t msg' (assert_multisub msg' ζ p)
      end.

    Global Instance SubstSPath {A} `{Subst A} : Subst (SPath A) :=
      fix subst_spath {Σ1} p {Σ2} ζ {struct p} :=
        match p with
        | pure a => pure (subst a ζ)
        | angelic_binary p1 p2 => angelic_binary (subst_spath p1 ζ) (subst_spath p2 ζ)
        | demonic_binary p1 p2 => demonic_binary (subst_spath p1 ζ) (subst_spath p2 ζ)
        | error msg => error (subst msg ζ)
        | block => block
        | assertk fml msg p => assertk (subst fml ζ) (subst msg ζ) (subst_spath p ζ)
        | assumek fml p => assumek (subst fml ζ) (subst_spath p ζ)
        | angelicv b k => angelicv b (subst_spath k (sub_up1 ζ))
        | demonicv b k => demonicv b (subst_spath k (sub_up1 ζ))
        | @assert_vareq _ _ x σ xIn t msg p =>
          let ζ' := subst (sub_shift _) ζ in
          assertk
            (formula_eq (env_lookup ζ xIn) (subst t ζ'))
            (subst msg ζ')
            (subst_spath p ζ')
        | @assume_vareq _ _ x σ xIn t p =>
          let ζ' := subst (sub_shift _) ζ in
          assumek
            (formula_eq (env_lookup ζ xIn) (subst t ζ'))
            (subst_spath p ζ')
        | debug d k => debug (subst d ζ) (subst_spath k ζ)
        end.

    Fixpoint occurs_check_spath {A} `{OccursCheck A} {Σ x} (xIn : x ∈ Σ) (o : SPath A Σ) :
      option (SPath A (Σ - x)) :=
      match o with
      | pure a => option_map pure (occurs_check xIn a)
      | angelic_binary o1 o2 =>
        option_ap (option_map (angelic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2)
      | demonic_binary o1 o2 =>
        option_ap (option_map (demonic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2)
      | error msg => option_map error (occurs_check xIn msg)
      | block => Some block
      | assertk P msg o =>
        option_ap (option_ap (option_map (assertk (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check xIn msg)) (occurs_check_spath xIn o)
      | assumek P o => option_ap (option_map (assumek (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check_spath xIn o)
      | angelicv b o => option_map (angelicv b) (occurs_check_spath (inctx_succ xIn) o)
      | demonicv b o => option_map (demonicv b) (occurs_check_spath (inctx_succ xIn) o)
      | @assert_vareq _ _ y σ yIn t msg o =>
        match occurs_check_view yIn xIn with
        | Same _ => None
        | @Diff _ _ _ _ x xIn =>
          option_ap
            (option_ap
               (option_map
                  (fun (t' : Term (Σ - (y :: σ) - x) σ) (msg' : Message (Σ - (y :: σ) - x)) (o' : SPath A (Σ - (y :: σ) - x)) =>
                     let e := swap_remove yIn xIn in
                     assert_vareq
                       y
                       (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e)
                       (eq_rect (Σ - (y :: σ) - x) Message msg' (Σ - x - (y :: σ)) e)
                       (eq_rect (Σ - (y :: σ) - x) (SPath A) o' (Σ - x - (y :: σ)) e))
                  (occurs_check xIn t))
               (occurs_check xIn msg))
            (occurs_check_spath xIn o)
        end
      | @assume_vareq _ _ y σ yIn t o =>
        match occurs_check_view yIn xIn with
        | Same _ => Some o
        | @Diff _ _ _ _ x xIn =>
          option_ap
            (option_map
               (fun (t' : Term (Σ - (y :: σ) - x) σ) (o' : SPath A (Σ - (y :: σ) - x)) =>
                  let e := swap_remove yIn xIn in
                  assume_vareq
                    y
                    (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e)
                    (eq_rect (Σ - (y :: σ) - x) (SPath A) o' (Σ - x - (y :: σ)) e))
               (occurs_check xIn t))
            (occurs_check_spath xIn o)
        end
      | debug b o => option_ap (option_map (debug (Σ := Σ - x)) (occurs_check xIn b)) (occurs_check_spath xIn o)
      end.

    Fixpoint inst_spath {AT A} `{Inst AT A} {Σ} (o : SPath AT Σ) (ι : SymInstance Σ) : Outcome A :=
      match o with
      | pure a               => outcome_pure (inst a ι)
      | angelic_binary o1 o2 => outcome_angelic_binary (inst_spath o1 ι) (inst_spath o2 ι)
      | demonic_binary o1 o2 => outcome_demonic_binary (inst_spath o1 ι) (inst_spath o2 ι)
      | error msg            => outcome_fail msg
      | block                => outcome_block
      | assertk fml msg o    => outcome_assertk
                                  (Obligation msg fml ι)
                                  (inst_spath o ι)
      | assumek fml o        => outcome_assumek (inst fml ι) (inst_spath o ι)
      | angelicv b k         => outcome_angelic (fun v : Lit (snd b) => inst_spath k (env_snoc ι b v))
      | demonicv b k         => outcome_demonic (fun v : Lit (snd b) => inst_spath k (env_snoc ι b v))
      | @assert_vareq _ _ x σ xIn t msg k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assertk
          (env_lookup ι xIn = inst t ι')
          (inst_spath k ι')
      | @assume_vareq _ _ x σ xIn t k =>
        let ι' := env_remove' _ ι xIn in
        outcome_assumek
          (env_lookup ι xIn = inst t ι')
          (inst_spath k ι')
      | debug d k            => outcome_debug (inst d ι) (inst_spath k ι)
      end.

    Definition mapping AT BT : TYPE :=
      □(AT -> BT).
    Definition arrow AT BT : TYPE :=
      □(AT -> SPath BT).

    (* Definition arrow_dcl {ET E AT A BT B} `{Subst ET, Subst BT, Inst ET E, Inst AT A, Inst BT B} {Σ} (f : arrow ET AT BT Σ) : Prop := *)
    (*   forall Σ1 Σ2 ζ1 ζ2 ζ12 a1 a2, *)
    (*     (forall ι1 ι2, ι1 = inst ι2 ζ12 -> inst ι1 a1 = inst ι2 a2) -> *)
    (*     geq (subst ζ12 (f Σ1 ζ1 a1)) (f Σ2 ζ2 a2). *)

    Definition angelic {AT} (x : option 𝑺) σ :
      ⊢ □(STerm σ -> SPath AT) -> SPath AT :=
      fun Σ pc k =>
        let y := fresh Σ x in
        angelicv
          (y :: σ) (k (Σ ▻ (y :: σ)) sub_wk1 (subst pc sub_wk1) (@term_var _ y σ inctx_zero)).
    Global Arguments angelic {_} x σ [Σ] pc k.

    Definition map {A B} :
      ⊢ □(A -> B) -> SPath A -> SPath B :=
      fix map {Σ} pc f p :=
        match p with
        | pure a                 => pure (T pc f a)
        | angelic_binary p1 p2   => angelic_binary (map pc f p1) (map pc f p2)
        | demonic_binary p1 p2   => demonic_binary (map pc f p1) (map pc f p2)
        | error msg              => error msg
        | block                  => block
        | assertk fml msg p      => let pc' := cons fml pc in
                                    (* assertk fml msg (map pc' (four pc f (sub_id _) pc') p) *)
                                    assertk fml msg (map pc' f p)
        | assumek fml p          => let pc' := cons fml pc in
                                    (* assumek fml (map pc' (four pc f (sub_id _) pc') p) *)
                                    assumek fml (map pc' f p)
        | angelicv b p           => let ζ'  := sub_wk1 in
                                    let pc' := subst pc sub_wk1 in
                                    angelicv b (map pc' (four pc f ζ' pc') p)
        | demonicv b p           => let ζ'  := sub_wk1 in
                                    let pc' := subst pc sub_wk1 in
                                    demonicv b (map pc' (four pc f ζ' pc') p)
        | assert_vareq x t msg p => let ζ'  := sub_single _ t in
                                    let pc' := subst pc ζ' in
                                    assert_vareq x t msg (map pc' (four pc f ζ' pc') p)
        | assume_vareq x t p     => let ζ'  := sub_single _ t in
                                    let pc' := subst pc ζ' in
                                    assume_vareq x t (map pc' (four pc f ζ' pc') p)
        | debug d p              => debug d (map pc f p)
        end.

    Definition bind {A B} :
      ⊢ SPath A -> □(A -> SPath B) -> SPath B :=
      fix bind {Σ} pc ma f :=
        match ma with
        | pure a                 => T pc f a
        | angelic_binary p1 p2   => angelic_binary (bind pc p1 f) (bind pc p2 f)
        | demonic_binary p1 p2   => demonic_binary (bind pc p1 f) (bind pc p2 f)
        | error msg              => error msg
        | block                  => block
        | assertk fml msg p      => let pc' := cons fml pc in
                                    (* assertk fml msg (bind pc' p (four pc f (sub_id _) pc')) *)
                                    assertk fml msg (bind pc' p f)
        | assumek fml p          => let pc' := cons fml pc in
                                    (* assumek fml (bind pc' p (four pc f (sub_id _) pc')) *)
                                    assumek fml (bind pc' p f)
        | angelicv b p           => let ζ'  := sub_wk1 in
                                    let pc' := subst pc sub_wk1 in
                                    angelicv b (bind pc' p (four pc f ζ' pc'))
        | demonicv b p           => let ζ'  := sub_wk1 in
                                    let pc' := subst pc sub_wk1 in
                                    demonicv b (bind pc' p (four pc f ζ' pc'))
        | assert_vareq x t msg p => let ζ'  := sub_single _ t in
                                    let pc' := subst pc ζ' in
                                    assert_vareq x t msg (bind pc' p (four pc f ζ' pc'))
        | assume_vareq x t p     => let ζ'  := sub_single _ t in
                                    let pc' := subst pc ζ' in
                                    assume_vareq x t (bind pc' p (four pc f ζ' pc'))
        | debug d p              => debug d (bind pc p f)
        end.

    Definition assume_formulas_without_solver {A} :
      ⊢ List Formula -> □(SPath A) -> SPath A :=
      fun Σ =>
        fix assume pc fmls k :=
          match fmls with
          | nil           => T pc k
          | cons fml fmls =>
            assumek fml (assume (cons fml pc) fmls k)
          end.

    Definition assert_formulas_without_solver {A} :
      ⊢ Message -> List Formula -> □(SPath A) -> SPath A :=
      fun Σ =>
        fix asserts pc msg fmls k :=
        match fmls with
        | nil           => T pc k
        | cons fml fmls =>
          assertk fml msg (asserts (cons fml pc) msg fmls k)
        end.

    Definition assume_formula :
      ⊢ Formula -> SPath Unit :=
      fun Σ0 pc fml =>
        match solver pc fml with
        | Some (existT Σ1 (ζ , fmls)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_multisub ζ
            (assume_formulas_without_solver (subst pc (sub_multi ζ)) fmls (fun _ _ _ => pure tt))
        | None =>
          (* The formula is inconsistent with the path constraints. *)
          block
        end.

    Definition assume_formulak {A} :
      ⊢ Formula -> □(SPath A) -> SPath A :=
      fun Σ0 pc fml k =>
        match solver pc fml with
        | Some (existT Σ1 (ζ , fmls)) =>
          (* Assume variable equalities and the residual constraints *)
          let ζ'  := sub_multi ζ in
          let pc' := subst pc ζ' in
          assume_multisub ζ
            (assume_formulas_without_solver pc' fmls (four pc k ζ' pc'))
        | None =>
          (* The formula is inconsistent with the path constraints. *)
          block
        end.

    Definition assume_formulas :
      ⊢ List Formula -> SPath Unit :=
      fix assume_formulas {Σ0} pc fmls {struct fmls} :=
        match fmls with
        | nil => pure tt
        | cons fml fmls =>
          bind
            pc
            (assume_formulas pc fmls)
            (fun Σ1 ζ01 pc1 _ => assume_formula pc1 (subst fml ζ01))
        end.

    Definition assert_formula :
      ⊢ Message -> Formula -> SPath Unit :=
      fun Σ pc msg fml =>
        match solver pc fml with
        | Some (existT Σ1 (ζ , fmls)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_multisub msg ζ
            (fun msg' => assert_formulas_without_solver (subst pc (sub_multi ζ)) msg' fmls (fun _ _ _ => pure tt))
        | None =>
          (* The formula is inconsistent with the path constraints. *)
          error msg
        end.

    Definition angelic_list {A} :
      ⊢ Message -> List A -> SPath A :=
      fun Σ pc msg =>
        fix rec xs :=
        match xs with
        | nil        => error msg
        | cons x nil => pure x
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition angelic_listk {A B} :
      ⊢ Message -> (A -> SPath B) -> List A -> SPath B :=
      fun Σ pc msg k =>
        fix rec xs :=
        match xs with
        | nil        => error msg
        | cons x nil => k x
        | cons x xs  => angelic_binary (k x) (rec xs)
        end.

    Definition demonic_list {A} :
      ⊢ List A -> SPath A :=
      fun Σ pc =>
        fix rec xs :=
        match xs with
        | nil        => block
        | cons x nil => pure x
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition demonic_listk {A B} :
      ⊢ (A -> SPath B) -> List A -> SPath B :=
      fun Σ pc k =>
        fix rec xs :=
        match xs with
        | nil        => block
        | cons x nil => k x
        | cons x xs  => demonic_binary (k x) (rec xs)
        end.

    Definition angelic_finite {A} F `{finite.Finite F} :
      ⊢ Message -> (⌜F⌝ -> SPath A) -> SPath A :=
      fun Σ pc msg k => angelic_listk pc msg k (finite.enum F).

    Definition demonic_finite {A} F `{finite.Finite F} :
      ⊢ (⌜F⌝ -> SPath A) -> SPath A :=
      fun Σ pc k => demonic_listk pc k (finite.enum F).

    Definition demonic_match_bool_fast {A} :
      ⊢ STerm ty_bool -> □(SPath A) -> □(SPath A) -> □(SPath A) :=
      fun Σ pc t pt pf Σ1 ζ01 pc1 =>
        let t' := subst t ζ01 in
        match term_get_lit t' with
        | Some true => pt Σ1 ζ01 pc1
        | Some false => pf Σ1 ζ01 pc1
        | None =>
          demonic_binary
            (assume_formulak pc1 (formula_bool t')
               (four pc pt ζ01 pc1))
            (assume_formulak pc1 (formula_bool (term_not t'))
               (four pc pt ζ01 pc1))
        end.

    Definition demonic_match_bool_fast_alt {A} :
      ⊢ □(STerm ty_bool) -> □(SPath A) -> □(SPath A) -> □(SPath A) :=
      fun Σ pc t pt pf Σ1 ζ01 pc1 =>
        let t' := t _ ζ01 pc1 in
        match term_get_lit t' with
        | Some true => pt Σ1 ζ01 pc1
        | Some false => pf Σ1 ζ01 pc1
        | None =>
          demonic_binary
            (assume_formulak pc1 (formula_bool t')
               (four pc pt ζ01 pc1))
            (assume_formulak pc1 (formula_bool (term_not t'))
               (four pc pt ζ01 pc1))
        end.

    Definition demonic_match_bool {A} :
      ⊢ STerm ty_bool -> □(SPath A) -> □(SPath A) -> SPath A :=
      fun Σ pc t pt pf =>
        match term_get_lit t with
        | Some true => T pc pt
        | Some false => T pc pf
        | None =>
          demonic_binary
            (assume_formulak pc (formula_bool t) pt)
            (assume_formulak pc (formula_bool (term_not t)) pf)
        end.

    Definition angelic_match_bool {A} :
      ⊢ Message -> STerm ty_bool -> □(SPath A) -> □(SPath A) -> SPath A :=
      fun Σ pc msg t pt pf =>
        match term_get_lit t with
        | Some true => T pc pt
        | Some false => T pc pf
        | None =>
          angelic_binary
            (bind pc
               (assert_formula pc msg (formula_bool t))
               (fun Σ1 ζ01 pc1 _ => pt Σ1 ζ01 pc1))
            (bind pc
               (assert_formula pc msg (formula_bool (term_not t)))
               (fun Σ1 ζ01 pc1 _ => pf Σ1 ζ01 pc1))
        end.

    Definition demonic_match_enum {AT E} :
      ⊢ STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(SPath AT)) -> SPath AT :=
      fun Σ pc t k =>
        match term_get_lit t with
        | Some v => T pc (k v)
        | None => demonic_finite
                    pc (fun v => assume_formulak pc (formula_eq t (term_enum E v)) (k v))
        end.

    Definition wp {AT A} `{Inst AT A} :
      (* ⊢ SPath AT -> ⌜A -> Prop⌝ -> SymInstance -> PROP *)
      forall Σ (pc : PathCondition Σ) (o : SPath AT Σ) (POST : A -> Prop) (ι : SymInstance Σ), Prop :=
      fix wp {Σ} pc o POST ι : Prop :=
      match o return Prop with
      | pure a                            => POST (inst a ι)
      | angelic_binary o1 o2              => (wp pc o1 POST ι) \/ (wp pc o2 POST ι)
      | demonic_binary o1 o2              => (wp pc o1 POST ι) /\ (wp pc o2 POST ι)
      | error msg                         => Error msg
      | block                             => True
      | assertk fml msg o                 => inst fml ι /\ wp (cons fml pc) o POST ι
      | assumek fml o                     => (inst (A := Prop) fml ι -> wp (cons fml pc) o POST ι):Prop
      | angelicv b k                      => exists (v : Lit (snd b)),
                                             wp (subst pc sub_wk1) k POST (env_snoc ι b v)
      | demonicv b k                      => forall (v : Lit (snd b)),
                                             wp (subst pc sub_wk1) k POST (env_snoc ι b v)
      | @assert_vareq _ _ x σ xIn t msg k => let ι' := env_remove' _ ι xIn in
                                             env_lookup ι xIn = inst t ι' /\
                                             wp (subst pc (sub_single xIn t)) k POST ι'
      | @assume_vareq _ _ x σ xIn t k     => let ι' := env_remove' _ ι xIn in
                                             env_lookup ι xIn = inst t ι' ->
                                             wp (subst pc (sub_single xIn t)) k POST ι'
      | debug d k                         => Debug (inst d ι) (wp pc k POST ι)
      end%type.

    Definition wp' {AT A} `{Inst AT A} :
      ⊢ SPath AT -> ⌜A -> Prop⌝ -> SymInstance -> PROP :=
      fun Σ pc o POST ι => outcome_satisfy (inst_spath o ι) POST.

    Lemma wp_wp' {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ)
      (o : SPath AT Σ) (POST : A -> Prop) (ι : SymInstance Σ) :
      wp pc o POST ι <-> wp' pc o POST ι.
    Proof.
      unfold wp'.
      induction o; cbn; auto.
      - specialize (IHo1 pc ι). specialize (IHo2 pc ι). intuition.
      - specialize (IHo1 pc ι). specialize (IHo2 pc ι). intuition.
      - split; intros [].
      - specialize (IHo (cons P pc) ι). intuition.
        constructor; auto.
      - specialize (IHo (cons P pc) ι). intuition.
      - split; intros [v HYP]; exists v;
          specialize (IHo (subst pc sub_wk1) (env_snoc ι b v)); intuition.
      - split; intros HYP v; specialize (HYP v);
          specialize (IHo (subst pc sub_wk1) (env_snoc ι b v)); intuition.
      - specialize (IHo (subst pc (sub_single xIn t))
                        (env_remove' (x :: σ) ι xIn)).
        intuition.
      - specialize (IHo (subst pc (sub_single xIn t))
                        (env_remove' (x :: σ) ι xIn)).
        intuition.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Lemma wp_monotonic {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ)
      (o : SPath AT Σ) (P Q : A -> Prop) (PQ : forall a, P a -> Q a)
      (ι : SymInstance Σ) :
      wp pc o P ι ->
      wp pc o Q ι.
    Proof.
      intros HP. rewrite wp_wp' in *.
      unfold wp' in *. revert HP.
      now apply outcome_satisfy_monotonic.
    Qed.

    Global Instance proper_wp {AT A} `{Inst AT A} {Σ} (pc : PathCondition Σ) (o : SPath AT Σ) :
      Proper
        (pointwise_relation A iff ==> eq ==> iff)
        (wp pc o).
    Proof.
      unfold Proper, respectful, pointwise_relation, Basics.impl.
      intros P Q PQ ι1 ι2 ->; split; apply wp_monotonic; intuition.
    Qed.

    Notation instpc ι pc := (@inst _ _ instantiate_pathcondition _ ι pc).

    Definition mapping_dcl {AT A BT B} `{Inst AT A, Inst BT B} :
      ⊢ mapping AT BT -> PROP :=
      fun Σ0 pc0 f =>
        forall Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1)
               Σ2 (ζ02 : Sub Σ0 Σ2) (pc2 : PathCondition Σ2)
               (ζ12 : Sub Σ1 Σ2) (a1 : AT Σ1) (a2 : AT Σ2) ,
        forall ι1 ι2,
          ι1 = inst ζ12 ι2 ->
          inst ζ01 ι1 = inst ζ02 ι2 ->
          inst a1 ι1 = inst a2 ι2 ->
          inst (f Σ1 ζ01 pc1 a1) ι1 = inst (f Σ2 ζ02 pc2 a2) ι2.

    Lemma mapping_dcl_four {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} (pc0 : PathCondition Σ0)
      (f : mapping AT BT Σ0) (f_dcl : mapping_dcl pc0 f) :
      forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1,
        mapping_dcl pc1 (four pc0 f ζ01 pc1).
    Proof.
      unfold mapping_dcl. intros * Hι Hζ Ha.
      eapply f_dcl; eauto. rewrite ?inst_subst.
      intuition.
    Qed.

    Lemma mapping_dcl_four_wk1 {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} pc0 (b : 𝑺 * Ty)
      (f : mapping AT BT Σ0) (f_dcl : mapping_dcl pc0 f) :
      mapping_dcl (subst pc0 sub_wk1) (four_wk1 pc0 f b).
    Proof.
      unfold mapping_dcl. intros * Hι Hζ Ha.
      unfold four_wk1. rewrite <- ?sub_comp_wk1_tail.
      eapply f_dcl; eauto. rewrite ?inst_subst.
      intuition.
    Qed.

    Definition dcl {AT A} `{Inst AT A} :
      ⊢ □(SPath AT) -> PROP :=
      fun Σ0 pc0 p =>
        forall
          (P Q : A -> Prop) (PQ : forall a, P a -> Q a)
          Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1)
          Σ2 (ζ02 : Sub Σ0 Σ2) (pc2 : PathCondition Σ2)
          (ζ12 : Sub Σ1 Σ2),
        forall ι1 ι2,
          ι1 = inst ζ12 ι2 ->
          instpc pc1 ι1 ->
          instpc pc2 ι2 ->
          inst ζ01 ι1 = inst ζ02 ι2 ->
          wp pc1 (p Σ1 ζ01 pc1) P ι1 ->
          wp pc2 (p Σ2 ζ02 pc2) Q ι2.

    Definition arrow_dcl {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} (pc0 : PathCondition Σ0) (f : arrow AT BT Σ0) : Prop :=
      forall
        (P Q : B -> Prop) (PQ : forall b, P b -> Q b)
        Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1)
        Σ2 (ζ02 : Sub Σ0 Σ2) (pc2 : PathCondition Σ2)
        (ζ12 : Sub Σ1 Σ2) (a1 : AT Σ1) (a2 : AT Σ2),
       forall (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2),
         ι1 = inst ζ12 ι2 ->
         instpc pc1 ι1 ->
         instpc pc2 ι2 ->
         inst ζ01 ι1 = inst ζ02 ι2 ->
         inst a1 ι1 = inst a2 ι2 ->
         wp pc1 (f Σ1 ζ01 pc1 a1) P ι1 ->
         wp pc2 (f Σ2 ζ02 pc2 a2) Q ι2.

    Lemma arrow_dcl_four {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} pc0 (f : arrow AT BT Σ0) (f_dcl : arrow_dcl pc0 f) :
      forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1,
        arrow_dcl pc1 (four pc0 f ζ01 pc1).
    Proof.
      unfold arrow_dcl. intros * PQ * Hι Hpc1 Hpc2 Hζ Ha.
      eapply f_dcl; eauto. rewrite ?inst_subst.
      intuition.
    Qed.

    Lemma arrow_dcl_four_wk1 {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} pc0 (f : arrow AT BT Σ0) (f_dcl : arrow_dcl pc0 f) :
      forall (b : 𝑺 * Ty),
        arrow_dcl (subst pc0 sub_wk1) (four_wk1 pc0 f b).
    Proof.
      unfold arrow_dcl. intros * PQ * Hι Hpc1 Hpc2 Hζ Ha.
      unfold four_wk1. rewrite <- ?sub_comp_wk1_tail.
      eapply f_dcl; eauto. rewrite ?inst_subst.
      intuition.
    Qed.

    Hint Resolve mapping_dcl_four : dcl.
    Hint Resolve mapping_dcl_four_wk1 : dcl.
    Hint Resolve arrow_dcl_four : dcl.
    Hint Resolve arrow_dcl_four_wk1 : dcl.

    Lemma wp_subst {AT A} `{InstLaws AT A} {Σ1 Σ2}
      (pc1 : PathCondition Σ1) (pc2 : PathCondition Σ2) (ζ12 : Sub Σ1 Σ2)
      (o : SPath AT Σ1) (POST : A -> Prop) (ι2 : SymInstance Σ2) :
      wp pc2 (subst o ζ12) POST ι2 <-> wp pc1 o POST (inst ζ12 ι2).
    Proof.
      revert Σ2 pc2 ζ12 ι2.
      induction o; cbn; intros.
      - now rewrite inst_subst.
      - now rewrite IHo1, IHo2.
      - now rewrite IHo1, IHo2.
      - split; intros [].
      - reflexivity.
      - now rewrite IHo, inst_subst.
      - now rewrite IHo, inst_subst.
      - specialize (IHo (subst pc1 sub_wk1)).
        split; intros [v HYP]; exists v; revert HYP;
          now rewrite IHo, inst_sub_up1.
      - specialize (IHo (subst pc1 sub_wk1)).
        split; intros HYP v; specialize (HYP v); revert HYP;
          now rewrite IHo, inst_sub_up1.
      - specialize (IHo (subst pc1 (sub_single xIn t))).
        now rewrite IHo, ?inst_subst, inst_sub_shift, <- inst_lookup.
      - specialize (IHo (subst pc1 (sub_single xIn t))).
        now rewrite IHo, ?inst_subst, inst_sub_shift, <- inst_lookup.
      - split; intros [HYP]; constructor; revert HYP; apply IHo.
    Qed.

    Definition geq {AT A} `{Inst AT A} {Σ} pc (o1 o2 : SPath AT Σ) : Prop :=
      forall (P Q : A -> Prop) (PQ : forall a, P a -> Q a) ι,
        wp pc o1 P ι ->
        wp pc o2 Q ι.

    Global Instance preorder_geq {AT A} `{Inst AT A} {Σ} pc : PreOrder (geq (Σ := Σ) pc).
    Proof.
      constructor.
      - unfold geq; intros o * PQ *.
        now apply wp_monotonic.
      - intros x y z. unfold geq.
        intros Rxy Ryz P Q PQ ι.
        specialize (Rxy P Q PQ ι).
        specialize (Ryz Q Q (fun _ p => p) ι).
        auto.
    Qed.

    Definition safe {AT} :
      (* ⊢ SPath AT -> SymInstance -> PROP := *)
      forall Σ (pc : PathCondition Σ) (o : SPath AT Σ) (ι : SymInstance Σ), Prop :=
      fix safe {Σ} pc o ι :=
        match o with
        | pure a => True
        | angelic_binary o1 o2 => safe pc o1 ι \/ safe pc o2 ι
        | demonic_binary o1 o2 => safe pc o1 ι /\ safe pc o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          Obligation msg fml ι /\ safe (cons fml pc) o ι
        | assumek fml o => (inst fml ι : Prop) -> safe (cons fml pc) o ι
        | angelicv b k => exists v, safe (subst pc sub_wk1) k (env_snoc ι b v)
        | demonicv b k => forall v, safe (subst pc sub_wk1) k (env_snoc ι b v)
        | @assert_vareq _ _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env_remove (x,σ) ι xIn in
          safe (subst pc (sub_single xIn t)) k ι')
        | @assume_vareq _ _ x σ xIn t k =>
          let ι' := env_remove (x,σ) ι xIn in
          env_lookup ι xIn = inst t ι' ->
          safe (subst pc (sub_single xIn t)) k ι'
        | debug d k => Debug (inst d ι) (safe pc k ι)
        end%type.
    Global Arguments safe {_ Σ} pc o ι.

    (* TODO: KILL *)
    Lemma wp_angelicvs {AT A} `{Inst AT A} Σ pc Δ (ma : SPath AT (Σ ▻▻ Δ)) :
      forall POST (ι : SymInstance Σ),
        wp pc (angelicvs pc Δ ma) POST ι <->
        exists ιΔ : SymInstance Δ, wp (subst pc (sub_cat_left Δ)) ma POST (env_cat ι ιΔ).
    Proof.
      intros ι POST.
      induction Δ; cbn.
      - split.
        + intros Hwp. exists env_nil; cbn. (* apply Hwp. *) admit.
        + intros [ιΔ Hwp]. destruct (nilView ιΔ). (* apply Hwp. *) admit.
      - rewrite IHΔ. cbn.
        split; intros [ιΔ Hwp].
        + destruct Hwp as [v Hwp].
          exists (env_snoc ιΔ _ v).
          (* apply Hwp. *)
          admit.
        + destruct (snocView ιΔ) as [ιΔ v].
          exists ιΔ, v.
          (* apply Hwp. *)
          admit.
    Admitted.

    Ltac rewrite_inst :=
      repeat rewrite <- ?sub_comp_wk1_tail, ?inst_subst,
        ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
        ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons.

    Lemma wp_angelic {AT A} `{InstLaws AT A} {Σ0} pc0 {x : option 𝑺} {σ : Ty}
          (k : arrow (STerm σ) AT Σ0) (k_dcl : arrow_dcl pc0 k)
          (POST : A -> Prop) (ι0 : SymInstance Σ0) :
      instpc pc0 ι0 ->
      wp pc0 (angelic x σ pc0 k) POST ι0 <->
      exists v : Lit σ, wp pc0 (k _ (sub_id _) pc0 (lift v)) POST ι0.
    Proof.
      cbn. split; intros [v Hwp]; exists v; revert Hwp.
      - apply k_dcl with (sub_snoc (sub_id Σ0) (fresh Σ0 x :: σ) (term_lit σ v));
          rewrite_inst; auto.
      - apply k_dcl with sub_wk1;
          rewrite_inst; auto.
    Qed.

    Lemma wp_map {AT A BT B} `{InstLaws AT A, Inst BT B} {Σ} pc (ma : SPath AT Σ)
      (f : mapping AT BT Σ) (f_dcl : mapping_dcl pc f) :
      forall POST (ι : SymInstance Σ) (Hpc : instpc pc ι),
        wp pc (map pc f ma) POST ι <->
        wp pc ma (fun a => POST (inst (T pc f (lift a)) ι)) ι.
    Proof.
      intros POST ι Hpc. unfold T.
      induction ma; cbn; auto.
      - unfold T. rewrite f_dcl; rewrite_inst; auto.
      - rewrite IHma1, IHma2; eauto.
      - rewrite IHma1, IHma2; eauto.
      - split; (intros [HP Hwp]; split; [exact HP | ]; revert Hwp);
          rewrite IHma; rewrite_inst; auto;
            apply wp_monotonic; intros a;
              rewrite f_dcl; rewrite_inst; auto; eauto.
      - split; (intros Hwp HP; specialize (Hwp HP); revert Hwp);
          rewrite IHma; rewrite_inst; auto;
            apply wp_monotonic; intros a;
              rewrite f_dcl; rewrite_inst; auto; eauto.
      - split; (intros [v Hwp]; exists v; revert Hwp);
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              match goal with
                |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto
              end;
              eapply f_dcl; rewrite_inst; eauto.
      - split; intros Hwp v; specialize (Hwp v); revert Hwp;
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              match goal with
                |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto
              end;
              eapply f_dcl; rewrite_inst; eauto.
      - split; (intros [Heq Hwp]; split; auto; revert Hwp);
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              match goal with
                |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto
              end;
              eapply f_dcl; rewrite_inst; eauto.
      - split; intros Hwp Heq; specialize (Hwp Heq); revert Hwp;
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              match goal with
                |- POST ?b1 -> POST ?b2 => assert (b1 = b2) as ->; auto
              end;
              eapply f_dcl; rewrite_inst; eauto.
      - split; intros [HYP]; constructor; revert HYP; now apply IHma.
    Qed.

    Lemma wp_bind {AT A BT B} `{InstLaws AT A, Inst BT B} {Σ} (pc : PathCondition Σ) (ma : SPath AT Σ)
      (f : arrow AT BT Σ) (f_dcl : arrow_dcl pc f) :
      forall (POST : B -> Prop) (ι : SymInstance Σ) (Hpc : instpc pc ι),
        wp pc (bind pc ma f) POST ι <->
        wp pc ma (fun a => wp pc (T pc f (lift a)) POST ι) ι.
    Proof.
      intros POST ι Hpc. induction ma; cbn; auto.
      - split; eapply f_dcl with (sub_id _); eauto; rewrite ?inst_sub_id, ?inst_lift; auto.
      - now rewrite IHma1, IHma2.
      - now rewrite IHma1, IHma2.
      - split; (intros [HP Hwp]; split; [exact HP | ]; revert Hwp);
          rewrite IHma; rewrite_inst; auto;
            apply wp_monotonic; intros a;
              eapply f_dcl; rewrite_inst; auto; eauto.
      - split; (intros Hwp HP; specialize (Hwp HP); revert Hwp);
          rewrite IHma; rewrite_inst; auto;
            apply wp_monotonic; intros a;
              eapply f_dcl; rewrite_inst; auto; eauto.
      - split; (intros [v Hwp]; exists v; revert Hwp);
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              eapply f_dcl; rewrite_inst; auto.
      - split; intros Hwp v; specialize (Hwp v); revert Hwp;
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              eapply f_dcl; rewrite_inst; auto; eauto.
      - split; (intros [Heq Hwp]; split; auto; revert Hwp);
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              eapply f_dcl; rewrite_inst; auto; eauto.
      - split; intros Hwp Heq; specialize (Hwp Heq); revert Hwp;
          rewrite IHma; rewrite_inst; auto with dcl;
            apply wp_monotonic; intros a;
              eapply f_dcl; rewrite_inst; auto; eauto.
      - split; intros [HYP]; constructor; revert HYP; now apply IHma.
    Qed.

    Lemma wp_assumek_subst {AT A} `{InstLaws AT A} {Σ pc x σ} (xIn : (x,σ) ∈ Σ) (t : Term (Σ - (x,σ)) σ)
          (k : SPath AT Σ) :
      forall POST ι,
        wp pc (assumek (formula_eq (term_var x) (subst (T := fun Σ => Term Σ _) t (sub_shift xIn))) k) POST ι <->
        wp pc (assume_vareq x t (subst k (sub_single xIn t))) POST ι.
    Proof.
      cbn. intros *. rewrite inst_subst, inst_sub_shift.
      rewrite (wp_subst (formula_eq (term_var x) (subst t (sub_shift xIn)) :: pc)%list).
      split; intros Hwp HYP; specialize (Hwp HYP); revert Hwp; now rewrite inst_sub_single.
    Qed.

    Lemma wp_assume_multisub {AT A} `{InstLaws AT A} {Σ0 Σ1} pc0 (ζ : MultiSub Σ0 Σ1)
      (o : SPath AT Σ1) (P : A -> Prop) (ι0 : SymInstance Σ0) :
      wp pc0 (assume_multisub ζ o) P ι0 <->
      (inst_multisub ζ ι0 -> wp (subst pc0 (sub_multi ζ)) o P (inst (sub_multishift ζ) ι0)).
    Proof.
      induction ζ; cbn in *.
      - rewrite subst_sub_id, inst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        rewrite inst_subst.
        rewrite subst_sub_comp.
        intuition.
    Qed.

    Lemma wp_assert_multisub {AT A} `{InstLaws AT A} {Σ0 Σ1} pc0 (msg : Message _) (ζ : MultiSub Σ0 Σ1)
      (o : Message _ -> SPath AT Σ1) (P : A -> Prop) (ι0 : SymInstance Σ0) :
      wp pc0 (assert_multisub msg ζ o) P ι0 <->
      (inst_multisub ζ ι0 /\ wp (subst pc0 (sub_multi ζ)) (o (subst msg (sub_multi ζ))) P (inst (sub_multishift ζ) ι0)).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id, ?subst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite ?subst_sub_comp.
        rewrite <- inst_sub_shift.
        rewrite ?inst_subst.
        intuition.
    Qed.

    Lemma wp_assume_formulas_without_solver {AT A} `{Inst AT A} {Σ0} pc
      (fmls : List Formula Σ0) (p : Box (SPath AT) Σ0) (POST : A -> Prop) (ι0 : SymInstance Σ0) :
      wp pc (assume_formulas_without_solver pc fmls p) POST ι0 <->
      (instpc fmls ι0 -> wp (rev_append fmls pc) (T (rev_append fmls pc) p) POST ι0).
    Proof.
      revert pc. induction fmls as [|fml fmls]; intros pc; cbn.
      - intuition. apply H0. constructor.
      - rewrite inst_pathcondition_cons.
        rewrite IHfmls. intuition.
    Qed.

    Lemma wp_assert_formulas_without_solver {AT A} `{Inst AT A} {Σ0} pc
      (msg : Message Σ0) (fmls : List Formula Σ0) (k : Box (SPath AT) Σ0) (ι0 : SymInstance Σ0) (POST : A -> Prop) :
      wp pc (assert_formulas_without_solver pc msg fmls k) POST ι0 <->
      (instpc fmls ι0 /\ wp (rev_append fmls pc) (T (rev_append fmls pc) k) POST ι0).
    Proof.
      revert pc. induction fmls as [|fml fmls]; intros pc; cbn.
      - intuition. constructor.
      - rewrite inst_pathcondition_cons.
        rewrite IHfmls. intuition.
    Qed.

    Lemma wp_assume_formula {Σ} (pc : PathCondition Σ) (fml : Formula Σ) :
      forall (P : unit -> Prop) (ι : SymInstance Σ),
        instpc pc ι ->
        wp pc (assume_formula pc fml) P ι <->
        ((inst fml ι : Prop) -> P tt).
    Proof.
      unfold assume_formula. intros P ι Hpc.
      destruct (solver_spec pc fml) as [[Σ1 [ζ fmls]]|].
      - specialize (H ι Hpc). destruct H as [Hζ Hfmls].
        specialize (Hfmls (inst (sub_multishift ζ) ι)).
        rewrite wp_assume_multisub, wp_assume_formulas_without_solver.
        cbn. split.
        + intros HP ?. apply HP; auto.
          rewrite inst_multi in Hfmls; auto.
          apply Hfmls; auto.
        + intros HP ? ?. apply HP. apply Hfmls; auto.
          rewrite inst_multi; auto.
      - specialize (H _ Hpc).
        cbn; intuition.
    Qed.

    Lemma wp_assume_formulak {AT A} `{InstLaws AT A} {Σ} (pc : PathCondition Σ) (fml : Formula Σ)
      (k : Box (SPath AT) Σ) (k_dcl : dcl pc k) (POST : A -> Prop) (ι : SymInstance Σ) (Hpc : instpc pc ι) :
      wp pc (assume_formulak pc fml k) POST ι <->
      (inst (A:=Prop) fml ι -> wp pc (T pc k) POST ι).
    Proof.
      unfold assume_formulak.
      destruct (solver_spec pc fml) as [[Σ1 [ζ fmls]] Hfml|Hfml].
      - specialize (Hfml ι Hpc). destruct Hfml as [Hζ Hfmls].
        specialize (Hfmls (inst (sub_multishift ζ) ι)).
        rewrite wp_assume_multisub, wp_assume_formulas_without_solver.
        split.
        + intros HP Hfml.
          specialize (Hζ Hfml).
          rewrite inst_multi in Hfmls; auto.
          inster Hfmls by reflexivity.
          apply Hfmls in Hfml.
          inster HP by auto. revert HP. unfold T.
          eapply k_dcl; auto.
          rewrite inst_pathcondition_rev_append.
          split; auto.
          now rewrite inst_subst, inst_multi.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_multi.
        + clear Hζ. intros Hwp Hζ Hfml.
          rewrite inst_multi in Hfmls; auto.
          destruct Hfmls as [_ Hfmls]; auto.
          inster Hfmls by auto.
          inster Hwp by auto.
          revert Hwp. unfold T.
          eapply k_dcl; auto. rewrite inst_multi; auto.
          rewrite inst_pathcondition_rev_append.
          rewrite inst_subst, inst_multi; auto.
          now rewrite ?inst_subst, ?inst_sub_id, ?inst_multi.
      - specialize (Hfml ι Hpc). cbn. intuition.
    Qed.

    Lemma wp_assert_formula {Σ} (msg : Message Σ) (fml : Formula Σ) (pc : PathCondition Σ) :
      forall (P : unit -> Prop) (ι : SymInstance Σ),
        instpc pc ι ->
        wp pc (assert_formula pc msg fml) P ι <->
        (inst fml ι /\ P tt).
    Proof.
      unfold assert_formula. intros P ι Hpc.
      destruct (solver_spec pc fml) as [[Σ1 [ζ fmls]]|].
      - specialize (H ι Hpc). destruct H as [Hζ Hfmls].
        specialize (Hfmls (inst (sub_multishift ζ) ι)).
        rewrite wp_assert_multisub, wp_assert_formulas_without_solver.
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

    Ltac fold_inst_term :=
      repeat change (@inst_term ?Σ ?σ ?t ?ι)
      with (@inst (fun Σ => Term Σ σ) (Lit σ) (@instantiate_term σ) Σ t ι) in *.

    Lemma wp_demonic_match_bool {AT A} `{InstLaws AT A} {Σ0} pc0 (t : Term Σ0 ty_bool)
      (pt pf : Box (SPath AT) Σ0) (pt_dcl : dcl pc0 pt) (pf_dcl : dcl pc0 pf)
      (POST : A -> Prop) (ι0 : SymInstance Σ0) (Hpc : instpc pc0 ι0) :
      wp pc0 (demonic_match_bool pc0 t pt pf) POST ι0 <->
      match inst (T := STerm ty_bool) (A := Lit ty_bool) t ι0 with
      | true  => wp pc0 (T pc0 pt) POST ι0
      | false => wp pc0 (T pc0 pf) POST ι0
      end.
    Proof.
      unfold demonic_match_bool.
      destruct (term_get_lit_spec t) as [[] Heq|_]; cbn [wp].
      - specialize (Heq ι0). rewrite Heq. reflexivity.
      - specialize (Heq ι0). rewrite Heq. reflexivity.
      - rewrite ?wp_assume_formulak; auto. cbn. fold_inst_term.
        destruct (inst t ι0); intuition.
    Qed.

    Definition angelic_binary_prune {AT} :
      ⊢ SPath AT -> SPath AT -> SPath AT :=
      fun Σ pc o1 o2 =>
        match o1 , o2 with
        | block   , _       => block
        | _       , block   => block
        | error _ , _       => o2
        | _       , error _ => o1
        | _       , _       => angelic_binary o1 o2
        end.

    Definition demonic_binary_prune {AT} :
      ⊢ SPath AT -> SPath AT -> SPath AT :=
      fun Σ pc o1 o2 =>
        match o1 , o2 with
        | block   , _       => o2
        | _       , block   => o1
        | error s , _       => error s
        | _       , error s => error s
        | _       , _       => demonic_binary o1 o2
        end.

    Definition assertk_prune {AT} :
      ⊢ Formula -> Message -> SPath AT -> SPath AT :=
      fun Σ pc fml msg o =>
        match o with
        | error s => error s
        | _       => assertk fml msg o
        end.

    Definition assumek_prune {AT} :
      ⊢ Formula -> SPath AT -> SPath AT :=
      fun Σ pc fml o =>
        match o with
        | block => block
        | _           => assumek fml o
        end.

    Definition angelicv_prune {AT} (* `{OccursCheck AT} *) b :
      ⊢ Snoc (SPath AT) b -> SPath AT :=
      fun Σ pc o =>
        match o with
        (* This is not good *)
        (* | fail s => fail s *)
        | _           => angelicv b o
        end.

    Definition demonicv_prune {AT} `{OccursCheck AT} b :
      ⊢ Snoc (SPath AT) b -> SPath AT :=
      fun Σ pc o =>
        match @occurs_check_spath AT _ (Σ ▻ b) b inctx_zero o with
        | Some o => o
        | None   => demonicv b o
        end.

    Definition assert_vareq_prune {AT Σ} (pc : PathCondition Σ)
      {x σ} {xIn : (x,σ) ∈ Σ} (t : Term (Σ - (x,σ)) σ)
      (msg : Message (Σ - (x,σ))) (k : SPath AT (Σ - (x,σ))) : SPath AT Σ :=
      match k with
      (* | fail s => fail s *)
      | _          => assert_vareq x t msg k
      end.

    Definition assume_vareq_prune {AT Σ} (pc : PathCondition Σ)
      {x σ} {xIn : (x,σ) ∈ Σ} (t : Term (Σ - (x,σ)) σ) (k : SPath AT (Σ - (x,σ))) : SPath AT Σ :=
      match k with
      | block => block
      | _          => assume_vareq x t k
      end.

    Definition prune {AT} `{OccursCheck AT} :
      ⊢ SPath AT -> SPath AT :=
      fix prune {Σ} pc o :=
        match o with
        | pure a => pure a
        | error msg => error msg
        | block => block
        | angelic_binary o1 o2 =>
          angelic_binary_prune pc (prune pc o1) (prune pc o2)
        | demonic_binary o1 o2 =>
          demonic_binary_prune pc (prune pc o1) (prune pc o2)
        | assertk P msg o =>
          assertk_prune pc P msg (prune pc o)
        | assumek P o =>
          assumek_prune pc P (prune pc o)
        | angelicv b o =>
          let pc' := subst pc (sub_wk1 (b := b)) in
          angelicv_prune pc (prune pc' o)
        | demonicv b o =>
          let pc' := subst pc (sub_wk1 (b := b)) in
          demonicv_prune pc (prune pc' o)
        | assert_vareq x t msg k =>
          let ζ'  := sub_single _ t in
          let pc' := subst pc ζ' in
          assert_vareq_prune pc t msg (prune pc' k)
        | assume_vareq x t k =>
          let ζ'  := sub_single _ t in
          let pc' := subst pc ζ' in
          assume_vareq_prune pc t (prune pc' k)
        | debug d k =>
          debug d (prune pc k)
        end.

    Definition ok {AT} `{OccursCheck AT} :
      ⊢ SPath AT -> ⌜bool⌝ :=
      fun Σ pc o =>
        match prune pc o with
        | block => true
        | _     => false
        end.

    Definition run {AT A} `{OccursCheck AT, Inst AT A} :
      ⊢ SPath AT -> SymInstance -> ⌜option A⌝ :=
      fun Σ pc o ι =>
        match prune pc o with
        | pure a => Some (inst a ι)
        | _      => None
        end.

    Module ModalWP.

      Import LogicalRelation.

      Definition wp {A} :
        (* ⊢ □(A -> SymInstance -> PROP) -> SPath A -> SymInstance -> PROP := *)
        forall Σ,  PathCondition Σ -> (Box (A -> SymInstance -> PROP) Σ) -> SPath A Σ -> SymInstance Σ -> Prop :=
        fix WP {Σ} pc POST o ι :=
          match o with
          | pure a                            => T pc POST a ι
          | angelic_binary o1 o2              => (WP pc POST o1 ι) \/ (WP pc POST o2 ι)
          | demonic_binary o1 o2              => (WP pc POST o1 ι) /\ (WP pc POST o2 ι)
          | error msg                         => Error msg
          | block                             => True
          | assertk fml msg o                 => let pc' := cons fml pc in
                                                 (* inst fml ι /\ WP pc' (four pc POST (sub_id _) pc') o ι *)
                                                 inst fml ι /\ WP pc' POST o ι
          | assumek fml o                     => let pc' := cons fml pc in
                                                 (* (inst fml ι : Prop) -> WP pc' (four pc POST (sub_id _) pc') o ι *)
                                                 (inst fml ι : Prop) -> WP pc' POST o ι
          | angelicv b k                      => let ζ'  := sub_wk1 in
                                                 let pc' := subst pc sub_wk1 in
                                                 exists (v : Lit (snd b)),
                                                 WP pc' (four pc POST ζ' pc') k (env_snoc ι b v)
          | demonicv b k                      => let ζ'  := sub_wk1 in
                                                 let pc' := subst pc sub_wk1 in
                                                 forall (v : Lit (snd b)),
                                                 WP pc' (four pc POST ζ' pc') k (env_snoc ι b v)
          | @assert_vareq _ _ x σ xIn t msg k => let ι'  := env_remove' _ ι xIn in
                                                 let ζ'  := sub_single xIn t in
                                                 let pc' := subst pc ζ' in
                                                 env_lookup ι xIn = inst t ι' /\ WP pc' (four pc POST ζ' pc') k ι'
          | @assume_vareq _ _ x σ xIn t k     => let ι'  := env_remove' _ ι xIn in
                                                 let ζ'  := sub_single xIn t in
                                                 let pc' := subst pc ζ' in
                                                 env_lookup ι xIn = inst t ι' -> WP pc' (four pc POST ζ' pc') k ι'
          | debug d k                         => Debug (inst d ι) (WP pc POST k ι)
          end%type.

      Definition wpbox {A} :
        ⊢ □(A -> SymInstance -> PROP) -> □(SPath A -> SymInstance -> PROP).
      Proof.
        intros Σ0 pc0 POST.
        refine (K pc0 _ (four pc0 POST)).
        intros Σ1 ζ01.
        unfold Box, Impl in *.
        apply (@wp A).
      Defined.

      Definition comp {A B C} :
        ⊢ (B -> C) -> (A -> B) -> (A -> C) :=
        fun Σ0 pc0 => Basics.compose.

      Definition bcomp {A B C} :
        ⊢ □(B -> C) -> □(A -> B) -> □(A -> C) :=
        fun Σ0 pc0 f => K pc0 (K pc0 (valid_box comp pc0) f).

      Definition IPROP : TYPE :=
        SymInstance -> PROP.

      Definition Dijkstra (A : TYPE) : TYPE :=
        □(A -> IPROP) -> IPROP.

      Definition wp' {A} :
        ⊢ SPath A -> Dijkstra A :=
        fun Σ pc o POST => wp pc POST o.

      Global Instance LRSPath {A} `{LR A} : LR (SPath A) :=
        fun Σ0 pc0 Σ1 ζ01 pc1 o0 o1 =>
          forall
            (POST : Box (A -> SymInstance -> PROP) Σ0)
            (POST_dcl : dcl pc0 POST)
            (ι1 : SymInstance Σ1),
            wp pc0 POST o0 (inst ζ01 ι1) ->
            wp pc1 (four pc0 POST ζ01 pc1) o1 ι1.

      Lemma wp_monotonic' {A} {Σ0} (pc0 : PathCondition Σ0) (p : SPath A Σ0)
        (P Q : Box (A -> SymInstance -> PROP) Σ0)
        (PQ : forall Σ1 (ζ01 : Sub Σ0 Σ1) pc1 a ι,
            P Σ1 ζ01 pc1 a ι ->
            Q Σ1 ζ01 pc1 a ι) :
        forall ι0 : SymInstance Σ0,
          wp pc0 P p ι0 ->
          wp pc0 Q p ι0.
      Proof.
        induction p; cbn.
        - apply PQ; auto.
        - intros ι0 [Hwp|Hwp]; [left|right]; revert Hwp.
          + now apply IHp1.
          + now apply IHp2.
        - intros ι0 [Hwp1 Hwp2]; split;
            [ revert Hwp1; now apply IHp1
            | revert Hwp2; now apply IHp2].
        - auto.
        - auto.
        - intros ι0 [Hfml Hwp]. split; auto.
          revert Hwp. apply IHp. auto.
        - intros ι0 Hwp Hfml; specialize (Hwp Hfml). revert Hwp.
          apply IHp. auto.
        - intros ι0 [v Hwp]; exists v; revert Hwp.
          apply IHp. intros ? ?. apply PQ.
        - intros ι0 Hwp v; specialize (Hwp v); revert Hwp.
          apply IHp. intros ? ?. apply PQ.
        - intros ι0 [Hfml Hwp]. split; auto.
          revert Hwp. apply IHp. intros ? ?. apply PQ.
        - intros ι0 Hwp Hfml; specialize (Hwp Hfml). revert Hwp.
          apply IHp. intros ? ?. apply PQ.
        - intros ι0 [Hwp]. constructor. revert Hwp.
          apply IHp, PQ.
      Qed.

      Lemma wp_monotonic {A} {subA : Subst A} {lrA : LR A} (* {lrReflA : LRRefl A} *)
        {Σ0} (pc0 : PathCondition Σ0) (p : SPath A Σ0) :
        forall Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1)
          (Hpc : Entailment.entails pc1 (subst pc0 ζ01))
          (P : Box (A -> SymInstance -> PROP) Σ0)
          (Q : Box (A -> SymInstance -> PROP) Σ1)
            (PQ : lr pc0 ζ01 pc1 P Q)
            (ι0 : SymInstance Σ0)
            (ι1 : SymInstance Σ1)
            (Hι : lr pc0 ζ01 pc1 ι0 ι1),
            wp pc0 P p ι0 ->
            wp pc1 Q (subst p ζ01) ι1.
      Proof.
      Admitted.

      Global Instance LRReflSPath {A} `{LR A} : LRRefl (SPath A).
      Proof.
        constructor.
        unfold lr, LRSPath.
        intros * POST_dcl ι0.
        rewrite inst_sub_id.
        apply wp_monotonic'.
        intros Σ1 ζ01 pc1 a1 ι1.
        unfold four.
        now rewrite sub_comp_id_left.
      Qed.

      Lemma wp_map {A B} {Σ0} (pc0 : PathCondition Σ0) (ma : SPath A Σ0)
        (f : Box (A -> B) Σ0)
        (POST : Box (B -> SymInstance -> PROP) Σ0) (ι : SymInstance Σ0) :
        wp pc0 POST (map pc0 f ma) ι <->
        wp pc0 (bcomp pc0 POST f) ma ι.
      Proof.
        induction ma; cbn.
        - auto.
        - rewrite IHma1, IHma2; auto.
        - rewrite IHma1, IHma2; auto.
        - auto.
        - auto.
        - rewrite IHma; auto.
        - rewrite IHma; auto.
        - setoid_rewrite IHma; auto.
        - setoid_rewrite IHma; auto.
        - rewrite IHma; auto.
        - rewrite IHma; auto.
        - split; intros []; constructor; apply IHma; auto.
      Qed.

      Lemma wp_bind {A B} {Σ0} (pc0 : PathCondition Σ0) (ma : SPath A Σ0)
        (f : Box (A -> SPath B) Σ0)
        (POST : Box (B -> SymInstance -> PROP) Σ0)
        (ι0 : SymInstance Σ0) (Hpc0 : instpc pc0 ι0) :
        wp pc0 POST (bind pc0 ma f) ι0 <->
        wp pc0 (bcomp pc0 (wpbox pc0 POST) f) ma ι0.
      Proof with unfold wpbox, four, bcomp, K, comp, Basics.compose, valid_box;
            apply wp_monotonic'; intros Σ1 ζ01 pc1 a1 ι1;
            apply wp_monotonic'; intros Σ2 ζ02 pc2 b2 ι2;
            now rewrite <- subst_sub_comp.
        induction ma; cbn.
        - unfold T, bcomp, wpbox, K, valid_box, comp, Basics.compose.
          split; apply wp_monotonic'; eauto.
          + intros Σ1 ζ01 pc1 a1 ι1.
            unfold four. now rewrite sub_comp_id_left.
          + intros Σ1 ζ01 pc1 a1 ι1.
            unfold four. now rewrite sub_comp_id_left.
        - rewrite IHma1, IHma2; auto.
        - rewrite IHma1, IHma2; auto.
        - auto.
        - auto.
        - split; intros [Hfml Hwp]; split; auto; revert Hwp;
            rewrite IHma; auto;
              now rewrite ?inst_pathcondition_cons.
        - split; intros Hwp Hfml; specialize (Hwp Hfml); revert Hwp;
            rewrite IHma; auto;
              now rewrite ?inst_pathcondition_cons.
        - rename Σ into Σ0.
          split; intros [v Hwp]; exists v; revert Hwp;
            rewrite IHma; clear IHma; auto;
              rewrite ?inst_subst, ?inst_sub_wk1; auto...
        - split; intros Hwp v; specialize (Hwp v); revert Hwp;
            rewrite IHma; auto;
              rewrite ?inst_subst, ?inst_sub_wk1; auto...
        - split; intros [Hfml Hwp]; split; auto; revert Hwp;
            rewrite IHma; auto;
              rewrite ?inst_subst, ?inst_sub_single; auto...
        - split; intros Hwp Hfml; specialize (Hwp Hfml); revert Hwp;
            rewrite IHma; auto;
              rewrite ?inst_subst, ?inst_sub_single; auto...
        - split; intros []; constructor; apply IHma; auto.
      Qed.

    End ModalWP.

  End Path.

  Import Path.

  Section VerificationConditions.

    Inductive VerificationCondition {AT} (p : SPath AT ctx_nil) : Prop :=
    | vc (P : safe nil p env_nil).

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
      intros Σ1 [a δ h] Σ2 ζ.
      constructor.
      apply (subst a ζ).
      apply (subst δ ζ).
      apply (subst h ζ).
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

    Definition SMut (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
      □(SStore Γ1 -> SHeap -> SPath (SMutResult Γ2 A)).
    Bind Scope smut_scope with SMut.

    Definition smut_mapping AT BT : TYPE :=
      fun Σ0 => forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> BT Σ1.
    Definition smut_arrow Γ1 Γ2 AT BT : TYPE :=
      fun Σ0 => forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> SMut Γ1 Γ2 BT Σ1.

    Definition smut_pure {Γ A} `{Subst A} {Σ} (a : A Σ) : SMut Γ Γ A Σ.
      intros Σ1 ζ1 pc1 δ h.
      apply pure.
      constructor.
      apply (subst a ζ1).
      apply δ.
      apply h.
    Defined.

    Definition smut_bind {Γ1 Γ2 Γ3 A B Σ0} (ma : SMut Γ1 Γ2 A Σ0) (f : smut_arrow Γ2 Γ3 A B Σ0) : SMut Γ1 Γ3 B Σ0 :=
      fun Σ1 ζ01 pc1 δ1 h1 =>
        @bind (SMutResult Γ2 A) (SMutResult Γ3 B) Σ1 pc1
          (ma Σ1 ζ01 pc1 δ1 h1)
          (fun Σ2 ζ12 pc2 '(MkSMutResult a2 δ2 h2) =>
             f Σ2 (subst ζ01 ζ12) a2 Σ2 (sub_id _) pc2 δ2 h2).
    (* Definition smut_join {Γ1 Γ2 Γ3 A Σ} (mm : SMut Γ1 Γ2 (SMut Γ2 Γ3 A) Σ) : *)
    (*   SMut Γ1 Γ3 A Σ := smut_bind mm (fun _ _ m => m). *)

    Definition smut_sub {Γ1 Γ2 A Σ1 Σ2} (ζ1 : Sub Σ1 Σ2) (p : SMut Γ1 Γ2 A Σ1) :
      SMut Γ1 Γ2 A Σ2 := fun Σ3 ζ2 => p _ (subst ζ1 ζ2).
    Global Arguments smut_sub {_ _ _ _ _} ζ1 p.
    Definition smut_strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : SMut Γ1 Γ2 A Σ) (b : B Σ) :
      SMut Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ :=
      smut_bind ma (fun _ ζ a => smut_pure (a, subst b ζ)).
    Definition smut_bind_right {Γ1 Γ2 Γ3 A B Σ} (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ) : SMut Γ1 Γ3 B Σ :=
      smut_bind ma (fun _ ζ _ => smut_sub ζ mb).
    Definition smut_bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} {Σ} (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ) : SMut Γ1 Γ3 A Σ :=
      smut_bind ma (fun _ ζ a => smut_bind_right (smut_sub ζ mb) (smut_pure a)) .
    Definition smut_fmap {Γ1 Γ2 Σ A B} `{Subst A, Subst B}
      (ma : SMut Γ1 Γ2 A Σ) (f : smut_mapping A B Σ) :
      SMut Γ1 Γ2 B Σ :=
      fun Σ1 ζ01 pc1 δ1 h1 =>
        @map (SMutResult Γ2 A) (SMutResult Γ2 B) Σ1 pc1
        (fun Σ2 ζ12 pc2 '(MkSMutResult a2 δ2 h2) => MkSMutResult (f Σ2 (subst ζ01 ζ12) a2) δ2 h2)
        (ma Σ1 ζ01 pc1 δ1 h1).
    Definition smut_fmap2 {Γ1 Γ2 Γ3 Σ A B C} `{Subst A, Subst B, Subst C}
      (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ)
      (f : forall Σ', Sub Σ Σ' -> A Σ' -> B Σ' -> C Σ') :
      SMut Γ1 Γ3 C Σ :=
      smut_bind ma (fun Σ1 ζ01 a1 =>
        smut_fmap (smut_sub ζ01 mb) (fun Σ2 ζ12 =>
          f Σ2 (subst ζ01 ζ12) (subst a1 ζ12))).
    Definition smut_pair {Γ1 Γ2 Γ3 Σ A B} `{Subst A, Subst B}
      (ma : SMut Γ1 Γ2 A Σ) (mb : SMut Γ2 Γ3 B Σ) :
      SMut Γ1 Γ3 (fun Σ => A Σ * B Σ)%type Σ :=
      smut_fmap2 ma mb (fun _ _ => pair).

    Definition smut_error {Γ1 Γ2 A Σ D} (func : string) (msg : string) (data:D) : SMut Γ1 Γ2 A Σ.
      intros Σ1 ζ1 pc1 δ1 h1.
      apply error.
      apply (@MkMessage _ func msg Γ1); assumption.
    Defined.

    Definition smut_block {Γ1 Γ2 A Σ} : SMut Γ1 Γ2 A Σ :=
      fun _ _ _ _ _ => block.

    Definition smut_angelic_binary {Γ1 Γ2 A Σ} (m1 m2 : SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 => angelic_binary (m1 Σ1 ζ1 pc1 δ1 h1) (m2 Σ1 ζ1 pc1 δ1 h1).
    Definition smut_demonic_binary {Γ1 Γ2 A Σ} (m1 m2 : SMut Γ1 Γ2 A Σ) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 => demonic_binary (m1 Σ1 ζ1 pc1 δ1 h1) (m2 Σ1 ζ1 pc1 δ1 h1).
    (* Definition smut_angelic_list {AT} `{Subst AT} {Γ Σ} (msg : Message Σ) (xs : List AT Σ) : SMut Γ Γ AT Σ := *)
    (*   fun Σ1 ζ1 pc1 δ1 h1 => *)
    (*     angelic_listk *)
    (*       pc1 (subst msg ζ1) *)
    (*       (fun x => pure (MkSMutResult x δ1 h1)) *)
    (*       (subst xs ζ1). *)
    Fixpoint smut_angelic_list {AT D} `{Subst AT} {Γ Σ} (func : string) (msg : string) (data:D) (xs : List AT Σ) :
      SMut Γ Γ AT Σ :=
      match xs with
      | nil        => smut_error func msg data
      | cons x nil => smut_pure x
      | cons x xs  => smut_angelic_binary (smut_pure x) (smut_angelic_list func msg data xs)
      end.
    Fixpoint smut_angelic_listk {AT D} {Γ1 Γ2 Σ} (func : string) (msg : string) (data:D) (xs : List AT Σ)
      {BT} (k : AT Σ -> SMut Γ1 Γ2 BT Σ) {struct xs} : SMut Γ1 Γ2 BT Σ :=
      match xs with
      | nil => smut_error func msg data
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
        let ζ1x := sub_snoc (subst ζ1 sub_wk1) (x :: τ) (@term_var _ x' τ inctx_zero) in
        angelicv (x' :: τ) (ma (Σ1 ▻ (x' :: τ)) ζ1x (subst pc1 sub_wk1) (subst δ1 sub_wk1) (subst h1 sub_wk1)).
    Global Arguments smut_angelicv {_ _ _ _} _ _ _.

    Definition smut_demonicv {Γ1 Γ2 A Σ} x τ (ma : SMut Γ1 Γ2 A (Σ ▻ (x :: τ))) : SMut Γ1 Γ2 A Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 =>
        let x'  := fresh Σ1 (Some x) in
        let ζ1x := sub_snoc (subst ζ1 sub_wk1) (x :: τ) (@term_var _ x' τ inctx_zero) in
        demonicv (x' :: τ) (ma (Σ1 ▻ (x' :: τ)) ζ1x (subst pc1 sub_wk1) (subst δ1 sub_wk1) (subst h1 sub_wk1)).
    Global Arguments smut_demonicv {_ _ _ _} _ _ _.

    Definition smut_angelic {AT Γ1 Γ2 Σ0} (x : option 𝑺) σ
      (k : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1) :
      SMut Γ1 Γ2 AT Σ0 :=
      fun Σ1 ζ01 pc1 δ1 h1 =>
        angelic x σ pc1
          (fun Σ2 ζ12 pc2 t2 =>
             k Σ2 (subst ζ01 ζ12) t2
               Σ2 (sub_id Σ2) pc2 (subst δ1 ζ12) (subst h1 ζ12)).
    Global Arguments smut_angelic {_ _ _ _} x σ k.

    Definition smut_demonic_termvar {Γ Σ} (x : option 𝑺) σ : SMut Γ Γ (fun Σ => Term Σ σ) Σ :=
      fun Σ1 ζ1 pc1 δ1 h1 =>
        let y := fresh Σ1 x in
        demonicv (y :: σ)
          (pure
             {|
               smutres_value := @term_var _ y σ inctx_zero;
               smutres_store := subst δ1 sub_wk1;
               smutres_heap := subst h1 sub_wk1;
             |}).
    Global Arguments smut_demonic_termvar {_ _} x σ.

    Definition smut_debug {AT DT D} `{Subst DT, Inst DT D, OccursCheck DT} {Σ0 Γ1 Γ2}
      (d : Box (SStore Γ1 -> SHeap -> DT) Σ0)
      (m : SMut Γ1 Γ2 AT Σ0) : SMut Γ1 Γ2 AT Σ0 :=
      fun Σ1 ζ01 pc1 δ1 h1 => debug (d Σ1 ζ01 pc1 δ1 h1) (m Σ1 ζ01 pc1 δ1 h1).

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
    apply pure.
    constructor.
    apply a.
    apply δ2.
    apply h2.
  Defined.

  Definition smut_get_local {Γ Σ} : SMut Γ Γ (fun Σ => SStore Γ Σ) Σ :=
    smut_state (fun _ _ δ h => MkSMutResult δ δ h).
  Definition smut_put_local {Γ Γ' Σ} (δ' : SStore Γ' Σ) : SMut Γ Γ' Unit Σ :=
    smut_state (fun _ ζ _ h => MkSMutResult tt (subst δ' ζ) h).
  Definition smut_pop_local {Γ x σ Σ} : SMut (Γ ▻ (x , σ)) Γ Unit Σ :=
    smut_state (fun _ _ δ h => MkSMutResult tt (env_tail δ) h).
  Definition smut_pops_local {Γ} Δ {Σ} : SMut (Γ ▻▻ Δ) Γ Unit Σ :=
    smut_state (fun _ _ δ h => MkSMutResult tt (env_drop Δ δ) h).
  Definition smut_push_local {Γ x σ Σ} (t : Term Σ σ) : SMut Γ (Γ ▻ (x , σ)) Unit Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult tt (env_snoc δ (x :: σ) (subst t ζ)) h).
  Definition smut_pushs_local {Γ Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) : SMut Γ (Γ ▻▻ Δ) Unit Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult tt (δ ►► (subst δΔ ζ)) h).
  Definition smut_pushpop {AT} `{Subst AT} {Γ1 Γ2 x σ Σ} (t : Term Σ σ) (d : SMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) :
    SMut Γ1 Γ2 AT Σ :=
    smut_push_local t ;; smut_bind_left d smut_pop_local.
  Definition smut_pushspops {AT} `{Subst AT} {Γ1 Γ2 Δ Σ} (δΔ : NamedEnv (Term Σ) Δ) (d : SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT Σ) :
    SMut Γ1 Γ2 AT Σ :=
    smut_pushs_local δΔ ;; smut_bind_left d (smut_pops_local Δ).
  Definition smut_get_heap {Γ Σ} : SMut Γ Γ SHeap Σ :=
    smut_state (fun _ _ δ h => MkSMutResult h δ h).
  Definition smut_put_heap {Γ Σ} (h : SHeap Σ) : SMut Γ Γ Unit Σ :=
    smut_state (fun _ ζ δ _ => MkSMutResult tt δ (subst h ζ)).
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
       smut_pure (subst δΔ ζ12 ► (x :: σ ↦ t))
   end.

  (* Add the provided formula to the path condition. *)
  Definition smut_assume_formula {Γ Σ} (fml : Formula Σ) : SMut Γ Γ Unit Σ :=
    fun Σ1 ζ1 pc1 δ1 h1 =>
      bind
        pc1
        (assume_formula pc1 (subst fml ζ1))
        (fun Σ2 ζ12 pc2 v => pure (MkSMutResult v (subst δ1 ζ12) (subst h1 ζ12))).
  Definition smut_assume_formulas {Γ Σ} (fmls : list (Formula Σ)) : SMut Γ Γ Unit Σ :=
    fold_right (fun fml => smut_bind_right (smut_assume_formula fml)) (smut_pure tt) fmls.

  Definition smut_assert_formula {Γ Σ} (fml : Formula Σ) : SMut Γ Γ Unit Σ :=
    fun Σ1 ζ1 pc1 δ1 h1 =>
      bind
        pc1
        (assert_formula
           pc1
           {| msg_function        := "smut_assert_formula";
              msg_message         := "Proof obligation";
              msg_program_context := Γ;
              msg_pathcondition   := pc1;
              msg_localstore      := δ1;
              msg_heap            := h1;
           |}
           (subst fml ζ1))
        (fun Σ2 ζ12 pc2 v => pure (MkSMutResult v (subst δ1 ζ12) (subst h1 ζ12))).

  Definition smut_assert_formulas {Γ Σ} (fmls : list (Formula Σ)) : SMut Γ Γ Unit Σ :=
    fold_right (fun fml => smut_bind_right (smut_assert_formula fml)) (smut_pure tt) fmls.
  Definition smut_assert_term {Γ Σ} (t : Term Σ ty_bool) : SMut Γ Γ Unit Σ :=
    smut_assert_formula (formula_bool t).
  Definition smut_produce_chunk {Γ Σ} (c : Chunk Σ) : SMut Γ Γ Unit Σ :=
    smut_state (fun _ ζ δ h => MkSMutResult tt δ (cons (subst c ζ) h)).
  Definition smut_consume_chunk {Γ Σ} (c : Chunk Σ) : SMut Γ Γ Unit Σ :=
     smut_get_heap >>= fun Σ1 ζ1 h1 =>
     smut_angelic_list "smut_consume_chunk" "Empty extraction" c
       (extract_chunk_eqb (subst c ζ1) h1) >>= fun Σ2 ζ2 '(Δpc2 , h2) =>
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
    | _   => smut_error "smut_leakcheck" "Heap leak" h
    end.

  Definition smut_make_message {Γ} (func msg : string) {Σ0} : SMut Γ Γ Message Σ0 :=
    fun Σ1 ζ01 pc1 δ1 h1 =>
      pure
        (MkSMutResult
           {| msg_function        := func;
              msg_message         := msg;
              msg_program_context := Γ;
              msg_localstore      := δ1;
              msg_heap            := h1;
              msg_pathcondition   := pc1
           |} δ1 h1).

  Definition smut_demonic_match_bool {AT} {Γ1 Γ2 Σ0} (t : Term Σ0 ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ0) : SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 pc1 δ1 h1 =>
      demonic_match_bool pc1 (subst t ζ01)
        (fun Σ2 ζ12 pc2 => smut_sub ζ01 dt Σ2 ζ12 pc2 (subst δ1 ζ12) (subst h1 ζ12))
        (fun Σ2 ζ12 pc2 => smut_sub ζ01 df Σ2 ζ12 pc2 (subst δ1 ζ12) (subst h1 ζ12)).

  Definition smut_angelic_match_bool {AT} {Γ1 Γ2 Σ} (t : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 pc1 δ1 h1 =>
      angelic_match_bool pc1
        {| msg_function        := "smut_angelic_match_bool";
           msg_message         := "pattern match assertion";
           msg_program_context := Γ1;
           msg_localstore      := δ1;
           msg_heap            := h1;
           msg_pathcondition   := pc1
        |}
        (subst t ζ01)
        (fun Σ2 ζ12 pc2 => smut_sub ζ01 dt Σ2 ζ12 pc2 (subst δ1 ζ12) (subst h1 ζ12))
        (fun Σ2 ζ12 pc2 => smut_sub ζ01 df Σ2 ζ12 pc2 (subst δ1 ζ12) (subst h1 ζ12)).

  Definition smut_demonic_match_enum {AT E} {Γ1 Γ2 Σ} (t : Term Σ (ty_enum E))
    (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) t ζ01 in
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
         (formula_eq (subst (T := fun Σ => Term Σ _) t ζ12) (term_inl tσ)) ;;
          dinl _ ζ12 tσ)
      (smut_demonic_termvar (Some y) τ >>= fun _ ζ12 tτ =>
       smut_assume_formula
         (formula_eq (subst (T := fun Σ => Term Σ _) t ζ12) (term_inr tτ)) ;;
          dinr _ ζ12 tτ).

  Definition smut_mapping_four {AT BT Σ0} (f : smut_mapping AT BT Σ0) {Σ1} (ζ01 : Sub Σ0 Σ1) :
    smut_mapping AT BT Σ1 :=
    fun Σ2 ζ12 => f Σ2 (subst ζ01 ζ12).

  Definition smut_arrow_four {AT BT Γ1 Γ2 Σ0} (f : smut_arrow Γ1 Γ2 AT BT Σ0) {Σ1} (ζ01 : Sub Σ0 Σ1) :
    smut_arrow Γ1 Γ2 AT BT Σ1 :=
    fun Σ2 ζ12 => f Σ2 (subst ζ01 ζ12).

  Definition smut_demonic_match_sum {AT Γ1 Γ2 Σ0} (x y : 𝑺) {σ τ} (t : Term Σ0 (ty_sum σ τ))
    (dinl : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1)
    (dinr : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 τ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) t ζ01 in
      match term_get_sum t' with
      | Some (inl tl) => dinl Σ1 ζ01 tl Σ1 (sub_id _)
      | Some (inr tr) => dinr Σ1 ζ01 tr Σ1 (sub_id _)
      | None => smut_demonic_match_sum' x y t' (smut_arrow_four dinl ζ01) (smut_arrow_four dinr ζ01) (sub_id _)
      end.

  Definition smut_demonic_match_pair {AT} {Γ1 Γ2 Σ} (x y : 𝑺) {σ τ} (s : Term Σ (ty_prod σ τ))
    (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ) ▻ (y :: τ))) : SMut Γ1 Γ2 AT Σ :=
    fun Σ1 ζ01 =>
    match term_get_pair (subst (T := fun Σ => Term Σ _) s ζ01) with
    | Some (tl,tr) => d Σ1 (sub_snoc (sub_snoc ζ01 (x :: σ) tl) (y :: τ) tr)
    | None =>
      smut_demonicv x σ (smut_demonicv y τ
        (smut_assume_formula
           (formula_eq
              (subst (T := fun Σ => Term Σ _) s (subst sub_wk1 sub_wk1))
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
         (subst t ζ01)
         (term_record R (record_pattern_match_env_reverse p ts))) ;;
    d _ ζ01 ts.

  Definition smut_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) t ζ01 in
      match term_get_record t' with
      | Some ts =>
        let tsΔ := record_pattern_match_env p ts in
        d Σ1 ζ01 tsΔ Σ1 (sub_id _)
      | None =>
        smut_demonic_match_record' n t' p (smut_arrow_four d ζ01) (sub_id _)
      end.

  Definition smut_demonic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_tuple σs)) (p : TuplePat σs Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_freshen_ctx n Δ >>= fun _ ζ01 ts =>
    smut_assume_formula
      (formula_eq
         (subst t ζ01)
         (term_tuple (tuple_pattern_match_env_reverse p ts))) ;;
      d _ ζ01 ts.

  Definition smut_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2 Σ0} {Δ : NCtx N Ty}
    (t : Term Σ0 (ty_tuple σs)) (p : TuplePat σs Δ)
    (d : forall Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) Δ -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) t ζ01 in
      match term_get_tuple t' with
      | Some ts =>
        let tsΔ := tuple_pattern_match_env p ts in
        d Σ1 ζ01 tsΔ Σ1 (sub_id _)
      | None => smut_demonic_match_tuple' n t' p (smut_arrow_four d ζ01) (sub_id _)
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
         (subst t ζ01)
         (pattern_match_env_reverse p ts)) ;;
    d _ ζ01 ts.

  Definition smut_demonic_match_union' {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U Σ0} {Δ : 𝑼𝑲 U -> NCtx N Ty}
    (t : Term Σ0 (ty_union U)) (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K))
    (d : forall (K : 𝑼𝑲 U) Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) (Δ K) -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    smut_demonic_finite (𝑼𝑲 U)
      (fun K =>
         smut_demonic_termvar None (𝑼𝑲_Ty K) >>= fun Σ1 ζ01 t__field =>
         smut_assume_formula (formula_eq (term_union U K t__field) (subst t ζ01)) ;;
         smut_demonic_match_pattern n t__field (p K) (smut_arrow_four (d K) ζ01)).

  Definition smut_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U Σ0} {Δ : 𝑼𝑲 U -> NCtx N Ty}
    (t : Term Σ0 (ty_union U)) (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K))
    (d : forall (K : 𝑼𝑲 U) Σ1, Sub Σ0 Σ1 -> NamedEnv (Term Σ1) (Δ K) -> SMut Γ1 Γ2 AT Σ1) :
    SMut Γ1 Γ2 AT Σ0 :=
    fun Σ1 ζ01 =>
      let t' := subst (T := fun Σ => Term Σ _) t ζ01 in
      match term_get_union t' with
      | Some (existT K t__field) =>
        smut_demonic_match_pattern n t__field (p K) (smut_arrow_four (d K) ζ01) (sub_id _)
      | None =>
        smut_demonic_match_union' n t' p (fun K => smut_arrow_four (d K) ζ01) (sub_id _)
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
      smut_error "smut_produce" "Not implemented" asn
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
      smut_error "smut_produce" "Not implemented" asn
    | asn_match_list s alt_nil xh xt alt_cons =>
      smut_error "smut_produce" "Not implemented" asn
    | asn_match_pair s xl xr asn =>
      smut_demonic_match_pair s (smut_producek asn (smut_sub (sub_cat_left (ε ▻ (xl,_) ▻ (xr,_))) k))
    | asn_match_tuple s p asn =>
      smut_demonic_match_tuple id s p
        (fun Σ1 ζ01 ts => smut_sub (env_cat ζ01 ts) (smut_producek asn (smut_sub (sub_cat_left _) k)))
    | asn_match_record R s p asn =>
      smut_demonic_match_record id s p
        (fun Σ1 ζ01 ts => smut_sub (env_cat ζ01 ts) (smut_producek asn (smut_sub (sub_cat_left _) k)))
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      smut_error "smut_produce" "Not implemented" asn
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
      smut_error "smut_consume" "Not implemented" asn
    | asn_match_pair s xl xr rhs =>
      smut_demonic_match_pair s (smut_consume rhs)
    | asn_match_tuple s p rhs =>
      smut_demonic_match_tuple id s p (fun Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_consume rhs))
    | asn_match_record R s p rhs =>
      smut_demonic_match_record id s p (fun Σ1 ζ01 ts => smut_sub (ζ01 ►► ts) (smut_consume rhs))
    | asn_match_union U s alt__ctx alt__pat alt__rhs =>
      smut_error  "smut_consume" "Not implemented" asn
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
      let ζ01' := subst ζ01 ζl ►► sub_cat_right Δ in
      angelicvs pc1 Δ (k (Σ1 ▻▻ Δ) ζ01' (subst pc1 ζl) (subst δ1 ζl) (subst h1 ζl)).

  Definition smut_call {Γ Δ τ Σr} (contract : SepContract Δ τ) (ts : NamedEnv (Term Σr) Δ) : SMut Γ Γ (fun Σ => Term Σ τ) Σr :=
    match contract with
    | MkSepContract _ _ Σe δ req result ens =>
      let ζleft := sub_cat_left Σe in
      let ζright := sub_cat_right Σe in
      smut_angelicvs Σe
        (smut_assert_formulask
           (formula_eqs (subst δ ζright) (subst (T:=fun Σ => NamedEnv (Term Σ) Δ) ts ζleft))
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
           (subst t ζ01)
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
      smut_state (fun _ ζ δ h => MkSMutResult tt (δ ⟪ x ↦ subst t ζ ⟫)%env h) ;;
      smut_pure t
    | stm_call f es =>
      ts <- smut_eval_exps es ;;
      match CEnv f with
      | Some c => smut_call c ts
      | None   => smut_error "smut_exec" "Function call without contract" (f,ts)
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
            (formula_eq (subst t (subst sub_wk1 sub_wk1))
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
           let tnew := subst tnew ζ in
           smut_consume_chunk (chunk_ptsreg reg told) ;;
           smut_produce_chunk (chunk_ptsreg reg tnew) ;;
           smut_pure tnew)
    | stm_bind _ _ =>
      smut_error "smut_exec" "stm_bind not supported" tt
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
    demonic_close
      (map
         nil
         (fun _ _ _ _ => tt)
         (smut_contract c s (sub_id _) nil δ nil)).

  Definition ValidContractNoEvar {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    VerificationCondition (prune nil (prune nil (smut_contract_outcome c body))).

  Section CallerContext.

    Context {Γ : PCtx}.

    Definition smut_consume_chunk_evar {Σe Σr} (c : Chunk Σe) (L : EvarEnv Σe Σr) : SMut Γ Γ (EvarEnv Σe) Σr.
      refine (smut_get_heap >>= fun Σ1 ζ1 h1 => _).
      refine (let L1 := subst L ζ1 in _).
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
      let tr1 := subst (T := fun Σ => Term Σ _) tr ζ1 in
      let L1  := subst L ζ1 in
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
          smut_error
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
                 smut_assert_term_eq_evar t1 (subst (T := fun Σ => Term Σ _) t2 ζ).

    Definition smut_consume_formula_evar {Σe Σr} (fml : Formula Σe) (L : EvarEnv Σe Σr) : SMut Γ Γ (EvarEnv Σe) Σr :=
      match fml with
      | formula_bool b =>
        match eval_term_evar L b with
        | Some b' => smut_assert_term b';; smut_pure L
        | None    => smut_error
                       "smut_consume_formula_evar"
                       "Uninstantiated evars when consuming formula"
                       {| evarerror_env := L;
                          evarerror_data := fml
                       |}
        end
      | formula_prop ζ P =>
        match evarenv_to_option_sub L with
        | Some ζ' => smut_assert_formula (formula_prop (subst ζ ζ') P);; smut_pure L
        | None   => smut_error
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
        | _       , _        => smut_error
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
        | _       , _        => smut_error
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
        | None    => smut_error
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
        | None => smut_error
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
                    (smut_assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) s ζ) (term_inl t)) ;;
                     smut_pure L')
                  | (_ , None) =>
                    smut_error
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
                    (smut_assert_formula (formula_eq (subst (T := fun Σ => Term Σ _) s ζ) (term_inr t)) ;;
                     smut_pure L')
                  | (_ , None) =>
                    smut_error
                      "smut_consume_evar"
                      "Uninstantiated evars when consuming assertion"
                      {| evarerror_env := Lxr;
                         evarerror_data := alt_inr
                      |}
                  end)
          end
        | _ => smut_error
                 "smut_consume_evar"
                 "Uninstantiated evars when consuming assertion"
                 {| evarerror_env := L;
                    evarerror_data := asn
                 |}
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        smut_error "smut_consume_evar" "Not implemented" asn
      | asn_match_pair scr xl xr rhs =>
        match eval_term_evar L scr with
        | Some s =>
          match term_get_pair s with
          | Some (tl, tr) =>
            let Lrhs := L ► (xl∶_ ↦ Some tl) ► (xr∶_ ↦ Some tr) in
            Lrhs' <- smut_consume_evar rhs Lrhs ;;
            smut_pure (env_tail (env_tail Lrhs'))
          | None =>
            smut_error "smut_consume_evar" "Not implemented" asn
          end
        | None => smut_error
                    "smut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_tuple s p rhs =>
        smut_error "smut_consume_evar" "Not implemented" asn
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
            smut_error "smut_consume_evar" "Not implemented" asn
          end
        | None => smut_error
                    "smut_consume_evar"
                    "Uninstantiated evars when consuming assertion"
                    {| evarerror_env := L;
                       evarerror_data := asn
                    |}
        end
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        smut_error  "smut_consume_evar" "Not implemented" asn
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
          smut_error
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
       smut_assert_namedenv_eq_evar δ (subst ts ζ1) E1 >>= fun Σr2 ζ2 E2 =>
       match evarenv_to_option_sub E2 with
       | Some ξ => smut_sub ξ (smut_demonicv result τ (smut_produce ens ;; smut_pure (@term_var _ result _ inctx_zero)))
       | None => smut_error
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
        then debug
               {| sdebug_call_function_parameters    := Δ;
                  sdebug_call_function_result_type   := τ;
                  sdebug_call_function_name          := f;
                  sdebug_call_function_arguments     := subst ts ζ1;
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
        smut_state (fun _ ζ δ h => MkSMutResult tt (δ ⟪ x ↦ subst t ζ ⟫)%env h) ;;
        smut_pure t
      | stm_call f es =>
        ts <- smut_eval_exps es ;;
        match CEnv f with
        | Some c => smut_call_evar_debug f c ts
        | None   => smut_error "smut_exec_evar" "Function call without contract" (f,ts)
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
              (formula_eq (subst (T := fun Σ => Term Σ _) t (subst sub_wk1 sub_wk1))
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
                  (subst (T := fun Σ => Term Σ _) t__sc (subst sub_wk1 sub_wk1))
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
        | None => smut_error "smut_exec_evar" "You have found a unicorn." tt
        end
      | stm_write_register reg e =>
        let x := fresh Σ None in
        tnew <- smut_eval_exp e ;;
        smut_consume_chunk_evar (chunk_ptsreg reg (@term_var _ x _ inctx_zero)) [None]%arg ;;
        smut_produce_chunk (chunk_ptsreg reg tnew) ;;
        smut_pure tnew
      | stm_bind _ _ =>
        smut_error "smut_exec_evar" "stm_bind not supported" tt
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
          smut_consume_evar ens (subst (create_evarenv_id _) (sub_snoc ζ1 (result,τ) t)) ;;
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
    (*       bind nil out (fun _ _ _ _ => block (A:=Unit)) *)
    (*   end. *)

    Definition smut_contract_evar_outcome {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) :
      SPath Unit ε :=
      let δ    := sep_contract_localstore c in
      demonic_close
        (map
           nil
           (fun _ _ _ _ => tt)
           (smut_contract_evar c s (sub_id _) nil δ nil)).

    Definition ValidContractWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (prune nil (prune nil (smut_contract_evar_outcome c body))).

  End WithConfig.

  Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContractWithConfig default_config c body.

  (* Transitional old name. *)
  Definition ValidContractDynMut {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    ValidContract c body.

  Definition ok_opaque {AT} `{OccursCheck AT} {Σ} (o : SPath AT Σ) : Prop :=
    is_true (ok nil o).
  Global Arguments ok_opaque {AT _} Σ o.
  Global Opaque ok_opaque.

  Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    is_true (ok nil (prune nil (smut_contract_evar_outcome default_config c body))).

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
