(******************************************************************************)
(* Copyright (c) 2021 Dominique Devriese, Steven Keuchel                      *)
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
     Classes.RelationClasses
     Lists.List
     NArith.NArith
     Program.Basics
     Relations.Relation_Definitions
     Strings.String.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Base
     Notations
     Prelude
     Bitvector
     Symbolic.Worlds
     Symbolic.UnifLogic
     Syntax.BinOps
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates
     Syntax.Registers.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Obligation Tactic := idtac.

Module Type SymPropOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P).

  Section Messages.

    (* A record to collect information passed to the user. *)
    Record Message (Σ : LCtx) : Type :=
      MkMessage
        { msg_function        : string;
          msg_message         : string;
          msg_program_context : PCtx;
          msg_localstore      : SStore msg_program_context Σ;
          msg_heap            : SHeap Σ;
          msg_pathcondition   : PathCondition Σ;
        }.
    Global Arguments MkMessage {Σ} _ _ _ _ _ _.

    #[export] Instance SubstMessage : Subst Message :=
      fun Σ1 msg Σ2 ζ12 =>
        match msg with
        | MkMessage f m Γ δ h pc => MkMessage f m Γ (subst δ ζ12) (subst h ζ12) (subst pc ζ12)
        end.

    #[export] Instance SubstLawsMessage : SubstLaws Message.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Import option.notations.
    #[export] Instance OccursCheckMessage : OccursCheck Message :=
      fun Σ x xIn msg =>
        match msg with
        | MkMessage f m Γ δ h pc =>
            δ'  <- occurs_check xIn δ;;
            h'  <- occurs_check xIn h;;
            pc' <- occurs_check xIn pc;;
            Some (MkMessage f m Γ δ' h' pc')
        end.

    Inductive Error (Σ : LCtx) (msg : Message Σ) : Prop :=.

  End Messages.

  Inductive Obligation {Σ} (msg : AMessage Σ) (fml : Formula Σ) (ι : Valuation Σ) : Prop :=
  | obligation (p : instprop fml ι : Prop).

  Inductive Debug {B : LCtx -> Type} {Σ : LCtx} (b : B Σ) (P : Prop) : Prop :=
  | debug (p : P).

  #[export] Instance proper_debug {B Σ b} : Proper (iff ==> iff) (@Debug B Σ b).
  Proof. intros P Q PQ. split; intros []; constructor; intuition. Qed.

  Module SymProp.

    Import ModalNotations.

    Inductive SymProp (Σ : LCtx) : Type :=
    | angelic_binary (o1 o2 : SymProp Σ)
    | demonic_binary (o1 o2 : SymProp Σ)
    | error (msg : AMessage Σ)
    | block
    | assertk (fml : Formula Σ) (msg : AMessage Σ) (k : SymProp Σ)
    | assumek (fml : Formula Σ) (k : SymProp Σ)
    (* Don't use these two directly. Instead, use the HOAS versions 'angelic' *)
    (* and 'demonic' that will freshen names. *)
    | angelicv b (k : SymProp (Σ ▻ b))
    | demonicv b (k : SymProp (Σ ▻ b))
    | assert_vareq
        x σ (xIn : x∷σ ∈ Σ)
        (t : Term (Σ - x∷σ) σ)
        (msg : AMessage (Σ - x∷σ))
        (k : SymProp (Σ - x∷σ))
    | assume_vareq
        x σ (xIn : x∷σ ∈ Σ)
        (t : Term (Σ - x∷σ) σ)
        (k : SymProp (Σ - x∷σ))
    | pattern_match {σ} (s : Term Σ σ) (pat : Pattern σ)
        (rhs : forall (pc : PatternCase pat),
            SymProp (Σ ▻▻ PatternCaseCtx pc))
    | pattern_match_var
        x σ (xIn : x∷σ ∈ Σ) (pat : Pattern σ)
        (rhs : forall (pc : PatternCase pat),
            SymProp (ctx.remove (ctx.in_cat_left (PatternCaseCtx pc) xIn)))
    | debug
        (b : AMessage Σ) (k : SymProp Σ).
    Notation 𝕊 := SymProp.

    Global Arguments error {_} _.
    Global Arguments block {_}.
    Global Arguments assertk {_} fml msg k.
    Global Arguments assumek {_} fml k.
    Global Arguments angelicv {_} _ _.
    Global Arguments demonicv {_} _ _.
    Global Arguments assert_vareq {_} x {_ _} t msg k.
    Global Arguments assume_vareq {_} x {_ _} t k.
    Global Arguments pattern_match_var {_} x {σ xIn} _ _.

    Definition angelic_close0 {Σ0 : LCtx} :
      forall Σ, 𝕊 (Σ0 ▻▻ Σ) -> 𝕊 Σ0 :=
      fix close Σ :=
        match Σ with
        | []    => fun p => p
        | Σ ▻ b => fun p => close Σ (angelicv b p)
        end%ctx.

    Definition demonic_close0 {Σ0 : LCtx} :
      forall Σ, 𝕊 (Σ0 ▻▻ Σ) -> 𝕊 Σ0 :=
      fix close Σ :=
        match Σ with
        | []    => fun p => p
        | Σ ▻ b => fun p => close Σ (demonicv b p)
        end%ctx.

    Definition demonic_close :
      forall Σ, 𝕊 Σ -> 𝕊 [] :=
      fix close Σ :=
        match Σ with
        | []    => fun k => k
        | Σ ▻ b => fun k => close Σ (@demonicv Σ b k)
        end%ctx.

    Definition angelic_list' {A Σ} (d : 𝕊 Σ) (P : A Σ -> 𝕊 Σ) :
      List A Σ -> 𝕊 Σ :=
      fix alist xs :=
        match xs with
        | nil       => d
        | cons x xs => angelic_binary (P x) (alist xs)
        end.

    Definition angelic_list {A Σ} (msg : AMessage Σ) (P : A Σ -> 𝕊 Σ) :
      List A Σ -> 𝕊 Σ :=
      fun xs =>
        match xs with
        | nil       => error msg
        | cons x xs => angelic_list' (P x) P xs
        end.

    Definition demonic_list' {A Σ} (d : 𝕊 Σ) (P : A Σ -> 𝕊 Σ) :
      List A Σ -> 𝕊 Σ :=
      fix dlist xs :=
        match xs with
        | nil       => d
        | cons x xs => demonic_binary (P x) (dlist xs)
        end.

    Definition demonic_list {A Σ} (P : A Σ -> 𝕊 Σ) :
      List A Σ -> 𝕊 Σ :=
      fun xs =>
        match xs with
        | nil       => block
        | cons x xs => demonic_list' (P x) P xs
        end.

    Definition angelic_finite F `{finite.Finite F} {Σ} (msg : AMessage Σ)
      (P : F -> 𝕊 Σ) : 𝕊 Σ := angelic_list msg P (finite.enum F).
    #[global] Arguments angelic_finite F {_ _} [Σ] msg P.
    Definition demonic_finite F `{finite.Finite F} {Σ}
      (P : F -> 𝕊 Σ) : 𝕊 Σ := demonic_list P (finite.enum F).
    #[global] Arguments demonic_finite F {_ _} [Σ] P.

    Definition angelic_pattern_match {σ} (pat : @Pattern LVar σ) {Σ} (s : Term Σ σ)
      (k : forall pc : PatternCase pat, 𝕊 (Σ ▻▻ PatternCaseCtx pc)) : 𝕊 Σ :=
      angelic_finite (PatternCase pat) amsg.empty
        (fun pc => angelic_close0 (PatternCaseCtx pc)
           (assertk
              (formula_relop bop.eq
                 (pattern_match_term_reverse pat pc (sub_cat_right _))
                 (subst s (sub_cat_left (PatternCaseCtx pc))))
              amsg.empty (k pc))).

    Definition angelic_pattern_match_var {σ} (pat : @Pattern LVar σ) {Σ} x {xIn : x∷σ ∈ Σ}
      (k : forall pc : PatternCase pat, 𝕊 (ctx.remove (ctx.in_cat_left (PatternCaseCtx pc) xIn))) : 𝕊 Σ :=
      angelic_finite (PatternCase pat) amsg.empty
        (fun pc => angelic_close0 (PatternCaseCtx pc)
           (assert_vareq x
              (pattern_match_term_reverse pat pc (wmatchvar_patternvars pc))
              amsg.empty
              (k pc))).

    Definition demonic_pattern_match {σ} (pat : @Pattern LVar σ) {Σ} (s : Term Σ σ)
      (k : forall pc : PatternCase pat, 𝕊 (Σ ▻▻ PatternCaseCtx pc)) : 𝕊 Σ :=
      demonic_finite (PatternCase pat)
        (fun pc => demonic_close0 (PatternCaseCtx pc)
           (assumek
              (formula_relop bop.eq
                 (pattern_match_term_reverse pat pc (sub_cat_right _))
                 (subst s (sub_cat_left (PatternCaseCtx pc))))
              (k pc))).

    Definition demonic_pattern_match_var {σ} (pat : @Pattern LVar σ) {Σ} x {xIn : x∷σ ∈ Σ}
      (k : forall pc : PatternCase pat, 𝕊 (ctx.remove (ctx.in_cat_left (PatternCaseCtx pc) xIn))) : 𝕊 Σ :=
      demonic_finite (PatternCase pat)
        (fun pc => demonic_close0 (PatternCaseCtx pc)
           (let e := eq_sym (ctx.remove_in_cat_left xIn) in
            assume_vareq x
              (eq_rect _ (STerm σ) (pattern_match_term_reverse pat pc (sub_cat_right (PatternCaseCtx pc))) _ e)
              (k pc))).

    Fixpoint assume_pathcondition_without_solver' {Σ}
      (C : PathCondition Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match C with
      | [ctx] => p
      | C ▻ F => assume_pathcondition_without_solver' C (assumek F p)
      end.

    Fixpoint assert_pathcondition_without_solver' {Σ}
      (msg : AMessage Σ) (C : PathCondition Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match C with
      | [ctx] => p
      | C ▻ F => assert_pathcondition_without_solver' msg C (assertk F msg p)
      end.

    (* These versions just add the world indexing. They simply enforces *)
    (* that p should have been computed in the world with [C] added. *)
    Definition assume_pathcondition_without_solver {w : World}
      (C : PathCondition w) (p : 𝕊 (wpathcondition w C)) : 𝕊 w :=
      assume_pathcondition_without_solver' C p.
    Global Arguments assume_pathcondition_without_solver {_} C p.

    Definition assert_pathcondition_without_solver {w : World} (msg : AMessage w)
      (C : PathCondition w) (p : 𝕊 (wpathcondition w C)) : 𝕊 w :=
      assert_pathcondition_without_solver' msg C p.
    Global Arguments assert_pathcondition_without_solver {_} msg C p.

    Fixpoint assume_triangular {w1 w2} (ξ : Tri w1 w2) : 𝕊 w2 -> 𝕊 w1 :=
      match ξ with
      | tri_id         => fun P => P
      | tri_cons x t ξ => fun P => assume_vareq x t (assume_triangular ξ P)
      end.

    Fixpoint assert_triangular {w1 w2} (msg : AMessage (wctx w1)) (ξ : Tri w1 w2) :
      (AMessage w2 -> 𝕊 w2) -> 𝕊 w1 :=
      match ξ with
      | tri_id         => fun P => P msg
      | tri_cons x t ξ =>
          fun P =>
            let ζ    := sub_single _ t in
            let msg' := subst msg ζ in
            assert_vareq x t msg' (assert_triangular msg' ξ P)
         end.

    Fixpoint safe {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) : Prop :=
      (* ⊢ 𝕊 -> Valuation -> PROP := *)
        match p with
        | angelic_binary o1 o2 => safe o1 ι \/ safe o2 ι
        | demonic_binary o1 o2 => safe o1 ι /\ safe o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          instprop fml ι /\ safe o ι
        | assumek fml o => instprop fml ι -> safe o ι
        | angelicv b k => exists v, safe k (env.snoc ι b v)
        | demonicv b k => forall v, safe k (env.snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' /\
          safe k ι'
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' ->
          safe k ι'
        | pattern_match s pat rhs =>
          let (c,ι__pat) := pattern_match_val pat (inst s ι) in
          safe (rhs c) (ι ►► ι__pat)
        | pattern_match_var x pat rhs =>
          let (c,ι__pat) := pattern_match_val pat ι.[?? x] in
          let ι' := env.remove (x∷_) (ι ►► ι__pat) _ in
          safe (rhs c) ι'
        | debug d k => safe k ι
        end%type.
    Global Arguments safe {Σ} p ι.

    #[export] Instance instprop_symprop : InstProp 𝕊 := fun Σ v ι => SymProp.safe v ι.

    Fixpoint safe_debug {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) : Prop :=
      (* ⊢ 𝕊 -> Valuation -> PROP := *)
        match p with
        | angelic_binary o1 o2 => safe_debug o1 ι \/ safe_debug o2 ι
        | demonic_binary o1 o2 => safe_debug o1 ι /\ safe_debug o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          Obligation msg fml ι /\ safe_debug o ι
        | assumek fml o => instprop fml ι -> safe_debug o ι
        | angelicv b k => exists v, safe_debug k (env.snoc ι b v)
        | demonicv b k => forall v, safe_debug k (env.snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_relop bop.eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env.remove (x∷σ) ι xIn in
          safe_debug k ι')
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' ->
          safe_debug k ι'
        | pattern_match s pat rhs =>
          let (c,ι__pat) := pattern_match_val pat (inst s ι) in
          safe_debug (rhs c) (ι ►► ι__pat)
        | pattern_match_var x pat rhs =>
          let (c,ι__pat) := pattern_match_val pat ι.[?? x] in
          let ι' := env.remove (x∷_) (ι ►► ι__pat) _ in
          safe_debug (rhs c) ι'
        | debug d k => Debug d (safe_debug k ι)
        end%type.
    Global Arguments safe_debug {Σ} p ι.

    (* We use a world indexed version of safe in the soundness proofs, just to make *)
(*        Coq's unifier happy. *)
    Fixpoint wsafe {w : World} (p : 𝕊 w) (ι : Valuation w) : Prop :=
      (* ⊢ 𝕊 -> Valuation -> PROP := *)
        match p with
        | angelic_binary o1 o2 => wsafe o1 ι \/ wsafe o2 ι
        | demonic_binary o1 o2 => wsafe o1 ι /\ wsafe o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          Obligation msg fml ι /\ @wsafe (wformula w fml) o ι
        | assumek fml o => instprop fml ι -> @wsafe (wformula w fml) o ι
        | angelicv b k => exists v, @wsafe (wsnoc w b) k (env.snoc ι b v)
        | demonicv b k => forall v, @wsafe (wsnoc w b) k (env.snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_relop bop.eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env.remove (x∷σ) ι xIn in
          @wsafe (wsubst w x t) k ι')
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' ->
          @wsafe (wsubst w x t) k ι'
        | pattern_match s pat rhs =>
          let (c,ι__pat) := pattern_match_val pat (inst s ι) in
          let w1   : World        := wmatch w s pat c in
          let r1   : w ⊒ w1       := acc_match_right c in
          let ι1   : Valuation w1 := ι ►► ι__pat in
          @wsafe w1 (rhs c) ι1
        | pattern_match_var x pat rhs =>
          let v    : Val _        := ι.[?? x] in
          let (c,ι__pat)            := pattern_match_val pat v in
          let Δ    : LCtx         := PatternCaseCtx c in
          let w1   : World        := wcat w Δ in
          let xIn1 : x∷_ ∈ w1     := ctx.in_cat_left Δ _ in
          let ι1   : Valuation w1 := ι ►► ι__pat in
          let w2   : World        := wsubst w1 x (lift v) in
          let ι2   : Valuation w2 := env.remove (x∷_) ι1 xIn1 in
          @wsafe w2 (rhs c) ι2
        | debug d k => Debug d (wsafe k ι)
        end%type.
    #[global] Arguments wsafe {w} p ι.

    Lemma safe_eq_rect {Σ Σ'} (eq : Σ = Σ') (p : 𝕊 Σ) (ι : Valuation Σ') :
      safe (eq_rect Σ 𝕊 p Σ' eq) ι <-> safe p (eq_rect Σ' (fun Σ => Valuation Σ) ι Σ (eq_sym eq)).
    Proof.
      now destruct eq.
    Qed.

    Lemma obligation_equiv {Σ : LCtx} (msg : AMessage Σ) (fml : Formula Σ) (ι : Valuation Σ) :
      Obligation msg fml ι <-> instprop fml ι.
    Proof. split. now intros []. now constructor. Qed.

    Lemma debug_equiv {B : LCtx -> Type} {Σ} {b : B Σ} {P : Prop} :
      @Debug B _ b P <-> P.
    Proof. split. now intros []. now constructor. Qed.

    Lemma wsafe_safe {w : World} (p : 𝕊 w) (ι : Valuation w) :
      wsafe p ι <-> safe_debug p ι.
    Proof.
      destruct w as [Σ C]; cbn in *. revert C.
      induction p; cbn; intros C.
      - apply or_iff_morphism; auto.
      - apply and_iff_morphism; auto.
      - reflexivity.
      - reflexivity.
      - apply and_iff_morphism; eauto.
      - apply imp_iff_compat_l; eauto.
      - apply ex_iff_morphism; intros v; eauto.
      - apply all_iff_morphism; intros v; eauto.
      - apply and_iff_morphism; eauto.
      - apply imp_iff_compat_l; eauto.
      - destruct pattern_match_val; apply H.
      - destruct pattern_match_val; apply H.
      - rewrite !debug_equiv; auto.
    Qed.

    Lemma safe_debug_safe {Σ : LCtx} (p : 𝕊 Σ) (ι : Valuation Σ) :
      safe_debug p ι <-> safe p ι.
    Proof.
      induction p; cbn; rewrite ?obligation_equiv; try progress cbn.
      - apply or_iff_morphism; auto.
      - apply and_iff_morphism; auto.
      - reflexivity.
      - reflexivity.
      - apply and_iff_morphism; eauto.
      - apply imp_iff_compat_l; eauto.
      - apply ex_iff_morphism; intros v; eauto.
      - apply all_iff_morphism; intros v; eauto.
      - rewrite inst_subst, inst_sub_shift.
        apply and_iff_morphism; eauto.
      - apply imp_iff_compat_l; eauto.
      - destruct pattern_match_val; apply H.
      - destruct pattern_match_val; apply H.
      - rewrite debug_equiv; auto.
    Qed.

    Lemma safe_assume_pathcondition_without_solver {w0 : World}
      (C : PathCondition w0) (p : 𝕊 w0) (ι0 : Valuation w0) :
      wsafe (assume_pathcondition_without_solver C p) ι0 <->
      (instprop C ι0 -> @wsafe (wpathcondition w0 C) p ι0).
    Proof.
      unfold assume_pathcondition_without_solver. revert p.
      induction C; cbn in *; intros p.
      - destruct w0; cbn; split; auto.
      - rewrite IHC. cbn. intuition.
    Qed.

    Lemma safe_assert_pathcondition_without_solver {w0 : World}
      (msg : AMessage w0) (C : PathCondition w0) (p : 𝕊 w0)
      (ι0 : Valuation w0) :
      wsafe (assert_pathcondition_without_solver msg C p) ι0 <->
      (instprop C ι0 /\ @wsafe (wpathcondition w0 C) p ι0).
    Proof.
      unfold assert_pathcondition_without_solver. revert p.
      induction C; cbn in *; intros p.
      - destruct w0; cbn; split.
        + intros HYP. split; auto.
        + intros []; auto.
      - rewrite IHC; cbn.
        split; intros []; auto.
        + destruct H0. destruct H0. auto.
        + destruct H. split; auto. split; auto.
          constructor. auto.
    Qed.

    Lemma safe_assume_triangular {w0 w1} (ζ : Tri w0 w1)
      (o : 𝕊 w1) (ι0 : Valuation w0) :
      wsafe (assume_triangular ζ o) ι0 <->
      (inst_triangular ζ ι0 -> wsafe o (inst (sub_triangular_inv ζ) ι0)).
    Proof.
      induction ζ; cbn in *.
      - rewrite inst_sub_id. intuition.
      - rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        rewrite inst_subst.
        intuition.
    Qed.

    Lemma safe_assert_triangular {w0 w1} msg (ζ : Tri w0 w1)
      (o : AMessage w1 -> 𝕊 w1) (ι0 : Valuation w0) :
      wsafe (assert_triangular msg ζ o) ι0 <->
      (inst_triangular ζ ι0 /\ wsafe (o (subst msg (sub_triangular ζ))) (inst (sub_triangular_inv ζ) ι0)).
    Proof.
      induction ζ.
      - cbn. rewrite inst_sub_id, subst_sub_id. intuition.
      - cbn [wsafe assert_triangular inst_triangular].
        rewrite obligation_equiv. cbn.
        rewrite subst_sub_comp.
        rewrite IHζ. clear IHζ.
        rewrite <- inst_sub_shift.
        rewrite ?inst_subst.
        intuition.
    Qed.

    Lemma safe_angelic_close0 {Σ0 Σ} (p : 𝕊 (Σ0 ▻▻ Σ)) (ι0 : Valuation Σ0) :
      safe (angelic_close0 Σ p) ι0 <-> exists (ι : Valuation Σ), safe p (env.cat ι0 ι).
    Proof.
      induction Σ; cbn.
      - split.
        + intros s.
          now exists env.nil.
        + intros [ι sp].
          destruct (env.view ι).
          now cbn in *.
      - rewrite (IHΣ (angelicv b p)).
        split.
        + intros (ι & v & sp).
          now exists (env.snoc ι b v).
        + intros (ι & sp).
          destruct (env.view ι) as (ι & v).
          now exists ι, v.
    Qed.

    Lemma safe_demonic_close0 {Σ0 Σ} (p : 𝕊 (Σ0 ▻▻ Σ)) (ι0 : Valuation Σ0) :
      safe (demonic_close0 Σ p) ι0 <-> forall (ι : Valuation Σ), safe p (env.cat ι0 ι).
    Proof.
      induction Σ; cbn.
      - split.
        + intros s ι. now destruct (env.view ι).
        + intros s; apply (s env.nil).
      - rewrite (IHΣ (demonicv b p)); cbn.
        split.
        + intros sp ι. destruct (env.view ι) as (ι & v). cbn. auto.
        + intros sp ι v. apply (sp (env.snoc ι b v)).
    Qed.

    Definition safe_demonic_close {Σ : LCtx} (p : 𝕊 Σ) :
      safe (demonic_close p) env.nil <-> forall ι : Valuation Σ, safe p ι.
    Proof.
      induction Σ; cbn [demonic_close] in *.
      - split.
        + intros s ι. now destruct (env.view ι).
        + intros s. apply (s env.nil).
      - rewrite (IHΣ (demonicv b p)); cbn.
        split.
        + intros sp ι. destruct (env.view ι) as (ι & v). auto.
        + intros sp ι v. apply (sp (env.snoc ι b v)).
    Qed.

    Lemma safe_angelic_list' {A Σ} (d : 𝕊 Σ) (P : A Σ -> 𝕊 Σ) (xs : List A Σ) :
      forall ι : Valuation Σ,
        safe (angelic_list' d P xs) ι <->
          safe d ι \/ exists x : A Σ, List.In x xs /\ safe (P x) ι.
    Proof.
      intros ι. induction xs; cbn.
      - split. now left. now intros [|(x & [] & ?)].
      - rewrite IHxs. clear IHxs. split; [intros [H|[H|H]]|intros [H|H]].
        + right. exists a; auto.
        + left. auto.
        + destruct H as (x & HIn & Hsafe). right. exists x. auto.
        + right. left. auto.
        + destruct H as (x & [Heq|HIn] & Hsafe).
          * left. now subst.
          * right. right. exists x. auto.
    Qed.

    Lemma safe_angelic_list {A Σ} (msg : AMessage Σ) (P : A Σ -> 𝕊 Σ) (xs : List A Σ) :
      forall ι : Valuation Σ,
        safe (angelic_list msg P xs) ι <->
          exists x : A Σ, List.In x xs /\ safe (P x) ι.
    Proof.
      intros ι. destruct xs; cbn.
      - split; [easy|]. now intros [].
      - rewrite safe_angelic_list'. split.
        + intros [|(x&?&?)]. exists a; auto. exists x; auto.
        + intros (x & [Heq|HIn] & Hsafe).
          * left. now subst.
          * right. exists x; auto.
    Qed.

    Lemma safe_demonic_list' {A Σ} (d : 𝕊 Σ) (P : A Σ -> 𝕊 Σ) (xs : List A Σ) :
      forall ι : Valuation Σ,
        safe (demonic_list' d P xs) ι <->
          safe d ι /\ forall x : A Σ, List.In x xs -> safe (P x) ι.
    Proof.
      intros ι. induction xs; cbn.
      - intuition.
      - rewrite IHxs. clear IHxs.
        intuition (subst; auto).
    Qed.

    Lemma safe_demonic_list {A Σ} (P : A Σ -> 𝕊 Σ) (xs : List A Σ) :
      forall ι : Valuation Σ,
        safe (demonic_list P xs) ι <->
          forall x : A Σ, List.In x xs -> safe (P x) ι.
    Proof.
      intros ι. destruct xs; cbn.
      - intuition.
      - rewrite safe_demonic_list'.
        intuition (subst; auto).
    Qed.

    Definition sequiv Σ : relation (𝕊 Σ) :=
      fun p q => forall ι, safe p ι <-> safe q ι.
    Arguments sequiv : clear implicits.
    Notation "p <=> q" := (sequiv _ p q) (at level 90, no associativity).

    Definition sequiv_refl {Σ} : Reflexive (sequiv Σ).
    Proof. intros p ι. reflexivity. Qed.

    Definition sequiv_sym {Σ} : Symmetric (sequiv Σ).
    Proof. intros p q pq ι. now symmetry. Qed.

    Definition sequiv_trans {Σ} : Transitive (sequiv Σ).
    Proof. intros p q r pq qr ι. now transitivity (safe q ι). Qed.

    #[export] Instance sequiv_equivalence {Σ} : Equivalence (sequiv Σ).
    Proof. split; auto using sequiv_refl, sequiv_sym, sequiv_trans. Qed.

    Definition simpl Σ : relation (𝕊 Σ) :=
      fun p q => forall ι, safe p ι -> safe q ι.
    Arguments simpl : clear implicits.
    Notation "p =>> q" := (simpl _ p q) (at level 90, no associativity).

    Definition simpl_refl {Σ} : Reflexive (simpl Σ).
    Proof. intros p ι. auto. Qed.

    Definition simpl_trans {Σ} : Transitive (simpl Σ).
    Proof. intros p q r pq qr ι. auto. Qed.

    #[export] Instance simpl_preorder {Σ} : PreOrder (simpl Σ).
    Proof. split; auto using simpl_refl, simpl_trans. Qed.

    #[export] Instance subrelation_sequiv_simpl {Σ} :
      subrelation (sequiv Σ) (simpl Σ).
    Proof. intros x y xy ι. apply xy. Qed.

    #[export] Instance subrelation_sequiv_flip_simpl {Σ} :
      subrelation (sequiv Σ) (Basics.flip (simpl Σ)).
    Proof. intros x y xy ι. apply xy. Qed.

    #[export] Instance proper_safe {Σ} : Proper (sequiv Σ ==> eq ==> Basics.impl) safe.
    Proof.
      unfold Proper, sequiv, respectful, Basics.impl.
      intros p q pq ι ? <-. apply pq.
    Qed.

    #[export] Instance proper_angelic_close0 {Σ Σe} : Proper (sequiv (Σ ▻▻ Σe) ==> sequiv Σ) (angelic_close0 Σe).
    Proof. intros p q pq ι. rewrite ?safe_angelic_close0. now apply ex_iff_morphism. Qed.

    #[export] Instance proper_angelic_binary {Σ} : Proper (sequiv Σ ==> sequiv Σ ==> sequiv Σ) (@angelic_binary Σ).
    Proof.
      unfold sequiv.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      now rewrite p12, q12.
    Qed.

    #[export] Instance proper_angelic_binary_impl {Σ} : Proper (simpl Σ ==> simpl Σ ==> simpl Σ) (@angelic_binary Σ).
    Proof.
      unfold simpl.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      intros []; auto.
    Qed.

    #[export] Instance proper_demonic_close0 {Σ Σu} : Proper (sequiv (Σ ▻▻ Σu) ==> sequiv Σ) (demonic_close0 Σu).
    Proof. intros p q pq ι. rewrite ?safe_demonic_close0. now apply all_iff_morphism. Qed.

    #[export] Instance proper_demonic_close0_impl {Σ Σu} : Proper (simpl (Σ ▻▻ Σu) ==> simpl Σ) (demonic_close0 Σu).
    Proof.
      unfold simpl. intros p q pq ι. rewrite ?safe_demonic_close0.
      intros HYP ιu. apply pq, HYP.
    Qed.

    #[export] Instance proper_demonic_binary {Σ} : Proper (sequiv Σ ==> sequiv Σ ==> sequiv Σ) (@demonic_binary Σ).
    Proof.
      unfold sequiv.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      now rewrite p12, q12.
    Qed.

    #[export] Instance proper_demonic_binary_impl {Σ} : Proper (simpl Σ ==> simpl Σ ==> simpl Σ) (@demonic_binary Σ).
    Proof. unfold simpl. intros p1 p2 p12 q1 q2 q12 ι []. cbn. auto. Qed.

    #[export] Instance proper_assumek {Σ} (fml : Formula Σ) : Proper (sequiv Σ ==> sequiv Σ) (assumek fml).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply imp_iff_compat_l. Qed.

    #[export] Instance proper_assertk {Σ} (fml : Formula Σ) (msg : AMessage Σ) : Proper (sequiv Σ ==> sequiv Σ) (assertk fml msg).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply and_iff_morphism. Qed.

    #[export] Instance proper_assertk_impl {Σ} (fml : Formula Σ) (msg : AMessage Σ) : Proper (simpl Σ ==> simpl Σ) (assertk fml msg).
    Proof. unfold simpl. intros p q pq ι. cbn. intuition auto. Qed.

    #[export] Instance proper_assume_vareq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      Proper (sequiv (Σ - x∷σ) ==> sequiv Σ) (assume_vareq x t).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply imp_iff_compat_l. Qed.

    #[export] Instance proper_assume_vareq_impl {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      Proper (simpl (Σ - x∷σ) ==> simpl Σ) (assume_vareq x t).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition auto. Qed.

    #[export] Instance proper_assert_vareq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (msg : AMessage (Σ - x∷σ)) :
      Proper (sequiv (Σ - x∷σ) ==> sequiv Σ) (assert_vareq x t msg).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply and_iff_morphism. Qed.

    #[export] Instance proper_assert_vareq_impl {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (msg : AMessage (Σ - x∷σ)) :
      Proper (simpl (Σ - x∷σ) ==> simpl Σ) (assert_vareq x t msg).
    Proof. unfold simpl. intros p q pq ι. cbn. intuition auto. Qed.

    #[export] Instance proper_angelicv {Σ b} : Proper (sequiv (Σ ▻ b) ==> sequiv Σ) (angelicv b).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply ex_iff_morphism. Qed.

    #[export] Instance proper_angelicv_impl {Σ b} : Proper (simpl (Σ ▻ b) ==> simpl Σ) (angelicv b).
    Proof. unfold simpl. intros p q pq ι [v H]. exists v. now apply pq. Qed.

    #[export] Instance proper_demonicv {Σ b} : Proper (sequiv (Σ ▻ b) ==> sequiv Σ) (demonicv b).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply all_iff_morphism. Qed.

    #[export] Instance proper_pattern_match {Σ σ} (s : Term Σ σ) (pat : Pattern σ) :
      Proper
        (forall_relation (fun pc => sequiv (Σ ▻▻ PatternCaseCtx pc)) ==> sequiv Σ)
        (pattern_match s pat).
    Proof. intros p q pq ι. cbn. destruct pattern_match_val. apply pq. Qed.

    #[export] Instance proper_pattern_match_impl {Σ σ} (s : Term Σ σ) (pat : Pattern σ) :
      Proper
        (forall_relation (fun pc => simpl (Σ ▻▻ PatternCaseCtx pc)) ==> simpl Σ)
        (pattern_match s pat).
    Proof. intros p q pq ι. cbn. destruct pattern_match_val. apply pq. Qed.

    #[export] Instance proper_pattern_match_var {Σ x σ} (xIn : x∷σ ∈ Σ)
      (pat : Pattern σ) :
      Proper
        (forall_relation
           (fun pc => sequiv ((Σ ▻▻ PatternCaseCtx pc) - x∷σ)) ==> sequiv Σ)
        (pattern_match_var x pat).
    Proof. intros p q pq ι. cbn. destruct pattern_match_val. apply pq. Qed.

    #[export] Instance proper_pattern_match_var_impl {Σ x σ} (xIn : x∷σ ∈ Σ)
      (pat : Pattern σ) :
      Proper
        (forall_relation
           (fun pc => simpl ((Σ ▻▻ PatternCaseCtx pc) - x∷σ)) ==> simpl Σ)
        (pattern_match_var x pat).
    Proof. intros p q pq ι. cbn. destruct pattern_match_val. apply pq. Qed.

    #[export] Instance proper_debug {Σ} {bt : AMessage Σ} :
      Proper (sequiv Σ ==> sequiv Σ) (debug bt).
    Proof. unfold sequiv. intros p q pq ι. cbn. now rewrite ?debug_equiv. Qed.

    #[export] Instance proper_debug_impl {Σ} {bt : AMessage Σ} :
      Proper (simpl Σ ==> simpl Σ) (debug bt).
    Proof. unfold sequiv. intros p q pq ι. cbn. apply pq. Qed.

    Lemma angelic_close0_angelic_binary {Σ Σe} (p1 p2 : 𝕊 (Σ ▻▻ Σe)) :
      angelic_close0 Σe (angelic_binary p1 p2) <=>
      angelic_binary (angelic_close0 Σe p1) (angelic_close0 Σe p2).
    Proof.
      intros ι; cbn. rewrite ?safe_angelic_close0. cbn.
      split.
      - intros [ιe [HYP|HYP]]; [left|right]; exists ιe; exact HYP.
      - intros [[ιe HYP]|[ιe HYP]]; exists ιe; [left|right]; exact HYP.
    Qed.

    Lemma demonic_close0_demonic_binary {Σ Σu} (p1 p2 : 𝕊 (Σ ▻▻ Σu)) :
      demonic_close0 Σu (demonic_binary p1 p2) <=>
      demonic_binary (demonic_close0 Σu p1) (demonic_close0 Σu p2).
    Proof.
      intros ι; cbn. rewrite ?safe_demonic_close0. cbn.
      split.
      - intros sp; split; intros ιu; apply (sp ιu).
      - intros [sp1 sp2] ιu; split; auto.
    Qed.

    Lemma angelic_pattern_match_correct [Σ σ] (s : Term Σ σ) (pat : Pattern σ)
      (rhs : forall pc : PatternCase pat, 𝕊 (Σ ▻▻ PatternCaseCtx pc)) :
      angelic_pattern_match pat s rhs <=> pattern_match s pat rhs.
    Proof.
      unfold angelic_pattern_match, angelic_finite. intros ι. cbn.
      rewrite safe_angelic_list.
      setoid_rewrite safe_angelic_close0. cbn.
      setoid_rewrite inst_pattern_match_term_reverse.
      change_no_check (@inst_env _ _ _ _) with (@inst_sub).
      setoid_rewrite inst_subst.
      setoid_rewrite inst_sub_cat_right.
      setoid_rewrite inst_sub_cat_left.
      split.
      - intros (pc & HIn & ιpat & Hmatch & Hsafe).
        now rewrite <- Hmatch, pattern_match_val_inverse_right.
      - pose proof (pattern_match_val_inverse_left pat (inst s ι)) as Hmatch.
        destruct pattern_match_val as [pc ιpat]. intros Hsafe.
        exists pc. split. apply base.elem_of_list_In, finite.elem_of_enum.
        exists ιpat. split. exact Hmatch. exact Hsafe.
    Qed.

    Lemma angelic_pattern_match_var_correct [Σ x σ] (xIn : x∷σ ∈ Σ) (pat : Pattern σ)
      (rhs : forall pc : PatternCase pat, 𝕊 ((Σ ▻▻ PatternCaseCtx pc) - x∷σ)) :
      angelic_pattern_match_var pat rhs <=> pattern_match_var x pat rhs.
    Proof.
      unfold angelic_pattern_match_var, angelic_finite. intros ι. cbn.
      rewrite safe_angelic_list.
      setoid_rewrite safe_angelic_close0. cbn.
      setoid_rewrite env.lookup_cat_left.
      setoid_rewrite inst_pattern_match_term_reverse.
      setoid_rewrite inst_eq_rect.
      setoid_rewrite eq_sym_involutive.
      split.
      - intros (pc & HIn & ιpat & Hmatch & Hsafe). revert Hsafe.
        rewrite Hmatch. clear Hmatch.
        rewrite pattern_match_val_inverse_right.
        match goal with
          |- safe ?P ?ι1 -> safe ?P ?ι2 => enough (ι1 = ι2) as <-; auto
        end.
        rewrite env.remove_cat_left. rewrite eq_rect_sym2.
        change_no_check (@inst_env _ _ _ _) with (@inst_sub).
        rewrite env.remove_cat_left.
        f_equal. f_equal. symmetry. apply inst_sub_cat_right.
      - pose proof (pattern_match_val_inverse_left pat ι.[? x∷σ]) as Hmatch.
        destruct pattern_match_val as [pc ιpat]. intros Hsafe.
        exists pc. split. apply base.elem_of_list_In, finite.elem_of_enum.
        exists ιpat. split; auto. clear Hsafe.
        rewrite env.remove_cat_left, eq_rect_sym2.
        symmetry. etransitivity; [|exact Hmatch].
        unfold pattern_match_val_reverse'. cbn.
        f_equal. apply inst_sub_cat_right.
    Qed.

    Lemma demonic_pattern_match_correct [Σ σ] (s : Term Σ σ) (pat : Pattern σ)
      (rhs : forall pc : PatternCase pat, 𝕊 (Σ ▻▻ PatternCaseCtx pc)) :
      demonic_pattern_match pat s rhs <=> pattern_match s pat rhs.
    Proof.
      unfold demonic_pattern_match, demonic_finite. intros ι. cbn.
      rewrite safe_demonic_list.
      setoid_rewrite safe_demonic_close0. cbn.
      setoid_rewrite inst_pattern_match_term_reverse.
      change_no_check (@inst_env _ _ _ _) with (@inst_sub).
      setoid_rewrite inst_subst.
      setoid_rewrite inst_sub_cat_right.
      setoid_rewrite inst_sub_cat_left.
      split.
      - pose proof (pattern_match_val_inverse_left pat (inst s ι)) as Hmatch.
        destruct pattern_match_val as [pc ιpat]. intros HYP. apply HYP; auto.
        apply base.elem_of_list_In, finite.elem_of_enum.
      - intros Heq pc HIn ιpat Hmatch. rewrite <- Hmatch in Heq.
        now rewrite pattern_match_val_inverse_right in Heq.
    Qed.

    Lemma demonic_pattern_match_var_correct [Σ x σ] (xIn : x∷σ ∈ Σ) (pat : Pattern σ)
      (rhs : forall pc : PatternCase pat, 𝕊 ((Σ ▻▻ PatternCaseCtx pc) - x∷σ)) :
      demonic_pattern_match_var pat rhs <=> pattern_match_var x pat rhs.
    Proof.
      unfold demonic_pattern_match_var, demonic_finite. intros ι. cbn.
      rewrite safe_demonic_list.
      setoid_rewrite safe_demonic_close0. cbn.
      setoid_rewrite env.lookup_cat_left.
      setoid_rewrite inst_eq_rect.
      setoid_rewrite inst_pattern_match_term_reverse.
      setoid_rewrite eq_sym_involutive.
      change_no_check (@inst_env _ _ _ _) with (@inst_sub).
      split.
      - pose proof (pattern_match_val_inverse_left pat ι.[? x∷σ]) as Hmatch.
        destruct pattern_match_val as [pc ιpat].
        intros HYP. apply HYP. apply base.elem_of_list_In, finite.elem_of_enum.
        rewrite <- Hmatch. unfold pattern_match_val_reverse'. cbn.
        f_equal. rewrite env.remove_cat_left. rewrite eq_rect_sym2.
        symmetry. apply inst_sub_cat_right.
      - intros HYP pc HIn ιpat Hmatch. revert HYP.
        rewrite Hmatch.
        rewrite pattern_match_val_inverse_right.
        match goal with
          |- safe ?P ?ι1 -> safe ?P ?ι2 => enough (ι1 = ι2) as ->; auto
        end.
        f_equal. f_equal.
        rewrite env.remove_cat_left. rewrite eq_rect_sym2.
        apply inst_sub_cat_right.
    Qed.

    Module notations.
      (* The notations for symbolic universal quantification (∀) has an
         incompatible prefixes with the notation for the regular quantifier. The
         regular one uses [binder] for the quantified variables whereas the
         symbolic one uses [constr] the strings that are put into these
         positions. We only use the symbolic notation for printing, so we
         locally disable the warning. *)
      #[local] Set Warnings "-notation-incompatible-prefix".

      Notation "x" := (@term_var _ x%string _ (@ctx.MkIn _ (x%string :: _) _ _ _)) (at level 1, only printing).
      Notation "s = t" := (formula_relop bop.eq s t) (only printing, s in scope term, t in scope term).
      Notation "' t" := (@formula_bool _ t) (at level 10, only printing, format "' t").
      Notation "F ∧ P" := (@SymProp.assertk _ F _ P) (only printing).
      Notation "F → P" := (@SymProp.assumek _ F P) (only printing).
      Notation "'∃' x '∷' σ , P" := (SymProp.angelicv (x ∷ σ) P) (at level 10, P at level 200, only printing, format "'[  ' '[  ' '∃'  x '∷' σ ']' ,  '/' P ']'").
      Notation "'∀' x '∷' σ , P" := (SymProp.demonicv (x ∷ σ) P) (at level 10, P at level 200, only printing, format "'[  ' '[  ' '∀'  x '∷' σ ']' ,  '/' P ']'").
      Notation "⊤" := (@SymProp.block _).
      Notation "x ↦ t ∧ k" := (@SymProp.assert_vareq _ x _ _ t _ k) (at level 99, right associativity, only printing).
      Notation "x ↦ t → k" := (@SymProp.assume_vareq _ x _ _ t k) (at level 99, right associativity, only printing).
      Notation "P ∧ Q" := (@SymProp.demonic_binary _ P Q) (at level 80, right associativity, only printing).
      Notation "P ∨ Q" := (@SymProp.angelic_binary _ P Q) (at level 85, right associativity, only printing).
      Notation "x >= y" := (formula_relop bop.le y x) (only printing, x in scope term, y in scope term).
      Notation "x > y" := (formula_relop bop.lt y x) (only printing, x in scope term, y in scope term).
      Notation "x <= y" := (formula_relop bop.le x y) (only printing, x in scope term, y in scope term).
      Notation "x < y" := (formula_relop bop.lt x y) (only printing, x in scope term, y in scope term).
      Notation "t" := (term_val _ t) (at level 1, only printing).
    End notations.

    Module Statistics.

      Fixpoint size {Σ} (s : SymProp Σ) : N :=
        match s with
        | SymProp.angelic_binary o1 o2 => 1 + size o1 + size o2
        | SymProp.demonic_binary o1 o2 => 1 + size o1 + size o2
        | SymProp.error msg => 0
        | SymProp.block => 0
        | SymProp.assertk fml msg k => 1 + size k
        | SymProp.assumek fml k => 1 + size k
        | SymProp.angelicv b k => 1 + size k
        | SymProp.demonicv b k => 1 + size k
        | @SymProp.assert_vareq _ x σ xIn t msg k => 1 + size k
        | @SymProp.assume_vareq _ x σ xIn t k => 1 + size k
        | pattern_match _ pat rhs =>
            List.fold_right
              (fun pc => N.add (size (rhs pc))) 1%N
              (finite.enum (PatternCase pat))
        | pattern_match_var _ pat rhs =>
            List.fold_right
              (fun pc => N.add (size (rhs pc))) 1%N
              (finite.enum (PatternCase pat))
        | SymProp.debug b k => 1 + size k
        end.

      Record Count : Set :=
        { block : N
        ; error : N
        ; debug : N
        }.

      Definition empty := {| block := 0; error := 0; debug := 0 |}.

      Definition inc_block (c : Count) : Count :=
        match c with
        | {| block := b; error := e; debug := d |} =>
            {| block := N.succ b; error := e; debug := d |}
        end.

      Definition inc_error (c : Count) : Count :=
        match c with
        | {| block := b; error := e; debug := d |} =>
            {| block := b; error := N.succ e; debug := d |}
        end.

      Definition inc_debug (c : Count) : Count :=
        match c with
        | {| block := b; error := e; debug := d |} =>
            {| block := b; error := e; debug := N.succ d |}
        end.

      Fixpoint count_nodes {Σ} (s : 𝕊 Σ) (c : Count) : Count :=
        match s with
        | SymProp.error _              => inc_error c
        | SymProp.block                => inc_block c
        | SymProp.debug _ s            => count_nodes s (inc_debug c)
        | SymProp.demonicv _ s         => count_nodes s c
        | SymProp.angelicv _ s         => count_nodes s c
        | SymProp.assertk _ _ s        => count_nodes s c
        | SymProp.assumek _ s          => count_nodes s c
        | SymProp.assert_vareq _ _ _ s => count_nodes s c
        | SymProp.assume_vareq _ _ s   => count_nodes s c
        | SymProp.angelic_binary s1 s2 => count_nodes s2 (count_nodes s1 c)
        | SymProp.demonic_binary s1 s2 => count_nodes s2 (count_nodes s1 c)
        | SymProp.pattern_match _ pat rhs  =>
            List.fold_right
              (fun pc => count_nodes (rhs pc)) c
              (finite.enum (PatternCase pat))
        | SymProp.pattern_match_var _ pat rhs =>
            List.fold_right
              (fun pc => count_nodes (rhs pc)) c
              (finite.enum (PatternCase pat))
        end.

      Definition count_to_stats (c : Count) : Stats :=
        match c with
        | {| block := b; error := e; debug := d |} =>
          {| branches := b + e; pruned := b + e - d |}
        end.

    End Statistics.

  End SymProp.
  Notation SymProp := SymProp.SymProp.
  Notation 𝕊 := SymProp.SymProp.

  Module Postprocessing.

    Import SymProp.

    Definition angelic_binary_prune {Σ} (p1 p2 : 𝕊 Σ) : 𝕊 Σ :=
      match p1 , p2 with
      | block   , _       => block
      | _       , block   => block
      | error _ , _       => p2
      | _       , error _ => p1
      | _       , _       => angelic_binary p1 p2
      end.

    Definition demonic_binary_prune {Σ} (p1 p2 : 𝕊 Σ) : 𝕊 Σ :=
      match p1 , p2 with
      | block   , _       => p2
      | _       , block   => p1
      | error s , _       => error s
      | _       , error s => error s
      | _       , _       => demonic_binary p1 p2
      end.

    Definition assertk_prune {Σ} (fml : Formula Σ) (msg : AMessage Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match p with
      | error s => @error Σ s
      | _       => assertk fml msg p
      end.
    Global Arguments assertk_prune {Σ} fml msg p.

    Definition assumek_prune {Σ} (fml : Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match p with
      | block => block
      | _     => assumek fml p
      end.
    Global Arguments assumek_prune {Σ} fml p.

    Definition angelicv_prune {Σ} b (p : 𝕊 (Σ ▻ b)) : 𝕊 Σ :=
      match p with
      | error msg => error (amsg.there msg)
      | _         => angelicv b p
      end.

    Definition demonicv_prune {Σ} b (p : 𝕊 (Σ ▻ b)) : 𝕊 Σ :=
      match p with
      | block => block
      | _     => demonicv b p
      end.

    Definition assume_vareq_prune {Σ} {x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ :=
      match k with
      | block => block
      | _     => assume_vareq x t k
      end.
    Global Arguments assume_vareq_prune {Σ} x {σ xIn} t k.

    Definition assert_vareq_prune {Σ} {x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (msg : AMessage (Σ - x∷σ)) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ :=
      match k with
      | error emsg => error (subst emsg (sub_shift xIn))
      | _          => assert_vareq x t msg k
      end.
    Global Arguments assert_vareq_prune {Σ} x {σ xIn} t msg k.

    Fixpoint prune {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      match p with
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
      | pattern_match s pat rhs =>
        pattern_match s pat (fun pc => prune (rhs pc))
      | pattern_match_var x pat rhs =>
        pattern_match_var x pat (fun pc => prune (rhs pc))
      | debug d k =>
        debug d (prune k)
      end.

    Lemma prune_angelic_binary_sound {Σ} (p1 p2 : 𝕊 Σ) (ι : Valuation Σ) :
      safe (angelic_binary_prune p1 p2) ι <-> safe (angelic_binary p1 p2) ι.
    Proof.
      destruct p1; cbn; auto.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition auto.
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
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
    Qed.

    Lemma prune_demonic_binary_sound {Σ} (p1 p2 : 𝕊 Σ) (ι : Valuation Σ) :
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
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
    Qed.

    Lemma prune_assertk_sound {Σ} fml msg (p : 𝕊 Σ) (ι : Valuation Σ) :
      safe (assertk_prune fml msg p) ι <-> safe (assertk fml msg p) ι.
    Proof. destruct p; cbn; rewrite ?obligation_equiv; auto; intuition. Qed.

    Lemma prune_assumek_sound {Σ} fml (p : 𝕊 Σ) (ι : Valuation Σ) :
      safe (assumek_prune fml p) ι <-> safe (assumek fml p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_angelicv_sound {Σ b} (p : 𝕊 (Σ ▻ b)) (ι : Valuation Σ) :
      safe (angelicv_prune p) ι <-> safe (angelicv b p) ι.
    Proof. destruct p; cbn; auto; firstorder. Qed.

    Lemma prune_demonicv_sound {Σ b} (p : 𝕊 (Σ ▻ b)) (ι : Valuation Σ) :
      safe (demonicv_prune p) ι <-> safe (demonicv b p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_assert_vareq_sound {Σ x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (msg : AMessage (Σ - x∷σ)) (p : 𝕊 (Σ - x∷σ)) (ι : Valuation Σ) :
      safe (assert_vareq_prune x t msg p) ι <-> safe (assert_vareq x t msg p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_assume_vareq_sound {Σ x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (p : 𝕊 (Σ - x∷σ)) (ι : Valuation Σ) :
      safe (assume_vareq_prune x t p) ι <-> safe (assume_vareq x t p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_sound {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
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
        apply ex_iff_morphism; intros v.
        now rewrite IHp.
      - rewrite prune_demonicv_sound; cbn.
        apply all_iff_morphism; intros v.
        now rewrite IHp.
      - rewrite prune_assert_vareq_sound; cbn.
        now rewrite IHp.
      - rewrite prune_assume_vareq_sound; cbn.
        now rewrite IHp.
      - destruct pattern_match_val; cbn; auto.
      - destruct pattern_match_val; cbn; auto.
      - now rewrite ?debug_equiv.
    Qed.

    Module SolveEvars.

      Fixpoint assert_msgs_formulas {Σ} (mfs : Ctx (Pair AMessage Formula Σ)) (p : 𝕊 Σ) : 𝕊 Σ :=
        match mfs with
        | ctx.nil => p
        | ctx.snoc mfs (msg,fml) =>
          assert_msgs_formulas mfs (assertk fml msg p)
        end.

      Lemma safe_assert_msgs_formulas {Σ} {mfs : Ctx (Pair AMessage Formula Σ)} {p : 𝕊 Σ} {ι : Valuation Σ} :
        (safe (assert_msgs_formulas mfs p) ι <-> instprop mfs ι /\ safe p ι).
      Proof.
        revert p.
        induction mfs; intros p; cbn.
        - intuition.
        - destruct b. rewrite IHmfs. now cbn.
      Qed.

      Inductive ECtx (Σ : LCtx) : LCtx -> Type :=
      | ectx Σe (mfs : Ctx (Pair AMessage Formula (Σ ▻▻ Σe))) : ECtx Σ (Σ ▻▻ Σe).
      Arguments ectx {Σ} Σe mfs.

      Definition ectx_refl {Σ : LCtx} : ECtx Σ Σ := @ectx Σ ctx.nil ctx.nil.

      Definition ectx_formula {Σ1 Σ2} (e: ECtx Σ1 Σ2) : AMessage Σ2 -> Formula Σ2 -> ECtx Σ1 Σ2 :=
        match e with ectx Σe mfs => fun msg fml => ectx Σe (mfs ▻ (msg,fml)) end.
      Definition ectx_snoc {Σ1 Σ2} (e: ECtx Σ1 Σ2) b : ECtx Σ1 (Σ2 ▻ b) :=
        match e with ectx Σe mfs => ectx (Σe ▻ b) (subst mfs sub_wk1) end.
      Definition ectx_subst {Σ1 Σ2} (e : ECtx Σ1 Σ2) :
        forall x σ (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ),
          option (ECtx Σ1 (Σ2 - x∷σ)) :=
        match e with
        | ectx Σe mfs =>
            fun x σ xIn =>
              match ctx.catView xIn with
              | ctx.isCatLeft bIn  => fun _ => None
              | ctx.isCatRight bIn =>
                  fun t =>
                    let e  := ctx.remove_in_cat_right bIn in
                    let ζ  := sub_single (ctx.in_cat_right bIn) t in
                    let ζ' := eq_rect _ (Sub (Σ1 ▻▻ Σe)) ζ _ e in
                    Some (eq_rect_r _ (ectx _ (subst mfs ζ')) e)
              end
        end.

      Definition plug {Σ1 Σ2} (e : ECtx Σ1 Σ2) : 𝕊 Σ2 -> 𝕊 Σ1 :=
        match e with ectx Σe mfs => fun p => angelic_close0 Σe (assert_msgs_formulas mfs p) end.

      Definition plug_msg {Σ1 Σ2} (ec : ECtx Σ1 Σ2) : AMessage Σ2 -> AMessage Σ1 :=
        match ec with ectx _ _ => amsg.close end.

      Fixpoint push {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (p : 𝕊 Σ2) {struct p} : 𝕊 Σ1 :=
        match p with
        | angelic_binary p1 p2   => angelic_binary (push ec p1) (push ec p2)
        | demonic_binary p1 p2   => plug ec (demonic_binary (push ectx_refl p1) (push ectx_refl p2))
        | error msg              => error (plug_msg ec msg)
        | block                  => plug ec block
        | assertk fml msg p      => push (ectx_formula ec msg fml) p
        | assumek fml p          => plug ec (assumek fml (push ectx_refl p))
        | angelicv b p           => push (ectx_snoc ec b) p
        | demonicv b p           => plug ec (demonicv b (push ectx_refl p))
        | assert_vareq x t msg p =>
            match ectx_subst ec _ t with
            | Some e' => push e' p
            | None    => plug ec (assert_vareq x t msg (push ectx_refl p))
            end
        | assume_vareq x t p     => plug ec (assume_vareq x t (push ectx_refl p))
        | pattern_match s pat rhs =>
            plug ec (pattern_match s pat (fun pc => push ectx_refl (rhs pc)))
        | pattern_match_var x pat rhs =>
            plug ec (pattern_match_var x pat (fun pc => push ectx_refl (rhs pc)))
        | debug b p              => plug ec (debug b (push ectx_refl p))
        end.

      #[export] Instance proper_assert_msgs_formulas {Σ} (mfs : Ctx (Pair AMessage Formula Σ)) :
        Proper (sequiv Σ ==> sequiv Σ) (assert_msgs_formulas mfs).
      Proof. intros p q pq ι. rewrite !safe_assert_msgs_formulas. now apply and_iff_morphism. Qed.

      #[export] Instance proper_plug {Σ1 Σ2} (ec : ECtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_angelic_close0, proper_assert_msgs_formulas.
      Qed.

      Lemma assert_msgs_formulas_angelic_binary {Σ} (mfs : Ctx (Pair AMessage Formula Σ)) (p1 p2 : 𝕊 Σ) :
        assert_msgs_formulas mfs (angelic_binary p1 p2) <=>
        angelic_binary (assert_msgs_formulas mfs p1) (assert_msgs_formulas mfs p2).
      Proof.
        intros ι; cbn.
        rewrite ?safe_assert_msgs_formulas.
        cbn. intuition.
      Qed.

      Lemma assert_msgs_formulas_angelicv {b Σ} (mfs : Ctx (Pair AMessage Formula Σ)) (p : 𝕊 (Σ ▻ b)) :
        assert_msgs_formulas mfs (angelicv b p) <=>
        angelicv b (assert_msgs_formulas (subst mfs sub_wk1) p).
      Proof.
        intros ι; cbn.
        rewrite safe_assert_msgs_formulas. cbn.
        rewrite Logic.and_comm, <- exists_and.
        apply ex_iff_morphism. intros v.
        rewrite safe_assert_msgs_formulas.
        rewrite instprop_subst.
        rewrite inst_sub_wk1.
        apply Logic.and_comm.
      Qed.

      Lemma plug_eq_rect {Σ1 Σ2 Σ2'} (eq : Σ2 = Σ2') (ec : ECtx Σ1 Σ2) (p : 𝕊 Σ2') :
        plug (eq_rect Σ2 (ECtx Σ1) ec Σ2' eq) p = plug ec (eq_rect_r (fun Σ3 : LCtx => 𝕊 Σ3) p eq).
      Proof. now destruct eq. Qed.

      Lemma ectx_subst_spec {Σ1 Σ2} (ec : ECtx Σ1 Σ2) {x σ} (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ) (msg : AMessage _) :
        option.wlp
          (fun e => forall p, plug e p <=> plug ec (assert_vareq x t msg p))
          (ectx_subst ec xIn t).
      Proof.
        destruct ec; cbn. destruct (ctx.catView xIn); constructor; auto.
        intros p ι. unfold eq_rect_r. rewrite plug_eq_rect. cbn.
        rewrite ?safe_angelic_close0.
        split; intros [ιe HYP].
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          unfold eq_rect_r in Hp. rewrite safe_eq_rect, eq_sym_involutive in Hp.
          exists (env.insert bIn ιe (inst (eq_rect ((Σ1 ▻▻ Σe) - x∷σ) (fun Σ => Term Σ σ) t (Σ1 ▻▻ Σe - x∷σ) (ctx.remove_in_cat_right bIn)) (ι ►► ιe))).
          rewrite safe_assert_msgs_formulas. cbn.
          rewrite env.insert_cat_right, env.remove_insert, env.lookup_insert.
          rewrite ?inst_eq_rect.
          split; auto.
          rewrite instprop_subst, inst_eq_rect in Hpc.
          now rewrite inst_sub_single2 in Hpc.
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          cbn in Hp. cbn in Hp. destruct Hp as [Ht Hp].
          rewrite env.remove_cat_right in Hp.
          exists (env.remove (x∷σ) ιe bIn).
          rewrite safe_assert_msgs_formulas.
          rewrite instprop_subst.
          unfold eq_rect_r. rewrite safe_eq_rect.
          rewrite eq_sym_involutive. split; auto.
          rewrite inst_eq_rect.
          rewrite <- env.remove_cat_right.
          rewrite <- inst_sub_shift.
          rewrite inst_sub_single_shift; auto.
          now rewrite inst_sub_shift.
      Qed.

      Lemma error_plug_msg {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (msg : AMessage Σ2) :
        error (plug_msg ec msg) <=> plug ec (error msg).
      Proof.
        destruct ec; intros ι; cbn.
        split; try contradiction.
        rewrite safe_angelic_close0.
        intros [ιe HYP].
        rewrite safe_assert_msgs_formulas in HYP.
        destruct HYP as [? []].
      Qed.

      Lemma push_plug {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (p : 𝕊 Σ2) :
        push ec p <=> plug ec p.
      Proof.
        revert Σ1 ec; induction p; cbn; intros Σ1 ec.
        - rewrite IHp1, IHp2. clear IHp1 IHp2.
          destruct ec. cbn [plug].
          rewrite <- angelic_close0_angelic_binary.
          apply proper_angelic_close0.
          now rewrite <- assert_msgs_formulas_angelic_binary.
        - apply proper_plug, proper_demonic_binary;
           [now rewrite IHp1 | now rewrite IHp2].
        - apply error_plug_msg.
        - reflexivity.
        - rewrite IHp. clear IHp.
          destruct ec; cbn. reflexivity.
        - apply proper_plug, proper_assumek, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn.
          apply proper_angelic_close0.
          rewrite assert_msgs_formulas_angelicv.
          reflexivity.
        - apply proper_plug, proper_demonicv, IHp.
        - destruct (ectx_subst_spec ec xIn t msg).
          + rewrite IHp. rewrite H. reflexivity.
          + apply proper_plug, proper_assert_vareq, IHp.
        - apply proper_plug, proper_assume_vareq, IHp.
        - apply proper_plug. (* rewrite angelic_pattern_match_correct. *)
          apply proper_pattern_match. intros pc. now rewrite H.
        - apply proper_plug.  (* rewrite angelic_pattern_match_var_correct. *)
          apply proper_pattern_match_var. intros pc. now rewrite H.
        - apply proper_plug, proper_debug, IHp.
      Qed.

    End SolveEvars.

    Definition solve_evars {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      SolveEvars.push SolveEvars.ectx_refl p.

    Lemma solve_evars_sound {Σ} (p : 𝕊 Σ) :
      forall ι, safe (solve_evars p) ι <-> safe p ι.
    Proof. apply (SolveEvars.push_plug SolveEvars.ectx_refl). Qed.

    Module SolveUvars.

      Fixpoint assume_pathcondition {Σ} (C : PathCondition Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
        match C with
        | [ctx] => p
        | C ▻ F => assume_pathcondition C (assumek F p)
        end.

      Lemma safe_assume_pathcondition {Σ} {C : PathCondition Σ} {p : 𝕊 Σ} {ι : Valuation Σ} :
        safe (assume_pathcondition C p) ι <-> (instprop C ι -> safe p ι).
      Proof.
        revert p.
        induction C; intros p; cbn.
        - intuition.
        - rewrite IHC. cbn. intuition.
      Qed.

      Inductive UCtx (Σ : LCtx) : LCtx -> Type :=
      | uctx Σu (mfs : PathCondition (Σ ▻▻ Σu)) : UCtx Σ (Σ ▻▻ Σu).
      Arguments uctx {Σ} Σu mfs.

      Definition uctx_refl {Σ : LCtx} : UCtx Σ Σ := @uctx Σ ctx.nil ctx.nil.

      Definition uctx_formula {Σ1 Σ2} (e : UCtx Σ1 Σ2) : Formula Σ2 -> UCtx Σ1 Σ2 :=
        match e with uctx Σu C => fun F => uctx Σu (C ▻ F) end.
      Definition uctx_snoc {Σ1 Σ2} (e: UCtx Σ1 Σ2) b : UCtx Σ1 (Σ2 ▻ b) :=
        match e with uctx Σu C => uctx (Σu ▻ b) (subst C sub_wk1) end.
      Definition uctx_subst {Σ1 Σ2} (e : UCtx Σ1 Σ2) :
        forall x σ (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ),
          option (UCtx Σ1 (Σ2 - x∷σ)) :=
        match e with
        | uctx Σu mfs =>
            fun x σ xIn =>
              match ctx.catView xIn with
              | ctx.isCatLeft bIn  => fun _ => None
              | ctx.isCatRight bIn =>
                  fun t =>
                    let e  := ctx.remove_in_cat_right bIn in
                    let ζ  := sub_single (ctx.in_cat_right bIn) t in
                    let ζ' := eq_rect _ (Sub (Σ1 ▻▻ Σu)) ζ _ e in
                    Some (eq_rect_r _ (uctx _ (subst mfs ζ')) e)
              end
        end.

      Definition plug {Σ1 Σ2} (e : UCtx Σ1 Σ2) : 𝕊 Σ2 -> 𝕊 Σ1 :=
        match e with uctx Σu C => fun p => demonic_close0 Σu (assume_pathcondition C p) end.

      Definition plug_error {Σ1 Σ2} (ec : UCtx Σ1 Σ2) : AMessage Σ2 -> 𝕊 Σ1 :=
       match ec with
       | uctx Σu C as ec =>
           fun msg =>
             match C with
             | [ctx] => error (amsg.close msg)
             | _ ▻ _ => plug ec (error msg)
             end
       end.

      Fixpoint push {Σ1 Σ2} (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2) {struct p} : 𝕊 Σ1 :=
        match p with
        | angelic_binary p1 p2   => plug ec (angelic_binary (push uctx_refl p1) (push uctx_refl p2))
        | demonic_binary p1 p2   => plug ec (demonic_binary (push uctx_refl p1) (push uctx_refl p2))
            (* demonic_binary (push ec p1) (push ec p2) *)
        | error msg              => plug_error ec msg
        | block                  => block
        | assertk fml msg p      => plug ec (assertk fml msg (push uctx_refl p))
        | assumek fml p          => push (uctx_formula ec fml) p
        | angelicv b p           => plug ec (angelicv b (push uctx_refl p))
        | demonicv b p           => push (uctx_snoc ec b) p
        | assert_vareq x t msg p => plug ec (assert_vareq x t msg (push uctx_refl p))
        | assume_vareq x t p     =>
            match uctx_subst ec _ t with
            | Some e' => push e' p
            | None    => plug ec (assume_vareq x t (push uctx_refl p))
            end
        | pattern_match s pat rhs =>
            plug ec (pattern_match s pat (fun pc => push uctx_refl (rhs pc)))
        | pattern_match_var x pat rhs =>
            plug ec (pattern_match_var x pat (fun pc => push uctx_refl (rhs pc)))
        | debug b p              => plug ec (debug b (push uctx_refl p))
        end.

      #[export] Instance proper_assume_pathcondition {Σ} (mfs : PathCondition Σ) :
        Proper (sequiv Σ ==> sequiv Σ) (assume_pathcondition mfs).
      Proof.
        intros p q pq ι. rewrite !safe_assume_pathcondition.
        now apply imp_iff_compat_l.
      Qed.

      #[export] Instance proper_assume_pathcondition_impl {Σ} (mfs : PathCondition Σ) :
        Proper (simpl Σ ==> simpl Σ) (assume_pathcondition mfs).
      Proof. intros p q pq ι. rewrite !safe_assume_pathcondition. auto. Qed.

      #[export] Instance proper_plug {Σ1 Σ2} (ec : UCtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_demonic_close0, proper_assume_pathcondition.
      Qed.

      #[export] Instance proper_plug_impl {Σ1 Σ2} (ec : UCtx Σ1 Σ2) :
        Proper (simpl Σ2 ==> simpl Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_demonic_close0_impl, proper_assume_pathcondition_impl.
      Qed.

      Lemma assume_pathcondition_demonic_binary {Σ} (fmls : PathCondition Σ) (p1 p2 : 𝕊 Σ) :
        assume_pathcondition fmls (demonic_binary p1 p2) <=>
        demonic_binary (assume_pathcondition fmls p1) (assume_pathcondition fmls p2).
      Proof.
        intros ι; cbn.
        rewrite !safe_assume_pathcondition.
        cbn. intuition auto.
      Qed.

      Lemma forall_impl {A : Type} {P : A -> Prop} {Q : Prop} :
        (Q -> forall (x : A), P x) <-> (forall (x : A), Q -> P x).
      Proof. firstorder. Qed.

      Lemma assume_pathcondition_demonicv {b Σ} (fmls : PathCondition Σ) (p : 𝕊 (Σ ▻ b)) :
        assume_pathcondition fmls (demonicv b p) <=>
        demonicv b (assume_pathcondition (subst fmls sub_wk1) p).
      Proof.
        intros ι; cbn.
        rewrite safe_assume_pathcondition. cbn.
        rewrite forall_impl.
        apply all_iff_morphism. intros v.
        rewrite safe_assume_pathcondition.
        rewrite instprop_subst.
        rewrite inst_sub_wk1.
        reflexivity.
      Qed.

      Lemma plug_eq_rect {Σ1 Σ2 Σ2'} (eq : Σ2 = Σ2') (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2') :
        plug (eq_rect Σ2 (UCtx Σ1) ec Σ2' eq) p = plug ec (eq_rect_r (fun Σ3 : LCtx => 𝕊 Σ3) p eq).
      Proof. now destruct eq. Qed.

      Lemma uctx_subst_spec {Σ1 Σ2} (ec : UCtx Σ1 Σ2) {x σ} (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ) :
        option.wlp
          (fun e => forall p, plug e p <=> plug ec (assume_vareq x t p))
          (uctx_subst ec xIn t).
      Proof.
        destruct ec; cbn. destruct (ctx.catView xIn); constructor; auto.
        intros p ι. unfold eq_rect_r. rewrite plug_eq_rect. cbn.
        rewrite ?safe_demonic_close0.
        split; intros HYP ιu.
        - specialize (HYP (env.remove (x∷σ) ιu bIn)).
          rewrite safe_assume_pathcondition. intros Hpc Heq.
          rewrite <- inst_sub_shift in Heq.
          rewrite safe_assume_pathcondition in HYP.
          rewrite instprop_subst in HYP.
          rewrite inst_eq_rect in HYP.
          unfold eq_rect_r in HYP. rewrite safe_eq_rect, eq_sym_involutive in HYP.
          rewrite <- env.remove_cat_right in HYP. apply HYP.
          rewrite <- inst_sub_shift.
          rewrite inst_sub_single_shift; auto.
        - specialize (HYP (env.insert bIn ιu (inst (eq_rect ((Σ1 ▻▻ Σu) - x∷σ) (fun Σ => Term Σ σ) t (Σ1 ▻▻ Σu - x∷σ) (ctx.remove_in_cat_right bIn)) (ι ►► ιu)))).
          rewrite safe_assume_pathcondition, instprop_subst, inst_eq_rect. intros Hpc.
          unfold eq_rect_r. rewrite safe_eq_rect, eq_sym_involutive.
          rewrite safe_assume_pathcondition in HYP. cbn in HYP.
          rewrite env.insert_cat_right, env.remove_insert, env.lookup_insert in HYP.
          rewrite inst_eq_rect in HYP.
          rewrite inst_sub_single2 in Hpc.
          now apply HYP.
      Qed.

      Lemma push_plug {Σ1 Σ2} (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2) :
        push ec p =>> plug ec p.
      Proof.
        revert Σ1 ec; induction p; cbn; intros Σ1 ec.
        - apply proper_plug_impl, proper_angelic_binary_impl; cbn;
           [now rewrite IHp1 | now rewrite IHp2].
        - rewrite IHp1, IHp2. clear IHp1 IHp2.
          reflexivity.
          (* destruct ec. cbn [plug]. *)
          (* rewrite <- demonic_close0_demonic_binary. *)
          (* apply proper_demonic_close0. *)
          (* now rewrite <- assume_pathcondition_demonic_binary. *)
        - now destruct ec as [? []].
        - intros ι _. destruct ec; cbn.
          rewrite safe_demonic_close0; intros ιu.
          rewrite safe_assume_pathcondition; cbn; auto.
        - apply proper_plug_impl, proper_assertk_impl, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn. reflexivity.
        - apply proper_plug_impl, proper_angelicv_impl, IHp.
        - rewrite IHp. clear IHp. destruct ec; cbn.
          apply proper_demonic_close0_impl. intros ι. cbn.
          rewrite safe_assume_pathcondition. intros H Mmfs v.
          specialize (H v). rewrite safe_assume_pathcondition in H.
          apply H. now rewrite instprop_subst, inst_sub_wk1.
        - apply proper_plug_impl, proper_assert_vareq_impl, IHp.
        - destruct (uctx_subst_spec ec xIn t).
          + rewrite IHp. intros ι. apply H.
          + apply proper_plug_impl, proper_assume_vareq_impl, IHp.
        - apply proper_plug_impl. (* rewrite demonic_pattern_match_correct. *)
          apply proper_pattern_match_impl. intros pc. now rewrite H.
        - apply proper_plug_impl. (* rewrite demonic_pattern_match_var_correct. *)
          apply proper_pattern_match_var_impl. intros pc. now rewrite H.
        - apply proper_plug_impl, proper_debug_impl, IHp.
      Qed.

    End SolveUvars.

    Definition solve_uvars {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      SolveUvars.push SolveUvars.uctx_refl p.

    Lemma solve_uvars_sound {Σ} (p : 𝕊 Σ) :
      forall ι, safe (solve_uvars p) ι -> safe p ι.
    Proof. apply (SolveUvars.push_plug SolveUvars.uctx_refl). Qed.

    Module Experimental.

      Definition Ephemeral (Σ1 Σ2 : LCtx) : Type :=
        SolveEvars.ECtx Σ1 Σ2 + SolveUvars.UCtx Σ1 Σ2.

      Definition EProp : LCtx -> Type :=
        fun Σ : LCtx => forall Σ0, Ephemeral Σ0 Σ -> 𝕊 Σ0.

      Definition angelic_binary {Σ} (p q : EProp Σ) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => SymProp.angelic_binary (p Σ0 eph) (q Σ0 eph)
          | inr uc => let eph' : Ephemeral _ _ := inl SolveEvars.ectx_refl in
                      SolveUvars.plug uc (SymProp.angelic_binary (p Σ eph') (q Σ eph'))
          end.

      Definition angelicv {Σ} (b : LVar ∷ Ty) (p : EProp (Σ ▻ b)) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => p Σ0 (inl (SolveEvars.ectx_snoc ec b))
          | inr uc => let eph' : Ephemeral _ _ := inl SolveEvars.ectx_refl in
                      SolveUvars.plug uc (angelicv b (p (Σ ▻ b) eph'))
          end.

      Definition demonic_binary {Σ} (p q : EProp Σ) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => let eph' : Ephemeral _ _ := inr SolveUvars.uctx_refl in
                      SolveEvars.plug ec (SymProp.demonic_binary (p Σ eph') (q Σ eph'))
          | inr uc => SymProp.demonic_binary (p Σ0 eph) (q Σ0 eph)
          end.

      Definition error {Σ} (msg : AMessage Σ) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => error (SolveEvars.plug_msg ec msg)
          | inr uc => SolveUvars.plug uc (error msg)
          end.

    End Experimental.

  End Postprocessing.

  Section PostProcess.

    Import SymProp.
    Import Postprocessing.

    Definition postprocess {Σ} (P : 𝕊 Σ) : 𝕊 Σ :=
      prune (solve_uvars (prune (solve_evars (prune P)))).

    Lemma postprocess_sound {Σ} (P : 𝕊 Σ) :
      forall ι, SymProp.safe (postprocess P) ι -> safe P ι.
    Proof.
      unfold postprocess. intros ι H.
      rewrite prune_sound in H.
      apply solve_uvars_sound in H.
      rewrite prune_sound in H.
      rewrite solve_evars_sound in H.
      rewrite prune_sound in H.
      exact H.
    Qed.

  End PostProcess.

  Module Erasure.

    Import SymProp.

    Inductive ETerm : Ty -> Set :=
    | eterm_var     (ℓ : LVar) (σ : Ty) (n : nat) : ETerm σ
    | eterm_val     (σ : Ty) (v : Val σ) : ETerm σ
    | eterm_binop   {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) (t1 : ETerm σ1) (t2 : ETerm σ2) : ETerm σ3
    | eterm_unop    {σ1 σ2} (op : UnOp σ1 σ2) (t : ETerm σ1) : ETerm σ2
    | eterm_tuple   {σs : Ctx Ty} (ts : Env ETerm σs) : ETerm (ty.tuple σs)
    | eterm_union   {U : unioni} (K : unionk U) (t : ETerm (unionk_ty U K)) : ETerm (ty.union U)
    | eterm_record  (R : recordi) (ts : NamedEnv ETerm (recordf_ty R)) : ETerm (ty.record R).

    Inductive EFormula : Type :=
    | eformula_user (p : 𝑷) (ts : Env ETerm (𝑷_Ty p))
    | eformula_bool (t : ETerm ty.bool)
    | eformula_prop {Σ' : LCtx} (ζ : Env (fun x => ETerm (type x)) Σ') (P : abstract_named Val Σ' Prop)
    | eformula_relop {σ} (op : RelOp σ) (t1 t2 : ETerm σ)
    | eformula_true
    | eformula_false
    | eformula_and (F1 F2 : EFormula)
    | eformula_or (F1 F2 : EFormula).
    Arguments eformula_user : clear implicits.

    Inductive ESymProp : Type :=
    | eangelic_binary (o1 o2 : ESymProp)
    | edemonic_binary (o1 o2 : ESymProp)
    | eerror
    | eblock
    | eassertk (fml : EFormula) (k : ESymProp)
    | eassumek (fml : EFormula) (k : ESymProp)
    | eangelicv (b : LVar∷Ty) (k : ESymProp)
    | edemonicv (b : LVar∷Ty) (k : ESymProp)
    | eassert_vareq
        (x : LVar)
        (σ : Ty)
        (n : nat)
        (t : ETerm σ)
        (k : ESymProp)
    | eassume_vareq
        (x : LVar)
        (σ : Ty)
        (n : nat)
        (t : ETerm σ)
        (k : ESymProp)
    | epattern_match {σ} (s : ETerm σ) (pat : @Pattern LVar σ)
        (rhs : PatternCase pat -> ESymProp)
    | epattern_match_var (x : LVar) σ (n : nat) (pat : @Pattern LVar σ)
        (rhs : PatternCase pat -> ESymProp)
    | edebug {Σ}
        (b : AMessage Σ) (k : ESymProp).

    Definition erase_term {Σ} : forall {σ} (t : Term Σ σ), ETerm σ :=
      fix erase {σ} t :=
        match t with
        | @term_var _ ℓ σ ℓIn         => eterm_var ℓ σ (ctx.in_at ℓIn)
        | term_val σ v               => eterm_val σ v
        | term_binop op t1 t2        => eterm_binop op (erase t1) (erase t2)
        | term_unop op t             => eterm_unop op (erase t)
        | term_tuple ts              => eterm_tuple (env.map (fun _ => erase) ts)
        | term_union U K t           => eterm_union K (erase t)
        | term_record R ts           => eterm_record R (env.map (fun _ => erase) ts)
        end.

    Definition erase_formula {Σ} : Formula Σ -> EFormula :=
      fix erase f :=
        match f with
        | formula_user p ts      => eformula_user p (env.map (@erase_term Σ) ts)
        | formula_bool t         => eformula_bool (erase_term t)
        | formula_prop ζ P       => eformula_prop (env.map (fun _ => erase_term) ζ) P
        | formula_relop op t1 t2 => eformula_relop op (erase_term t1) (erase_term t2)
        | formula_true           => eformula_true
        | formula_false          => eformula_false
        | formula_and F1 F2      => eformula_and (erase F1) (erase F2)
        | formula_or F1 F2       => eformula_or (erase F1) (erase F2)
        end.

    Fixpoint erase_symprop {Σ} (p : SymProp Σ) : ESymProp :=
      match p with
      | angelic_binary o1 o2 => eangelic_binary (erase_symprop o1) (erase_symprop o2)
      | demonic_binary o1 o2 => edemonic_binary (erase_symprop o1) (erase_symprop o2)
      | error _ => eerror
      | block => eblock
      | assertk fml _ k => eassertk (erase_formula fml) (erase_symprop k)
      | assumek fml k => eassumek (erase_formula fml) (erase_symprop k)
      | angelicv b k => eangelicv b (erase_symprop k)
      | demonicv b k => edemonicv b (erase_symprop k)
      | @assert_vareq _ x σ xIn t msg k => eassert_vareq x (ctx.in_at xIn) (erase_term t) (erase_symprop k)
      | @assume_vareq _ x σ xIn t k => eassume_vareq x (ctx.in_at xIn) (erase_term t) (erase_symprop k)
      | pattern_match s pat rhs =>
          epattern_match (erase_term s) pat
            (fun pc => erase_symprop (rhs pc))
      | @pattern_match_var _ x σ xIn pat rhs =>
          epattern_match_var x (ctx.in_at xIn) pat
            (fun pc => erase_symprop (rhs pc))
      | debug b k => edebug b (erase_symprop k)
      end.

    Fixpoint erase_valuation {Σ} (ι : Valuation Σ) : list { σ : Ty & Val σ} :=
      match ι with
      | env.nil        => nil
      | env.snoc ι b v => cons (existT (type b) v) (erase_valuation ι)
      end.

    Lemma erase_valuation_eq_rect {Σ1 Σ2} (ι : Valuation Σ1) (e : Σ1 = Σ2) :
      erase_valuation (eq_rect Σ1 (fun Σ => Valuation Σ) ι Σ2 e) = erase_valuation ι.
    Proof. now subst. Qed.

    Import option.notations.

    Definition inst_env' (ι : list { σ : Ty & Val σ}) (inst_eterm : forall τ, ETerm τ -> option (Val τ)) :
      forall {Δ : Ctx Ty}, Env ETerm Δ -> option (Env Val Δ) :=
       fix inst_env {Δ} E :=
         match E with
         | [] => Some []
         | @env.snoc _ _ Γ E σ t =>
             v  <- inst_eterm σ t;;
             vs <- inst_env E;;
             Some (vs ► (σ ↦ v))
         end.

    Definition inst_namedenv' (ι : list { σ : Ty & Val σ}) (inst_eterm : forall τ, ETerm τ -> option (Val τ)) {N} :
      forall {Δ : NCtx N Ty}, NamedEnv ETerm Δ -> option (NamedEnv Val Δ) :=
       fix inst_env {Δ} E :=
         match E with
         | [] => Some []
         | @env.snoc _ _ Γ E (ℓ∷σ) t =>
             v  <- inst_eterm σ t;;
             vs <- inst_env E;;
             Some (vs ► (ℓ∷σ ↦ v))
         end.

    Definition inst_eterm (ι : list { σ : Ty & Val σ}) : forall [τ], ETerm τ -> option (Val τ) :=
      fix inst_eterm [τ] t :=
        match t with
        | eterm_var _ τ n =>
            '(existT σ v) <- nth_error ι n;;
            match Classes.eq_dec σ τ with
            | left e => Some (eq_rect σ Val v τ e)
            | right _ => None
            end
        | eterm_val σ v => Some v
        | @eterm_binop σ1 σ2 σ3 op t1 t2 =>
            v1 <- inst_eterm t1;;
            v2 <- inst_eterm t2;;
            Some (bop.eval op v1 v2)
        | @eterm_unop σ1 σ2 op t0  =>
            uop.eval op <$> inst_eterm t0
        | @eterm_tuple σs ts =>
            envrec.of_env (σs := σs) <$> inst_env' ι inst_eterm ts
        | @eterm_union U K t0 =>
            v <- inst_eterm t0 ;;
            Some (unionv_fold U (existT K v))
        | @eterm_record R ts =>
            recordv_fold R <$> inst_namedenv' ι inst_eterm ts
        end.

    Definition inst_namedenv (ι : list { σ : Ty & Val σ}) {N} {Δ : NCtx N Ty} :
      NamedEnv ETerm Δ -> option (NamedEnv Val Δ) :=
      inst_namedenv' ι (inst_eterm ι).

    Definition inst_env (ι : list { σ : Ty & Val σ}) :
      forall {Δ : Ctx Ty}, Env ETerm Δ -> option (Env Val Δ) :=
      fix inst_env {Δ} E :=
        match E with
        | [] => Some []
        | @env.snoc _ _ Γ E σ t =>
            v  <- inst_eterm ι t;;
            vs <- inst_env E;;
            Some (vs ► (σ ↦ v))
        end.

    Fixpoint inst_eformula (ι : list { σ : Ty & Val σ}) (f : EFormula) : option Prop :=
      match f with
      | @eformula_user p ts     => vs <- inst_env ι ts ;; Some (env.uncurry (𝑷_inst p) vs)
      | eformula_bool t         => b  <- inst_eterm ι t ;;
                                   Some (b = true)
      | @eformula_prop Σ' ζ P   => vs <- inst_namedenv ι ζ ;;
                                   Some (uncurry_named P vs)
      | eformula_relop op t1 t2 => v1 <- inst_eterm ι t1 ;;
                                   v2 <- inst_eterm ι t2 ;;
                                   Some (bop.eval_relop_prop op v1 v2)
      | eformula_true           => Some True
      | eformula_false          => Some False
      | eformula_and F1 F2      => p1 <- inst_eformula ι F1;;
                                   p2 <- inst_eformula ι F2;;
                                   Some (p1 /\ p2)
      | eformula_or F1 F2       => p1 <- inst_eformula ι F1;;
                                   p2 <- inst_eformula ι F2;;
                                   Some (p1 \/ p2)
      end.

    Definition inst_eformula' (ι : list { σ : Ty & Val σ}) (f : EFormula) : Prop :=
      option_rect (fun _ => Prop) (fun p => p) False (inst_eformula ι f).
    #[global] Arguments inst_eformula' !_ !_ /.

    Fixpoint list_remove {A} (xs : list A) (n : nat) : list A :=
      match xs with
      | nil       => nil
      | cons x xs => match n with
                     | O   => xs
                     | S n => cons x (list_remove xs n)
                     end
      end.

    Definition inst_eq {σ} (o1 o2 : option (Val σ)) : Prop :=
      match o1 , o2 with
      | Some v1 , Some v2 => v1 = v2
      | _       , _       => False
      end.

    Fixpoint inst_symprop (ι : list { σ : Ty & Val σ}) (f : ESymProp) : Prop :=
      match f with
      | eangelic_binary p1 p2 => inst_symprop ι p1 \/ inst_symprop ι p2
      | edemonic_binary p1 p2 => inst_symprop ι p1 /\ inst_symprop ι p2
      | eerror => False
      | eblock => True
      | eassertk fml k => inst_eformula' ι fml /\ inst_symprop ι k
      | eassumek fml k => inst_eformula' ι fml -> inst_symprop ι k
      | eangelicv b k => exists v : Val (type b), inst_symprop (cons (existT (type b) v) ι) k
      | edemonicv b k => forall v : Val (type b), inst_symprop (cons (existT (type b) v) ι) k
      | eassert_vareq x n t k =>
          let ι' := list_remove ι n in
          inst_eq (inst_eterm ι (eterm_var x _ n)) (inst_eterm ι' t) /\
          inst_symprop ι' k
      | eassume_vareq x n t k =>
          let ι' := list_remove ι n in
          inst_eq (inst_eterm ι (eterm_var x _ n)) (inst_eterm ι' t) ->
          inst_symprop ι' k
      | epattern_match s pat rhs =>
          match inst_eterm ι s with
          | Some v => let (c,ι__pat) := pattern_match_val pat v in
                      inst_symprop (app (erase_valuation ι__pat) ι) (rhs c)
          | None   => False
          end
      | epattern_match_var x n pat rhs =>
          match inst_eterm ι (eterm_var x _ n) with
          | Some v => let ι'       := list_remove ι n in
                      let (c,ι__pat) := pattern_match_val pat v in
                      inst_symprop (app (erase_valuation ι__pat) ι') (rhs c)
          | None   => False
          end
      | edebug _ k => inst_symprop ι k
      end.

    Lemma erase_valuation_remove {Σ b} (bIn : b ∈ Σ) (ι : Valuation Σ) :
      list_remove (erase_valuation ι) (ctx.in_at bIn) =
      erase_valuation (env.remove b ι bIn).
    Proof. induction ι; destruct (ctx.view bIn); cbn; now f_equal. Qed.

    Lemma erase_valuation_cat {Σ1 Σ2} (ι1 : Valuation Σ1) (ι2 : Valuation Σ2) :
      app (erase_valuation ι2) (erase_valuation ι1) =
      erase_valuation (ι1 ►► ι2).
    Proof. induction ι2; cbn; now f_equal. Qed.

    Lemma nth_error_erase {Σ b} (ι : Valuation Σ) (bIn : b ∈ Σ) :
      nth_error (erase_valuation ι) (ctx.in_at bIn) =
      Some (existT (type b) (env.lookup ι bIn)).
    Proof. induction ι; destruct (ctx.view bIn); cbn; now f_equal. Qed.

    Lemma inst_eterm_erase {Σ σ} (t : Term Σ σ) (ι : Valuation Σ) :
      inst_eterm (erase_valuation ι) (erase_term t) = Some (inst t ι).
    Proof.
      induction t; cbn [inst_eterm erase_term].
      - rewrite nth_error_erase; cbn.
        now rewrite EqDec.eq_dec_refl.
      - reflexivity.
      - now rewrite IHt1, IHt2.
      - now rewrite IHt.
      - cbn. apply option.map_eq_some.
        induction IH as [|Δ E σ t _ IHE IHt]; cbn in *.
        + reflexivity.
        + now rewrite IHt, IHE.
      - now rewrite IHt.
      - cbn. apply option.map_eq_some.
        induction IH as [|Δ E [x σ] t _ IHE IHt]; cbn in *.
        + reflexivity.
        + now rewrite IHt, IHE.
    Qed.

    Lemma inst_env_erase {Σ Δ} (ts : Env (Term Σ) Δ) (ι : Valuation Σ) :
      inst_env (erase_valuation ι) (env.map (@erase_term Σ) ts) = Some (inst ts ι).
    Proof.
      induction ts; cbn.
      - reflexivity.
      - now rewrite inst_eterm_erase, IHts.
    Qed.

    Lemma inst_namedenv_erase {Σ N} {Δ : NCtx N Ty} (ts : NamedEnv (Term Σ) Δ) (ι : Valuation Σ) :
      inst_namedenv (erase_valuation ι) (env.map (fun _ => erase_term) ts) = Some (inst ts ι).
    Proof.
      unfold inst_namedenv.
      induction ts as [|Δ ts IHts [x σ]]; cbn.
      - reflexivity.
      - now rewrite inst_eterm_erase, IHts.
    Qed.

    Lemma inst_eformula_erase {Σ} (fml : Formula Σ) (ι : Valuation Σ) :
      inst_eformula (erase_valuation ι) (erase_formula fml) = Some (instprop fml ι).
    Proof.
      induction fml;
        repeat
          (try progress cbn;
           try rewrite ?inst_eterm_erase, ?inst_env_erase, ?inst_namedenv_erase;
           try match goal with H: ?x = Some _ |- context[?x] => rewrite H end); auto.
    Qed.

    Lemma erase_safe {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      inst_symprop (erase_valuation ι) (erase_symprop p) <->
      safe p ι.
    Proof.
      induction p; cbn [inst_symprop erase_symprop safe]; unfold inst_eformula'.
      - apply Morphisms_Prop.or_iff_morphism. auto. auto.
      - apply Morphisms_Prop.and_iff_morphism. auto. auto.
      - reflexivity.
      - reflexivity.
      - apply Morphisms_Prop.and_iff_morphism.
        + now rewrite inst_eformula_erase.
        + auto.
      - apply Morphisms_Prop.iff_iff_iff_impl_morphism.
        + now rewrite inst_eformula_erase.
        + auto.
      - apply ex_iff_morphism. intros v. apply (IHp (env.snoc ι b v)).
      - apply all_iff_morphism. intros v. apply (IHp (env.snoc ι b v)).
      - change (eterm_var x σ (ctx.in_at xIn)) with (erase_term (term_var x)).
        rewrite erase_valuation_remove, !inst_eterm_erase.
        now apply Morphisms_Prop.and_iff_morphism.
      - change (eterm_var x σ (ctx.in_at xIn)) with (erase_term (term_var x)).
        rewrite erase_valuation_remove, !inst_eterm_erase.
        now apply Morphisms_Prop.iff_iff_iff_impl_morphism.
      - rewrite inst_eterm_erase. destruct pattern_match_val as [pc ι__pat].
        now rewrite erase_valuation_cat.
      - change (eterm_var x σ (ctx.in_at xIn)) with (erase_term (term_var x)).
        rewrite inst_eterm_erase. cbn. destruct pattern_match_val as [pc ι__pat].
        rewrite erase_valuation_remove, erase_valuation_cat.
        now rewrite env.cat_remove_left, erase_valuation_eq_rect.
      - apply IHp.
    Qed.

    Lemma erase_safe' {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      inst_symprop (erase_valuation ι) (erase_symprop p) ->
      safe p ι.
    Proof. apply erase_safe. Qed.

    #[global] Arguments eterm_var _ {_ _}.

    Module notations.

      Notation "x" := (eterm_var x%string) (at level 1, only printing).
      Notation "s = t" := (eformula_relop bop.eq s t) (only printing).
      Notation "s <> t" := (eformula_relop bop.neq s t) (only printing).
      Notation "s <= t" := (eformula_relop bop.le s t) (only printing).
      Notation "s < t" := (eformula_relop bop.lt s t) (only printing).

      Notation "x" := (eterm_val _ x) (at level 1, only printing).
      Notation "F ∧ P" := (eassertk F P) (only printing, format "'[v' F  ∧ '/ ' P ']'").
      Notation "F → P" := (eassumek F P) (only printing, format "'[v' F  → '/ ' P ']'").
      Notation "'∃' x '∷' σ , P" := (eangelicv (x ∷ σ) P) (at level 10, P at level 200, only printing, format "'[  ' '[  ' '∃'  x '∷' σ ']' ,  '/' P ']'").
      Notation "'∀' x '∷' σ , P" := (edemonicv (x ∷ σ) P) (at level 10, P at level 200, only printing, format "'[  ' '[  ' '∀'  x '∷' σ ']' ,  '/' P ']'").
      Notation "x ↦ t ∧ k" := (eassert_vareq x _ t k) (at level 99, right associativity, only printing).
      Notation "x ↦ t → k" := (eassume_vareq x _ t k) (at level 99, right associativity, only printing).
      Notation "P ∧ Q" := (edemonic_binary P Q) (at level 80, right associativity, only printing).
      Notation "P ∧ Q" := (eformula_and P Q) (at level 80, right associativity, only printing).
      Notation "P ∨ Q" := (eangelic_binary P Q) (at level 85, right associativity, only printing).
      Notation "P ∨ Q" := (eformula_or P Q) (at level 85, right associativity, only printing).
      Notation "⊤" := (eblock) (only printing).
      Notation "⊥" := (eerror) (only printing).

      Notation "e1 + e2"  := (eterm_binop bop.plus e1 e2) (only printing).
      Notation "e1 * e2"  := (eterm_binop bop.times e1 e2) (only printing).
      Notation "e1 +ᵇ e2" := (eterm_binop bop.bvadd e1 e2) (only printing).
      Notation "e1 -ᵇ e2" := (eterm_binop bop.bvsub e1 e2) (only printing).
      Notation "e1 *ᵇ e2" := (eterm_binop bop.bvmul e1 e2) (only printing).

      Notation "e1 >=ᵘ e2" := (eformula_relop bop.bvule e2 e1) (only printing).
      Notation "e1 >ᵘ e2" := (eformula_relop bop.bvult e2 e1) (only printing).
      Notation "e1 <=ᵘ e2" := (eformula_relop bop.bvule e1 e2) (only printing).
      Notation "e1 <ᵘ e2" := (eformula_relop bop.bvult e1 e2) (only printing).

    End notations.

  End Erasure.

End SymPropOn.

Module Type LogSymPropOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P)
  (Import SP : SymPropOn B P W)
  (Import UL : UnifLogicOn B P W).

  Module LogicalSoundness.
    Import iris.bi.interface iris.proofmode.tactics.
    Import SymProp.
    Import ModalNotations.
    Import proofmode logicalrelation.

    Lemma inst_triangular_knowing {w0 w1} (ζ : Tri w0 w1) :
      (inst_triangular ζ : Pred w0) ⊣⊢ knowing (acc_triangular ζ) True%I. 
    Proof.
      unfold knowing; crushPredEntails3.
      - exists (inst (sub_triangular_inv ζ) ι).
        rewrite sub_acc_triangular inst_triangular_right_inverse; last done.
        now intuition (eapply entails_triangular_inv).
      - rewrite <-H0, sub_acc_triangular.
        eapply inst_triangular_valid.
    Qed.

    (* logical version of wsafe *)
    Fixpoint psafe {w : World} (p : SymProp w) : Pred w :=
      (match p with
       | angelic_binary o1 o2 => psafe o1 ∨ psafe o2
       | demonic_binary o1 o2 => psafe o1 ∗ psafe o2
       | error msg => False
       | SymProp.block => True
       | assertk fml msg o =>
           (Obligation msg fml : Pred w) ∗ psafe (w := wformula w fml) o
       | assumek fml o => instpred fml -∗ (psafe (w := wformula w fml) o : Pred w)
       | angelicv b k => knowing (w1 := wsnoc w b) acc_snoc_right (@psafe (wsnoc w b) k)
       | demonicv b k => assuming (w1 := wsnoc w b) acc_snoc_right (@psafe (wsnoc w b) k)
       | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
           Obligation (subst msg ζ) (formula_relop bop.eq (term_var x) (subst t ζ)) : Pred w) ∗
            assuming (w1 := wsubst w x t) (acc_subst_right t) (psafe (w := wsubst w x t) k)
       | @assume_vareq _ x σ xIn t k =>
           (* eqₚ (term_var x (ςInΣ := xIn)) (subst t (sub_shift xIn)) -∗ *)
           let ω := acc_subst_right t in
           assuming (w1 := wsubst w x t) ω (psafe (w := wsubst w x t) k)
       | pattern_match s pat rhs =>
           ∀ (pc : PatternCase pat),
             let wm : World := wmatch w s pat pc in
             let ω : w ⊒ wm := acc_match_right pc in
             assuming ω (psafe (w := wmatch w s pat pc) (rhs pc))
       | @pattern_match_var _ x σ xIn pat rhs =>
           ∀ (pc : PatternCase pat),
             let wmv : World := wmatchvar w xIn pat pc in
             let ω : w ⊒ wmv := acc_matchvar_right pc in
             assuming ω (@psafe wmv (rhs pc))
        | debug d k => DebugPred _ d (psafe k)
        end)%I.
    #[global] Arguments psafe {w} p ι.

    Lemma psafe_safe {w p} : psafe (w := w) p ⊣⊢ safe p.
    Proof.
      refine (SymProp_ind (fun Σ p => forall (w : World) (eq : Σ = w), (psafe (w := w) (eq_rect Σ 𝕊 p w eq) : Pred w) ⊣⊢ safe (eq_rect Σ 𝕊 p w eq)) _ _ _ _ _ _ _ _ _ _ _ _ _ p w eq_refl);
        clear; intros; subst; cbn.
      5, 6:  specialize (H (wformula w fml) eq_refl); cbn in H.
      7, 8:  specialize (H (wsnoc w b) eq_refl); cbn in H.
      9, 10: specialize (H (wsubst w x t)%ctx eq_refl); cbn in H.
      11: constructor; intros ι;
        destruct (pattern_match_val pat (inst s ι)) as [c ι__pat] eqn:Hpmv;
        specialize (H c (wmatch w s pat c) eq_refl); cbn in H.
      12: constructor; intros ι;
        destruct (pattern_match_val pat ι.[? x∷σ]) as [c ι__pat] eqn:Hpmv;
        specialize (H c (wmatchvar w xIn pat c) eq_refl); cbn in H.
      all: crushPredEntails3.
      all: repeat match goal with
        [ H : forall (x : @eq ?A ?y ?y), _ |- _ ] => specialize (H eq_refl); cbn in H
      end; crushPredEntails3.
      - now rewrite obligation_equiv in H1.
      - apply H; last done.
        split; first done.
        now rewrite obligation_equiv in H1.
      - now rewrite obligation_equiv.
      - apply H; last done.
        now split.
      - rewrite instpred_prop in H1.
        apply H; last intuition.
        now split.
      - rewrite instpred_prop in H2.
        apply H; last intuition.
        now split.
      - destruct H1 as (ι' & <- & Hpc' & Hsafe).
        destruct (env.view ι') as [ι v].
        exists v.
        apply H; cbn; now rewrite ?instprop_subst inst_sub_wk1.
      - exists (ι.[b ↦ x]).
        split.
        + apply inst_sub_wk1.
        + split; cbn.
          * now rewrite instprop_subst inst_sub_wk1.
          * apply H; last done.
            now rewrite instprop_subst inst_sub_wk1.
      - apply H; cbn.
        + now rewrite instprop_subst inst_sub_wk1.
        + apply H1; cbn; now rewrite ?instprop_subst inst_sub_wk1.
      - intros ιpast <- Hpc2.
        apply H; first done.
        destruct (env.view ιpast) as [ι v].
        specialize (H1 v); cbn in H1.
        now rewrite inst_sub_wk1 in H1.
      - rewrite <-inst_sub_shift.
        rewrite obligation_equiv in H1; cbn in H1.
        now rewrite <-inst_subst.
      - rewrite <-inst_sub_shift.
        rewrite obligation_equiv in H1; cbn in H1.
        rewrite inst_subst in H1.
        assert (instprop (wco (wsubst w x t)) (inst (sub_shift xIn) ι)).
        { rewrite instprop_subst.
          now rewrite inst_sub_single_shift.
        }
        apply H; first done.
        apply H2; last done.
        now rewrite inst_sub_single_shift.
      - rewrite obligation_equiv.
        cbn.
        now rewrite inst_subst inst_sub_shift.
      - intros ιpast <- Hpc2.
        apply H; first done.
        cbn in H2.
        now rewrite <-inst_sub_shift, <-inst_subst, sub_comp_shift_single, inst_sub_id in H2.
      - rewrite <-inst_sub_shift.
        rewrite <-inst_sub_shift in H2.
        assert (instprop (wco (wsubst w x t)) (inst (sub_shift xIn) ι)).
        { rewrite instprop_subst.
          now rewrite inst_sub_single_shift.
        }
        apply H; first done.
        apply H1; last done.
        now rewrite inst_sub_single_shift.
      - intros ιpast <- Hpc.
        apply H; first done.
        rewrite <-inst_sub_shift in H1.
        rewrite <-!inst_subst in H1.
        rewrite sub_comp_shift_single inst_sub_id in H1.
        apply H1.
        rewrite <-inst_lookup.
        rewrite lookup_sub_single_eq.
        rewrite <-subst_sub_comp.
        now rewrite sub_comp_shift_single subst_sub_id.
      - assert (instprop (wco (wmatch w s pat c)) (ι ►► ι__pat)).
        { cbn. split.
          + change (instprop_ctx ?z ?ι) with (instprop z ι).
            now rewrite instprop_subst inst_sub_cat_left.
          + rewrite inst_subst inst_sub_cat_left.
            rewrite inst_pattern_match_term_reverse inst_sub_cat_right.
            apply (f_equal (pattern_match_val_reverse' pat)) in Hpmv.
            now rewrite pattern_match_val_inverse_left in Hpmv.
        }
        apply H; first done.
        apply H1; try done.
        * apply inst_sub_cat_left.
      - unfold assuming; crushPredEntails3.
        env.destroy ιpast.
        rewrite inst_sub_cat_left in H2; subst.
        rewrite inst_subst in H4.
        rewrite instprop_subst in H3.
        rewrite inst_sub_cat_left in H3,H4.
        rewrite inst_pattern_match_term_reverse in H4.
        rewrite inst_sub_cat_right in H4.
        apply (f_equal (pattern_match_val pat)) in H4.
        rewrite pattern_match_val_inverse_right in H4.
        rewrite Hpmv in H4; dependent elimination H4; subst.
        apply H; last done.
        cbn. split.
        + now rewrite instprop_subst inst_sub_cat_left.
        + rewrite inst_subst inst_sub_cat_left.
          rewrite inst_pattern_match_term_reverse inst_sub_cat_right.
          apply (f_equal (pattern_match_val_reverse' pat)) in Hpmv.
          now rewrite pattern_match_val_inverse_left in Hpmv.
      - rewrite <-inst_sub_shift.
        assert (inst (pattern_match_term_reverse pat c (eq_rect (w - x∷σ ▻▻ PatternCaseCtx c) (fun w => NamedEnv (Term w) (PatternCaseCtx c)) (sub_cat_right (PatternCaseCtx c)) ((w ▻▻ PatternCaseCtx c) - x∷σ)%ctx (eq_sym (ctx.remove_in_cat_left xIn)))) (inst (sub_shift (ctx.in_cat_left (PatternCaseCtx c) xIn)) (ι ►► ι__pat)) = env.lookup (ι ►► ι__pat) (ctx.in_cat_left _ xIn)).
        { rewrite inst_pattern_match_term_reverse.
          rewrite inst_eq_rect.
          rewrite eq_sym_involutive.
          rewrite inst_sub_shift.
          change (wcat w (PatternCaseCtx c) : LCtx) with (ctx.cat w (PatternCaseCtx c)).
          change (fun Σ => Env (fun xt => Val (type xt)) Σ) with (@Env (Binding LVar Ty) (fun xt => Val (type xt))).
          rewrite <-(env.cat_remove_left xIn ι ι__pat).
          rewrite inst_sub_cat_right.
          rewrite env.lookup_cat_left.
          apply (f_equal (pattern_match_val_reverse' pat)) in Hpmv.
          now rewrite pattern_match_val_inverse_left in Hpmv.
        }
        assert (instprop (wco (wmatchvar w xIn pat c)) (inst (sub_shift (ctx.in_cat_left (PatternCaseCtx c) xIn)) (ι ►► ι__pat))).
        { rewrite !instprop_subst.
          rewrite inst_sub_single_shift; last done.
          now rewrite inst_sub_cat_left.
        }
        apply H; first done.
        apply H1; last done.
        cbn.
        rewrite inst_subst.
        rewrite inst_sub_single_shift; last done.
        now rewrite inst_sub_cat_left.
      - unfold assuming. crushPredEntails3.
        rewrite inst_subst in H2.
        pose proof (f_equal (fun ι => env.lookup ι xIn) H2) as Hlkp.
        rewrite inst_sub_single2 -inst_lookup env.lookup_tabulate in Hlkp.
        cbn in Hlkp.
        rewrite env.lookup_insert inst_pattern_match_term_reverse in Hlkp.
        apply (f_equal (pattern_match_val pat)) in Hlkp.
        rewrite pattern_match_val_inverse_right Hpmv in Hlkp.
        dependent elimination Hlkp.
        set (ι__pat := inst (wmatchvar_patternvars a) ιpast).
        assert (eq_rect ((w ▻▻ PatternCaseCtx a) - x∷σ)%ctx (λ Σ : LCtx, Valuation Σ) (env.remove (x∷σ) (ι ►► ι__pat) (ctx.in_cat_left (PatternCaseCtx a) xIn)) (w - x∷σ ▻▻ PatternCaseCtx a) (ctx.remove_in_cat_left xIn) = env.remove (x∷σ) ι xIn ►► ι__pat) as Hremcat.
        { change (wcat w (PatternCaseCtx a) : LCtx) with (ctx.cat w (PatternCaseCtx a)).
          change (fun Σ => Env (fun xt => Val (type xt)) Σ) with (@Env (Binding LVar Ty) (fun xt => Val (type xt))).
          now rewrite <-(env.cat_remove_left xIn ι ι__pat).
        }
        assert (inst (sub_cat_right (PatternCaseCtx a)) (eq_rect ((w ▻▻ PatternCaseCtx a) - x∷σ)%ctx (λ Σ : LCtx, Valuation Σ) (inst (sub_shift (ctx.in_cat_left (PatternCaseCtx a) xIn)) (ι ►► ι__pat)) (w - x∷σ ▻▻ PatternCaseCtx a) (ctx.remove_in_cat_left xIn)) = ι__pat).
        { rewrite inst_sub_shift.
          rewrite Hremcat.
          now rewrite inst_sub_cat_right.
        }
        apply (f_equal (pattern_match_val_reverse' pat)) in Hpmv.
        rewrite pattern_match_val_inverse_left in Hpmv.
        unfold pattern_match_val_reverse' in Hpmv; cbn in Hpmv.
        assert (inst (pattern_match_term_reverse pat a (eq_rect (w - x∷σ ▻▻ PatternCaseCtx a) (fun w => NamedEnv (Term w) (PatternCaseCtx a)) (sub_cat_right (PatternCaseCtx a)) ((w ▻▻ PatternCaseCtx a) - x∷σ)%ctx (eq_sym (ctx.remove_in_cat_left xIn)))) (inst (sub_shift (ctx.in_cat_left (PatternCaseCtx a) xIn)) (ι ►► ι__pat)) = ι.[? x∷σ]).
        { rewrite inst_pattern_match_term_reverse.
          rewrite inst_eq_rect.
          rewrite eq_sym_involutive.
          now rewrite H4.
        }
        assert (instprop (wco (wmatchvar w xIn pat a)) (inst (sub_shift (ctx.in_cat_left (PatternCaseCtx a) xIn)) (ι ►► ι__pat))).
        { rewrite !instprop_subst.
          rewrite inst_sub_single_shift.
          + now rewrite inst_sub_cat_left.
          + now rewrite env.lookup_cat_left.
        }
        apply H; first done.
        replace ιpast with (env.remove (x∷σ) (ι ►► ι__pat) (ctx.in_cat_left (PatternCaseCtx a) xIn)); first done.
        rewrite env.remove_cat_left.
        rewrite <-H2.
        rewrite inst_sub_cat_left_drop.
        rewrite env.remove_drop.
        rewrite inst_sub_single2.
        rewrite env.remove_insert.
        unfold ι__pat.
        unfold wmatchvar_patternvars.
        rewrite inst_eq_rect.
        rewrite eq_sym_involutive.
        rewrite inst_sub_cat_right_take.
        rewrite env.drop_take.
        now rewrite eq_rect_sym1.
      - now destruct H1.
      - now constructor.
    Qed.


    #[export] Instance proper_psafe: ∀ {w : World}, Proper (sequiv w ==> entails (w := w)) psafe.
    Proof.
      intros w P sP HP.
      rewrite !psafe_safe.
      constructor.
      intros.
      now apply HP.
    Qed.

    (* Relatedness of symbolic and shallow propositions. The driving base case! *)
    Definition RProp : Rel SymProp Prop :=
      MkRel (fun P w SP => (psafe SP -∗ ⌜ P ⌝)%I).
    Arguments RProp : simpl never.
    #[export] Instance intowand_rprop {P w SP} :
      IntoWand false false (RSat RProp P SP) (psafe (w := w) SP) (⌜ P ⌝).
    Proof.
      unfold IntoWand, RProp; now cbn.
    Qed.

    Section logicalrelation.
      Import SymProp logicalrelation logicalrelation.notations.

      Lemma refine_symprop_debug {w : World} PC PS (msg : AMessage w) :
        ⊢ ℛ⟦RProp⟧ PC PS -∗ ℛ⟦RProp⟧ PC (debug msg PS).
      Proof.
        iIntros "HP HPS". cbn.
        iDestruct (elim_debugPred with "HPS") as "HPS".
        iApply ("HP" with "HPS").
      Qed.

      Lemma refine_symprop_angelic_binary {w : World} :
        ⊢ ℛ⟦RProp -> RProp -> RProp⟧ (@or) (@angelic_binary w).
      Proof.
        iIntros (PC1 PS1) "#HP1 %PC2 %PS2 #HP2 [#HPS1 | #HPS2]"; cbn.
        - iLeft. now iApply "HP1".
        - iRight. now iApply "HP2".
      Qed.

      Lemma refine_symprop_demonic_binary {w : World} :
        ⊢ ℛ⟦RProp -> RProp -> RProp⟧ (@and) (@demonic_binary w).
      Proof.
        iIntros (PC1 PS1) "#HP1 %PC2 %PS2 #HP2 [#HPS1 #HPS2]"; cbn.
        iSplitL "HP1 HPS1".
        - now iApply "HP1".
        - now iApply "HP2".
      Qed.

      Global Instance frompure_RProp_block {w} {P} :
        FromPure false (RSat RProp P (w := w) SymProp.block) P.
      Proof. now constructor. Qed.

    End logicalrelation.
    Notation "'ℙ'" := (RProp) : rel_scope.

  End LogicalSoundness.

  Import iris.bi.interface iris.proofmode.tactics.
  Import SymProp.
  Import logicalrelation.notations.
  Import proofmode.

  End LogSymPropOn.
