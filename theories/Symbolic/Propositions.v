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
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     NArith.NArith
     Relations.Relation_Definitions
     Strings.String.

From Katamaran Require Import
     Base
     Notations
     Prelude
     Symbolic.Worlds
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
  (Import B    : Base)
  (Import PK   : PredicateKit B)
  (Import FML  : FormulasOn B PK)
  (Import CHK  : ChunksOn B PK)
  (Import WRLD : WorldsOn B PK FML).

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

    Global Instance SubstMessage : Subst Message :=
      fun Σ1 msg Σ2 ζ12 =>
        match msg with
        | MkMessage f m Γ δ h pc => MkMessage f m Γ (subst δ ζ12) (subst h ζ12) (subst pc ζ12)
        end.

    Global Instance SubstLawsMessage : SubstLaws Message.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Import option.notations.
    Global Instance OccursCheckMessage : OccursCheck Message :=
      fun Σ x xIn msg =>
        match msg with
        | MkMessage f m Γ δ h pc =>
            δ'  <- occurs_check xIn δ;;
            h'  <- occurs_check xIn h;;
            pc' <- occurs_check xIn pc;;
            Some (MkMessage f m Γ δ' h' pc')
        end.

    Inductive Error (Σ : LCtx) (msg : Message Σ) : Prop :=.

    Inductive AMessage (Σ : LCtx) : Type :=
    | MkAMessage {BT} {subB : Subst BT} {sublawsB : SubstLaws BT} {occB: OccursCheck BT} : BT Σ -> AMessage Σ
    .

    Global Instance SubstAMessage : Subst AMessage :=
      fun Σ1 msg Σ2 ζ12 =>
        match msg with
        | @MkAMessage _ BT subB sublB occB msg => MkAMessage _ (subst msg ζ12)
        end.

    Global Instance SubstLawsAMessage : SubstLaws AMessage.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    Global Instance OccursCheckAMessage : OccursCheck AMessage :=
      fun Σ x xIn msg =>
        match msg with
        | MkAMessage _ msg =>
            msg' <- occurs_check xIn msg;;
            Some (MkAMessage _ msg')
        end.

  End Messages.

  Inductive Obligation {Σ} (msg : AMessage Σ) (fml : Formula Σ) (ι : Valuation Σ) : Prop :=
  | obligation (p : inst fml ι : Prop).

  Inductive Debug {B : LCtx -> Type} {Σ : LCtx} (b : B Σ) (P : Prop) : Prop :=
  | debug (p : P).

  Module SymProp.

    Inductive EMessage (Σ : LCtx) : Type :=
    | EMsgHere {M} {subM : Subst M} {occM: OccursCheck M} (msg : M Σ)
    | EMsgThere {b} (msg : EMessage (Σ ▻ b)).
    Global Arguments EMsgHere {_ _ _ _} msg.

    Fixpoint emsg_close {Σ ΣΔ} {struct ΣΔ} : EMessage (Σ ▻▻ ΣΔ) -> EMessage Σ :=
      match ΣΔ with
      | []      => fun msg => msg
      | ΣΔ  ▻ b => fun msg => emsg_close (EMsgThere msg)
      end%ctx.

    Fixpoint shift_emsg {Σ b} (bIn : b ∈ Σ) (emsg : EMessage (Σ - b)) : EMessage Σ :=
      match emsg with
      | EMsgHere msg   => EMsgHere (subst msg (sub_shift bIn))
      | EMsgThere emsg => EMsgThere (shift_emsg (ctx.in_succ bIn) emsg)
      end.

    Inductive SymProp (Σ : LCtx) : Type :=
    | angelic_binary (o1 o2 : SymProp Σ)
    | demonic_binary (o1 o2 : SymProp Σ)
    | error (msg : EMessage Σ)
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

    (* Global Instance persistent_spath : Persistent 𝕊 := *)
    (*   (* ⊢ 𝕊 -> □𝕊 := *) *)
    (*    fix pers (w0 : World) (p : 𝕊 w0) {w1 : World} ω01 {struct p} : 𝕊 w1 := *)
    (*      match p with *)
    (*      | angelic_binary p1 p2 => angelic_binary (pers w0 p1 ω01) (pers w0 p2 ω01) *)
    (*      | demonic_binary p1 p2 => demonic_binary (pers w0 p1 ω01) (pers w0 p2 ω01) *)
    (*      | error msg            => error (subst msg (sub_acc ω01)) *)
    (*      | block                => block *)
    (*      | assertk fml msg p0   => *)
    (*          assertk (subst fml (sub_acc ω01)) (subst msg (sub_acc ω01)) *)
    (*            (pers (wformula w0 fml) p0 (wacc_formula ω01 fml)) *)
    (*      | assumek fml p        => *)
    (*          assumek (subst fml (sub_acc ω01)) *)
    (*            (pers (wformula w0 fml) p (wacc_formula ω01 fml)) *)
    (*      | angelicv b p0        => angelicv b (pers (wsnoc w0 b) p0 (wacc_snoc ω01 b)) *)
    (*      | demonicv b p0        => demonicv b (pers (wsnoc w0 b) p0 (wacc_snoc ω01 b)) *)
    (*      | assert_vareq x t msg p => *)
    (*        let ζ := subst (sub_shift _) (sub_acc ω01) in *)
    (*        assertk *)
    (*          (formula_eq (env_lookup (sub_acc ω01) _) (subst t ζ)) *)
    (*          (subst msg ζ) *)
    (*          (pers (wsubst w0 x t) p *)
    (*             (MkAcc (MkWorld (subst (wco w0) (sub_single _ t))) *)
    (*                (MkWorld *)
    (*                   (cons (formula_eq (env_lookup (sub_acc ω01) _) (subst t ζ)) *)
    (*                      (wco w1))) ζ)) *)
    (*      | assume_vareq x t p => *)
    (*        let ζ := subst (sub_shift _) (sub_acc ω01) in *)
    (*        assumek *)
    (*          (formula_eq (env_lookup (sub_acc ω01) _) (subst t ζ)) *)
    (*          (pers (wsubst w0 x t) p *)
    (*             (MkAcc (MkWorld (subst (wco w0) (sub_single _ t))) *)
    (*                (MkWorld *)
    (*                   (cons (formula_eq (env_lookup (sub_acc ω01) _) (subst t ζ)) *)
    (*                      (wco w1))) ζ)) *)
    (*      | debug d p => debug (subst d (sub_acc ω01)) (pers w0 p ω01) *)
    (*      end. *)

    Fixpoint assume_formulas_without_solver' {Σ}
      (fmls : List Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match fmls with
      | nil           => p
      | cons fml fmls => assume_formulas_without_solver' fmls (assumek fml p)
      end.

    Fixpoint assert_formulas_without_solver' {Σ}
      (msg : AMessage Σ) (fmls : List Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match fmls with
      | nil => p
      | cons fml fmls =>
        assert_formulas_without_solver' msg fmls (assertk fml msg p)
      end.

    (* These versions just add the world indexing. They simply enforces *)
(*        that p should have been computed in the world with fmls added. *)
    Definition assume_formulas_without_solver {w : World}
      (fmls : List Formula w) (p : 𝕊 (wformulas w fmls)) : 𝕊 w :=
      assume_formulas_without_solver' fmls p.
    Global Arguments assume_formulas_without_solver {_} fmls p.

    Definition assert_formulas_without_solver {w : World} (msg : AMessage w)
      (fmls : List Formula w) (p : 𝕊 (wformulas w fmls)) : 𝕊 w :=
      assert_formulas_without_solver' msg fmls p.
    Global Arguments assert_formulas_without_solver {_} msg fmls p.

    Fixpoint assume_triangular {w1 w2} (ν : Tri w1 w2) :
      𝕊 w2 -> 𝕊 w1.
    Proof.
      destruct ν; intros o; cbn in o.
      - exact o.
      - apply (@assume_vareq w1 x σ xIn t).
        eapply (assume_triangular _ _ ν o).
    Defined.

    Fixpoint assert_triangular {w1 w2} (msg : AMessage (wctx w1)) (ζ : Tri w1 w2) :
      (AMessage w2 -> 𝕊 w2) -> 𝕊 w1.
    Proof.
      destruct ζ; intros o; cbn in o.
      - apply o. apply msg.
      - apply (@assert_vareq w1 x σ xIn t).
        apply (subst msg (sub_single xIn t)).
        refine (assert_triangular (wsubst w1 x t) _ (subst msg (sub_single xIn t)) ζ o).
    Defined.

    Fixpoint safe {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) : Prop :=
      (* ⊢ 𝕊 -> Valuation -> PROP := *)
        match p with
        | angelic_binary o1 o2 => safe o1 ι \/ safe o2 ι
        | demonic_binary o1 o2 => safe o1 ι /\ safe o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          inst fml ι /\ safe o ι
        | assumek fml o => (inst fml ι : Prop) -> safe o ι
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
        | debug d k => safe k ι
        end%type.
    Global Arguments safe {Σ} p ι.

    Fixpoint safe_debug {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) : Prop :=
      (* ⊢ 𝕊 -> Valuation -> PROP := *)
        match p with
        | angelic_binary o1 o2 => safe_debug o1 ι \/ safe_debug o2 ι
        | demonic_binary o1 o2 => safe_debug o1 ι /\ safe_debug o2 ι
        | error msg => False
        | block => True
        | assertk fml msg o =>
          Obligation msg fml ι /\ safe_debug o ι
        | assumek fml o => (inst fml ι : Prop) -> safe_debug o ι
        | angelicv b k => exists v, safe_debug k (env.snoc ι b v)
        | demonicv b k => forall v, safe_debug k (env.snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env.remove (x∷σ) ι xIn in
          safe_debug k ι')
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' ->
          safe_debug k ι'
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
        | assumek fml o => (inst fml ι : Prop) -> @wsafe (wformula w fml) o ι
        | angelicv b k => exists v, @wsafe (wsnoc w b) k (env.snoc ι b v)
        | demonicv b k => forall v, @wsafe (wsnoc w b) k (env.snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env.remove (x∷σ) ι xIn in
          @wsafe (wsubst w x t) k ι')
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' ->
          @wsafe (wsubst w x t) k ι'
        | debug d k => Debug d (wsafe k ι)
        end%type.
    Global Arguments wsafe {w} p ι.

    Lemma obligation_equiv {Σ : LCtx} (msg : AMessage Σ) (fml : Formula Σ) (ι : Valuation Σ) :
      Obligation msg fml ι <-> inst fml ι.
    Proof. split. now intros []. now constructor. Qed.

    Lemma debug_equiv {B : LCtx -> Type} {Σ} {b : B Σ} {P : Prop} :
      @Debug B _ b P <-> P.
    Proof. split. now intros []. now constructor. Qed.

    Lemma wsafe_safe {w : World} (p : 𝕊 w) (ι : Valuation w) :
      wsafe p ι <-> safe_debug p ι.
    Proof.
      destruct w as [Σ pc]; cbn in *; revert pc.
      induction p; cbn; intros pc; rewrite ?debug_equiv; auto;
        try (intuition; fail).
      apply base.exist_proper; eauto.
    Qed.

    Lemma safe_debug_safe {Σ : LCtx} (p : 𝕊 Σ) (ι : Valuation Σ) :
      safe_debug p ι <-> safe p ι.
    Proof.
      induction p; cbn; rewrite ?debug_equiv, ?obligation_equiv; auto;
        try (intuition; fail).
      apply base.exist_proper; eauto.
      apply Morphisms_Prop.and_iff_morphism; cbn; eauto.
      now rewrite inst_subst, inst_sub_shift.
    Qed.

    (* Lemma safe_persist  {w1 w2 : World} (ω12 : w1 ⊒ w2) *)
    (*       (o : 𝕊 w1) (ι2 : Valuation w2) : *)
    (*   safe (persist (A := 𝕊) o ω12) ι2 <-> *)
    (*   safe o (inst (T := Sub _) ω12 ι2). *)
    (* Proof. *)
    (*   revert w2 ω12 ι2. *)
    (*   induction o; cbn; intros. *)
    (*   - now rewrite IHo1, IHo2. *)
    (*   - now rewrite IHo1, IHo2. *)
    (*   - split; intros []. *)
    (*   - reflexivity. *)
    (*   - rewrite ?obligation_equiv. *)
    (*     now rewrite IHo, inst_subst. *)
    (*   - now rewrite IHo, inst_subst. *)
    (*   - split; intros [v HYP]; exists v; revert HYP; *)
    (*       rewrite IHo; unfold wacc_snoc, wsnoc; *)
    (*         cbn [wctx wsub]; now rewrite inst_sub_up1. *)
    (*   - split; intros HYP v; specialize (HYP v); revert HYP; *)
    (*       rewrite IHo; unfold wacc_snoc, wsnoc; *)
    (*         cbn [wctx wsub]; now rewrite inst_sub_up1. *)
    (*   - rewrite ?obligation_equiv. *)
    (*     rewrite IHo; unfold wsubst; cbn [wctx wsub]. cbn. *)
    (*     now rewrite ?inst_subst, ?inst_sub_shift, <- inst_lookup. *)
    (*   - rewrite IHo; unfold wsubst; cbn [wctx wsub]. *)
    (*     now rewrite ?inst_subst, ?inst_sub_shift, <- inst_lookup. *)
    (*   - now rewrite ?debug_equiv. *)
    (* Qed. *)

    Lemma safe_assume_formulas_without_solver {w0 : World}
      (fmls : List Formula w0) (p : 𝕊 w0) (ι0 : Valuation w0) :
      wsafe (assume_formulas_without_solver fmls p) ι0 <->
      (instpc fmls ι0 -> @wsafe (wformulas w0 fmls) p ι0).
    Proof.
      unfold assume_formulas_without_solver. revert p.
      induction fmls; cbn in *; intros p.
      - destruct w0; cbn; split; auto.
      - rewrite IHfmls. cbn. intuition.
    Qed.

    Lemma safe_assert_formulas_without_solver {w0 : World}
      (msg : AMessage w0) (fmls : List Formula w0) (p : 𝕊 w0)
      (ι0 : Valuation w0) :
      wsafe (assert_formulas_without_solver msg fmls p) ι0 <->
      (instpc fmls ι0 /\ @wsafe (wformulas w0 fmls) p ι0).
    Proof.
      unfold assert_formulas_without_solver. revert p.
      induction fmls; cbn in *; intros p.
      - destruct w0; cbn; split.
        + intros HYP. split; auto.
        + intros []; auto.
      - rewrite IHfmls; cbn.
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
          destruct (env.nilView ι).
          now cbn in *.
      - rewrite (IHΣ (angelicv b p)).
        split.
        + intros (ι & v & sp).
          now exists (env.snoc ι b v).
        + intros (ι & sp).
          destruct (env.snocView ι) as (ι & v).
          now exists ι, v.
    Qed.

    Lemma safe_demonic_close0 {Σ0 Σ} (p : 𝕊 (Σ0 ▻▻ Σ)) (ι0 : Valuation Σ0) :
      safe (demonic_close0 Σ p) ι0 <-> forall (ι : Valuation Σ), safe p (env.cat ι0 ι).
    Proof.
      induction Σ; cbn.
      - split.
        + intros s ι. now destruct (env.nilView ι).
        + intros s; apply (s env.nil).
      - rewrite (IHΣ (demonicv b p)); cbn.
        split.
        + intros sp ι. destruct (env.snocView ι) as (ι & v). cbn. auto.
        + intros sp ι v. apply (sp (env.snoc ι b v)).
    Qed.

    Definition safe_demonic_close {Σ : LCtx} (p : 𝕊 Σ) :
      safe (demonic_close p) env.nil <-> forall ι : Valuation Σ, safe p ι.
    Proof.
      induction Σ; cbn [demonic_close] in *.
      - split.
        + intros s ι. now destruct (env.nilView ι).
        + intros s. apply (s env.nil).
      - rewrite (IHΣ (demonicv b p)); cbn.
        split.
        + intros sp ι. destruct (env.snocView ι) as (ι & v). auto.
        + intros sp ι v. apply (sp (env.snoc ι b v)).
    Qed.

    (* Fixpoint occurs_check_spath {Σ x} (xIn : x ∈ Σ) (p : 𝕊 Σ) : option (𝕊 (Σ - x)) := *)
    (*   match p with *)
    (*   | angelic_binary o1 o2 => *)
    (*     option_ap (option_map (angelic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2) *)
    (*   | demonic_binary o1 o2 => *)
    (*     option_ap (option_map (demonic_binary (Σ := Σ - x)) (occurs_check_spath xIn o1)) (occurs_check_spath xIn o2) *)
    (*   | error msg => option_map error (occurs_check xIn msg) *)
    (*   | block => Some block *)
    (*   | assertk P msg o => *)
    (*     option_ap (option_ap (option_map (assertk (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check xIn msg)) (occurs_check_spath xIn o) *)
    (*   | assumek P o => option_ap (option_map (assumek (Σ := Σ - x)) (occurs_check xIn P)) (occurs_check_spath xIn o) *)
    (*   | angelicv b o => option_map (angelicv b) (occurs_check_spath (inctx_succ xIn) o) *)
    (*   | demonicv b o => option_map (demonicv b) (occurs_check_spath (inctx_succ xIn) o) *)
    (*   | @assert_vareq _ y σ yIn t msg o => *)
    (*     match occurs_check_view yIn xIn with *)
    (*     | Same _ => None *)
    (*     | @Diff _ _ _ _ x xIn => *)
    (*       option_ap *)
    (*         (option_ap *)
    (*            (option_map *)
    (*               (fun (t' : Term (Σ - (y :: σ) - x) σ) (msg' : Message (Σ - (y :: σ) - x)) (o' : 𝕊 (Σ - (y :: σ) - x)) => *)
    (*                  let e := swap_remove yIn xIn in *)
    (*                  assert_vareq *)
    (*                    y *)
    (*                    (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e) *)
    (*                    (eq_rect (Σ - (y :: σ) - x) Message msg' (Σ - x - (y :: σ)) e) *)
    (*                    (eq_rect (Σ - (y :: σ) - x) 𝕊 o' (Σ - x - (y :: σ)) e)) *)
    (*               (occurs_check xIn t)) *)
    (*            (occurs_check xIn msg)) *)
    (*         (occurs_check_spath xIn o) *)
    (*     end *)
    (*   | @assume_vareq _ y σ yIn t o => *)
    (*     match occurs_check_view yIn xIn with *)
    (*     | Same _ => Some o *)
    (*     | @Diff _ _ _ _ x xIn => *)
    (*       option_ap *)
    (*         (option_map *)
    (*            (fun (t' : Term (Σ - (y :: σ) - x) σ) (o' : 𝕊 (Σ - (y :: σ) - x)) => *)
    (*               let e := swap_remove yIn xIn in *)
    (*               assume_vareq *)
    (*                 y *)
    (*                 (eq_rect (Σ - (y :: σ) - x) (fun Σ => Term Σ σ) t' (Σ - x - (y :: σ)) e) *)
    (*                 (eq_rect (Σ - (y :: σ) - x) 𝕊 o' (Σ - x - (y :: σ)) e)) *)
    (*            (occurs_check xIn t)) *)
    (*         (occurs_check_spath xIn o) *)
    (*     end *)
    (*   | debug b o => option_ap (option_map (debug (Σ := Σ - x)) (occurs_check xIn b)) (occurs_check_spath xIn o) *)
    (*   end. *)

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

    Instance sequiv_equivalence {Σ} : Equivalence (sequiv Σ).
    Proof. split; auto using sequiv_refl, sequiv_sym, sequiv_trans. Qed.

    Definition simpl Σ : relation (𝕊 Σ) :=
      fun p q => forall ι, safe p ι -> safe q ι.
    Arguments simpl : clear implicits.
    Notation "p =>> q" := (simpl _ p q) (at level 90, no associativity).

    Definition simpl_refl {Σ} : Reflexive (simpl Σ).
    Proof. intros p ι. auto. Qed.

    Definition simpl_trans {Σ} : Transitive (simpl Σ).
    Proof. intros p q r pq qr ι. auto. Qed.

    Instance simpl_preorder {Σ} : PreOrder (simpl Σ).
    Proof. split; auto using simpl_refl, simpl_trans. Qed.

    Instance simpl_rewriterelation {Σ} : RewriteRelation (sequiv Σ).
    Defined.

    Instance proper_angelic_close0 {Σ Σe} : Proper (sequiv (Σ ▻▻ Σe) ==> sequiv Σ) (angelic_close0 Σe).
    Proof. intros p q pq ι. rewrite ?safe_angelic_close0. now apply base.exist_proper. Qed.

    Instance proper_angelic_binary {Σ} : Proper (sequiv Σ ==> sequiv Σ ==> sequiv Σ) (@angelic_binary Σ).
    Proof.
      unfold sequiv.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      now rewrite p12, q12.
    Qed.

    Instance proper_angelic_binary_impl {Σ} : Proper (simpl Σ ==> simpl Σ ==> simpl Σ) (@angelic_binary Σ).
    Proof.
      unfold simpl.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      intros []; auto.
    Qed.


    Instance proper_demonic_close0 {Σ Σu} : Proper (sequiv (Σ ▻▻ Σu) ==> sequiv Σ) (demonic_close0 Σu).
    Proof. intros p q pq ι. rewrite ?safe_demonic_close0. now apply base.forall_proper. Qed.

    Instance proper_demonic_close0_impl {Σ Σu} : Proper (simpl (Σ ▻▻ Σu) ==> simpl Σ) (demonic_close0 Σu).
    Proof.
      unfold simpl. intros p q pq ι. rewrite ?safe_demonic_close0.
      intros HYP ιu. apply pq, HYP.
    Qed.

    Instance proper_demonic_binary {Σ} : Proper (sequiv Σ ==> sequiv Σ ==> sequiv Σ) (@demonic_binary Σ).
    Proof.
      unfold sequiv.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      now rewrite p12, q12.
    Qed.

    Instance proper_demonic_binary_impl {Σ} : Proper (simpl Σ ==> simpl Σ ==> simpl Σ) (@demonic_binary Σ).
    Proof. intros p1 p2 p12 q1 q2 q12 ι. cbn. intuition. Qed.

    Instance proper_assumek {Σ} (fml : Formula Σ) : Proper (sequiv Σ ==> sequiv Σ) (assumek fml).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assertk {Σ} (fml : Formula Σ) (msg : AMessage Σ) : Proper (sequiv Σ ==> sequiv Σ) (assertk fml msg).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assertk_impl {Σ} (fml : Formula Σ) (msg : AMessage Σ) : Proper (simpl Σ ==> simpl Σ) (assertk fml msg).
    Proof. unfold simpl. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assume_vareq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      Proper (sequiv (Σ - x∷σ) ==> sequiv Σ) (assume_vareq x t).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assume_vareq_impl {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      Proper (simpl (Σ - x∷σ) ==> simpl Σ) (assume_vareq x t).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assert_vareq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (msg : AMessage (Σ - x∷σ)) :
      Proper (sequiv (Σ - x∷σ) ==> sequiv Σ) (assert_vareq x t msg).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assert_vareq_impl {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (msg : AMessage (Σ - x∷σ)) :
      Proper (simpl (Σ - x∷σ) ==> simpl Σ) (assert_vareq x t msg).
    Proof. unfold simpl. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_angelicv {Σ b} : Proper (sequiv (Σ ▻ b) ==> sequiv Σ) (angelicv b).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply base.exist_proper. Qed.

    Instance proper_angelicv_impl {Σ b} : Proper (simpl (Σ ▻ b) ==> simpl Σ) (angelicv b).
    Proof. unfold simpl. intros p q pq ι [v H]. exists v. now apply pq. Qed.

    Instance proper_demonicv {Σ b} : Proper (sequiv (Σ ▻ b) ==> sequiv Σ) (demonicv b).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply base.forall_proper. Qed.

    Instance proper_debug {Σ} {bt : AMessage Σ} :
      Proper (sequiv Σ ==> sequiv Σ) (debug bt).
    Proof. unfold sequiv. intros p q pq ι. cbn. now rewrite ?debug_equiv. Qed.

    Instance proper_debug_impl {Σ} {bt : AMessage Σ} :
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

    Module notations.
      Notation "x" := (@term_var _ x%string _ (@ctx.MkIn _ (x%string :: _) _ _ _)) (at level 1, only printing).
      Notation "s = t" := (@formula_eq _ _ s t) (only printing).
      Notation "' t" := (@formula_bool _ t) (at level 10, only printing, format "' t").
      Notation "F ∧ P" := (@SymProp.assertk _ F _ P) (only printing).
      Notation "F → P" := (@SymProp.assumek _ F P) (only printing).
      Notation "'∃' x '∷' σ , P" := (SymProp.angelicv (x ∷ σ) P) (at level 200, right associativity, only printing, format "'∃'  x '∷' σ ,  '/' P").
      Notation "'∀' x '∷' σ , P" := (SymProp.demonicv (x ∷ σ) P) (at level 200, right associativity, only printing, format "'∀'  x '∷' σ ,  '/' P").
      Notation "⊤" := (@SymProp.block _).
      Notation "x - y" := (term_binop bop.minus x y) : exp_scope.
      Notation "x + y" := (term_binop bop.plus x y) : exp_scope.
      Notation "x * y" := (term_binop bop.times x y) : exp_scope.
      Notation "x ↦ t ∧ k" := (@SymProp.assert_vareq _ x _ _ t _ k) (at level 99, right associativity, only printing).
      Notation "x ↦ t → k" := (@SymProp.assume_vareq _ x _ _ t k) (at level 99, right associativity, only printing).
      Notation "P ∧ Q" := (@SymProp.demonic_binary _ P Q) (at level 80, right associativity, only printing).
      Notation "P ∨ Q" := (@SymProp.angelic_binary _ P Q) (at level 85, right associativity, only printing).
      Notation "x < y" := (formula_lt x y) (only printing).
      Notation "x <= y" := (formula_le x y) (only printing).
      Notation "x >= y" := (formula_ge x y) (only printing).
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

      (* Definition plus_count (c1 c2 : Count) : Count := *)
      (*   match c1, c2 with *)
      (*   | {| block := b1; error := e1; debug := d1 |}, *)
      (*     {| block := b2; error := e2; debug := d2 |} => *)
      (*       {| block := b1 + b2; error := e1 + e2; debug := d1 + d2 |} *)
      (*   end. *)

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
      | error msg => error (EMsgThere msg)
      | _         => angelicv b p
      end.

    Definition demonicv_prune {Σ} b (p : 𝕊 (Σ ▻ b)) : 𝕊 Σ :=
      (* match @occurs_check_spath AT _ (Σ ▻ b) b inctx_zero o with *)
      (* | Some o => o *)
      (* | None   => demonicv b o *)
      (* end. *)
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
      | error emsg => error (shift_emsg xIn emsg)
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
      | debug d k =>
        debug d (prune k)
      end.

    Lemma prune_angelic_binary_sound {Σ} (p1 p2 : 𝕊 Σ) (ι : Valuation Σ) :
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

    Section Util.

      Lemma exists_and {A : Type} {P : A -> Prop} {Q : Prop} :
        (exists (x : A), P x /\ Q) <-> ((exists (x : A), P x) /\ Q).
      Proof. firstorder. Qed.

      Lemma safe_eq_rect {Σ Σ'} (eq : Σ = Σ') (p : 𝕊 Σ) (ι : Valuation Σ') :
        safe (eq_rect Σ 𝕊 p Σ' eq) ι = safe p (eq_rect Σ' (fun Σ => Valuation Σ) ι Σ (eq_sym eq)).
      Proof.
        now destruct eq.
      Qed.

      Lemma inst_eq_rect `{Inst AT A} {Σ Σ'} (t : AT Σ) (eq : Σ = Σ') (ι : Valuation Σ'):
        inst (eq_rect Σ AT t Σ' eq) ι = inst t (eq_rect Σ' (fun Σ => Valuation Σ) ι Σ (eq_sym eq)).
      Proof.
        now subst.
      Qed.

      Lemma eq_rect_sym1 {A : Type} {P : A -> Type} {a a' : A} (eq : a = a') (v : P a) :
        eq_rect a' P (eq_rect a P v a' eq) a (eq_sym eq) = v.
      Proof.
        now subst.
      Qed.

      Lemma eq_rect_sym2 {A : Type} {P : A -> Type} {a a' : A} (eq : a' = a) (v : P a) :
        eq_rect a' P (eq_rect a P v a' (eq_sym eq)) a eq = v.
      Proof.
        now subst.
      Qed.

      Lemma match_snocView_eq_rect {Σ1 Σ2 b} {R : Type} (eq : Σ1 = Σ2) (E : Valuation (Σ1 ▻ b))
        (f : Valuation Σ2 -> Val (type b) -> R) :
        match env.snocView (eq_rect Σ1 (fun Σ => Valuation (Σ ▻ b)) E Σ2 eq) with
        | env.isSnoc E v => f E v
        end =
        match env.snocView E with
        | env.isSnoc E v => f (eq_rect Σ1 (fun Σ => Valuation Σ) E Σ2 eq) v
        end.
      Proof.
        now destruct eq.
      Qed.

      Lemma snoc_eq_rect {Σ1 Σ2 b v} (eq : Σ1 = Σ2) (E : Valuation Σ1) :
        eq_rect Σ1 (fun Σ => Valuation Σ) E Σ2 eq ► (b ↦ v) =
        eq_rect Σ1 (fun Σ => Valuation (Σ ▻ b)) (E ► (b ↦ v)) Σ2 eq.
      Proof.
        now destruct eq.
      Qed.

      Lemma env_insert_app {x : 𝑺} {σ : Ty} {Σ0 Σe : LCtx}
            (bIn : x∷σ ∈ Σe) (v : Val σ)
            {ι : Valuation Σ0} {ιe : Valuation (Σe - x∷σ)} :
            (ι ►► env.insert bIn ιe v) =
            env.insert (ctx.in_cat_right bIn) (eq_rect (Σ0 ▻▻ Σe - x∷σ) (fun Σ => Valuation Σ) (ι ►► ιe) ((Σ0 ▻▻ Σe) - x∷σ) (eq_sym (ctx.remove_in_cat_right bIn))) v.
      Proof.
        revert bIn ιe.
        induction Σe; intros bIn ιe;
          try destruct (ctx.nilView bIn).
        cbn [env.insert ctx.remove_in_cat_right].
        (* can't destruct Contxt.snocView bIn?*)
        destruct bIn as ([|n] & eq).
        - cbn in eq.
          now subst.
        - cbn in ιe.
          destruct (env.snocView ιe) as (ιe & v').
          change (ctx.remove_in_cat_right {| ctx.in_at := S n; ctx.in_valid := eq |})
                 with (f_equal (fun f => f b) (eq_trans eq_refl (f_equal ctx.snoc (@ctx.remove_in_cat_right _ Σ0 Σe _ {| ctx.in_at := n; ctx.in_valid := eq |})))).
          rewrite eq_trans_refl_l.
          cbn.
          rewrite (eq_sym_map_distr (fun f : 𝑺 ∷ Ty -> LCtx => f b)).
          rewrite eq_sym_map_distr.
          rewrite f_equal_compose.
          rewrite (map_subst_map (P := fun x => Valuation (ctx.snoc x b)) (fun a : LCtx => a ▻ b) (fun _ x => x) ).
          rewrite match_snocView_eq_rect.
          now rewrite IHΣe.
      Qed.

      Lemma env_remove_app {x : 𝑺} {σ : Ty} {Σ0 Σe : LCtx} (bIn : x∷σ ∈ Σe)
        (ι : Valuation Σ0) (ιe : Valuation Σe) :
        env.remove (x∷σ) (ι ►► ιe) (ctx.in_cat_right bIn) =
        eq_rect (Σ0 ▻▻ Σe - x∷σ) (fun Σ : LCtx => Valuation Σ) (ι ►► env.remove (x∷σ) ιe bIn)
                 ((Σ0 ▻▻ Σe) - x∷σ) (eq_sym (ctx.remove_in_cat_right bIn)).
      Proof.
        revert bIn ιe.
        induction Σe; intros bIn ιe; try destruct (ctx.nilView bIn).
        destruct (ctx.snocView bIn).
        - now destruct (env.snocView ιe).
        - destruct (env.snocView ιe) as (ιe & v).
          change (ctx.remove_in_cat_right (ctx.in_succ i))
                 with (f_equal (fun f => f b) (eq_trans eq_refl (f_equal ctx.snoc (@ctx.remove_in_cat_right _ Σ0 Σe _ i)))).
          rewrite eq_trans_refl_l.
          cbn.
          rewrite (eq_sym_map_distr (fun f : 𝑺 ∷ Ty -> LCtx => f b)).
          rewrite eq_sym_map_distr.
          rewrite f_equal_compose.
          rewrite (map_subst_map (P := fun x => Valuation (ctx.snoc x b)) (fun a : LCtx => a ▻ b) (fun _ x => x) ).
          rewrite IHΣe.
          now rewrite snoc_eq_rect.
      Qed.

    End Util.

    Module SolveEvars.

      Fixpoint assert_msgs_formulas {Σ} (mfs : List (Pair AMessage Formula) Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
        match mfs with
        | nil => p
        | cons (msg,fml) mfs =>
          assert_msgs_formulas mfs (assertk fml msg p)
        end.

      Lemma safe_assert_msgs_formulas {Σ} {mfs : List (Pair AMessage Formula) Σ} {p : 𝕊 Σ} {ι : Valuation Σ} :
        (safe (assert_msgs_formulas mfs p) ι <-> instpc (map snd mfs) ι /\ safe p ι).
      Proof.
        revert p.
        induction mfs; intros p; cbn.
        - intuition.
        - destruct a. rewrite IHmfs. now cbn.
      Qed.

      Inductive ECtx (Σ : LCtx) : LCtx -> Type :=
      | ectx Σe (mfs : List (Pair AMessage Formula) (Σ ▻▻ Σe)) : ECtx Σ (Σ ▻▻ Σe).
      Arguments ectx {Σ} Σe mfs.

      Definition ectx_refl {Σ : LCtx} : ECtx Σ Σ := @ectx Σ ctx.nil nil.

      Definition ectx_formula {Σ1 Σ2} (e: ECtx Σ1 Σ2) : AMessage Σ2 -> Formula Σ2 -> ECtx Σ1 Σ2 :=
        match e with ectx Σe mfs => fun msg fml => ectx Σe (cons (msg,fml) mfs) end.
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

      Definition plug_msg {Σ1 Σ2} (ec : ECtx Σ1 Σ2) : EMessage Σ2 -> EMessage Σ1 :=
        match ec with ectx _ _ => emsg_close end.

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
        | debug b p              => plug ec (debug b (push ectx_refl p))
        end.

      Instance proper_assert_msgs_formulas {Σ} (mfs : List (Pair AMessage Formula) Σ) :
        Proper (sequiv Σ ==> sequiv Σ) (assert_msgs_formulas mfs).
      Proof. intros p q pq ι. rewrite ?safe_assert_msgs_formulas. intuition. Qed.

      Instance proper_plug {Σ1 Σ2} (ec : ECtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_angelic_close0, proper_assert_msgs_formulas.
      Qed.

      Lemma assert_msgs_formulas_angelic_binary {Σ} (mfs : List (Pair AMessage Formula) Σ) (p1  p2 : 𝕊 Σ) :
        assert_msgs_formulas mfs (angelic_binary p1 p2) <=>
        angelic_binary (assert_msgs_formulas mfs p1) (assert_msgs_formulas mfs p2).
      Proof.
        intros ι; cbn.
        rewrite ?safe_assert_msgs_formulas.
        cbn. intuition.
      Qed.

      Lemma map_snd_subst {Σ Σ' : LCtx} {ζ : Sub Σ Σ'}
            {mfs : List (Pair AMessage Formula) Σ} :
            map snd (subst mfs ζ) = subst (map snd mfs) ζ.
      Proof.
        induction mfs.
        - easy.
        - cbn.
          rewrite IHmfs.
          now destruct a.
      Qed.

      Lemma assert_msgs_formulas_angelicv {b Σ} (mfs : List (Pair AMessage Formula) Σ) (p : 𝕊 (Σ ▻ b)) :
        assert_msgs_formulas mfs (angelicv b p) <=>
        angelicv b (assert_msgs_formulas (subst mfs sub_wk1) p).
      Proof.
        intros ι; cbn.
        rewrite safe_assert_msgs_formulas. cbn.
        rewrite and_comm, <- exists_and.
        apply base.exist_proper. intros v.
        rewrite safe_assert_msgs_formulas.
        rewrite map_snd_subst.
        rewrite inst_subst.
        rewrite inst_sub_wk1.
        apply and_comm.
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
          rewrite env_insert_app, env.remove_insert, env.insert_lookup.
          rewrite ?inst_eq_rect.
          split; auto.
          rewrite map_snd_subst, inst_subst, inst_eq_rect in Hpc.
          now rewrite inst_sub_single2 in Hpc.
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          cbn in Hp. cbn in Hp. destruct Hp as [Ht Hp].
          rewrite env_remove_app in Hp.
          exists (env.remove (x∷σ) ιe bIn).
          rewrite safe_assert_msgs_formulas.
          rewrite map_snd_subst, inst_subst.
          unfold eq_rect_r. rewrite safe_eq_rect.
          rewrite eq_sym_involutive. split; auto.
          rewrite inst_eq_rect.
          rewrite <- env_remove_app.
          rewrite <- inst_sub_shift.
          rewrite inst_sub_single_shift; auto.
          now rewrite inst_sub_shift.
      Qed.

      Lemma error_plug_msg {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (msg : EMessage Σ2) :
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
        - apply proper_plug, proper_debug, IHp.
      Qed.

    End SolveEvars.

    Definition solve_evars {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      SolveEvars.push SolveEvars.ectx_refl p.

    Lemma solve_evars_sound {Σ} (p : 𝕊 Σ) :
      forall ι, safe (solve_evars p) ι <-> safe p ι.
    Proof. apply (SolveEvars.push_plug SolveEvars.ectx_refl). Qed.

    Module SolveUvars.

      Fixpoint assume_formulas {Σ} (fs : List Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
        match fs with
        | nil => p
        | cons fml mfs =>
          assume_formulas mfs (assumek fml p)
        end.

      Lemma safe_assume_formulas {Σ} {fs : List Formula Σ} {p : 𝕊 Σ} {ι : Valuation Σ} :
        safe (assume_formulas fs p) ι <-> (instpc fs ι -> safe p ι).
      Proof.
        revert p.
        induction fs; intros p; cbn.
        - intuition.
        - rewrite IHfs. cbn. intuition.
      Qed.

      Inductive UCtx (Σ : LCtx) : LCtx -> Type :=
      | uctx Σu (mfs : List Formula (Σ ▻▻ Σu)) : UCtx Σ (Σ ▻▻ Σu).
      Arguments uctx {Σ} Σu mfs.

      Definition uctx_refl {Σ : LCtx} : UCtx Σ Σ := @uctx Σ ctx.nil nil.

      Definition uctx_formula {Σ1 Σ2} (e : UCtx Σ1 Σ2) : Formula Σ2 -> UCtx Σ1 Σ2 :=
        match e with uctx Σu mfs => fun fml => uctx Σu (cons fml mfs) end.
      Definition uctx_snoc {Σ1 Σ2} (e: UCtx Σ1 Σ2) b : UCtx Σ1 (Σ2 ▻ b) :=
        match e with uctx Σu mfs => uctx (Σu ▻ b) (subst mfs sub_wk1) end.
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
        match e with uctx Σu mfs => fun p => demonic_close0 Σu (assume_formulas mfs p) end.

      Fixpoint close_message {Σ ΣΔ} : EMessage (Σ ▻▻ ΣΔ) -> EMessage Σ :=
         match ΣΔ as c return (EMessage (Σ ▻▻ c) -> EMessage Σ) with
         | ctx.nil      => fun msg => msg
         | ctx.snoc Γ b => fun msg => close_message (EMsgThere msg)
         end.

      Definition plug_error {Σ1 Σ2} (ec : UCtx Σ1 Σ2) : EMessage Σ2 -> 𝕊 Σ1 :=
       match ec with
       | uctx Σu mfs as ec =>
           fun msg =>
             match mfs with
             | List.nil      => error (close_message msg)
             | List.cons _ _ => plug ec (error msg)
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
        | debug b p              => plug ec (debug b (push uctx_refl p))
        end.

      Instance proper_assume_formulas {Σ} (mfs : List Formula Σ) :
        Proper (sequiv Σ ==> sequiv Σ) (assume_formulas mfs).
      Proof. intros p q pq ι. rewrite ?safe_assume_formulas. intuition. Qed.

      Instance proper_assume_formulas_impl {Σ} (mfs : List Formula Σ) :
        Proper (simpl Σ ==> simpl Σ) (assume_formulas mfs).
      Proof. intros p q pq ι. rewrite ?safe_assume_formulas. intuition. Qed.

      Instance proper_plug {Σ1 Σ2} (ec : UCtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_demonic_close0, proper_assume_formulas.
      Qed.

      Instance proper_plug_impl {Σ1 Σ2} (ec : UCtx Σ1 Σ2) :
        Proper (simpl Σ2 ==> simpl Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_demonic_close0_impl, proper_assume_formulas_impl.
      Qed.

      Lemma assume_formulas_demonic_binary {Σ} (fmls : List Formula Σ) (p1 p2 : 𝕊 Σ) :
        assume_formulas fmls (demonic_binary p1 p2) <=>
        demonic_binary (assume_formulas fmls p1) (assume_formulas fmls p2).
      Proof.
        intros ι; cbn.
        rewrite ?safe_assume_formulas.
        cbn. intuition.
      Qed.

      Lemma forall_impl {A : Type} {P : A -> Prop} {Q : Prop} :
        (Q -> forall (x : A), P x) <-> (forall (x : A), Q -> P x).
      Proof. firstorder. Qed.

      Lemma assume_formulas_demonicv {b Σ} (fmls : List Formula Σ) (p : 𝕊 (Σ ▻ b)) :
        assume_formulas fmls (demonicv b p) <=>
        demonicv b (assume_formulas (subst fmls sub_wk1) p).
      Proof.
        intros ι; cbn.
        rewrite safe_assume_formulas. cbn.
        rewrite forall_impl.
        apply base.forall_proper. intros v.
        rewrite safe_assume_formulas.
        rewrite inst_subst.
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
          rewrite safe_assume_formulas. intros Hpc Heq.
          rewrite <- inst_sub_shift in Heq.
          rewrite safe_assume_formulas in HYP.
          rewrite inst_subst in HYP.
          rewrite inst_eq_rect in HYP.
          unfold eq_rect_r in HYP. rewrite safe_eq_rect, eq_sym_involutive in HYP.
          rewrite <- env_remove_app in HYP. apply HYP.
          rewrite <- inst_sub_shift.
          rewrite inst_sub_single_shift; auto.
        - specialize (HYP (env.insert bIn ιu (inst (eq_rect ((Σ1 ▻▻ Σu) - x∷σ) (fun Σ => Term Σ σ) t (Σ1 ▻▻ Σu - x∷σ) (ctx.remove_in_cat_right bIn)) (ι ►► ιu)))).
          rewrite safe_assume_formulas, inst_subst, inst_eq_rect. intros Hpc.
          unfold eq_rect_r. rewrite safe_eq_rect, eq_sym_involutive.
          rewrite safe_assume_formulas in HYP. cbn in HYP.
          rewrite env_insert_app, env.remove_insert, env.insert_lookup in HYP.
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
          (* now rewrite <- assume_formulas_demonic_binary. *)
        - now destruct ec as [? []].
        - intros ι _. destruct ec; cbn.
          rewrite safe_demonic_close0; intros ιu.
          rewrite safe_assume_formulas; cbn; auto.
        - apply proper_plug_impl, proper_assertk_impl, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn. reflexivity.
        - apply proper_plug_impl, proper_angelicv_impl, IHp.
        - rewrite IHp. clear IHp. destruct ec; cbn.
          apply proper_demonic_close0_impl. intros ι. cbn.
          rewrite safe_assume_formulas. intros H Mmfs v.
          specialize (H v). rewrite safe_assume_formulas in H.
          apply H. now rewrite inst_subst, inst_sub_wk1.
        - apply proper_plug_impl, proper_assert_vareq_impl, IHp.
        - destruct (uctx_subst_spec ec xIn t).
          + rewrite IHp. intros ι. apply H.
          + apply proper_plug_impl, proper_assume_vareq_impl, IHp.
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

      Definition angelicv {Σ} (b : 𝑺 ∷ Ty) (p : EProp (Σ ▻ b)) : EProp Σ :=
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

      Definition error {Σ} (msg : EMessage Σ) : EProp Σ :=
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

  Module ErasureOld.

    Import SymProp.

    Inductive ETerm : Set :=
    | eterm_var     (ℓ : 𝑺) (n : nat)
    | eterm_val     (σ : Ty) (v : Val σ)
    | eterm_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (t1 : ETerm) (t2 : ETerm)
    | eterm_neg     (t : ETerm)
    | eterm_not     (t : ETerm)
    | eterm_inl     (t : ETerm)
    | eterm_inr     (t : ETerm)
    | eterm_union   {U : unioni} (K : unionk U) (t : ETerm)
    | eterm_record  (R : recordi) (ts : NamedEnv (fun _ => ETerm) (recordf_ty R)).

    Inductive EFormula : Type :=
    | eformula_user (p : 𝑷) (ts : Env (fun _ => ETerm) (𝑷_Ty p))
    | eformula_bool (t : ETerm)
    | eformula_prop {Σ' : LCtx} (ζ : Env (fun _ => ETerm) Σ') (P : abstract_named Val Σ' Prop)
    | eformula_ge (t1 t2 : ETerm)
    | eformula_gt (t1 t2 : ETerm)
    | eformula_le (t1 t2 : ETerm)
    | eformula_lt (t1 t2 : ETerm)
    | eformula_eq (σ : Ty) (t1 t2 : ETerm)
    | eformula_neq (σ : Ty) (t1 t2 : ETerm).

    Inductive ESymProp : Type :=
    | eangelic_binary (o1 o2 : ESymProp)
    | edemonic_binary (o1 o2 : ESymProp)
    | eerror
    | eblock
    | eassertk (fml : EFormula) (k : ESymProp)
    | eassumek (fml : EFormula) (k : ESymProp)
    | eangelicv (b : 𝑺∷Ty) (k : ESymProp)
    | edemonicv (b : 𝑺∷Ty) (k : ESymProp)
    | eassert_vareq
        (x : 𝑺)
        (σ : Ty)
        (n : nat)
        (t : ETerm)
        (k : ESymProp)
    | eassume_vareq
        (x : 𝑺)
        (σ : Ty)
        (n : nat)
        (t : ETerm)
        (k : ESymProp).

    Definition erase_term {Σ} : forall {σ} (t : Term Σ σ), ETerm :=
      fix erase {σ} t :=
        match t with
        | @term_var _ ℓ _ ℓIn => eterm_var ℓ (ctx.in_at ℓIn)
        | term_val σ v => eterm_val σ v
        | term_binop op t1 t2 => eterm_binop op (erase t1) (erase t2)
        | term_neg t => eterm_neg (erase t)
        | term_not t => eterm_not (erase t)
        | term_inl t => eterm_inl (erase t)
        | term_inr t => eterm_inr (erase t)
        | term_union U K t => eterm_union K (erase t)
        | term_record R ts => eterm_record R (env.map (fun _ => erase) ts)
        end.

    Definition erase_formula {Σ} : Formula Σ -> EFormula :=
      fix erase f :=
        match f with
        | formula_user p ts => @eformula_user p (env.map (@erase_term Σ) ts)
        | formula_bool t => eformula_bool (erase_term t)
        | formula_prop ζ P =>  eformula_prop (env.map (fun _ => erase_term) ζ) P
        | formula_ge t1 t2 => eformula_ge (erase_term t1) (erase_term t2)
        | formula_gt t1 t2 => eformula_gt (erase_term t1) (erase_term t2)
        | formula_le t1 t2 => eformula_le (erase_term t1) (erase_term t2)
        | formula_lt t1 t2 => eformula_lt (erase_term t1) (erase_term t2)
        | @formula_eq _ σ t1 t2 => eformula_eq σ (erase_term t1) (erase_term t2)
        | @formula_neq _ σ t1 t2 => eformula_neq σ (erase_term t1) (erase_term t2)
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
      | @assert_vareq _ x σ xIn t msg k => eassert_vareq x σ (ctx.in_at xIn) (erase_term t) (erase_symprop k)
      | @assume_vareq _ x σ xIn t k => eassume_vareq x σ (ctx.in_at xIn) (erase_term t) (erase_symprop k)
      | debug b k => erase_symprop k
      end.

    Fixpoint erase_valuation {Σ} (ι : Valuation Σ) : list { σ : Ty & Val σ} :=
      match ι with
      | env.nil        => nil
      | env.snoc ι b v => cons (existT (type b) v) (erase_valuation ι)
      end.

    Import option.notations.

    Definition inst_namedenv' (ι : list { σ : Ty & Val σ}) (inst_eterm : ETerm -> forall τ, option (Val τ)) {N} :
      forall {Δ : NCtx N Ty}, NamedEnv (fun _ => ETerm) Δ -> option (NamedEnv Val Δ) :=
       fix inst_env {Δ} E :=
         match E with
         | [] => Some []
         | @env.snoc _ _ Γ E (ℓ∷σ) t =>
             v  <- inst_eterm t σ;;
             vs <- inst_env E;;
             Some (vs ► (ℓ∷σ ↦ v))
         end.

    Definition inst_eterm (ι : list { σ : Ty & Val σ}) : ETerm -> forall τ, option (Val τ) :=
      fix inst_eterm t τ :=
        match t with
        | eterm_var _ n =>
            '(existT σ v) <- nth_error ι n;;
            match Classes.eq_dec σ τ with
            | left e => Some (eq_rect σ Val v τ e)
            | right _ => None
            end
        | eterm_val σ v =>
            match Classes.eq_dec σ τ with
            | left e => Some (eq_rect σ Val v τ e)
            | right _ => None
            end
        | @eterm_binop σ1 σ2 σ3 op t1 t2 =>
            match Classes.eq_dec σ3 τ with
            | left e =>
                v1 <- inst_eterm t1 σ1;;
                v2 <- inst_eterm t2 σ2;;
                Some (eq_rect σ3 Val (bop.eval op v1 v2) τ e)
            | right _ => None
            end
        | eterm_neg t0 =>
            match Classes.eq_dec ty.int τ with
            | left e => v <- inst_eterm t0 ty.int;;
                        Some (eq_rect ty.int Val (BinInt.Z.opp v) τ e)
            | right _ => None
            end
        | eterm_not t0 =>
            match Classes.eq_dec ty.bool τ with
            | left e => v <- inst_eterm t0 ty.bool;;
                        Some (eq_rect ty.bool Val (negb v) τ e)
            | right _ => None
            end
        | eterm_inl t0 =>
            match τ with
            | ty.sum τ1 τ2 => v <- inst_eterm t0 τ1 ;; Some (inl v)
            | _ => None
            end
        | eterm_inr t0 =>
            match τ with
            | ty.sum τ1 τ2 => v <- inst_eterm t0 τ2 ;; Some (inr v)
            | _ => None
            end
        | @eterm_union U K t0 =>
            match τ with
            | ty.union U' =>
                match Classes.eq_dec U U' with
                | left e =>
                    v <- inst_eterm t0 (unionk_ty U K);;
                    Some (eq_rect U uniont (unionv_fold U (existT K v)) U' e)
                | right _ => None
                end
            | _ => None
            end
        | @eterm_record R ts =>
            match τ with
            | ty.record R' =>
                match Classes.eq_dec R R' with
                | left e =>
                    v <- inst_namedenv' ι inst_eterm ts;;
                    Some (eq_rect R recordt (recordv_fold R v) R' e)
                | right _ => None
                end
            | _ => None
            end
        end.

    Definition inst_namedenv (ι : list { σ : Ty & Val σ}) {N} {Δ : NCtx N Ty} :
      Env (fun _ => ETerm) Δ -> option (NamedEnv Val Δ) :=
      inst_namedenv' ι (inst_eterm ι).

    Definition inst_env (ι : list { σ : Ty & Val σ}) :
      forall {Δ : Ctx Ty}, Env (fun _ => ETerm) Δ -> option (Env Val Δ) :=
      fix inst_env {Δ} E :=
        match E with
        | [] => Some []
        | @env.snoc _ _ Γ E σ t =>
            v  <- inst_eterm ι t σ;;
            vs <- inst_env E;;
            Some (vs ► (σ ↦ v))
        end.

    Definition inst_eformula (ι : list { σ : Ty & Val σ}) (f : EFormula) : Prop :=
      match f with
      | @eformula_user p ts => option_rect (fun _ => Prop) (env.uncurry (𝑷_inst p)) False (inst_env ι ts)
      | eformula_bool t => option_rect (fun _ => Prop) (fun b => b = true) False (inst_eterm ι t ty.bool)
      | @eformula_prop Σ' ζ P => option_rect (fun _ => Prop) (uncurry_named P) False (inst_namedenv ι ζ)
      | eformula_ge t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.ge v1 v2) False
                               (v1 <- inst_eterm ι t1 ty.int;; v2 <- inst_eterm ι t2 ty.int;; Some (v1, v2))
      | eformula_gt t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.gt v1 v2) False
                               (v1 <- inst_eterm ι t1 ty.int;; v2 <- inst_eterm ι t2 ty.int;; Some (v1, v2))
      | eformula_le t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.le v1 v2) False
                               (v1 <- inst_eterm ι t1 ty.int;; v2 <- inst_eterm ι t2 ty.int;; Some (v1, v2))
      | eformula_lt t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.lt v1 v2) False
                               (v1 <- inst_eterm ι t1 ty.int;; v2 <- inst_eterm ι t2 ty.int;; Some (v1, v2))
      | eformula_eq σ t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => v1 = v2) False
                                 (v1 <- inst_eterm ι t1 σ;; v2 <- inst_eterm ι t2 σ;; Some (v1, v2))
      | eformula_neq σ t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => v1 <> v2) False
                                  (v1 <- inst_eterm ι t1 σ;; v2 <- inst_eterm ι t2 σ;; Some (v1, v2))
      end.

    Fixpoint list_remove {A} (xs : list A) (n : nat) : list A :=
      match xs with
      | nil       => nil
      | cons x xs => match n with
                     | O   => xs
                     | S n => cons x (list_remove xs n)
                     end
      end.

    Fixpoint inst_symprop (ι : list { σ : Ty & Val σ}) (f : ESymProp) : Prop :=
      match f with
      | eangelic_binary p1 p2 => inst_symprop ι p1 \/ inst_symprop ι p2
      | edemonic_binary p1 p2 => inst_symprop ι p1 /\ inst_symprop ι p2
      | eerror => False
      | eblock => True
      | eassertk fml k => inst_eformula ι fml /\ inst_symprop ι k
      | eassumek fml k => inst_eformula ι fml -> inst_symprop ι k
      | eangelicv b k => exists v : Val (type b), inst_symprop (cons (existT (type b) v) ι) k
      | edemonicv b k => forall v : Val (type b), inst_symprop (cons (existT (type b) v) ι) k
      | eassert_vareq x σ n t k =>
          let ι' := list_remove ι n in
          inst_eterm ι (eterm_var x n) σ = inst_eterm ι' t σ /\
          inst_symprop ι' k
      | eassume_vareq x σ n t k =>
          let ι' := list_remove ι n in
          inst_eterm ι (eterm_var x n) σ = inst_eterm ι' t σ ->
          inst_symprop ι' k
      end.

    Lemma erase_valuation_remove {Σ b} (bIn : b ∈ Σ) (ι : Valuation Σ) :
      list_remove (erase_valuation ι) (ctx.in_at bIn) =
      erase_valuation (env.remove b ι bIn).
    Proof.
      induction ι.
      - destruct (ctx.nilView bIn).
      - destruct (ctx.snocView bIn); cbn.
        + reflexivity.
        + f_equal. apply (IHι i).
    Qed.

    Lemma nth_error_erase {Σ b} (ι : Valuation Σ) (bIn : b ∈ Σ) :
      nth_error (erase_valuation ι) (ctx.in_at bIn) =
      Some (existT (type b) (env.lookup ι bIn)).
    Proof.
      induction ι; cbn.
      - destruct (ctx.nilView bIn).
      - destruct (ctx.snocView bIn) as [|b bIn]; cbn.
        + reflexivity.
        + now rewrite IHι.
    Qed.

    Lemma inst_eterm_erase {Σ σ} (t : Term Σ σ) (ι : Valuation Σ) :
      inst_eterm (erase_valuation ι) (erase_term t) σ = Some (inst t ι).
    Proof.
      induction t; cbn [inst_eterm erase_term].
      - rewrite nth_error_erase; cbn.
        now rewrite EqDec.eq_dec_refl.
      - now rewrite EqDec.eq_dec_refl.
      - now rewrite EqDec.eq_dec_refl, IHt1, IHt2.
      - now rewrite IHt.
      - now rewrite IHt.
      - now rewrite IHt.
      - now rewrite IHt.
      - now rewrite EqDec.eq_dec_refl, IHt.
      - rewrite EqDec.eq_dec_refl. cbn.
        assert (inst_namedenv'
                  (erase_valuation ι)
                  (inst_eterm (erase_valuation ι))
                  (env.map (fun b : recordf∷Ty => erase_term) es) =
                  Some (inst
                    (* (T := fun Σ => @NamedEnv 𝑹𝑭 Ty (Term Σ) (𝑹𝑭_Ty R)) *)
                    (* (A := @NamedEnv 𝑹𝑭 Ty Val (𝑹𝑭_Ty R)) *)
                    es ι)) as ->; auto.
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
      inst_eformula (erase_valuation ι) (erase_formula fml) <-> inst fml ι.
    Proof.
      destruct fml; cbn;
        now rewrite ?inst_eterm_erase, ?inst_env_erase, ?inst_namedenv_erase.
    Qed.

    Lemma erase_safe {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      inst_symprop (erase_valuation ι) (erase_symprop p) <->
      safe p ι.
    Proof.
      induction p; cbn [inst_symprop erase_symprop safe].
      - apply Morphisms_Prop.or_iff_morphism. auto. auto.
      - apply Morphisms_Prop.and_iff_morphism. auto. auto.
      - reflexivity.
      - reflexivity.
      - apply Morphisms_Prop.and_iff_morphism.
        + apply inst_eformula_erase.
        + auto.
      - apply Morphisms_Prop.iff_iff_iff_impl_morphism.
        + apply inst_eformula_erase.
        + auto.
      - apply base.exist_proper. intros v. apply (IHp (env.snoc ι b v)).
      - apply base.forall_proper. intros v. apply (IHp (env.snoc ι b v)).
      - apply Morphisms_Prop.and_iff_morphism; cbn.
        + rewrite nth_error_erase; cbn.
          rewrite EqDec.eq_dec_refl.
          rewrite erase_valuation_remove. cbn.
          rewrite inst_eterm_erase.
          intuition.
        + generalize (IHp (env.remove _ ι xIn)).
          now rewrite erase_valuation_remove.
      - apply Morphisms_Prop.iff_iff_iff_impl_morphism; cbn.
        + rewrite nth_error_erase; cbn.
          rewrite EqDec.eq_dec_refl.
          rewrite erase_valuation_remove. cbn.
          rewrite inst_eterm_erase.
          intuition.
        + generalize (IHp (env.remove _ ι xIn)).
          now rewrite erase_valuation_remove.
      - apply IHp.
    Qed.

    Lemma erase_safe' {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      inst_symprop (erase_valuation ι) (erase_symprop p) ->
      safe p ι.
    Proof. apply erase_safe. Qed.

  End ErasureOld.

  Module Erasure.

    Import SymProp.

    Inductive ETerm : Ty -> Set :=
    | eterm_var     (ℓ : 𝑺) (σ : Ty) (n : nat) : ETerm σ
    | eterm_val     (σ : Ty) (v : Val σ) : ETerm σ
    | eterm_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (t1 : ETerm σ1) (t2 : ETerm σ2) : ETerm σ3
    | eterm_neg     (t : ETerm ty.int) : ETerm ty.int
    | eterm_not     (t : ETerm ty.bool) : ETerm ty.bool
    | eterm_inl     {σ1 σ2 : Ty} (t : ETerm σ1) : ETerm (ty.sum σ1 σ2)
    | eterm_inr     {σ1 σ2 : Ty} (t : ETerm σ2) : ETerm (ty.sum σ1 σ2)
    | eterm_union   {U : unioni} (K : unionk U) (t : ETerm (unionk_ty U K)) : ETerm (ty.union U)
    | eterm_record  (R : recordi) (ts : NamedEnv ETerm (recordf_ty R)) : ETerm (ty.record R).

    Inductive EFormula : Type :=
    | eformula_user (p : 𝑷) (ts : Env ETerm (𝑷_Ty p))
    | eformula_bool (t : ETerm ty.bool)
    | eformula_prop {Σ' : LCtx} (ζ : Env (fun x => ETerm (type x)) Σ') (P : abstract_named Val Σ' Prop)
    | eformula_ge (t1 t2 : ETerm ty.int)
    | eformula_gt (t1 t2 : ETerm ty.int)
    | eformula_le (t1 t2 : ETerm ty.int)
    | eformula_lt (t1 t2 : ETerm ty.int)
    | eformula_eq (σ : Ty) (t1 t2 : ETerm σ)
    | eformula_neq (σ : Ty) (t1 t2 : ETerm σ).

    Inductive ESymProp : Type :=
    | eangelic_binary (o1 o2 : ESymProp)
    | edemonic_binary (o1 o2 : ESymProp)
    | eerror
    | eblock
    | eassertk (fml : EFormula) (k : ESymProp)
    | eassumek (fml : EFormula) (k : ESymProp)
    | eangelicv (b : 𝑺∷Ty) (k : ESymProp)
    | edemonicv (b : 𝑺∷Ty) (k : ESymProp)
    | eassert_vareq
        (x : 𝑺)
        (σ : Ty)
        (n : nat)
        (t : ETerm σ)
        (k : ESymProp)
    | eassume_vareq
        (x : 𝑺)
        (σ : Ty)
        (n : nat)
        (t : ETerm σ)
        (k : ESymProp).

    Definition erase_term {Σ} : forall {σ} (t : Term Σ σ), ETerm σ :=
      fix erase {σ} t :=
        match t with
        | @term_var _ ℓ σ ℓIn => eterm_var ℓ σ (ctx.in_at ℓIn)
        | term_val σ v => eterm_val σ v
        | term_binop op t1 t2 => eterm_binop op (erase t1) (erase t2)
        | term_neg t => eterm_neg (erase t)
        | term_not t => eterm_not (erase t)
        | term_inl t => eterm_inl (erase t)
        | term_inr t => eterm_inr (erase t)
        | term_union U K t => eterm_union K (erase t)
        | term_record R ts => eterm_record R (env.map (fun _ => erase) ts)
        end.

    Definition erase_formula {Σ} : Formula Σ -> EFormula :=
      fix erase f :=
        match f with
        | formula_user p ts => @eformula_user p (env.map (@erase_term Σ) ts)
        | formula_bool t => eformula_bool (erase_term t)
        | formula_prop ζ P =>  eformula_prop (env.map (fun _ => erase_term) ζ) P
        | formula_ge t1 t2 => eformula_ge (erase_term t1) (erase_term t2)
        | formula_gt t1 t2 => eformula_gt (erase_term t1) (erase_term t2)
        | formula_le t1 t2 => eformula_le (erase_term t1) (erase_term t2)
        | formula_lt t1 t2 => eformula_lt (erase_term t1) (erase_term t2)
        | @formula_eq _ σ t1 t2 => eformula_eq (erase_term t1) (erase_term t2)
        | @formula_neq _ σ t1 t2 => eformula_neq (erase_term t1) (erase_term t2)
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
      | debug b k => erase_symprop k
      end.

    Fixpoint erase_valuation {Σ} (ι : Valuation Σ) : list { σ : Ty & Val σ} :=
      match ι with
      | env.nil        => nil
      | env.snoc ι b v => cons (existT (type b) v) (erase_valuation ι)
      end.

    Import option.notations.

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
        | eterm_neg t0 =>
            BinInt.Z.opp <$> inst_eterm t0
        | eterm_not t0 =>
            negb <$> inst_eterm t0
        | eterm_inl t0 =>
            inl <$> inst_eterm t0
        | eterm_inr t0 =>
            inr <$> inst_eterm t0
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

    Definition inst_eformula (ι : list { σ : Ty & Val σ}) (f : EFormula) : Prop :=
      match f with
      | @eformula_user p ts => option_rect (fun _ => Prop) (env.uncurry (𝑷_inst p)) False (inst_env ι ts)
      | eformula_bool t => option_rect (fun _ => Prop) (fun b => b = true) False (inst_eterm ι t)
      | @eformula_prop Σ' ζ P => option_rect (fun _ => Prop) (uncurry_named P) False (inst_namedenv ι ζ)
      | eformula_ge t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.ge v1 v2) False
                               (v1 <- inst_eterm ι t1;; v2 <- inst_eterm ι t2;; Some (v1, v2))
      | eformula_gt t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.gt v1 v2) False
                               (v1 <- inst_eterm ι t1;; v2 <- inst_eterm ι t2;; Some (v1, v2))
      | eformula_le t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.le v1 v2) False
                               (v1 <- inst_eterm ι t1;; v2 <- inst_eterm ι t2;; Some (v1, v2))
      | eformula_lt t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => BinInt.Z.lt v1 v2) False
                               (v1 <- inst_eterm ι t1;; v2 <- inst_eterm ι t2;; Some (v1, v2))
      | eformula_eq t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => v1 = v2) False
                                 (v1 <- inst_eterm ι t1;; v2 <- inst_eterm ι t2;; Some (v1, v2))
      | eformula_neq t1 t2 => option_rect (fun _ => Prop) (fun '(v1,v2) => v1 <> v2) False
                                  (v1 <- inst_eterm ι t1;; v2 <- inst_eterm ι t2;; Some (v1, v2))
      end.

    Fixpoint list_remove {A} (xs : list A) (n : nat) : list A :=
      match xs with
      | nil       => nil
      | cons x xs => match n with
                     | O   => xs
                     | S n => cons x (list_remove xs n)
                     end
      end.

    Fixpoint inst_symprop (ι : list { σ : Ty & Val σ}) (f : ESymProp) : Prop :=
      match f with
      | eangelic_binary p1 p2 => inst_symprop ι p1 \/ inst_symprop ι p2
      | edemonic_binary p1 p2 => inst_symprop ι p1 /\ inst_symprop ι p2
      | eerror => False
      | eblock => True
      | eassertk fml k => inst_eformula ι fml /\ inst_symprop ι k
      | eassumek fml k => inst_eformula ι fml -> inst_symprop ι k
      | eangelicv b k => exists v : Val (type b), inst_symprop (cons (existT (type b) v) ι) k
      | edemonicv b k => forall v : Val (type b), inst_symprop (cons (existT (type b) v) ι) k
      | eassert_vareq x n t k =>
          let ι' := list_remove ι n in
          inst_eterm ι (eterm_var x _ n) = inst_eterm ι' t /\
          inst_symprop ι' k
      | eassume_vareq x n t k =>
          let ι' := list_remove ι n in
          inst_eterm ι (eterm_var x _ n) = inst_eterm ι' t ->
          inst_symprop ι' k
      end.

    Lemma erase_valuation_remove {Σ b} (bIn : b ∈ Σ) (ι : Valuation Σ) :
      list_remove (erase_valuation ι) (ctx.in_at bIn) =
      erase_valuation (env.remove b ι bIn).
    Proof.
      induction ι.
      - destruct (ctx.nilView bIn).
      - destruct (ctx.snocView bIn); cbn.
        + reflexivity.
        + f_equal. apply (IHι i).
    Qed.

    Lemma nth_error_erase {Σ b} (ι : Valuation Σ) (bIn : b ∈ Σ) :
      nth_error (erase_valuation ι) (ctx.in_at bIn) =
      Some (existT (type b) (env.lookup ι bIn)).
    Proof.
      induction ι; cbn.
      - destruct (ctx.nilView bIn).
      - destruct (ctx.snocView bIn) as [|b bIn]; cbn.
        + reflexivity.
        + now rewrite IHι.
    Qed.

    Lemma inst_eterm_erase {Σ σ} (t : Term Σ σ) (ι : Valuation Σ) :
      inst_eterm (erase_valuation ι) (erase_term t) = Some (inst t ι).
    Proof.
      induction t; cbn [inst_eterm erase_term].
      - rewrite nth_error_erase; cbn.
        now rewrite EqDec.eq_dec_refl.
      - reflexivity.
      - now rewrite IHt1, IHt2.
      - now rewrite IHt.
      - now rewrite IHt.
      - now rewrite IHt.
      - now rewrite IHt.
      - now rewrite IHt.
      - assert (inst_namedenv'
                  (erase_valuation ι)
                  (inst_eterm (erase_valuation ι))
                  (env.map (fun b : recordf∷Ty => erase_term) es) =
                  Some (inst
                    (* (T := fun Σ => @NamedEnv 𝑹𝑭 Ty (Term Σ) (𝑹𝑭_Ty R)) *)
                    (* (A := @NamedEnv 𝑹𝑭 Ty Val (𝑹𝑭_Ty R)) *)
                    es ι)) as ->; auto.
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
      inst_eformula (erase_valuation ι) (erase_formula fml) <-> inst fml ι.
    Proof.
      destruct fml; cbn;
        now rewrite ?inst_eterm_erase, ?inst_env_erase, ?inst_namedenv_erase.
    Qed.

    Lemma erase_safe {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      inst_symprop (erase_valuation ι) (erase_symprop p) <->
      safe p ι.
    Proof.
      induction p; cbn [inst_symprop erase_symprop safe].
      - apply Morphisms_Prop.or_iff_morphism. auto. auto.
      - apply Morphisms_Prop.and_iff_morphism. auto. auto.
      - reflexivity.
      - reflexivity.
      - apply Morphisms_Prop.and_iff_morphism.
        + apply inst_eformula_erase.
        + auto.
      - apply Morphisms_Prop.iff_iff_iff_impl_morphism.
        + apply inst_eformula_erase.
        + auto.
      - apply base.exist_proper. intros v. apply (IHp (env.snoc ι b v)).
      - apply base.forall_proper. intros v. apply (IHp (env.snoc ι b v)).
      - apply Morphisms_Prop.and_iff_morphism; cbn.
        + rewrite nth_error_erase; cbn.
          rewrite EqDec.eq_dec_refl.
          rewrite erase_valuation_remove. cbn.
          rewrite inst_eterm_erase.
          intuition.
        + generalize (IHp (env.remove _ ι xIn)).
          now rewrite erase_valuation_remove.
      - apply Morphisms_Prop.iff_iff_iff_impl_morphism; cbn.
        + rewrite nth_error_erase; cbn.
          rewrite EqDec.eq_dec_refl.
          rewrite erase_valuation_remove. cbn.
          rewrite inst_eterm_erase.
          intuition.
        + generalize (IHp (env.remove _ ι xIn)).
          now rewrite erase_valuation_remove.
      - apply IHp.
    Qed.

    Lemma erase_safe' {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      inst_symprop (erase_valuation ι) (erase_symprop p) ->
      safe p ι.
    Proof. apply erase_safe. Qed.

  End Erasure.

End SymPropOn.
