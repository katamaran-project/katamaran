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
     Relations.Relation_Definitions
     Strings.String.

From Katamaran Require Import
     Base
     Notations
     Prelude
     Symbolic.Worlds
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

    Global Instance OccursCheckMessage : OccursCheck Message :=
      fun Σ x xIn msg =>
        match msg with
        | MkMessage f m Γ δ h pc =>
          option_ap
            (option_ap
               (option_map
                  (MkMessage f m Γ)
                  (occurs_check xIn δ))
               (occurs_check xIn h))
            (occurs_check xIn pc)
        end.

    Inductive Error (Σ : LCtx) (msg : Message Σ) : Prop :=.

  End Messages.

  Inductive Obligation {Σ} (msg : Message Σ) (fml : Formula Σ) (ι : Valuation Σ) : Prop :=
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
      | ε       => fun msg => msg
      | ΣΔ  ▻ b => fun msg => emsg_close (EMsgThere msg)
      end.

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
    | assertk (fml : Formula Σ) (msg : Message Σ) (k : SymProp Σ)
    | assumek (fml : Formula Σ) (k : SymProp Σ)
    (* Don't use these two directly. Instead, use the HOAS versions 'angelic' *)
    (* and 'demonic' that will freshen names. *)
    | angelicv b (k : SymProp (Σ ▻ b))
    | demonicv b (k : SymProp (Σ ▻ b))
    | assert_vareq
        x σ (xIn : x∷σ ∈ Σ)
        (t : Term (Σ - x∷σ) σ)
        (msg : Message (Σ - x∷σ))
        (k : SymProp (Σ - x∷σ))
    | assume_vareq
        x σ (xIn : x∷σ ∈ Σ)
        (t : Term (Σ - x∷σ) σ)
        (k : SymProp (Σ - x∷σ))
    | debug
        {BT} {subB : Subst BT} {occB: OccursCheck BT}
        (b : BT Σ) (k : SymProp Σ).
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
        | ε     => fun p => p
        | Σ ▻ b => fun p => close Σ (angelicv b p)
        end.

    Definition demonic_close0 {Σ0 : LCtx} :
      forall Σ, 𝕊 (Σ0 ▻▻ Σ) -> 𝕊 Σ0 :=
      fix close Σ :=
        match Σ with
        | ε     => fun p => p
        | Σ ▻ b => fun p => close Σ (demonicv b p)
        end.

    Definition demonic_close :
      forall Σ, 𝕊 Σ -> 𝕊 ε :=
      fix close Σ :=
        match Σ with
        | ε     => fun k => k
        | Σ ▻ b => fun k => close Σ (@demonicv Σ b k)
        end.

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
      (msg : Message Σ) (fmls : List Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
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

    Definition assert_formulas_without_solver {w : World} (msg : Message w)
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

    Fixpoint assert_triangular {w1 w2} (msg : Message (wctx w1)) (ζ : Tri w1 w2) :
      (Message w2 -> 𝕊 w2) -> 𝕊 w1.
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
          Obligation msg fml ι /\ safe o ι
        | assumek fml o => (inst fml ι : Prop) -> safe o ι
        | angelicv b k => exists v, safe k (env.snoc ι b v)
        | demonicv b k => forall v, safe k (env.snoc ι b v)
        | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
          Obligation (subst msg ζ) (formula_eq (term_var x) (subst t ζ))) ι /\
          (let ι' := env.remove (x∷σ) ι xIn in
          safe k ι')
        | @assume_vareq _ x σ xIn t k =>
          let ι' := env.remove (x∷σ) ι xIn in
          env.lookup ι xIn = inst t ι' ->
          safe k ι'
        | debug d k => Debug d (safe k ι)
        end%type.
    Global Arguments safe {Σ} p ι.

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

    Lemma obligation_equiv {Σ : LCtx} (msg : Message Σ) (fml : Formula Σ) (ι : Valuation Σ) :
      Obligation msg fml ι <-> inst fml ι.
    Proof. split. now intros []. now constructor. Qed.

    Lemma debug_equiv {B : LCtx -> Type} {Σ} {b : B Σ} {P : Prop} :
      @Debug B _ b P <-> P.
    Proof. split. now intros []. now constructor. Qed.

    Lemma wsafe_safe {w : World} (p : 𝕊 w) (ι : Valuation w) :
      wsafe p ι <-> safe p ι.
    Proof.
      destruct w as [Σ pc]; cbn in *; revert pc.
      induction p; cbn; intros pc; rewrite ?debug_equiv; auto;
        try (intuition; fail).
      apply base.exist_proper; eauto.
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
      (msg : Message w0) (fmls : List Formula w0) (p : 𝕊 w0)
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
      (o : Message w1 -> 𝕊 w1) (ι0 : Valuation w0) :
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

    Instance proper_angelic_close0 {Σ Σe} : Proper (sequiv (Σ ▻▻ Σe) ==> sequiv Σ) (angelic_close0 Σe).
    Proof. intros p q pq ι. rewrite ?safe_angelic_close0. now apply base.exist_proper. Qed.

    Instance proper_angelic_binary {Σ} : Proper (sequiv Σ ==> sequiv Σ ==> sequiv Σ) (@angelic_binary Σ).
    Proof.
      unfold sequiv.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      now rewrite p12, q12.
    Qed.

    Instance proper_demonic_close0 {Σ Σu} : Proper (sequiv (Σ ▻▻ Σu) ==> sequiv Σ) (demonic_close0 Σu).
    Proof. intros p q pq ι. rewrite ?safe_demonic_close0. now apply base.forall_proper. Qed.

    Instance proper_demonic_binary {Σ} : Proper (sequiv Σ ==> sequiv Σ ==> sequiv Σ) (@demonic_binary Σ).
    Proof.
      unfold sequiv.
      intros p1 p2 p12 q1 q2 q12 ι; cbn.
      now rewrite p12, q12.
    Qed.

    Instance proper_assumek {Σ} (fml : Formula Σ) : Proper (sequiv Σ ==> sequiv Σ) (assumek fml).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assertk {Σ} (fml : Formula Σ) (msg : Message Σ) : Proper (sequiv Σ ==> sequiv Σ) (assertk fml msg).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assume_vareq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      Proper (sequiv (Σ - x∷σ) ==> sequiv Σ) (assume_vareq x t).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_assert_vareq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (msg : Message (Σ - x∷σ)) :
      Proper (sequiv (Σ - x∷σ) ==> sequiv Σ) (assert_vareq x t msg).
    Proof. unfold sequiv. intros p q pq ι. cbn. intuition. Qed.

    Instance proper_angelicv {Σ b} : Proper (sequiv (Σ ▻ b) ==> sequiv Σ) (angelicv b).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply base.exist_proper. Qed.

    Instance proper_demonicv {Σ b} : Proper (sequiv (Σ ▻ b) ==> sequiv Σ) (demonicv b).
    Proof. unfold sequiv. intros p q pq ι. cbn. now apply base.forall_proper. Qed.

    Instance proper_debug {BT} `{Subst BT, OccursCheck BT} {Σ} {bt : BT Σ} :
      Proper (sequiv Σ ==> sequiv Σ) (debug bt).
    Proof. unfold sequiv. intros p q pq ι. cbn. now rewrite ?debug_equiv. Qed.

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
      Notation "x - y" := (term_binop binop_minus x y) : exp_scope.
      Notation "x + y" := (term_binop binop_plus x y) : exp_scope.
      Notation "x * y" := (term_binop binop_times x y) : exp_scope.
      Notation "x ↦ t ∧ k" := (@SymProp.assert_vareq _ x _ _ t _ k) (at level 99, right associativity, only printing).
      Notation "x ↦ t → k" := (@SymProp.assume_vareq _ x _ _ t k) (at level 99, right associativity, only printing).
      Notation "P ∧ Q" := (@SymProp.demonic_binary _ P Q) (at level 80, right associativity, only printing).
      Notation "P ∨ Q" := (@SymProp.angelic_binary _ P Q) (at level 85, right associativity, only printing).
      Notation "x < y" := (formula_lt x y) (only printing).
      Notation "x <= y" := (formula_le x y) (only printing).
      Notation "x >= y" := (formula_ge x y) (only printing).
      Notation "t" := (term_val _ t) (at level 1, only printing).
    End notations.

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

    Definition assertk_prune {Σ} (fml : Formula Σ) (msg : Message Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
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
      (t : Term (Σ - x∷σ) σ) (msg : Message (Σ - x∷σ)) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ :=
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
      (t : Term (Σ - x∷σ) σ) (msg : Message (Σ - x∷σ)) (p : 𝕊 (Σ - x∷σ)) (ι : Valuation Σ) :
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

      Fixpoint assert_msgs_formulas {Σ} (mfs : List (Pair Message Formula) Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
        match mfs with
        | nil => p
        | cons (msg,fml) mfs =>
          assert_msgs_formulas mfs (assertk fml msg p)
        end.

      Lemma safe_assert_msgs_formulas {Σ} {mfs : List (Pair Message Formula) Σ} {p : 𝕊 Σ} {ι : Valuation Σ} :
        (safe (assert_msgs_formulas mfs p) ι <-> instpc (map snd mfs) ι /\ safe p ι).
      Proof.
        revert p.
        induction mfs; intros p; cbn.
        - intuition.
        - destruct a. rewrite IHmfs. cbn.
          now rewrite obligation_equiv.
      Qed.

      Inductive ECtx (Σ : LCtx) : LCtx -> Type :=
      | ectx Σe (mfs : List (Pair Message Formula) (Σ ▻▻ Σe)) : ECtx Σ (Σ ▻▻ Σe).
      Arguments ectx {Σ} Σe mfs.

      Definition ectx_refl {Σ : LCtx} : ECtx Σ Σ := @ectx Σ ctx.nil nil.

      Definition ectx_formula {Σ1 Σ2} (e: ECtx Σ1 Σ2) : Message Σ2 -> Formula Σ2 -> ECtx Σ1 Σ2 :=
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

      Instance proper_assert_msgs_formulas {Σ} (mfs : List (Pair Message Formula) Σ) :
        Proper (sequiv Σ ==> sequiv Σ) (assert_msgs_formulas mfs).
      Proof. intros p q pq ι. rewrite ?safe_assert_msgs_formulas. intuition. Qed.

      Instance proper_plug {Σ1 Σ2} (ec : ECtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_angelic_close0, proper_assert_msgs_formulas.
      Qed.

      Lemma assert_msgs_formulas_angelic_binary {Σ} (mfs : List (Pair Message Formula) Σ) (p1  p2 : 𝕊 Σ) :
        assert_msgs_formulas mfs (angelic_binary p1 p2) <=>
        angelic_binary (assert_msgs_formulas mfs p1) (assert_msgs_formulas mfs p2).
      Proof.
        intros ι; cbn.
        rewrite ?safe_assert_msgs_formulas.
        cbn. intuition.
      Qed.

      Lemma map_snd_subst {Σ Σ' : LCtx} {ζ : Sub Σ Σ'}
            {mfs : List (Pair Message Formula) Σ} :
            map snd (subst mfs ζ) = subst (map snd mfs) ζ.
      Proof.
        induction mfs.
        - easy.
        - cbn.
          rewrite IHmfs.
          now destruct a.
      Qed.

      Lemma assert_msgs_formulas_angelicv {b Σ} (mfs : List (Pair Message Formula) Σ) (p : 𝕊 (Σ ▻ b)) :
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

      Lemma ectx_subst_spec {Σ1 Σ2} (ec : ECtx Σ1 Σ2) {x σ} (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ) (msg : Message _) :
        OptionSpec
          (fun e => forall p, plug e p <=> plug ec (assert_vareq x t msg p))
          True
          (ectx_subst ec xIn t).
      Proof.
        destruct ec; cbn. destruct (ctx.catView xIn); constructor; auto.
        intros p ι. unfold eq_rect_r. rewrite plug_eq_rect. cbn.
        rewrite ?safe_angelic_close0.
        split; intros [ιe HYP].
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          unfold eq_rect_r in Hp. rewrite safe_eq_rect, eq_sym_involutive in Hp.
          exists (env.insert bIn ιe (inst (eq_rect ((Σ1 ▻▻ Σe) - x∷σ) (fun Σ => Term Σ σ) t (Σ1 ▻▻ Σe - x∷σ) (ctx.remove_in_cat_right bIn)) (ι ►► ιe))).
          rewrite safe_assert_msgs_formulas. cbn. rewrite obligation_equiv. cbn.
          rewrite env_insert_app, env.remove_insert, env.insert_lookup.
          rewrite inst_subst, inst_sub_shift, env.remove_insert, ?inst_eq_rect.
          split; auto.
          rewrite map_snd_subst, inst_subst, inst_eq_rect in Hpc.
          now rewrite inst_sub_single2 in Hpc.
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          cbn in Hp. rewrite obligation_equiv in Hp. cbn in Hp. destruct Hp as [Ht Hp].
          rewrite env_remove_app in Hp.
          exists (env.remove (x∷σ) ιe bIn).
          rewrite safe_assert_msgs_formulas.
          rewrite map_snd_subst, inst_subst.
          unfold eq_rect_r. rewrite safe_eq_rect.
          rewrite eq_sym_involutive. split; auto.
          rewrite inst_subst in Ht.
          rewrite inst_eq_rect.
          rewrite <- env_remove_app.
          rewrite <- inst_sub_shift.
          now rewrite inst_sub_single_shift.
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

      Fixpoint push {Σ1 Σ2} (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2) {struct p} : 𝕊 Σ1 :=
        match p with
        | angelic_binary p1 p2   => plug ec (angelic_binary (push uctx_refl p1) (push uctx_refl p2))
        | demonic_binary p1 p2   => plug ec (demonic_binary (push uctx_refl p1) (push uctx_refl p2))
            (* demonic_binary (push ec p1) (push ec p2) *)
        | error msg              => plug ec (error msg)
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

      Instance proper_plug {Σ1 Σ2} (ec : UCtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_demonic_close0, proper_assume_formulas.
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
        OptionSpec
          (fun e => forall p, plug e p <=> plug ec (assume_vareq x t p))
          True
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
        push ec p <=> plug ec p.
      Proof.
        revert Σ1 ec; induction p; cbn; intros Σ1 ec.
        - apply proper_plug, proper_angelic_binary;
           [now rewrite IHp1 | now rewrite IHp2].
        - rewrite IHp1, IHp2. clear IHp1 IHp2.
          reflexivity.
          (* destruct ec. cbn [plug]. *)
          (* rewrite <- demonic_close0_demonic_binary. *)
          (* apply proper_demonic_close0. *)
          (* now rewrite <- assume_formulas_demonic_binary. *)
        - reflexivity.
        - intros ι; cbn; split; auto. intros _.
          destruct ec; cbn.
          rewrite safe_demonic_close0; intros ιu.
          rewrite safe_assume_formulas; cbn; auto.
        - apply proper_plug, proper_assertk, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn. reflexivity.
        - apply proper_plug, proper_angelicv, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn.
          apply proper_demonic_close0.
          rewrite assume_formulas_demonicv.
          reflexivity.
        - apply proper_plug, proper_assert_vareq, IHp.
        - destruct (uctx_subst_spec ec xIn t).
          + rewrite IHp. rewrite H. reflexivity.
          + apply proper_plug, proper_assume_vareq, IHp.
        - apply proper_plug, proper_debug, IHp.
      Qed.

    End SolveUvars.

    Definition solve_uvars {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      SolveUvars.push SolveUvars.uctx_refl p.

    Lemma solve_uvars_sound {Σ} (p : 𝕊 Σ) :
      forall ι, safe (solve_uvars p) ι <-> safe p ι.
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
  Import Postprocessing.

End SymPropOn.
