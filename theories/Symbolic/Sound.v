(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
     Program.Equality
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From Katamaran Require Import
     SemiConcrete.Mutator
     SemiConcrete.Sound
     Sep.Hoare
     Sep.Logic
     Sep.Spec
     Symbolic.Mutator
     Syntax
     Tactics.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).
  Module MUT := Mutators termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic termkit progkit assertkit contractkit.
  Import LOG.
  Module SCMUT := SemiConcrete.Sound.Soundness termkit progkit assertkit contractkit.
  Import SCMUT.
  Import SCMUT.MUT.

  Import SPath.

  Class Approx (AT : TYPE) (A : Type) : Type :=
    approx :
      forall (w : World) (ι : SymInstance w), (* instpc (wco w) ι -> *)
        AT w -> A -> Prop.
  Global Arguments approx {_ _ _ w} ι _ _.

  Global Instance ApproxInst {AT A} `{instA : Inst AT A} : Approx AT A :=
    fun w ι t v =>
      v = inst t ι.
  Global Arguments ApproxInst {_ _ _} w ι t v /.

  Global Instance ApproxPath : Approx SPath Prop :=
    fun w ι SP P => wsafe SP ι -> P.

  Global Instance ApproxBox {AT A} `{Approx AT A} : Approx (Box AT) A :=
    fun w0 ι0 a0 a =>
      forall (w1 : World) (ω01 : w0 ⊒ w1) (ι1 : SymInstance w1),
        ι0 = inst (sub_acc ω01) ι1 ->
        instpc (wco w1) ι1 ->
        approx ι1 (a0 w1 ω01) a.

  Global Instance ApproxImpl {AT A BT B} `{Approx AT A, Approx BT B} : Approx (Impl AT BT) (A -> B) :=
    fun w ι fs fc =>
      forall (ta : AT w) (a : A),
        approx ι ta a ->
        approx ι (fs ta) (fc a).

  Global Instance ApproxForall {𝑲 : Set} {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type} {apxA : forall K, Approx (AT K) (A K)} :
    Approx (@Forall 𝑲 AT) (forall K : 𝑲, A K) :=
    fun w ι fs fc =>
      forall K : 𝑲,
        approx ι (fs K) (fc K).

  Global Instance ApproxMut {Γ1 Γ2 AT A} `{Approx AT A} : Approx (SMut Γ1 Γ2 AT) (CMut Γ1 Γ2 A).
  Proof.
    unfold SMut, CMut.
    eapply ApproxImpl.
  Defined.
  (* Defined. *)
  (*   (* fun w ι ms mc => *) *)
  (*   (*   forall POST δt ht δc hc, *) *)
  (*   (*     δc = inst δt ι -> *) *)
  (*   (*     hc = inst ht ι -> *) *)
  (*   (*     smut_wp ms POST δt ht ι -> *) *)
  (*   (*     cmut_wp mc POST δc hc. *) *)

  Global Instance ApproxTermLit {σ} : Approx (STerm σ) (Lit σ) :=
    ApproxInst (AT := STerm σ).

  Global Instance ApproxStore {Δ : PCtx} :
    Approx (SStore Δ) (CStore Δ) :=
    ApproxInst.

  Global Instance ApproxNamedEnv {N : Set} {Δ : NCtx N Ty} :
    Approx (fun w => NamedEnv (Term w) Δ) (NamedEnv Lit Δ) | 1 :=
    ApproxInst.

  (* Global Instance ApproxChunk : Approx Chunk SCChunk := *)
  (*   fun w ι t v => *)
  (*     v = inst t ι. *)

  (* Global Instance ApproxUnit : Approx Unit unit := *)
  (*   fun w ι t v => *)
  (*     v = inst t ι. *)

  Hint Unfold SMut : core.
  Hint Unfold CMut : core.

  Hint Unfold SMut : typeclass_instances.
  Hint Unfold CMut : typeclass_instances.

  Hint Unfold approx ApproxImpl ApproxBox ApproxInst ApproxPath (* ApproxMut  *)ApproxTermLit (* ApproxNamedEnv *) ApproxStore : core.

  Import ModalNotations.
  Open Scope modal.

  Lemma approx_four {AT A} `{Approx AT A} {w0 : World} (ι0 : SymInstance w0) :
    forall (a0 : Box AT w0) (a : A),
      approx ι0 a0 a ->
      forall w1 (ω01 : w0 ⊒ w1) (ι1 : SymInstance w1),
        ι0 = inst (sub_acc ω01) ι1 ->
        approx ι1 (four a0 ω01) a.
  Proof.
    unfold approx, ApproxBox.
    intros * H0 w1 ω01 ι1 ? w2 ω12 ι2 ? Hpc2.
    apply H0; auto.
    rewrite sub_acc_trans, inst_subst.
    now subst.
  Qed.
  Hint Resolve approx_four : core.

  Lemma approx_lift {AT A} `{InstLaws AT A} {w0 : World} (ι0 : SymInstance w0) (a : A) :
    approx ι0 (lift (T := AT) a) a.
  Proof.
    hnf. now rewrite inst_lift.
  Qed.
  Hint Resolve approx_lift : core.

  Ltac wsimpl :=
    repeat
      (try change (wctx (wsnoc ?w ?b)) with (ctx_snoc (wctx w) b);
       (* try change (wsub (@wred_sup ?w ?b ?t)) with (sub_snoc (sub_id (wctx w)) b t); *)
       try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b)));
       try change (sub_acc (@acc_refl ?w)) with (sub_id (wctx w));
       (* try change (wsub (@wsnoc_sup ?w ?b)) with (@sub_wk1 (wctx w) b); *)
       try change (wctx (wformula ?w ?fml)) with (wctx w);
       try change (sub_acc (@acc_formula_right ?w ?fml)) with (sub_id (wctx w));
       try change (sub_acc (@acc_formulas_right ?w ?fmls)) with (sub_id (wctx w));
       try change (wco (wformula ?w ?fml)) with (cons fml (wco w));
       try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t));
       try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx_remove xIn);
       try change (sub_acc (@acc_subst_right ?w _ _ ?xIn ?t)) with (sub_single xIn t);
       rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id,
         ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
         ?inst_lift, ?inst_sub_single_shift, ?inst_pathcondition_cons,
         ?sub_acc_trans, ?sub_acc_triangular, ?inst_triangular_right_inverse).
       (* repeat *)
       (*   match goal with *)
       (*   | |- approx _ (@smut_angelic _ _ _ _ _) (@cmut_angelic _ _ _) => *)
       (*     apply approx_angelic; auto *)
       (*   | |- approx _ (smut_pure _) (cmut_pure _) => *)
       (*     apply approx_pure; auto *)
       (*   | |- approx _ (smut_bind _ _) (cmut_bind _ _) => *)
       (*     apply approx_bind; auto *)
       (*   | |- forall (_ : World) (_ : SymInstance _), instpc (wco _) _ -> _ => *)
       (*     let w := fresh "w" in *)
       (*     let ι := fresh "ι" in *)
       (*     let Hpc := fresh "Hpc" in *)
       (*     intros w ι Hpc *)
       (*   end). *)

  Module Path.

    Lemma approx_angelic_binary
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@angelic_binary w) (@or).
    Proof.
      intros PS1 PC1 HP1 PS2 PC2 HP2.
      intros [H1|H2]; [left|right]; auto.
    Qed.

    Lemma approx_demonic_binary
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@demonic_binary w) (@and).
    Proof.
      intros PS1 PC1 HP1 PS2 PC2 HP2.
      intros [H1 H2]; split; auto.
    Qed.

  End Path.

  Module Dijk.

    Lemma approx_pure {AT A} `{Approx AT A} {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SDijk.pure AT w) CDijk.pure.
    Proof.
      intros t v tv.
      intros POST__s POST__c HPOST.
      unfold SDijk.pure, CDijk.pure.
      apply HPOST; auto. cbn.
      now rewrite inst_sub_id.
    Qed.

    Lemma approx_bind {AT A BT B} `{Approx AT A, Approx BT B}
          {w0 : World} (ι0 : SymInstance w0) (* (Hpc0 : instpc (wco w0) ι0) *) :
      approx ι0 (@SDijk.bind AT BT w0) (@CDijk.bind A B).
    Proof.
      (* cbv [approx ApproxBox ApproxImpl ApproxMut ApproxPath ApproxInst]. *)
      intros ms mc Hm fs fc Hf.
      intros POST__s POST__c HPOST.
      unfold SDijk.bind, CDijk.bind.
      apply Hm; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply Hf; auto.
      eapply approx_four; eauto.
    Qed.

    Lemma approx_angelic (x : option 𝑺) (σ : Ty) :
      forall {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@SDijk.angelic x σ w0) (@CDijk.angelic σ).
    Proof.
      intros w0 ι0 Hpc0.
      intros POST__s POST__c HPOST.
      intros [v Hwp]. exists v. revert Hwp.
      apply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
    Qed.

    Lemma approx_angelic_ctx {N : Set} {n : N -> 𝑺} {Δ : NCtx N Ty} :
      forall {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@SDijk.angelic_ctx N n w0 Δ) (@CDijk.angelic_ctx N Δ).
    Proof.
      induction Δ.
      - intros w0 ι0 Hpc0.
        intros POST__s POST__c HPOST.
        unfold SDijk.angelic_ctx, CDijk.angelic_ctx, T.
        apply HPOST; wsimpl; try reflexivity; auto.
      - destruct b as [x σ].
        intros w0 ι0 Hpc0 POST__s POST__c HPOST; cbn.
        apply approx_angelic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros t v tv.
        apply IHΔ; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ts vs tvs.
        apply HPOST; cbn; wsimpl; auto.
        rewrite tv, tvs. hnf.
        rewrite <- inst_persist.
        reflexivity.
    Qed.

    Lemma approx_demonic (x : option 𝑺) (σ : Ty) :
      forall {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@SDijk.demonic x σ w0) (@CDijk.demonic σ).
    Proof.
      intros w0 ι0 Hpc0.
      intros POST__s POST__c HPOST.
      intros Hwp v.
      specialize (Hwp v).
      revert Hwp.
      eapply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
    Qed.

    Lemma approx_demonic_ctx {N : Set} {n : N -> 𝑺} {Δ : NCtx N Ty} :
      forall {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@SDijk.demonic_ctx N n w0 Δ) (@CDijk.demonic_ctx N Δ).
    Proof.
      induction Δ.
      - intros w0 ι0 Hpc0.
        intros POST__s POST__c HPOST.
        unfold SDijk.demonic_ctx, CDijk.demonic_ctx, T.
        apply HPOST; wsimpl; try reflexivity; auto.
      - destruct b as [x σ].
        intros w0 ι0 Hpc0 POST__s POST__c HPOST; cbn.
        apply approx_demonic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros t v tv.
        apply IHΔ; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ts vs tvs.
        apply HPOST; cbn; wsimpl; auto.
        rewrite tv, tvs. hnf.
        rewrite <- inst_persist.
        reflexivity.
    Qed.

    Lemma approx_assume_formulas {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0)
      (fmls0 : List Formula w0) (P : Prop) (Heq : instpc fmls0 ι0 <-> P) :
      approx ι0 (@SDijk.assume_formulas w0 fmls0) (@CDijk.assume_formula P).
    Proof.
      intros POST__s POST__c HPOST. unfold SDijk.assume_formulas.
      intros Hwp Hfmls0. apply Heq in Hfmls0.
      destruct (Solver.solver_spec w0 fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0).
        destruct Hsolver as [Hν Hsolver]. inster Hν by auto.
        specialize (Hsolver (inst (sub_triangular_inv ζ) ι0)).
        rewrite inst_triangular_right_inverse in Hsolver; auto.
        inster Hsolver by now try apply entails_triangular_inv.
        destruct Hsolver as [Hsolver _]. inster Hsolver by auto.
        rewrite safe_assume_triangular, safe_assume_formulas_without_solver in Hwp.
        specialize (Hwp Hν Hsolver). revert Hwp.
        unfold four. apply HPOST; cbn; wsimpl; auto.
        rewrite inst_pathcondition_app. split; auto.
        now apply entails_triangular_inv.
      - intuition.
    Qed.

    Lemma approx_assume_formula {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0)
      (fml : Formula w0) (P : Prop) (Heq : inst fml ι0 <-> P) :
      approx ι0 (@SDijk.assume_formula w0 fml) (@CDijk.assume_formula P).
    Proof. unfold SDijk.assume_formula. now apply approx_assume_formulas. Qed.

    Lemma approx_assert_formulas {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0)
      (msg : Message w0) (fmls0 : List Formula w0) (P : Prop) (Heq : instpc fmls0 ι0 <-> P) :
      approx ι0 (@SDijk.assert_formulas w0 msg fmls0) (@CDijk.assert_formula P).
    Proof.
      unfold SDijk.assert_formulas, CDijk.assert_formula.
      intros POST__s POST__c HPOST Hwp.
      destruct (Solver.solver_spec w0 fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [_ Hsolver].
        rewrite safe_assert_triangular in Hwp. destruct Hwp as [Hν Hwp].
        rewrite safe_assert_formulas_without_solver in Hwp.
        destruct Hwp as [Hfmls Hwp].
        split.
        + apply Hsolver in Hfmls; rewrite ?inst_triangular_right_inverse; auto.
          now apply Heq.
          now apply entails_triangular_inv.
        + revert Hwp. unfold four.
          apply HPOST; cbn; wsimpl; eauto.
          rewrite inst_pathcondition_app. split; auto.
          now apply entails_triangular_inv.
      - intuition.
    Qed.

    Lemma approx_assert_formula {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0)
      (msg : Message w0) (fml : Formula w0) (P : Prop) (Heq : inst fml ι0 <-> P) :
      approx ι0 (@SDijk.assert_formula w0 msg fml) (@CDijk.assert_formula P).
    Proof. unfold SDijk.assert_formula. now apply approx_assert_formulas. Qed.

    Lemma approx_angelic_list {AT A} `{Inst AT A}
      {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) msg :
      approx ι0 (@SDijk.angelic_list AT w0 msg) (@CDijk.angelic_list A).
    Proof.
      intros xs ? ->.
      induction xs; cbn - [inst];
        intros POST__s POST__c HPOST.
      - intros [].
      - cbn.
        apply Path.approx_angelic_binary; auto.
        apply HPOST; wsimpl; auto.
    Qed.

    Lemma approx_demonic_list {AT A} `{Inst AT A}
      {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) :
      approx ι0 (@SDijk.demonic_list AT w0) (@CDijk.demonic_list A).
    Proof.
      intros xs ? ->.
      induction xs; cbn - [inst];
        intros POST__s POST__c HPOST.
      - constructor.
      - cbn.
        apply Path.approx_demonic_binary; auto.
        apply HPOST; wsimpl; auto.
    Qed.

    Lemma approx_angelic_finite {F} `{finite.Finite F}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) msg :
      approx (AT := SDijkstra (Const F)) ι (@SDijk.angelic_finite F _ _ w msg) (@CDijk.angelic_finite F _ _).
    Proof.
      unfold SDijk.angelic_finite, CDijk.angelic_finite.
      intros POST__s POST__c HPOST.
      apply approx_angelic_list; eauto.
      hnf. cbv [inst instantiate_const instantiate_list].
      now rewrite List.map_id.
    Qed.

    Lemma approx_demonic_finite {F} `{finite.Finite F}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx (AT := SDijkstra (Const F)) ι (@SDijk.demonic_finite F _ _ w) (@CDijk.demonic_finite F _ _).
    Proof.
      unfold SDijk.demonic_finite, CDijk.demonic_finite.
      intros POST__s POST__c HPOST.
      apply approx_demonic_list; eauto.
      hnf. cbv [inst instantiate_const instantiate_list].
      now rewrite List.map_id.
    Qed.

    (* Lemma approx_angelic_match_bool {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) *)
    (*   (msg : Message w) : *)
    (*   approx ι (@SDijk.angelic_match_bool w msg) (@CDijk.angelic_match_bool). *)
    (* Proof. *)
    (*   intros t v ->. *)
    (*   unfold SDijk.angelic_match_bool. *)
    (*   destruct (term_get_lit_spec t). *)
    (*   - apply approx_pure; auto. *)
    (*   - unfold SDijk.angelic_match_bool'. *)
    (*     intros POST__s POST__c HPOST. *)
    (*     cbv [SDijk.angelic_binary SDijk.bind CDijk.pure SDijk.assert_formula]. *)
    (*     hnf. *)
    (*     intros δs δc Hδ hs hc Hh. *)
    (*     hnf. rewrite CMut.wp_angelic_match_bool. *)
    (*     destruct a. *)
    (*     + apply Hkt; wsimpl; eauto. *)
    (*     + apply Hkf; wsimpl; eauto. *)
    (*   - now apply approx_angelic_match_bool'. *)
    (* Qed. *)

  End Dijk.

  Section Basics.

    Lemma approx_dijkstra {Γ AT A} `{Approx AT A}
      {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) :
      approx ι0 (@SMut.dijkstra Γ AT w0) (@CMut.dijkstra Γ A).
    Proof.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh.
      unfold SMut.dijkstra, CMut.dijkstra.
      apply Hm.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply HPOST; auto.
      hnf. rewrite inst_persist. apply Hδ.
      hnf. rewrite inst_persist. apply Hh.
    Qed.
    Hint Resolve approx_dijkstra : core.

    Lemma approx_block {AT A} `{Approx AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
      approx ι (@SMut.block Γ1 Γ2 AT w) CMut.block.
    Proof. unfold approx, ApproxMut, ApproxImpl. auto. Qed.

    Lemma approx_error {AT A D} `{Approx AT A} {Γ1 Γ2} {w : World} {ι: SymInstance w} (func msg : string) (d : D) (cm : CMut Γ1 Γ2 A) :
      approx ι (@SMut.error Γ1 Γ2 AT D func msg d w) cm.
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh [].
    Qed.
    Hint Resolve approx_error : core.

    Lemma approx_pure {AT A} `{Approx AT A} {Γ} {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.pure Γ AT w) CMut.pure.
    Proof.
      intros t v tv.
      intros POST__s POST__c HPOST.
      unfold SMut.pure, CMut.pure.
      apply HPOST; auto. cbn.
      now rewrite inst_sub_id.
    Qed.

    Lemma approx_bind {AT A BT B} `{Approx AT A, Approx BT B}
      {Γ1 Γ2 Γ3} {w0 : World} (ι0 : SymInstance w0) (* (Hpc0 : instpc (wco w0) ι0) *) :
      approx ι0 (@SMut.bind Γ1 Γ2 Γ3 AT BT w0) (@CMut.bind Γ1 Γ2 Γ3 A B).
    Proof.
      (* cbv [approx ApproxBox ApproxImpl ApproxMut ApproxPath ApproxInst]. *)
      intros ms mc Hm fs fc Hf.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      unfold SMut.bind, CMut.bind.
      apply Hm; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply Hf; auto.
      eapply approx_four; eauto.
    Qed.

    Lemma approx_bind_right {AT A BT B} `{Approx AT A, Approx BT B}
      {Γ1 Γ2 Γ3} {w0 : World} (ι0 : SymInstance w0) (* (Hpc0 : instpc (wco w0) ι0) *) :
      approx ι0 (@SMut.bind_right Γ1 Γ2 Γ3 AT BT w0) (@CMut.bind_right Γ1 Γ2 Γ3 A B).
    Proof.
      intros ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      unfold SMut.bind_right, CMut.bind_right, CMut.bind.
      apply Hm1; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply Hm2; auto.
      eapply approx_four; eauto.
    Qed.

    Lemma approx_angelic (x : option 𝑺) (σ : Ty)
      {Γ : PCtx} {w0 : World} (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0) :
      approx ι0 (@SMut.angelic Γ x σ w0) (@CMut.angelic Γ σ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      intros [v Hwp]; exists v; revert Hwp.
      apply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
    Qed.
    Hint Resolve approx_angelic : core.

    Lemma approx_demonic (x : option 𝑺) (σ : Ty)
      {Γ : PCtx} {w0 : World} (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0) :
      approx ι0 (@SMut.demonic Γ x σ w0) (@CMut.demonic Γ σ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      intros Hwp v. cbn in Hwp. specialize (Hwp v). revert Hwp.
      apply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
    Qed.
    Hint Resolve approx_demonic : core.

    Lemma approx_angelic_ctx {N : Set} (n : N -> 𝑺) {Γ : PCtx} (Δ : NCtx N Ty) :
      forall {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@SMut.angelic_ctx N n Γ w0 Δ) (@CMut.angelic_ctx N Γ Δ).
    Proof.
      intros w0 ι0 Hpc0. unfold SMut.angelic_ctx, CMut.angelic_ctx.
      apply approx_dijkstra; auto.
      now apply Dijk.approx_angelic_ctx.
    Qed.

    Lemma approx_demonic_ctx {N : Set} (n : N -> 𝑺) {Γ : PCtx} (Δ : NCtx N Ty) :
      forall {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@SMut.demonic_ctx N n Γ w0 Δ) (@CMut.demonic_ctx N Γ Δ).
    Proof.
      intros w0 ι0 Hpc0. unfold SMut.demonic_ctx, CMut.demonic_ctx.
      apply approx_dijkstra; auto.
      now apply Dijk.approx_demonic_ctx.
    Qed.

    Lemma approx_debug {AT A DT D} `{Approx AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2} {w0 : World} (ι0 : SymInstance w0)
          (Hpc : instpc (wco w0) ι0) f ms mc :
      approx ι0 ms mc ->
      approx ι0 (@SMut.debug AT DT D _ _ _ Γ1 Γ2 w0 f ms) mc.
    Proof.
      intros Hap.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      unfold SMut.debug. hnf.
      cbn. intros [HP]. revert HP.
      apply Hap; auto.
    Qed.

    Lemma approx_angelic_binary {AT A} `{Approx AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
      approx ι (@SMut.angelic_binary Γ1 Γ2 AT w) (@CMut.angelic_binary Γ1 Γ2 A).
    Proof.
      intros ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      unfold SMut.angelic_binary, CMut.angelic_binary.
      intros [HYP|HYP]; [left|right]; revert HYP.
      - apply Hm1; auto.
      - apply Hm2; auto.
    Qed.

    Lemma approx_demonic_binary {AT A} `{Approx AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
      approx ι (@SMut.demonic_binary Γ1 Γ2 AT w) (@CMut.demonic_binary Γ1 Γ2 A).
    Proof.
      intros ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      unfold SMut.demonic_binary, CMut.demonic_binary.
      intros [H1 H2]. split.
      - revert H1. apply Hm1; auto.
      - revert H2. apply Hm2; auto.
    Qed.

    Lemma approx_angelic_list {AT A} `{Inst AT A} {Γ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) msg :
      approx ι (@SMut.angelic_list AT Γ w msg) (@CMut.angelic_list A Γ).
    Proof.
      intros ls lc Hl.
      unfold SMut.angelic_list, CMut.angelic_list.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
      apply approx_dijkstra; eauto.
      apply Dijk.approx_angelic_list; auto.
    Qed.

    Lemma approx_angelic_finite {F} `{finite.Finite F} {Γ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) msg :
      approx (AT := SMut Γ Γ (Const F)) ι (@SMut.angelic_finite Γ F _ _ w msg) (@CMut.angelic_finite Γ F _ _).
    Proof.
      unfold SMut.angelic_finite, CMut.angelic_finite.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
      eapply approx_dijkstra; eauto.
      apply Dijk.approx_angelic_finite; auto.
    Qed.

    Lemma approx_demonic_finite {F} `{finite.Finite F} {Γ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx (AT := SMut Γ Γ (Const F)) ι (@SMut.demonic_finite Γ F _ _ w) (@CMut.demonic_finite Γ F _ _).
    Proof.
      unfold SMut.demonic_finite, CMut.demonic_finite.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
      eapply approx_dijkstra; eauto.
      apply Dijk.approx_demonic_finite; auto.
    Qed.

  End Basics.

  Section AssumeAssert.

    Lemma approx_assume_formula {Γ} {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      approx ι0 (@SMut.assume_formula Γ w0 fml__s) (CMut.assume_formula fml__c).
    Proof.
      unfold SMut.assume_formula, CMut.assume_formula.
      apply approx_dijkstra; auto.
      now apply Dijk.approx_assume_formula.
    Qed.

    Lemma approx_box_assume_formula {Γ} {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      approx ι0 (@SMut.box_assume_formula Γ w0 fml__s) (CMut.assume_formula fml__c).
    Proof.
      unfold SMut.box_assume_formula, map_box.
      intros w1 ω01 ι1 -> Hpc1.
      apply approx_assume_formula; auto.
      now rewrite inst_persist.
    Qed.

    Lemma approx_assert_formula {Γ} {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      approx ι0 (@SMut.assert_formula Γ w0 fml__s) (@CMut.assert_formula Γ fml__c).
    Proof.
      unfold SMut.assert_formula, CMut.assert_formula.
      intros POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh.
      apply approx_dijkstra; auto.
      now apply Dijk.approx_assert_formula.
    Qed.

    Lemma approx_box_assert_formula {Γ} {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      approx ι0 (@SMut.box_assert_formula Γ w0 fml__s) (CMut.assert_formula fml__c).
    Proof.
      unfold SMut.box_assert_formula, map_box.
      intros w1 ω01 ι1 -> Hpc1.
      apply approx_assert_formula; auto.
      now rewrite inst_persist.
    Qed.

    Lemma approx_assert_formulas {Γ} {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0)
      (fmls__s : List Formula w0) (fmls__c : Prop) (Hfmls : fmls__c <-> instpc fmls__s ι0) :
      approx ι0 (@SMut.assert_formulas Γ w0 fmls__s) (@CMut.assert_formula Γ fmls__c).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      unfold SMut.assert_formulas, CMut.assert_formula.
      apply approx_dijkstra; auto.
      now apply Dijk.approx_assert_formulas.
    Qed.

  End AssumeAssert.

  Section PatternMatching.

    Lemma approx_angelic_match_bool' {AT A} `{Approx AT A} {Γ1 Γ2}
      {w : World} (ι : SymInstance w) (Hpc: instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_bool' AT Γ1 Γ2 w) (CMut.angelic_match_bool (A := A)).
    Proof.
      unfold SMut.angelic_match_bool', CMut.angelic_match_bool.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      apply approx_angelic_binary; eauto.
      apply approx_bind_right; eauto.
      apply approx_assert_formula; eauto.
      apply approx_bind_right; eauto.
      apply approx_assert_formula; eauto.
      cbn. unfold is_true. now rewrite negb_true_iff.
    Qed.

    Lemma approx_angelic_match_bool {AT A} `{Approx AT A} {Γ1 Γ2}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_bool AT Γ1 Γ2 w) (CMut.angelic_match_bool (A := A)).
    Proof.
      unfold SMut.angelic_match_bool.
      intros t v ->.
      destruct (term_get_lit_spec t).
      - rewrite H0.
        intros kt__s kt__c Hkt.
        intros kf__s kf__c Hkf.
        intros POST__s POST__c HPOST.
        intros δs δc Hδ hs hc Hh.
        hnf. rewrite CMut.wp_angelic_match_bool.
        destruct a.
        + apply Hkt; wsimpl; eauto.
        + apply Hkf; wsimpl; eauto.
      - now apply approx_angelic_match_bool'.
    Qed.

    Lemma approx_box_angelic_match_bool {AT A} `{Approx AT A} {Γ1 Γ2}
      {w : World} (ι : SymInstance w) :
      approx ι (@SMut.box_angelic_match_bool AT Γ1 Γ2 w) (CMut.angelic_match_bool (A := A)).
    Proof.
      unfold SMut.box_angelic_match_bool, map_box, K.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      intros w1 ω01 ι1 -> Hpc1.
      apply approx_angelic_match_bool; wsimpl; eauto.
      rewrite <- inst_persist; auto.
    Qed.

    Lemma approx_demonic_match_bool' {AT A} `{Approx AT A} {Γ1 Γ2}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_bool' AT Γ1 Γ2 w) (CMut.demonic_match_bool (A := A)).
    Proof.
      unfold SMut.demonic_match_bool, CMut.demonic_match_bool.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      apply approx_demonic_binary; eauto.
      apply approx_bind_right; eauto.
      apply approx_assume_formula; eauto.
      apply approx_bind_right; eauto.
      apply approx_assume_formula; eauto.
      cbn. unfold is_true. now rewrite negb_true_iff.
    Qed.

    Lemma approx_demonic_match_bool {AT A} `{Approx AT A} {Γ1 Γ2} {w : World}
      (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_bool AT Γ1 Γ2 w) (CMut.demonic_match_bool (A := A)).
    Proof.
      unfold SMut.demonic_match_bool.
      intros t v ->.
      destruct (term_get_lit_spec t).
      - rewrite H0.
        intros kt__s kt__c Hkt.
        intros kf__s kf__c Hkf.
        intros POST__s POST__c HPOST.
        intros δs δc Hδ hs hc Hh.
        hnf. rewrite CMut.wp_demonic_match_bool.
        destruct a.
        + apply Hkt; wsimpl; eauto.
        + apply Hkf; wsimpl; eauto.
      - now apply approx_demonic_match_bool'.
    Qed.

    Lemma approx_box_demonic_match_bool {AT A} `{Approx AT A} {Γ1 Γ2} 
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.box_demonic_match_bool AT Γ1 Γ2 w) (CMut.demonic_match_bool (A := A)).
    Proof.
      unfold SMut.box_demonic_match_bool, map_box, K.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      intros w1 ω01 ι1 -> Hpc1.
      apply approx_demonic_match_bool; wsimpl; eauto.
      rewrite <- inst_persist. auto.
    Qed.

    Lemma approx_angelic_match_enum {AT A} `{Approx AT A} {E : 𝑬} {Γ1 Γ2 : PCtx}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_enum AT E Γ1 Γ2 w) (@CMut.angelic_match_enum A E Γ1 Γ2).
    Proof.
      intros t v ->.
      intros ks kc Hk.
      unfold SMut.angelic_match_enum, CMut.angelic_match_enum.
      apply approx_bind.
      apply approx_angelic_finite; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros EK1 EK2 ->.
      apply approx_bind_right.
      apply approx_assert_formula; cbn; wsimpl; auto.
      now rewrite <- inst_persist.
      intros w2 ω12 ι2 -> Hpc2.
      eapply Hk; wsimpl; auto.
    Qed.

    Lemma approx_demonic_match_enum {AT A} `{Approx AT A} {E : 𝑬} {Γ1 Γ2 : PCtx}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_enum AT E Γ1 Γ2 w) (@CMut.demonic_match_enum A E Γ1 Γ2).
    Proof.
      intros t v ->.
      intros ks kc Hk.
      unfold SMut.demonic_match_enum, CMut.demonic_match_enum.
      apply approx_bind.
      apply approx_demonic_finite; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros EK1 EK2 ->.
      apply approx_bind_right.
      apply approx_assume_formula; cbn; wsimpl; auto.
      now rewrite <- inst_persist.
      intros w2 ω12 ι2 -> Hpc2.
      eapply Hk; wsimpl; auto.
    Qed.

    Lemma approx_angelic_match_sum {AT A} `{Approx AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_sum AT Γ1 Γ2 x y σ τ w) (@CMut.angelic_match_sum A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros kl kl__c Hk__l.
      intros kr kr__c Hk__r.
      unfold SMut.angelic_match_sum, CMut.angelic_match_sum.
      eapply approx_angelic_binary, approx_bind.
      - eapply approx_bind; try (eapply approx_angelic; assumption).
        intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 ->.
        eapply approx_bind_right.
        * eapply approx_assert_formula; try assumption. cbn.
          now rewrite <- inst_persist.
        * intros w2 r12 ι2 -> Hpc2.
          eapply (approx_four Hk__l); eauto.
          now rewrite <- inst_persist.
      - now eapply approx_angelic.
      - intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 ->.
        eapply approx_bind_right.
        + eapply approx_assert_formula; try assumption.
          now rewrite <- inst_persist.
        + intros w2 r12 ι2 -> Hpc2.
          eapply (approx_four Hk__r); eauto.
          now rewrite <- inst_persist.
    Qed.

    Lemma approx_demonic_match_sum {AT A} `{Approx AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_sum AT Γ1 Γ2 x y σ τ w) (@CMut.demonic_match_sum A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros kl kl__c Hk__l.
      intros kr kr__c Hk__r.
      unfold SMut.demonic_match_sum, CMut.demonic_match_sum.
      eapply approx_demonic_binary, approx_bind.
      - eapply approx_bind; try (eapply approx_demonic; assumption).
        intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 ->.
        eapply approx_bind_right.
        * eapply approx_assume_formula; try assumption.
          now rewrite <- inst_persist.
        * intros w2 r12 ι2 -> Hpc2.
          eapply (approx_four Hk__l); eauto.
          now rewrite <- inst_persist.
      - now eapply approx_demonic.
      - intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 ->.
        eapply approx_bind_right.
        + eapply approx_assume_formula; try assumption.
          now rewrite <- inst_persist.
        + intros w2 r12 ι2 -> Hpc2.
          eapply (approx_four Hk__r); eauto.
          now rewrite <- inst_persist.
    Qed.

    Lemma approx_angelic_match_prod {AT A} `{Approx AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_prod AT Γ1 Γ2 x y σ τ w) (@CMut.angelic_match_prod A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.angelic_match_prod, CMut.angelic_match_prod.
      eapply approx_bind; try (eapply approx_angelic; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      eapply approx_bind; try (eapply approx_angelic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      eapply approx_bind_right.
      - eapply approx_assert_formula; try assumption. cbn - [Lit].
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Lit _)).
        rewrite (inst_persist (AT := STerm _) (A := Lit _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3.
        eapply (approx_four Hk); eauto.
        + now rewrite sub_acc_trans, inst_subst.
        + rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
        + now rewrite <- inst_persist.
    Qed.

    Lemma approx_demonic_match_prod {AT A} `{Approx AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_prod AT Γ1 Γ2 x y σ τ w) (@CMut.demonic_match_prod A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.demonic_match_prod, CMut.demonic_match_prod.
      apply approx_bind; try (eapply approx_demonic; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply approx_bind; try (eapply approx_demonic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      apply approx_bind_right.
      - apply approx_assume_formula; try assumption. cbn - [Lit].
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Lit _)).
        rewrite (inst_persist (AT := STerm _) (A := Lit _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3.
        eapply (approx_four Hk); eauto.
        + now rewrite sub_acc_trans, inst_subst.
        + rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
        + now rewrite <- inst_persist.
    Qed.

    Lemma approx_angelic_match_list {AT A} `{Approx AT A} {Γ1 Γ2} xhead xtail σ
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_list AT Γ1 Γ2 xhead xtail σ w) (@CMut.angelic_match_list A Γ1 Γ2 σ).
    Proof.
      intros t ? ->.
      intros sknil cknil Hknil.
      intros skcons ckcons Hkcons.
      unfold SMut.angelic_match_list, CMut.angelic_match_list.
      apply approx_angelic_binary.
      - apply approx_bind_right; auto.
        apply approx_assert_formula; auto.
      - apply approx_bind; auto.
        apply approx_angelic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros thead vhead ->.
        apply approx_bind; auto.
        apply approx_angelic; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ttail vtail ->.
        apply approx_bind_right; auto.
        + apply approx_assert_formula; auto.
          cbn - [Lit].
          change (inst_term ?t ?ι) with (inst t ι).
          rewrite (inst_persist (AT := STerm _) (A := Lit _)).
          rewrite (inst_persist (AT := STerm _) (A := Lit _)).
          now rewrite sub_acc_trans, inst_subst.
        + intros w3 ω23 ι3 -> Hpc3.
          apply Hkcons; wsimpl; eauto.
          rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
          now rewrite <- inst_persist.
    Qed.

    Lemma approx_demonic_match_list {AT A} `{Approx AT A} {Γ1 Γ2} xhead xtail σ
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_list AT Γ1 Γ2 xhead xtail σ w) (@CMut.demonic_match_list A Γ1 Γ2 σ).
    Proof.
      intros t ? ->.
      intros sknil cknil Hknil.
      intros skcons ckcons Hkcons.
      unfold SMut.demonic_match_list, CMut.demonic_match_list.
      apply approx_demonic_binary.
      - apply approx_bind_right; auto.
        apply approx_assume_formula; auto.
      - apply approx_bind; auto.
        apply approx_demonic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros thead vhead ->.
        apply approx_bind; auto.
        apply approx_demonic; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ttail vtail ->.
        apply approx_bind_right; auto.
        + apply approx_assume_formula; auto.
          cbn - [Lit].
          change (inst_term ?t ?ι) with (inst t ι).
          rewrite (inst_persist (AT := STerm _) (A := Lit _)).
          rewrite (inst_persist (AT := STerm _) (A := Lit _)).
          now rewrite sub_acc_trans, inst_subst.
        + intros w3 ω23 ι3 -> Hpc3.
          apply Hkcons; wsimpl; eauto.
          rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
          now rewrite <- inst_persist.
    Qed.

    Lemma approx_angelic_match_record' {N : Set} (n : N -> 𝑺) {R AT A} `{Approx AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (𝑹𝑭_Ty R) Δ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_record' N n AT R Γ1 Γ2 Δ p w) (@CMut.angelic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.angelic_match_record', CMut.angelic_match_record.
      eapply approx_bind; try (eapply approx_angelic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply approx_bind_right.
      - apply approx_assert_formula; try assumption. cbn - [Lit].
        now rewrite <- inst_persist, (inst_record_pattern_match_reverse ι1 p).
      - intros w2 r12 ι2 -> Hpc2.
        eapply (approx_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma approx_angelic_match_record {N : Set} (n : N -> 𝑺) {R AT A} `{Approx AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (𝑹𝑭_Ty R) Δ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_record N n AT R Γ1 Γ2 Δ p w) (@CMut.angelic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros c c__c Hc.
      unfold SMut.angelic_match_record.
      destruct (term_get_record_spec t).
      - intros P2 Pc2 HP2.
        intros c2 cc2 Hc2.
        intros s2 sc2 Hs2.
        hnf.
        rewrite CMut.wp_angelic_match_record.
        apply Hc; wsimpl; eauto.
        hnf.
        unfold record_pattern_match_lit.
        rewrite H0. rewrite 𝑹_unfold_fold.
        symmetry.
        apply inst_record_pattern_match.
      - apply approx_angelic_match_record'; auto.
    Qed.

    Lemma approx_demonic_match_record' {N : Set} (n : N -> 𝑺) {R AT A} `{Approx AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (𝑹𝑭_Ty R) Δ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_record' N n AT R Γ1 Γ2 Δ p w) (@CMut.demonic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.demonic_match_record', CMut.demonic_match_record.
      eapply approx_bind. try (eapply approx_demonic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      eapply approx_bind_right.
      - eapply approx_assume_formula; try assumption. cbn - [Lit].
        now rewrite <- inst_persist, (inst_record_pattern_match_reverse ι1 p).
      - intros w2 r12 ι2 -> Hpc2.
        eapply (approx_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma approx_demonic_match_record {N : Set} (n : N -> 𝑺) {R AT A} `{Approx AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (𝑹𝑭_Ty R) Δ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_record N n AT R Γ1 Γ2 Δ p w) (@CMut.demonic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros c c__c Hc.
      unfold SMut.demonic_match_record.
      destruct (term_get_record_spec t).
      - intros P2 Pc2 HP2.
        intros c2 cc2 Hc2.
        intros s2 sc2 Hs2.
        hnf.
        rewrite CMut.wp_demonic_match_record.
        apply Hc; wsimpl; eauto.
        hnf.
        unfold record_pattern_match_lit.
        rewrite H0. rewrite 𝑹_unfold_fold.
        change (fun Σ => @Env (N * Ty) (fun τ => Term Σ (@snd N Ty τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
        now rewrite inst_record_pattern_match.
      - apply approx_demonic_match_record'; auto.
    Qed.

    Lemma approx_angelic_match_tuple {N : Set} (n : N -> 𝑺) {σs AT A} `{Approx AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : TuplePat σs Δ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_tuple N n AT σs Γ1 Γ2 Δ p w) (@CMut.angelic_match_tuple N A σs Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.angelic_match_tuple, CMut.angelic_match_tuple.
      apply approx_bind; try (apply approx_angelic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      change (fun Σ => @Env (N * Ty) (fun τ => Term Σ (@snd N Ty τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      apply approx_bind_right.
      - apply approx_assert_formula; try assumption. cbn - [Lit].
        rewrite inst_term_tuple.
        rewrite inst_tuple_pattern_match_reverse.
        rewrite <- inst_persist.
        unfold tuple_pattern_match_lit.
        split; intros <-.
        + now rewrite tuple_pattern_match_env_inverse_left, envrec_env_inverse_left.
        + now rewrite envrec_env_inverse_right, tuple_pattern_match_env_inverse_right.
      - intros w2 r12 ι2 -> Hpc2.
        eapply (approx_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma approx_demonic_match_tuple {N : Set} (n : N -> 𝑺) {σs AT A} `{Approx AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : TuplePat σs Δ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_tuple N n AT σs Γ1 Γ2 Δ p w) (@CMut.demonic_match_tuple N A σs Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.demonic_match_tuple, CMut.demonic_match_tuple.
      apply approx_bind; try (apply approx_demonic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      change (fun Σ => @Env (N * Ty) (fun τ => Term Σ (@snd N Ty τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      apply approx_bind_right.
      - apply approx_assume_formula; try assumption. cbn - [Lit].
        rewrite inst_term_tuple.
        rewrite inst_tuple_pattern_match_reverse.
        rewrite <- inst_persist.
        unfold tuple_pattern_match_lit.
        split; intros <-.
        + now rewrite tuple_pattern_match_env_inverse_left, envrec_env_inverse_left.
        + now rewrite envrec_env_inverse_right, tuple_pattern_match_env_inverse_right.
      - intros w2 r12 ι2 -> Hpc2.
        eapply (approx_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma approx_angelic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty}
          {p : Pattern Δ σ} {Γ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) {msg} :
      approx ι (@SMut.angelic_match_pattern N n σ Δ p Γ w msg) (@CMut.angelic_match_pattern N σ Δ p Γ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.angelic_match_pattern, CMut.angelic_match_pattern.
      eapply approx_bind; try (eapply approx_angelic_ctx; assumption); try assumption.
      intros w1 r01 ι1 -> Hpc1.
      intros ts vs ->.
      change (fun Σ => @Env (N * Ty) (fun τ => Term Σ (@snd N Ty τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      eapply approx_bind_right.
      - eapply approx_assert_formula; try assumption. cbn - [Lit].
        rewrite inst_pattern_match_env_reverse.
        rewrite <- inst_persist.
        split; intros <-.
        + now rewrite pattern_match_lit_inverse_left.
        + now rewrite pattern_match_lit_inverse_right.
      - intros w2 r12 ι2 -> Hpc2.
        eapply approx_pure; try assumption.
        now rewrite <- inst_persist.
    Qed.

    Lemma approx_angelic_match_union {N : Set} (n : N -> 𝑺) {AT A} `{Approx AT A} {Γ1 Γ2 : PCtx} {U : 𝑼}
      {Δ : 𝑼𝑲 U -> NCtx N Ty} {p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.angelic_match_union N n AT Γ1 Γ2 U Δ p w) (@CMut.angelic_match_union N A Γ1 Γ2 U Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.angelic_match_union, CMut.angelic_match_union.
      apply approx_bind; try (apply approx_angelic_finite; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply approx_bind; try (apply approx_angelic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      eapply approx_bind_right.
      - eapply approx_assert_formula; try assumption. cbn - [Lit].
        change (inst v1 _) with v1.
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Lit _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3.
        eapply approx_bind.
        + eapply approx_angelic_match_pattern; try assumption.
          now rewrite <- inst_persist.
        + change (inst v1 _) with v1.
          specialize (Hk v1).
          eapply (approx_four Hk).
          now rewrite ?sub_acc_trans, ?inst_subst.
    Qed.

    Lemma approx_demonic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty}
          {p : Pattern Δ σ} {Γ}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_pattern N n σ Δ p Γ w) (@CMut.demonic_match_pattern N σ Δ p Γ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.demonic_match_pattern, CMut.demonic_match_pattern.
      eapply approx_bind; try (eapply approx_demonic_ctx; assumption); try assumption.
      intros w1 r01 ι1 -> Hpc1.
      intros ts vs ->.
      change (fun Σ => @Env (N * Ty) (fun τ => Term Σ (@snd N Ty τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      eapply approx_bind_right.
      - eapply approx_assume_formula; try assumption. cbn - [Lit].
        rewrite inst_pattern_match_env_reverse.
        rewrite <- inst_persist.
        split; intros <-.
        + now rewrite pattern_match_lit_inverse_left.
        + now rewrite pattern_match_lit_inverse_right.
      - intros w2 r12 ι2 -> Hpc2.
        eapply approx_pure; try assumption.
        now rewrite <- inst_persist.
    Qed.

    Lemma approx_demonic_match_union {N : Set} (n : N -> 𝑺) {AT A} `{Approx AT A} {Γ1 Γ2 : PCtx} {U : 𝑼}
      {Δ : 𝑼𝑲 U -> NCtx N Ty} {p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)}
      {w : World} (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
      approx ι (@SMut.demonic_match_union N n AT Γ1 Γ2 U Δ p w) (@CMut.demonic_match_union N A Γ1 Γ2 U Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SMut.demonic_match_union, CMut.demonic_match_union.
      eapply approx_bind; try (eapply approx_demonic_finite; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      eapply approx_bind; try (eapply approx_demonic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      eapply approx_bind_right.
      - eapply approx_assume_formula; try assumption. cbn - [Lit].
        change (inst v1 _) with v1.
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Lit _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3.
        eapply approx_bind.
        + eapply approx_demonic_match_pattern; try assumption.
          now rewrite <- inst_persist.
        + change (inst v1 _) with v1.
          specialize (Hk v1).
          eapply (approx_four Hk).
          now rewrite ?sub_acc_trans, ?inst_subst.
    Qed.

  End PatternMatching.

  Section State.

    Lemma approx_pushpop {AT A} `{Approx AT A} {Γ1 Γ2 x σ} {w0 : World} (ι0 : SymInstance w0)
          (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.pushpop AT Γ1 Γ2 x σ w0) (@CMut.pushpop A Γ1 Γ2 x σ).
    Proof.
      intros t v ->.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh0.
      unfold SMut.pushpop, CMut.pushpop.
      apply Hm; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      intros δs1 δc1 -> hs1 hc1 Hh1.
      apply HPOST; auto.
      now destruct (snocView δs1).
    Qed.

    Lemma approx_pushspops {AT A} `{Approx AT A} {Γ1 Γ2 Δ} {w0 : World} (ι0 : SymInstance w0)
          (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.pushspops AT Γ1 Γ2 Δ w0) (@CMut.pushspops A Γ1 Γ2 Δ).
    Proof.
      intros δΔ ? ->.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh0.
      unfold SMut.pushspops, CMut.pushspops.
      apply Hm; auto.
      - intros w1 ω01 ι1 -> Hpc1.
        intros a1 a Ha.
        intros δs1 δc1 -> hs1 hc1 ->.
        apply HPOST; auto.
        destruct (catView δs1).
        hnf.
        unfold inst at 1; cbn.
        rewrite <- env_map_drop.
        rewrite ?env_drop_cat.
        reflexivity.
      - hnf.
        unfold inst at 3; cbn.
        rewrite env_map_cat.
        reflexivity.
    Qed.

    Lemma approx_get_local {Γ}
      {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.get_local Γ w0) (@CMut.get_local Γ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SMut.get_local, CMut.get_local.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma approx_put_local {Γ1 Γ2}
      {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.put_local Γ1 Γ2 w0) (@CMut.put_local Γ1 Γ2).
    Proof.
      intros δs2 δc2 Hδ2.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SMut.put_local, CMut.put_local.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma approx_get_heap {Γ}
      {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.get_heap Γ w0) (@CMut.get_heap Γ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SMut.get_heap, CMut.get_heap.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma approx_put_heap {Γ}
      {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.put_heap Γ w0) (@CMut.put_heap Γ).
    Proof.
      intros hs hc Hh.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SMut.put_heap, CMut.put_heap.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma approx_eval_exp {Γ σ} (e : Exp Γ σ)
      {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.eval_exp Γ σ e w0) (@CMut.eval_exp Γ σ e).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh.
      apply HPOST; wsimpl; rewrite ?inst_sub_id; auto.
      hnf. now rewrite <- eval_exp_inst.
    Qed.

    Lemma approx_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w0 : World} (ι0 : SymInstance w0)
          (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.eval_exps Γ Δ es w0) (@CMut.eval_exps Γ Δ es).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh.
      change (@instantiate_env _ _ _ _ ?Γ) with (@inst_localstore Γ).
      apply HPOST; auto. cbn. rewrite ?inst_sub_id; auto.
      apply env_lookup_extensional; cbn; intros [x σ] xIn.
      unfold evals, inst at 2; cbn. rewrite ?env_lookup_map.
      change (@instantiate_env _ _ _ _ ?Γ) with (@inst_localstore Γ).
      (* change (fun Σ : LCtx => @Env (𝑿 * Ty) (fun τ : 𝑿 * Ty => Term Σ (@snd 𝑿 Ty τ)) Γ) with (SStore Γ). *)
      now rewrite eval_exp_inst.
    Qed.

    Lemma approx_assign {Γ x σ} {xIn : x::σ ∈ Γ}
      {w0 : World} (ι0 : SymInstance w0) (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.assign Γ x σ xIn w0) (@CMut.assign Γ x σ xIn).
    Proof.
      intros t v ->.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh.
      unfold SMut.assign, CMut.assign.
      apply HPOST; wsimpl; eauto.
      hnf. unfold inst at 3. cbn.
      now rewrite env_map_update.
    Qed.

  End State.
  Hint Resolve approx_eval_exp : core.
  Hint Resolve approx_eval_exps : core.
  Hint Resolve approx_pushpop : core.
  Hint Resolve approx_pushspops : core.
  Hint Resolve approx_debug : core.

  Hint Resolve approx_demonic : core.
  Hint Resolve approx_bind : core.
  Hint Resolve approx_angelic_ctx : core.
  Hint Resolve approx_bind_right : core.

  Lemma approx_produce_chunk {Γ} {w0 : World} (ι0 : SymInstance w0)
    (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (@SMut.produce_chunk Γ w0) (CMut.produce_chunk).
  Proof.
    intros cs cc ->.
    intros POST__s POST__c HPOST.
    intros δs δc -> hs hc ->.
    unfold SMut.produce_chunk, CMut.produce_chunk.
    apply HPOST; cbn; rewrite ?inst_sub_id; auto.
  Qed.

  Lemma inst_env_cat {T : Set} {AT : LCtx -> T -> Set} {A : T -> Set}
     {instAT : forall τ : T, Inst (fun Σ : LCtx => AT Σ τ) (A τ)}
     {Σ : LCtx} {Γ Δ : Ctx T} (EΓ : Env (fun τ => AT Σ τ) Γ) (EΔ : Env (fun τ => AT Σ τ) Δ)
     (ι : SymInstance Σ) :
    inst (EΓ ►► EΔ) ι = inst EΓ ι ►► inst EΔ ι.
  Proof.
    unfold inst; cbn.
    now rewrite env_map_cat.
  Qed.

  Lemma inst_sub_cat {Σ Γ Δ : LCtx} (ζΓ : Sub Γ Σ) (ζΔ : Sub Δ Σ) (ι : SymInstance Σ) :
    inst (A := SymInstance _) (ζΓ ►► ζΔ) ι = inst ζΓ ι ►► inst ζΔ ι.
  Proof.
    apply (@inst_env_cat (𝑺 * Ty) (fun Σ b => Term Σ (snd b))).
  Qed.

  Lemma approx_produce {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.produce Γ w0 asn) (CMut.produce ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [wctx Lit].
    - now apply approx_box_assume_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply approx_produce_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_bool; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_enum; auto.
      intros EK1 EK2 HEK. hnf in HEK. subst EK2.
      eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_sum; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn1; cbn - [inst sub_wk1]; wsimpl; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_list; auto.
      eapply approx_four; eauto.
      intros w2 ω12 ι2 -> Hpc2.
      intros thead vhead ->.
      intros ttail vtail ->.
      apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_prod; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros t1 v1 -> t2 v2 ->.
      apply IHasn; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_tuple; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@instantiate_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_record; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@instantiate_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_demonic_match_union; auto.
      intros UK.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@instantiate_sub (alt__ctx UK)).
        fold (Sub (alt__ctx UK)).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_bind_right; eauto.
      apply IHasn1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_demonic_binary;
        try apply IHasn1; try apply IHasn2;
        cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_bind.
      apply approx_demonic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_debug; auto.
      apply approx_pure; auto.
  Qed.

  Lemma try_consume_chunk_exact_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
    OptionSpec
      (fun h' => List.In (c , h') (heap_extractions h))
      True
      (SMut.try_consume_chunk_exact h c).
  Proof.
    induction h as [|c' h].
    - now constructor.
    - cbn -[is_duplicable].
      destruct (chunk_eqb_spec c c').
      + constructor. left. subst.
        remember (is_duplicable c') as dup.
        destruct dup; reflexivity.
      + apply optionspec_map. revert IHh.
        apply optionspec_monotonic; auto.
        intros h' HIn. right.
        rewrite List.in_map_iff.
        exists (c :: h'). auto.
  Qed.

  Lemma inst_is_duplicable {w : World} (c : Chunk w) (ι : SymInstance w) :
    is_duplicable (inst c ι) = is_duplicable c.
  Proof.
    destruct c; now cbn.
  Qed.

  
  Lemma approx_consume_chunk {Γ} {w0 : World} (ι0 : SymInstance w0)
    (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (@SMut.consume_chunk Γ w0) (CMut.consume_chunk).
  Proof.
    intros cs cc ->.
    unfold SMut.consume_chunk, CMut.consume_chunk.
    apply approx_bind.
    apply approx_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    destruct (try_consume_chunk_exact_spec hs (persist cs ω01)) as [h' HIn|].
    - intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      unfold approx, ApproxPath. intros Hwp.
      cbv [SMut.put_heap CMut.bind CMut.put_heap CMut.bind_right CMut.assert_formula
                         T CMut.angelic_list CMut.dijkstra].
      rewrite CDijk.wp_angelic_list.
      change (SHeap w1) in h'.
      exists (inst (persist (A := Chunk) cs ω01) ι1, inst h' ι1).
      split.
      + unfold inst at 3. cbn. rewrite heap_extractions_map.
        rewrite List.in_map_iff. exists (persist (A := Chunk) cs ω01 , h').
        split. reflexivity. assumption.
        eauto using inst_is_duplicable.
      + hnf. rewrite inst_persist. split; auto. revert Hwp.
        apply HPOST; wsimpl; auto.
    - apply approx_bind.
      apply approx_angelic_list; eauto.
      { hnf. unfold inst at 1. cbn.
        rewrite heap_extractions_map.
        apply List.map_ext. now intros [].
        eauto using inst_is_duplicable.
      }
      intros w2 ω12 ι2 -> Hpc2.
      intros [cs' hs'] [cc' hc'].
      intros Hch'. inversion Hch'; subst; clear Hch'.
      apply approx_bind_right.
      apply approx_assert_formulas; auto.
      rewrite SMut.inst_match_chunk.
      rewrite inst_persist, sub_acc_trans, inst_subst. intuition.
      intros w3 ω23 ι3 -> Hpc3.
      rewrite <- inst_persist.
      apply approx_put_heap; auto.
  Qed.

  Lemma approx_consume {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.consume Γ w0 asn) (CMut.consume ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [wctx Lit].
    - now apply approx_box_assert_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply approx_consume_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_bool; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_enum; auto.
      intros EK1 EK2 HEK. hnf in HEK. subst EK2.
      eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_sum; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn1; cbn - [inst sub_wk1]; wsimpl; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_list; auto.
      eapply approx_four; eauto.
      intros w2 ω12 ι2 -> Hpc2.
      intros thead vhead ->.
      intros ttail vtail ->.
      apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_prod; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros t1 v1 -> t2 v2 ->.
      apply IHasn; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_tuple; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@instantiate_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_record; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@instantiate_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply approx_angelic_match_union; auto.
      intros UK.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@instantiate_sub (alt__ctx UK)).
        fold (Sub (alt__ctx UK)).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_bind_right; eauto.
      apply IHasn1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_angelic_binary;
        try apply IHasn1; try apply IHasn2;
        cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_bind.
      apply approx_angelic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_debug; auto.
      apply approx_pure; auto.
  Qed.

  Lemma approx_call_contract {Γ Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) :
    forall {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.call_contract Γ Δ τ c w0) (@CMut.call_contract Γ Δ τ c).
  Proof.
    destruct c; cbv [SMut.call_contract CMut.call_contract].
    intros w0 ι0 Hpc0.
    intros args__s args__c Hargs.
    apply approx_bind; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros evars__s evars__c Hevars.
    apply approx_bind_right.
    apply approx_assert_formulas; auto.
    { rewrite inst_formula_eqs_nctx.
      rewrite inst_persist, inst_subst.
      rewrite Hargs, Hevars.
      reflexivity.
    }
    intros w2 ω12 ι2 -> Hpc2.
    apply approx_bind_right.
    { apply approx_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3.
    apply approx_bind.
    { apply approx_demonic; auto. }
    intros w4 ω34 ι4 -> Hpc4.
    intros res__s res__c Hres.
    apply approx_bind_right.
    { apply approx_produce; auto.
      constructor.
      cbn - [instantiate_env sub_snoc].
      rewrite inst_sub_snoc, inst_persist, ?sub_acc_trans, ?inst_subst.
      now rewrite Hevars, Hres.
    }
    intros w5 ω45 ι5 -> Hpc5.
    apply approx_pure; auto.
    rewrite Hres. rewrite <- inst_persist.
    reflexivity.
  Qed.

  Lemma approx_call_lemma {Γ Δ : PCtx} (lem : Lemma Δ) :
    forall {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.call_lemma Γ Δ lem w0) (@CMut.call_lemma Γ Δ lem).
  Proof.
    destruct lem; cbv [SMut.call_lemma CMut.call_lemma].
    intros w0 ι0 Hpc0.
    intros args__s args__c Hargs.
    apply approx_bind; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros evars__s evars__c Hevars.
    apply approx_bind_right.
    apply approx_assert_formulas; auto.
    { rewrite inst_formula_eqs_nctx.
      rewrite inst_persist, inst_subst.
      rewrite Hargs, Hevars.
      reflexivity.
    }
    intros w2 ω12 ι2 -> Hpc2.
    apply approx_bind_right.
    { apply approx_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3.
    { apply approx_produce; auto.
      constructor.
      cbn - [instantiate_env sub_snoc].
      rewrite inst_persist, sub_acc_trans, inst_subst.
      now rewrite Hevars.
    }
  Qed.

  Lemma approx_exec {cfg Γ τ} (s : Stm Γ τ) :
    forall {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.exec cfg Γ τ s w0) (@CMut.exec Γ τ s).
  Proof.
    induction s; cbn; intros * ?.
    - apply approx_pure; auto.
    - now apply approx_eval_exp.
    - apply approx_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_pushpop; auto.
    - apply approx_pushspops; auto.
      apply approx_lift.
    - apply approx_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply approx_bind_right.
      apply approx_assign; auto.
      intros w2 ω12 ι2 -> Hpc2.
      rewrite <- inst_subst.
      apply approx_pure; auto.
    - apply approx_bind.
      apply approx_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      destruct (CEnv f).
      + unfold SMut.call_contract_debug.
        destruct (config_debug_function cfg f).
        apply approx_debug; auto.
        apply approx_call_contract; auto.
        apply approx_call_contract; auto.
      + apply approx_error.
    - apply approx_bind.
      apply approx_get_local; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros δs1 δc1 ->.
      apply approx_bind_right.
      apply approx_put_local; auto.
      apply approx_lift.
      intros w2 ω12 ι2 -> Hpc2.
      apply approx_bind; auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros t v ->.
      apply approx_bind_right.
      apply approx_put_local; auto.
      rewrite persist_subst.
      hnf. rewrite sub_acc_trans, ?inst_subst; auto.
      intros w4 ω34 ι4 -> Hpc4.
      rewrite <- inst_persist.
      apply approx_pure; auto.
    - apply approx_bind.
      apply approx_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      apply approx_call_contract; auto.
    - apply approx_bind_right; auto.
      apply approx_bind.
      apply approx_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      apply approx_call_lemma; auto.
    - apply approx_bind.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_bool; auto.
    - apply approx_bind_right; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply approx_bind_right.
      apply approx_assume_formula; auto.
      intros w2 ω12 ι2 -> Hpc2.
      now apply IHs.
    - apply approx_block.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_list; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros thead vhead ->.
      intros ttail vtail ->.
      apply approx_pushspops; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_sum; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros tl vl ->.
        apply approx_pushpop; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros tr vr ->.
        apply approx_pushpop; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_prod; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros t1 v1 ->.
      intros t2 v2 ->.
      apply approx_pushspops; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_enum; auto.
      intros EK1 EK2 ->.
      intros w2 ω12 ι2 -> Hpc2; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_tuple; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply approx_pushspops; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_union; auto.
      intros UK.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply approx_pushspops; auto.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_demonic_match_record; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply approx_pushspops; auto.
    - apply approx_bind; auto.
      apply approx_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply approx_bind_right; auto.
      apply approx_consume_chunk; auto.
      intros w2 ω12 ι2 -> Hpc2.
      apply approx_bind_right; auto.
      rewrite <- inst_persist.
      apply approx_produce_chunk; auto.
      intros w3 ω23 ι3 -> Hpc3.
      apply approx_pure; auto. hnf.
      rewrite (persist_trans (A := STerm _)).
      now rewrite <- ?inst_persist.
    - apply approx_bind; auto.
      apply approx_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros told v ->.
      apply approx_bind_right; auto.
      apply approx_consume_chunk; auto.
      intros w2 ω12 ι2 -> Hpc2.
      apply approx_bind; auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros tnew v ->.
      apply approx_bind_right; auto.
      apply approx_produce_chunk; auto.
      intros w4 ω34 ι4 -> Hpc4.
      apply approx_pure; auto.
      now rewrite <- inst_persist.
    - apply approx_error.
    - apply approx_debug; auto.
  Qed.

  Lemma approx_exec_contract {cfg : Config} {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) :
    let w0 := {| wctx := sep_contract_logic_variables c; wco := nil |} in
    forall (ι0 : SymInstance w0),
      approx (w := w0) ι0 (@SMut.exec_contract cfg Γ τ c s) (@CMut.exec_contract Γ τ c s ι0).
  Proof.
    unfold SMut.exec_contract, CMut.exec_contract; destruct c as [Σ δ pre result post]; cbn in *.
    intros ι0.
    apply approx_bind_right.
    apply approx_produce; wsimpl; cbn; auto.
    constructor. constructor.
    intros w1 ω01 ι1 -> Hpc1.
    apply approx_bind.
    apply approx_exec; auto.
    intros w2 ω12 ι2 -> Hpc2.
    intros res__s res__c Hres.
    apply approx_consume; cbn - [inst]; wsimpl; auto.
    constructor.
    f_equal; auto.
  Qed.

  Definition safe_demonic_close {Σ : LCtx} :
    forall p : SPath Σ,
      safe (demonic_close p) env_nil ->
      forall ι : SymInstance Σ,
        safe p ι.
  Proof.
    induction Σ; cbn [demonic_close] in *.
    - intros p Hwp ι.
      destruct (nilView ι). apply Hwp.
    - intros p Hwp ι.
      destruct b as [x σ], (snocView ι).
      now apply (IHΣ (demonicv (x :: σ) p)).
  Qed.

  Lemma symbolic_sound {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    SMut.ValidContract c body ->
    CMut.ValidContract c body.
  Proof.
    unfold SMut.ValidContract, CMut.ValidContract, ForallNamed.
    rewrite Forall_forall. intros [Hwp] ι.
    unfold SMut.exec_contract_path in Hwp.
    rewrite Postprocessing.prune_sound in Hwp.
    rewrite Postprocessing.solve_uvars_sound in Hwp.
    rewrite Postprocessing.prune_sound in Hwp.
    rewrite Postprocessing.solve_evars_sound in Hwp.
    rewrite Postprocessing.prune_sound in Hwp. cbn in Hwp.
    apply safe_demonic_close with _ ι in Hwp. revert Hwp.
    rewrite <- (wsafe_safe (w := @MkWorld (sep_contract_logic_variables c) nil)).
    apply approx_exec_contract; auto.
    intros w1 ω01 ι1 -> Hpc1.
    auto.
  Qed.

  (* Print Assumptions symbolic_sound. *)

End Soundness.
