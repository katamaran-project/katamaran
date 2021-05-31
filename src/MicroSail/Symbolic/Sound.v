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

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     Symbolic.Mutator.
From MicroSail Require Import
     SemiConcrete.Mutator
     SemiConcrete.Outcome
     SemiConcrete.Sound.

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
      forall (w : World) (ι : SymInstance w),
        AT w -> A -> Prop.
  Global Arguments approx {_ _ _ w} ι _ _.

  Global Instance ApproxInst {AT A} `{instA : Inst AT A} : Approx AT A :=
    fun w ι t v =>
      v = inst t ι.
  Global Arguments ApproxInst {_ _ _} w ι t v /.

  Global Instance ApproxPath : Approx SPath Prop :=
    fun w ι SP P => safe SP ι -> P.

  Global Instance ApproxBox {AT A} `{Approx AT A} : Approx (Box AT) A :=
    fun w0 ι0 a0 a =>
      forall (w1 : World) (ω01 : w0 ⊒ w1) (ι1 : SymInstance w1),
        ι0 = inst (wsub ω01) ι1 ->
        instpc (wco w1) ι1 ->
        approx ι1 (a0 w1 ω01) a.

  Global Instance ApproxImpl {AT A BT B} `{Approx AT A, Approx BT B} : Approx (Impl AT BT) (A -> B) :=
    fun w ι fs fc =>
      forall (ta : AT w) (a : A),
        approx ι ta a ->
        approx ι (fs ta) (fc a).

  Global Instance ApproxInj {A} : Approx (fun _ => A) A :=
    fun w ι a1 a2 => a1 = a2.

  (* Global Instance ApproxMutResult {AT A} `{Approx AT A} {Γ} : Approx (SMutResult Γ AT) (CMutResult Γ A). *)
  (* Proof. *)
  (*   intros w0 ι0 [a0 δ0 h0] [a δ h]. *)
  (*   refine (approx ι0 a0 a /\ approx ι0 δ0 δ /\ approx ι0 h0 h). *)
  (* Defined. *)

  Global Instance ApproxMut {Γ1 Γ2 AT A} `{instA : Inst AT A} : Approx (SMut Γ1 Γ2 AT) (CMut Γ1 Γ2 A).
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

  Global Instance ApproxNamedEnv {N : Set} {Δ : NCtx N Ty} :
    Approx (fun w => NamedEnv (Term w) Δ) (NamedEnv Lit Δ) :=
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

  Hint Unfold approx ApproxImpl ApproxBox ApproxInst ApproxPath ApproxMut ApproxTermLit ApproxNamedEnv : core.


  Lemma approx_four {AT A} `{Approx AT A} {w0 : World} (ι0 : SymInstance w0) :
    forall (a0 : Box AT w0) (a : A),
      approx ι0 a0 a ->
      forall w1 (ω01 : w0 ⊒ w1) (ι1 : SymInstance w1),
        ι0 = inst (wsub ω01) ι1 ->
        approx ι1 (four a0 ω01) a.
  Proof.
    unfold approx, ApproxBox. intros. apply H0; auto.
    unfold wtrans; cbn. rewrite inst_subst. now subst.
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
       try change (wsub (@wred_sup ?w ?b ?t)) with (sub_snoc (sub_id (wctx w)) b t);
       try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b)));
       try change (wsub (@wrefl ?w)) with (sub_id (wctx w));
       try change (wsub (@wsnoc_sup ?w ?b)) with (@sub_wk1 (wctx w) b);
       try change (wctx (wformula ?w ?fml)) with (wctx w);
       try change (wsub (wtrans ?ω1 ?ω2)) with (subst (wsub ω1) (wsub ω2));
       try change (wsub (@wformula_sup ?w ?fml)) with (sub_id (wctx w));
       try change (wco (wformula ?w ?fml)) with (cons fml (wco w));
       try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t));
       try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx_remove xIn);
       try change (wsub (@wsubst_sup ?w _ _ ?xIn ?t)) with (sub_single xIn t);
       rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id,
         ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
         ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons).
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

  Module dijk.

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
      intros [v Hwp]; exists v; revert Hwp.
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
        apply HPOST; wsimpl; auto.
      - destruct b as [x σ].
        intros w0 ι0 Hpc0 POST__s POST__c HPOST; cbn.
        apply approx_angelic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros t v tv.
        apply IHΔ; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ts vs tvs.
        apply HPOST; cbn; rewrite ?inst_subst; auto.
        rewrite tv, tvs. hnf.
        rewrite <- inst_subst.
        reflexivity.
    Qed.

    Lemma approx_assume_formula {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) (fml : Formula w0) (P : Prop) :
      (inst fml ι0 <-> P) ->
      approx ι0 (@SDijk.assume_formula w0 fml) (@CDijk.assume_formula P).
    Proof.
      intros Heq POST__s POST__c HPOST. unfold SDijk.assume_formula.
      intros Hwp Hfml. apply Heq in Hfml.
      destruct (solver_spec fml) as [[w1 [ζ fmls]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [Hν Hsolver].
        specialize (Hν Hfml). specialize (Hsolver (inst (sub_multishift ζ) ι0)).
        rewrite inst_multi in Hsolver; auto. specialize (Hsolver eq_refl).
        destruct Hsolver as [Hsolver _]. specialize (Hsolver Hfml).
        rewrite safe_assume_multisub, safe_assume_formulas_without_solver in Hwp.
        specialize (Hwp Hν Hsolver). revert Hwp.
        unfold four, wtrans, persist, persist_subst; cbn.
        wsimpl. apply HPOST; cbn; auto.
        rewrite inst_multi; auto.
        rewrite inst_pathcondition_app. split; auto.
        now apply multishift_entails.
      - intuition.
    Qed.

    Lemma approx_assume_formulas {w0 : World} (fmls : List Formula w0) (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) :
      approx ι0 (@SDijk.assume_formulas w0 fmls) (@CDijk.assume_formulas _ ι0 fmls).
    Proof.
      induction fmls; cbn.
      - apply approx_pure; auto.
      - apply approx_bind; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros ? ? ?.
        intros POST__s POST__c HPOST.
        intros Hwp.
        eapply approx_assume_formula in Hwp; eauto.
        now rewrite inst_subst.
    Qed.

  End dijk.

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
    hnf. rewrite inst_subst. apply Hδ.
    hnf. rewrite inst_subst. apply Hh.
  Qed.
  Hint Resolve approx_dijkstra : core.

  Lemma approx_block {AT A} `{Approx AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
    approx ι (@SMut.block Γ1 Γ2 AT w) CMut.block.
  Proof. auto. Qed.

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
    now apply dijk.approx_angelic_ctx.
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

  Lemma approx_assume_formula {Γ} {w0 : World} {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0)
    (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
    approx ι0 (@SMut.assume_formula Γ w0 fml__s) (CMut.assume_formula fml__c).
  Proof.
    unfold SMut.assume_formula, CMut.assume_formula.
    apply approx_dijkstra; auto.
    now apply dijk.approx_assume_formula.
  Qed.

  (* Lemma approx_assume_formulak {AT A} `{InstLaws AT A} {Γ1 Γ2} {w0 : World} {fml : Formula w0} *)
  (*   {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0) : *)
  (*   approx ι0 (@smutk_assume_formula AT Γ1 Γ2 w0 fml) (@cmut_assume_formulak A Γ1 Γ2 _ ι0 fml). *)
  (* Proof. *)
  (*   intros ms mc Hm δt δc Hδ hs hc Hh P Q PQ Hwp Hfml. *)
  (*   unfold smutk_assume_formula, assume_formulak in Hwp. *)
  (*   destruct (solver_spec fml) as [[w1 [ζ fmls]] Hsolver|Hsolver]. *)
  (*   - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [Hν Hsolver]. *)
  (*     specialize (Hν Hfml). specialize (Hsolver (inst (sub_multishift ζ) ι0)). *)
  (*     rewrite inst_multi in Hsolver; auto. specialize (Hsolver eq_refl). *)
  (*     destruct Hsolver as [Hsolver _]. specialize (Hsolver Hfml). *)
  (*     rewrite wp_assume_multisub, wp_assume_formulas_without_solver in Hwp. *)
  (*     specialize (Hwp Hν Hsolver). revert Hwp. *)
  (*     unfold four, smut_bpure, wtrans, persist, persist_subst, K; cbn. *)
  (*     wsimpl. apply Hm; cbn; wsimpl; auto. *)
  (*     + rewrite ?inst_multi; auto. *)
  (*     + rewrite inst_pathcondition_app. split; auto. *)
  (*       now apply multishift_entails. *)
  (*     + unfold approx, ApproxInst. cbn. *)
  (*       now rewrite inst_subst, inst_multi. *)
  (*     + unfold approx, ApproxInst. cbn. *)
  (*       now rewrite inst_subst, inst_multi. *)
  (*   - intuition. *)
  (* Qed. *)

  (* Lemma approx_box_assume_formula {Γ} {w0 : World} (ι0 : SymInstance w0) *)
  (*   (Hpc : instpc (wco w0) ι0) (fml : Formula w0) : *)
  (*   approx ι0 (@smut_box_assume_formula Γ w0 fml) (cmut_assume_formula ι0 fml). *)
  (* Proof. *)
  (*   (* intros w1 ω01 ι1 -> Hpc1 δs δc Hδ hs hc Hh P Q PQ Hwp. *) *)
  (*   (* eapply approx_assume_formula in Hwp; eauto. revert Hwp. *) *)
  (*   (* cbn. now rewrite ?inst_subst. *) *)
  (* Admitted. *)

  Lemma approx_assert_formula {Γ} {w0 : World} (ι0 : SymInstance w0)
    (Hpc : instpc (wco w0) ι0) (fml : Formula w0) :
    approx ι0 (@SMut.assert_formula Γ w0 fml) (@CMut.assert_formula Γ w0 ι0 fml).
  Admitted.

  Lemma approx_assert_formulas {Γ} {w0 : World} (ι0 : SymInstance w0)
        (Hpc : instpc (wco w0) ι0) (fmls : List Formula w0) :
    approx ι0 (@SMut.assert_formulas Γ w0 fmls) (@CMut.assert_formulas Γ w0 ι0 fmls).
  Proof.
    intros POST__s POST__c HPOST.
    intros δs δc -> hs hc ->.
    unfold CMut.assert_formulas.
    hnf.
    induction fmls as [|fml fmls]; cbn.
    - unfold SMut.pure. intros Hwp. split.
      constructor. revert Hwp. apply HPOST; auto.
      cbn. now rewrite inst_sub_id.
    - (* unfold smut_bind_right. apply approx_bind_right. *)
      (* apply IHfmls. *)
      (* intros w1 ω01 ι1 -> Hpc1. *)
      (* intros POST__s POST__c HPOST. *)
      (* intros δs δc -> hs hc ->. *)
      (* unfold cmut_assert_formula. *)
      (* rewrite <- inst_subst. *)
      (* apply approx_assert_formula; auto. *)

    (* induction fmls as [|fml fmls]; cbn. *)
    (* - now apply approx_pure. *)
    (* - apply approx_bind_right. *)
    (*   apply IHfmls. *)
    (*   intros w1 ω01 ι1 -> Hpc1. *)
    (*   intros POST__s POST__c HPOST. *)
    (*   intros δs δc -> hs hc ->. *)
    (*   unfold cmut_assert_formula. *)
    (*   rewrite <- inst_subst. *)
    (*   apply approx_assert_formula; auto. *)
  Admitted.

  Section PatternMatching.

    Lemma approx_angelic_match_bool {AT A} `{Approx AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
      approx ι (@SMut.angelic_match_bool AT Γ1 Γ2 w) (CMut.match_bool (A := A)).
    Admitted.

    Lemma approx_demonic_match_bool' {AT A} `{Approx AT A} {Γ1 Γ2} {w : World}
      (ι : SymInstance w) (Hpc : instpc (wco w) ι) :
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
        intros Hwp.
        (* apply cmut_wp_demonic_match_bool. *)
        (* revert Hwp. *)
        (* destruct a. *)
        (* apply Hkt; wsimpl; auto. *)
        (* apply Hkf; wsimpl; auto. *)
        admit.
      - now apply approx_demonic_match_bool'.
    Admitted.

    Lemma approx_angelic_match_enum {AT A} `{Approx AT A} {E : 𝑬} {Γ1 Γ2 : PCtx} {w : World} (ι : SymInstance w) :
      approx ι (@SMut.angelic_match_enum AT E Γ1 Γ2 w) (@CMut.match_enum A E Γ1 Γ2).
    Proof.
    Admitted.

    Lemma approx_demonic_match_enum {AT A} `{Approx AT A} {E : 𝑬} {Γ1 Γ2 : PCtx} {w : World} (ι : SymInstance w) :
      approx ι (@SMut.demonic_match_enum AT E Γ1 Γ2 w) (@CMut.match_enum A E Γ1 Γ2).
    Proof.
    Admitted.
  End PatternMatching.

  Section State.

    Lemma approx_eval_exp {Γ σ} (e : Exp Γ σ) {w0 : World} (ι0 : SymInstance w0)
          (Hpc : instpc (wco w0) ι0) :
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
      apply HPOST; auto. cbn. rewrite ?inst_sub_id; auto.
      apply env_lookup_extensional; cbn; intros [x σ] xIn.
      unfold inst at 2; cbn. rewrite ?env_lookup_map.
      now rewrite eval_exp_inst.
    Qed.

    Lemma approx_pushpop {AT A} `{Approx AT A} {Γ1 Γ2 x σ} {w0 : World} (ι0 : SymInstance w0)
          (Hpc : instpc (wco w0) ι0) :
      approx ι0 (@SMut.pushpop AT Γ1 Γ2 x σ w0) (@CMut.pushpop A Γ1 Γ2 x σ).
    Proof.
      intros t v ->.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      cbv [SMut.pushpop
             CMut.pushpop CMut.bind_right CMut.bind CMut.push_local
             CMut.bind_left CMut.pop_local CMut.state CMut.pure].
      apply Hm; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      intros δs1 δc1 -> hs1 hc1 ->.
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
      intros δs0 δc0 -> hs0 hc0 ->.
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
    unfold SMut.produce_chunk, CMut.produce_chunk, CMut.state.
    apply HPOST; cbn; rewrite ?inst_sub_id; auto.
  Qed.

  Lemma approx_produce {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.produce Γ w0 asn) (CMut.produce ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn.
    - (* unfold smutb_assume_formula. *)
      (* intros w1 ω01 ι1 -> Hpc1. *)
      (* rewrite <- inst_subst. *)
      (* now apply approx_assume_formula. *)
      admit.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_subst.
      now apply approx_produce_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_subst.
      apply approx_demonic_match_bool; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_subst.
      apply approx_demonic_match_enum; auto.
      intros EK1 EK2 HEK. hnf in HEK. subst EK2.
      eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_subst.
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_bind_right; eauto.
      apply IHasn1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_bind.
      apply approx_demonic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply approx_debug; auto.
      apply approx_pure; auto.
  Admitted.

  Lemma approx_consume {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0),
      approx ι0 (@SMut.consume Γ w0 asn) (CMut.consume ι0 asn).
  Admitted.

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
    { rewrite Hargs, Hevars.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      hnf. intros Hwp.
      eapply approx_assert_formulas in Hwp; eauto.
      revert Hwp. unfold CMut.assert_formulas.
      intros [Hfmls Hpost]; split; auto. revert Hfmls.
      clear.
      induction args__s.
      - destruct (nilView sep_contract_localstore0). cbn.
        intros. constructor.
      - destruct (snocView sep_contract_localstore0). cbn.
        rewrite ?inst_pathcondition_cons. cbn.
        rewrite ?inst_subst, ?inst_lift.
        intros [? HYP]; split; auto.
    }
    intros w2 ω12 ι2 -> Hpc2.
    apply approx_bind_right.
    { apply approx_consume; auto.
      constructor.
      cbn - [subst instantiate_env sub_snoc].
      rewrite ?inst_subst.
      now rewrite Hevars.
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
      rewrite inst_sub_snoc, ?inst_subst.
      now rewrite Hevars, Hres.
    }
    intros w5 ω45 ι5 -> Hpc5.
    apply approx_pure; auto.
    rewrite Hres. rewrite <- inst_subst.
    reflexivity.
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
      intros t v Htv.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      unfold CMut.bind_right, CMut.bind, CMut.state, CMut.pure.
      apply HPOST; wsimpl; auto.
      hnf. unfold inst; cbn.
      now rewrite (env_map_update _ _ xInΓ), Htv.
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
    - admit.
    - apply approx_bind.
      apply approx_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      apply approx_call_contract; auto.
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
      intros t v Htv.
      admit.
    - apply approx_block.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros POST__s POST__c HPOST.
      apply approx_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      admit.
    - apply approx_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply approx_bind_right; auto.
      admit.
      intros w2 ω12 ι2 -> Hpc2.
      apply approx_bind_right; auto.
      admit.
      intros w3 ω23 ι3 -> Hpc3.
      apply approx_pure; auto.
      hnf. now rewrite ?inst_subst.
    - apply approx_bind; auto.
      admit.
      admit.
    - apply approx_error.
    - apply approx_debug; auto.
  Admitted.

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
    let w := {| wctx := Σ; wco := nil |} in
    forall p : SPath w,
      @safe wnil (demonic_close p) env_nil ->
      forall ι : SymInstance w,
        @safe w p ι.
  Proof.
    induction Σ; cbn [demonic_close] in *.
    - intros p Hwp ι.
      destruct (nilView ι). apply Hwp.
    - intros p Hwp ι.
      destruct b as [x σ], (snocView ι).
      now apply (IHΣ (demonicv (w := {| wctx := Σ; wco := nil |}) (x :: σ) p)).
  Qed.

  Lemma symbolic_sound {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    SMut.ValidContract c body ->
    CMut.ValidContract c body.
  Proof.
    unfold SMut.ValidContract, CMut.ValidContract. intros [Hwp] ι.
    unfold SMut.exec_contract_path in Hwp. rewrite prune_sound in Hwp.
    generalize (@safe_demonic_close (sep_contract_logic_variables c) _ Hwp ι).
    apply approx_exec_contract; auto.
    intros w1 ω01 ι1 -> Hpc1.
    auto.
  Qed.

  Print Assumptions symbolic_sound.

End Soundness.
