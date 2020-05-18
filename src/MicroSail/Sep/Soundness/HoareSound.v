Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.
Require Import Equations.Equations.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.SmallStep.Inversion.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.
Require Import MicroSail.Sep.Hoare.
Require Import MicroSail.Sep.Model.Disjoint.

Module HoareSound
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit)
       (Import heapkit : HeapKit typekit termkit progkit assertkit contractkit).
  Module SSI := Inversion typekit termkit progkit.
  Import SSI.
  Import SS.

  Module PL := ProgramLogic typekit termkit progkit assertkit contractkit heapkit.
  Import PL.

  Module Model := Disjoint typekit termkit progkit assertkit contractkit heapkit.
  Import Model.

  Section Soundness.

    Open Scope logic.

    (* forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ), *)
    (*   ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' -> *)
    (*   forall (POST : Lit σ -> LocalStore Γ -> RegStore -> Prop), *)
    (*     WLP s POST δ γ -> ResultNoFail s' (fun v => POST v δ' γ'). *)

    Definition Total (h : Heap) : Prop :=
      forall σ r, exists v, h σ r = Some v.

    Definition heap (rs : RegStore) : Heap :=
      fun _ r => Some (read_register rs r).

    Lemma RegStoreIsTotal (rs : RegStore) : Total (heap rs).
    Proof.
      intros σ r.
      exists (read_register rs r).
      now unfold heap.
    Qed.

    Local Ltac sound_steps_inversion :=
      repeat
        match goal with
        | [ H: ResultNoFail _ _ |- _ ] =>
          apply result_no_fail_inversion in H; destruct_conjs; subst
        | [ H: ⟨ _, _, _, ?s ⟩ ---> ⟨ _, _, _, _ ⟩ |- _ ] =>
          microsail_stm_primitive_step s; dependent destruction H
        | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, ?t ⟩, HF: Final ?t |- _ ] =>
          first
            [ microsail_stm_primitive_step s; dependent destruction H; cbn in HF
            | match head s with
              | @stm_call'   => apply (steps_inversion_call'  HF) in H
              | @stm_let     => apply (steps_inversion_let    HF) in H
              | @stm_let'    => apply (steps_inversion_let'   HF) in H
              | @stm_seq     => apply (steps_inversion_seq    HF) in H
              | @stm_assign  => apply (steps_inversion_assign HF) in H
              | @stm_bind    => apply (steps_inversion_bind   HF) in H
              end; destruct_conjs
            ]
        | _ => progress (cbn in *)
                        end.

  Import EnvNotations.

  Local Ltac sound_simpl :=
    repeat
      match goal with
      | [ H: True |- _ ] => clear H
      | [ H: False |- _ ] => destruct H
      | [ H: Env _ (ctx_snoc _ _) |- _ ] =>
        dependent destruction H
      | [ H: Env _ ctx_nil |- _ ] =>
        dependent destruction H
      | [ H: context[env_drop _ (_ ►► _)]|- _] =>
        rewrite env_drop_cat in H
      | [ _: context[match eval ?e ?δ with _ => _ end] |- _ ] =>
        destruct (eval e δ)
      | _ => progress (cbn in *; destruct_conjs; subst)
      end.

    (* Lemma sound {Γ σ} (s : Stm Γ σ) : *)
    (*   forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ), *)
    (*   ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' -> *)
    (*   forall (PRE : HProp) (POST : Lit σ -> LocalStore Γ -> HProp) *)
    (*     (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄) *)
    (*     (γframe γfocus : Heap), *)
    (*       split (heap γ) γframe γfocus -> *)
    (*       PRE γfocus -> *)
    (*       (exists (γfocus' : Heap), *)
    (*         ResultNoFail s' (fun v => POST v δ' γfocus')). *)
    (* Proof. *)
    (* Abort. *)

    Lemma sound {Γ σ} (s : Stm Γ σ) :
      forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ),
      ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
      forall (PRE : HProp) (POST : Lit σ -> LocalStore Γ -> HProp)
        (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄)
        (γframe γfocus : Heap),
          split (heap γ) γframe γfocus ->
          PRE γfocus ->
          exists (γframe' γfocus' : Heap),
            split (heap γ') γframe' γfocus' /\
            ResultNoFail s' (fun v => POST v δ' γfocus').
    Proof.
      (* intros. *)
      (* generalize dependent γframe. *)
      (* generalize dependent γfocus. *)
      (* generalize dependent H. *)
      (* generalize dependent H0. *)
      (* generalize dependent POST. *)
      (* generalize dependent PRE. *)
      (* revert s' γ γ' μ μ' δ δ'. *)
      induction s.
      (* stm_lit *)
      * intros γ γ' μ μ' δ δ' s' Hsteps Hfinal PRE POST triple γframe γfocus Hsplit_γ Hpre.
        sound_steps_inversion.
        sound_simpl.
        dependent induction triple.
        (* rule_consequence *)
        + specialize (IHtriple l P' Q' eq_refl JMeq_refl JMeq_refl eq_refl JMeq_refl).
          specialize (IHtriple γframe γfocus Hsplit_γ (H γfocus Hpre)).
          inversion IHtriple as [γframe' [γfocus' [Hsplit_γ' HQ']]].
          clear IHtriple.
          exists γframe', γfocus'.
          intuition.
        (* rule_frame *)
        + inversion Hpre as [γl [γr [Hsplit_γfocus [HR HP]]]].
          clear Hpre.
          specialize (IHtriple l P Q eq_refl JMeq_refl JMeq_refl eq_refl JMeq_refl).
          destruct (split_assoc_r (heap γ) γframe γfocus γl γr Hsplit_γ Hsplit_γfocus)
          as [γ0 [Hsplit_γ0r Hsplit_γframer]].
          specialize (IHtriple γ0 γr Hsplit_γ0r HP).
          inversion IHtriple as [γframe' [γfocus' [Hsplit_γ' HQ']]]. clear IHtriple.
          exists γframe', γfocus'.
          split.
          ++ apply Hsplit_γ'.
          ++ cbn in *.
             exists γl, γr.
             admit.
        (* rule_stm_lit *)
        + exists γframe, γfocus.
          split.
          ++ apply Hsplit_γ.
          ++ now cbn in *.
     (* stm_exp *)
     Abort.




    Lemma sound {Γ σ} (s : Stm Γ σ) :
      forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ),
      ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
      forall (PRE : HProp) (POST : Lit σ -> LocalStore Γ -> HProp)
        (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄)
        (γframe γfocus : Heap),
          split (heap γ) γframe γfocus ->
          PRE γfocus ->
          exists (γframe' γfocus' : Heap),
            split (heap γ') γframe' γfocus' /\
            ResultNoFail s' (fun v => POST v δ' γfocus').
    Proof.
      intros γ γ' μ μ' δ δ' s' Hsteps Hfinal PRE POST triple γframe γfocus Hsplit_γ Hpre.
      revert Hpre Hsplit_γ.
      generalize dependent γfocus.
      generalize dependent γframe.
      revert Hfinal Hsteps.
      generalize dependent s'.
      revert γ γ' μ μ' δ'.
      induction triple; intros.
      (* consequence *)
      - destruct (IHtriple γ γ' μ μ' δ' s' Hfinal Hsteps
                  γframe γfocus (H γfocus Hpre) Hsplit_γ)
          as [γframe' [γfocus' [Hsplit_γ' IH]]].
        exists γframe', γfocus'.
        split.
        + apply Hsplit_γ'.
        + destruct (result_no_fail_inversion _ _ IH) as [v [s'eq HQ']].
          subst.
          unfold ResultNoFail.
          apply (H0 _ _ γfocus' HQ').
      (* frame *)
      - inversion Hpre as [γl [γr [Hsplit_γfocus [HR HP]]]].
        destruct (split_assoc_r (heap γ) γframe γfocus γl γr Hsplit_γ Hsplit_γfocus)
          as [γ0 [Hsplit_γ0r Hsplit_γframer]].
        destruct (IHtriple γ γ' μ μ' δ' s' Hfinal Hsteps γ0 γr HP Hsplit_γ0r)
          as [γframe' [γfocus' [Hsplit_γ' IH]]].
        exists γframe', γfocus'.
        split.
        * apply Hsplit_γ'.
        * dependent elimination s';
          sound_steps_inversion;
          sound_simpl.
          ** exists γl, γr.
             (* stuck: something is wrong with the connection between γfocus and γfocus'.
                Should R, the frame predicate, hold on γframe instead of a part of γfocus?*)
             admit.
          ** discriminate.
      (* rule_stm_lit *)
      - sound_steps_inversion.
        exists γframe, γfocus.
        intuition.
      (* rule_stm_exp_forwards *)
      - sound_steps_inversion; try contradiction.
        exists γframe, γfocus. intuition.
      (* rule_stm_exp_backwards *)
      - admit.
      (* rule_stm_let *)
      - admit.
      (* rule_stm_if *)
      - sound_steps_inversion.
        sound_simpl.
        destruct (eval e δ); cbn in *.
        * apply (IHtriple1 γ γ3 μ μ3 δ3 s4 Hfinal Hsteps γframe γfocus
                           (conj Hpre eq_refl) Hsplit_γ).
        * apply (IHtriple2 γ γ3 μ μ3 δ3 s4 Hfinal Hsteps γframe γfocus
                           (conj Hpre eq_refl) Hsplit_γ).
      (* rule_stm_if_backwards *)
      - admit.
      (* rule_stm_seq *)
      - sound_steps_inversion.
        sound_simpl.
        destruct H3.
        + sound_steps_inversion.
          sound_simpl.
          destruct (IHtriple γ γ0 μ μ0 δ0 (stm_lit τ l)
                              ltac:(easy) H4 γframe γfocus Hpre Hsplit_γ) as
              [γframe0 [γfocus0 [Hsplit_γ0 HQ]]].
          cbn in HQ.
          specialize (H0 δ0 γ0 γ' μ0 μ' δ' s' Hfinal H8 γframe0 γfocus0 HQ Hsplit_γ0).
          apply H0.
      (* rule_stm_assert *)
      - intros γfocus HP γframe Hsplit_γ.
        sound_steps_inversion; try contradiction.
        admit.
      (* rule_stm_fail *)
      - admit.
      (* rule_stm_match_sum *)
      - intros γfocus HP γframe Hsplit_γ.
        sound_steps_inversion. sound_simpl.
        destruct (eval e δ); cbn in *.
        *
          specialize (steps_inversion_let' H1 H0) as Z.
          dependent destruction Z.
          destruct_conjs.
          progress (cbn in *).
          exists γfocus.
          specialize (step_trans H14 H15) as H16.
          (* specialize (step_trans H15 Z). *)
          cbn in *.

          specialize (H3 l (env_cat H8 H9) H10 H11).
          admit.
        * exists γfocus. cbn in *.
          sound_steps_inversion. sound_simpl.
          destruct (eval e1 δ).
        * exists γfocus.
      1:{  }
      1:{


          apply (result_no_fail_inversion s' (fun v : Lit σ => Q v δ' γfocus')).
          unfold ResultNoFail.

      - cbn in *.
      - cbn in *.
        sound_steps_inversion.
        dependent elimination triple.
        2:{
          exists γfocus.

          cbn.
          exists γl, γr.
          split.
          * apply Hsplit_γ.
          * split.
            ** apply HR.
            ** dependent elimination t0.
               remember (@rule_frame HProp _ Γ δ σ0 R P0 Q0 (stm_lit σ0 l) t0) as t.

        + specialize (IHtriple l γ γ0 Heqγ0 γframe γfocus H2 (H γfocus H3)).
          clear H3 H2 H.
          destruct IHtriple as [γfocus' HQ'].
          exists γfocus'. intuition.
        + specialize (IHtriple l _ γfocus γr HP).
          assert (forall (γ : RegStore) (hl hr : Heap),
                     split (totalHeap γ) hl hr -> exists γl γr, totalHeap γl = hl
                                                        /\ totalHeap γr = hr).
          { intros.
            unfold split in H.

          specialize (IHtriple l γ γl).
          assert (forall (R P : HProp) h, (R ✱ P) h -> P h).
          { intros. destruct H as [hl [hr [_ [_ HP]]]]. apply HP.
cbn in *.

specialize (H2 γframe).


        +
          exists γfocus, γframe.
          split.
          * apply H3.
          * eapply H1.
            cbn in *.
            specialize (H (totalHeap γfocus) H2).
            specialize (IHtriple l γ γfocus H γframe H3).
            destruct (
            dependent destruction IHtriple.
            dependent destruction H2.
            dependent destruction H2.
            apply H3.
        (* generalize dependent γframe. *)
        (* generalize dependent γfocus. *)
        (* dependent induction triple. *)
        (* + *)
        (*   exists γfocus. *)
        (*   eapply H1. *)
        (*   cbn in *. *)
        (*   specialize (H (totalHeap γfocus) H3). *)

        (*   specialize (IHtriple l P' Q' eq_refl JMeq_refl JMeq_refl eq_refl JMeq_refl *)
        (*               γframe γfocus H2 H). *)
        (*   dependent elimination IHtriple. *)
        (*   specialize (IHtriple l H) as z. *)
        (*   dependent elimination z. *)



eapply IHtriple.
        dependent induction triple.
        + exists γfocus.
          specialize (IHtriple l PRE POST eq_refl ).

          eapply H1.
          eapply IHtriple.
        dependent elimination triple.
        + exists γfocus.
          eapply l1.

          destruct (@rule_consequence HProp _ Γ δ σ P P' Q Q' (stm_lit σ l) l0 l1 t).
          *

          eapply l1.
          eapply l0.
          dependent elimination t.
          *
        Focus 3.
        cbn in *.
        auto.
        apply rule_stm_lit.
        specialize (rule_stm_lit Γ δ τ l) as H.
        cbn in H.
        dependent destruction H.
        + specialize (H2 l δ).

        destruct (rule_stm).
        specialize (POST l δ (totalHeap γ)) as t.
        compute.

        compute.
        extensionality r.
        compute.
sound_simpl.
        unfold HProp in *.
        remember (totalHeap γ) as heap in *.
        unfold Heap in *.
        destruct (heap τ).
        +
        unfold ResultNoFail.
        unfold totalHeap.
        cbn.
        eapply result_no_fail_inversion.
      dependent induction H.
      -
      dependent destruction H1.


  (* The soundness proof needs to be carried out in terms of the logic interface *)


    (* Proof. *)
    (*   destruct triple. *)
    (*   - intros. *)
    (*     exists (stm_lit τ l). *)
    (*     admit. *)
    (*   - intros. *)
    (*     exists (stm_lit τ (eval e δ1)). *)
    (*     exists γ1. exists μ1. exists δ1. *)
    (*     constructor. *)
    (* Abort. *)

  (* Theorem sound_backward *)
  (*   (Γ : Ctx (𝑿 * Ty)) *)
  (*   (σ : Ty) *)
  (*   (stm1 stm2 : Stm Γ σ) *)
  (*   (γ1 γ2 : RegStore) (μ1 μ2 : Memory) (δ1 δ2 : LocalStore Γ) *)
  (*   (step : ⟨ γ1 , μ1 , δ1 , stm1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , stm2 ⟩) : *)
  (*   exists (pre : LocalStore Γ -> A) *)
  (*     (post : LocalStore Γ -> Lit σ -> A), *)
  (*     Triple Γ pre stm1 post. *)
  (*   (* (triple : Γ ⊢ ⦃ pre ⦄ stm ⦃ post ⦄) : *) *)
  (*   (triple : Triple Γ pre stm post) : *)
  (*   forall (γ1 : RegStore) (μ1 : Memory) (δ1 : LocalStore Γ), *)
  (*        exists (stm' : Stm Γ σ) (γ2 : RegStore) (μ2 : Memory) (δ2 : LocalStore Γ) , *)

  (*   Proof. *)
  (*     destruct triple. *)
  (*     - intros. *)
  (*       exists (stm_lit τ l). *)
  (*       admit. *)
  (*     - intros. *)
  (*       exists (stm_lit τ (eval e δ1)). *)
  (*       exists γ1. exists μ1. exists δ1. *)
  (*       constructor. *)
  (*   Abort. *)
