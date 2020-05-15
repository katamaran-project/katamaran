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
    (*   intros. *)
    (*   generalize dependent γfocus. *)
    (*   generalize dependent γframe. *)
    (*   generalize dependent γ. *)
    (*   induction s; intros. *)
    (*   3:{ cbn in *. *)
    (*       sound_steps_inversion. *)

  (*   Lemma sound_stm_seq {Γ σ} (s : Stm Γ σ) *)
  (*         (s_eq : exists τ s1 s2 *)
  (* (IHs1 : forall (s' : Stm Γ τ) (γ γ' : RegStore) (μ μ' : Memory) *)
  (*          (δ δ' : LocalStore Γ) (PRE : HProp) (POST : Lit τ -> LocalStore Γ -> HProp), *)
  (*        δ ⊢ ⦃ PRE ⦄ s1 ⦃ POST ⦄ -> *)
  (*        Final s' -> *)
  (*        ⟨ γ, μ, δ, s1 ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
  (*        forall γfocus : Heap, *)
  (*        PRE γfocus -> *)
  (*        forall γframe : Heap, *)
  (*        split (heap γ) γframe γfocus -> *)
  (*        exists γframe' γfocus' : Heap, *)
  (*          split (heap γ') γframe' γfocus' /\ *)
  (*          ResultNoFail s' (fun v : Lit τ => POST v δ' γfocus')) *)
  (* (IHs2 : forall (s' : Stm Γ σ) (γ γ' : RegStore) (μ μ' : Memory) *)
  (*          (δ δ' : LocalStore Γ) (PRE : HProp) (POST : Lit σ -> LocalStore Γ -> HProp), *)
  (*        δ ⊢ ⦃ PRE ⦄ s2 ⦃ POST ⦄ -> *)
  (*        Final s' -> *)
  (*        ⟨ γ, μ, δ, s2 ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
  (*        forall γfocus : Heap, *)
  (*        PRE γfocus -> *)
  (*        forall γframe : Heap, *)
  (*        split (heap γ) γframe γfocus -> *)
  (*        exists γframe' γfocus' : Heap, *)
  (*          split (heap γ') γframe' γfocus' /\ *)
  (*          ResultNoFail s' (fun v : Lit σ => POST v δ' γfocus')), *)
  (*             s = @stm_seq Γ τ s1 σ s2)  : *)
  (*     forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ), *)
  (*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' -> *)
  (*     forall (PRE : HProp) (POST : Lit σ -> LocalStore Γ -> HProp) *)
  (*       (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄) *)
  (*       (γframe γfocus : Heap), *)
  (*         split (heap γ) γframe γfocus -> *)
  (*         PRE γfocus -> *)
  (*         exists (γframe' γfocus' : Heap), *)
  (*           split (heap γ') γframe' γfocus' /\ *)
  (*           ResultNoFail s' (fun v => POST v δ' γfocus'). *)
  (*     Proof. *)
  (*       intros γ γ' μ μ' δ δ' s' Hsteps Hfinal PRE POST triple γframe γfocus Hsplit_γ Hpre. *)
  (*       inversion s_eq as [τ [s1 [s2 [IHs1 [ IHs2 eq]]]]]. subst. clear s_eq. *)
  (*       sound_steps_inversion. *)
  (*       sound_simpl. *)
  (*       rename Hsteps into γ0. *)
  (*       induction triple. *)
  (*       (* consequence *) *)
  (*       - destruct (IHtriple s1 s2 δ' s' H0 H1 H2 H3 H4 H5 H6 Hfinal *)
  (*                   (H7 γfocus Hpre) IHs1 IHs2) as [γframe' [γfocus' [IHsplit IHresult]]]. *)
  (*            exists γframe', γfocus'. *)
  (*            split. *)
  (*            ** apply IHsplit. *)
  (*            ** destruct s'; cbn in *; try congruence. *)
  (*               apply (H8 _ _ _ IHresult). *)
  (*       (* frame *) *)
  (*       - admit. *)
  (*       - dependent destruction H1; *)
  (*         cbn in *; *)
  (*         sound_steps_inversion; *)
  (*         sound_simpl. *)
  (*         + exists γframe, γfocus. *)
  (*           Abort. *)
(*           + (* specialize (step_trans H5 H6) as H7. *) *)
(*             specialize (IHs1 (stm_lit τ l) γ γ0 μ μ0 δ δ0 P6 (fun _ => Q5) t7 *)
(*                              (ltac:(now cbn)) H2 γfocus HPRE γframe Hsplit_γ). *)
(*             inversion IHs1 as [γframe' [γfocus' [Hsplit_γ' HQ]]]. clear IHs1. *)
(*             cbn in HQ. *)
(*             specialize (IHs2 s' γ0 γ' μ0 μ' δ0 δ' (Q5 δ0) R1 (t8 δ0) HFinal_s' *)
(*                              H6 γfocus' HQ γframe' Hsplit_γ'). *)
(*             apply IHs2. *)


(* dependent destruction H1; *)
(*           cbn in *; *)
(*           sound_steps_inversion; *)
(*           sound_simpl. *)
(*           + *)
(* Abort. *)
    (*         specialize (IHs1 (stm_lit τ l) γ γ0 μ μ0 δ δ0 P6 (fun _ => Q5) t7 *)
    (*                          (ltac:(now cbn)) H2 γfocus HPRE γframe Hsplit_γ). *)
    (*         inversion IHs1 as [γframe' [γfocus' [Hsplit_γ' HQ]]]. clear IHs1. *)
    (*         cbn in HQ. *)
    (*         specialize (IHs2 s' γ0 γ' μ0 μ' δ0 δ' (Q5 δ0) R1 (t8 δ0) HFinal_s' *)
    (*                          H6 γfocus' HQ γframe' Hsplit_γ'). *)
    (*         apply IHs2. *)
    (*     intros. *)


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
     *




        exists γframe, γfocus.
        split.
        ** apply Hsplit_γ.
        **
           +

               triple Hfinal
                  γfocus HPRE γframe Hsplit_γ.
      10:{
        intros s' γ γ' μ μ' δ δ' PRE POST triple Hfinal Hsteps
                  γfocus HPRE γframe Hsplit_γ.
        sound_steps_inversion.
        sound_simpl.
        rename Hsteps into γ0.
        dependent elimination triple.
        3:{
        dependent induction triple.
        3:{ simplify_IH_hyps.
            simpl_JMeq.
            simpl_depind.

      10:{ intros γ γ' μ μ' δ δ' s' Hsteps Hfinal PRE POST triple
                  γframe γfocus Hsplit_γ HPRE.
           sound_steps_inversion.
           sound_simpl.
           rename Hsteps into γ0.
           induction triple.
           (* dependent elimination triple. *)
           * specialize (IHtriple s1 s2 IHs1 IHs2 δ' s' H0 H1 H2 H3 H4 H5 H6 Hfinal
                       (H7 γfocus HPRE)) as [γframe' [γfocus' [IHsplit IHresult]]].
             exists γframe', γfocus'.
             split.
             ** apply IHsplit.
             ** destruct s'; cbn in *; try congruence.
                apply (H8 _ _ _ IHresult).
           * admit.
           * dependent destruction H1;
             cbn in *;
             sound_steps_inversion;
             sound_simpl.
             specialize (IHs2 γ0 γ' μ0 μ' δ0 δ' s' H6 Hfinal).

             (Q5 δ0) R1 (t8 δ0) HFinal_s'
                            H6 γfocus' HQ γframe' Hsplit_γ').

             sound_steps_inversion.
             sound_simpl.

             +
               (* specialize (step_trans H5 H6) as H7. *)
                 specialize (IHs1 (stm_lit τ l0) γ γ0 μ μ0 δ δ0
                                  ⊤ (fun v δ' => !!(l0 = v /\ δ = δ'))
                                  ). P6 (fun _ => Q5) t7
                            (ltac:(now cbn)) H2 γfocus HPRE γframe Hsplit_γ).
                 inversion IHs1 as [γframe' [γfocus' [Hsplit_γ' HQ]]]. clear IHs1.
                 cbn in HQ.
                 specialize (IHs2 s' γ0 γ' μ0 μ' δ0 δ' (Q5 δ0) R1 (t8 δ0) HFinal_s'
                            H6 γfocus' HQ γframe' Hsplit_γ').
                 apply IHs2.
  (* specialize (IHs1 (stm_lit τ l) γ γ0 μ μ0 δ δ0 P6 (fun _ => Q5) t7 *)
  (*                           (ltac:(now cbn)) H2 γfocus HPRE γframe Hsplit_γ). *)
  (*                inversion IHs1 as [γframe' [γfocus' [Hsplit_γ' HQ]]]. clear IHs1. *)
  (*                cbn in HQ. *)
  (*                specialize (IHs2 s' γ0 γ' μ0 μ' δ0 δ' (Q5 δ0) R1 (t8 δ0) HFinal_s' *)
  (*                           H6 γfocus' HQ γframe' Hsplit_γ'). *)
  (*                apply IHs2. *)
               + admit. }


                 sound_steps_inversion.
                 sound_simpl.

               + cbn in *.
                 sound_steps_inversion.
                 sound_simpl.

                 dependent destruction t7.








      induction .
      9:{
        intros HFinal_s' Hsteps γfocus HP γframe Hsplit_γ.
        sound_steps_inversion.
        sound_simpl.
        rename Hsteps into γ0.



      (* consequence *)
      - intros γfocus HP γframe Hsplit_γ.
        destruct (IHtriple δ' s' H H0 γfocus (H1 γfocus HP) γframe Hsplit_γ)
          as [γfocus' IH].
        exists γfocus'.
        destruct (result_no_fail_inversion _ _ IH) as [v [s'eq HQ']].
        subst.
        unfold ResultNoFail.
        apply (H2 _ _ γfocus' HQ').
      (* frame *)
      - intros γfocus HRP γframe Hsplit_γ.
        inversion HRP as [γl [γr [Hsplit_γfocus [HR HP]]]].
        destruct (split_assoc_r (heap γ) γframe γfocus γl γr Hsplit_γ Hsplit_γfocus)
          as [γ0 [Hsplit_γ0r Hsplit_γframer]].
        destruct (IHtriple δ' s' H H0 γr HP γ0 Hsplit_γ0r) as [γfocus' IH].
        (* stuck: do we need some sort of connection between γfocus and γfocus'? *)
        admit.
      (* rule_stm_lit *)
      - intros. cbn in *.
        sound_steps_inversion.
        now exists γfocus.
      (* rule_stm_exp_forwards *)
      - intros.
        sound_steps_inversion; try contradiction.
        exists γfocus. intuition.
      (* rule_stm_exp_backwards *)
      - admit.
      (* rule_stm_let *)
      - intros.
      (*    sound_steps_inversion. *)
      (*    sound_simpl. *)
      (*    cbn in *. *)
      (*    dependent destruction s'. *)
      (*    + cbn in *. *)
      (*      dependent destruction H7. *)
      (*      ++ cbn in *. *)
      (*         specialize (H2 l0). *)
      (*         specialize (step_trans H11 H12) as H13. *)
      (*         specialize (H1 l0 δ) as Z. *)
      (*         destruct Z. subst. *)
      (*         cbn in *. *)
      (*         specialize (H14 l (env_snoc δ' (x, τ0) l0)). *)
      (*         cbn in *. *)
      (*         exists γfocus. *)
      (*         apply (H14 γfocus). *)

      (*         sound_steps_inversion. *)
      (*         sound_simpl. *)

      (*    dependent destruction H7. *)
      (*    + cbn in *. *)
      (*      specialize (H1 l δ). *)
      (*      dependent destruction H1. *)
      (*      cbn in *. *)
      (*      specialize (H2 l (env_snoc δ (x, τ0) l)). *)
      (*      specialize (H2 l H6 (env_snoc δ' (x, τ0) l) ). *)
         admit.
      (* rule_stm_if *)
      - intros γfocus HP γframe Hsplit_γ.
         sound_steps_inversion.
         sound_simpl.
         destruct (eval e δ); cbn in *.
         * apply (IHtriple1 δ3 s4 H0 H1 γfocus (conj HP eq_refl) γframe Hsplit_γ).
         * apply (IHtriple2 δ3 s4 H0 H1 γfocus (conj HP eq_refl) γframe Hsplit_γ).
      (* rule_stm_if_backwards *)
      - intros γfocus eqs γframe Hsplit_γ.
        sound_steps_inversion.
        sound_simpl.
        destruct eqs as [HP1 HP2].
        destruct (eval e δ); cbn in *.
        + apply (IHtriple1 δ3 s4 H0 H1 γfocus (HP1 eq_refl) γframe Hsplit_γ).
        + apply (IHtriple2 δ3 s4 H0 H1 γfocus (HP2 eq_refl) γframe Hsplit_γ).
      (* rule_stm_seq *)
      - intros γfocus HP γframe Hsplit_γ.
         sound_steps_inversion.
         sound_simpl.
         destruct H5.
         + sound_steps_inversion.
           sound_simpl.
           specialize (H2 δ0 δ' s' H10).
         admit.
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
