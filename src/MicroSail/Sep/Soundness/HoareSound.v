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

    Lemma RegStoreIsTotal (rs : RegStore) : Total (heap rs).
    Proof.
      intros σ r.
      exists (read_register rs r).
      now unfold heap.
    Qed.

    Local Ltac sound_steps_inversion :=
      repeat
        match goal with
        | [ H: ResultOrFail _ _ |- _ ] =>
          apply result_or_fail_inversion in H;
          dependent destruction H; destruct_conjs; subst
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
      | [ Hsplit : split (heap ?γ) ?γframe ?γfocus
        |- exists (_ : Heap), split (heap ?γ) ?γframe _ /\ _
        ] => econstructor; intuition
        (* exists ?γfocus *)
      | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, ?t ⟩, HF: Final ?t |- _ ] =>
        dependent destruction t
      | _ => progress (cbn in *; destruct_conjs; subst)
      end.

  Lemma steps_lit_no_fail {Γ γ1 γ2 μ1 μ2 δ1 δ2 σ l s} :
    ⟨ γ1, μ1, δ1, @stm_lit Γ σ l ⟩ --->* ⟨ γ2, μ2, δ2, stm_fail _ s ⟩ -> False.
  Proof.
    intros.
    dependent elimination H.
    sound_steps_inversion;
    sound_simpl.
  Qed.

  Local Ltac sound_destruct_result_or_fail H :=
    destruct (result_or_fail_inversion _ _ H); destruct_conjs; subst;
    sound_steps_inversion; sound_simpl.

  Local Ltac sound_destruct_final t :=
    match goal with
    | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, t ⟩, HF: Final t |- _ ] =>
      dependent destruction t; sound_steps_inversion; sound_simpl
    end.

  Local Ltac sound_use_IH IH s γframe γfocus Hpre :=
    match goal with
    | [ Hfinal : Final s
      , Hsplit_γ : split (heap ?γ) γframe γfocus
      , Hsteps : ⟨ ?γ, ?μ, ?δ, ?s0 ⟩ --->* ⟨ ?γ', ?μ', ?δ', s ⟩
        |- _ ] =>
      let ident := fresh
      in match IH with
      | context[_ : LocalStore _] =>
        specialize (IH _ _ _ _ _ _ _ s Hfinal Hsteps
                          (* ?γframe ?γfocus prf Hsplit_γ) as Z *)
                       γframe γfocus Hpre Hsplit_γ) as ident
      | _ =>
        specialize (IH _ _ _ _ _ _ s Hfinal Hsteps
                       γframe γfocus Hpre Hsplit_γ) as ident
      end;
      let γfocus := fresh
      in destruct ident as [γfocus ident];
      destruct_conjs;
      exists γfocus
    end.

  Local Ltac hoare_sound_inst :=
    match goal with
    | [
      IH: forall _ _ _ _ _ _, Final _ -> _
      , Hsplit_γ : split (heap ?γ) ?γframe ?γfocus
      , HS: ⟨ _, _, _ , _ ⟩ --->* ⟨ _, _, _ , ?t ⟩
      , HF: Final ?t
      , Hpre : ?P ?γfocus
      |- _
      ] => let ident := fresh
          in specialize (IH _ _ _ _ _ _ HF HS γframe γfocus ltac:(auto) Hsplit_γ) as ident;
          clear HS HF;
          destruct_conjs
    end.

  Local Ltac steps_inversion_inster :=
    repeat
      match goal with
      | [ H : forall _, _ = _ -> _ |- _ ]
        => specialize (H _ eq_refl)
      | [ H : forall _ _, _ = _ -> _ |- _ ]
        => specialize (H _ _ eq_refl)
      | [ H : forall _ _ _, _ = _ -> _ |- _ ]
        => specialize (H _ _ _ eq_refl)
      | [ H : Final ?s -> _, H' : Final ?s |- _ ]
        => specialize (H H')
      end.

  Local Ltac hoare_sound_solve :=
    repeat
      (sound_steps_inversion;
       sound_simpl;
       try steps_inversion_inster;
       try hoare_sound_inst); intuition.

  Lemma sound {Γ σ} (s : Stm Γ σ) :
    forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore Γ) (s' : Stm Γ σ),
      ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
      forall (PRE : HProp) (POST : Lit σ -> LocalStore Γ -> HProp)
        (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄)
        (γframe γfocus : Heap),
        split (heap γ) γframe γfocus ->
        PRE γfocus ->
        exists (γfocus' : Heap),
          split (heap γ') γframe γfocus' /\
          ResultOrFail s' (fun v => POST v δ' γfocus').
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
      - hoare_sound_solve.
      (* frame *)
      - inversion Hpre as [γl [γr [Hsplit_γfocus [HR HP]]]].
        destruct (split_assoc_r (heap γ) γframe γfocus γl γr Hsplit_γ Hsplit_γfocus)
          as [γ0 [Hsplit_γ0r Hsplit_γframer]].
        destruct (IHtriple γ γ' μ μ' δ' s' Hfinal Hsteps γ0 γr HP Hsplit_γ0r)
          as [γr' [Hsplit_γ' IH]].
        destruct (split_assoc_l (heap γ') γ0 γr' γframe γl Hsplit_γ' Hsplit_γframer) as
            [γfocus' [Hsplit_γ'' Hsplit_γfocus']].
        exists γfocus'.
        split.
        + hoare_sound_solve.
        + destruct s';
          sound_steps_inversion;
          sound_simpl.
          ++ exists γl, γr'.
             discriminate.
          ++ exists γl, γr'. dependent elimination H0. intuition.
          ++ intuition.
          ++ intuition.
      (* rule_stm_lit *)
      - hoare_sound_solve.
      (* rule_stm_exp_forwards *)
      - hoare_sound_solve.
      (* rule_stm_exp_backwards *)
      - hoare_sound_solve.
      (* rule_stm_let *)
      - sound_steps_inversion; sound_simpl.
        sound_destruct_final H3.
        + destruct (IHtriple γ γ0 μ μ0 δ0 (stm_lit _ l)
                             ltac:(easy) H4 γframe γfocus Hpre Hsplit_γ) as
              [γfocus' [Hsplit_γ0 HQ]]; cbn in HQ.
          specialize (step_trans H11 H12) as H13.
          sound_use_IH H0 H6 γframe γfocus' HQ.
          hoare_sound_solve.
       + remember (stm_fail _ _) as s_fail.
         assert (Final s_fail) by now subst.
         hoare_sound_inst.
         hoare_sound_solve.
      (* rule_stm_if *)
      - sound_steps_inversion.
        sound_simpl.
        destruct (eval e δ); cbn in *; hoare_sound_solve.
      (* rule_stm_if_backwards *)
      - admit.
      (* rule_stm_seq *)
      - hoare_sound_solve.
      (* rule_stm_assert *)
      - hoare_sound_solve.
        admit.
      (* rule_stm_fail *)
      - hoare_sound_solve.
      (* rule_stm_match_sum *)
      - sound_steps_inversion.
        sound_simpl.
        remember (eval e δ) as ident. cbn in ident.
        destruct ident;
        (* dependent elimination ident; *)
        sound_steps_inversion; sound_simpl.
        + admit.
        + admit.
       (*  (* now the proof should be smthng like two proofs of rule_stm_let *) *)
       (*  + sound_destruct_final s3; *)
       (*    specialize (step_trans H12 H13) as H14; *)
       (*    sound_steps_inversion; *)
       (*    sound_simpl; *)
       (*    sound_use_IH H0 H8 γframe γfocus (H3 _ eq_refl); *)
       (*    sound_destruct_final H8; *)
       (*    dependent elimination H13; sound_steps_inversion; firstorder. *)
       (* + sound_destruct_final s3; *)
       (*   specialize (step_trans H12 H13) as H14; *)
       (*   sound_steps_inversion; *)
       (*   sound_simpl; *)
       (*   sound_use_IH H2 H8 γframe γfocus (H4 _ eq_refl); *)
       (*   sound_destruct_final H8; *)
       (*   dependent elimination H13; sound_steps_inversion; firstorder. *)

     (* rule_stm_read_register *)
     - sound_steps_inversion. sound_simpl.
       exists γfocus.
       firstorder.
       unfold heap in *.
       unfold split in *.
       specialize (Hsplit_γ σ r).
       destruct_conjs.
       destruct H; destruct (γframe σ r); congruence.
     (* rule_stm_read_register_backwards *)
     - admit.
     (* rule_stm_write_register *)
     - sound_steps_inversion.
       sound_simpl.
       specialize (write_heap_ptsreg γfocus r v0) as Hpost.
       remember (write_heap γfocus r v0) as γfocus'.
       remember (write_register γ r v0) as γ'.
       exists γfocus'.
       split.
       + unfold split.
         intros τ k.
         split.
         ++ unfold split in Hsplit_γ.
            specialize (Hsplit_γ τ k) as H10.
            destruct_conjs.
            remember (𝑹𝑬𝑮_eq_dec r k) as reg_eq.
            dependent destruction reg_eq.
            * dependent destruction t.
              dependent destruction eqi.
              cbn in *.
              rewrite <- eqf in *.
              firstorder. rewrite H in Hpre. discriminate.
            * destruct H.
              ** left. apply H.
              ** compute in n.
                 rewrite H in H0.
                 specialize (write_heap_distinct γfocus r k n None v0 H) as Hγfocus'_None.
                 rewrite <- Heqγfocus' in Hγfocus'_None.
                 right. apply Hγfocus'_None.
         ++ unfold split in Hsplit_γ.
            specialize (Hsplit_γ τ k) as H10.
            destruct_conjs.
            remember (𝑹𝑬𝑮_eq_dec r k) as reg_eq.
            dependent destruction reg_eq.
            * dependent destruction t.
              dependent destruction eqi.
              cbn in *.
              rewrite <- eqf in *.
              firstorder.
              ** rewrite H.
                 subst γ'.
                 rewrite Hpost.
                 unfold heap. f_equal.
                 now rewrite read_write.
              ** congruence.
            * specialize (split_in_r_then_not_in_l
                            (heap γ) γframe γfocus r v ltac:(auto) Hpre) as Hγframe_r_None.
              firstorder.
              ** rewrite H.
                 subst γfocus'.
                 unfold write_heap.
                 rewrite <- Heqreg_eq.
                 rewrite H in H0.
                 rewrite <- H0.
                 unfold heap.
                 subst γ'.
                 remember (read_register γ k) as w0.
                 rewrite (read_write_distinct γ n v0).
                 now subst.
              ** specialize (write_heap_distinct γfocus r k n None v0 H) as Hγfocus'_None.
                 rewrite <- Heqγfocus' in Hγfocus'_None.
                 rewrite Hγfocus'_None.
                 destruct (split_not_in_r_then_in_l
                            (heap γ) γframe γfocus k (RegStoreIsTotal γ)
                            Hsplit_γ H).
                 rewrite H1 in *.
                 subst γ'.
                 unfold heap.
                 now rewrite (read_write_distinct γ n v0).
       + firstorder.
     - admit.
     (* rule_stm_assign_backwards *)
     - hoare_sound_solve.
     (* rule_stm_assign_forwards *)
     - hoare_sound_solve.
       admit.
     - admit.
     - admit.
    Abort.

  End Soundness.

End HoareSound.
