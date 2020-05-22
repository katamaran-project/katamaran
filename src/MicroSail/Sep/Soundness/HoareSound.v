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
        (* | [ H: ResultOrFail _ _ |- _ ] => *)
        (*   destruct (result_or_fail_inversion _ _ H); destruct_conjs; subst *)
          (* apply result_or_fail_inversion in H; destruct_conjs; subst *)
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
      - destruct (IHtriple γ γ' μ μ' δ' s' Hfinal Hsteps
                  γframe γfocus (H γfocus Hpre) Hsplit_γ)
          as [γfocus' [Hsplit_γ' IH]].
        exists γfocus'.
        split.
        + apply Hsplit_γ'.
        + sound_destruct_result_or_fail IH; firstorder.

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
        + apply Hsplit_γ''.
        + destruct s';
          sound_steps_inversion;
          sound_simpl.
          exists γl, γr'.
          firstorder. trivial.

      (* rule_stm_lit *)
      - sound_steps_inversion.
        exists γfocus.
        firstorder.

      (* rule_stm_exp_forwards *)
      - sound_steps_inversion; try contradiction.
        exists γfocus. firstorder.

      (* rule_stm_exp_backwards *)
      - admit.

      (* rule_stm_let *)
      - sound_steps_inversion.
        sound_destruct_final H3.
        + destruct (IHtriple γ γ0 μ μ0 δ0 (stm_lit _ l)
                             ltac:(easy) H4 γframe γfocus Hpre Hsplit_γ) as
              [γfocus' [Hsplit_γ0 HQ]]; cbn in HQ.
          specialize (step_trans H11 H12) as H13.
          sound_use_IH H0 H6 γframe γfocus' HQ.
          sound_destruct_result_or_fail H14;
          firstorder.
       + specialize (IHtriple γ γ0 μ μ0 δ0 (stm_fail _ _)
                               ltac:(easy) H4 γframe γfocus Hpre Hsplit_γ).
         apply IHtriple.

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
        sound_destruct_final H3.
        + destruct (IHtriple γ γ0 μ μ0 δ0 (stm_lit τ l)
                              ltac:(easy) H4 γframe γfocus Hpre Hsplit_γ) as
              [γfocus0 [Hsplit_γ0 HQ]].
          cbn in HQ.
          specialize (H0 δ0 γ0 γ' μ0 μ' δ' s' Hfinal H8 γframe γfocus0 HQ Hsplit_γ0).
          apply H0.
        + specialize (IHtriple γ γ0 μ μ0 δ0 (stm_fail _ s)
                               ltac:(easy) H4 γframe γfocus Hpre Hsplit_γ).
          cbn in *. apply IHtriple.
      (* rule_stm_assert *)
      - admit.
        (* sound_steps_inversion; sound_simpl; try discriminate. *)
        (* dependent elimination s'; sound_steps_inversion; sound_simpl. *)
        (* exists γfocus. dependent elimination x. firstorder. *)
      (* rule_stm_fail *)
      - destruct Hpre.
      (* rule_stm_match_sum *)
      - sound_steps_inversion.
        sound_simpl.
        remember (eval e δ) as ident.
        dependent elimination ident;
        sound_steps_inversion; sound_simpl.
        (* now the proof should be smthng like two proofs of rule_stm_let *)
        + sound_destruct_final s3;
          specialize (step_trans H12 H13) as H14;
          sound_steps_inversion;
          sound_simpl;
          sound_use_IH H0 H8 γframe γfocus (H3 _ eq_refl);
          sound_destruct_final H8;
          dependent elimination H13; sound_steps_inversion; firstorder.
       + sound_destruct_final s3;
         specialize (step_trans H12 H13) as H14;
         sound_steps_inversion;
         sound_simpl;
         sound_use_IH H2 H8 γframe γfocus (H4 _ eq_refl);
         sound_destruct_final H8;
         dependent elimination H13; sound_steps_inversion; firstorder.

     (* rule_stm_read_register_backwards *)
     - sound_steps_inversion.
       + destruct Hfinal.
       + destruct (Hpre (read_register γ r))
           as [γl [γr [Hsplit_γfocus [γl_has_r H]]]].
         exists γfocus.
         split.
         ++ apply Hsplit_γ.
         ++ specialize (split_comm γfocus γl γr Hsplit_γfocus) as Hsplit_γfocus_comm.
            apply (H γfocus γl Hsplit_γfocus_comm γl_has_r).
Abort.
