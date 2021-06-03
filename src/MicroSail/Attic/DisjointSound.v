Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.
From Equations Require Import Equations.

Require Import MicroSail.Syntax.
Require Import MicroSail.Tactics.
Require Import MicroSail.Environment.
Require Import MicroSail.SmallStep.Inversion.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.
Require Import MicroSail.Sep.Hoare.
Require Import MicroSail.Attic.Disjoint.

Module HoareSound
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).

  Module SSI := Inversion termkit progkit.
  Import SSI.
  Import SS.

  Module PL := ProgramLogic termkit progkit assertkit contractkit.
  Import PL.

  Module Model := Disjoint termkit progkit assertkit contractkit.
  Import Model.

  Section Soundness.

    Open Scope logic.
    Import CtxNotations.
    Import EnvNotations.

    Local Ltac sound_inversion :=
      lazymatch goal with
      | [ H: ⟨ _, _, _, stm_let _ _ ?s ?k ⟩ ---> ⟨ _, _, _, _ ⟩, HF: Final ?s |- _ ] =>
        is_var s; apply (step_inversion_let HF) in H;
        destruct_propositional H; subst; cbn in *
      | [ H: ⟨ _, _, _, ?s ⟩ ---> ⟨ _, _, _, _ ⟩ |- _ ] =>
        microsail_stm_primitive_step s;
        dependent elimination H

      | [ H: ⟨ _, _, _, stm_lit _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ] =>
        apply steps_inversion_lit in H;
        destruct_propositional H; subst; cbn in *
      | [ H: ⟨ _, _, _, stm_fail _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ] =>
        apply steps_inversion_fail in H;
        destruct_propositional H; subst; cbn in *
      | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, ?t ⟩, HF: Final ?t |- _ ] =>
        first
          [ lazymatch head s with
            | @stm_exp        => apply (steps_inversion_exp           HF) in H
            | @stm_call_frame => apply (steps_inversion_ex_call_frame HF) in H
            | @stm_let        => apply (steps_inversion_ex_let        HF) in H
            | @stm_block      => apply (steps_inversion_ex_block      HF) in H
            | @stm_seq        => apply (steps_inversion_ex_seq        HF) in H
            | @stm_assign     => apply (steps_inversion_ex_assign     HF) in H
            | @stm_bind       => apply (steps_inversion_ex_bind       HF) in H
            end;
            destruct_propositional H; subst; cbn in *
          | microsail_stm_primitive_step s;
            dependent elimination H;
            [ contradiction HF | idtac ]
          ]
      end.

    Local Ltac sound_simpl :=
      match goal with
      | [ H: ?x = ?x |- _ ] => clear H
      | [ H: True |- _ ] => clear H
      | [ H: False |- _ ] => destruct H
      | [ H: Env _ (ctx_snoc _ _) |- _ ] =>
        dependent elimination H
      | [ H: Env _ ctx_nil |- _ ] =>
        dependent elimination H
      | [ H: context[env_drop _ (_ ►► _)]|- _] =>
        rewrite env_drop_cat in H
      | [ _: context[match eval ?e ?δ with _ => _ end] |- _ ] =>
        destruct (eval e δ) eqn:?
      end.

    Lemma resultorfail_monotonicity {Γ σ} {s : Stm Γ σ} {P Q : Lit σ -> Prop} :
      (forall v, P v -> Q v) -> ResultOrFail s P -> ResultOrFail s Q.
    Proof. destruct s; firstorder. Qed.

    Local Ltac sound_inster :=
      match goal with
      | [ Hsplit : split (heap ?γ) ?γframe ?γfocus
          |- exists (_ : Heap), split (heap ?γ) ?γframe _ /\ _
        ] => exists γfocus; split; [ exact Hsplit | idtac]
      | [ IH: context[⟨ _, _, _ , ?s ⟩ --->* ⟨ _, _, _ , _ ⟩ -> _],
          HS: ⟨ _, _, _ , ?s ⟩ --->* ⟨ _, _, _ , _ ⟩ |- _ ] =>
        inster IH by (cbn in *; eauto); cbn in IH;
        destruct_propositional IH
      | [ IH: context[⟨ _, _, _ , ?alt _ ⟩ --->* ⟨ _, _, _ , _ ⟩ -> _],
          HS: ⟨ _, _, _ , ?alt _ ⟩ --->* ⟨ _, _, _ , _ ⟩ |- _ ] =>
        inster IH by (cbn in *; eauto); cbn in IH;
        destruct_propositional IH
      | [H: ResultOrFail ?s _ |- ResultOrFail ?s _] =>
        refine (resultorfail_monotonicity _ H)
      | [ IH: context[split ?H _ _ -> _],
          HS: split ?H _ _ |- _ ] =>
        inster IH by (cbn in *; eauto); cbn in IH;
        destruct_propositional IH
      end.

    Local Ltac sound_solve :=
      repeat
        (destruct_conjs;
         repeat sound_inversion;
         repeat sound_simpl;
         repeat sound_inster;
         auto).

    Lemma RegStoreIsTotal (rs : RegStore) : Total (heap rs).
    Proof.
      intros σ r.
      exists (read_register rs r).
      now unfold heap.
    Qed.

    Definition ValidContractEnv' (cenv : SepContractEnv) : Prop :=
      forall σs σ (f : 𝑭 σs σ),
        match cenv σs σ f with
        | Some (MkSepContract _ _ Σ θΔ pre result post) =>
          forall (ι : SymInstance Σ)
                 (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : CStore σs) (s' : Stm σs σ),
            ⟨ γ, μ, δ, Pi f ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
            forall (γframe γfocus : Heap),
              split (heap γ) γframe γfocus ->
              (interpret_assertion (L:=HProp) pre ι) γfocus ->
              exists (γfocus' : Heap),
                split (heap γ') γframe γfocus' /\
                ResultOrFail s' (fun v => interpret_assertion post (env_snoc ι (result :: σ) v) γfocus')
        | None => False
        end.

    Hypothesis validCEnv : ValidContractEnv' CEnv.

    Lemma sound {Γ σ} (s : Stm Γ σ) :
      forall (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : CStore Γ) (s' : Stm Γ σ),
        ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
        forall (PRE : HProp) (POST : Lit σ -> CStore Γ -> HProp)
               (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄)
               (γframe γfocus : Heap),
          split (heap γ) γframe γfocus ->
          PRE γfocus ->
          exists (γfocus' : Heap),
            split (heap γ') γframe γfocus' /\
            ResultOrFail s' (fun v => POST v δ' γfocus').
    Proof.
      intros γ γ' μ μ' δ δ' s' Hsteps Hfinal
             PRE POST triple γframe γfocus Hsplit_γ Hpre.
      revert Hpre Hsplit_γ.
      generalize dependent γfocus.
      generalize dependent γframe.
      revert Hsteps Hfinal.
      generalize dependent s'.
      revert γ γ' μ μ' δ'.
      induction triple; cbn; intros.
      (* consequence *)
      - sound_solve. intuition.
      (* frame *)
      - destruct Hpre as (γl & γr & Hsplit_γfocus & HR & HP).
        destruct (split_assoc_r (heap γ) γframe γfocus γl γr Hsplit_γ Hsplit_γfocus)
          as (γ0 & Hsplit_γ0r & Hsplit_γframer).
        inster IHtriple by eauto.
        destruct IHtriple as (γr' & Hsplit_γ' & IH).
        destruct (split_assoc_l (heap γ') γ0 γr' γframe γl Hsplit_γ' Hsplit_γframer)
          as (γfocus' & Hsplit_γ'' & Hsplit_γfocus').
        repeat sound_inster.
        intros. exists γl, γr'. auto.
      (* pull *)
      - sound_solve.
      (* rule_exists *)
      - sound_solve.
      (* (* rule_forall *) *)
      (* - pose proof (H x). *)
      (*   microsail_insterU (eauto) H0. *)
      (*   destruct_conjs. *)
      (*   sound_inster. *)
      (*   destruct s'; cbn in *; try contradiction; auto. *)
      (*   intros. *)
      (*   pose proof (H x0). *)
      (*   microsail_insterU (eauto) H3. *)
      (*   destruct_conjs; cbn in *. *)
      (*   pose proof (split_eq_right H1 H4); subst; auto. *)
      (* rule_stm_lit *)
      - sound_solve.
      (* rule_stm_exp *)
      - sound_solve.
      (* rule_stm_let *)
      - sound_solve.
      (* rule_stm_block *)
      - sound_solve.
      (* rule_stm_if *)
      - sound_solve.
      (* rule_stm_seq *)
      - sound_solve.
      (* rule_stm_assert *)
      - sound_solve.
      (* rule_stm_fail *)
      - sound_solve.
      (* rule_stm_match_list *)
      - sound_solve.
      (* rule_stm_match_sum *)
      - sound_solve.
      (* rule_stm_match_pair *)
      - sound_solve.
      (* rule_stm_match_enum *)
      - sound_solve.
      (* rule_stm_match_tuple *)
      - sound_solve.
      (* rule_stm_match_union *)
      - sound_solve.
        destruct (𝑼_unfold (eval e9 δ)) eqn:Heq.
        assert (𝑼_fold (𝑼_unfold (eval e9 δ)) = 𝑼_fold (existT x l)) as Heq' by now f_equal.
        rewrite 𝑼_fold_unfold in Heq'.
        sound_solve.
      (* rule_stm_match_record *)
      - sound_solve.
      (* rule_stm_read_register *)
      - sound_solve.
        repeat (split; auto).
        specialize (Hsplit_γ _ r0); cbn in *.
        destruct Hsplit_γ as [[Heq1|Heq1] Heq2].
        + rewrite Heq1, Hpre in Heq2.
          unfold heap in Heq2.
          congruence.
        + congruence.
      (* rule_stm_write_register *)
      - sound_solve.
        rename γ into γ__pre, r1 into reg, v into v__pre, v5 into v__post, τ into σ, e10 into e, δ3 into δ.
        exists (write_heap γfocus reg v__post); cbn.
        specialize (write_heap_ptsreg γfocus reg v__post) as Hpost.
        split; auto.
        rewrite write_register_write_heap.
        intros τ k.
        specialize (Hsplit_γ τ k) as H__k.
        destruct_conjs.
        destruct (eq_dec_het reg k).
        + dependent elimination e0.
          destruct H; [ idtac | congruence ].
          rewrite H in *.
          split; auto.
          now rewrite !write_heap_ptsreg.
        + destruct H.
          * rewrite H in *; split; auto.
            erewrite !write_heap_distinct; eauto.
          * eapply split_not_in_r_then_in_l in Hsplit_γ; eauto using RegStoreIsTotal.
            destruct_conjs.
            rewrite H1 in *.
            erewrite !write_heap_distinct; eauto.
            congruence.
      (* rule_stm_assign_backwards *)
      - sound_solve.
      (* rule_stm_assign_forwards *)
      - sound_solve.
        exists (H ‼ x)%exp.
        now rewrite env_update_update, env_update_lookup, env_lookup_update.
      (* rule_stm_call_forwards *)
      - admit.
      (* rule_stm_call_inline *)
      - sound_solve.
      (* rule_stm_call_frame *)
      - sound_solve.
      (* rule_stm_call_external_backwards *)
      - admit.
      (* rule_stm_bind *)
      - sound_solve.
    Admitted.

  End Soundness.

End HoareSound.
