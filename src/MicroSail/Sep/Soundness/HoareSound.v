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

    Lemma RegStoreIsTotal (rs : RegStore) : Total (heap rs).
    Proof.
      intros σ r.
      exists (read_register rs r).
      now unfold heap.
    Qed.

    Local Ltac sound_steps_inversion :=
      lazymatch goal with
      | [ H: ⟨ _, _, _, stm_let _ _ ?s ?k ⟩ ---> ⟨ _, _, _, _ ⟩, HF: Final ?s |- _ ] =>
        is_var s; apply (step_inversion_let HF) in H;
        microsail_destruct_propositional H; subst
      | [ H: ⟨ _, _, _, ?s ⟩ ---> ⟨ _, _, _, _ ⟩ |- _ ] =>
        microsail_stm_primitive_step s;
        dependent elimination H

      | [ H: ⟨ _, _, _, stm_lit _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ] =>
        apply steps_inversion_lit in H;
        microsail_destruct_propositional H; subst
      | [ H: ⟨ _, _, _, stm_fail _ _ ⟩ --->* ⟨ _, _, _, _ ⟩ |- _ ] =>
        apply steps_inversion_fail in H;
        microsail_destruct_propositional H; subst
      | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, ?t ⟩, HF: Final ?t |- _ ] =>
        first
          [ lazymatch head s with
            | @stm_exp        => apply (steps_inversion_exp           HF) in H
            | @stm_call_frame => apply (steps_inversion_ex_call_frame HF) in H
            | @stm_let        => apply (steps_inversion_ex_let        HF) in H
            | @stm_block      => apply (steps_inversion_ex_block      HF) in H
            | @stm_seq        => apply (steps_inversion_ex_seq        HF) in H
            | @stm_assign     => apply (steps_inversion_ex_assign     HF) in H
            | @stm_bind       => apply (steps_inversion_bind          HF) in H
            end;
            microsail_destruct_propositional H; subst
          | microsail_stm_primitive_step s; dependent destruction H; cbn in HF
          ]
      end.

  Import EnvNotations.

  Local Ltac sound_simpl :=
    repeat
      match goal with
      | [ H: ?x = ?x |- _ ] => clear H
      | [ H: True |- _ ] => clear H
      | [ H: False |- _ ] => destruct H
      | [ H: Env _ (ctx_snoc _ _) |- _ ] =>
        dependent destruction H
      | [ H: Env _ ctx_nil |- _ ] =>
        dependent destruction H
      | [ H: context[env_drop _ (_ ►► _)]|- _] =>
        rewrite env_drop_cat in H
      | [ _: context[match eval ?e ?δ with _ => _ end] |- _ ] =>
        destruct (eval e δ) eqn:?
      end.

  (* This tactic instantiates a hypothesis with fresh unification variables,
   possibly solving some on the fly.
   Adopted from CPDT: http://adam.chlipala.net/cpdt/html/Match.html
   *)
  Local Ltac insterU tac H :=
    repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
             | Prop =>
               (let H' := fresh "H'" in
                assert (H' : T) by solve [ tac ];
                specialize (H H'); clear H')
               || fail 1
             | _ =>
               let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                   clear x; specialize (H x')
             end
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

  Lemma resultorfail_monotonicity {Γ σ} {s : Stm Γ σ} {P Q : Lit σ -> Prop} :
    (forall v, P v -> Q v) -> ResultOrFail s P -> ResultOrFail s Q.
  Proof. destruct s; firstorder. Qed.

  Local Ltac hoare_sound_inst :=
    match goal with
    | [ Hsplit : split (heap ?γ) ?γframe ?γfocus
        |- exists (_ : Heap), split (heap ?γ) ?γframe _ /\ _
      ] => exists γfocus; split; [ exact Hsplit | idtac]
    (* | [ IH: forall _ _ _ _ _ _, ⟨ _, _, _ , _ ⟩ --->* ⟨ _, _, _ , _ ⟩ -> Final _ -> _ *)
    (*   , Hsplit_γ : split (heap ?γ) ?γframe ?γfocus *)
    (*   , HS: ⟨ _, _, _ , _ ⟩ --->* ⟨ _, _, _ , ?t ⟩ *)
    (*   , HF: Final ?t *)
    (*   , Hpre : ?P ?γfocus *)
    (*   |- _ *)
    (*   ] => insterU ltac:(intuition; try now subst) IH *)
    (* | [ δΣ : NamedEnv Lit ?Σ *)
    (*   , IH : forall (δΣ : NamedEnv Lit ?Σ) _ _ _ _ _ _ _, _ -> Final _ -> _ *)
    (*   |- _ ] => unshelve (insterU ltac:(intuition; try now subst) IH); try assumption *)
    | [H: ResultOrFail ?s _ |- ResultOrFail ?s _] =>
      refine (resultorfail_monotonicity _ H)
    end.

  (* Local Ltac hoare_sound_solve := *)
  (*   repeat *)
  (*     (sound_steps_inversion; *)
  (*      sound_simpl; *)
  (*      try steps_inversion_inster; *)
  (*      try hoare_sound_inst); intuition. *)

  Definition ValidContractEnv' (cenv : SepContractEnv) : Prop :=
    forall σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | @sep_contract_result _ _ Σ θΔ result pre post =>
        forall (δΣ : NamedEnv Lit Σ)
          (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore σs) (s' : Stm σs σ),
          ⟨ γ, μ, δ, Pi f ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
          forall (γframe γfocus : Heap),
            split (heap γ) γframe γfocus ->
            (interpret (L:=HProp) δΣ pre) γfocus ->
            exists (γfocus' : Heap),
              split (heap γ') γframe γfocus' /\
              ResultOrFail s' (fun v => interpret (env_snoc δΣ (result , σ) v) post γfocus')
      | _ => False
      end.

  Hypothesis validCEnv : ValidContractEnv' CEnv.

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
      - insterU ltac:(eauto) IHtriple.
        microsail_destruct_propositional IHtriple.
        hoare_sound_inst.
        hoare_sound_inst.
        intuition.
      (* frame *)
      - destruct Hpre as (γl & γr & Hsplit_γfocus & HR & HP).
        destruct (split_assoc_r (heap γ) γframe γfocus γl γr Hsplit_γ Hsplit_γfocus)
          as (γ0 & Hsplit_γ0r & Hsplit_γframer).
        insterU ltac:(eauto) IHtriple.
        destruct IHtriple as (γr' & Hsplit_γ' & IH).
        destruct (split_assoc_l (heap γ') γ0 γr' γframe γl Hsplit_γ' Hsplit_γframer)
          as (γfocus' & Hsplit_γ'' & Hsplit_γfocus').
        hoare_sound_inst.
        hoare_sound_inst.
        intros. exists γl, γr'. auto.
      (* rule_stm_lit *)
      - sound_steps_inversion.
        hoare_sound_inst. cbn. auto.
      (* rule_stm_exp_forwards *)
      - sound_steps_inversion.
        hoare_sound_inst. cbn. auto.
      (* rule_stm_exp_backwards *)
      - sound_steps_inversion.
        hoare_sound_inst. cbn. auto.
      (* rule_stm_let *)
      - sound_steps_inversion; cbn in *.
        { insterU ltac:(eassumption) IHtriple.
          microsail_destruct_propositional IHtriple.
          hoare_sound_inst; auto.
        }
        insterU ltac:(cbn; auto; eassumption) IHtriple.
        microsail_destruct_propositional IHtriple.
        sound_steps_inversion; cbn in *.
        { insterU ltac:(eassumption) H0.
          microsail_destruct_propositional H0; subst; cbn in *.
          hoare_sound_inst; auto.
        }
        sound_simpl; cbn in *.
        insterU ltac:(cbn; auto; eassumption) H0.
        microsail_destruct_propositional H0; subst; cbn in *.
        hoare_sound_inst; auto.
      (* rule_stm_if *)
      - sound_steps_inversion; cbn in *.
        + contradiction.
        + dependent elimination H.
          sound_simpl; eauto.
      (* rule_stm_if_backwards *)
      - sound_steps_inversion; cbn in *.
        + contradiction.
        + destruct Hpre.
          dependent elimination H.
          sound_simpl; eauto.
      (* rule_stm_seq *)
      - sound_steps_inversion; cbn in *.
        { insterU ltac:(eassumption) IHtriple.
          microsail_destruct_propositional IHtriple.
          hoare_sound_inst; auto.
        }
        insterU ltac:(cbn; auto; eassumption) IHtriple; cbn in IHtriple.
        microsail_destruct_propositional IHtriple.
        insterU ltac:(eassumption) H0; cbn in H0.
        microsail_destruct_propositional H0.
        hoare_sound_inst; auto.
      (* (* rule_stm_assert *) *)
      - sound_steps_inversion; cbn in *.
        + contradiction.
        + dependent elimination H.
          sound_simpl; eauto.
          * sound_steps_inversion; cbn.
            hoare_sound_inst; auto.
          * sound_steps_inversion; cbn.
            hoare_sound_inst; auto.
      (* rule_stm_fail *)
      - sound_steps_inversion; cbn in *.
        hoare_sound_inst; auto.
      (* rule_stm_match_sum *)
      - destruct Hpre.
        sound_steps_inversion; sound_simpl.
        dependent elimination H3; sound_simpl.
        + insterU ltac:(reflexivity) H4; clear H5.
          sound_steps_inversion; sound_simpl.
          * insterU ltac:(eassumption) H0; cbn in H0.
            microsail_destruct_propositional H0.
            hoare_sound_inst; auto.
          * insterU ltac:(eassumption) H0; cbn in H0.
            microsail_destruct_propositional H0.
            hoare_sound_inst; auto.
        + insterU ltac:(reflexivity) H5; clear H4.
          sound_steps_inversion; sound_simpl.
          * insterU ltac:(eassumption) H2; cbn in H2.
            microsail_destruct_propositional H2.
            hoare_sound_inst; auto.
          * insterU ltac:(eassumption) H2; cbn in H2.
            microsail_destruct_propositional H2.
            hoare_sound_inst; auto.
      (* rule_stm_read_register *)
      - sound_steps_inversion.
        { contradiction. }
        sound_steps_inversion.
        sound_steps_inversion.
        exists γfocus.
        repeat (split; auto).
        specialize (Hsplit_γ σ19 r0); cbn in *.
        intuition.
        + rewrite H1, Hpre in H0.
          unfold heap in H0.
          injection H0; auto.
        + congruence.
      (* rule_stm_write_register *)
      - sound_steps_inversion.
        { contradiction. }
        sound_steps_inversion.
        sound_steps_inversion.
        rename γ30 into γ__pre, r1 into reg, v into v__pre, v5 into v__post, σ20 into σ, e11 into e, δ3 into δ.
        exists (write_heap γfocus reg v__post); cbn.
        specialize (write_heap_ptsreg γfocus reg v__post) as Hpost.
        split; auto.
        rewrite write_register_write_heap.
        intros τ k.
        specialize (Hsplit_γ τ k) as H__k.
        destruct_conjs.
        destruct (𝑹𝑬𝑮_eq_dec reg k).
        + dependent destruction t.
          dependent destruction eqi; cbn in *; subst.
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
      - sound_steps_inversion; cbn in *;
        insterU ltac:(cbn; auto; eassumption) IHtriple;
        microsail_destruct_propositional IHtriple;
        hoare_sound_inst; auto.
      (* rule_stm_assign_forwards *)
      - sound_steps_inversion; cbn in *.
        { insterU ltac:(cbn; auto; eassumption) IHtriple;
            microsail_destruct_propositional IHtriple;
            hoare_sound_inst; auto.
        }
        insterU ltac:(cbn; auto; eassumption) IHtriple.
        microsail_destruct_propositional IHtriple. cbn in *.
        hoare_sound_inst; auto.
        exists (H ‼ x)%lit.
        now rewrite env_update_update, env_update_lookup.
     (* rule_stm_call_forwards *)
      - pose proof (validCEnv _ _ f).
        destruct H; try contradiction.
        sound_steps_inversion; try contradiction.
        do 2 sound_steps_inversion.
        { insterU ltac:(cbn; auto; eassumption) H1.
          microsail_destruct_propositional H1.
          hoare_sound_inst; auto.
        }
        insterU ltac:(cbn; auto; eassumption) H1.
        microsail_destruct_propositional H1; cbn in *.
        hoare_sound_inst; auto; split; auto.
    Qed.

  End Soundness.

End HoareSound.
