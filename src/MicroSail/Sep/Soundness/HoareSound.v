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
      (* | [ H: ⟨ _, _, _, ?s ⟩ --->* ⟨ _, _, _, ?t ⟩, HF: Final ?t |- _ ] => *)
      (*   dependent destruction t *)
      | _ => progress (cbn in *; destruct_conjs; subst)
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

 Local Ltac hoare_sound_inst :=
    match goal with
    | [ IH: forall _ _ _ _ _ _, Final _ -> _
      , Hsplit_γ : split (heap ?γ) ?γframe ?γfocus
      , HS: ⟨ _, _, _ , _ ⟩ --->* ⟨ _, _, _ , ?t ⟩
      , HF: Final ?t
      , Hpre : ?P ?γfocus
      |- _
      ] => insterU ltac:(intuition; try now subst) IH
    | [ δΣ : NamedEnv Lit ?Σ
      , IH : forall (δΣ : NamedEnv Lit ?Σ) _ _ _ _ _ _ _, _ -> Final _ -> _
      |- _ ] => unshelve (insterU ltac:(intuition; try now subst) IH); try assumption
    end.

  Local Ltac hoare_sound_solve :=
    repeat
      (sound_steps_inversion;
       sound_simpl;
       try steps_inversion_inster;
       try hoare_sound_inst); intuition.

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
      (* | @sep_contract_unit _ Σ θΔ pre post => *)
      (*   forall (δΣ : NamedEnv Lit Σ) *)
      (*     (γ γ' : RegStore) (μ μ' : Memory) (δ δ' : LocalStore σs) (s' : Stm σs σ), *)
      (*     ⟨ γ, μ, δ, Pi f ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' -> *)
      (*     forall (γframe γfocus : Heap), *)
      (*       split (heap γ) γframe γfocus -> *)
      (*       (interpret (L:=HProp) δΣ pre) γfocus -> *)
      (*       exists (γfocus' : Heap), *)
      (*         split (heap γ') γframe γfocus' /\ *)
      (*         ResultOrFail s' (fun v => (interpret δΣ post) γfocus') *)
      | _ => False
      end.

  Lemma sound {Γ σ} (s : Stm Γ σ) :
    forall (validCEnv : ValidContractEnv' CEnv),
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
      intros validCEnv γ γ' μ μ' δ δ' s' Hsteps Hfinal
             PRE POST triple γframe γfocus Hsplit_γ Hpre.
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
        intuition; hoare_sound_solve; firstorder.
      (* rule_stm_lit *)
      - hoare_sound_solve.
      (* rule_stm_exp_forwards *)
      - hoare_sound_solve.
      (* rule_stm_exp_backwards *)
      - hoare_sound_solve.
      (* rule_stm_let *)
      - hoare_sound_solve.
        insterU ltac:(intuition; try now subst) H0.
        hoare_sound_solve.
      (* rule_stm_if *)
      - unshelve hoare_sound_solve; assumption.
        (* here insterU generates some trivial existential variables and shelves them.
           How to avoid that? *)
      (* rule_stm_if_backwards *)
      - hoare_sound_solve; firstorder.
      (* rule_stm_seq *)
      - hoare_sound_solve.
      (* (* rule_stm_assert *) *)
      - hoare_sound_solve.
        admit.
      (* rule_stm_fail *)
      - hoare_sound_solve.
      (* rule_stm_match_sum *)
      (* the proof of this case is slow, around 2min on my machine *)
      - admit.
      (* - sound_steps_inversion; sound_simpl. *)
      (*   + sound_steps_inversion; sound_simpl. *)
      (*     specialize (step_trans H12 H13) as H14. *)
      (*     insterU ltac:(intuition; now subst) H0. *)
      (*     destruct_conjs. *)
      (*     destruct H8; hoare_sound_solve. *)
      (*   + sound_steps_inversion; sound_simpl. *)
      (*     specialize (step_trans H12 H13) as H14. *)
      (*     insterU ltac:(intuition; now subst) H2. *)
      (*     destruct_conjs. *)
      (*     destruct H8; hoare_sound_solve. *)
      (*     congruence. *)
      (*     now dependent elimination H15. *)
     (* rule_stm_read_register *)
     - sound_steps_inversion. sound_simpl.
       exists γfocus.
       firstorder.
       unfold heap in *.
       unfold split in *.
       specialize (Hsplit_γ σ r).
       destruct_conjs.
       destruct H; destruct (γframe σ r); congruence.
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
         unfold split in Hsplit_γ.
         specialize (Hsplit_γ τ k) as H10.
         destruct_conjs.
         remember (𝑹𝑬𝑮_eq_dec r k) as reg_eq.
         dependent destruction reg_eq.
         * dependent destruction t.
           dependent destruction eqi.
           cbn in *.
           rewrite <- eqf in *.
           firstorder.
           ** rewrite H in Hpre. discriminate.
           ** subst. rewrite H.
              rewrite Hpost.
              unfold heap. f_equal.
              now rewrite read_write.
           ** rewrite H in Hpre. discriminate.
         * firstorder.
            ** subst.
               right. apply (write_heap_distinct γfocus r k n None v0 H).
            ** destruct (split_not_in_r_then_in_l (heap γ) γfocus γframe k
                           (RegStoreIsTotal γ) (split_comm _ _ _ Hsplit_γ) ltac:(auto)).
               rewrite H in *.
               subst.
               rewrite (write_heap_distinct γfocus r k n (Some x) ltac:(auto)
                           ltac:(auto)).
               unfold heap in *.
               rewrite (read_write_distinct γ n ).
               rewrite H1 in H0.
               assumption.
            ** specialize (split_not_in_r_then_in_l
                           (heap γ) γframe γfocus k (RegStoreIsTotal γ)
                           Hsplit_γ H) as [v1 H1].
               rewrite H1 in *.
               unfold heap in *. subst γ'.
               rewrite (read_write_distinct γ n).
               assumption.
       + firstorder.

     (* rule_stm_assign_backwards *)
     - hoare_sound_solve.
     (* rule_stm_assign_forwards *)
     -  admit.
     (* rule_stm_call_forwards *)
     - pose proof (validCEnv _ _ f).
       destruct (CEnv f).
       * destruct H0.
       * dependent elimination Hsteps.
         + sound_steps_inversion. sound_simpl.
         + sound_steps_inversion.
           dependent destruction H7.
           ++ dependent destruction H7; hoare_sound_solve.
           ++ dependent destruction H.
              hoare_sound_solve.
           ++ dependent destruction H.
              hoare_sound_solve.
       * firstorder.
    Admitted.

  End Soundness.

End HoareSound.
