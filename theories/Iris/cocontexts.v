From stdpp Require Import hlist.
From iris.prelude Require Export prelude.
From iris.bi Require Export bi.
From iris.proofmode Require Import base environments classes string_ident ltac_tactics coq_tactics reduction intro_patterns ltac_tactics.
From iris.prelude Require Import options.
Import bi.

From Katamaran.Iris Require Import cointro_patterns.

Definition pre_envs_entails_cocontexts_def {PROP : bi} (Γp Γs : env PROP) (Q : env PROP) :=
  (of_envs' Γp Γs ⊢ [∗] Q).
Definition pre_envs_entails_cocontexts_aux : seal (@pre_envs_entails_cocontexts_def). Proof. by eexists. Qed.
Definition pre_envs_entails_cocontexts := pre_envs_entails_cocontexts_aux.(unseal).
Definition pre_envs_entails_cocontexts_eq : @pre_envs_entails_cocontexts = @pre_envs_entails_cocontexts_def :=
  pre_envs_entails_cocontexts_aux.(seal_eq).

Definition envs_entails_cocontexts {PROP : bi} (Δ : envs PROP) (Q : env PROP) : Prop :=
  pre_envs_entails_cocontexts  PROP (env_intuitionistic Δ) (env_spatial Δ) Q.
Definition envs_entails_cocontexts_eq :
  @envs_entails_cocontexts = λ PROP (Δ : envs PROP) Q, (of_envs Δ ⊢ [∗] Q).
Proof. by rewrite /envs_entails_cocontexts pre_envs_entails_cocontexts_eq. Qed.
Global Instance: Params (@envs_entails_cocontexts) 1 := {}.


Declare Scope cocontexts_scope.
Global Arguments envs_entails_cocontexts {PROP} Δ Q%_cocontexts_scope.
(* Delimit Scope cocontexts_scope with env. *)
Global Arguments Envs _ _%_cocontexts_scope _%_cocontexts_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%_cocontexts_scope _%_string _%_I.

Notation "" := Enil (only printing) : cocontexts_scope.
Notation "Γ H : P" := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : stdpp_scope.
Notation "Γ '_' : P" := (Esnoc Γ (IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ '_'  :  '[' P ']' '//'", only printing) : stdpp_scope.

Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ Qp " :=
  (envs_entails_cocontexts (Envs Γ Δ _) Qp%I)
  (at level 1, Qp at level 200, left associativity,
  format "'[' Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ '//' Qp ']'", only printing) :
  stdpp_scope.
Notation "Δ '--------------------------------------' ∗ Qp" :=
  (envs_entails_cocontexts (Envs Enil Δ _) Qp%I)
  (at level 1, Qp at level 200, left associativity,
  format "'[' Δ '--------------------------------------' ∗ '//' Qp ']'", only printing) : stdpp_scope.

Section tactics.
Context {PROP : bi}.

Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types A : envs PROP.
Implicit Types P : PROP.

Lemma env_lookup_delete_sound  `{! Proper (equiv ==> equiv ==> equiv) op} `{! Monoid op} {i}
                     {m : PROP -> PROP}
                     `{! Proper (equiv ==> equiv) m} {Γ : env PROP} {P : PROP} :
  env_lookup i Γ = Some P ->
  ([^op list] k↦x ∈ Γ, m x) ⊣⊢ op (m P) ([^op list] k↦x ∈ env_delete i Γ, m x).
Proof.
  induction Γ; cbn.
  - inversion 1.
  - destruct (ident_beq i i0) eqn:ii0eq; cbn; first by inversion 1.
    intros Heq.
    rewrite monoid_assoc (monoid_comm (m P) (m a)) -monoid_assoc.
    now rewrite -(IHΓ Heq).
Qed.

Lemma env_app_sound  `{! Proper (equiv ==> equiv ==> equiv) op} `{! Monoid op}
                     {m : PROP -> PROP}
                     `{! Proper (equiv ==> equiv) m} {Γ1 Γ2 Γ3 : env PROP} :
  env_app Γ1 Γ2 = Some Γ3 ->
  ([^op list] k↦x ∈ Γ3, m x) ⊣⊢ op ([^op list] k↦x ∈ Γ1, m x) ([^op list] k↦x ∈ Γ2, m x).
Proof.
  revert Γ2 Γ3 ; induction Γ1; intros Γ2 Γ3; cbn.
  - inversion 1.
    now rewrite monoid_left_id.
  - destruct (env_app Γ1 Γ2) eqn:iheq; cbn; last inversion 1.
    destruct (env_lookup i e); inversion 1; cbn.
    rewrite <-(monoid_assoc (m a)).
    now rewrite (IHΓ1 _ _ iheq).
Qed.

Lemma env_replace_sound_sep
  `{! Proper (bi_entails ==> bi_entails ==> bi_entails) op}
  `{! Proper (equiv ==> equiv ==> equiv) op}
  `{! Monoid op} {m : PROP -> PROP} `{! Proper (equiv ==> equiv) m} `{! Proper (bi_entails ==> bi_entails) m}
  i (Δ Γ Δ' : env PROP) P :
  env_lookup i Δ = Some P ->
  env_replace i Γ Δ = Some Δ' ->
  (m P ⊢ ([^op list] k↦x ∈ Γ, m x)) -> ([^op list] k↦x ∈ Δ, m x) ⊢ ([^op list] k↦x ∈ Δ', m x).
Proof.
  revert Γ Δ';
  induction Δ; intros Γ Δ'; first inversion 1; cbn.
  destruct (ident_beq i i0).
  - inversion 1; subst.
    intros appeq HPΓ.
    now rewrite HPΓ (env_app_sound appeq).
  - intros lkpeq.
    destruct (env_lookup i0 Γ); first inversion 1.
    destruct (env_replace i Γ Δ) eqn:rplceq; cbn; inversion 1; subst.
    cbn. intros HPΓ.
    now rewrite (IHΔ _ _ lkpeq rplceq).
Qed.

Lemma env_replace_sound_sep_2 `{! Proper (bi_entails ==> bi_entails ==> bi_entails) op}
  `{! Proper (equiv ==> equiv ==> equiv) op}
  `{! Monoid op}
  `{! Monoid op} {m : PROP -> PROP} `{! Proper (equiv ==> equiv) m} `{! Proper (bi_entails ==> bi_entails) m}
  i (Δ Γ Δ' : env PROP) P :
  env_lookup i Δ = Some P ->
  env_replace i Γ Δ = Some Δ' ->
  (([^op list] k↦x ∈ Γ, m x) ⊢ m P) -> ([^op list] k↦x ∈ Δ', m x) ⊢ ([^op list] k↦x ∈ Δ, m x).
Proof.
  revert Γ Δ';
  induction Δ; intros Γ Δ'; first inversion 1; cbn.
  destruct (ident_beq i i0).
  - inversion 1; subst.
    intros appeq HPΓ.
    now rewrite (env_app_sound appeq) HPΓ.
  - intros lkpeq.
    destruct (env_lookup i0 Γ); first inversion 1.
    destruct (env_replace i Γ Δ) eqn:rplceq; inversion 1; subst.
    cbn. intros HΓP.
    now rewrite (IHΔ _ _ lkpeq rplceq).
Qed.
  
Lemma env_replace_sound_sep_3 {i Γ} {Δ Δ' : env PROP} {P : PROP}: 
  env_lookup i Δ = Some P ->
  env_replace i Γ Δ = Some Δ' ->
  [∗] Δ' ⊣⊢ [∗] (env_delete i Δ) ∗ [∗] Γ.
Proof.
  revert Δ'.
  induction Δ; first done. cbn.
  destruct (ident_beq i i0) eqn:Hii0; cbn.
  - induction 1. intros.
    rewrite sep_comm.
    rewrite env_app_sound //.
  - destruct (env_lookup i0 Γ); first by done.
    destruct (env_replace i Γ Δ) as [Δ2'| ] eqn:Hrep; last by done.
    intros Δ' HidP Hrep2.
    inversion Hrep2; subst; clear Hrep2.
    rewrite <-sep_assoc.
    now rewrite <-(IHΔ _ HidP eq_refl).
Qed.

(* Lemma envs_simple_replace_sound_2 Δ Δ' i p P Γ : *)
(*   envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' → *)
(*   ((if p then env_and_persistently Γ else [∗] Γ) ⊢ bi_persistently_if p P) -> (of_envs Δ' ⊢ of_envs Δ). *)
(* Proof.  *)
(*   destruct Δ; cbn in *. *)
(*   destruct (env_lookup i env_intuitionistic) eqn:lkpeq. *)
(*   - inversion 1; subst. *)
(*     destruct (env_app Γ env_spatial) eqn:appeq; last inversion 1. *)
(*     destruct (env_replace i Γ env_intuitionistic) eqn:repleq; cbn; inversion 1; subst. *)
(*     rewrite /of_envs /of_envs'; cbn. *)
(*     intros HΓP. *)
(*     rewrite (env_replace_sound_sep_2 (op := bi_and) (m := bi_persistently) _ _ _ _ _ lkpeq repleq HΓP). *)
(*     apply and_mono_l, pure_mono. *)
(*     admit. *)
(*   - destruct (env_lookup i env_spatial) eqn:lkpeq2; cbn; inversion 1; subst. *)
(*     destruct (env_app Γ env_intuitionistic) eqn:appeq; cbn; last inversion 1. *)
(*     destruct (env_replace i Γ env_spatial) eqn:repleq; cbn; inversion 1; subst. *)
(*     rewrite /of_envs /of_envs'; cbn. *)
(*     intros HΓP. *)
(*     rewrite (env_replace_sound_sep_2 _ _ _ _ _ lkpeq2 repleq HΓP). *)
(*     apply and_mono_l, pure_mono. *)
(*     admit. *)
(* Admitted. *)

Lemma tac_and_codestruct Δ i j1 j2 P P1 P2 Q :
  env_lookup i Q = Some P →
  FromSep P P2 P1 →
  match env_replace i (Esnoc (Esnoc Enil j2 P1) j1 P2) Q with
  | None => False
  | Some Q' => envs_entails_cocontexts Δ Q'
  end →
  envs_entails_cocontexts Δ Q.
Proof.
  destruct (env_replace _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_cocontexts_eq. intros.
  rewrite H1. clear H1 Δ.
  apply (env_replace_sound_sep_2 _ _ _ _ _ H Hrep).
  cbn.
  now rewrite sep_emp -(from_sep P P2 P1).
Qed.

Lemma tac_corename Δ i j P Q :
  env_lookup i Q = Some (P) →
  match env_replace i (Esnoc Enil j P) Q with
  | None => False
  | Some Q' => envs_entails_cocontexts Δ Q'
  end →
  envs_entails_cocontexts Δ Q.
Proof.
  destruct (env_replace _ _ _) as [Q' |] eqn:Hrep; last done.
  rewrite envs_entails_cocontexts_eq=> Hlkp HΔQp.
  rewrite HΔQp; clear HΔQp.
  apply (env_replace_sound_sep_2 _ _ _ _ _ Hlkp Hrep).
  cbn.
  now rewrite sep_emp.
Qed.

Lemma tac_start_cocontexts P (Γ : envs PROP) : envs_entails_cocontexts Γ (Esnoc Enil "Goal" P) -> envs_entails Γ P.
Proof.
  rewrite envs_entails_unseal /=.
  rewrite envs_entails_cocontexts_eq /=.
  now rewrite right_id.
Qed.

Lemma tac_stop_cocontexts {s} P (Γ : envs PROP) : envs_entails Γ P -> envs_entails_cocontexts Γ (Esnoc Enil s P).
Proof.
  rewrite envs_entails_unseal /=.
  rewrite envs_entails_cocontexts_eq /=.
  now rewrite right_id.
Qed.

Lemma tac_stop_cocontexts_entirely (Δh : envs PROP) (Δg : env PROP) :
  (of_envs Δh ⊢ [∗] Δg) →
  envs_entails_cocontexts Δh Δg.
Proof.
  now rewrite envs_entails_cocontexts_eq.
Qed.

(* Lemma envs_lookup_sound_2 Δ i p P : *)
(*   envs_lookup i Δ = Some (p,P) → *)
(*   envs_lookup i (envs_delete true i p Δ) = None -> *)
(*   □?p P ∗ of_envs (envs_delete true i p Δ) ⊢ of_envs Δ. *)
(* Proof. *)
(*   rewrite /envs_lookup !of_envs_eq=>HΔi HΔii. *)
(*   destruct Δ as [Γp Γs], (env_lookup i Γp) eqn:Heqo; simplify_eq/=. *)
(*   - rewrite -persistently_and_intuitionistically_sep_l. *)
(*     rewrite (env_lookup_perm Γp) //= !assoc (and_comm (<pers> P)%I _). *)
(*     repeat apply and_mono_l. *)
(*     apply pure_elim'. intros Hwf. *)
(*     apply pure_intro. *)
(*     destruct (env_lookup i (env_delete i Γp)) eqn:HeqΓii; inversion HΔii. *)
(*     destruct (env_lookup i Γs) eqn:HeqΓsi; inversion HΔii. *)
(*     admit. *)
(*   - destruct (env_lookup i Γs) eqn:?; simplify_eq/=. *)
(*     rewrite (env_lookup_perm Γs) //=. *)

(*     rewrite sep_mono_r. *)
(*     rewrite (comm _ P) -persistent_and_sep_assoc. *)
(*     rewrite [(⌜_⌝ ∧ _)%I]and_elim_r. *)
(*     apply and_mono; first done. rewrite comm //. *)
(* Qed. *)

Lemma tac_frame_hyp Δh Δc i j P :
  envs_lookup i Δh = Some (false, P) →
  env_lookup j Δc = Some P →
  envs_entails_cocontexts (envs_delete false i false  Δh) (env_delete j Δc) →
  envs_entails_cocontexts Δh Δc.
Proof.
  rewrite envs_entails_cocontexts_eq.
  intros Hhi Hcj Hframe.
  rewrite (envs_lookup_sound' _ false) //.
  rewrite Hframe.
  now rewrite <-(env_lookup_delete_sound Hcj).
Qed.

Class LookupEnv (Γ : env PROP) (P : PROP) i :=
  lookup_env_result : env_lookup i Γ = Some P.
Global Arguments LookupEnv _ _%_I : simpl never.
Global Arguments lookup_env_result _ _%_I.
Global Hint Mode LookupEnv + + - : typeclass_instances.

Global Program Instance lookup_env_here {i Γ P}: LookupEnv (Esnoc Γ i P) P i.
Next Obligation.
  intros. cbn.
  destruct (ident_beq_reflect i i); [done| contradiction].
Qed.
Global Program Instance lookup_env_there {i Γ P j Q}: forall `{! LookupEnv Γ P i}, ident_beq i j = false -> LookupEnv (Esnoc Γ j Q) P i.
Next Obligation.
  intros * HLE Hineq. cbn.
  destruct (ident_beq_reflect i j).
  - inversion Hineq.
  - now apply lookup_env_result.
Qed.

(* Lemma tac_frame_hyp_in Δh Δc i j Δc' p R P Q : *)
(*   envs_wf Δc -> *)
(*   envs_lookup i Δh = Some (p, P) → *)
(*   envs_lookup j Δc = Some (p, R) → *)
(*   Frame p P R Q → *)
(*   (envs_simple_replace j p (Esnoc Enil j Q) Δc) = Some Δc' -> *)
(*   envs_entails_cocontexts (envs_delete false i p Δh) Δc' → *)
(*   envs_entails_cocontexts Δh Δc. *)
(* Proof. *)
(*   rewrite envs_entails_cocontexts_eq. *)
(*   intros Hwfc Hhi Hcj Hframe Hrep HQ. *)
(*   rewrite (envs_lookup_sound' _ false) //. *)
(*   rewrite HQ. *)
(*   rewrite <-(envs_simple_replace_sound_2 Δc Δc' j p R (Esnoc Enil j Q) Hwfc Hcj Hrep). *)
(*   - apply sep_elim_r. *)
(*     Search Affine. *)
(*   Search bi_sep. *)
(*   Search envs_simple_replace. *)
(* (* Qed. *) *)
(* (* Admitted. *) *)

(* Lemma tac_frame_hyp_in_lookup Δh Δc i j p P : *)
(*   envs_lookup i Δh = Some (p, P) → *)
(*   LookupEnv (env_spatial Δc) P j -> *)
(*   envs_entails_cocontexts (envs_delete false i p Δh) (envs_delete false j p Δc) → *)
(*   envs_entails_cocontexts Δh Δc. *)
(* Proof. *)
(* (*   rewrite envs_entails_cocontexts_eq. intros ? Hframe HQ. *) *)
(* (*   rewrite (envs_lookup_sound' _ false) //. by rewrite -Hframe HQ. *) *)
(* (* Qed. *) *)
(* Admitted. *)

Lemma lookup_env_envs {Δ j P} : `{LookupEnv (env_spatial Δ) P j} ->
                                envs_wf Δ ->
                                  envs_lookup j Δ = Some (false, P).
Proof.
  intros HLE Hwf.
  assert (eq := @lookup_env_result _ _ _ HLE).
  unfold envs_lookup.
  destruct Δ; cbn.
  inversion Hwf.
  destruct (envs_disjoint j).
  - now rewrite H eq; cbn.
  - assert (Some P = None) by (now transitivity (env_lookup j env_spatial)).
    now inversion H0.
Qed.

Lemma use_wf {Δ Q} : (envs_wf Δ -> of_envs Δ ⊢ Q) -> of_envs Δ ⊢ Q.
Proof.
  intros.
  rewrite of_envs_eq.
  rewrite <-(idemp bi_and (bi_pure (envs_wf Δ))).
  rewrite -!bi.and_assoc.
  apply pure_elim_l; intros Hwf.
  rewrite -of_envs_eq.
  now apply H.
Qed.

Lemma tac_frame_cohyp_in_lookup Δh Δc i j P :
  env_lookup i Δc = Some P →
  LookupEnv (env_spatial Δh) P j ->
  envs_entails_cocontexts (envs_delete false j false Δh) (env_delete i Δc) →
  envs_entails_cocontexts Δh Δc.
Proof.
  rewrite envs_entails_cocontexts_eq. intros Hci Hhj HQ.
  apply use_wf. intros Hwfh.
  assert (Hhj2 := lookup_env_envs Hhj Hwfh).
  rewrite (envs_lookup_sound' _ false) //.
  rewrite HQ.
  cbn.
  now rewrite -env_lookup_delete_sound.
Qed.

Class FromPureEnv {PROP : bi} (a : bool) (P : env PROP) (φ : Prop) :=
  from_pure_env : <affine>?a ⌜φ⌝ ⊢ [∗] P.
Global Arguments FromPureEnv {_} _ _%_I _%_type_scope : simpl never.
Global Arguments from_pure_env {_} _ _%_I _%_type_scope {_}.
Global Hint Mode FromPureEnv + - ! - : typeclass_instances.

Global Instance from_pure_env_nil :
  FromPureEnv true (Enil : env PROP) True.
Proof.
  now apply affinely_elim_emp.
Qed.

Global Instance from_pure_env_snoc {a} {Γ : env PROP} {Γt P Pt i} :
  forall `{! FromPureEnv a Γ Γt}
  `{! FromPure a P Pt},
    FromPureEnv a (Esnoc Γ i P) (Γt /\ Pt).
Proof.
  intros HΓ HP.
  now rewrite /FromPureEnv pure_and affinely_if_and persistent_and_sep_1 sep_comm HΓ HP.
Qed.

(** * Pure *)
Lemma tac_pure_intro Δh (Δc : env PROP) φ :
  FromPureEnv false Δc φ →
  (* (if a then AffineEnv (env_spatial Δc) else TCTrue) → *)
  φ →
  envs_entails_cocontexts Δh Δc.
Proof.
  intros.
  apply tac_stop_cocontexts_entirely.
  rewrite <-(from_pure_env false _ _).
  now apply pure_intro.
Qed.

Lemma tac_split_off_cohyp Δh Δc i P js :
  env_lookup i Δc = Some P →
  match envs_split Left js Δh with
  | Some (Δl , Δr) => 
      envs_entails Δl P /\
        envs_entails_cocontexts Δr (env_delete i Δc)
  | None => False
  end →
  envs_entails_cocontexts Δh Δc.
Proof.
  destruct (envs_split Left js Δh) as [[Δl Δr]|] eqn:Hsplit ; last easy.
  rewrite envs_entails_cocontexts_eq.
  rewrite envs_entails_unseal.
  intros Hlkp [Hl Hr].
  rewrite (env_lookup_delete_sound Hlkp).
  rewrite (envs_split_sound _ _ _ _ _ Hsplit).
  now rewrite Hr Hl.
Qed.

Lemma tac_pure_intro_cohyp Δh Δc i P φ :
  env_lookup i Δc = Some P →
  FromPure false P φ →
  (* (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) → *)
  (envs_entails_cocontexts Δh (env_delete i Δc)) → φ → envs_entails_cocontexts Δh Δc.
Proof.
  rewrite envs_entails_cocontexts_eq.
  intros.
  rewrite (env_lookup_delete_sound H).
  rewrite <-(from_pure false P φ).
  apply sep_intro_emp_valid_l; [|done].
  now apply pure_intro.
Qed.

Lemma tac_clear_cohyp Δh Δc i P :
  env_lookup i Δc = Some P →
  FromPure false P True →
  (* (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) → *)
  (envs_entails_cocontexts Δh (env_delete i Δc)) → envs_entails_cocontexts Δh Δc.
Proof.
  intros Hci Hpure HQ.
  now apply (tac_pure_intro_cohyp _ _ _ _ _ Hci Hpure HQ).
Qed.

(* not sure why this is local in iris.proofmode.coq_tactics.v *)
Local Instance affine_env_spatial Δ :
  AffineEnv (env_spatial Δ) → Affine ([∗] env_spatial Δ).
Proof. intros H. induction H; simpl; apply _. Qed.

Lemma tac_empty_cocontext_intro Δ :
  AffineEnv (env_spatial Δ) → envs_entails_cocontexts Δ Enil.
Proof. intros. rewrite envs_entails_cocontexts_eq.
       rewrite (affine (of_envs Δ)); cbn.
       repeat apply and_intro; cbn; last easy.
Qed.

Lemma tac_exist_codestruct {A : Type} Δh Δc i j P (Φ : A → PROP) a :
  env_lookup i Δc = Some P → FromExist P Φ →
  ( match env_replace i (Esnoc Enil j (Φ a)) Δc with
     | Some Δc' => envs_entails_cocontexts Δh Δc'
     | None => False
     end) →
  envs_entails_cocontexts Δh Δc.
Proof.
  rewrite envs_entails_cocontexts_eq.
  intros.
  destruct (env_replace i (Esnoc _ j (Φ a)) Δc) eqn:rep; last done.
  rewrite -(env_replace_sound_sep_2 _ _ _ _ _ H rep) //=.
  rewrite sep_emp.
  rewrite <-H0.
  now apply exist_intro.
Qed.

End tactics.

(** Called by all tactics to perform computation to lookup items in the
    context.  We avoid reducing anything user-visible here to make sure we
    do not reduce e.g. before unification happens in [iApply].*)
Declare Reduction pm_eval_cocontexts := cbv [
  (* base *)
  base.negb base.beq
  base.Pos_succ base.ascii_beq base.string_beq base.positive_beq base.ident_beq
  (* environments *)
  env_lookup env_lookup_delete env_delete env_app env_replace
  env_dom env_intuitionistic env_spatial env_counter env_spatial_is_nil envs_dom
  envs_lookup envs_lookup_delete envs_delete envs_snoc envs_app
  envs_simple_replace envs_replace envs_split
  envs_clear_spatial envs_clear_intuitionistic envs_incr_counter
  envs_split_go envs_split
  env_to_prop_go env_to_prop env_to_prop_and_go env_to_prop_and
  (* PM list and option functions *)
  pm_app pm_option_bind pm_from_option pm_option_fun
].
Ltac pm_eval t :=
  eval pm_eval_cocontexts in t.
Ltac pm_reduce :=
  (* Use [change_no_check] instead of [change] to avoid performing the
  conversion check twice. *)
  match goal with |- ?u => let v := pm_eval u in change_no_check v end.


Tactic Notation "iAndCodestructCohyp" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_and_codestruct with H H1 H2  _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iCoDestructCoHypAnd:" H "not found"
    |pm_reduce; tc_solve ||
     let P :=
       lazymatch goal with
       | |- IntoSep ?P _ _ => P
       | |- IntoAnd _ ?P _ _ => P
       end in
     fail "iAndDestruct: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H1 := pretty_ident H1 in
         let H2 := pretty_ident H2 in
         fail "iAndDestruct:" H1 "or" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

(** * Context manipulation *)
Tactic Notation "iCoRename" constr(H1) "into" constr(H2) :=
  eapply tac_corename with H1 H2 _ _; (* (i:=H1) (j:=H2) *)
    [pm_reflexivity ||
     let H1 := pretty_ident H1 in
     fail "iCoRename:" H1 "not found"
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H2 := pretty_ident H2 in
         fail "iRename:" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

(** * Start a proof *)
Tactic Notation "iStartProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => eapply tac_start_cocontexts
  | |- envs_entails_cocontexts _ _ => idtac
  | |- ?φ => notypeclasses refine (as_emp_valid_2 φ _ _);
           eapply tac_start_cocontexts;
               [tc_solve || fail "iStartProof: not a BI assertion"
               |notypeclasses refine (tac_start _ _)]
  end.

Ltac iTryStopCocontexts :=
  lazymatch goal with
  | |- envs_entails_cocontexts _ (Esnoc Enil _ _) => apply tac_stop_cocontexts; pm_reduce
  | |- _ => idtac
  end.

Tactic Notation "iStopProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => apply tac_stop; pm_reduce
  | |- envs_entails_cocontexts _ _ => apply tac_stop_cocontexts; pm_reduce
  | |- _ => fail "iStopProof: proofmode not started"
  end.

Ltac iFrameHyp Hh Hc :=
  iStartProof;
  eapply tac_frame_hyp with Hh Hc _ _;
    [pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |pm_reduce; iFrameFinish].

(* Ltac iFrameHypIn Hh Hc := *)
(*   iStartProof; *)
(*   eapply tac_frame_hyp_in with Hh Hc _ _ _ _ _; *)
(*     [pm_reflexivity || *)
(*      let H := pretty_ident Hh in *)
(*      fail "iFrame:" Hh "not found" *)
(*     |pm_reflexivity || *)
(*      let H := pretty_ident Hh in *)
(*      fail "iFrame:" Hh "not found" *)
(*     |tc_solve || *)
(*      let R := match goal with |- Frame _ ?R _ _ => R end in *)
(*      fail "iFrame: cannot frame" R *)
(*     |pm_reduce; iFrameFinish]. *)

(* Ltac iFrameHyp2 Hh := *)
(*   iStartProof; *)
(*   eapply tac_frame_hyp_in_lookup with Hh _ _ _; *)
(*     [pm_reflexivity || *)
(*      let H := pretty_ident Hh in *)
(*      fail "iFrame:" Hh "not found" *)
(*     |tc_solve || *)
(*      let P := match goal with |- LookupEnv _ ?P _ => P end in *)
(*      fail "iFrame: cannot frame" P *)
(*     |pm_reduce; iFrameFinish]. *)

Ltac iFrameCohyp Hh :=
  iStartProof;
  eapply tac_frame_cohyp_in_lookup with Hh _ _;
    [pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |((* not sure why this is needed *)
     try eauto using lookup_env_here, lookup_env_there;
     tc_solve) ||
     let P := match goal with |- LookupEnv _ ?P _ => P end in
     fail "iFrame: cannot frame" P
    |pm_reduce; iFrameFinish].

Ltac iFresh :=
  (* We make use of an Ltac hack to allow the [iFresh] tactic to both have a
  side-effect (i.e. to bump the counter) and to return a value (the fresh name).
  We do this by wrapped the side-effect under a [match] in a let-binding. See
  https://stackoverflow.com/a/46178884 *)
  let start :=
    lazymatch goal with
    | _ => iStartProof
    end in
  let c :=
    lazymatch goal with
    | |- envs_entails (Envs _ _ ?c) _ => c
    | |- envs_entails_cocontexts (Envs _ _ ?c) _ => c
    end in
  let inc :=
    lazymatch goal with
    | |- envs_entails (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails (Envs Δp Δs c') Q)
    | |- envs_entails_cocontexts (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails_cocontexts (Envs Δp Δs c') Q)
    end in
  constr:(IAnon c).

(* stolen from iris.proofmode.coq_tactics *)
Local Ltac ident_for_pat pat :=
  lazymatch pat with
  | IIdent ?x => x
  | _ => let x := iFresh in x
  end.

Local Ltac ident_for_pat_default pat default :=
  lazymatch pat with
  | IIdent ?x => x
  | _ =>
    lazymatch default with
    | IAnon _ => default
    | _ => let x := iFresh in x
    end
  end.

Tactic Notation "iPureIntroCohyp" constr(H) tactic(solver):=
  iStartProof;
  eapply tac_pure_intro_cohyp with H _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iFrame:" H "not found"
    |tc_solve ||
     let P := match goal with |- FromPure _ ?P _ => P end in
     fail "iPureIntroCohyp:" P "not pure"
    (* |pm_reduce; tc_solve || *)
    (*  fail "iPureIntro: spatial context contains non-affine hypotheses" *)
    | pm_reduce |  solver ].

Tactic Notation "iPureIntro" :=
  iStopProof; iPureIntro.
  (* iStartProof; *)
  (* eapply tac_pure_intro; *)
  (*   [tc_solve || *)
  (*    let P := match goal with |- FromPureEnv _ ?P _ => P end in *)
  (*    match goal with |- ?H => idtac H end; *)
  (*    fail "iPureIntro:" P "not pure" *)
  (*   (* |pm_reduce; tc_solve || *) *)
  (*   (*  fail "iPureIntro: spatial context contains non-affine hypotheses" *) *)
  (*   |]. *)

Tactic Notation "iExistCodestruct" constr(H)
    "as" constr(Hx) :=
  eapply tac_exist_codestruct with H Hx _ _ _; (* (i:=H) (j:=Hx) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistCodestruct:" H "not found"
    |tc_solve ||
     let P := match goal with |- FromExist ?P _ => P end in
     fail "iExistCodestruct: cannot codestruct" P|]; pm_reduce.

Tactic Notation "iClearCohyp" constr(H) :=
  iPureIntroCohyp H done.

(** [pat0] is the unparsed pattern, and is only used in error messages *)
Ltac iCodestructCohypCointroGo Hz pat0 pat :=
  lazymatch pat with
  (* | IFresh => *)
  (*    lazymatch Hz with *)
  (*    | IAnon _ => idtac *)
  (*    | INamed ?Hz => let Hz' := iFresh in iCoRename Hz into Hz' *)
  (*    end *)
  | SDrop => iClearCohyp Hz
  | SFrame => iFrameCohyp Hz
  | SFrameByName ?Hh _ => iFrameHyp Hh Hz
  | SPureGoal ?pd =>
      iPureIntroCohyp Hz (refine _; match pd with
                                    | true => done
                                    | _ => idtac
                                    end)
  | SCoHyp ?y => iRename Hz into y
  | SSplitGoal ?cg => idtac
  | SRefl => iPureIntroCohyp Hz reflexivity
  | SList [[]] => iExFalso; iExact Hz
  (* conjunctive patterns like [H1 H2] *)
  (* [% ...] is always interpreted as an existential; there are [IntoExist]
  instances in place to handle conjunctions with a pure left-hand side this way
  as well. *)
  | SList [SPureGoal ?pd; ?pat2] =>
      (* guard (¬pd); *)
      let x := ident_for_pat_default pat2 Hz in
      iExistCodestruct Hz as x; iCodestructCohypCointroGo x pat0 pat2
  | SList [?pat1; ?pat2] =>
     (* We have to take care of not using the same name for the two hypotheses: *)
  (*       [ident_for_pat_default] will thus only reuse [Hz] (which could in principle *)
  (*       clash with a name from [pat2]) if it is an anonymous name. *)
     let x1 := ident_for_pat_default pat1 Hz in
     let x2 := ident_for_pat pat2 in
     iAndCodestructCohyp Hz as x1 x2;
     iCodestructCohypCointroGo x1 pat0 pat1;
     iCodestructCohypCointroGo x2 pat0 pat2
  | _ => fail "iDestruct:" pat0 "is not supported due to" pat
  end.


Ltac iCodestructCohypCointroFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify (* post-tactic prettification *)
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => iCodestructCohypCointroGo Hgo pat pat1; iCodestructCohypCointroFindPat Hgo pat true pats
     | true => fail "iCoestructCointro:" pat "should contain exactly one proper introduction pattern"
     end
  end.
Tactic Notation "iCodestructCointro" constr(H) "as" constr(pat) :=
  try iStartProof;
  let pats := cointro_pat.parse pat in iCodestructCohypCointroFindPat H pat false pats.
Tactic Notation "iCodestructCointro" "as" constr(pat) :=
  iCodestructCointro "Goal" as pat.
(** [pat0] is the unparsed pattern, and is only used in error messages *)

Ltac iCodestructCohypGo Hz pat0 pat :=
  lazymatch pat with
  | IFresh =>
     lazymatch Hz with
     | IAnon _ => idtac
     | INamed ?Hz => let Hz' := iFresh in iCoRename Hz into Hz'
     end
  | IDrop => iClearCohyp Hz
  | IFrame => iFrameCohyp Hz
  | IIdent Hz => idtac
  | IIdent ?y => iRename Hz into y
  (* | IList [[]] => iExFalso; iExact Hz *)

  (* conjunctive patterns like [H1 H2] *)
  (* | IList [[?pat1; IDrop]] => *)
  (*    let x := ident_for_pat_default pat1 Hz in *)
  (*    iAndDestructChoice Hz as Left x; *)
  (*    iDestructHypGo x pat0 pat1 *)
  (* | IList [[IDrop; ?pat2]] => *)
  (*    let x := ident_for_pat_default pat2 Hz in *)
  (*    iAndDestructChoice Hz as Right x; *)
  (*    iDestructHypGo x pat0 pat2 *)
  (* [% ...] is always interpreted as an existential; there are [IntoExist]
  instances in place to handle conjunctions with a pure left-hand side this way
  as well. *)
  | IList [[IPure IGallinaAnon; ?pat2]] =>
     let x := ident_for_pat_default pat2 Hz in
     iExistCodestruct Hz as x; iCodestructCohypGo x pat0 pat2
  (* | IList [[IPure (IGallinaNamed ?s); ?pat2]] => *)
  (*    let y := ident_for_pat_default pat2 Hz in *)
  (*    iExistCodestruct Hz as x y; *)
  (*    rename_by_string x s; *)
  (*    iDestructHypGo y pat0 pat2 *)
  | IList [[?pat1; ?pat2]] =>
     (* We have to take care of not using the same name for the two hypotheses: *)
  (*       [ident_for_pat_default] will thus only reuse [Hz] (which could in principle *)
  (*       clash with a name from [pat2]) if it is an anonymous name. *)
     let x1 := ident_for_pat_default pat1 Hz in
     let x2 := ident_for_pat pat2 in
     iAndCodestructCohyp Hz as x1 x2;
     iCodestructCohypGo x1 pat0 pat1;
     iCodestructCohypGo x2 pat0 pat2
  | IList [_ :: _ :: _] => fail "iDestruct:" pat0 "has too many conjuncts"
  | IList [[_]] => fail "iDestruct:" pat0 "has just a single conjunct"

  (* disjunctive patterns like [H1|H2] *)
  (* | IList [[?pat1];[?pat2]] => *)
  (*    let x1 := ident_for_pat_default pat1 Hz in *)
  (*    let x2 := ident_for_pat_default pat2 Hz in *)
  (*    iOrDestruct Hz as x1 x2; *)
  (*    [iDestructHypGo x1 pat0 pat1|iDestructHypGo x2 pat0 pat2] *)
  (* this matches a list of three or more disjunctions [H1|H2|H3] *)
  (* | IList (_ :: _ :: _ :: _) => fail "iDestruct:" pat0 "has too many disjuncts" *)
  (* the above patterns don't match [H1 H2|H3] *)
  (* | IList [_;_] => fail "iDestruct: in" pat0 "a disjunct has multiple patterns" *)

  | IPure IGallinaAnon =>
      iPureIntroCohyp Hz (refine _)
  (* | IPure (IGallinaNamed ?s) => *)
  (*    let x := fresh in *)
  (*    iPure Hz as x; *)
  (*    rename_by_string x s *)
  | IRewrite _ => iPureIntroCohyp Hz reflexivity
  (* | IIntuitionistic ?pat => *)
  (*   let x := ident_for_pat_default pat Hz in *)
  (*   iIntuitionistic Hz as x; iDestructHypGo x pat0 pat *)
  (* | ISpatial ?pat => *)
  (*   let x := ident_for_pat_default pat Hz in *)
  (*   iSpatial Hz as x; iDestructHypGo x pat0 pat *)
  (* | IModalElim ?pat => *)
  (*   let x := ident_for_pat_default pat Hz in *)
  (*   iModCore Hz as x; iDestructHypGo x pat0 pat *)
  | _ => fail "iDestruct:" pat0 "is not supported due to" pat
  end.

Local Ltac iCodestructCohypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify (* post-tactic prettification *)
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ISimpl :: ?pats => simpl; iCodestructCohypFindPat Hgo pat found pats
  (* | IClear ?H :: ?pats => iClear H; iDestructHypFindPat Hgo pat found pats *)
  (* | IClearFrame ?H :: ?pats => iFrame H; iDestructHypFindPat Hgo pat found pats *)
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => iCodestructCohypGo Hgo pat pat1; iCodestructCohypFindPat Hgo pat true pats
     | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
     end
  end.
Tactic Notation "iCodestruct" constr(H) "as" constr(pat) :=
  try iStartProof;
  let pats := intro_pat.parse pat in iCodestructCohypFindPat H pat false pats.
Tactic Notation "iCodestruct" "as" constr(pat) :=
  iCodestruct "Goal" as pat.

Tactic Notation "iIntros" := (iTryStopCocontexts; iIntros [IAll]).
Tactic Notation "iIntros" constr(pat) := (iTryStopCocontexts; pm_reduce; iIntros pat).
Tactic Notation "iIntros" constr(pat) := (iTryStopCocontexts; pm_reduce; iIntros pat).

(* Tactic Notation "iEmpIntroCohyp" := *)
(*   iStartProof; *)
(*   eapply tac_emp_intro_cohyp; *)
(*     [pm_reduce; tc_solve || *)
(*      fail "iEmpIntro: spatial context contains non-affine hypotheses"]. *)

Tactic Notation "iEmptyCocontextIntro" :=
  iStartProof;
  eapply tac_empty_cocontext_intro;
    [pm_reduce; tc_solve ||
     fail "iEmpIntro: spatial context contains non-affine hypotheses"].

(** Automation *)
Global Hint Extern 0 (_ ⊢ _) => iStartProof : core.
Global Hint Extern 0 (⊢ _) => iStartProof : core.

(* Make sure that [by] and [done] solve trivial things in proof mode.
[iPureIntro] invokes [FromPure], so adding [FromPure] instances can help improve
what [done] can do. *)
Global Hint Extern 0 (envs_entails_cocontexts _ _) => iPureIntro; try done : core.
(* Global Hint Extern 0 (envs_entails _ ?Q) => *)
(*   first [is_evar Q; fail 1|iAssumption] : core. *)
Global Hint Extern 0 (envs_entails_cocontexts _ Enil) => iEmptyCocontextIntro : core.

(* (* TODO: look for a more principled way of adding trivial hints like those *)
(* below; see the discussion in !75 for further details. *) *)
(* Global Hint Extern 0 (envs_entails _ (_ ≡ _)) => *)
(*   rewrite envs_entails_eq; apply internal_eq_refl : core. *)
(* Global Hint Extern 0 (envs_entails _ (big_opL _ _ _)) => *)
(*   rewrite envs_entails_eq; apply (big_sepL_nil' _) : core. *)
(* Global Hint Extern 0 (envs_entails _ (big_sepL2 _ _ _)) => *)
(*   rewrite envs_entails_eq; apply (big_sepL2_nil' _) : core. *)
(* Global Hint Extern 0 (envs_entails _ (big_opM _ _ _)) => *)
(*   rewrite envs_entails_eq; apply (big_sepM_empty' _) : core. *)
(* Global Hint Extern 0 (envs_entails _ (big_sepM2 _ _ _)) => *)
(*   rewrite envs_entails_eq; apply (big_sepM2_empty' _) : core. *)
(* Global Hint Extern 0 (envs_entails _ (big_opS _ _ _)) => *)
(*   rewrite envs_entails_eq; apply (big_sepS_empty' _) : core. *)
(* Global Hint Extern 0 (envs_entails _ (big_opMS _ _ _)) => *)
(*   rewrite envs_entails_eq; apply (big_sepMS_empty' _) : core. *)

(* (* These introduce as much as possible at once, for better performance. *) *)
(* Global Hint Extern 0 (envs_entails _ (∀ _, _)) => iIntros : core. *)
(* Global Hint Extern 0 (envs_entails _ (_ → _)) => iIntros : core. *)
(* Global Hint Extern 0 (envs_entails _ (_ -∗ _)) => iIntros : core. *)
(* (* Multi-intro doesn't work for custom binders. *) *)
(* Global Hint Extern 0 (envs_entails _ (∀.. _, _)) => iIntros (?) : core. *)

(* Global Hint Extern 1 (envs_entails _ (_ ∧ _)) => iSplit : core. *)
(* Global Hint Extern 1 (envs_entails _ (_ ∗ _)) => iSplit : core. *)
(* Global Hint Extern 1 (envs_entails _ (_ ∗-∗ _)) => iSplit : core. *)
(* Global Hint Extern 1 (envs_entails _ (▷ _)) => iNext : core. *)
(* Global Hint Extern 1 (envs_entails _ (■ _)) => iModIntro : core. *)
(* Global Hint Extern 1 (envs_entails _ (<pers> _)) => iModIntro : core. *)
(* Global Hint Extern 1 (envs_entails _ (<affine> _)) => iModIntro : core. *)
(* Global Hint Extern 1 (envs_entails _ (□ _)) => iModIntro : core. *)
(* Global Hint Extern 1 (envs_entails _ (∃ _, _)) => iExists _ : core. *)
(* Global Hint Extern 1 (envs_entails _ (∃.. _, _)) => iExists _ : core. *)
(* Global Hint Extern 1 (envs_entails _ (◇ _)) => iModIntro : core. *)
(* Global Hint Extern 1 (envs_entails _ (_ ∨ _)) => iLeft : core. *)
(* Global Hint Extern 1 (envs_entails _ (_ ∨ _)) => iRight : core. *)
(* Global Hint Extern 1 (envs_entails _ (|==> _)) => iModIntro : core. *)
(* Global Hint Extern 1 (envs_entails _ (<absorb> _)) => iModIntro : core. *)
(* Global Hint Extern 2 (envs_entails _ (|={_}=> _)) => iModIntro : core. *)

(* Global Hint Extern 2 (envs_entails _ (_ ∗ _)) => progress iFrame : iFrame. *)

Fixpoint bi_wands {PROP : bi} (q : bool) (Ps : list PROP) (Q : PROP) : PROP :=
  match Ps with
  | nil => Q
  | P :: Ps => □?q P -∗ bi_wands q Ps Q
  end.

Class IntoWands {PROP : bi} {p q : bool} {R : PROP} {Ps : list PROP} {Q : PROP} :=
  into_wands : □?p R ⊢ bi_wands q Ps Q.
Global Arguments IntoWands {_} _ _ _%_I _%_I _%_I : simpl never.
Global Arguments into_wands {_} _ _ _%_I _%_I _%_I {_}.
Global Hint Mode IntoWands + + + ! - - : typeclass_instances.

Global Program Instance intoWandsNil {PROP : bi} {q} {R : PROP} : IntoWands false q R nil R.
Next Obligation. now cbn. Qed.

Global Program Instance intoWandsCons {PROP : bi} {Ps} {P R Q : PROP} 
  (iwR : IntoWands false false R Ps Q) : IntoWands false false (P -∗ R) (P :: Ps) Q.
Next Obligation.
  cbn. intros.
  pose proof (H := into_wands false _ _ _ Q (IntoWands := iwR)).
  cbn in H.
  now rewrite H.
Qed.

Lemma wands_elim_r {PROP : bi} {Ps : list PROP} {Q : PROP} `{!Affine (emp%I : PROP)} :
  [∗] Ps ∗ bi_wands false Ps Q ⊢ Q.
Proof.
  induction Ps; cbn.
  - apply sep_elim_r.
    now apply TCOr_l.
  - rewrite <-sep_assoc, <-sep_comm, <-sep_assoc.
    now rewrite wand_elim_l.
Qed.

Fixpoint list_to_env {A} (E : list A) (vs : list ident) : env A :=
  match (E, vs) with
  | (nil, nil) => Enil
  | (P :: Ps, v :: vs) => Esnoc (list_to_env Ps vs) v P 
  | _ => Enil
  end.
Global Instance: Params (@env_to_list) 1 := {}.

Lemma big_sep_list_to_env {PROP : bi} {Ps : list PROP} {vs} :
  length Ps = length vs ->
  [∗] list_to_env Ps vs ⊣⊢ [∗] Ps.
Proof.
  revert vs. induction Ps; intros vs.
  - destruct vs; now cbn.
  - destruct vs; first done.
    cbn. intros Heq.
    rewrite IHPs //.
    now lia.
Qed.


Lemma tac_apply_cocon {PROP : bi} Δh Δg i j vs Ps p (Q Q2 : PROP) P Δg2 :
  env_lookup i Δg = Some Q →
  envs_lookup j Δh = Some (p, P) →
  IntoWands p false P Ps Q2 →
  length vs = length Ps ->
  TCEq Q Q2 ->
  env_replace i (list_to_env Ps vs) Δg = Some Δg2 ->
  envs_entails_cocontexts (envs_delete true j p Δh) Δg2 ->
  envs_entails_cocontexts Δh Δg.
Proof.
  rewrite envs_entails_cocontexts_eq.
  intros lidgQ ljdhP PPsQ Hlen Qeq riPdg dh2dg2.
  induction Qeq.
  rewrite envs_lookup_sound //.
  clear ljdhP.
  rewrite (into_wands _ _ _ _ _ (IntoWands := PPsQ)).
  clear PPsQ.
  rewrite dh2dg2.
  clear dh2dg2.
  rewrite (env_replace_sound_sep_3 lidgQ riPdg).
  clear riPdg.
  rewrite sep_assoc sep_comm sep_assoc.
  rewrite big_sep_list_to_env //.
  rewrite wands_elim_r.
  now rewrite (env_lookup_delete_sound lidgQ).
Qed.

Ltac iApplyHypCocon H G Hs :=
  eapply (tac_apply_cocon _ _ G H Hs);
  [pm_reflexivity
  |pm_reflexivity
  |tc_solve
  |pm_reduce; tc_solve].


(** There is some hacky stuff going on here: because of Coq bug #6583, unresolved
type classes in e.g. the arguments [xs] of [iSpecializeArgs_go] are resolved at
arbitrary moments. That is because tactics like [apply], [split] and [eexists]
wrongly trigger type class search. To avoid TC being triggered too eagerly, the
tactics below use [notypeclasses refine] instead of [apply], [split] and
[eexists]. *)
Local Ltac iSpecializeArgs_go H xs :=
  lazymatch xs with
  | hnil => idtac
  | hcons ?x ?xs =>
     notypeclasses refine (tac_forall_specialize _ H _ _ _ _ _ _ _);
       [pm_reflexivity ||
        let H := pretty_ident H in
        fail "iSpecialize:" H "not found"
       |tc_solve ||
        let P := match goal with |- IntoForall ?P _ => P end in
        fail "iSpecialize: cannot instantiate" P "with" x
       |lazymatch goal with (* Force [A] in [ex_intro] to deal with coercions. *)
        | |- ∃ _ : ?A, _ =>
          notypeclasses refine (@ex_intro A _ x _)
        end; [shelve..|pm_reduce; iSpecializeArgs_go H xs]]
  end.
Local Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
  iSpecializeArgs_go H xs.

Ltac iSpecializePatCointro_go H1 pats :=
  let solve_to_wand H1 :=
    tc_solve ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand" in
  let solve_done d :=
    lazymatch d with
    | true =>
       first [ done
             | let Q := match goal with |- envs_entails _ ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done"
             | let Q := match goal with |- ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done" ]
    | false => idtac
    end in
  let Δ := iGetCtx in
  lazymatch pats with
    | [] => idtac
    (* | SIdent ?H2 [] :: ?pats => *)
    (*    (* If we not need to specialize [H2] we can avoid a lot of unncessary *)
    (*    context manipulation. *) *)
    (*    notypeclasses refine (tac_specialize false _ H2 _ H1 _ _ _ _ _ _ _ _ _); *)
    (*      [pm_reflexivity || *)
    (*       let H2 := pretty_ident H2 in *)
    (*       fail "iSpecialize:" H2 "not found" *)
    (*      |pm_reflexivity || *)
    (*       let H1 := pretty_ident H1 in *)
    (*       fail "iSpecialize:" H1 "not found" *)
    (*      |tc_solve || *)
    (*       let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in *)
    (*       let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in *)
    (*       fail "iSpecialize: cannot instantiate" P "with" Q *)
    (*      |pm_reduce; iSpecializePat_go H1 pats] *)
    (* | SIdent ?H2 ?pats1 :: ?pats => *)
    (*    (* If [H2] is in the intuitionistic context, we copy it into a new *)
    (*    hypothesis [Htmp], so that it can be used multiple times. *) *)
    (*    let H2tmp := iFresh in *)
    (*    iPoseProofCoreHyp H2 as H2tmp; *)
    (*    (* Revert [H1] and re-introduce it later so that it will not be consumsed *)
    (*    by [pats1]. *) *)
    (*    iRevertHyp H1 with (fun p => *)
    (*      iSpecializePatCointro_go H2tmp pats1; *)
    (*        [.. (* side-conditions of [iSpecialize] *) *)
    (*        |iIntro H1 as p]); *)
    (*      (* We put the stuff below outside of the closure to get less verbose *)
    (*      Ltac backtraces (which would otherwise include the whole closure). *) *)
    (*      [.. (* side-conditions of [iSpecialize] *) *)
    (*      |(* Use [remove_intuitionistic = true] to remove the copy [Htmp]. *) *)
    (*       notypeclasses refine (tac_specialize true _ H2tmp _ H1 _ _ _ _ _ _ _ _ _); *)
    (*         [pm_reflexivity || *)
    (*          let H2tmp := pretty_ident H2tmp in *)
    (*          fail "iSpecialize:" H2tmp "not found" *)
    (*         |pm_reflexivity || *)
    (*          let H1 := pretty_ident H1 in *)
    (*          fail "iSpecialize:" H1 "not found" *)
    (*         |tc_solve || *)
    (*          let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in *)
    (*          let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in *)
    (*          fail "iSpecialize: cannot instantiate" P "with" Q *)
    (*         |pm_reduce; iSpecializePat_go H1 pats]] *)
    (* | SPureGoal ?d :: ?pats => *)
    (*    notypeclasses refine (tac_specialize_assert_pure _ H1 _ _ _ _ _ _ _ _ _ _ _ _); *)
    (*      [pm_reflexivity || *)
    (*       let H1 := pretty_ident H1 in *)
    (*       fail "iSpecialize:" H1 "not found" *)
    (*      |solve_to_wand H1 *)
    (*      |tc_solve || *)
    (*       let Q := match goal with |- FromPure _ ?Q _ => Q end in *)
    (*       fail "iSpecialize:" Q "not pure" *)
    (*      |solve_done d (*goal*) *)
    (*      |pm_reduce; *)
    (*       iSpecializePat_go H1 pats] *)
    (* | SGoal (SpecGoal GIntuitionistic false ?Hs_frame [] ?d) :: ?pats => *)
    (*    notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _); *)
    (*      [pm_reflexivity || *)
    (*       let H1 := pretty_ident H1 in *)
    (*       fail "iSpecialize:" H1 "not found" *)
    (*      |solve_to_wand H1 *)
    (*      |tc_solve || *)
    (*       let Q := match goal with |- Persistent ?Q => Q end in *)
    (*       fail "iSpecialize:" Q "not persistent" *)
    (*      |tc_solve *)
    (*      |pm_reduce; iFrame Hs_frame; solve_done d (*goal*) *)
    (*      |pm_reduce; iSpecializePat_go H1 pats] *)
    (* | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: ?pats => *)
    (*    fail "iSpecialize: cannot select hypotheses for intuitionistic premise" *)
    (* | SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d) :: ?pats => *)
    (*    let Hs' := eval cbv in (if lr then Hs else Hs_frame ++ Hs) in *)
    (*    notypeclasses refine (tac_specialize_assert _ H1 _ *)
    (*        (if m is GModal then true else false) lr Hs' _ _ _ _ _ _ _ _ _); *)
    (*      [pm_reflexivity || *)
    (*       let H1 := pretty_ident H1 in *)
    (*       fail "iSpecialize:" H1 "not found" *)
    (*      |solve_to_wand H1 *)
    (*      |tc_solve || fail "iSpecialize: goal not a modality" *)
    (*      |pm_reduce; *)
    (*       lazymatch goal with *)
    (*       | |- False => *)
    (*         let Hs' := iMissingHypsCore Δ Hs' in *)
    (*         fail "iSpecialize: hypotheses" Hs' "not found" *)
    (*       | _ => *)
    (*         notypeclasses refine (conj _ _); *)
    (*           [iFrame Hs_frame; solve_done d (*goal*) *)
    (*           |iSpecializePat_go H1 pats] *)
    (*       end] *)
    (* | SAutoFrame GIntuitionistic :: ?pats => *)
    (*    notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _); *)
    (*      [pm_reflexivity || *)
    (*       let H1 := pretty_ident H1 in *)
    (*       fail "iSpecialize:" H1 "not found" *)
    (*      |solve_to_wand H1 *)
    (*      |tc_solve || *)
    (*       let Q := match goal with |- Persistent ?Q => Q end in *)
    (*       fail "iSpecialize:" Q "not persistent" *)
    (*      |tc_solve || *)
    (*       fail "iSpecialize: Cannot find IntoAbsorbingly;" *)
    (*            "this should not happen, please report a bug" *)
    (*      |pm_reduce; solve [iFrame "∗ #"] *)
    (*      |pm_reduce; iSpecializePat_go H1 pats] *)
    (* | SAutoFrame ?m :: ?pats => *)
    (*    notypeclasses refine (tac_specialize_frame _ H1 _ *)
    (*        (if m is GModal then true else false) _ _ _ _ _ _ _ _ _ _ _); *)
    (*      [pm_reflexivity || *)
    (*       let H1 := pretty_ident H1 in *)
    (*       fail "iSpecialize:" H1 "not found" *)
    (*      |solve_to_wand H1 *)
    (*      |tc_solve || fail "iSpecialize: goal not a modality" *)
    (*      |pm_reduce; *)
    (*       first *)
    (*         [notypeclasses refine (tac_unlock_emp _ _ _) *)
    (*         |notypeclasses refine (tac_unlock_True _ _ _) *)
    (*         |iFrame "∗ #"; notypeclasses refine (tac_unlock _ _ _) *)
    (*         |let P := *)
    (*            match goal with |- envs_entails _ (?P ∗ locked _)%I => P end in *)
    (*          fail 1 "iSpecialize: premise" P "cannot be solved by framing"] *)
    (*      |exact eq_refl]; iIntro H1; iSpecializePat_go H1 pats *)
    end.

Local Tactic Notation "iSpecializePatCointro" open_constr(H) constr(pat) :=
  let pats := cointro_pat.parse pat in iSpecializePatCointro_go H pats.


(** The argument [p] of [iSpecializeCore] can either be a Boolean, or an
introduction pattern that is coerced into [true] when it solely contains [#] or
[%] patterns at the top-level. *)
Tactic Notation "iSpecializeCoreCointro" open_constr(H)
    "with" open_constr(xs) open_constr(pat) "as" constr(p) :=
  let p := intro_pat_intuitionistic p in
  let pat := cointro_pat.parse pat in
  let H :=
    lazymatch type of H with
    | string => constr:(INamed H)
    | _ => H
    end in
  iSpecializeArgs H xs; [..|
    lazymatch type of H with
    | ident =>
       let pat := cointro_pat.parse pat in
       let Δ := iGetCtx in
       (* Check if we should use [tac_specialize_intuitionistic_helper]. Notice
       that [pm_eval] does not unfold [use_tac_specialize_intuitionistic_helper],
       so we should do that first. *)
       let b := eval cbv [use_tac_specialize_intuitionistic_helper] in
         (if p then use_tac_specialize_intuitionistic_helper Δ pat else false) in
       lazymatch eval pm_eval in b with
       | true =>
          (* Check that the BI is either affine, or the hypothesis [H] resides
          in the intuitionistic context. *)
          lazymatch iTypeOf H with
          | Some (?q, _) =>
             let PROP := iBiOfGoal in
             lazymatch eval compute in (q || tc_to_bool (BiAffine PROP)) with
             | true =>
                notypeclasses refine (tac_specialize_intuitionistic_helper _ H _ _ _ _ _ _ _ _ _ _);
                  [pm_reflexivity
                   (* This premise, [envs_lookup j Δ = Some (q,P)],
                   holds because the [iTypeOf] above succeeded *)
                  |pm_reduce; tc_solve
                   (* This premise, [if q then TCTrue else BiAffine PROP], holds
                   because we established that [q || TC_to_bool (BiAffine PROP)]
                   is true *)
                  |iSpecializePatCointro H pat;
                    [..
                    |notypeclasses refine (tac_specialize_intuitionistic_helper_done _ H _ _ _);
                     pm_reflexivity]
                  |tc_solve ||
                   let Q := match goal with |- IntoPersistent _ ?Q _ => Q end in
                   fail "iSpecialize:" Q "not persistent"
                  |pm_reduce (* goal *)]
             | false => iSpecializePatCointro H pat
             end
          | None =>
             let H := pretty_ident H in
             fail "iSpecialize:" H "not found"
          end
       | false => iSpecializePatCointro H pat
       end
    | _ => fail "iSpecialize:" H "should be a hypothesis, use iPoseProof instead"
    end].

Tactic Notation "iSpecializeCoreCointro" open_constr(t) "as" constr(p) :=
  lazymatch type of t with
  | string => iSpecializeCore t with hnil "" as p
  | ident => iSpecializeCore t with hnil "" as p
  | _ =>
    lazymatch t with
    | ITrm ?H ?xs ?pat => iSpecializeCore H with xs pat as p
    | _ => fail "iSpecialize:" t "should be a proof mode term"
    end
  end.

Tactic Notation "iSpecializeCointro" open_constr(t) :=
  iSpecializeCoreCointro t as false.
Tactic Notation "iSpecializeCointro" open_constr(t) "as" "#" :=
  iSpecializeCoreCointro t as true.



(* DOMI: Cocontexts ideas not yet there *)
(* less hard:
   - the cointroduction pattern [%x pat] should satisfy an existential goal by introducing an evar x and continuing with cointro pattern pat
   - codestruct a disjunction by choosing left or right branch.
   - make (iNext and) iModIntro work properly?
   - make iIntros work when there is only a single goal in the cocontext.
   - a variant of iIntros that introduces context and cocontext variables in one go.
   - what is actually the point of an intuitionistic cocontext?
   - a variant of iSplit that splits off a subset of context and cocontext into a separate coq goal.
   hard:
   - a variant of iApply that applies an entailment or wand to satisfy one of the current goals in the cocontext.
   - merge specialization patterns and cocontext patterns
   - what should iLob or iInduction or iInv or iRewrite do?
   - improve automation hints to make "now xyz" or "by xyz" more effective?
 *)
