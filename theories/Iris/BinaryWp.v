From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

Class irisGS2 (Λ1 Λ2 : language) (Σ : gFunctors) := IrisG {
  iris_invGS2 :: invGS Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program. *)
  state_interp2 : state Λ1 -> state Λ2 → nat → iProp Σ;

  (** Number of additional logical steps (i.e., later modality in the
  definition of WP) per physical step, depending on the physical steps
  counter. In addition to these steps, the definition of WP adds one
  extra later per physical step to make sure that there is at least
  one later for each physical step. *)
  num_laters_per_step2 : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono2 σ1 σ2 ns :
    state_interp2 σ1 σ2 ns ={∅}=∗ state_interp2 σ1 σ2 (S ns)
}.
Global Opaque iris_invGS2.

Definition wp_pre2 `{!irisGS2 Λ1 Λ2 Σ} (s : stuckness)
    (wp : coPset -d> expr Λ1 -d> expr Λ2 -d> (val Λ1 -d> val Λ2 -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ1 -d> expr Λ2 -d> (val Λ1 -d> val Λ2 -d> iPropO Σ) -d> iPropO Σ := λ E e11 e21 Φ,
  match to_val e11 with
  | Some v1 => |={E}=> ∃ v2, ⌜ e21 = of_val v2 ⌝ ∗ Φ v1 v2
  | None =>
      (|={E}=> ∀ σ11 σ21, ⌜stuck e11 σ11 -> stuck e21 σ21 ⌝) ∧
      (∀ σ11 σ21 ns κ1, state_interp2 σ11 σ21 ns ∗ £ 1 ={E,∅}=∗
       ⌜if s is NotStuck then reducible e11 σ11 else True⌝ ∗
       (∀ e12 σ12, ⌜prim_step e11 σ11 κ1 e12 σ12 []⌝
         ={∅}▷=∗^(S $ num_laters_per_step2 ns) |={∅,E}=>
       ∃ e22 σ22 κ2,
         ⌜ prim_step e21 σ21 κ2 e22 σ22 [] ⌝ ∗
         state_interp2 σ12 σ22 (S ns) ∗
         wp E e12 e22 Φ))
  end%I.

Local Instance wp_pre2_contractive `{!irisGS2 Λ1 Λ2 Σ} s : Contractive (wp_pre2 s).
Proof.
  rewrite /wp_pre2 /= => n wp wp' Hwp E e1 e2 Φ.
  do 20 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step2 as [|k IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

Definition wp_def2 `{!irisGS2 Λ1 Λ2 Σ} : stuckness -> coPset -d> expr Λ1 -d> expr Λ2 -d> (val Λ1 -d> val Λ2 -d> iPropO Σ) -d> iPropO Σ :=
  λ s : stuckness, fixpoint (wp_pre2 s).
Definition wp_aux2 : seal (@wp_def2). Proof. by eexists. Qed.
Definition wp2 := wp_aux2.(unseal).
Global Arguments wp2 {Λ1 Λ2 Σ _}.
Notation "'WP2' e1 'and' e2 @ s ; E {{ Φ }}" := (wp2 s E e1%E e2%E Φ)
  (at level 20, e1, e2, Φ at level 200, only parsing) : bi_scope.
Notation "'WP2' e1 'and' e2 @ s ; E {{| v w , Φ }}" := (wp2 s E e1%E e2%E (fun v w => Φ))
  (at level 20, e1, e2, Φ at level 200, v name, w name, only parsing) : bi_scope.
Lemma wp2_eq `{!irisGS2 Λ1 Λ2 Σ} : wp2 = @wp_def2 Λ1 Λ2 Σ _.
Proof. rewrite -wp_aux2.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS2 Λ1 Λ2 Σ}.
Implicit Type s : stuckness.
Implicit Type P : iProp Σ.
Implicit Type Φ : val Λ1 → val Λ2 → iProp Σ.
Implicit Type vA : val Λ1.
Implicit Type vB : val Λ2.
Implicit Type eA : expr Λ1.
Implicit Type eB : expr Λ2.

(* Weakest pre *)
Lemma wp2_unfold s E eA eB Φ :
  wp2 s E eA eB Φ ⊣⊢ wp_pre2 s (wp2 s) E eA eB Φ.
Proof. rewrite wp2_eq. apply (fixpoint_unfold (wp_pre2 s)). Qed.

Global Instance wp_ne2 s E eA eB n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp2 s E eA eB).
Proof.
  revert eA eB. induction (lt_wf n) as [n _ IH]=> eA eB Φ Ψ HΦ.
  rewrite !wp2_unfold /wp_pre2 /=.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 20 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step2 as [|k IHk]; simpl; last by rewrite IHk.
  do 10 (f_contractive || f_equiv).
  apply IH; auto. intros v.
  apply dist_lt with n; auto.
Qed.
Global Instance wp2_proper s E eA eB :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp2 s E eA eB).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne2=>v; apply equiv_dist.
Qed.
Global Instance wp2_contractive s E eA eB n :
  TCEq (to_val eA) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp2 s E eA eB).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp2_unfold /wp_pre2 He /=.
  do 19 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step2 as [|k IHk]; simpl; last by rewrite IHk.
  do 13 (f_contractive || f_equiv).
Qed.

Lemma wp2_value_fupd' s E Φ vA vB : WP2 (of_val vA) and (of_val vB) @ s ; E {{ Φ }} ⊣⊢ |={E}=> Φ vA vB.
Proof. rewrite wp2_unfold /wp_pre2 to_of_val.
       iSplit.
       - iIntros ">(%v2 & %eq & H)".
         apply of_val_inj in eq.
         now subst.
       - iIntros ">H !>".
         iExists vB.
         now iSplit.
Qed.

Lemma wp2_value s E Φ vA vB : Φ vA vB ⊢ WP2 (of_val vA) and (of_val vB) @ s ; E {{ Φ }}.
Proof. iIntros "HΦ".
       now rewrite wp2_value_fupd'.
Qed.

Lemma wp2_value' s E Φ eA eB vA vB : to_val eA = Some vA -> to_val eB = Some vB -> Φ vA vB ⊢ WP2 eA and eB @ s ; E {{ Φ }}.
Proof. iIntros (<-%of_to_val <-%of_to_val) "HΦ".
       now iApply wp2_value.
Qed.

Lemma wp2_strong_mono s1 s2 E1 E2 eA eB Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP2 eA and eB @ s1 ; E1 {{ Φ }} -∗ (∀ vA vB, Φ vA vB ={E2}=∗ Ψ vA vB) -∗ WP2 eA and eB @ s2 ; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (eA eB E1 E2 HE Φ Ψ).
  rewrite !wp2_unfold /wp_pre2 /=.
  destruct (to_val eA) as [v|] eqn:?.
  { iApply fupd_idemp.
    iApply (fupd_mask_mono E1 _); first done.
    iMod "H" as (v2 ->) "H".
    iModIntro.
    iMod ("HΦ" with "H") as "HΨ".
    iModIntro. iExists v2. now iSplitR.
  }
  iSplit.
  { iDestruct "H" as "[Hstuck _]".
    now iApply (fupd_mask_mono E1). }
  iDestruct "H" as "[_ H]".
  iIntros (σ11 σ21 ns κ1) "Hσ".
  iMod (fupd_mask_subseteq E1 HE) as "Hclose".
  iMod ("H" with "Hσ") as "[%Hred H]".
  iModIntro. iSplit; [by destruct s1, s2|].
  iIntros (e12 σ12 Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros ">(%e22 & %σ22 & %κ2 & %Hstep2 & Hstate & H)".
  iMod "Hclose" as "_".
  iModIntro.
  iExists e22, σ22, κ2.
  iSplitR; first done.
  iFrame "Hstate".
  iApply ("IH" with "[//] H HΦ").
Qed.

Lemma fupd_wp2 s E eA eB Φ : (|={E}=> wp2 s E eA eB Φ) ⊢ wp2 s E eA eB Φ.
Proof.
  rewrite wp2_unfold /wp_pre2. iIntros "H". destruct (to_val eA) as [v|] eqn:?.
  { by iMod "H". }
  iSplit.
  - now iMod "H" as "[H _]".
  - iIntros (σ11 σ21 ns κ1) "Hstate".
    iMod "H" as "[ _ H ]".
    iMod ("H" $! σ11 σ21 ns κ1 with "Hstate") as "[ %Hred H ]".
    iModIntro. now iSplitR.
Qed.

Lemma wp2_fupd s E eA eB Φ : wp2 s E eA eB (fun vA vB => |={E}=> Φ vA vB) ⊢ wp2 s E eA eB Φ.
Proof. iIntros "H". iApply (wp2_strong_mono s s E with "H"); auto. Qed.

(* Lemma wp2_atomic s E1 E2 eA eB Φ `{!Atomic (stuckness_to_atomicity s) eA} : *)
(*   (|={E1,E2}=> wp2 s E2 eA eB (fun vA vB => |={E2,E1}=> Φ vA vB)) ⊢ wp2 s E1 eA eB Φ. *)
(* Admitted. *)
(* Proof. *)
(*   iIntros "H". rewrite !wp2_unfold /wp_pre2. *)
(*   destruct (to_val eA) as [v|] eqn:He. *)
(*   { iDestruct "H" as ">>(%v2 & -> & >x)". auto. } *)
(*   iIntros (σ1 ns κ nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]". *)
(*   iModIntro. iIntros (e2 σ2 Hstep). *)
(*   iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
(*   iIntros ">(Hσ & H)". destruct s. *)
(*   - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2. *)
(*     + iDestruct "H" as ">> $". by iFrame. *)
(*     + iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?). *)
(*       by edestruct (atomic _ _ _ _ _ Hstep). *)
(*   - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val]. *)
(*     rewrite wp_value_fupd'. iMod "H" as ">H". *)
(*     iModIntro. iFrame "Hσ Hefs". by iApply wp_value_fupd'. *)
(* Qed. *)

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
(* Lemma wp_step_fupdN_strong n s E1 E2 e P Φ : *)
(*   TCEq (to_val e) None → E2 ⊆ E1 → *)
(*   (∀ σ ns κs nt, state_interp σ ns κs nt *)
(*        ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧ *)
(*   ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗ *)
(*     WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗ *)
(*   WP e @ s; E1 {{ Φ }}. *)
(* Proof. *)
(*   destruct n as [|n]. *)
(*   { iIntros (_ ?) "/= [_ [HP Hwp]]". *)
(*     iApply (wp_strong_mono with "Hwp"); [done..|]. *)
(*     iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". } *)
(*   rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H". *)
(*   iIntros (σ1 ns κ κs nt) "Hσ". *)
(*   destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last. *)
(*   { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. } *)
(*   iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP". *)
(*   iIntros "!>" (e2 σ2 efs Hstep). iMod ("H" $! e2 σ2 efs with "[% //]") as "H". *)
(*   iIntros "!>!>". iMod "H". iMod "HP". iModIntro. *)
(*   revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn. *)
(*   iInduction n as [|n] "IH" forall (n0 Hn). *)
(*   - iApply (step_fupdN_wand with "H"). iIntros ">($ & Hwp & $)". iMod "HP". *)
(*     iModIntro. iApply (wp_strong_mono with "Hwp"); [done|set_solver|]. *)
(*     iIntros (v) "HΦ". iApply ("HΦ" with "HP"). *)
(*   - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>". *)
(*     iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H"). *)
(*     auto with lia. *)
(* Qed. *)

Lemma stuck_fill_inv `{!@LanguageCtx Λ K} e σ :
  to_val e = None -> stuck (K e) σ → stuck e σ.
Proof. rewrite /stuck. intros ? [? ?]. eauto using irreducible_fill_inv. Qed.

Lemma wp_bind K1 K2 `{!LanguageCtx K1} `{!LanguageCtx K2} s E e1 e2 Φ :
  WP2 e1 and e2 @ s ; E {{| v1 v2 , WP2 (K1 (of_val v1)) and (K2 (of_val v2)) @ s ; E {{ Φ }} }} ⊢ WP2 (K1 e1) and (K2 e2) @ s ; E {{ Φ }}.
Proof.
  iIntros "H".
  iLöb as "IH" forall (E e1 e2 Φ). rewrite wp2_unfold /wp_pre2.
  destruct (to_val e1) as [v1|] eqn:He1.
  { apply of_to_val in He1 as <-. iApply fupd_wp2.
    now iMod "H" as "[%v2 (-> & H)]".
  }
  rewrite wp2_unfold /wp_pre2 fill_not_val /=; [|done].
  iSplit.
  { iDestruct "H" as "[>H _]". iModIntro.
    iIntros (σ11 σ21 Hstuck).
    iDestruct ("H" $! σ11 σ21) as "%Hstuck12".
    iPureIntro. now apply stuck_fill, Hstuck12, stuck_fill_inv.
  }
  iIntros (σ11 σ21 ns κ1) "Hσ".
  iDestruct "H" as "[_ H]".
  iMod ("H" with "Hσ") as "[%Hred H]".
  iModIntro. iSplitR.
  { destruct s; last by trivial. iPureIntro; now apply reducible_fill. }
  iIntros (e12 σ12 Hstep).
  destruct (fill_step_inv e1 σ11 κ1 e12 σ12 []) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ12 with "[//]") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "(%e22 & %σ22 & %κ2 & %Hstep2 & Hσ2 & Hwp)".
  iModIntro.
  iExists (K2 e22), σ22, κ2.
  iSplitR; first by iPureIntro; apply fill_step.
  iFrame "Hσ2".
  now iApply "IH".
Qed.

(* Lemma wp_bind_inv K1 `{!LanguageCtx K1} s E e Φ : *)
(*   wp2 s E (K1 e1) @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}. *)
(* Proof. *)
(*   iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=. *)
(*   destruct (to_val e) as [v|] eqn:He. *)
(*   { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. } *)
(*   rewrite fill_not_val //. *)
(*   iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]". *)
(*   iModIntro; iSplit. *)
(*   { destruct s; eauto using reducible_fill_inv. } *)
(*   iIntros (e2 σ2 efs Hstep). *)
(*   iMod ("H" $! _ _ _ with "[]") as "H"; first eauto using fill_step. *)
(*   iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). *)
(*   iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH". *)
(* Qed. *)

(** * Derived rules *)
Lemma wp2_mono s E e1 e2 Φ Ψ : (∀ v1 v2, Φ v1 v2 ⊢ Ψ v1 v2) → wp2 s E e1 e2 Φ ⊢ wp2 s E e1 e2 Ψ.
Proof.
  iIntros (HΦ) "H"; iApply (wp2_strong_mono with "H"); auto.
  iIntros (v1 v2) "?". by iApply HΦ.
Qed.
(* Lemma wp_stuck_mono s1 s2 E e1 e2 Φ : *)
(*   s1 ⊑ s2 → wp2 s1 E e1 e2 Φ ⊢ wp2 s2 E e @ s2; E {{ Φ }}. *)
(* Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed. *)
(* Lemma wp_stuck_weaken s E e Φ : *)
(*   WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}. *)
(* Proof. apply wp_stuck_mono. by destruct s. Qed. *)
(* Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}. *)
(* Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed. *)
(* Global Instance wp_mono' s E e : *)
(*   Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e). *)
(* Proof. by intros Φ Φ' ?; apply wp_mono. Qed. *)
(* Global Instance wp_flip_mono' s E e : *)
(*   Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e). *)
(* Proof. by intros Φ Φ' ?; apply wp_mono. Qed. *)

(* Lemma wp_value_fupd s E Φ e1 v1 e2 : IntoVal e1 v1 → WP2 e1 and e2 @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v. *)
(* Proof. intros <-. by apply wp_value_fupd'. Qed. *)
(* Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}. *)
(* Proof. rewrite wp_value_fupd'. auto. Qed. *)
(* Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}. *)
(* Proof. intros <-. apply wp_value'. Qed. *)

Lemma wp2_frame_l s E e1 e2 Φ R : R ∗ WP2 e1 and e2 @ s; E {{ Φ }} ⊢ WP2 e1 and e2 @ s; E {{| v1 v2, R ∗ Φ v1 v2 }}.
Proof. iIntros "[? H]". iApply (wp2_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp2_frame_r s E e1 e2 Φ R : WP2 e1 and e2 @ s; E {{ Φ }} ∗ R ⊢ WP2 e1 and e2 @ s; E {{| v1 v2, Φ v1 v2 ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp2_strong_mono with "H"); auto with iFrame. Qed.

(* (** This lemma states that if we can prove that [n] laters are used in *)
(*    the current physical step, then one can perform an n-steps fancy *)
(*    update during that physical step. The resources needed to prove the *)
(*    bound on [n] are not used up: they can be reused in the proof of *)
(*    the WP or in the proof of the n-steps fancy update. In order to *)
(*    describe this unusual resource flow, we use ordinary conjunction as *)
(*    a premise. *) *)
(* Lemma wp_step_fupdN n s E1 E2 e P Φ : *)
(*   TCEq (to_val e) None → E2 ⊆ E1 → *)
(*   (∀ σ ns κs nt, state_interp σ ns κs nt *)
(*        ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧ *)
(*   ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗ *)
(*     WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗ *)
(*   WP e @ s; E1 {{ Φ }}. *)
(* Proof. *)
(*   iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|]. *)
(*   iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP". *)
(*   iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|]. *)
(*   iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first. *)
(*   { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. } *)
(*   iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H". *)
(*   iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|]. *)
(*   by rewrite difference_empty_L (comm_L (∪)) -union_difference_L. *)
(* Qed. *)
(* Lemma wp_step_fupd s E1 E2 e P Φ : *)
(*   TCEq (to_val e) None → E2 ⊆ E1 → *)
(*   (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}. *)
(* Proof. *)
(*   iIntros (??) "HR H". *)
(*   iApply (wp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit. *)
(*   - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|]. *)
(*     auto with lia. *)
(*   - iFrame "H". iMod "HR" as "$". auto. *)
(* Qed. *)

(* Lemma wp_frame_step_l s E1 E2 e Φ R : *)
(*   TCEq (to_val e) None → E2 ⊆ E1 → *)
(*   (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}. *)
(* Proof. *)
(*   iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done. *)
(*   iApply (wp_mono with "Hwp"). by iIntros (?) "$$". *)
(* Qed. *)
(* Lemma wp_frame_step_r s E1 E2 e Φ R : *)
(*   TCEq (to_val e) None → E2 ⊆ E1 → *)
(*   WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}. *)
(* Proof. *)
(*   rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R). *)
(*   apply wp_frame_step_l. *)
(* Qed. *)
(* Lemma wp_frame_step_l' s E e Φ R : *)
(*   TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}. *)
(* Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed. *)
(* Lemma wp_frame_step_r' s E e Φ R : *)
(*   TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}. *)
(* Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed. *)

Lemma wp_wand s E e1 e2 Φ Ψ :
  WP2 e1 and e2 @ s; E {{ Φ }} -∗ (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) -∗ WP2 e1 and e2 @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp2_strong_mono with "Hwp"); auto.
  iIntros (? ?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e1 e2 Φ Ψ :
  (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) ∗ WP2 e1 and e2 @ s; E {{ Φ }} ⊢ WP2 e1 and e2 @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e1 e2 Φ Ψ :
  WP2 e1 and e2 @ s; E {{ Φ }} ∗ (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) ⊢ WP2 e1 and e2 @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e1 e2 Φ R :
  R -∗ WP2 e1 and e2 @ s; E {{| v1 v2 , R -∗ Φ v1 v2 }} -∗ WP2 e1 and e2 @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v1 v2) "HΦ". by iApply "HΦ".
Qed.
End wp.

(** Proofmode class instances *)
(* Section proofmode_classes. *)
(*   Context `{!irisGS Λ Σ}. *)
(*   Implicit Types P Q : iProp Σ. *)
(*   Implicit Types Φ : val Λ → iProp Σ. *)
(*   Implicit Types v : val Λ. *)
(*   Implicit Types e : expr Λ. *)

(*   Global Instance frame_wp p s E e R Φ Ψ : *)
(*     (∀ v, Frame p R (Φ v) (Ψ v)) → *)
(*     Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2. *)
(*   Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed. *)

(*   Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}). *)
(*   Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed. *)

(*   Global Instance elim_modal_bupd_wp p s E e P Φ : *)
(*     ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     by rewrite /ElimModal intuitionistically_if_elim *)
(*       (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp. *)
(*   Qed. *)

(*   Global Instance elim_modal_fupd_wp p s E e P Φ : *)
(*     ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     by rewrite /ElimModal intuitionistically_if_elim *)
(*       fupd_frame_r wand_elim_r fupd_wp. *)
(*   Qed. *)

(*   Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ : *)
(*     ElimModal (Atomic (stuckness_to_atomicity s) e) p false *)
(*             (|={E1,E2}=> P) P *)
(*             (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100. *)
(*   Proof. *)
(*     intros ?. by rewrite intuitionistically_if_elim *)
(*       fupd_frame_r wand_elim_r wp_atomic. *)
(*   Qed. *)

(*   Global Instance add_modal_fupd_wp s E e P Φ : *)
(*     AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}). *)
(*   Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed. *)

(*   Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ : *)
(*     ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e) *)
(*             (fupd E1 E2) (fupd E2 E1) *)
(*             α β γ (WP e @ s; E1 {{ Φ }}) *)
(*             (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100. *)
(*   Proof. *)
(*     iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
(*     iApply (wp_wand with "(Hinner Hα)"). *)
(*     iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
(*   Qed. *)

(*   Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ : *)
(*     ElimAcc (X:=X) True (fupd E E) (fupd E E) *)
(*             α β γ (WP e @ s; E {{ Φ }}) *)
(*             (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
(*   Proof. *)
(*     iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
(*     iApply wp_fupd. *)
(*     iApply (wp_wand with "(Hinner Hα)"). *)
(*     iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
(*   Qed. *)
(* End proofmode_classes. *)
