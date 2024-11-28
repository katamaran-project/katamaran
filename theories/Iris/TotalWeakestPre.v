(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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

From Equations Require Import
     Equations Signature.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     program_logic.adequacy
     program_logic.total_weakestpre
     proofmode.tactics.

From Katamaran Require Import
     Prelude
     Sep.Logic
     Semantics
     Iris.Model.

Require Import Coq.Program.Equality.

Import ctx.notations.
Import env.notations.
Set Implicit Arguments.

Section TransparentObligations.
  Local Set Transparent Obligations.
  (* Derive NoConfusion for SomeReg. *)
  (* Derive NoConfusion for SomeVal. *)
  Derive NoConfusion for iris.algebra.excl.excl.
End TransparentObligations.

(* TODO: Split up IrisResources, so that we can have seperate WP and TWP using the same resources (sailgs etc) *)
Module Type IrisResources
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B).
  Class sailGS Σ := SailGS { (* resources for the implementation side *)
                       sailGS_invGS : invGS Σ; (* for fancy updates, invariants... *)
                       sailGS_sailRegGS : sailRegGS Σ;

                       (* ghost variable for tracking state of memory cells *)
                       sailGS_memGS : memGS Σ
                     }.
  #[export] Existing Instance sailGS_invGS.
  #[export] Existing Instance sailGS_sailRegGS.

  (* We declare the memGS field as a class so that we can define the
     [sailGS_memGS] field as an instance as well. Currently, the [Existing
     Class] command does not support specifying a locality
     (local/export/global), so it is not clear what the scope of this command
     is. Because [memGS] will be inline on module functor applications, the
     [sailGS_memGS] instance will refer to the user-provided class instead of
     the [memGS] field. *)
  Existing Class memGS.
  #[export] Existing Instance sailGS_memGS.

  #[export] Instance sailGS_irisGS {Γ τ} `{sailGS Σ} : irisGS (microsail_lang Γ τ) Σ := {
    iris_invGS := sailGS_invGS;
    state_interp σ ns κs nt := (regs_inv σ.1 ∗ mem_inv σ.2)%I;
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
                                                                                }.
  Global Opaque iris_invGS.

  Definition semTWP {Σ} `{sG : sailGS Σ} [Γ τ] (s : Stm Γ τ)
    (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) : iProp Σ :=
    WP {| conf_stm := s; conf_store := δ |} ?[{ v, Q (valconf_val v) (valconf_store v) }].
  Global Arguments semTWP {Σ} {sG} [Γ] [τ] s%exp Q%I δ.

  Ltac fold_semTWP :=
    first
      [ progress
          change_no_check
          (twp MaybeStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              (fun v => ?Q (valconf_val v) (valconf_store v)))
        with (semTWP s Q δ)
      | progress
          change_no_check
          (twp MaybeStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              ?Q)
        with (semTWP s (fun v δ' => Q (MkValConf _ v δ')) δ);
        try (progress (cbn [valconf_val valconf_store]))
      ].

  Section TotalWeakestPre.

    Context `{sG : sailGS Σ}.

    Lemma semTWP_unfold [Γ τ] (s : Stm Γ τ)
      (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      semTWP s Q δ ⊣⊢
        match stm_to_val s with
        | Some v => |={⊤}=> Q v δ
        | None   => ∀ (γ1 : RegStore) (μ1 : Memory),
                       regs_inv γ1 ∗ mem_inv μ1 ={⊤,∅}=∗
                       (∀ (s2 : Stm Γ τ) (δ2 : CStore Γ) (γ2 : RegStore) (μ2 : Memory),
                          ⌜⟨ γ1, μ1, δ , s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩⌝ ={∅}=∗
                          |={∅,⊤}=> (regs_inv γ2 ∗ mem_inv μ2) ∗ semTWP s2 Q δ2)
        end.
    Proof.
      unfold semTWP. rewrite twp_unfold. unfold twp_pre. cbn.
      destruct stm_to_val; cbn; [easy|].
      apply bi.entails_anti_sym; iIntros "HYP".
      - iIntros (γ μ) "state_inv".
        iSpecialize ("HYP" $! (γ,μ) O nil O with "state_inv").
        iMod "HYP" as "[_ HYP]". iModIntro.
        iIntros (s' δ' γ' μ' step).
        iSpecialize ("HYP" $! nil (MkConf s' δ') (γ',μ') nil
                       (mk_prim_step (MkConf _ _) step)). iModIntro.
        iMod "HYP" as "HYP". iModIntro. iDestruct "HYP" as "(_ & $ & $ & _)".
      - iIntros (σ _ κ _) "state_inv".
        iSpecialize ("HYP" $! (fst σ) (snd σ) with "state_inv").
        iMod "HYP". iModIntro. iSplitR; [easy|].
        iIntros (κ' c' σ' efs [γ γ' μ μ' δ' s']).
        iSpecialize ("HYP" $! s' δ' γ' μ' with "[]"); first eauto.
        iMod "HYP". iMod "HYP". iModIntro.
        iDestruct "HYP" as "($ & $)". now cbn.
    Qed.

    Lemma semTWP_unfold_nolc [Γ τ] (s : Stm Γ τ)
      (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
        match stm_to_val s with
        | Some v => |={⊤}=> Q v δ
        | None   => ∀ (γ1 : RegStore) (μ1 : Memory),
                       regs_inv γ1 ∗ mem_inv μ1 ={⊤,∅}=∗
                       (∀ (s2 : Stm Γ τ) (δ2 : CStore Γ) (γ2 : RegStore) (μ2 : Memory),
                          ⌜⟨ γ1, μ1, δ , s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩⌝ ={∅}=∗
                          |={∅,⊤}=> (regs_inv γ2 ∗ mem_inv μ2) ∗ semTWP s2 Q δ2)
        end ⊢ semTWP s Q δ.
    Proof.
      rewrite semTWP_unfold.
      destruct (stm_to_val s); first easy.
      iIntros "HYP" (γ1 μ1) "Hres".
      iMod ("HYP" with "Hres") as "HYP".
      iIntros "!>" (s2 δ2 γ2 μ2 Hstep).
      iMod ("HYP" $! _ _ _ _ Hstep) as "HYP".
      repeat iModIntro. iMod "HYP".
      now iModIntro.
    Qed.

    Lemma semTWP_mono [Γ τ] (s : Stm Γ τ) (P Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      ⊢ (semTWP s P δ -∗ (∀ v δ, P v δ -∗ Q v δ) -∗ semTWP s Q δ).
    Proof.
      unfold semTWP. iIntros "WP PQ".
      iApply (twp_strong_mono with "WP"); auto.
      iIntros ([v δΓ]) "X"; cbn.
      by iApply "PQ".
    Qed.
    Lemma semTWP_val {Γ τ} (v : Val τ) (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      semTWP (stm_val τ v) Q δ ⊣⊢ |={⊤}=> Q v δ.
    Proof. rewrite semTWP_unfold. reflexivity. Qed.

    Lemma semTWP_fail {Γ τ s} (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      semTWP (stm_fail _ s) Q δ ⊣⊢ True.
    Proof.
      apply bi.entails_anti_sym; [auto|]. rewrite <-semTWP_unfold_nolc. cbn.
      iIntros "_" (γ μ) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step).
    Qed.

    Lemma semTWP_exp {Γ τ} (e : Exp Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          Q (eval e δ) δ -∗ semTWP (stm_exp e) Q δ.
    Proof.
      iIntros (Q δ1) "P". rewrite <-semTWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "state_inv". by iApply semTWP_val.
    Qed.

    Lemma semTWP_block {Γ τ Δ} (δΔ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semTWP s (fun v δ1 => Q v (env.drop Δ δ1)) (δ ►► δΔ) -∗
          semTWP (stm_block δΔ s) Q δ.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ Q (valconf_val v) (env.drop Δ (valconf_store v)))%I as "(%Φ & HΦ)".
      { iExists (λ v, Q (valconf_val v) (env.drop Δ (valconf_store v))). auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember ({| conf_stm := s; conf_store := δ ►► δΔ |} : expr (microsail_lang _ τ)) as e eqn:He.
      iRevert (s δ δΔ HE He) "HΦ". iRevert (e E Φ) "H".
      iApply twp_ind; first solve_proper.
      iIntros "!>" (e E Φ) "IH". iIntros (s δ δΔ -> ->) "#HΦ".
      fold_semTWP. rewrite semTWP_unfold /twp_pre; cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step); destruct (smallinvstep step); cbn.
      - rewrite !semTWP_val.
        iModIntro. iMod "Hclose" as "_". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH". cbn.
        rewrite env.drop_cat. by iFrame.
      - rewrite !semTWP_fail. by iFrame.
      - rewrite (stm_val_stuck H). cbn.
        iSpecialize ("IH" $! (γ1 , μ1) O nil O with "state_inv").
        iMod "Hclose" as "_". iMod "IH" as "(_ & IH)".
        iSpecialize ("IH" $! _ _ _ _ with "[]"); first easy.
        iModIntro. iMod "IH". iModIntro.
        iDestruct "IH" as "(_ & $ & [IH _] & _)".
        repeat fold_semTWP.
        iApply "IH"; done.
    Qed.

    Lemma semTWP_call_frame {Γ τ Δ} (δΔ : CStore Δ) (s : Stm Δ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semTWP s (fun v _ => Q v δ) δΔ -∗
          semTWP (stm_call_frame δΔ s) Q δ.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ Q (valconf_val v) δ)%I as "(%Φ & HΦ)".
      { iExists (λ v, Q (valconf_val v) δ). auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember ({| conf_stm := s; conf_store := δΔ |} : expr (microsail_lang _ τ)) as e eqn:He.
      iRevert (s δ δΔ HE He) "HΦ". iRevert (e E Φ) "H".
      iApply twp_ind; first solve_proper.
      iIntros "!>" (e E Φ) "IH". iIntros (s δ δΔ -> ->) "#HΦ".
      fold_semTWP. rewrite semTWP_unfold /twp_pre; cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      - rewrite !semTWP_val. iModIntro. iMod "Hclose". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH". by iFrame.
      - rewrite !semTWP_fail. by iFrame.
      - rewrite (stm_val_stuck H); cbn.
        iSpecialize ("IH" $! (γ1, μ1) O nil O with "state_inv").
        iMod "Hclose". iMod "IH" as "(_ & IH)". iModIntro.
        iSpecialize ("IH" $! _ _ _ _ with "[]"); first easy.
        iMod "IH". iModIntro. iDestruct "IH" as "(_ & $ & [IH _] & _)".
        fold_semTWP. by iApply "IH".
    Qed.

    Lemma semTWP_call_inline {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
          semTWP (FunDef f) (fun vτ _ => Q vτ δΓ) (evals es δΓ) -∗
          semTWP (stm_call f es) Q δΓ.
    Proof.
      iIntros (Q δΓ) "wpbody". rewrite <-(semTWP_unfold_nolc (stm_call f es)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "state_inv". by iApply semTWP_call_frame.
    Qed.

    Lemma semTWP_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ → Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semTWP s (fun v => semTWP (k v) Q) δ -∗ semTWP (stm_bind s k) Q δ.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ WP {| conf_stm := k (valconf_val v); conf_store := valconf_store v |}
                                 ?[{ v', Q (valconf_val v') (valconf_store v') }])%I as "(%Φ & HΦ)".
      { iExists (λ v, WP {| conf_stm := k (valconf_val v); conf_store := valconf_store v |}
                        ?[{ v', Q (valconf_val v') (valconf_store v') }])%I. auto. }
      iPoseProof (twp_wand _ _ _ _ _ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember ({| conf_stm := s; conf_store := δ |}) as e eqn:He.
      iRevert (s δ He HE) "HΦ". iRevert (e E Φ) "H".
      iApply twp_ind; first solve_proper.
      iIntros "!>" (e E Φ) "IH". iIntros (s δ -> ->) "#HΦ".
      repeat fold_semTWP.
      rewrite semTWP_unfold /twp_pre; cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      - iModIntro. iMod "Hclose". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH".
        by iFrame.
      - rewrite !semTWP_fail. by iFrame.
      - rewrite (stm_val_stuck H). cbn.
        iSpecialize ("IH" $! (γ1 , μ1) O nil O with "state_inv").
        iMod "Hclose". iMod "IH" as "(_ & IH)".
        iSpecialize ("IH" $! _ _ _ _ with "[]"); first easy.
        iModIntro. iMod "IH". iModIntro.
        iDestruct "IH" as "(_ & $ & [IH _] & _)".
        repeat fold_semTWP.
        by iApply "IH".
    Qed.

    Lemma semTWP_let {Γ τ x σ} (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semTWP s (fun v1 δ1 => semTWP k (fun v2 δ2 => Q v2 (env.tail δ2)) δ1.[x∷σ ↦ v1]) δ -∗
          semTWP (let: x ∷ σ := s in k) Q δ.
    Proof.
      iIntros (Q δΓ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_let x σ s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semTWP_bind. iApply (semTWP_mono with "WPs"). iIntros (v δ) "wpk".
      iApply (semTWP_block [env].[_∷_ ↦ v]). iApply (semTWP_mono with "wpk").
      clear. iIntros (? δ) "HQ". by destruct (env.view δ).
    Qed.

    Lemma semTWP_seq {Γ τ σ} (s : Stm Γ σ) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semTWP s (fun _ => semTWP k Q) δ -∗ semTWP (s;;k) Q δ.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_seq s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      by iApply semTWP_bind.
    Qed.

    Lemma semTWP_assertk {Γ τ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          (⌜eval e1 δ = true⌝ → semTWP k Q δ) -∗ semTWP (stm_assertk e1 e2 k) Q δ.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_assertk e1 e2 k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      destruct eval; [by iApply "WPs"|by iApply semTWP_fail].
    Qed.

    Lemma semTWP_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg v -∗ Q v δ)) -∗
          semTWP (stm_read_register reg) Q δ.
    Proof.
      iIntros (Q δ) "[% [Hreg HP]]". rewrite <-semTWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro.
      iDestruct (@reg_valid with "Hregs Hreg") as %->.
      iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semTWP_val.
    Qed.

    Lemma semTWP_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg (eval e δ) -∗ Q (eval e δ) δ)) -∗
          semTWP (stm_write_register reg e) Q δ.
    Proof.
      iIntros (Q δ) "[% [Hreg HP]]". rewrite <-semTWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iMod (reg_update γ1 reg v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro.
      iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semTWP_val.
    Qed.

    Lemma semTWP_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semTWP s (λ (a : Val τ) (δ0 : CStore Γ), Q a (δ0 ⟪ x ↦ a ⟫)) δ -∗
          semTWP (stm_assign x s) Q δ.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ Q (valconf_val v) (valconf_store v ⟪ x ↦ (valconf_val v) ⟫))%I as "(%Φ & HΦ)".
      { iExists (λ v, Q (valconf_val v) (valconf_store v ⟪ x ↦ (valconf_val v) ⟫)). auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember ({| conf_stm := s; conf_store := δ |} : expr (microsail_lang _ τ)) as e eqn:He.
      iRevert (s δ HE He) "HΦ". iRevert (e E Φ) "H".
      iApply twp_ind; first solve_proper.
      iIntros "!>" (e E Φ) "IH". iIntros (s δ -> ->) "#HΦ".
      fold_semTWP. rewrite semTWP_unfold /twp_pre; cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      - rewrite !semTWP_val.
        iModIntro. iMod "Hclose". iMod "IH". iModIntro.
        iPoseProof ("HΦ" with "IH") as "IH". 
        by iFrame.
      - rewrite !semTWP_fail. by iFrame.
      - rewrite (stm_val_stuck H); cbn.
        iSpecialize ("IH" $! (γ1,μ1) O nil O with "state_inv").
        iMod "Hclose". iMod "IH" as "(_ & IH)".
        iSpecialize ("IH" $! _ _ _ _ with "[]"); first easy.
        iModIntro. iMod "IH" as "(_ & $ & [IH _] & _)". iModIntro.
        by iApply "IH".
    Qed.

    Lemma semTWP_pattern_match {Γ τ σ} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
      semTWP s
        (fun vσ δ1 =>
           let (pc,δpc) := pattern_match_val pat vσ in
           semTWP (rhs pc)
             (fun vτ δ2 => Q vτ (env.drop (PatternCaseCtx pc) δ2))
             (δ1 ►► δpc)) δ -∗
      semTWP (stm_pattern_match s pat rhs) Q δ.
    Proof.
      iIntros (Q δΓ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_pattern_match s pat rhs)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semTWP_bind. iApply (semTWP_mono with "WPs"). iIntros (v δ) "WPrhs".
      destruct pattern_match_val as [pc δpc]. by iApply (semTWP_block δpc).
    Qed.

    Lemma semTWP_foreign {Γ Δ τ} {f : 𝑭𝑿 Δ τ} {es : NamedEnv (Exp Γ) Δ} {Q δ} :
      ⊢ (∀ γ μ,
            (regs_inv γ ∗ mem_inv μ)
            ={⊤,∅}=∗
        (∀ res γ' μ' ,
          ⌜ ForeignCall f (evals es δ) res γ γ' μ μ' ⌝
           -∗
           |={∅,⊤}=> (regs_inv γ' ∗ mem_inv μ') ∗
                      semTWP (match res with inr v => stm_val _ v
                                       | inl s => stm_fail _ s
                             end) Q δ)) -∗
        semTWP (stm_foreign f es) Q δ.
    Proof.
      iIntros "H". rewrite <-semTWP_unfold_nolc. cbn. iIntros (γ1 μ1) "state_inv".
      iMod ("H" $! γ1 μ1 with "[$]") as "H". iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn. by iApply "H".
    Qed.

    Lemma semTWP_debugk {Γ τ} (s : Stm Γ τ) :
      ⊢ ∀ Q δ, semTWP s Q δ -∗ semTWP (stm_debugk s) Q δ.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_debugk s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. now iFrame "state_inv".
    Qed.

    Lemma semTWP_lemmak {Γ τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (s : Stm Γ τ) :
      ⊢ ∀ Q δ, semTWP s Q δ -∗ semTWP (stm_lemmak l es s) Q δ.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_lemmak l es s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. now iFrame "state_inv".
    Qed.

  End TotalWeakestPre.

  Module twptactics.
    Ltac kEval :=
      match goal with
      | |- environments.envs_entails ?ctx (semTWP ?s ?post ?store) =>
          let s' := eval compute - [Val] in s in
          let store' := eval compute - [Val] in store in
          change_no_check (environments.envs_entails ctx (semTWP s' post store'))
      end.

    Ltac kStep :=
      match goal with
      | |- environments.envs_entails ?ctx (semTWP ?stm ?post ?store) =>
          match stm with
          | stm_val ?τ ?v => iApply semTWP_val
          | stm_exp ?e => iApply (semTWP_exp e)
          | stm_let ?x ?τ ?s1 ?s2 => iApply (semTWP_let s1 s2)
          | stm_pattern_match ?scrut ?pat ?rhs =>
              iApply (semTWP_pattern_match scrut pat rhs)
          | match ?x with _ => _ end => destruct x eqn:?
          end
      end.
  End twptactics.

End IrisResources.

(* TODO: IrisBase should end with <+ IrisResources <+ IrisWP <+ IrisTWP *)
Module Type IrisBase (B : Base) (PROG : Program B) (SEM : Semantics B PROG) :=
  IrisPrelims B PROG SEM <+ IrisParameters B <+ IrisResources B PROG SEM.
