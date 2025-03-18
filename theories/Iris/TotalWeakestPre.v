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
     Semantics
     Iris.Resources.

Require Import Coq.Program.Equality.

Import ctx.notations.
Import env.notations.
Set Implicit Arguments.

Module Type IrisTotalWeakestPre
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B)
  (Import IR   : IrisResources B PROG SEM IPre IP).

  Definition semTWP {Σ} `{sG : sailGS Σ} [Γ τ] (δ : CStore Γ) (s : Stm Γ τ)
    (Q : Post Γ τ) : iProp Σ :=
    WP (MkConf s δ) [{ v, Q (valconf_val v) (valconf_store v) }].
  Global Arguments semTWP {Σ} {sG} [Γ] [τ] δ s%_exp Q%_I.

  Ltac fold_semTWP :=
    first
      [ progress
          change_no_check
          (twp NotStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              (fun v => ?Q (valconf_val v) (valconf_store v)))
        with (semTWP δ s Q)
      | progress
          change_no_check
          (twp NotStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              ?Q)
        with (semTWP δ s (fun v δ' => Q (MkValConf _ v δ')));
        try (progress (cbn [valconf_val valconf_store]))
      ].

  Section TotalWeakestPre.

    Context `{sG : sailGS Σ}.

    Lemma semTWP_unfold [Γ τ] (s : Stm Γ τ)
      (Q : Post Γ τ) (δ : CStore Γ) :
      semTWP δ s Q ⊣⊢
        match stm_to_val s with
        | Some v => |={⊤}=> Q v δ
        | None   => ∀ (γ1 : RegStore) (μ1 : Memory),
                       regs_inv γ1 ∗ mem_inv μ1 ={⊤,∅}=∗
                       (∀ (s2 : Stm Γ τ) (δ2 : CStore Γ) (γ2 : RegStore) (μ2 : Memory),
                          ⌜⟨ γ1, μ1, δ , s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩⌝ ={∅}=∗
                          |={∅,⊤}=> (regs_inv γ2 ∗ mem_inv μ2) ∗ semTWP δ2 s2 Q)
        end.
    Proof.
      unfold semTWP. rewrite twp_unfold. unfold twp_pre. cbn.
      destruct (stm_to_val s) eqn:Es; cbn; [easy|].
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
        iMod "HYP". iModIntro. iSplitR. iPureIntro. apply reducible_no_obs_not_val; auto.
        iIntros (κ' c' σ' efs [γ γ' μ μ' δ' s']).
        iSpecialize ("HYP" $! s' δ' γ' μ' with "[]"); first eauto.
        iMod "HYP". iMod "HYP". iModIntro.
        iDestruct "HYP" as "($ & $)". now cbn.
    Qed.

    Lemma semTWP_unfold_nolc [Γ τ] (s : Stm Γ τ)
      (Q : Post Γ τ) (δ : CStore Γ) :
        match stm_to_val s with
        | Some v => |={⊤}=> Q v δ
        | None   => ∀ (γ1 : RegStore) (μ1 : Memory),
                       regs_inv γ1 ∗ mem_inv μ1 ={⊤,∅}=∗
                       (∀ (s2 : Stm Γ τ) (δ2 : CStore Γ) (γ2 : RegStore) (μ2 : Memory),
                          ⌜⟨ γ1, μ1, δ , s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩⌝ ={∅}=∗
                          |={∅,⊤}=> (regs_inv γ2 ∗ mem_inv μ2) ∗ semTWP δ2 s2 Q)
        end ⊢ semTWP δ s Q.
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

    Lemma semTWP_mono [Γ τ] (s : Stm Γ τ) (P Q : Post Γ τ) (δ : CStore Γ) :
      ⊢ (semTWP δ s P -∗ (∀ v δ, P v δ -∗ Q v δ) -∗ semTWP δ s Q).
    Proof.
      unfold semTWP. iIntros "WP PQ".
      iApply (twp_strong_mono with "WP"); auto.
      iIntros ([v δΓ]) "X"; cbn.
      by iApply "PQ".
    Qed.
    Lemma semTWP_val {Γ τ} (v : Val τ) (Q : Post Γ τ) (δ : CStore Γ) :
      semTWP δ (stm_val τ v) Q ⊣⊢ |={⊤}=> Q (inl v) δ.
    Proof. rewrite semTWP_unfold. reflexivity. Qed.

    Lemma semTWP_fail {Γ τ s} (Q : Post Γ τ) (δ : CStore Γ) :
      semTWP δ (stm_fail _ s) Q ⊣⊢ |={⊤}=> Q (inr s) δ.
    Proof. rewrite semTWP_unfold. reflexivity. Qed.

    Lemma semTWP_exp {Γ τ} (e : Exp Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          Q (inl (eval e δ)) δ -∗ semTWP δ (stm_exp e) Q.
    Proof.
      iIntros (Q δ1) "P". rewrite <-semTWP_unfold_nolc. cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "state_inv". by iApply semTWP_val.
    Qed.

    Lemma semTWP_block {Γ τ Δ} (δΔ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semTWP (δ ►► δΔ) s (fun v δ1 => Q v (env.drop Δ δ1)) -∗
          semTWP δ (stm_block δΔ s) Q.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ Q (valconf_val v) (env.drop Δ (valconf_store v)))%I as "(%Φ & HΦ)".
      { iExists (λ v, Q (valconf_val v) (env.drop Δ (valconf_store v))). auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember (MkConf s (δ ►► δΔ) : expr (microsail_lang _ τ)) as e eqn:He.
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
      - rewrite !semTWP_fail.
        iModIntro. iMod "Hclose" as "_". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH". cbn.
        rewrite env.drop_cat. by iFrame.
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
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semTWP δΔ s (fun v _ => Q v δ) -∗
          semTWP δ (stm_call_frame δΔ s) Q.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ Q (valconf_val v) δ)%I as "(%Φ & HΦ)".
      { iExists (λ v, Q (valconf_val v) δ). auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember (MkConf s δΔ : expr (microsail_lang _ τ)) as e eqn:He.
      iRevert (s δ δΔ HE He) "HΦ". iRevert (e E Φ) "H".
      iApply twp_ind; first solve_proper.
      iIntros "!>" (e E Φ) "IH". iIntros (s δ δΔ -> ->) "#HΦ".
      fold_semTWP. rewrite semTWP_unfold /twp_pre; cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      - rewrite !semTWP_val. iModIntro. iMod "Hclose". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH". by iFrame.
      - rewrite !semTWP_fail. iModIntro. iMod "Hclose". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH". by iFrame.
      - rewrite (stm_val_stuck H); cbn.
        iSpecialize ("IH" $! (γ1, μ1) O nil O with "state_inv").
        iMod "Hclose". iMod "IH" as "(_ & IH)". iModIntro.
        iSpecialize ("IH" $! _ _ _ _ with "[]"); first easy.
        iMod "IH". iModIntro. iDestruct "IH" as "(_ & $ & [IH _] & _)".
        fold_semTWP. by iApply "IH".
    Qed.

    Lemma semTWP_call_inline {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⊢ ∀ (Q : Post Γ τ) (δΓ : CStore Γ),
          semTWP (evals es δΓ) (FunDef f) (fun vτ _ => Q vτ δΓ) -∗
          semTWP δΓ (stm_call f es) Q.
    Proof.
      iIntros (Q δΓ) "wpbody". rewrite <-(semTWP_unfold_nolc (stm_call f es)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "state_inv". by iApply semTWP_call_frame.
    Qed.

    Lemma semTWP_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ → Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semTWP δ s (fun v δ => semTWP δ (lift_cnt k v) Q) -∗ semTWP δ (stm_bind s k) Q.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ WP (MkConf (lift_cnt k (valconf_val v)) (valconf_store v))
                                 [{ v', Q (valconf_val v') (valconf_store v') }])%I as "(%Φ & HΦ)".
      { iExists (λ v, WP (MkConf (lift_cnt k (valconf_val v)) (valconf_store v))
                        [{ v', Q (valconf_val v') (valconf_store v') }])%I. auto. }
      iPoseProof (twp_wand _ _ _ _ _ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember (MkConf s δ) as e eqn:He.
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
      - iModIntro. iMod "Hclose". iMod "IH".
        iPoseProof ("HΦ" with "IH") as "IH".
        by iFrame.
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
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semTWP δ s (fun v1 δ1 => match v1 with
                                | inl v1 => semTWP δ1.[x∷σ ↦ v1] k (fun v2 δ2 => Q v2 (env.tail δ2))
                                | inr m1 => semTWP δ1 (of_ival (inr m1)) Q
                                end) -∗
          semTWP δ (let: x ∷ σ := s in k) Q.
    Proof.
      iIntros (Q δΓ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_let x σ s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semTWP_bind. iApply (semTWP_mono with "WPs"). iIntros ([v|m] δ) "wpk".
      - iApply (semTWP_block [env].[_∷_ ↦ v]). iApply (semTWP_mono with "wpk").
        clear. iIntros (? δ) "HQ". by destruct (env.view δ).
      - now simpl.
    Qed.

    Lemma semTWP_seq {Γ τ σ} (s : Stm Γ σ) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semTWP δ s (λ v δ, match v with
                          | inl _ => semTWP δ k Q
                          | inr m => semTWP δ (of_ival (inr m)) Q
                          end) -∗ semTWP δ (s;;k) Q.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_seq s k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semTWP_bind. iApply (semTWP_mono with "WPs"). iIntros ([v|m] ?).
      - simpl. iIntros "$".
      - simpl. now iIntros "H".
    Qed.

    Lemma semTWP_assertk {Γ τ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          (⌜eval e1 δ = true⌝ → semTWP δ k Q) -∗
          (⌜eval e1 δ = false⌝ → semTWP δ (fail (eval e2 δ)) Q) -∗
          semTWP δ (stm_assertk e1 e2 k) Q.
    Proof.
      iIntros (Q δ) "WPtrue WPfalse". rewrite <-(semTWP_unfold_nolc (stm_assertk e1 e2 k)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      destruct eval; [by iApply "WPtrue"|by iApply "WPfalse"].
    Qed.

    Lemma semTWP_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg v -∗ Q (inl v) δ)) -∗
          semTWP δ (stm_read_register reg) Q.
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
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg (eval e δ) -∗ Q (inl (eval e δ)) δ)) -∗
          semTWP δ (stm_write_register reg e) Q.
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
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
          semTWP δ s (λ (a : IVal τ) (δ0 : CStore Γ), match a with
                                                   | inl a => Q (inl a) (δ0 ⟪ x ↦ a ⟫)
                                                   | inr m => Q (inr m) δ0
                                                   end) -∗
          semTWP δ (stm_assign x s) Q.
    Proof.
      iIntros (Q δ) "H". rewrite /semTWP.
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ 
            match valconf_val v with
            | inl a => Q (inl a) (valconf_store v ⟪ x ↦ a ⟫)
            | inr m => Q (inr m) (valconf_store v)
            end)%I as "(%Φ & HΦ)".
      { iExists (λ v, match valconf_val v with
            | inl a => Q (inl a) (valconf_store v ⟪ x ↦ a ⟫)
            | inr m => Q (inr m) (valconf_store v)
            end)%I. auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "H [HΦ]") as "H".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember (MkConf s δ : expr (microsail_lang _ τ)) as e eqn:He.
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
      - rewrite !semTWP_fail.
        iModIntro. iMod "Hclose". iMod "IH". iModIntro.
        iPoseProof ("HΦ" with "IH") as "IH". 
        by iFrame.
      - rewrite (stm_val_stuck H); cbn.
        iSpecialize ("IH" $! (γ1,μ1) O nil O with "state_inv").
        iMod "Hclose". iMod "IH" as "(_ & IH)".
        iSpecialize ("IH" $! _ _ _ _ with "[]"); first easy.
        iModIntro. iMod "IH" as "(_ & $ & [IH _] & _)". iModIntro.
        by iApply "IH".
    Qed.

    Lemma semTWP_pattern_match {Γ τ σ} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Post Γ τ) (δ : CStore Γ),
      semTWP δ s
        (fun vσ δ1 =>
           match vσ with
           | inl vσ =>
               let (pc,δpc) := pattern_match_val pat vσ in
               semTWP (δ1 ►► δpc) (rhs pc)
                 (fun vτ δ2 =>
                    match vτ with
                    | inl vτ => Q (inl vτ) (env.drop (PatternCaseCtx pc) δ2)
                    | inr m  => Q (inr m) (env.drop (PatternCaseCtx pc) δ2)
                    end)
           | inr m => |={⊤}=> Q (inr m) δ1
           end) -∗
      semTWP δ (stm_pattern_match s pat rhs) Q.
    Proof.
      iIntros (Q δΓ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_pattern_match s pat rhs)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semTWP_bind. iApply (semTWP_mono with "WPs"). iIntros ([v|m] δ) "WPrhs".
      - simpl. destruct pattern_match_val as [pc δpc]. iApply (semTWP_block δpc).
        iApply (semTWP_mono with "WPrhs"). iIntros ([v'|m'] ?) "H"; simpl; auto.
      - simpl. now rewrite semTWP_fail.
    Qed.

    Lemma semTWP_foreign {Γ Δ τ} {f : 𝑭𝑿 Δ τ} {es : NamedEnv (Exp Γ) Δ} {Q δ} :
      ⊢ (∀ γ μ,
            (regs_inv γ ∗ mem_inv μ)
            ={⊤,∅}=∗
        (∀ res γ' μ' ,
          ⌜ ForeignCall f (evals es δ) res γ γ' μ μ' ⌝
           -∗
           |={∅,⊤}=> (regs_inv γ' ∗ mem_inv μ') ∗
                      semTWP δ (match res with inr v => stm_val _ v
                                       | inl s => stm_fail _ s
                             end) Q)) -∗
        semTWP δ (stm_foreign f es) Q.
    Proof.
      iIntros "H". rewrite <-semTWP_unfold_nolc. cbn. iIntros (γ1 μ1) "state_inv".
      iMod ("H" $! γ1 μ1 with "[$]") as "H". iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn. by iApply "H".
    Qed.

    Lemma semTWP_debugk {Γ τ} (s : Stm Γ τ) :
      ⊢ ∀ Q δ, semTWP δ s Q -∗ semTWP δ (stm_debugk s) Q.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_debugk s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. now iFrame "state_inv".
    Qed.

    Lemma semTWP_lemmak {Γ τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (s : Stm Γ τ) :
      ⊢ ∀ Q δ, semTWP δ s Q -∗ semTWP δ (stm_lemmak l es s) Q.
    Proof.
      iIntros (Q δ) "WPs". rewrite <-(semTWP_unfold_nolc (stm_lemmak l es s)). cbn.
      iIntros (γ1 μ1) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
      iModIntro. iMod "Hclose" as "_". iModIntro. now iFrame "state_inv".
    Qed.

    Import SmallStepNotations.

    Lemma semTWP_Steps {Γ τ} {s1 : Stm Γ τ} {Q δ1} :
      ∀ {γ1 : RegStore} {μ1 : Memory},
        regs_inv γ1 ∗ mem_inv μ1 -∗
        semTWP δ1 s1 Q ={⊤}=∗
        ∃ γ2 μ2 δ2 s2 v, ⌜⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s2 ⟩ ⌝
                        ∗ ⌜stm_to_val s2 = Some v⌝
                        ∗ regs_inv γ2 ∗ mem_inv μ2 ∗ Q v δ2.
    Proof.
      iIntros (γ1 μ1) "Hres HTWP".
      iAssert (∃ Φ, ∀ v, Φ v ∗-∗ Q (valconf_val v) (valconf_store v))%I as "(%Φ & HΦ)".
      { iExists (λ v, Q (valconf_val v) (valconf_store v)). auto. }
      iPoseProof (twp_wand _ _ _ _ Φ with "HTWP [HΦ]") as "HTWP".
      { iIntros (v) "HQ". by iApply ("HΦ" with "HQ"). }
      remember (⊤ : coPset) as E eqn:HE.
      remember (MkConf s1 δ1 : expr (microsail_lang Γ τ)) as e eqn:He.
      iRevert (s1 δ1 γ1 μ1 HE He) "Hres HΦ". iRevert (e E Φ) "HTWP".
      iApply twp_ind; first solve_proper.
      iIntros "!>" (e E Φ) "IH". iIntros (s1 δ1 γ1 μ1 HE He) "Hres #HΦ".
      rewrite /twp_pre. cbn. destruct (to_val e) as [[[v|m] δ]|] eqn:Ee.
      - iMod "IH". iModIntro.
        iExists γ1, μ1, δ1, (stm_val _ v), (inl v). iDestruct "Hres" as "($ & $)".
        rewrite He in Ee. destruct s1; try discriminate; inversion Ee; subst.
        iSplitR. iPureIntro. apply step_refl. iSplitR. iPureIntro. auto.
        iApply ("HΦ" with "IH").
      - iMod "IH". iModIntro.
        iExists γ1, μ1, δ1, (stm_fail _ m), (inr m). iDestruct "Hres" as "($ & $)".
        rewrite He in Ee. destruct s1; try discriminate; inversion Ee; subst.
        iSplitR. iPureIntro. apply step_refl. iSplitR. iPureIntro. auto.
        iApply ("HΦ" with "IH").
      - iSpecialize ("IH" $! (γ1, μ1) O nil O with "Hres").
        pose proof (progress s1) as [H|H].
        + destruct s1; cbn in H; try discriminate; try contradiction;
            rewrite He in Ee; cbn in Ee; inversion Ee.
        + iMod "IH" as "(_ & IH)".
          destruct (H γ1 μ1 δ1) as (γ2 & μ2 & δ2 & s2 & Hs).
          iSpecialize ("IH" $! nil (MkConf s2 δ2) _ nil with "[]").
          { iPureIntro. constructor. rewrite He; simpl. apply Hs. }
          iMod "IH" as "(_ & Hres & [IH _] & _)".
          iMod ("IH" with "[] [] Hres HΦ") as "IH"; auto. iModIntro.
          iDestruct "IH" as "(%γ3 & %μ3 & %δ3 & %s3 & %v' & IH)".
          iExists γ3, μ3, δ3, s3, v'. iDestruct "IH" as "(%Hs2 & $)".
          iPureIntro. eapply Steps_trans; last apply Hs2.
          apply (step_trans Hs). apply step_refl.
    Qed.

  End TotalWeakestPre.

  Module twptactics.
    Ltac kEval :=
      match goal with
      | |- environments.envs_entails ?ctx (semTWP ?store ?s ?post) =>
          let s' := eval compute - [Val] in s in
          let store' := eval compute - [Val] in store in
          change_no_check (environments.envs_entails ctx (semTWP store' s' post))
      end.

    Ltac kStep :=
      match goal with
      | |- environments.envs_entails ?ctx (semTWP ?store ?stm ?post) =>
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

End IrisTotalWeakestPre.
