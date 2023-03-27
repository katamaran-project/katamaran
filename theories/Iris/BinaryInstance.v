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
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     base_logic.lib.fancy_updates
     base_logic.lib.gen_heap
     base_logic.lib.own
     bi.big_op
     bi.interface
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.tactics.

From Katamaran Require Import
     Iris.Model
     Iris.BinaryWp
     Iris.Instance
     Prelude
     Semantics
     Sep.Hoare
     Sep.Logic
     Signature
     SmallStep.Step
     Specification.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type IrisParameters2
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IP   : IrisPrelims B PROG SEM).
  Parameter memGpreS2 : gFunctors -> Set.
  Parameter Inline memGS2 : gFunctors -> Set.
  Parameter memΣ2 : gFunctors.
  Parameter memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ.
  Parameter mem_inv2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.
  Parameter mem_res2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.

    (* Definition mem_inv `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
    (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
    (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
    (*   )%I. *)

  Parameter mem_inv_init2 : forall `{mGS : memGpreS2 Σ} (μ1 μ2 : Memory),
                                         ⊢ |==> ∃ mG : memGS2 Σ, (mem_inv2 (mG := mG) μ1 μ2 ∗ mem_res2 (mG := mG) μ1 μ2)%I.
End IrisParameters2.

Module Type IrisResources2
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters2 B PROG SEM IPre).
  Class sailGpreS2 Σ := SailGpreS2 { (* resources for the implementation side *)
                       sailGpresS_invGpreS2 : invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variables for tracking state of registers *)
                       reg_pre_inG2_left : inG Σ regUR;
                       reg_pre_inG2_right : inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS2 : memGpreS2 Σ
                     }.
  #[export] Existing Instance sailGpresS_invGpreS2.

  Class sailGS2 Σ := SailGS2 { (* resources for the implementation side *)
                       sailGS2_invGS : invGS Σ; (* for fancy updates, invariants... *)
                       sailGS2_sailRegGS_left : sailRegGS Σ;
                       sailGS2_sailRegGS_right : sailRegGS Σ;

                       (* ghost variable for tracking user-defined state *)
                       sailGS2_memGS : memGS2 Σ;
                     }.

  Context `{sG : sailGS2 Σ}.
  #[export] Existing Instance sailGS2_invGS.

  #[export] Program Instance sailGS2_irisGS2 {Γ τ} : irisGS2 (microsail_lang Γ τ) (microsail_lang Γ τ) Σ :=
    {|
      iris_invGS2 := sailGS2_invGS;
      state_interp2 σ1 σ2 κ := (regs_inv (srGS := sailGS2_sailRegGS_left) σ1.1 ∗ regs_inv (srGS := sailGS2_sailRegGS_right) σ2.1 ∗ @mem_inv2 _ (sailGS2_memGS) σ1.2 σ2.2)%I;
      num_laters_per_step2 := fun _ => 0
    |}.
  Next Obligation.
    iIntros (Γ τ σ1 σ2 ns) "(Hreg1 & Hreg2 & Hmem)".
    now iFrame.
  Qed.


  (* Definition binwp_pre `{!sailGS2 Σ} {Γ τ} *)
  (*   (wp : coPset -d> expr (microsail_lang Γ τ) -d> expr (microsail_lang Γ τ) -d> (val (microsail_lang Γ τ) -d> iPropO Σ) -d> iPropO Σ) : *)
  (*   coPset -d> expr (microsail_lang Γ τ) -d> expr (microsail_lang Γ τ) -d> (val (microsail_lang Γ τ) -d> iPropO Σ) -d> iPropO Σ  := λ E e1 e2 Φ, *)
  (* match to_val e1 with *)
  (* | Some v2 => ∃ v2, |={E}=> Φ v1 v2 *)
  (* | None => ∀ σ1 ns κ κs nt, *)
  (*    state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗ *)
  (*      ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗ *)
  (*      ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ *)
  (*        £ (S (num_laters_per_step ns)) *)
  (*        ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=> *)
  (*        state_interp σ2 (S ns) κs (length efs + nt) ∗ *)
  (*        wp E e2 Φ ∗ *)
  (*        [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post *)
  (* end%I. *)

End IrisResources2.

Module Type IrisBase2 (B : Base) (PROG : Program B) (SEM : Semantics B PROG) :=
  IrisPrelims B PROG SEM <+ IrisParameters2 B PROG SEM <+ IrisResources2 B PROG SEM.

(* The following three modules define the Iris instance of the program logic
   depending solely on the operational semantics (through IrisBase) and the
   user-defined predicates (in IrisPredicates), but without depending on a
   Specification module. The program logic rules of this subset are implemented
   in IrisSignatureRules, which is combined with IrisPredicates to form
   IrisInstance.

   This split allows us to use multiple different specifications with the same
   Iris model, so that the resulting triples can be combined. This is important
   particularly when combining specifications of universal contracts for unknown
   code with known code verifications, e.g. as in the RiscvPmp.BlockVerification
   proofs. *)

Module Type IrisPredicates2
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import SIG  : Signature B)
  (Import IB   : IrisBase2 B PROG SEM).
  Parameter luser_inst2 : forall `(sRG_left : sailRegGS Σ) `(sRG_right : sailRegGS Σ) `{!invGS Σ} (mG : memGS2 Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst2 : forall `(sRG_left : sailRegGS Σ) `(sRG_right : sailRegGS Σ) `{invGS Σ} (mG : memGS2 Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true ->
      luser_inst2 sRG_left sRG_right mG ts ⊢ luser_inst2 sRG_left sRG_right mG ts ∗ luser_inst2 sRG_left sRG_right mG ts.

End IrisPredicates2.

Module Type IrisSignatureRules2
  (Import B     : Base)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import SIG   : Signature B)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B PROG SEM SIG IB).
Section Soundness.

  Import SmallStepNotations.

  Existing Instance IB.sG.

  #[export] Program Instance PredicateDefIProp : PredicateDef (IProp Σ) :=
    {| lptsreg σ r v        := (@reg_pointsTo _ sailGS2_sailRegGS_left _ r v ∗ @reg_pointsTo _ sailGS2_sailRegGS_right _ r v)%I;
       luser p ts           := luser_inst2 sailGS2_sailRegGS_left sailGS2_sailRegGS_right sailGS2_memGS ts;
       lduplicate p ts Hdup := lduplicate_inst2 sailGS2_sailRegGS_left sailGS2_sailRegGS_right sailGS2_memGS ts Hdup
    |}.

  Definition semWp2 {Γ τ} (δ1 δ2 : CStore Γ)
             (s1 s2 : Stm Γ τ) (POST : Val τ -> CStore Γ -> Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
           WP2 (MkConf s1 δ1) and (MkConf s2 δ2) @ MaybeStuck ; ⊤ {{ fun c1 c2 => POST (valconf_val c1) (valconf_store c1) (valconf_val c2) (valconf_store c2) }}%I.

  Lemma semWp2_unfold [Γ τ] (s1 s2 : Stm Γ τ)
    (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 s1 s2 Q ⊣⊢
      match stm_to_val s1 with
      | Some v1 => |={⊤}=> ∃ v2, ⌜ s2 = stm_val τ v2 ⌝ ∗ Q v1 δ1 v2 δ2
      | None   => ∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
          (regs_inv (srGS := sailGS2_sailRegGS_left) γ1 ∗
             regs_inv (srGS := sailGS2_sailRegGS_right) γ2 ∗
             mem_inv2 (mG := sailGS2_memGS) μ1 μ2
           ={⊤,∅}=∗
              (∀ (s12 : Stm Γ τ) (δ12 : CStore Γ) (γ12 : RegStore) (μ12 : Memory),
                  ⌜⟨ γ1, μ1, δ1 , s1 ⟩ ---> ⟨ γ12, μ12, δ12, s12 ⟩⌝ ={∅}▷=∗
                     |={∅,⊤}=> ∃ s22 γ22 μ22 δ22,
                       ⌜⟨ γ2, μ2, δ2 , s2 ⟩ ---> ⟨ γ22, μ22, δ22, s22 ⟩⌝ ∗
                      (regs_inv (srGS := sailGS2_sailRegGS_left) γ12 ∗
                         regs_inv (srGS := sailGS2_sailRegGS_right) γ22 ∗
                         mem_inv2 (mG := sailGS2_memGS) μ12 μ22) ∗
                                 semWp2 δ12 δ22 s12 s22 Q))
      end.
  Proof.
    rewrite /semWp2 wp2_unfold /wp_pre2.
    cbn.
    destruct (stm_to_val s1); cbn.
    { iSplit.
      - iIntros ">(%v2 & %eq & HQ) !>".
        inversion eq.
        iExists _; now iSplitR.
      - iIntros ">(%v2 & -> & HQ) !>".
        iExists (MkValConf _ _ _); now iSplitR.
    }
    - iSplit.
      + iIntros "H" (γ1 γ2 μ1 μ2) "(Hγ1 & Hγ2 & Hmem)".
        iMod ("H" $! (γ1 , μ1)  (γ2 , μ2) 0 []%list with "[$Hγ1 $Hγ2 $Hmem]") as "(_ & H)".
        iModIntro.
        iIntros (s12 δ12 γ12 μ12 Hstep) "".
        iMod ("H" $! (MkConf s12 δ12) (γ12 , μ12) (mk_prim_step (MkConf s1 δ1) Hstep)) as "H".
        do 2 iModIntro.
        iMod "H" as "H". iModIntro.
        iMod "H" as "(%c22 & %σ22 & %κ2 & %Hstep2 & (Hγ12 & Hγ22 & Hmem) & Hcont)". iModIntro.
        inversion Hstep2; subst; cbn in *.
        iExists _, _, _, _; now iFrame.
      + iIntros "H" ([γ1 μ1] [γ2 μ2] _ κ1) "(Hγ1 & Hγ2 & Hmem)".
        iMod ("H" with "[$Hγ1 $Hγ2 $Hmem]") as "H".
        iModIntro. iSplitR; first easy.
        iIntros ([s12 δ12] [γ12 μ12] Hstep) "".
        inversion Hstep; subst.
        cbn in H2.
        iMod ("H" $! s12 δ12 γ12 μ12 H2) as "H".
        do 2 iModIntro.
        iMod "H" as "H". iModIntro.
        iMod "H" as "(%s22 & %γ22 & %μ22 & %δ22 & %Hstep2 & (Hγ12 & Hγ22 & Hmem) & Hcont)".
        iModIntro.
        iExists (MkConf _ _), (_ , _), []%list; now iFrame.
  Qed.

  Lemma semWp2_mono [Γ τ] (s1 s2 : Stm Γ τ)
    (Q1 Q2 : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    ⊢ semWp2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWp2 δ1 δ2 s1 s2 Q2.
  Proof.
    unfold semWp2. iIntros "Hwp HQ".
    iApply (wp2_strong_mono with "Hwp"); auto.
    iIntros ([v1 δ1'] [v2 δ2']) "HQ1".
    now iApply ("HQ" with "HQ1").
  Qed.

  Lemma semWp2_val {Γ τ} (v1 : Val τ) e2 (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 (stm_val τ v1) e2 Q ⊣⊢ |={⊤}=> ∃ v2, ⌜ e2 = stm_val τ v2 ⌝ ∗ Q v1 δ1 v2 δ2.
  Proof.
    now rewrite semWp2_unfold.
  Qed.

  Lemma semWp2_val' {Γ τ} (Φ : Val τ -> CStore Γ -> Val τ -> CStore Γ -> iProp Σ) vA vB δA δB :
    Φ vA δA vB δB ⊢ semWp2 δA δB (stm_val _ vA) (stm_val _ vB) Φ.
  Proof. rewrite semWp2_val. iIntros "HΦ !>". iExists vB.
         now iFrame "HΦ".
  Qed.

  Lemma semWp2_fail {Γ τ s} Q (δ1 δ2 : CStore Γ) s2 :
      semWp2 δ1 δ2 (stm_fail τ s) s2 Q ⊣⊢ True.
  Proof.
    apply bi.entails_anti_sym; [auto|].
    rewrite semWp2_unfold. cbn.
    iIntros "_" (γ1 γ2 μ1 μ2) "Hstate".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iIntros (s12 δ12 γ12 μ12 step).
    destruct (smallinvstep step).
  Qed.

  Lemma semWp2_exp {Γ τ} (Φ : Val τ -> CStore Γ -> Val τ -> CStore Γ -> iProp Σ) eA eB δA δB :
    Φ (eval eA δA) δA (eval eB δB) δB ⊢ semWp2 δA δB (stm_exp eA) (stm_exp eB) Φ.
  Proof.
    rewrite semWp2_unfold.
    iIntros "HΦ" (γ11 γ21 μ11 μ21) "Hσ".
    iMod (@fupd_mask_subseteq _ _ ⊤ empty) as "Hclose"; first set_solver.
    iModIntro. iIntros (s12 δ12 γ12 μ12 Hstep).
    destruct (smallinvstep Hstep).
    do 3 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iExists (stm_val _ (eval eB δB)), _ , _, _.
    iSplitR.
    - iPureIntro; repeat constructor.
    - iFrame "Hσ".
      now iApply semWp2_val'.
  Qed.

  Lemma semWp2_bind {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
    (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12 δ22 (k1 v1) (k2 v2) Q) ⊢
      semWp2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
  Proof.
    iRevert (s1 s2 δ1 δ2).
    iLöb as "IH".
    iIntros (s1 s2 δ1 δ2) "Hs".
    rewrite (semWp2_unfold (stm_bind _ _)).
    cbn.
    iIntros (γ1 γ2 μ1 μ2) "Hstate".
    iMod (@fupd_mask_subseteq _ _ ⊤ empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 Hstep).
    destruct (smallinvstep Hstep); cbn.
    - rewrite semWp2_val.
      do 3 iModIntro.
      iMod "Hclose" as "_".
      iMod "Hs" as "(%v2 & -> & Hk)".
      iExists _, _, _, _.
      iFrame "Hk Hstate".
      iPureIntro; constructor.
    - do 3 iModIntro.
      iMod "Hclose" as "_".
      rewrite semWp2_fail.
      (* damn, something wrong in definition of WP2: failure left should imply failure right? *)
      admit.
    - rewrite (semWp2_unfold s).
      rewrite (stm_val_stuck H); cbn.
      iMod "Hclose" as "_".
      iMod ("Hs" with "Hstate") as "Hs".
      iMod ("Hs" $! _ _ _ _ H) as "Hs".
      do 2 iModIntro.
      iMod "Hs" as "Hs". iModIntro.
      iMod "Hs" as "(%s22 & %γ22 & %μ22 & %δ22 & %Hstep & Hstate & Hwp)". iModIntro.
      iExists (stm_bind s22 k2), γ22, μ22, δ22.
      iSplitR; first by iPureIntro; constructor.
      iFrame "Hstate".
      now iApply "IH".
  Admitted.

  Lemma semWp2_block {Γ τ Δ} (δΔ1 δΔ2 : CStore Δ) (s1 s2 : Stm (Γ ▻▻ Δ) τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        semWp2 (δ1 ►► δΔ1) (δ2 ►► δΔ2) s1 s2 (fun v1 δ21 v2 δ22 => Q v1 (env.drop Δ δ21) v2 (env.drop Δ δ22)) -∗
        semWp2 δ1 δ2 (stm_block δΔ1 s1) (stm_block δΔ2 s2) Q.
  Proof.
    iIntros (Q). iRevert (δΔ1 s1 δΔ2 s2).
    iLöb as "IH". iIntros (δΔ1 s1 δΔ2 s2 δΓ1 δΓ2) "WPk".
    rewrite (semWp2_unfold (stm_block δΔ1 s1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 step). destruct (smallinvstep step); cbn.
    - rewrite !semWp2_val. rewrite ?env.drop_cat.
      do 3 iModIntro. iMod "Hclose" as "_".
      iMod "WPk" as "(%v2 & -> & HQ)". iModIntro.
      iExists _, _, _, _.
      rewrite semWp2_val.
      iSplitR; first by iPureIntro; constructor.
      iFrame "state_inv". iModIntro.
      iExists v2. now iSplitR.
    - rewrite !semWp2_fail.
      do 3 iModIntro. iMod "Hclose" as "_".
      iModIntro.
      (* see above: failure left should imply failure right? *)
      admit.
    - rewrite (semWp2_unfold k s2). rewrite (stm_val_stuck H).
      iSpecialize ("WPk" with "state_inv").
      iMod "Hclose" as "_". iMod "WPk".
      iSpecialize ("WPk" $! _ _ _ _ H).
      iMod "WPk". iModIntro. iModIntro. iModIntro.
      iMod "WPk". iMod "WPk" as "(%s22 & %γ22 & %μ22 & %δ22 & %step2 & state_inv & WPk)". iModIntro.
      destruct (env.catView δ22) as (δΓ22 & δΔ22).
      iExists _, _, _, _.
      iSplitR; first by iPureIntro; constructor.
      iFrame.
      by iApply "IH".
  Admitted.

  Lemma semWp2_let {Γ τ x σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm (Γ ▻ x∷σ) τ)
    (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    ⊢ semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12.[x∷σ ↦ v1] δ22.[x∷σ ↦ v2] k1 k2 (fun v12 δ13 v22 δ23 => Q v12 (env.tail δ13) v22 (env.tail δ23)) ) -∗
        semWp2 δ1 δ2 (let: x ∷ σ := s1 in k1) (let: x ∷ σ := s2 in k2) Q.
  Proof.
    rewrite (semWp2_unfold (stm_let _ _ _ _)); cbn.
    iIntros "Hs" (γ1 γ2 μ1 μ2) "Hstate".
    iMod (@fupd_mask_subseteq _ _ ⊤ empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 Hstep).
    destruct (smallinvstep Hstep).
    do 3 iModIntro.
    iMod "Hclose" as "_". iModIntro.
    iExists _, _, _, _.
    iSplitR.
    - iPureIntro; repeat constructor.
    - iFrame "Hstate".
      iApply semWp2_bind.
      iApply (semWp2_mono with "Hs"). iIntros (v1 δ21 v2 δ22) "WPk".
      now iApply (semWp2_block [env].[_∷_ ↦ v1]).
  Qed.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗
           semWp2 δ δ s s (fun v1 δ1 v2 δ2 => ⌜ v1 = v2 ⌝ ∗ ⌜ δ1 = δ2 ⌝ ∗ POST v1 δ1)%I.
  (* always modality needed? perhaps not because sail not higher-order? *)
  Global Arguments semTriple {Γ} {τ} δ PRE%I s%exp POST%I.

  Definition ValidLemma {Δ} (lem : Lemma Δ) : Prop :=
    match lem with
      {| lemma_logic_variables := Σ;
         lemma_patterns        := θΔ;
         lemma_precondition    := req;
         lemma_postcondition   := ens;
      |} =>
      forall (ι : Valuation Σ),
        ⊢ asn.interpret req ι -∗
          asn.interpret ens ι
    end.

  Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
        {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "trips P".
    iPoseProof (PP with "P") as "P'".
    iPoseProof ("trips" with "P'") as "wpq".
    iApply (semWp2_mono with "wpq").
    iIntros (v1 δ1 v2 δ2) "(-> & -> & HQ)".
    repeat (iSplitR; first easy).
    now iApply QQ.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "trips [HR HP]".
    iApply (semWp2_mono with "[trips HP]").
    - now iApply "trips".
    - iIntros (v1 d1 v2 δ2) "(-> & -> & HQ)".
      now iFrame.
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ → semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R).
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q :  Val σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q).
  Proof.
    iIntros "trips [%x Px]".
    by iApply "trips".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q v δ)%I -∗ semTriple δ P (stm_val τ v) Q).
  Proof.
    iIntros "PQ P".
    iApply wp2_value'; try reflexivity.
    repeat (iSplitR; first done).
    by iApply "PQ".
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q).
  Proof.
    iIntros "PQ P".
    iApply semWp2_exp.
    repeat (iSplitR; first done).
    by iApply "PQ".
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : PVar) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Val σ) (δ' : CStore Γ),
                         semTriple (env.snoc δ' (x∷σ) v) (Q v δ') k (fun v δ'' => R v (env.tail δ'')) ) -∗
                     semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "trips tripk P".
    iApply semWp2_let.
    iApply (semWp2_mono with "[trips P] [tripk]").
    { now iApply ("trips" with "P"). }
    iIntros (v1 δ1 v2 δ2) "(-> & -> & HQ)".
    iApply (semWp2_mono with "[tripk HQ] []").
    { iApply ("tripk" with "HQ"). }
    iIntros (v1 δ1 v2' δ2') "(-> & -> & HR)".
    auto.
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
                   semTriple δ P (stm_block δΔ k) R).
  Proof.
  (*   iIntros "tripk P". iPoseProof ("tripk" with "P") as "wpk". *)
  (*   by iApply semWP_block. *)
  (* Qed. *)
  Admitted.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R).
  Proof.
  Admitted.
  (*   iIntros "trips1 trips2 P". *)
  (*   iSpecialize ("trips1" with "P"). *)
  (*   iApply semWP_seq. *)
  (*   iApply (semWP_mono with "[$]"). *)
  (*   by iFrame. *)
  (* Qed. *)

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜ eval e1 δ = true ⌝ → semTriple δ P k Q) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
  Admitted.
  (*   iIntros "tripk P". *)
  (*   iApply semWP_assertk. *)
  (*   iIntros (->). *)
  (*   by iApply "tripk". *)
  (* Qed. *)

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Val ty.string) :
        forall (Q : Val τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    by iApply semWp2_fail.
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v)).
  Proof.
  Admitted.
  (*   iIntros "Hreg". *)
  (*   iApply semWP_read_register. *)
  (*   iExists v. *)
  (*   iFrame. *)
  (*   repeat iSplit; auto. *)
  (* Qed. *)

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
  Proof.
  Admitted.
  (*   iIntros "Hreg". *)
  (*   iApply semWP_write_register. *)
  (*   iExists v. *)
  (*   iFrame. *)
  (*   repeat iSplit; auto. *)
  (* Qed. *)

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R).
  Proof.
  Admitted.
  (*   iIntros "trips P". *)
  (*   iSpecialize ("trips" with "P"). *)
  (*   by iApply semWP_assign. *)
  (* Qed. *)

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Val σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R).
  Proof.
  Admitted.
  (*   iIntros "trips tripk P". *)
  (*   iSpecialize ("trips" with "P"). *)
  (*   iApply semWP_bind. *)
  (*   by iApply (semWP_mono with "trips"). *)
  (* Qed. *)

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
  Admitted.
  (*   iIntros "tripbody P". *)
  (*   iApply semWP_call_inline_later. *)
  (*   by iApply "tripbody". *)
  (* Qed. *)

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
  Admitted.
  (*   iIntros "Hdef". *)
  (*   iApply (iris_rule_stm_call_inline_later with "Hdef"). *)
  (* Qed. *)

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q).
  Proof.
  Admitted.
  (*   iIntros "tripk P". iApply semWP_debugk. now iApply "tripk". *)
  (* Qed. *)

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    stm_to_val s = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                            ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
  Admitted.
  (*   iIntros (Hnv Hnoop) "HPQ HP". *)
  (*   rewrite semWP_unfold. rewrite Hnv. *)
  (*   iIntros (γ1 μ1) "state_inv". *)
  (*   iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro. *)
  (*   iIntros (s2 δ2 γ2 μ2) "%". *)
  (*   destruct (Hnoop _ _ _ _ _ _ H) as (-> & -> & -> & [[v ->]|[msg ->]]). *)
  (*   - do 3 iModIntro. iMod "Hclose" as "_". *)
  (*     iFrame. iApply semWP_val. now iApply "HPQ". *)
  (*   - do 3 iModIntro. iMod "Hclose" as "_". *)
  (*     iFrame. now iApply semWP_fail. *)
  (* Qed. *)

  Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      sep.Forall (fun (ι : Valuation ctxΣ) =>
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
    end.

  Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      ∀ (ι : Valuation ctxΣ),
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v))
    end.

  Definition ValidContractForeign {Δ τ} (contract : SepContract Δ τ) (f : 𝑭𝑿 Δ τ) : Prop :=
    forall Γ (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match contract with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : Valuation Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (asn.interpret req ι) (stm_foreign f es)
          (fun v δ' => asn.interpret ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
      end.

  Lemma Forall_forall {B : Set} {D : B -> Set} (Δ : Ctx B) (P : Env D Δ → iProp Σ) :
    sep.Forall P ⊣⊢ (∀ E : Env D Δ, P E).
  Proof. apply bi.equiv_entails, sep.Forall_forall. Qed.

  Definition valid_contract_curry {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
    ValidContractSem body contract ⊣⊢ ValidContractSemCurried body contract.
  Proof.
    destruct contract as [lvars δ req res ens]; cbn.
    now rewrite Forall_forall.
  Qed.

End Soundness.

Section Adequacy.

  Import SmallStepNotations.

(*   Definition sailΣ : gFunctors := #[ memΣ ; invΣ ; GFunctor regUR]. *)

(*   Instance subG_sailGpreS {Σ} : subG sailΣ Σ -> sailGpreS Σ. *)
(*   Proof. *)
(*     intros. *)
(*     lazymatch goal with *)
(*     | H:subG ?xΣ _ |- _ => try unfold xΣ in H *)
(*     end. *)
(*     repeat match goal with *)
(*            | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H *)
(*            end. *)
(*     split; eauto using memΣ_GpreS, subG_invΣ. *)
(*     solve_inG. *)
(*  Qed. *)

(*   Definition RegStore_to_map (γ : RegStore) : gmap SomeReg (exclR (leibnizO SomeVal)) := *)
(*     list_to_map (K := SomeReg) *)
(*                 (fmap (fun x => match x with *)
(*                               existT _ r => *)
(*                                 pair (existT _ r) (Excl (existT _ (read_register γ r))) *)
(*                             end) *)
(*                      (finite.enum (sigT 𝑹𝑬𝑮))). *)

(*   Lemma RegStore_to_map_Forall (γ : RegStore) : *)
(*     map_Forall (K := SomeReg) *)
(*       (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register γ reg)) = v end) *)
(*       (RegStore_to_map γ). *)
(*   Proof. *)
(*     eapply map_Forall_lookup_2. *)
(*     intros [σ r] x eq. *)
(*     unfold RegStore_to_map in eq. *)
(*     destruct (list_to_map _ !! _) eqn:eq' in eq; inversion eq; subst. *)
(*     rewrite <-elem_of_list_to_map in eq'. *)
(*     - eapply elem_of_list_fmap_2 in eq'. *)
(*       destruct eq' as ([σ' r'] & eq2 & eq3). *)
(*       now inversion eq2. *)
(*     - rewrite <-list_fmap_compose. *)
(*       rewrite (list_fmap_ext (compose fst (λ x : {H : Ty & 𝑹𝑬𝑮 H}, *)
(*           let (x0, r0) := x in (existT x0 r0 , Excl (existT x0 (read_register γ r0))))) id _ _ _ eq_refl). *)
(*       + rewrite list_fmap_id. *)
(*         eapply finite.NoDup_enum. *)
(*       + now intros [σ' r']. *)
(*   Qed. *)

(*   Lemma RegStore_to_map_valid (γ : RegStore) : *)
(*     valid (RegStore_to_map γ). *)
(*   Proof. *)
(*     intros i. *)
(*     cut (exists v, RegStore_to_map γ !! i = Some (Excl v)). *)
(*     - intros [v eq]. *)
(*       now rewrite eq. *)
(*     - destruct i as [σ r]. *)
(*       exists (existT _ (read_register γ r)). *)
(*       eapply elem_of_list_to_map_1'. *)
(*       + intros y eq. *)
(*         eapply elem_of_list_fmap_2 in eq. *)
(*         destruct eq as ([σ2 r2] & eq1 & eq2). *)
(*         now inversion eq1. *)
(*       + refine (elem_of_list_fmap_1 _ _ (existT _ r) _). *)
(*         eapply finite.elem_of_enum. *)
(*   Qed. *)

(*   Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}: *)
(*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
(*     rtc erased_step ([MkConf s δ]%list, (γ,μ)) ([MkConf s' δ']%list, (γ',μ')). *)
(*   Proof. *)
(*     induction 1; first done. *)
(*     refine (rtc_l _ _ _ _ _ IHSteps). *)
(*     exists nil. *)
(*     refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _). *)
(*     by eapply mk_prim_step. *)
(*   Qed. *)

(*   Lemma steps_to_nsteps {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}: *)
(*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
(*     exists n, language.nsteps n ([MkConf s δ]%list , (γ,μ)) [] ([MkConf s' δ']%list , (γ',μ')). *)
(*   Proof. *)
(*     induction 1. *)
(*     - exists 0. now constructor. *)
(*     - destruct IHSteps as [n steps]. *)
(*       exists (S n). *)
(*       refine (language.nsteps_l _ _ _ _ [] _ _ steps). *)
(*       refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _). *)
(*       now eapply mk_prim_step. *)
(*   Qed. *)

(*   Lemma own_RegStore_to_map_reg_pointsTos `{sailRegGS Σ'} {γ : RegStore} {l : list (sigT 𝑹𝑬𝑮)} : *)
(*     NoDup l -> *)
(*     ⊢ own reg_gv_name (◯ list_to_map (K := SomeReg) *)
(*                          (fmap (fun x => match x with existT _ r => *)
(*                                                      pair (existT _ r) (Excl (existT _ (read_register γ r))) *)
(*                                       end) l)) -∗ *)
(*       [∗ list] x ∈ l, *)
(*         let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo r (read_register γ r). *)
(*   Proof. *)
(*     iIntros (nodups) "Hregs". *)
(*     iInduction l as [|[x r]] "IH". *)
(*     - now iFrame. *)
(*     - rewrite big_sepL_cons. cbn. *)
(*       rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ r)))). *)
(*       rewrite auth_frag_op. *)
(*       iPoseProof (own_op with "Hregs") as "[Hreg Hregs]". *)
(*       iFrame. *)
(*       iApply ("IH" with "[%] [$]"). *)
(*       + refine (NoDup_cons_1_2 (existT x r) l nodups). *)
(*       + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _]. *)
(*         refine (not_elem_of_list_to_map_1 _ (existT x r) _). *)
(*         rewrite <-list_fmap_compose. *)
(*         rewrite (list_fmap_ext (compose fst (λ x : {H : Ty & 𝑹𝑬𝑮 H}, *)
(*           let (x0, r0) := x in (existT x0 r0, Excl (existT x0 (read_register γ r0))))) id _ _ _ eq_refl). *)
(*         now rewrite list_fmap_id. *)
(*         now intros [σ2 r2]. *)
(*   Qed. *)

(*   Definition own_regstore `{sailGS Σ} (γ : RegStore) : iProp Σ := *)
(*     [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮), *)
(*       match x with | existT _ r => reg_pointsTo r (read_register γ r) end. *)

(*   Lemma adequacy {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'} *)
(*         {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : Val σ -> Prop} : *)
(*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' -> *)
(*     (forall `{sailGS Σ'}, ⊢ semTriple δ (mem_res μ ∗ own_regstore γ) s (fun v _ => ⌜ Q v ⌝)) -> *)
(*     ResultOrFail s' Q. *)
(*   Proof. *)
(*     intros steps fins trips. *)
(*     cut (adequate MaybeStuck (MkConf s δ) (γ,μ) *)
(*              (λ (v : val (microsail_lang Γ σ)) (_ : state (microsail_lang Γ σ)), *)
(*                 (λ v0 : val (microsail_lang Γ σ), match v0 with *)
(*                                                   | MkValConf _ v' _ => Q v' *)
(*                                                   end) v)). *)
(*     - destruct s'; cbn in fins; destruct fins; last done. *)
(*       intros adeq. *)
(*       apply (adequate_result MaybeStuck (MkConf s δ) (γ , μ) (fun v _ => match v with | MkValConf _ v' δ' => Q v' end) adeq nil (γ' , μ') (MkValConf _ v δ')). *)
(*       by apply steps_to_erased. *)
(*     - constructor; last done. *)
(*       intros t2 σ2 [v2 δ2] eval. *)
(*       assert (eq := RegStore_to_map_Forall γ). *)
(*       assert (regsmapv := RegStore_to_map_valid γ). *)
(*       pose proof (wp_adequacy sailΣ (microsail_lang Γ σ) MaybeStuck (MkConf s δ) (γ , μ) (fun v => match v with | MkValConf _ v' δ' => Q v' end)) as adeq. *)
(*       refine (adequate_result _ _ _ _ (adeq _) _ _ _ eval); clear adeq. *)
(*       iIntros (Hinv κs) "". *)
(*       iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]"; *)
(*         first by apply auth_both_valid. *)
(*       pose proof (memΣ_GpreS (Σ := sailΣ) _) as mGS. *)
(*       iMod (mem_inv_init (mGS := mGS)) as (memG) "[Hmem Rmem]". *)
(*       iModIntro. *)
(*       iExists (fun σ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_inv (σ.2))%I. *)
(*       iExists _. *)
(*       iSplitR "Hs2 Rmem". *)
(*       * iFrame. *)
(*         iExists (RegStore_to_map γ). *)
(*         now iFrame. *)
(*       * iApply (wp_mono). *)
(*         2: { *)
(*           iApply (trips _ (SailGS Hinv (SailRegGS reg_pre_inG spec_name) memG) with "[$Rmem Hs2]"). *)
(*           iApply (own_RegStore_to_map_reg_pointsTos (H := SailRegGS reg_pre_inG spec_name)(γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2"). *)
(*           eapply finite.NoDup_enum. *)
(*         } *)
(*         done. *)
(*   Qed. *)

(*   Lemma adequacy_gen {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'} *)
(*         {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : forall `{sailGS Σ}, Val σ -> CStore Γ -> iProp Σ} (φ : Prop): *)
(*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
(*     (forall `{sailGS Σ'}, *)
(*         mem_res μ ∗ own_regstore γ ⊢ |={⊤}=> semWP s Q δ *)
(*           ∗ (mem_inv μ' ={⊤,∅}=∗ ⌜φ⌝) *)
(*     )%I -> φ. *)
(*   Proof. *)
(*     (* intros steps trips. *) *)
(*     intros [n steps]%steps_to_nsteps trips. *)
(*     refine (wp_strong_adequacy sailΣ (microsail_lang Γ σ) _ _ _ _ _ _ _ (fun _ => 0) _ steps). *)
(*     iIntros (Hinv) "". *)
(*     assert (eq := RegStore_to_map_Forall γ). *)
(*     assert (regsmapv := RegStore_to_map_valid γ). *)
(*     iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]"; *)
(*         first by apply auth_both_valid. *)
(*     pose proof (memΣ_GpreS (Σ := sailΣ) _) as mGS. *)
(*     iMod (mem_inv_init (mGS := mGS)) as (memG) "[Hmem Rmem]". *)
(*     pose (regsG := {| reg_inG := @reg_pre_inG sailΣ (@subG_sailGpreS sailΣ (subG_refl sailΣ)); reg_gv_name := spec_name |}). *)
(*     pose (sailG := SailGS Hinv regsG memG). *)
(*     iMod (trips sailΣ sailG with "[$Rmem Hs2]") as "[trips Hφ]". *)
(*     {unfold own_regstore. *)
(*       iApply (own_RegStore_to_map_reg_pointsTos (H := regsG) (γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2"). *)
(*       eapply finite.NoDup_enum. *)
(*     } *)
(*     iModIntro. *)
(*     iExists MaybeStuck. *)
(*     iExists (fun σ _ _ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_inv (σ.2))%I. *)
(*     iExists [ fun v => Q _ sailG (valconf_val v) (valconf_store v) ]%list. *)
(*     iExists _. *)
(*     iExists _. *)
(*     iSplitR "trips Hφ". *)
(*     * iFrame. *)
(*       iExists (RegStore_to_map γ). *)
(*       now iFrame. *)
(*     * cbn. iFrame. *)
(*       iIntros (es' t2') "_ _ _ [Hregsinv Hmeminv] _ _". *)
(*       now iApply "Hφ". *)
(*   Qed. *)

End Adequacy.
End IrisSignatureRules2.

(* Module Type IrisInstance (B : Base) (PROG : Program B) (SEM : Semantics B PROG) (SIG : Signature B) (IB : IrisBase B PROG SEM) := *)
(*   IrisPredicates B PROG SEM SIG IB <+ IrisSignatureRules B PROG SEM SIG IB. *)

(* (* *)
(*  * The following module defines the parts of the Iris model that must depend on the Specification, not just on the Signature. *)
(*  * This is kept to a minimum (see comment for the IrisPredicates module). *)
(*  *) *)
(* Module IrisInstanceWithContracts *)
(*   (Import B     : Base) *)
(*   (Import PROG  : Program B) *)
(*   (Import SEM   : Semantics B PROG) *)
(*   (Import SIG   : Signature B) *)
(*   (Import SPEC  : Specification B PROG SIG) *)
(*   (Import IB    : IrisBase B PROG SEM) *)
(*   (Import II    : IrisInstance B PROG SEM SIG IB) *)
(*   (Import PLOG  : ProgramLogicOn B PROG SIG SPEC). *)

(*   Section WithSailGS. *)
(*   Import ProgramLogic. *)
(*   Context {Σ} {sG : sailGS Σ}. *)

(*   Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ := *)
(*     (∀ σs σ (f : 𝑭 σs σ), *)
(*       match cenv σs σ f with *)
(*       | Some c => ValidContractSem (FunDef f) c *)
(*       | None => True *)
(*       end)%I. *)

(*   Definition ForeignSem := *)
(*     ∀ (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ), *)
(*       ValidContractForeign (CEnvEx f) f. *)

(*   Definition LemmaSem : Prop := *)
(*     forall (Δ : PCtx) (l : 𝑳 Δ), *)
(*       ValidLemma (LEnv l). *)

(*   Lemma iris_rule_stm_call {Γ} (δ : CStore Γ) *)
(*     {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ) *)
(*     (P : iProp Σ) *)
(*     (Q : Val σ -> CStore Γ -> iProp Σ) : *)
(*     CEnv f = Some c -> *)
(*     CTriple P c (evals es δ) (fun v => Q v δ) -> *)
(*     ⊢ ▷ ValidContractEnvSem CEnv -∗ *)
(*        semTriple δ P (stm_call f es) Q. *)
(*   Proof. *)
(*     iIntros (ceq ctrip) "cenv P". *)
(*     iApply semWP_call_inline_later. *)
(*     iModIntro. *)
(*     iSpecialize ("cenv" $! _ _ f). *)
(*     rewrite ceq. clear ceq. *)
(*     destruct c as [Σe δΔ req res ens]; cbn in *. *)
(*     iPoseProof (ctrip with "P") as (ι Heq) "[req consr]". clear ctrip. *)
(*     iPoseProof ("cenv" $! ι with "req") as "wpf0". rewrite Heq. *)
(*     iApply (semWP_mono with "wpf0"). *)
(*     by iIntros (v _). *)
(*   Qed. *)

(*   Lemma iris_rule_stm_call_frame {Γ} (δ : CStore Γ) *)
(*         (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ) *)
(*         (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) : *)
(*         ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗ *)
(*            semTriple δ P (stm_call_frame δΔ s) Q). *)
(*   Proof. *)
(*     iIntros "trips P". *)
(*     iSpecialize ("trips" with "P"). *)
(*     by iApply semWP_call_frame. *)
(*   Qed. *)

(*   Lemma iris_rule_stm_foreign *)
(*     {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ) *)
(*     (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) : *)
(*     ForeignSem -> *)
(*     CTriple P (CEnvEx f) (evals es δ) (λ v : Val τ, Q v δ) -> *)
(*     ⊢ semTriple δ P (stm_foreign f es) Q. *)
(*   Proof. *)
(*     iIntros (forSem ctrip) "P". *)
(*     specialize (forSem Δ τ f Γ es δ). *)
(*     destruct CEnvEx as [Σe δΔ req res ens]; cbn in *. *)
(*     iPoseProof (ctrip with "P") as "[%ι [%Heq [req consr]]]". clear ctrip. *)
(*     iPoseProof (forSem ι Heq with "req") as "WPf". clear forSem. *)
(*     iApply (semWP_mono with "WPf"). *)
(*     iIntros (v δΓ') "[ens ->]". *)
(*     by iApply "consr". *)
(*   Qed. *)

(*   Lemma iris_rule_stm_lemmak *)
(*     {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ) *)
(*     (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) : *)
(*     LemmaSem -> *)
(*     LTriple (evals es δ) P Q (LEnv l) -> *)
(*     ⊢ semTriple δ Q k R -∗ *)
(*       semTriple δ P (stm_lemmak l es k) R. *)
(*   Proof. *)
(*     iIntros (lemSem ltrip) "tripk P". iApply semWP_lemmak. iApply "tripk". *)
(*     specialize (lemSem _ l). remember (LEnv l) as contractL. *)
(*     clear - lemSem ltrip. *)
(*     dependent elimination ltrip; cbn in lemSem. *)
(*     iPoseProof (l with "P") as (ι Heq) "[req consr]". *)
(*     iApply "consr". by iApply lemSem. *)
(*   Qed. *)

(*   Lemma iris_rule_stm_pattern_match {Γ τ σ} (δΓ : CStore Γ) *)
(*     (s : Stm Γ σ) (pat : Pattern σ) *)
(*     (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) *)
(*     (P : iProp Σ) (Q : Val σ → CStore Γ → iProp Σ) (R : Val τ → CStore Γ → iProp Σ) : *)
(*     ⊢ semTriple δΓ P s Q -∗ *)
(*       (∀ pc δpc δΓ1, *)
(*          semTriple (δΓ1 ►► δpc) (Q (pattern_match_val_reverse pat pc δpc) δΓ1) (rhs pc) *)
(*            (λ vτ (δ' : CStore (Γ ▻▻ PatternCaseCtx pc)), R vτ (env.drop (PatternCaseCtx pc) δ'))) -∗ *)
(*       semTriple δΓ P (stm_pattern_match s pat rhs) R. *)
(*   Proof. *)
(*     iIntros "WPs WPrhs P". *)
(*     iSpecialize ("WPs" with "P"). *)
(*     iApply semWP_pattern_match. *)
(*     iApply (semWP_mono with "WPs"). *)
(*     iIntros (vσ δΓ') "Q". *)
(*     destruct pattern_match_val as [pc δpc] eqn:Heq. *)
(*     iApply "WPrhs". *)
(*     change (pattern_match_val_reverse pat pc δpc) with *)
(*       (pattern_match_val_reverse' pat (existT pc δpc)). *)
(*     rewrite <- Heq. *)
(*     now rewrite pattern_match_val_inverse_left. *)
(*   Qed. *)

(*   Lemma sound_stm *)
(*     {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}: *)
(*     forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ), *)
(*       ForeignSem -> *)
(*       LemmaSem -> *)
(*       ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ -> *)
(*       ⊢ (□ ▷ ValidContractEnvSem CEnv -∗ *)
(*           semTriple δ PRE s POST)%I. *)
(*   Proof. *)
(*     iIntros (PRE POST extSem lemSem triple) "#vcenv". *)
(*     iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips". *)
(*     - by iApply iris_rule_consequence. *)
(*     - by iApply iris_rule_frame. *)
(*     - by iApply iris_rule_pull. *)
(*     - by iApply iris_rule_exist. *)
(*     - iApply iris_rule_stm_val. *)
(*       by iApply H. *)
(*     - iApply iris_rule_stm_exp. *)
(*       by iApply H. *)
(*     - by iApply iris_rule_stm_let. *)
(*     - by iApply iris_rule_stm_block. *)
(*     - by iApply iris_rule_stm_seq. *)
(*     - by iApply iris_rule_stm_assertk. *)
(*     - by iApply iris_rule_stm_fail. *)
(*     - by iApply iris_rule_stm_read_register. *)
(*     - by iApply iris_rule_stm_write_register. *)
(*     - by iApply iris_rule_stm_assign. *)
(*     - by iApply iris_rule_stm_call. *)
(*     - by iApply iris_rule_stm_call_inline. *)
(*     - by iApply iris_rule_stm_call_frame. *)
(*     - by iApply iris_rule_stm_foreign. *)
(*     - by iApply iris_rule_stm_lemmak. *)
(*     - by iApply iris_rule_stm_bind. *)
(*     - by iApply iris_rule_stm_debugk. *)
(*     - by iApply iris_rule_stm_pattern_match. *)
(*   Qed. *)

(*   Lemma sound : *)
(*     ForeignSem -> LemmaSem -> ValidContractCEnv -> *)
(*     ⊢ ValidContractEnvSem CEnv. *)
(*   Proof. *)
(*     intros extSem lemSem vcenv. *)
(*     iLöb as "IH". *)
(*     iIntros (σs σ f). *)
(*     specialize (vcenv σs σ f). *)
(*     destruct (CEnv f) as [[]|];[|trivial]. *)
(*     specialize (vcenv _ eq_refl). *)
(*     iIntros (ι). *)
(*     iApply (sound_stm extSem lemSem); [|trivial]. *)
(*     apply (vcenv ι). *)
(*   Qed. *)

(*   End WithSailGS. *)
(* End IrisInstanceWithContracts. *)
