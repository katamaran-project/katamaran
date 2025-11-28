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

From Coq Require Import
  Program.Equality.
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
     Iris.Base
     (* Iris.Instance *)
     Prelude
     Semantics
     Sep.Hoare
     Sep.Logic
     Signature
     SmallStep.Step
     Specification
     BinaryResources.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

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
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IB   : IrisBase2 B PROG SEM).
  Parameter luser_inst2 : forall `{sRG : sailRegGS2 Σ} `{invGS Σ} `{mG : memGS2 Σ} (p : 𝑯) (ts : Env RelVal (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst2 : forall `{sRG : sailRegGS2 Σ} `{invGS Σ} {mG : memGS2 Σ} (p : 𝑯) (ts : Env RelVal (𝑯_Ty p)),
      is_duplicable p = true ->
      luser_inst2 ts ⊢ luser_inst2 ts ∗ luser_inst2 ts.

End IrisPredicates2.

Module IrisBinaryWP
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB2   : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB2).

  Section WithSailGS2.
    Context `{sG : sailGS2 Σ}.

    #[export] Program Instance PredicateDefIProp : PredicateDef (iProp Σ) :=
      {| lptsreg σ r v        := reg_pointsTo2 r v;
        luser p ts           := luser_inst2 ts;
        lduplicate p ts Hdup := lduplicate_inst2 ts Hdup
      |}.

    (* Declare necessary OFE instances. Don't use them directly, they will be
     resolved when needed. *)
    Canonical Structure PCtxO     := leibnizO PCtx.
    Canonical Structure TyO       := leibnizO Ty.
    Canonical Structure CStoreO Γ := leibnizO (CStore Γ).
    Canonical Structure StmO Γ τ  := leibnizO (Stm Γ τ).
    Canonical Structure ValO τ    := leibnizO (Val τ).
    Canonical Structure IValO τ   := leibnizO (IVal τ).

    Definition Post2 Γ1 Γ2 τ :=
      IVal τ -> CStoreVal Γ1 -> IVal τ -> CStoreVal Γ2 -> iProp Σ.
    Canonical Structure Post2O Γ1 Γ2 τ := leibnizO (Post2 Γ1 Γ2 τ).

    Definition Wp2 Γ1 Γ2 τ :=
      CStoreVal Γ1 -d> CStoreVal Γ2 -d>
        Stm Γ1 τ -d> Stm Γ2 τ -d>
        Post2 Γ1 Γ2 τ -d>
        iProp Σ.

    (* IDEA: borrow idea of Atomic of Iris. When s1 and s2 are atomic, they are
           allowed to open the invariants and close them.
           Some useful resources to look at:
           - iris/program_logic/weakestpre.v > wp_atomic
           - iris/program_logic/atomic.v > atomic_wp_inv

           It might be that some restrictions that apply to wp2 are only
           exposed at the ISA level (for example, MMIO interactions ≡ effects)

           How does PMP come into play? Can we capture non-interferene of U-mode
           data through invariants? (I would assume so)
     *)

    Import SmallStepNotations.

    Definition semWP2_fix {Γ1 Γ2 τ}
      (wp : Wp2 Γ1 Γ2 τ) : Wp2 Γ1 Γ2 τ :=
      (λ (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2)
         (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
         (POST : Post2 Γ1 Γ2 τ),
        match stm_to_val s1, stm_to_val s2 with
        | Some v1, Some v2 => |={⊤}=> POST v1 δ1 v2 δ2
        | Some v1, None    => |={⊤}=> False
        | None   , Some v2 => |={⊤}=> False
        | None   , None    =>
            (∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
                (regs_inv2 γ1 γ2 ∗ mem_inv2_sail μ1 μ2
                 ={⊤,∅}=∗ (∀ (s12 : Stm Γ1 τ) (δ12 : CStoreVal Γ1)
                             (γ12 : RegStore) (μ12 : Memory)
                             (s22 : Stm Γ2 τ) (δ22 : CStoreVal Γ2)
                             (γ22 : RegStore) (μ22 : Memory),
                              ⌜⟨ γ1, μ1, δ1 , s1 ⟩ ---> ⟨ γ12, μ12, δ12, s12 ⟩⌝
                                ∗ ⌜⟨ γ2, μ2, δ2 , s2 ⟩ ---> ⟨ γ22, μ22, δ22, s22 ⟩⌝
                              ={∅}▷=∗
                                      |={∅,⊤}=> 
                             (regs_inv2 γ12 γ22 ∗ mem_inv2_sail μ12 μ22) ∗
                               wp δ12 δ22 s12 s22 POST)))
        end)%I.
    Global Arguments semWP2_fix {_ _}%ctx_scope {_} wp /.

  Ltac f_equiv_more_arities := match goal with
                               | H:_ ?f ?g |- ?R (?f ?x ?y ?z1) (?g ?x ?y ?z1) => solve [ simple apply H ]
                               | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2) (?g ?x ?y ?z1 ?z2) => solve [ simple apply H ]
                               | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3) (?g ?x ?y ?z1 ?z2 ?z3) => solve [ simple apply H ]
                               end.

  Ltac solve_contractive_more_arities := solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | f_equiv_more_arities]).

  Global Instance semWP2_fix_Contractive {Γ1 Γ2 τ} :
    Contractive (@semWP2_fix Γ1 Γ2 τ).
  Proof.
    unfold Wp2.
    solve_contractive_more_arities.
  Qed.

  Definition semWP2 {Γ1 Γ2 τ} : Wp2 Γ1 Γ2 τ :=
    λ δ1 δ2 s1 s2 POST, (fixpoint (@semWP2_fix Γ1 Γ2 τ)) δ1 δ2 s1 s2 POST.

  Lemma fixpoint_semWP2_fix_eq {Γ1 Γ2 τ} (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (POST : Post2 Γ1 Γ2 τ) :
    fixpoint semWP2_fix δ1 δ2 s1 s2 POST ≡ semWP2_fix (fixpoint semWP2_fix) δ1 δ2 s1 s2 POST.
  Proof. exact: (fixpoint_unfold semWP2_fix δ1 δ2 s1 s2 POST). Qed.

  Lemma fixpoint_semWP2_eq {Γ1 Γ2 τ} (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (POST : Post2 Γ1 Γ2 τ) :
    semWP2 δ1 δ2 s1 s2 POST ≡ semWP2_fix semWP2 δ1 δ2 s1 s2 POST.
  Proof. by unfold semWP2; rewrite fixpoint_semWP2_fix_eq. Qed.

  Lemma semWP2_unfold [Γ1 Γ2 τ] (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2) (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (Q : Post2 Γ1 Γ2 τ) :
    semWP2 δ1 δ2 s1 s2 Q ⊣⊢
      match stm_to_val s1, stm_to_val s2 with
      | Some v1, Some v2 => |={⊤}=> Q v1 δ1 v2 δ2
      | None, Some _ => |={⊤}=> False
      | Some _, None => |={⊤}=> False
      | None, None =>
          (∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
              (regs_inv2 γ1 γ2 ∗ mem_inv2_sail μ1 μ2
               ={⊤,∅}=∗ (∀ (s12 : Stm Γ1 τ) (δ12 : CStoreVal Γ1)
                           (γ12 : RegStore) (μ12 : Memory)
                           (s22 : Stm Γ2 τ) (δ22 : CStoreVal Γ2)
                           (γ22 : RegStore) (μ22 : Memory),
                            ⌜⟨ γ1, μ1, δ1 , s1 ⟩ ---> ⟨ γ12, μ12, δ12, s12 ⟩⌝
                              ∗ ⌜⟨ γ2, μ2, δ2 , s2 ⟩ ---> ⟨ γ22, μ22, δ22, s22 ⟩⌝
                            ={∅}▷=∗
                                    |={∅,⊤}=> 
                           (regs_inv2 γ12 γ22 ∗ mem_inv2_sail μ12 μ22) ∗
                             semWP2 δ12 δ22 s12 s22 Q)))%I
      end.
    Proof.
      rewrite (fixpoint_semWP2_eq _ _ s1). cbn.
      destruct (stm_to_val s1); destruct (stm_to_val s2).
      { auto. }
      { auto. }
      { auto. }
      apply bi.entails_anti_sym; iIntros "HYP".
      - iIntros (γ1 γ2 μ1 μ2) "state_inv".
        iSpecialize ("HYP" $! γ1 γ2 μ1 μ2 with "state_inv").
        iMod "HYP". iModIntro.
        iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 step).
        iSpecialize ("HYP" $! s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 step).
        iMod "HYP". do 2 iModIntro. iMod "HYP". iModIntro.
        auto.
      - iIntros (γ1 γ2 μ1 μ2) "state_inv".
        iSpecialize ("HYP" $! γ1 γ2 μ1 μ2 with "state_inv").
        iMod "HYP". iModIntro.
        iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 step).
        iSpecialize ("HYP" $! s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 step).
        iMod "HYP". do 2 iModIntro. iMod "HYP". iModIntro.
        auto.
    Qed.


    Lemma semWP2_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (Q1 Q2 : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2) :
      ⊢ semWP2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWP2 δ1 δ2 s1 s2 Q2.
    Proof.
      iIntros "H HQ".
      iLöb as "IH" forall (δ1 δ2 s1 s2).
                          rewrite semWP2_unfold.
                          rewrite semWP2_unfold.
                          destruct (stm_to_val s1) eqn:Es1v;
                            destruct (stm_to_val s2) eqn:Es2v; auto.
                          { iMod "H".
                            iModIntro.
                            by iApply "HQ". }
                          iIntros (γ1 γ2 μ1 μ2) "Hresources".
                          iMod ("H" with "Hresources") as "H".
                          iModIntro.
                          iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 Hstep).
                          iSpecialize ("H" $! _ _ _ _ _ _ _ _ Hstep).
                          iMod "H". iModIntro.
                          iModIntro.
                          iMod "H".
                          iModIntro.
                          iMod "H".
                          iModIntro.
                          iDestruct "H" as "(Hresources & H)".
                          iFrame "Hresources".
                          iApply ("IH" with "H HQ").
    Qed.
    

    Lemma semWP2_val_1 {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
      ∀ δ1 δ2,
        (|={⊤}=> Q (inl v1) δ1 (inl v2) δ2) ⊢ semWP2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q.
    Proof.
      iIntros (δ1 δ2) "HQ".
      by rewrite semWP2_unfold.
    Qed.

    (* TODO: doesn't hold (resources!) *)
    Lemma semWP2_val {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
      forall δ1 δ2,
        semWP2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q ⊣⊢ |={⊤}=> Q (inl v1) δ1 (inl v2) δ2.
    Proof.
      intros δ1 δ2.
      iSplit.
      - iIntros "H".
        rewrite semWP2_unfold. cbn. auto.
      - iApply semWP2_val_1.
    Qed.

    Lemma semWP2_fail {Γ1 Γ2 τ s1 s2} (Q : Post2 Γ1 Γ2 τ) :
      ∀ δ1 δ2,
        (|={⊤}=> Q (inr s1) δ1 (inr s2) δ2) ⊣⊢ semWP2 δ1 δ2 (stm_fail _ s1) (stm_fail _ s2) Q. 
    Proof.
      iIntros (δ1 δ2).
      iSplit.
      - iIntros "HQ".
        rewrite semWP2_unfold. auto.
      - iIntros "HQ".
        by rewrite semWP2_unfold.
    Qed.

    (* Lemma fupd_semWP2 {Γ1 Γ2 τ} E (δA : CStoreVal Γ1) (δB : CStoreVal Γ2) *)
    (*   (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) Φ :  *)
    (*   (|={E}=> semWP2 δA δB eA eB Φ) ⊢ semWP2 δA δB eA eB Φ. *)
    (* Proof. *)
    (*   unfold semWP2. iIntros "WP". *)
    (*   iApply fupd_wp. iMod (fupd_mask_subseteq E) as "Hclose"; first auto. *)
    (*   iMod "WP". iMod "Hclose" as "_". now iModIntro. *)
    (* Qed. *)

    Lemma semWP2_frame_l {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2) (POST : Post2 Γ1 Γ2 τ)
      (R : iProp Σ) :
      R ∗ semWP2 δ1 δ2 s1 s2 POST -∗
      semWP2 δ1 δ2 s1 s2 (λ v1 δ1 v2 δ2, R ∗ POST v1 δ1 v2 δ2).
    Proof.
      iIntros "(HR & H)".
      do 2 rewrite semWP2_unfold.
      cbn.
      destruct (stm_to_val s1); destruct (stm_to_val s2).
      - iFrame. auto.
      - auto.
      - auto.
      - iIntros (γ1 γ2 μ1 μ2) "Hres".
        iSpecialize ("H" with "Hres").
        iMod "H". iModIntro.
        iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 HStep).
        iSpecialize ("H" $!  _ _ _ _ _ _ _ _ HStep).
        iMod "H"; iModIntro. iModIntro. iMod "H". iModIntro. iMod "H". iModIntro.
        iDestruct "H" as "(Hres & H)".
        iFrame.
        iApply (semWP2_mono with "H").
        iIntros. iFrame.
    Qed.

    Ltac discriminate_step :=
      match goal with
      | H: ⟨ ?γ, ?μ, ?δ, stm_fail ?τ ?m ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s ⟩ |- _ =>
          inversion H
      | H: ⟨ ?γ, ?μ, ?δ, stm_val ?τ ?v ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s ⟩ |- _ =>
          inversion H
      end.

    Ltac close_later H :=
      iMod (fupd_mask_subseteq empty) as H; first set_solver.

    Ltac stm_val_fail_stuck :=
      repeat match goal with
        | H: ⟨ ?γ, ?μ, ?δ, ?s ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s' ⟩
          |- context[stm_to_val ?s] => rewrite (stm_val_stuck H)
        | H: ⟨ ?γ, ?μ, ?δ, ?s ⟩ ---> ⟨ ?γ', ?μ', ?δ', ?s' ⟩
          |- context[stm_to_fail ?s] => rewrite (stm_fail_stuck H)
        end.

    Lemma semWP2_exp {Γ1 Γ2 τ} (Φ : Post2 Γ1 Γ2 τ) eA eB δA δB :
      Φ (inl (evalVal eA δA)) δA (inl (evalVal eB δB)) δB ⊢ semWP2 δA δB (stm_exp eA) (stm_exp eB) Φ.
    Proof.
      iIntros "HΦ".
      rewrite semWP2_unfold.
      iIntros (γ1 γ2 μ1 μ2) "Hregs".
      iMod (@fupd_mask_subseteq _ _ ⊤ empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (Hstep1 & Hstep2)).
      destruct (smallinvstep Hstep1).
      destruct (smallinvstep Hstep2).
      do 3 iModIntro.
      iMod "Hclose" as "_". iModIntro.
      iFrame.
      iApply semWP2_val. iModIntro. iFrame.        
    Qed.

    (* TODO: move somewhere else? *)
    Ltac semWP2_stuck_progress :=
      repeat match goal with
        | H: ⟨ ?γ1, ?μ1, ?δ1, ?s ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s' ⟩
          |- context[stm_to_val ?s] =>
            rewrite (stm_val_stuck H)
        | H: ⟨ ?γ1, ?μ1, ?δ1, ?s ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s' ⟩
          |- context[stm_to_fail ?s] =>
            rewrite (stm_fail_stuck H)
        end.

    Lemma not_final_expanded : ∀ {Γ τ} (s : Stm Γ τ),
        ~ Final s -> stm_to_val s = None ∧ stm_to_fail s = None.
    Proof.
      intros Γ τ s H; unfold Final in H; destruct s; auto; contradiction.
    Qed.


    (* TODO: Ugly and incredly slow, ask Steven about slowness issue *)
    Lemma semWP2_call_frame {Γ1 Γ2 τ Δ} (δΔ1 δΔ2 : CStoreVal Δ) (s1 s2 : Stm Δ τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2  τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          semWP2 δΔ1 δΔ2 s1 s2 (fun v1 _ v2 _ => Q v1 δ1 v2 δ2) -∗
           semWP2 δ1 δ2 (stm_call_frame δΔ1 s1) (stm_call_frame δΔ2 s2) Q.
    Proof.
      iIntros (Q δΓ).
      iRevert (δΔ2 s2).
      iRevert (δΔ1 s1).
      iLöb as "IH". iIntros (δΔ1 s1 δΔ2 s2 δ2) "WPs".
      rewrite (semWP2_unfold _ _ (stm_call_frame δΔ1 s1)).
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      - rewrite !semWP2_val. by iFrame.
      - rewrite !semWP2_unfold. cbn. by iFrame.
      - destruct s; rewrite semWP2_unfold; cbn.
        { inversion H. }
        all: try solve [do 3 iModIntro; iMod "Hclose"; iMod "WPs"; auto].
        { inversion H. }
      - rewrite !semWP2_unfold. by iFrame.
      - rewrite <- !semWP2_fail. by iFrame.
      - destruct s0; rewrite semWP2_unfold; cbn.
        { inversion H. }
        all: try solve [do 3 iModIntro; iMod "Hclose"; iMod "WPs"; auto].
        { inversion H. }
      - destruct s; rewrite semWP2_unfold; cbn.
        { inversion H. }
        all: try solve [do 3 iModIntro; iMod "Hclose"; iMod "WPs"; auto].
        { inversion H. }
      - destruct s; rewrite semWP2_unfold; cbn.
        { inversion H. }
        all: try solve [do 3 iModIntro; iMod "Hclose"; iMod "WPs"; auto].
        { inversion H. }
      - assert (⟨ γ1, μ1, δΔ1, s ⟩ ---> ⟨ γ', μ', δΔ', s' ⟩ /\ ⟨ γ2, μ2, δΔ2, s0 ⟩ ---> ⟨ γ'0, μ'0, δΔ'0, s'0 ⟩) as step.
        { tauto. }
        rewrite (semWP2_unfold _ _ s).
        rewrite (stm_val_stuck H). rewrite (stm_val_stuck H0).
        (* rewrite (stm_fail_stuck H). rewrite (stm_fail_stuck H0). *)
        iSpecialize ("WPs" $! _ _ _ _ with "state_inv").
        iSpecialize ("WPs" $! _ _ _ _ _ _ _ _ step).
        iMod "Hclose". iMod "WPs". iMod "WPs".
        iModIntro. iModIntro.
        iMod "WPs". iMod "WPs".
        iMod (fupd_mask_subseteq empty) as "Hclose1"; first set_solver. iModIntro.
        iMod "Hclose1".
        iModIntro.
        iDestruct "WPs" as "(Hres & WPs)".
        iFrame.
        by iApply "IH".
    Qed.

    Lemma semWP2_call_inline_later {Γ1 Γ2 τ Δ} (f1 f2 : 𝑭 Δ τ)
      (es1 : NamedEnv (Exp Γ1) Δ) (es2 : NamedEnv (Exp Γ2) Δ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δΓ1 : CStoreVal Γ1) (δΓ2 : CStoreVal Γ2),
          ▷ semWP2 (evalVals es1 δΓ1) (evalVals es2 δΓ2) (FunDef f1) (FunDef f2) (λ v1τ _ v2τ _, Q v1τ δΓ1 v2τ δΓ2) -∗
          semWP2 δΓ1 δΓ2 (stm_call f1 es1) (stm_call f2 es2) Q.
    Proof.
      iIntros (Q δΓ1 δΓ2) "H".
      do 2 rewrite semWP2_unfold.
      iIntros (γ1 γ2 μ1 μ2) "Hres".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (Hstep1 & Hstep2)). destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
      iModIntro. iModIntro. iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame "Hres". iApply semWP2_call_frame.
      rewrite semWP2_unfold. auto.
    Qed.

    Lemma semWP2_call_inline {Γ1 Γ2 τ Δ} (f1 f2 : 𝑭 Δ τ)
      (es1 : NamedEnv (Exp Γ1) Δ) (es2 : NamedEnv (Exp Γ2) Δ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δΓ1 : CStoreVal Γ1) (δΓ2 : CStoreVal Γ2),
          semWP2 (evalVals es1 δΓ1) (evalVals es2 δΓ2) (FunDef f1) (FunDef f2) (λ v1τ _ v2τ _, Q v1τ δΓ1 v2τ δΓ2) -∗
          semWP2 δΓ1 δΓ2 (stm_call f1 es1) (stm_call f2 es2) Q.
    Proof. iIntros (? ? ?) "?". by iApply semWP2_call_inline_later. Qed.

    Lemma semWP2_bind {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ)
      (k1 : Val σ -> Stm Γ1 τ) (k2 : Val σ → Stm Γ2 τ) (Q : Post2 Γ1 Γ2 τ)
      (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2) :
      semWP2 δ1 δ2 s1 s2 (λ v1 δ12 v2 δ22, semWP2 δ12 δ22 (lift_cnt k1 v1) (lift_cnt k2 v2) Q) ⊢
        semWP2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
    Proof.
      iRevert (s1 s2 δ1 δ2). iLöb as "IH". iIntros (s1 s2 δ1 δ2) "WPs".
      rewrite (semWP2_unfold _ _ (stm_bind s1 k1)).
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      - rewrite !semWP2_val. do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite (semWP2_unfold _ _ (stm_val _ _)). cbn.
        do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite !semWP2_unfold.
        rewrite (stm_val_stuck H). cbn. do 3 iModIntro. iMod "Hclose". iMod "WPs".
        auto.
      - rewrite (semWP2_unfold _ _ _ (stm_val _ _)). cbn.
        do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite <- !semWP2_fail.
        rewrite semWP2_unfold. cbn.
        do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite (semWP2_unfold _ _ (stm_fail _ _)).
        rewrite (stm_val_stuck H). cbn. do 3 iModIntro. iMod "Hclose". iMod "WPs".
        auto.
      - rewrite (semWP2_unfold _ _ _ (stm_val _ _)).
        rewrite (stm_val_stuck H). cbn.
        do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
      - rewrite (semWP2_unfold _ _ _ (stm_fail _ _)).
        rewrite (stm_val_stuck H). cbn. do 3 iModIntro. iMod "Hclose". iMod "WPs".
        auto.
      - rewrite (semWP2_unfold _ _ s).
        rewrite (stm_val_stuck H). rewrite (stm_val_stuck H0).
        (* rewrite (stm_fail_stuck H). rewrite (stm_fail_stuck H0). *)
        iSpecialize ("WPs" $! γ1 γ2 μ1 μ2 with "state_inv").
        iMod "Hclose". iMod "WPs".
        assert (⟨ γ1, μ1, δ1, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩
                /\ ⟨ γ2, μ2, δ2, s0 ⟩ ---> ⟨ γ'0, μ'0, δ'0, s'0 ⟩) as step.
        { tauto. }
        iSpecialize ("WPs" $! s' δ' γ' μ' s'0 δ'0 γ'0 μ'0 step).
        iMod "WPs". iModIntro. iModIntro. iModIntro.
        iMod "WPs". iMod "WPs" as "[$ wps]".
        by iApply "IH".
    Qed.

    Lemma semWP2_block {Γ1 Γ2 τ Δ1 Δ2} (δΔ1 : CStoreVal Δ1) (δΔ2 : CStoreVal Δ2) (s1 : Stm (Γ1 ▻▻ Δ1) τ) (s2 : Stm (Γ2 ▻▻ Δ2) τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          semWP2 (δ1 ►► δΔ1) (δ2 ►► δΔ2) s1 s2 (fun v1 δ21 v2 δ22 => Q v1 (env.drop Δ1 δ21) v2 (env.drop Δ2 δ22)) -∗
          semWP2 δ1 δ2 (stm_block δΔ1 s1) (stm_block δΔ2 s2) Q.
    Proof.      
      iIntros (Q). iRevert (δΔ1 δΔ2 s1 s2). iLöb as "IH". iIntros (δΔ1 δΔ2 k1 k2 δΓ1 δΓ2) "WPk".
      rewrite (semWP2_unfold _ _ (stm_block δΔ1 k1)). cbn.
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      - rewrite !semWP2_val. rewrite !env.drop_cat. by iFrame.
      - rewrite !semWP2_unfold. cbn. rewrite !env.drop_cat. do 3 iModIntro. iMod "Hclose". iModIntro. by iFrame.
      - rewrite !semWP2_unfold. cbn. rewrite !env.drop_cat.
        rewrite (stm_val_stuck H). do 3 iModIntro. iMod "Hclose". iMod "WPk". auto.
      - rewrite !semWP2_unfold. cbn. rewrite !env.drop_cat. do 3 iModIntro. iMod "Hclose". iModIntro. by iFrame.
      - rewrite <- !semWP2_fail. rewrite env.drop_cat.
        do 3 iModIntro. iMod "Hclose". iMod "WPk". iModIntro. iFrame. iModIntro.
        rewrite !env.drop_cat. iFrame.
      - rewrite !semWP2_unfold. cbn. rewrite !env.drop_cat.
        rewrite (stm_val_stuck H). do 3 iModIntro. iMod "Hclose". iMod "WPk". auto.
      - rewrite !semWP2_unfold. cbn. rewrite !env.drop_cat.
        rewrite (stm_val_stuck H). do 3 iModIntro. iMod "Hclose". iMod "WPk". auto.
      - rewrite !semWP2_unfold. cbn. rewrite !env.drop_cat.
        rewrite (stm_val_stuck H). do 3 iModIntro. iMod "Hclose". iMod "WPk". auto.
      - rewrite (semWP2_unfold _ _ k).
        rewrite (stm_val_stuck H). rewrite (stm_val_stuck H0).
        (* rewrite (stm_fail_stuck H). rewrite (stm_fail_stuck H0). *)
        iSpecialize ("WPk" $! γ1 γ2 μ1 μ2 with "state_inv").
        iMod "Hclose". iMod "WPk" as "WPk".
        assert (⟨ γ1, μ1, δΓ1 ►► δΔ1, k ⟩ ---> ⟨ γ', μ', δ' ►► δΔ', k' ⟩ /\ ⟨ γ2, μ2, δΓ2 ►► δΔ2, k0 ⟩ ---> ⟨ γ'0, μ'0, δ'0 ►► δΔ'0, k'0 ⟩) as steps.
        { tauto. }
        iSpecialize ("WPk" $! _ _ _ _ _ _ _ _ steps). 
        iMod "WPk". iModIntro. iModIntro. iModIntro.
        iMod "WPk". iMod "WPk" as "[$ wps]".
        by iApply "IH".
    Qed.

    (* Lemma semWP2_call_frame {Γ1 Γ2 τ Δ} (δ1Δ δ2Δ : CStoreVal Δ) (s1 s2 : Stm Δ τ) : *)
    (*   ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2), *)
    (*       semWP2 δ1Δ δ2Δ s1 s2 (λ v1 _ v2 _, Q v1 δ1 v2 δ2) -∗ *)
    (*       semWP2 δ1 δ2 (stm_call_frame δ1Δ s1) (stm_call_frame δ2Δ s2) Q. *)
    (* Proof. *)
    (*   iIntros (Q δ1 δ2) "Hk". rewrite /semWP2. iIntros (γ21 μ21) "Hres". *)
    (*   iSpecialize ("Hk" with "Hres"). iApply semWP_call_frame. *)
    (*   iApply (semWP_mono with "Hk"). *)
    (*   iIntros (v1 _) "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hsteps & %Hval & Hregs & Hmem & H)". *)
    (*   iExists γ22, μ22, δ2, (of_ival v2), v2. *)
    (*   iFrame "Hregs Hmem H". iPureIntro. split. *)
    (*   - rewrite (stm_to_val_eq Hval) in Hsteps. *)
    (*     eapply (Steps_trans (Steps_call_frame Hsteps)). *)
    (*     destruct v2; eapply step_trans; simpl; constructor. *)
    (*   - apply stm_to_val_of_ival. *)
    (* Qed. *)

    Lemma semWP2_let {Γ1 Γ2 τ x σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ)
      (k1 : Stm (Γ1 ▻ x∷σ) τ) (k2 : Stm (Γ2 ▻ x∷σ) τ)
      (Q : Post2 Γ1 Γ2 τ) (δΓ1 : CStoreVal Γ1) (δΓ2 : CStoreVal Γ2) :
      ⊢ semWP2 δΓ1 δΓ2 s1 s2 (λ v1 δ12 v2 δ22, match v1, v2 with
                                             | inl v1, inl v2 => semWP2 δ12.[x∷σ ↦ v1] δ22.[x∷σ ↦ v2] k1 k2 (λ v12 δ13 v22 δ23, Q v12 (env.tail δ13) v22 (env.tail δ23))
                                               | inr m1, inl v2 => |={⊤}=> False
                                               | inl v1, inr m2 => |={⊤}=> False
                                             | inr m1, inr m2 => semWP2 δ12 δ22 (of_ival (inr m1)) (of_ival (inr m2)) Q 
                                             end) -∗
        semWP2 δΓ1 δΓ2 (let: x ∷ σ := s1 in k1)%exp (let: x ∷ σ := s2 in k2)%exp Q.
    Proof.
      iIntros "WPs".
      rewrite (semWP2_unfold _ _ (stm_let x σ s1 k1)). cbn.
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semWP2_bind. iApply (semWP2_mono with "WPs"). iIntros ([v1|m1] δ1 [v2|m2] δ2) "wpk".
      - simpl. iApply (semWP2_block [env].[_∷_ ↦ v1] [env].[_∷_ ↦ v2]).
        iApply (semWP2_mono with "wpk").
        clear. iIntros (? δ1 ? ?) "HQ". by destruct (env.view δ1).
      - simpl. rewrite semWP2_unfold. cbn. auto.
      - simpl. rewrite semWP2_unfold. cbn. auto.
      - simpl. done.
    Qed.

    Lemma semWP2_seq {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ)
      (k1 : Stm Γ1 τ) (k2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          semWP2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22,
              match v1, v2 with
              | inr m1, inr m2 => semWP2 δ21 δ22 (of_ival (inr m1)) (of_ival (inr m2)) Q
              | inr m1, inl v2 => semWP2 δ21 δ22 (of_ival (inr m1)) k2 Q
              | inl v1, inr m2 => semWP2 δ21 δ22 k1 (of_ival (inr m2)) Q
              | inl v1, inl v2 => semWP2 δ21 δ22 k1 k2 Q
              end) -∗
          semWP2 δ1 δ2 (s1;;k1)%exp (s2;;k2)%exp Q.
    Proof.
      iIntros (Q δ1 δ2) "WPs". rewrite (semWP2_unfold _ _ (stm_seq s1 k1)). cbn.
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semWP2_bind. iApply (semWP2_mono with "WPs"). iIntros ([v1|m1] δ1' [v2|m2] δ2').
      - simpl. iIntros "$".
      - simpl. now iIntros "H".
      - simpl. now iIntros "H".
      - simpl. now iIntros "H".
    Qed.

    Lemma semWP2_assertk {Γ1 Γ2 τ} (e11 : Exp Γ1 ty.bool) (e21 : Exp Γ2 ty.bool)
      (e12 : Exp Γ1 ty.string) (e22 : Exp Γ2 ty.string) (k1 : Stm Γ1 τ) (k2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          (⌜evalVal e11 δ1 = true⌝ → ⌜evalVal e21 δ2 = true⌝ → semWP2 δ1 δ2 k1 k2 Q) -∗
          (⌜evalVal e11 δ1 = false⌝ → ⌜evalVal e21 δ2 = true⌝ → semWP2 δ1 δ2 (fail (evalVal e12 δ1))%exp k2 Q) -∗
          (⌜evalVal e11 δ1 = true⌝ → ⌜evalVal e21 δ2 = false⌝ → semWP2 δ1 δ2 k1 (fail (evalVal e22 δ2))%exp Q) -∗
          (⌜evalVal e11 δ1 = false⌝ → ⌜evalVal e21 δ2 = false⌝ → semWP2 δ1 δ2 (fail (evalVal e12 δ1))%exp (fail (evalVal e22 δ2))%exp Q) -∗
          semWP2 δ1 δ2 (stm_assertk e11 e12 k1) (stm_assertk e21 e22 k2) Q.
    Proof.
     iIntros (Q δ1 δ2) "WPtt WPft WPtf WPff".
     rewrite (semWP2_unfold _ _ (stm_assertk e11 e12 k1)). cbn.
     iIntros (γ1 γ2 μ1 μ2) "state_inv".
     iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
     iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
     destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
     do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
     do 2 destruct evalVal.
     - by iApply "WPtt".
     - by iApply "WPtf".
     - by iApply "WPft".
     - by iApply "WPff".
    Qed.

    Lemma semWP2_read_register {Γ1 Γ2 τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          (∃ rv : RelVal τ, reg_pointsTo2 reg rv ∗ (reg_pointsTo2 reg rv -∗ Q (inl (ty.projLeft rv)) δ1 (inl (ty.projRight rv)) δ2)) -∗
          semWP2 δ1 δ2 (stm_read_register reg) (stm_read_register reg) Q.
    Proof.
      iIntros (Q δ1 δ2) "(%rv & Hreg & Hk)".
      rewrite semWP2_unfold. cbn.
      iIntros (γ1 γ2 μ1 μ2) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iDestruct (@reg_valid2 with "Hregs Hreg") as "(-> & ->)".
      iSpecialize ("Hk" with "Hreg"). iFrame "Hregs Hmem". by iApply semWP2_val.
    Qed.

    (* TODO: I think this doesn't matter that only a NonSyncVal version exists *)
    Lemma semWP2_write_register {Γ1 Γ2 τ} (reg : 𝑹𝑬𝑮 τ) (e1 : Exp Γ1 τ) (e2 : Exp Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          (∃ rv : RelVal τ, reg_pointsTo2 reg rv ∗ (reg_pointsTo2 reg (NonSyncVal (evalVal e1 δ1) (evalVal e2 δ2)) -∗ Q (inl (evalVal e1 δ1)) δ1 (inl (evalVal e2 δ2)) δ2)) -∗
          semWP2 δ1 δ2 (stm_write_register reg e1) (stm_write_register reg e2) Q.
    Proof.
      iIntros (Q δ1 δ2) "[% [Hreg HP]]".
      rewrite semWP2_unfold. cbn.
      iIntros (γ1 γ2 μ1 μ2) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iMod (reg_update2 γ1 γ2 reg rv (NonSyncVal (evalVal e1 δ1) (evalVal e2 δ2)) with "Hregs Hreg") as "[Hregs Hreg]".
      iModIntro. iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semWP2_val.
    Qed.

    Lemma semWP2_assign {Γ1 Γ2 τ x} (xInΓ1 : x∷τ ∈ Γ1) (xInΓ2 : x∷τ ∈ Γ2)
      (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          semWP2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22,
              match v1, v2 with
              | inl v1, inl v2 => Q (inl v1) (δ21 ⟪ x ↦ v1 ⟫) (inl v2) (δ22 ⟪ x ↦ v2 ⟫)
              | inl v1, inr m2 => Q (inl v1) (δ21 ⟪ x ↦ v1 ⟫) v2 δ22
              | inr m1, inl v2 => Q v1 δ21 (inl v2) (δ22 ⟪ x ↦ v2 ⟫)
              | inr m1, inr m2 => Q v1 δ21 v2 δ22
              end) -∗
          semWP2 δ1 δ2 (stm_assign x s1) (stm_assign x s2) Q.
    Proof.
      iIntros (Q). iRevert (s1 s2). iLöb as "IH". iIntros (s1 s2 δ1 δ2) "WPs".
      rewrite (semWP2_unfold _ _ (stm_assign x s1)). cbn.
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      - rewrite !semWP2_val. by iFrame.
      - rewrite !semWP2_unfold. cbn.
        do 3 iModIntro. iMod "Hclose". iMod "WPs". iModIntro.
        by iFrame.
      - rewrite !semWP2_unfold. cbn. rewrite (stm_val_stuck H).
        do 3 iModIntro. iMod "Hclose". iMod "WPs". iModIntro.
        done.
      - rewrite !semWP2_unfold. cbn.
        do 3 iModIntro. iMod "Hclose". iMod "WPs". iModIntro.
        by iFrame.
      - rewrite <- !semWP2_fail. by iFrame.
      - rewrite !semWP2_unfold. cbn. rewrite (stm_val_stuck H).
        do 3 iModIntro. iMod "Hclose". iMod "WPs". iModIntro.
        done.
      - rewrite !semWP2_unfold. cbn. rewrite (stm_val_stuck H).
        do 3 iModIntro. iMod "Hclose". iMod "WPs". iModIntro.
        done.
      - rewrite !semWP2_unfold. cbn. rewrite (stm_val_stuck H).
        do 3 iModIntro. iMod "Hclose". iMod "WPs". iModIntro.
        done.
      - rewrite (semWP2_unfold _ _ s).
        rewrite (stm_val_stuck H). rewrite (stm_val_stuck H0).
        (* rewrite (stm_fail_stuck H). rewrite (stm_fail_stuck H0). *)
        iSpecialize ("WPs" $! γ1 γ2 μ1 μ2 with "state_inv").
        iMod "Hclose". iMod "WPs".
        assert (⟨ γ1, μ1, δ1, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ /\ ⟨ γ2, μ2, δ2, s0 ⟩ ---> ⟨ γ'0, μ'0, δ'0, s'0 ⟩) as steps.
        { tauto. }
        iSpecialize ("WPs" $! _ _ _ _ _ _ _ _ steps).
        iMod "WPs". iModIntro. iModIntro. iModIntro.
        iMod "WPs". iMod "WPs" as "[$ wps]".
        by iApply "IH".
    Qed.

    Lemma semWP2_pattern_match {Γ1 Γ2 τ σ} (s1 : Stm Γ1 σ) (s2 : Stm Γ2 σ) (pat : Pattern σ)
      (rhs1 : ∀ pc : PatternCase pat, Stm (Γ1 ▻▻ PatternCaseCtx pc) τ)
      (rhs2 : ∀ pc : PatternCase pat, Stm (Γ2 ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Post2 Γ1 Γ2 τ) (δ1 : CStoreVal Γ1) (δ2 : CStoreVal Γ2),
          semWP2 δ1 δ2 s1 s2
            (λ vσ1 δ12 vσ2 δ22,
              match vσ1, vσ2 with
              | inl vσ1, inl vσ2 =>
                  let (pc1,δpc1) := pattern_match_val pat vσ1 in
                  let (pc2,δpc2) := pattern_match_val pat vσ2 in
                  semWP2 (δ12 ►► δpc1) (δ22 ►► δpc2) (rhs1 pc1) (rhs2 pc2)
                    (λ vτ1 δ21 vτ2 δ22, Q vτ1 (env.drop (PatternCaseCtx pc1) δ21) vτ2 (env.drop (PatternCaseCtx pc2) δ22))
              | inr mσ1, inl vσ2 => |={⊤}=> False
              | inl vσ1, inr mσ2 => |={⊤}=> False
              | inr mσ1, inr mσ2 =>
                  semWP2 δ12 δ22 (stm_fail _ mσ1) (stm_fail _ mσ2) Q
              end
            ) -∗
          semWP2 δ1 δ2 (stm_pattern_match s1 pat rhs1) (stm_pattern_match s2 pat rhs2) Q.
    Proof.
      iIntros (Q δ1 δ2) "WPs".
      rewrite (semWP2_unfold _ _ (stm_pattern_match s1 pat rhs1)). cbn.
      iIntros (γ1 γ2 μ1 μ2) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 (step1 & step2)).
      destruct (smallinvstep step1); destruct (smallinvstep step2); cbn.
      do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
      iApply semWP2_bind. iApply (semWP2_mono with "WPs"). iIntros ([v1|m1] δ1' [v2|m2] δ2') "WPrhs".
      - simpl.
        destruct pattern_match_val as [pc1 δpc1]. destruct pattern_match_val as [pc2 δpc2].
        iApply (semWP2_block δpc1).
        iApply (semWP2_mono with "WPrhs").
        iIntros ([v1'|m1'] ? ? ?) "H"; simpl; auto.
      - rewrite (semWP2_unfold _ _ _ (fail _)). cbn.
        destruct pattern_match_val. cbn. auto.
      - rewrite (semWP2_unfold _ _ (fail _)). cbn.
        destruct pattern_match_val. cbn. auto.
      - simpl. now rewrite <- semWP2_fail.
    Qed.

    Lemma semWp2_foreign {Γ Δ τ} {f1 f2 : 𝑭𝑿 Δ τ} {es1 es2 : NamedEnv (Exp Γ) Δ} {Q δ1 δ2} :
      ⊢ (∀ γ1 γ2 μ1 μ2,
            (regs_inv2 γ1 γ2 ∗ mem_inv2 μ1 μ2)
            ={⊤,∅}=∗
                     (∀ res1 γ1' μ1' res2 γ2' μ2',
                         ⌜ ForeignCall f1 (evalVals es1 δ1) res1 γ1 γ1' μ1 μ1' ⌝
                           ∗ ⌜ ForeignCall f2 (evalVals es2 δ2) res2 γ2 γ2' μ2 μ2' ⌝
                         ={∅}▷=∗
                                 |={∅,⊤}=>
                        (regs_inv2 γ1' γ2' ∗ mem_inv2 μ1' μ2') ∗
                          semWP2 δ1 δ2 (match res1 with inr v => stm_val _ v
                                                   | inl s => stm_fail _ s
                                        end)
                          (match res2 with inr v => stm_val _ v
                                      | inl s => stm_fail _ s
                           end)
                          Q)) -∗
                                 semWP2 δ1 δ2 (stm_foreign f1 es1) (stm_foreign f2 es2) Q.
    Proof.
      iIntros "H". rewrite semWP2_unfold. iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
      iMod ("H" with "[$]") as "H". iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
      destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
      by iMod ("H" $! _ _ _ _ _ _ (conj H H0)) as "H".
    Qed.

    Lemma semWP2_debugk {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ Q δ1 δ2, semWP2 δ1 δ2 s1 s2 Q -∗ semWP2 δ1 δ2 (stm_debugk s1) (stm_debugk s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "WPs". rewrite (semWP2_unfold _ _ (stm_debugk s1)).
      iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
      destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
      now iFrame.
    Qed.

    Lemma semWP2_lemmak {Γ1 Γ2 τ} {Δ} (l1 l2 : 𝑳 Δ) (es1 : NamedEnv (Exp Γ1) Δ)
      (es2 : NamedEnv (Exp Γ2) Δ) (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
      ⊢ ∀ Q δ1 δ2, semWP2 δ1 δ2 s1 s2 Q -∗ semWP2 δ1 δ2 (stm_lemmak l1 es1 s1) (stm_lemmak l2 es2 s2) Q.
    Proof.
      iIntros (Q δ1 δ2) "WPs". rewrite (semWP2_unfold _ _ (stm_lemmak l1 es1 s1)).
      iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
      destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
      now iFrame.
    Qed.

    (* Lemma semWP2_focus {Γ1 Γ2 τ} {s1 : Stm Γ1 τ} {s2 : Stm Γ2 τ} : *)
    (*   ⊢ ∀ Q1 Q2 Q δ1 δ2, *)
    (*       @semTWP _ sailGS2_sailGS_left _ _ δ1 s1 Q1 -∗ *)
    (*       @semTWP _ sailGS2_sailGS_right _ _ δ2 s2 Q2 -∗ *)
    (*       (∀ v1 δ1 v2 δ2, Q1 v1 δ1 ∗ Q2 v2 δ2 -∗ Q v1 δ1 v2 δ2) -∗ *)
    (*       semWP2 δ1 δ2 s1 s2 Q. *)
    (* Proof. *)
    (*   iIntros (Q1 Q2 Q δ1 δ2) "HTWP1 HTWP2 H". rewrite /semWP2. *)
    (*   iIntros (γ21 μ21) "Hres". iApply semWP_fupd. *)
    (*   iPoseProof (semTWP_semWP with "HTWP1") as "HWP1". *)
    (*   iPoseProof (semTWP_Steps with "[Hres] HTWP2") as "H2". *)
    (*   { iDestruct "Hres" as "($ & $)". } *)
    (*   iApply (semWP_mono with "HWP1"). iIntros (v1 δ1') "HQ1". *)
    (*   iMod "H2" as "(%γ22 & %μ22 & %δ2' & %s2' & %v2 & %Hstep & %Hs2' & Hreg & Hmem & HQ2)". *)
    (*   iModIntro. iExists γ22, μ22, δ2', (of_ival v2), v2. iFrame "Hreg Hmem". *)
    (*   iDestruct ("H" with "[$HQ1 $HQ2]") as "$". iPureIntro. *)
    (*   split; last apply stm_to_val_of_ival. rewrite (stm_to_val_eq Hs2') in Hstep. *)
    (*   auto. *)
    (* Qed. *)

    (* Lemma semWP2_focus_seq {Γ1 Γ2 τ} {s1 : Stm Γ1 τ} {s2 : Stm Γ2 τ} : *)
    (*   ⊢ ∀ Q δ1 δ2, *)
    (*       @semTWP _ sailGS2_sailGS_left _ _ δ1 s1 (λ v1 δ1, *)
    (*           @semTWP _ sailGS2_sailGS_right _ _ δ2 s2 *)
    (*             (λ v2 δ2, Q v1 δ1 v2 δ2)) -∗ *)
    (*       semWP2 δ1 δ2 s1 s2 Q. *)
    (* Proof. *)
    (*   iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres". *)
    (*   iApply semWP_fupd. *)
    (*   iPoseProof (semTWP_semWP with "H") as "H". iApply (semWP_mono with "H"). *)
    (*   iIntros (v1 δ1') "H". now iApply (semTWP_Steps with "[Hres] H"). *)
    (* Qed. *)

    (* Lemma semWP2_anaglyph {Γ1 Γ2 τ} {s1 : Stm Γ1 τ} {s2 : Stm Γ2 τ} : *)
    (*   ⊢ ∀ Q δ1 δ2, *)
    (*       @semWP _ sailGS2_sailGS_left _ _ δ1 s1 (λ v1 δ1, *)
    (*           @semTWP _ sailGS2_sailGS_right _ _ δ2 s2 *)
    (*                   (λ v2 δ2, Q v1 δ1 v2 δ2)) -∗ *)
    (*       semWP2 δ1 δ2 s1 s2 Q. *)
    (* Proof. *)
    (*   iIntros (Q δ1 δ2) "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres". *)
    (*   iApply semWP_fupd. *)
    (*   iApply (semWP_mono with "H"). iIntros (v1 δ1') "H". *)
    (*   now iApply (semTWP_Steps with "[Hres] H"). *)
    (* Qed. *)

  End WithSailGS2.
End IrisBinaryWP.

Module Type IrisSignatureRules2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB2   : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB2).

  Module Export IWP := IrisBinaryWP B SIG PROG SEM IB2 IPred.

  Section WithSailGS2.
  Context `{sG : sailGS2 Σ}.

Section Soundness.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : RelVal τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗
    semWP2 (projLeftCStore δ) (projRightCStore δ) s s
    (λ v1 δ1 v2 δ2, ∃ δ',  ⌜ projLeftCStore δ' = δ1 /\ projRightCStore δ' = δ2 ⌝ ∗
      match v1 , v2 with
      | inl v1 , inl v2 => ∃ rv,  ⌜ ty.projLeft rv = v1 /\ ty.projRight rv = v2 ⌝ ∗ POST rv δ'
      | inr m1 , inl v2 => False%I
      | inl v1 , inr m2 => False%I
      | inr m1 , inr m2 => True%I
      end)%I.
  (* always modality needed? perhaps not because sail not higher-order? *)
  Global Arguments semTriple {Γ} {τ} δ PRE%_I s%_exp POST%_I.

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
        {P P'} {Q Q' : RelVal σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "Htriple P".
    iApply (semWP2_mono with "[Htriple P]").
    - iApply "Htriple".
      now iApply PP.
    - iIntros ([v1|m1] δ1 [v2|m2] δ2) "(%δ' & %defδ & H)".
      + iDestruct "H" as "(%rv & defRv & QQ)".
        iExists δ'.
        iSplit. { auto. }
        iExists rv.
        iFrame.
        by iApply QQ.
      + auto.
      + auto.
      + iExists (zipCStoreVal δ1 δ2). rewrite projLeftZipCStoreVal projRightZipCStoreVal.
        iFrame.
        iPureIntro.
        tauto.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : RelVal σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "Htriple [HR HP]".
    iSpecialize ("Htriple" with "HP").
    iPoseProof (semWP2_frame_l with "[HR Htriple]") as "Hwp".
    { iSplitL "HR". iExact "HR". iExact "Htriple". }
    iApply (semWP2_mono with "Hwp").
    iIntros ([] ? ? ?) "(R & (%δ' & (<- & <-) & H))"; auto.
    iExists δ'.
    iSplit.
    - iPureIntro. tauto.
    - destruct v2.
      + now iFrame "R H".
      + auto.
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : RelVal σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ -∗ semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R).
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q : RelVal σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q).
  Proof.
    iIntros "Htriple [% P]".
    by iApply "Htriple".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : RelVal τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (ty.valToRelVal v) δ)%I -∗ semTriple δ P (stm_val τ v) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP2_val_1.
    iSpecialize ("PQ" with "P").
    iModIntro.
    iExists δ.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : RelVal τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP2_exp.
    iSpecialize ("PQ" with "P").
    iExists δ.
    iSplit.
    - iPureIntro. tauto.
    - iExists (eval e δ).
      rewrite evalValProjLeftIsProjLeftEval.
      rewrite evalValProjRightIsProjRightEval.
    iFrame.
    iPureIntro. tauto.
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : PVar) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : RelVal σ -> CStore Γ -> iProp Σ)
        (R : RelVal τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
            (∀ (rv : RelVal σ) (δ' : CStore Γ),
               semTriple (env.snoc δ' (x∷σ) rv) (Q rv δ') k (fun rv δ'' => R rv (env.tail δ''))) -∗
               semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "Hs Hk P".
    iApply semWP2_let.
    iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs").
    iIntros ([v1|m1] δ1 [v2|m2] δ2) "(%δ' & (<- & <-) & Q)".
    - iDestruct "Q" as "(%rv & (<- & <-) & Q)".
      iSpecialize ("Hk" $! rv δ' with "Q").
      iApply (semWP2_mono with "Hk").
      iIntros (? ? ? ?) "(%δ'0 & (<- & <-) & R)".
      env.destroy δ'0.
      iExists δ'0.
      by iFrame "R".
    - auto.
    - auto.
    - simpl. iApply semWP2_fail. auto.
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStoreVal Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : RelVal τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► (env.map (fun _ => ty.valToRelVal) δΔ)) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
            semTriple δ P (stm_block δΔ k) R).
  Proof.
    iIntros "Hk P". iApply semWP2_block. iSpecialize ("Hk" with "P").
    rewrite projLeftCStoreCatIsCatOfProjLeftCStore projRightCStoreCatIsCatOfProjRightCStore.
    rewrite projLeftCStoreEnvMapValToRelValIsId projRightCStoreEnvMapValToRelValIsId.
    iApply (semWP2_mono with "Hk"). iIntros (? ? ? ?) "(%δ' & (<- & <-) & R)".
    iExists (env.drop Δ δ').
    rewrite projLeftCStoreEnvDropIsEnvDropProjLeftCStore projRightCStoreEnvDropIsEnvDropProjRightCStore.
    by iFrame "R".
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : RelVal τ -> CStore Γ -> iProp Σ) (R : RelVal σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple δ P s1 Q -∗
      (∀ v δ', semTriple δ' (Q v δ') s2 R) -∗
      semTriple δ P (s1 ;; s2) R.
  Proof.
    iIntros "Hs Hk P". iApply semWP2_seq. iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs"). iIntros (v1 δ1 v2 δ2) "(%δ' & (<- & <-) & Q)".
    destruct v1 as [v1|m1]; destruct v2 as [v2|m2]; simpl.
    - iDestruct "Q" as "(%rv & (<- & <-) & Q)". now iSpecialize ("Hk" with "Q").
    - auto.
    - auto.
    - iApply semWP2_fail. iModIntro. iExists δ'. auto.
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : RelVal τ -> CStore Γ -> iProp Σ) :
    ⊢ (∃ v, ⌜ eval e1 δ = SyncVal v ⌝) -∗
      (⌜eval e1 δ = ty.valToRelVal (σ := ty.bool) true⌝ -∗ semTriple δ P k Q) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
    iIntros "(%v & %eq) Hk P".
    destruct v eqn:Ee1.
      + iSpecialize ("Hk" with "[] P"); auto.
      iApply (semWP2_assertk with "[Hk]");
      rewrite evalValProjLeftIsProjLeftEval evalValProjRightIsProjRightEval !eq;
      cbn;
        iIntros (H1e H2e);
        try (rewrite H1e in H2e, Ee1; discriminate);
        auto.
      congruence.
      + iApply (semWP2_assertk with "[Hk]");
          rewrite evalValProjLeftIsProjLeftEval evalValProjRightIsProjRightEval !eq;
          cbn;
          iIntros (H1e H2e);
          try congruence.
        iApply semWP2_fail. auto.
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
    (τ : Ty) (s : Val ty.string) :
    forall {Q : RelVal τ -> CStore Γ -> iProp Σ},
      ⊢ semTriple δ True (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    iApply semWP2_fail.
    iExists δ. auto.
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (rv : RelVal σ) :
    ⊢ (semTriple δ (lptsreg r rv) (stm_read_register r)
         (λ rv' δ', ⌜δ' = δ⌝ ∧ ⌜rv' = rv⌝ ∧ lptsreg r rv)).
  Proof.
    iIntros "H". iApply semWP2_read_register. iExists rv.
    iFrame. iIntros "H".
    iExists δ.
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : RelVal σ -> CStore Γ -> iProp Σ)
                              (rv : RelVal σ) :
        ⊢ semTriple δ (lptsreg r rv) (stm_write_register r w)
            (λ v' δ',
              ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
  Proof.
    iIntros "H". iApply semWP2_write_register. iExists rv.
    iFrame. iIntros "H".
    iExists δ. iSplit. auto. iExists (eval w δ).
    rewrite evalValProjLeftIsProjLeftEval evalValProjRightIsProjRightEval.
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : RelVal σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R).
  Proof.
    iIntros "Hk P". iApply semWP2_assign. iSpecialize ("Hk" with "P").
    iApply (semWP2_mono with "Hk").
    iIntros (? ? ? ?) "(%δ' & (<- & <-) & R)".
    destruct v1 as [v1|m1]; destruct v2 as [v2|m2]; auto.
    iDestruct "R" as "(%rv & (<- & <-) & R)".
    iExists (δ' ⟪ x ↦ rv ⟫).
    rewrite projLeftCStoreEnvUpdateIsEnvUpdateProjLeftCStore projRightCStoreEnvUpdateIsEnvUpdateProjRightCStore.
    iSplit.
    - auto.
    - iExists rv. auto.
  Qed.

  (* Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ) *)
  (*       {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ) *)
  (*       (Q : RelVal σ -> CStore Γ -> iProp Σ) *)
  (*       (R : RelVal τ -> CStore Γ -> iProp Σ) : *)
  (*       ⊢ semTriple δ True (stm_bind s k) R. *)
  (* Proof. *)
  (*   iIntros "_". *)
  (*   iApply semWP2_bind. *)
  (*   iExists δ. *)
  (* Qed. *)

  Lemma iris_rule_stm_fail' {Γ} (δ : CStore Γ)
    (τ : Ty) (s : Val ty.string) :
    forall {Q : RelVal τ -> CStore Γ -> iProp Σ},
      ⊢ semTriple δ True (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    iApply semWP2_fail.
    iExists δ. auto.
  Qed.

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : RelVal σ -> CStore Γ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hk P". iApply semWP2_call_inline_later. iModIntro.
    iSpecialize ("Hk" with "P").
    rewrite evalValsProjLeftIsProjLeftEvals evalValsProjRightIsProjRightEvals.
    iApply (semWP2_mono with "Hk").
    iIntros (? ? ? ?) "(%δ & (<- & <-) & H)".
    iExists δΓ.
    now iFrame "H".
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : RelVal σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hk". now iApply iris_rule_stm_call_inline_later.
  Qed.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : RelVal τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q).
  Proof.
    iIntros "Hk P". iApply semWP2_debugk. iApply ("Hk" with "P").
  Qed.

  (* Lemma iris_rule_noop {Γ σ} {δ : CStore Γ} *)
  (*       {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} : *)
  (*   stm_to_val s = None -> *)
  (*   (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ -> *)
  (*                           (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\ *)
  (*                             (forall {γ2 μ2} {δ2 : CStore Γ}, ⟨ γ2, μ2, δ2, s ⟩ ---> ⟨ γ2, μ2, δ2, s' ⟩) /\ *)
  (*                           ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) -> *)
  (*   (∀ v, P ={⊤}=∗ Q v δ) -∗ *)
  (*                semTriple δ P s Q. *)
  (* Proof. *)
  (*   iIntros (Hnv Hnoop) "HPQ HP". rewrite /semWP2. iIntros (γ21 μ21) "(Hreg2 & Hmem2)". *)
  (*   rewrite <-semWP_unfold_nolc. rewrite Hnv. iIntros (γ11 μ11) "Hres1". *)
  (*   iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. *)
  (*   iIntros "!>" (s12 δ12 γ12 μ12 Hs). *)
  (*   destruct (Hnoop _ _ _ _ _ _ Hs) as (-> & -> & -> & Hs2 & [[v ->]|[msg ->]]). *)
  (*   - do 3 iModIntro. iMod "Hclose" as "_". *)
  (*     iFrame. iModIntro. iApply semWP_val. *)
  (*     iExists γ21, μ21, δ, (of_ival (inl v)), (inl v). *)
  (*     iMod ("HPQ" $! v with "HP") as "$". repeat iModIntro. *)
  (*     iFrame "Hreg2 Hmem2". repeat iSplit; auto. iPureIntro. eapply step_trans. *)
  (*     apply Hs2. apply step_refl. *)
  (*   - do 3 iModIntro. iMod "Hclose" as "_". iFrame "Hres1". *)
  (*     iModIntro. iApply semWP_fail. *)
  (*     repeat iModIntro. iExists γ21, μ21, δ, (of_ival (inr msg)), (inr msg). *)
  (*     iFrame "Hreg2 Hmem2". repeat iSplit; auto. iPureIntro. *)
  (*     eapply step_trans. apply Hs2. simpl. apply step_refl. *)
  (* Qed. *)

  Lemma iris_rule_stm_pattern_match {Γ τ σ} (δΓ : CStore Γ)
    (s : Stm Γ σ) (pat : Pattern σ)
    (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ)
    (P : iProp Σ) (Q : RelVal σ → CStore Γ → iProp Σ) (R : RelVal τ → CStore Γ → iProp Σ) :
    ⊢ semTriple δΓ P s (fun rv δ => ⌜secLeak rv⌝ ∗ Q rv δ) -∗
      (∀ pc δpc δΓ1,
                semTriple (δΓ1 ►► δpc) (Q (pattern_match_relval_reverse pat pc δpc) δΓ1) (rhs pc)
                  (λ vτ (δ' : CStore (Γ ▻▻ PatternCaseCtx pc)), R vτ (env.drop (PatternCaseCtx pc) δ'))) -∗
      semTriple δΓ P (stm_pattern_match s pat rhs) R.
  Proof.
    iIntros "Hs Hk P". iApply semWP2_pattern_match. iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs").
    iIntros (v1 δ1 v2 δ2) "(%δ & (<- & <-) & Q)".
    destruct v1 as [v1|m1]; destruct v2 as [v2|m2].
    - iDestruct "Q" as "(%rv & (<- & <-) & %secLeakRv & Q)".
      unfold secLeak in secLeakRv.
      destruct rv; try contradiction.
      cbn in *.
      destruct (pattern_match_val pat v) as [pc δpc] eqn:Ev.
      iSpecialize ("Hk" $! pc (env.map (fun _ => SyncVal) δpc) δ with "[Q]").
      + rewrite pattern_match_relval_reverse_syncNamedEnvIsSync.
        change (pattern_match_val_reverse pat pc δpc) with (pattern_match_val_reverse' pat (existT pc δpc)).
        rewrite <- Ev. now rewrite pattern_match_val_inverse_left.
      + rewrite !projLeftCStoreCatIsCatOfProjLeftCStore !projRightCStoreCatIsCatOfProjRightCStore.
        rewrite projLeftCStoreEnvMapValToRelValIsId projRightCStoreEnvMapValToRelValIsId.
        iApply (semWP2_mono with "Hk").
        iIntros (? ? ? ?) "(%δ' & (<- & <-) & R)".
        iExists (env.drop (PatternCaseCtx pc) δ').
        rewrite projLeftCStoreEnvDropIsEnvDropProjLeftCStore projRightCStoreEnvDropIsEnvDropProjRightCStore.
        now iFrame "R".
    - auto.
    - auto.
    - iApply semWP2_fail.
      now iExists δ.
  Qed.

  Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      Sep.Logic.Forall (fun (ι : Valuation ctxΣ) =>
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
    end.

  Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      ∀ (ι : Valuation ctxΣ),
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
          (λ v δ, asn.interpret post (env.snoc ι (result∷σ) v))
    end.

  Definition ValidContractForeign {Δ τ} (contract : SepContract Δ τ) (f : 𝑭𝑿 Δ τ) : Prop :=
    forall Γ (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match contract with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : Valuation Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (asn.interpret req ι) (stm_foreign f es)
          (λ v δ', asn.interpret ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
      end.

  Definition valid_contract_curry {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
    ValidContractSem body contract ⊣⊢ ValidContractSemCurried body contract.
  Proof.
    destruct contract as [lvars δ req res ens]; cbn.
    now rewrite Forall_forall.
  Qed.

End Soundness.
End WithSailGS2.

End IrisSignatureRules2.
