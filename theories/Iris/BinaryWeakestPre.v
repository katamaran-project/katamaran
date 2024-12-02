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
     Iris.Instance
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
  Parameter luser_inst2 : forall `{sRG : sailRegGS2 Σ} `{invGS Σ} `{mG : memGS2 Σ} (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst2 : forall `{sRG : sailRegGS2 Σ} `{invGS Σ} {mG : memGS2 Σ} (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
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
      {| lptsreg σ r v        := reg_pointsTo2 r v v;
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

    Definition Post2 Γ1 Γ2 τ :=
      Val τ -> CStore Γ1 -> Val τ -> CStore Γ2 -> iProp Σ.
    Canonical Structure Post2O Γ1 Γ2 τ := leibnizO (Post2 Γ1 Γ2 τ).

    Definition Wp2 Γ1 Γ2 τ :=
      CStore Γ1 -d> CStore Γ2 -d>
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
    Ltac f_equiv_more_arities := match goal with
                                 | H:_ ?f ?g |- ?R (?f ?x ?y ?z1) (?g ?x ?y ?z1) => solve [ simple apply H ]
                                 | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2) (?g ?x ?y ?z1 ?z2) => solve [ simple apply H ]
                                 | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3) (?g ?x ?y ?z1 ?z2 ?z3) => solve [ simple apply H ]
                                 end.

    Ltac solve_contractive_more_arities := solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | f_equiv_more_arities]).

    Import SmallStepNotations.

    Definition semWP2 {Γ1 Γ2 τ} : Wp2 Γ1 Γ2 τ :=
      let sG_left    := sailGS2_sailGS_left in
      let srGS_right := sailRegGS2_sailRegGS_right in
      let mG_right   := memGS2_memGS_right in
      (λ δ1 δ2 s1 s2 Q,
        ∀ γ21 μ21,
          regs_inv (srGS := srGS_right) γ21 ∗ mem_inv (mG := mG_right) μ21 -∗
            semWP (sG := sG_left) s1 (λ v1 δ1',
              ∃ γ22 μ22 δ2' v2,
                ⌜⟨ γ21, μ21, δ2, s2 ⟩ --->* ⟨ γ22, μ22, δ2', stm_val τ v2 ⟩⌝
                ∗ regs_inv (srGS := srGS_right) γ22 ∗ mem_inv (mG := mG_right) μ22
                ∗ Q v1 δ1' v2 δ2'
          ) δ1)%I.

    Lemma semWP2_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (Q1 Q2 : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
      ⊢ semWP2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWP2 δ1 δ2 s1 s2 Q2.
    Proof.
      iIntros "Hwp H". rewrite /semWP2.
      iIntros (γ21 μ21) "Hres". iSpecialize ("Hwp" with "Hres").
      iApply (semWP_mono with "Hwp").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %v2 & Hk)".
      iExists γ22, μ22, δ2', v2. iDestruct "Hk" as "($ & $ & $ & HQ1)".
      by iApply ("H" with "HQ1").
    Qed.

    Lemma semWP2_val_1 {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
      ∀ δ1 δ2,
        (|={⊤}=> Q v1 δ1 v2 δ2) ⊢ semWP2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q.
    Proof.
      iIntros (δ1 δ2) "HQ". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      rewrite semWP_val. iMod "HQ". iModIntro. iExists γ21, μ21, δ2, v2.
      iFrame "HQ Hres". iPureIntro. apply step_refl.
    Qed.

    (* TODO: doesn't hold (resources!) *)
    Lemma semWP2_val {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
      forall δ1 δ2,
        semWP2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q ⊣⊢ |={⊤}=> Q v1 δ1 v2 δ2.
    Abort.

    Lemma fupd_semWP2 {Γ1 Γ2 τ} E (δA : CStore Γ1) (δB : CStore Γ2)
      (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) Φ : 
      (|={E}=> semWP2 δA δB eA eB Φ) ⊢ semWP2 δA δB eA eB Φ.
    Admitted.

    Lemma semWP2_step_fupd {Γ1 Γ2 τ} (δA : CStore Γ1) (δB : CStore Γ2)
      (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) (P :iProp Σ) Φ : 
      to_val {| conf_stm := eA; conf_store := δA |} = None ->
      to_val {| conf_stm := eB; conf_store := δB |} = None ->
      P -∗
      semWP2 δA δB eA eB (λ v1 δA v2 δB, P -∗ Φ v1 δA v2 δB) -∗
      semWP2 δA δB eA eB Φ.
    Admitted.

    Lemma semWP2_frame_l {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (δ1 : CStore Γ1) (δ2 : CStore Γ2) (POST : Post2 Γ1 Γ2 τ)
      (R : iProp Σ) :
      R ∗ semWP2 δ1 δ2 s1 s2 POST -∗
      semWP2 δ1 δ2 s1 s2 (λ v1 δ1 v2 δ2, R ∗ POST v1 δ1 v2 δ2).
    Proof.
      iIntros "(HR & H)". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply (semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %v2 & H)".
      iExists γ22, μ22, δ2', v2. now iDestruct "H" as "($ & $ & $ & $)".
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

    Lemma semWP2_exp {Γ τ} (Φ : Post2 Γ Γ τ) eA eB δA δB :
      Φ (eval eA δA) δA (eval eB δB) δB ⊢ semWP2 δA δB (stm_exp eA) (stm_exp eB) Φ.
    Admitted.

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

    Lemma stm_to_val_not_fail {Γ τ} {s : Stm Γ τ} :
      forall {v}, stm_to_val s = Some v -> stm_to_fail s = None.
    Proof. intros; by destruct s. Qed.

    Lemma semWP2_bind {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
      (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
      semWP2 δ1 δ2 s1 s2 (λ v1 δ12 v2 δ22, semWP2 δ12 δ22 (k1 v1) (k2 v2) Q) ⊢
        semWP2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
    Proof.
      iIntros "H". rewrite /semWP2. iIntros (γ21 μ21) "Hres".
      iSpecialize ("H" with "Hres"). iApply semWP_bind.
      iApply (semWP_mono with "H").
      iIntros (v1 δ1') "(%γ22 & %μ22 & %δ2' & %v2 & %Hsteps & Hregs & Hmem & H)".
      iSpecialize ("H" with "[$Hregs $Hmem]"). iApply (semWP_mono with "H").
      iIntros (v1' δ1'') "(%γ23 & %μ23 & %δ2'' & %v2' & H)".
      iExists γ23, μ23, δ2'', v2'. iDestruct "H" as "(%Hsteps' & $ & $ & $)".
      iPureIntro. apply (Steps_bind Hsteps Hsteps').
    Qed.

    Lemma semWP2_block {Γ1 Γ2 τ Δ1 Δ2} (δΔ1 : CStore Δ1) (δΔ2 : CStore Δ2) (s1 : Stm (Γ1 ▻▻ Δ1) τ) (s2 : Stm (Γ2 ▻▻ Δ2) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ1 → Val τ → CStore Γ2 → iProp Σ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
          semWP2 (δ1 ►► δΔ1) (δ2 ►► δΔ2) s1 s2 (fun v1 δ21 v2 δ22 => Q v1 (env.drop Δ1 δ21) v2 (env.drop Δ2 δ22)) -∗
                                                                                                                     semWP2 δ1 δ2 (stm_block δΔ1 s1) (stm_block δΔ2 s2) Q.
    Proof.
    Admitted.

    Lemma semWP2_let {Γ τ x σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm (Γ ▻ x∷σ) τ)
      (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
      ⊢ semWP2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWP2 δ12.[x∷σ ↦ v1] δ22.[x∷σ ↦ v2] k1 k2 (fun v12 δ13 v22 δ23 => Q v12 (env.tail δ13) v22 (env.tail δ23)) ) -∗
                                                                                                                                                                  semWP2 δ1 δ2 (let: x ∷ σ := s1 in k1)%exp (let: x ∷ σ := s2 in k2)%exp Q.
    Proof.
    Admitted.

    Lemma semWP2_seq {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm Γ τ) :
      ⊢ ∀ (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ),
          semWP2 δ1 δ2 s1 s2 (fun v1 δ21 v2 δ22 => semWP2 δ21 δ22 k1 k2 Q) -∗ semWP2 δ1 δ2 (s1;;k1)%exp (s2;;k2)%exp Q.
    Proof.
    Admitted.

    Lemma semWP2_assertk {Γ τ} (e11 e21 : Exp Γ ty.bool) (e12 e22 : Exp Γ ty.string) (k1 k2 : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
          ⌜eval e11 δ1 = eval e21 δ2⌝ -∗
                                         (⌜eval e11 δ1 = true⌝ → ⌜eval e21 δ2 = true⌝ → semWP2 δ1 δ2 k1 k2 Q) -∗
                                                                                                                 semWP2 δ1 δ2 (stm_assertk e11 e12 k1) (stm_assertk e21 e22 k2) Q.
    Proof.
    Admitted.

    Lemma semWP2_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
          (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg v1 v2 -∗ Q v1 δ1 v2 δ2)) -∗
                                                                                                     semWP2 δ1 δ2 (stm_read_register reg) (stm_read_register reg) Q.
    Proof.
    Admitted.

    Lemma semWP2_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e1 e2 : Exp Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
          (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg (eval e1 δ1) (eval e2 δ2) -∗ Q (eval e1 δ1) δ1 (eval e2 δ2) δ2)) -∗
                                                                                                                                             semWP2 δ1 δ2 (stm_write_register reg e1) (stm_write_register reg e2) Q.
    Proof.
    Admitted.

    (* TODO: notation for cstore update not working? (import env.notations doesn't solve it) Investigate and define lemma *)
    (* Lemma semWP2_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s1 s2 : Stm Γ τ) : *)
    (*   ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ), *)
    (*       semWP2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22, Q v1 (δ21 ⟪ x ↦ v1 ⟫) v2 (δ22 ⟪ x ↦ v2 ⟫)) -∗ *)
    (*       semWP2 δ1 δ2 (stm_assign x s1) (stm_assign x s2) Q. *)
    (* Proof. *)
    (* Admitted. *)

    Lemma semWP2_pattern_match {Γ τ σ} (s1 s2 : Stm Γ σ) (pat : Pattern σ)
      (rhs1 rhs2 : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
          semWP2 δ1 δ2 s1 s2
            (fun vσ1 δ12 vσ2 δ22 =>
               let (pc1,δpc1) := pattern_match_val pat vσ1 in
               let (pc2,δpc2) := pattern_match_val pat vσ2 in
               semWP2 (δ12 ►► δpc1) (δ22 ►► δpc2) (rhs1 pc1) (rhs2 pc2)
                 (fun vτ1 δ21 vτ2 δ22 => Q vτ1 (env.drop (PatternCaseCtx pc1) δ21) vτ2 (env.drop (PatternCaseCtx pc2) δ22))
            ) -∗
                 semWP2 δ1 δ2 (stm_pattern_match s1 pat rhs1) (stm_pattern_match s2 pat rhs2) Q.
    Proof.
    Admitted.

    Lemma semWP2_foreign {Γ Δ τ} {f1 f2 : 𝑭𝑿 Δ τ} {es1 es2 : NamedEnv (Exp Γ) Δ} {Q δ1 δ2} :
      ⊢ (∀ γ1 γ2 μ1 μ2,
            (regs_inv2 γ1 γ2 ∗ mem_inv2 μ1 μ2)
            ={⊤,∅}=∗
                     (∀ res1 γ1' μ1' res2 γ2' μ2',
                         ⌜ ForeignCall f1 (evals es1 δ1) res1 γ1 γ1' μ1 μ1' ⌝
                           ∗ ⌜ ForeignCall f2 (evals es2 δ2) res2 γ2 γ2' μ2 μ2' ⌝
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
    Admitted.

    Lemma semWP2_debugk {Γ τ} (s1 s2 : Stm Γ τ) :
      ⊢ ∀ Q δ1 δ2, semWP2 δ1 δ2 s1 s2 Q -∗ semWP2 δ1 δ2 (stm_debugk s1) (stm_debugk s2) Q.
    Proof.
    Admitted.

    Lemma semWP2_lemmak {Γ τ} {Δ} (l1 l2 : 𝑳 Δ) (es1 es2 : NamedEnv (Exp Γ) Δ) (s1 s2 : Stm Γ τ) :
      ⊢ ∀ Q δ1 δ2, semWP2 δ1 δ2 s1 s2 Q -∗ semWP2 δ1 δ2 (stm_lemmak l1 es1 s1) (stm_lemmak l2 es2 s2) Q.
    Proof.
    Admitted.
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
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗
           semWP2 δ δ s s (fun v1 δ1 v2 δ2 => ⌜ v1 = v2 ⌝ ∗ ⌜ δ1 = δ2 ⌝ ∗ POST v1 δ1)%I.
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
    iIntros (PP QQ) "Htriple P".
    iApply (semWP2_mono with "[Htriple P]").
    - iApply "Htriple".
      now iApply PP.
    - iIntros (v1 δ1 v2 δ2) "(-> & -> & Q')".
      iPoseProof (QQ with "Q'") as "Q"; auto.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "Htriple [HR HP]".
    iSpecialize ("Htriple" with "HP").
    iPoseProof (semWP2_frame_l with "[HR Htriple]") as "Hwp".
    { iSplitL "HR". iExact "HR". iExact "Htriple". }
    iApply (semWP2_mono with "Hwp").
    iIntros (? ? ? ?) "($ & $ & $ & $)".
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
    iIntros "Htriple [% P]".
    by iApply "Htriple".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q v δ)%I -∗ semTriple δ P (stm_val τ v) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP2_val.
    iSpecialize ("PQ" with "P").
    iModIntro; by iFrame.
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP2_exp.
    iSpecialize ("PQ" with "P").
    now iFrame.
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
    iIntros "Hs Hk P".
    iApply semWP2_let.
    iSpecialize ("Hs" with "P").
    iApply (semWP2_mono with "Hs").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & Q)".
    iSpecialize ("Hk" $! v1 δ1 with "Q").
    iApply (semWP2_mono with "Hk").
    iIntros (? ? ? ?) "(<- & <- & R)".
    by iFrame"R".
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
                   semTriple δ P (stm_block δΔ k) R).
  Proof.
  Admitted.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R).
  Proof.
  Admitted.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜ eval e1 δ = true ⌝ → semTriple δ P k Q) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
  Admitted.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Val ty.string) :
        forall (Q : Val τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True (stm_fail τ s) Q.
  Proof.
  Admitted.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v)).
  Proof.
  Admitted.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
  Proof.
  Admitted.

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R).
  Proof.
  Admitted.

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Val σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R).
  Proof.
    iIntros "trips tripk P".
    iSpecialize ("trips" with "P").
    iApply semWP2_bind.
    iApply (semWP2_mono with "trips").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & HR)".
    now iApply ("tripk" with "HR").
  Qed.

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
  Admitted.

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
  Admitted.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q).
  Proof.
  Admitted.

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    stm_to_val s = None ->
    stm_to_fail s = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                              (forall {s2 : Stm Γ σ} {γ2 μ2} {δ2 : CStore Γ}, ⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2, μ2, δ2, s' ⟩) /\
                            ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
  Admitted.

  Lemma iris_rule_stm_pattern_match {Γ τ σ} (δΓ : CStore Γ)
    (s : Stm Γ σ) (pat : Pattern σ)
    (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ)
    (P : iProp Σ) (Q : Val σ → CStore Γ → iProp Σ) (R : Val τ → CStore Γ → iProp Σ) :
    ⊢ semTriple δΓ P s Q -∗
      (∀ pc δpc δΓ1,
         semTriple (δΓ1 ►► δpc) (Q (pattern_match_val_reverse pat pc δpc) δΓ1) (rhs pc)
           (λ vτ (δ' : CStore (Γ ▻▻ PatternCaseCtx pc)), R vτ (env.drop (PatternCaseCtx pc) δ'))) -∗
      semTriple δΓ P (stm_pattern_match s pat rhs) R.
  Proof.
  Admitted.

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

  Definition valid_contract_curry {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
    ValidContractSem body contract ⊣⊢ ValidContractSemCurried body contract.
  Proof.
    destruct contract as [lvars δ req res ens]; cbn.
    now rewrite Forall_forall.
  Qed.

End Soundness.
End WithSailGS2.

End IrisSignatureRules2.
