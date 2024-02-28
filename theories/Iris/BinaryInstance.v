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
     Iris.Model
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

Module Type IrisParameters2
  (Import B    : Base).

  Parameter Inline memGS2 : gFunctors -> Set.
  Existing Class memGS2.
  Parameter mem_inv2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.
End IrisParameters2.

Module Type IrisResources2
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IP   : IrisParameters2 B)
  (Import IPre : IrisPrelims B PROG SEM).

  Class sailRegGS2 Σ := SailRegGS2 {
                            sailRegGS2_sailRegGS_left : sailRegGS Σ;
                            sailRegGS2_sailRegGS_right : sailRegGS Σ;
                          }.
  Class sailGS2 Σ := SailGS2 { (* resources for the implementation side *)
                       sailGS2_invGS : invGS Σ; (* for fancy updates, invariants... *)
                       sailGS2_regGS2 : sailRegGS2 Σ;
                       (* ghost variable for tracking user-defined state *)
                       sailGS2_memGS : memGS2 Σ;
                     }.

  #[export] Existing Instance sailGS2_invGS.
  #[export] Existing Instance sailGS2_regGS2.
  #[export] Existing Instance sailGS2_memGS.

  Definition regs_inv2 `{sailRegGS2 Σ} γ1 γ2 := (regs_inv (srGS := sailRegGS2_sailRegGS_left) γ1 ∗ regs_inv (srGS := sailRegGS2_sailRegGS_right) γ2)%I.
  Definition mem_inv2_sail `{sailGS2 Σ} μ1 μ2 := @mem_inv2 _ (sailGS2_memGS) μ1 μ2.

  Definition reg_pointsTo2 `{sailRegGS2 Σ} {τ} : 𝑹𝑬𝑮 τ → Val τ → Val τ → iProp Σ :=
    fun reg v1 v2 =>
    (@reg_pointsTo _ sailRegGS2_sailRegGS_left _ reg v1 ∗ @reg_pointsTo _ sailRegGS2_sailRegGS_right _ reg v2)%I.

  #[export] Program Instance sailGS2_irisGS2 `{sailGS2 Σ} {Γ1 Γ2 τ} : irisGS2 (microsail_lang Γ1 τ) (microsail_lang Γ2 τ) Σ :=
    {|
      iris_invGS2 := sailGS2_invGS;
      state_interp2 σ1 σ2 κ := (regs_inv2 σ1.1 σ2.1 ∗ mem_inv2_sail σ1.2 σ2.2)%I;
      num_laters_per_step2 := fun _ => 0
    |}.
  Next Obligation.
    iIntros (Σ sG Γ1 Γ2 τ σ1 σ2 ns) "((Hreg1 & Hreg2) & Hmem)".
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
  IrisParameters2 B <+ IrisPrelims B PROG SEM <+ IrisResources2 B PROG SEM.

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

Module Type IrisSignatureRules2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB).
Section Soundness.

  Import SmallStepNotations.

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

  Definition Post Γ1 Γ2 τ :=
    Val τ -> CStore Γ1 -> Val τ -> CStore Γ2 -> iProp Σ.
  Canonical Structure PostO Γ1 Γ2 τ := leibnizO (Post Γ1 Γ2 τ).

  (* TODO: these don't need to be "-n>", but discrete? *)
  Definition Wp {Γ1 Γ2 τ} :=
    CStore Γ1 -d> CStore Γ2 -d>
    Stm Γ1 τ -d> Stm Γ2 τ -d>
    Post Γ1 Γ2 τ -d>
    iProp Σ.

  Definition semWp2_fix {Γ1 Γ2 τ}
    (wp : Wp) : Wp :=
    (λ (δ1 : CStore Γ1) (δ2 : CStore Γ2)
         (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
         (POST : Post Γ1 Γ2 τ),
      match stm_to_val s1, stm_to_val s2 with
      | Some v1, Some v2 => |={⊤}=> POST v1 δ1 v2 δ2
      | Some v1, None    => |={⊤}=> False
      | None   , Some v2 => |={⊤}=> False
      | None   , None    =>
          match stm_to_fail s1, stm_to_fail s2 with
          | Some m1, Some m2 => |={⊤}=> True
          | Some m1, None    => |={⊤}=> False
          | None   , Some m2 => |={⊤}=> False
          | None   , None    =>
              (∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
                  (regs_inv2 γ1 γ2 ∗ mem_inv2_sail μ1 μ2
                   ={⊤,∅}=∗ (∀ (s12 : Stm Γ1 τ) (δ12 : CStore Γ1)
                               (γ12 : RegStore) (μ12 : Memory)
                               (s22 : Stm Γ2 τ) (δ22 : CStore Γ2)
                               (γ22 : RegStore) (μ22 : Memory),
                                ⌜⟨ γ1, μ1, δ1 , s1 ⟩ ---> ⟨ γ12, μ12, δ12, s12 ⟩⌝
                                ∗ ⌜⟨ γ2, μ2, δ2 , s2 ⟩ ---> ⟨ γ22, μ22, δ22, s22 ⟩⌝
                                ={∅}▷=∗
                                |={∅,⊤}=> 
                                         (regs_inv2 γ12 γ22 ∗ mem_inv2_sail μ12 μ22) ∗
                                         wp δ12 δ22 s12 s22 POST)))
          end
      end)%I.
  Global Arguments semWp2_fix {_ _}%ctx_scope {_} wp /.

  Ltac f_equiv_more_arities := match goal with
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1) (?g ?x ?y ?z1) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2) (?g ?x ?y ?z1 ?z2) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3) (?g ?x ?y ?z1 ?z2 ?z3) => solve [ simple apply H ]
  end.

  Ltac solve_contractive_more_arities := solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | f_equiv_more_arities]).

  Global Instance semWp2_fix_Contractive {Γ1 Γ2 τ} :
    Contractive (@semWp2_fix Γ1 Γ2 τ).
  Proof.
    unfold Wp.
    solve_contractive_more_arities.
  Qed.

  Definition semWp2 {Γ1 Γ2 τ} : Wp :=
    λ δ1 δ2 s1 s2 POST, (fixpoint (@semWp2_fix Γ1 Γ2 τ)) δ1 δ2 s1 s2 POST.

  Lemma fixpoint_semWp2_fix_eq {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (POST : Post Γ1 Γ2 τ) :
    fixpoint semWp2_fix δ1 δ2 s1 s2 POST ≡ semWp2_fix (fixpoint semWp2_fix) δ1 δ2 s1 s2 POST.
  Proof. exact: (fixpoint_unfold semWp2_fix δ1 δ2 s1 s2 POST). Qed.

  Lemma fixpoint_semWp2_eq {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (POST : Post Γ1 Γ2 τ) :
    semWp2 δ1 δ2 s1 s2 POST ≡ semWp2_fix semWp2 δ1 δ2 s1 s2 POST.
  Proof. by unfold semWp2; rewrite fixpoint_semWp2_fix_eq. Qed.

  Lemma semWp2_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (Q1 Q2 : Val τ → CStore Γ1 → Val τ → CStore Γ2 → iProp Σ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    ⊢ semWp2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWp2 δ1 δ2 s1 s2 Q2.
  Proof.
    iIntros "H HQ".
    iLöb as "IH" forall (δ1 δ2 s1 s2).
    rewrite (fixpoint_semWp2_eq _ _ s1).
    rewrite (fixpoint_semWp2_eq _ _ s1).
    cbn.
    repeat case_match; try done.
    - iMod "H".
      iModIntro.
      iApply ("HQ" with "H").
    - iIntros (γ1 γ2 μ1 μ2) "Hresources".
      iMod ("H" with "Hresources") as "H".
      iModIntro.
      iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "[%Hstep1 %Hstep2]".
      iMod ("H" $! _ _ _ _ _ _ _ _ (conj Hstep1 Hstep2)) as "H".
      iIntros "!> !>".
      iMod "H".
      iModIntro.
      iMod "H".
      iModIntro.
      iDestruct "H" as "($ & H)".
      iApply ("IH" with "H HQ").
  Qed.

  Lemma semWp2_val {Γ1 Γ2 τ} (v1 : Val τ) e2 (Q : Val τ → CStore Γ1 → Val τ → CStore Γ2 → iProp Σ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    semWp2 δ1 δ2 (stm_val τ v1) e2 Q ⊣⊢ |={⊤}=> ∃ v2, ⌜ e2 = stm_val τ v2 ⌝ ∗ Q v1 δ1 v2 δ2.
  Proof.
    rewrite fixpoint_semWp2_eq; cbn.
    case_match eqn:Ee2;
      iSplit; iIntros "H"; iMod "H"; iModIntro.
    - iExists v.
      iFrame "H".
      destruct e2; try discriminate; iPureIntro.
      by inversion Ee2.
    - iDestruct "H" as "(%v2 & -> & HQ)".
      by inversion Ee2.
    - done.
    - by iDestruct "H" as "(% & -> & _)".
  Qed.

  Lemma semWp2_val' {Γ τ} (Φ : Val τ -> CStore Γ -> Val τ -> CStore Γ -> iProp Σ) vA vB δA δB :
    Φ vA δA vB δB ⊢ semWp2 δA δB (stm_val _ vA) (stm_val _ vB) Φ.
  Proof. rewrite semWp2_val. iIntros "HΦ !>". iExists vB.
         now iFrame "HΦ".
  Qed.

  Lemma semWp2_fail_1 {Γ1 Γ2 τ s} Q (δ1 : CStore Γ1) (δ2 : CStore Γ2) s2 :
      semWp2 δ1 δ2 (stm_fail τ s) s2 Q ={⊤}=∗
      ⌜ exists m, stm_to_fail s2 = Some m ⌝.
  Proof.
    rewrite fixpoint_semWp2_eq. cbn. iIntros "H".
    repeat case_match; iMod "H"; auto.
    iModIntro.
    iPureIntro.
    by exists s0.
  Qed.

  Lemma semWp2_fail_2 {Γ1 Γ2 τ s} Q (δ1 : CStore Γ1) (δ2 : CStore Γ2) s2 m :
    stm_to_fail s2 = Some m -> ⊢ semWp2 δ1 δ2 (stm_fail τ s) s2 Q.
  Proof.
    iIntros (eqs2f) "".
    rewrite fixpoint_semWp2_eq; cbn.
    rewrite eqs2f.
    case_match;
      iModIntro; iPureIntro; auto.
    destruct s2; discriminate.
  Qed.

  Lemma fupd_semWp2 {Γ1 Γ2 τ} E (δA : CStore Γ1) (δB : CStore Γ2)
    (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) Φ : 
    (|={E}=> semWp2 δA δB eA eB Φ) ⊢ semWp2 δA δB eA eB Φ.
  Proof.
    rewrite fixpoint_semWp2_eq; cbn; unfold semWp2_fix.
    iIntros "H".
    repeat case_match;
      iMod (fupd_mask_subseteq E) as "Hclose"; auto;
      iMod "H";
      iMod "Hclose";
      iApply "H".
  Qed.

  Lemma semWp2_step_fupd {Γ1 Γ2 τ} (δA : CStore Γ1) (δB : CStore Γ2)
    (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) (P :iProp Σ) Φ : 
    to_val {| conf_stm := eA; conf_store := δA |} = None ->
    to_val {| conf_stm := eB; conf_store := δB |} = None ->
    P -∗
    semWp2 δA δB eA eB (λ v1 δA v2 δB, P -∗ Φ v1 δA v2 δB) -∗
    semWp2 δA δB eA eB Φ.
  Proof.
    rewrite ?fixpoint_semWp2_eq; cbn.
    iIntros (HeA HeB) "HP".
    repeat case_match;
      inversion HeA;
      inversion HeB; iIntros "H";
      try done.
    iIntros (? ? ? ?) "Hres".
    iMod ("H" with "Hres") as "H".
    iModIntro.
    iIntros (? ? ? ? ? ? ? ?) "%Hstep".
    iSpecialize ("H" $! s12 δ12 γ12 μ12 s22 δ22 γ22 μ22 Hstep).
    iMod "H".
    iIntros "!> !>".
    iMod "H".
    iModIntro.
    iMod "H".
    iModIntro.
    iDestruct "H" as "($ & H)".
    iApply (semWp2_mono with "H").
    iIntros (v1 δ1 v2 δ2) "H".
    by iApply "H".
  Qed.
    
  Lemma semWp2_exp {Γ τ} (Φ : Val τ -> CStore Γ -> Val τ -> CStore Γ -> iProp Σ) eA eB δA δB :
    Φ (eval eA δA) δA (eval eB δB) δB ⊢ semWp2 δA δB (stm_exp eA) (stm_exp eB) Φ.
  Proof.
    rewrite fixpoint_semWp2_eq; cbn.
    iIntros "HΦ" (γ11 γ21 μ11 μ21) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "[%Hstep1 %Hstep2]".
    iIntros "!> !>".
    iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    destruct (smallinvstep Hstep1).
    destruct (smallinvstep Hstep2).
    iFrame "Hregs Hmem".
    now iApply semWp2_val'.
  Qed.

  (* TODO: move somewhere else? *)
  Ltac semWp2_stuck_progress :=
    repeat match goal with
      | H: ⟨ ?γ1, ?μ1, ?δ1, ?s ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s' ⟩
        |- context[stm_to_val ?s] =>
          rewrite (stm_val_stuck H)
      | H: ⟨ ?γ1, ?μ1, ?δ1, ?s ⟩ ---> ⟨ ?γ2, ?μ2, ?δ2, ?s' ⟩
        |- context[stm_to_fail ?s] =>
          rewrite (stm_fail_stuck H)
      end.

  Ltac semWp2_progress s :=
    rewrite (fixpoint_semWp2_eq _ _ s); cbn;
    semWp2_stuck_progress.

  Lemma semWp2_call_frame {Γ τ Δ} (δΔA δΔB : CStore Δ) (sA sB : Stm Δ τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δA δB : CStore Γ),
        semWp2 δΔA δΔB sA sB (fun vA _ vB _ => Q vA δA vB δB) -∗
        semWp2 δA δB (stm_call_frame δΔA sA) (stm_call_frame δΔB sB) Q.
  Proof.
    iIntros (Q δA δB). iRevert (δΔA δΔB sA sB Q). iLöb as "IH". iIntros (δΔA δΔB sA sB Q) "WPs".
    rewrite (fixpoint_semWp2_eq _ _ (stm_call_frame δΔA sA)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "[%Hstep1 %Hstep2]".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    - iPoseProof (semWp2_val with "WPs") as "WPs".
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      iMod "WPs" as "(%v2 & %Heq & HQ)".
      inversion Heq; subst.
      iFrame "Hregs Hmem".
      iModIntro.
      iApply semWp2_val.
      iModIntro.
      iExists v2.
      iSplitR; done.
    - iPoseProof (semWp2_val with "WPs") as "WPs".
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      iMod "WPs" as "(%v2 & %Heq & HQ)".
      inversion Heq.
    - rewrite fixpoint_semWp2_eq; cbn.
      semWp2_stuck_progress.
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      by iMod "WPs".
    - iPoseProof (semWp2_fail_1 with "WPs") as "WPs".
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      iMod "WPs" as "(%m & %Heq)".
      inversion Heq.
    - iPoseProof (semWp2_fail_1 with "WPs") as "WPs".
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      iMod "WPs" as "(%m & %Heq)".
      iModIntro.
      iFrame "Hregs Hmem".
      by iApply semWp2_fail_2.
    - rewrite fixpoint_semWp2_eq; cbn.
      semWp2_stuck_progress.
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      by iMod "WPs".
    - semWp2_progress s.
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      by iMod "WPs".
    - semWp2_progress s.
      iIntros "!> !>".
      iModIntro.
      iMod "Hclose" as "_".
      by iMod "WPs".
    - semWp2_progress s.
      iSpecialize ("WPs" $! γ1 γ2 μ1 μ2).
      iSpecialize ("WPs" with "[Hregs Hmem]");
        first iFrame.
      iMod "Hclose" as "_".
      iMod "WPs".
      iSpecialize ("WPs" $! _ _ _ _ _ _ _ _ (conj H H0)).
      iMod "WPs".
      iIntros "!> !>".
      iMod "WPs".
      iModIntro.
      iMod "WPs".
      iModIntro.
      iDestruct "WPs" as "($ & H)".
      iApply ("IH" with "H").
  Qed.

  Lemma semWp2_call_inline_later {Γ τ Δ} (f1 f2 : 𝑭 Δ τ) (es1 es2 : NamedEnv (Exp Γ) Δ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δΓ1 δΓ2 : CStore Γ),
        ▷ semWp2 (evals es1 δΓ1) (evals es2 δΓ2) (FunDef f1) (FunDef f2) (fun v1 _ v2 _ => Q v1 δΓ1 v2 δΓ2) -∗
        semWp2 δΓ1 δΓ2 (stm_call f1 es1) (stm_call f2 es2) Q.
  Proof.
    iIntros (Q δΓ1 δΓ2) "wpbody". rewrite (fixpoint_semWp2_eq _ _ (stm_call f1 es1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); cbn.
    iModIntro. iModIntro. iModIntro. iMod "Hclose" as "_". iModIntro.
    destruct (smallinvstep Hstep2); cbn.
    iFrame "Hregs Hmem".
    by iApply semWp2_call_frame.
  Qed.

  Lemma semWp2_call_inline {Γ τ Δ} (f1 f2 : 𝑭 Δ τ) (es1 es2 : NamedEnv (Exp Γ) Δ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δΓ1 δΓ2 : CStore Γ),
        semWp2 (evals es1 δΓ1) (evals es2 δΓ2) (FunDef f1) (FunDef f2) (fun v1 _ v2 _ => Q v1 δΓ1 v2 δΓ2) -∗
        semWp2 δΓ1 δΓ2 (stm_call f1 es1) (stm_call f2 es2) Q.
  Proof. iIntros (Q δΓ1 δΓ2) "wpbody". by iApply semWp2_call_inline_later. Qed.

  Lemma semWp2_bind {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
    (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12 δ22 (k1 v1) (k2 v2) Q) ⊢
      semWp2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
  Proof.
    iRevert (s1 s2 δ1 δ2).
    iLöb as "IH".
    iIntros (s1 s2 δ1 δ2) "Hs".
    rewrite (fixpoint_semWp2_eq _ _ (stm_bind _ _)).
    cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (@fupd_mask_subseteq _ _ ⊤ empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    - rewrite semWp2_val.
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      iMod "Hs" as "(%v2 & %Heq & Hk)".
      iModIntro.
      inversion Heq; subst.
      now iFrame "Hregs Hmem".
    - rewrite semWp2_val.
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      iMod "Hs" as "(%v2 & %Heq & Hk)".
      inversion Heq.
    - rewrite semWp2_val.
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      iMod "Hs" as "(%v2 & -> & Hk)".
      inversion H.
    - iIntros "!> !> !>".
      iMod "Hclose" as "_".
      iPoseProof (semWp2_fail_1 with "Hs") as "Hs".
      iMod "Hs" as "(%m & %Heq)".
      inversion Heq.
    - iPoseProof (semWp2_fail_1 with "Hs") as "Hs".
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      iMod "Hs" as "(%m & %Heq)".
      iModIntro.
      iFrame "Hregs Hmem".
      now iApply semWp2_fail_2.
    - iPoseProof (semWp2_fail_1 with "Hs") as "Hs".
      apply stm_fail_stuck in H.
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      iMod "Hs" as "(%m & %Heq)".
      now rewrite H in Heq.
    - semWp2_progress s.
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      by iMod "Hs".
    - semWp2_progress s.
      iIntros "!> !> !>".
      iMod "Hclose" as "_".
      by iMod "Hs".
    - semWp2_progress s.
      iSpecialize ("Hs" with "[Hregs Hmem]");
        first by iFrame.
      iMod "Hclose" as "_".
      iMod "Hs".
      iSpecialize ("Hs" $! _ _ _ _ _ _ _ _ (conj H H0)).
      iMod "Hs".
      iIntros "!> !>".
      iMod "Hs".
      iModIntro.
      iMod "Hs" as "($ & Hs)".
      iModIntro.
      by iApply ("IH" with "Hs").
  Qed.

  Lemma semWp2_block {Γ1 Γ2 τ Δ1 Δ2} (δΔ1 : CStore Δ1) (δΔ2 : CStore Δ2) (s1 : Stm (Γ1 ▻▻ Δ1) τ) (s2 : Stm (Γ2 ▻▻ Δ2) τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ1 → Val τ → CStore Γ2 → iProp Σ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
        semWp2 (δ1 ►► δΔ1) (δ2 ►► δΔ2) s1 s2 (fun v1 δ21 v2 δ22 => Q v1 (env.drop Δ1 δ21) v2 (env.drop Δ2 δ22)) -∗
        semWp2 δ1 δ2 (stm_block δΔ1 s1) (stm_block δΔ2 s2) Q.
  Proof.
    iIntros (Q). iRevert (δΔ1 s1 δΔ2 s2).
    iLöb as "IH". iIntros (δΔ1 s1 δΔ2 s2 δΓ1 δΓ2) "WPk".
    rewrite (fixpoint_semWp2_eq _ _ (stm_block δΔ1 s1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    - rewrite !semWp2_val. rewrite ?env.drop_cat.
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPk" as "(%v2 & %Heq & HQ)". iModIntro.
      iFrame "Hregs Hmem".
      iModIntro.
      inversion Heq; subst.
      iExists _; iSplitR; done.
    - iPoseProof (semWp2_val with "WPk") as "WPk".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPk" as "(%v2 & %Heq & HQ)".
      inversion Heq.
    - iPoseProof (semWp2_val with "WPk") as "WPk".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPk" as "(%v2 & %Heq & HQ)".
      apply stm_val_stuck in H.
      by rewrite Heq in H.
    - iPoseProof (semWp2_fail_1 with "WPk") as "WPk".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPk" as "(%m & %Heq)".
      inversion Heq.
    - iPoseProof (semWp2_fail_1 with "WPk") as "WPk".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPk" as "(%m & %Heq)".
      iModIntro.
      iFrame "Hregs Hmem".
      by iApply semWp2_fail_2.
    - iPoseProof (semWp2_fail_1 with "WPk") as "WPk".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPk" as "(%m & %Heq)".
      apply stm_fail_stuck in H.
      by rewrite Heq in H.
    - semWp2_progress k.
      iIntros "!> !> !>". iMod "Hclose" as "_".
      by iMod "WPk".
    - semWp2_progress k.
      iIntros "!> !> !>". iMod "Hclose" as "_".
      by iMod "WPk".
    - semWp2_progress k.
      iSpecialize ("WPk" with "[Hregs Hmem]"); first by iFrame.
      iMod "Hclose" as "_".
      iMod "WPk".
      iSpecialize ("WPk" $! _ _ _ _ _ _ _ _ (conj H H0)).
      iMod "WPk".
      iIntros "!> !>".
      iMod "WPk".
      iModIntro.
      iMod "WPk".
      iModIntro.
      iDestruct "WPk" as "($ & WPk)".
      by iApply ("IH" with "WPk").
  Qed.
  (* TODO: got rid of dependent induction, can close the issue on GH :) *)

  Lemma semWp2_let {Γ τ x σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm (Γ ▻ x∷σ) τ)
    (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ) :
    ⊢ semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12.[x∷σ ↦ v1] δ22.[x∷σ ↦ v2] k1 k2 (fun v12 δ13 v22 δ23 => Q v12 (env.tail δ13) v22 (env.tail δ23)) ) -∗
        semWp2 δ1 δ2 (let: x ∷ σ := s1 in k1)%exp (let: x ∷ σ := s2 in k2)%exp Q.
  Proof.
    rewrite (fixpoint_semWp2_eq _ _ (stm_let _ _ _ _)); cbn.
    iIntros "Hs" (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (@fupd_mask_subseteq _ _ ⊤ empty) as "Hclose"; first set_solver.
    iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    iIntros "!> !> !>".
    iMod "Hclose" as "_". iModIntro.
    iFrame "Hregs Hmem".
    iApply semWp2_bind.
    iApply (semWp2_mono with "Hs").
    iIntros (v1 δ21 v2 δ22) "WPk".
    now iApply (semWp2_block [env].[_∷_ ↦ v1] [env].[_∷_ ↦ v2]).
  Qed.

  Lemma semWp2_seq {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm Γ τ) :
    ⊢ ∀ (Q : Post Γ Γ τ) (δ1 δ2 : CStore Γ),
        semWp2 δ1 δ2 s1 s2 (fun v1 δ21 v2 δ22 => semWp2 δ21 δ22 k1 k2 Q) -∗ semWp2 δ1 δ2 (s1;;k1)%exp (s2;;k2)%exp Q.
  Proof.
    iIntros (Q δ1 δ2) "WPs". rewrite (fixpoint_semWp2_eq _ _ (stm_seq s1 k1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    iIntros "!> !> !>". iMod "Hclose" as "_". iModIntro.
    iFrame "Hregs Hmem".
    by iApply semWp2_bind.
  Qed.

  Lemma semWp2_assertk {Γ τ} (e11 e21 : Exp Γ ty.bool) (e12 e22 : Exp Γ ty.string) (k1 k2 : Stm Γ τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        ⌜eval e11 δ1 = eval e21 δ2⌝ -∗
        (⌜eval e11 δ1 = true⌝ → ⌜eval e21 δ2 = true⌝ → semWp2 δ1 δ2 k1 k2 Q) -∗
        semWp2 δ1 δ2 (stm_assertk e11 e12 k1) (stm_assertk e21 e22 k2) Q.
  Proof.
    iIntros (Q δ1 δ2) "%Heq WPs". rewrite (fixpoint_semWp2_eq _ _ (stm_assertk e11 e12 k1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
    iFrame "Hregs Hmem".
    rewrite Heq.
    case_match.
    - by iApply "WPs".
    - by iApply semWp2_fail_2.
  Qed.

  Lemma semWp2_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg v1 v2 -∗ Q v1 δ1 v2 δ2)) -∗
        semWp2 δ1 δ2 (stm_read_register reg) (stm_read_register reg) Q.
  Proof.
    iIntros (Q δ1 δ2) "(% & % & (Hreg1 & Hreg2) & HP)". rewrite fixpoint_semWp2_eq. cbn.
    iIntros (γ1 γ2 μ1 μ2) "((Hregs1 & Hregs2) & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
    iDestruct (@reg_valid with "Hregs1 Hreg1") as %->.
    iDestruct (@reg_valid with "Hregs2 Hreg2") as %Heq2.
    iSpecialize ("HP" with "[$Hreg1 $Hreg2]").
    iFrame "Hregs1 Hregs2 Hmem". rewrite Heq2.
    iApply semWp2_val.
    iExists _; now iSplitR.
  Qed.

  Lemma semWp2_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e1 e2 : Exp Γ τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg (eval e1 δ1) (eval e2 δ2) -∗ Q (eval e1 δ1) δ1 (eval e2 δ2) δ2)) -∗
        semWp2 δ1 δ2 (stm_write_register reg e1) (stm_write_register reg e2) Q.
  Proof.
    iIntros (Q δ1 δ2) "(% & % & (Hreg1 & Hreg2) & HP)". rewrite fixpoint_semWp2_eq. cbn.
    iIntros (γ1 γ2 μ1 μ2) "((Hregs1 & Hregs2) & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iMod (reg_update γ1 reg v1 (eval e1 δ1) with "Hregs1 Hreg1") as "[Hregs1 Hreg1]".
    iMod (reg_update γ2 reg v2 (eval e2 δ2) with "Hregs2 Hreg2") as "[Hregs2 Hreg2]".
    iModIntro. iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
    iSpecialize ("HP" with "[$Hreg1 $Hreg2]").
    iFrame "Hregs1 Hregs2 Hmem".
    iApply semWp2_val.
    iExists _; now iSplitR.
  Qed.

  Lemma semWp2_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s1 s2 : Stm Γ τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        semWp2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22, Q v1 (δ21 ⟪ x ↦ v1 ⟫) v2 (δ22 ⟪ x ↦ v2 ⟫)) -∗
        semWp2 δ1 δ2 (stm_assign x s1) (stm_assign x s2) Q.
  Proof.
    iIntros (Q δ1 δ2). iRevert (s1 s2 δ1 δ2). iLöb as "IH". iIntros (s1 s2 δ1 δ2) "WPs".
    rewrite (fixpoint_semWp2_eq _ _ (stm_assign x s1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    - rewrite !semWp2_val.
      do 3 iModIntro. iMod "Hclose" as "_".
      iMod "WPs" as "(%v2 & %Heq & HQ)". iModIntro.
      iFrame "Hregs Hmem".
      inversion Heq; subst.
      iExists v2; now iSplitR.
    - iPoseProof (semWp2_val with "WPs") as "WPs".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPs" as "(%v2 & %Heq & ?)".
      inversion Heq.
    - iPoseProof (semWp2_val with "WPs") as "WPs".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPs" as "(%v2 & %Heq & ?)".
      now rewrite Heq in H.
    - iPoseProof (semWp2_fail_1 with "WPs") as "WPs".
      do 3 iModIntro.
      iMod "Hclose" as "_".
      iMod "WPs" as "[%m %eqs2f]".
      inversion eqs2f.
    - iPoseProof (semWp2_fail_1 with "WPs") as "WPs".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPs" as "(%m & %Heq)".
      iFrame "Hregs Hmem".
      iModIntro.
      by iApply semWp2_fail_2.
    - iPoseProof (semWp2_fail_1 with "WPs") as "WPs".
      iIntros "!> !> !>". iMod "Hclose" as "_".
      iMod "WPs" as "(%m & %Heq)".
      apply stm_fail_stuck in H.
      now rewrite Heq in H.
    - semWp2_progress s.
      iIntros "!> !> !>". iMod "Hclose" as "_".
      now iMod "WPs".
    - semWp2_progress s.
      iIntros "!> !> !>". iMod "Hclose" as "_".
      now iMod "WPs".
    - semWp2_progress s.
      iSpecialize ("WPs" with "[Hregs Hmem]"); first by iFrame.
      iMod "Hclose" as "_".
      iMod "WPs".
      iSpecialize ("WPs" $! _ _ _ _ _ _ _ _ (conj H H0)).
      iMod "WPs".
      iIntros "!> !> !>".
      iMod "WPs".
      iMod "WPs".
      iDestruct "WPs" as "($ & WPs)".
      by iApply ("IH" with "WPs").
  Qed.

  Lemma semWp2_pattern_match {Γ τ σ} (s1 s2 : Stm Γ σ) (pat : Pattern σ)
    (rhs1 rhs2 : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
    semWp2 δ1 δ2 s1 s2
      (fun vσ1 δ12 vσ2 δ22 =>
         let (pc1,δpc1) := pattern_match_val pat vσ1 in
         let (pc2,δpc2) := pattern_match_val pat vσ2 in
         semWp2 (δ12 ►► δpc1) (δ22 ►► δpc2) (rhs1 pc1) (rhs2 pc2)
           (fun vτ1 δ21 vτ2 δ22 => Q vτ1 (env.drop (PatternCaseCtx pc1) δ21) vτ2 (env.drop (PatternCaseCtx pc2) δ22))
           ) -∗
    semWp2 δ1 δ2 (stm_pattern_match s1 pat rhs1) (stm_pattern_match s2 pat rhs2) Q.
  Proof.
    iIntros (Q δΓ1 δΓ2) "WPs". rewrite (fixpoint_semWp2_eq _ _ (stm_pattern_match s1 pat rhs1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs  & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
    iFrame "Hregs Hmem".
    iApply semWp2_bind. iApply (semWp2_mono with "WPs"). iIntros (v1 δ21 v2 δ22) "WPrhs".
    destruct pattern_match_val as [pc1 δpc1].
    destruct pattern_match_val as [pc2 δpc2]. by iApply (semWp2_block δpc1 δpc2).
  Qed.

  Lemma semWp2_foreign {Γ Δ τ} {f1 f2 : 𝑭𝑿 Δ τ} {es1 es2 : NamedEnv (Exp Γ) Δ} {Q δ1 δ2} :
    ⊢ (∀ γ1 γ2 μ1 μ2,
          (regs_inv2 γ1 γ2 ∗ mem_inv2 μ1 μ2)
          ={⊤,∅}=∗
      (∀ res1 γ1' μ1' res2 γ2' μ2',
        ⌜ ForeignCall f1 (evals es1 δ1) res1 γ1 γ1' μ1 μ1' ⌝
        ∗ ⌜ ForeignCall f2 (evals es2 δ2) res2 γ2 γ2' μ2 μ2' ⌝
        ={∅}▷=∗
         |={∅,⊤}=>
         (regs_inv2 γ1' γ2' ∗ mem_inv2 μ1' μ2') ∗
                    semWp2 δ1 δ2 (match res1 with inr v => stm_val _ v
                                             | inl s => stm_fail _ s
                                  end)
                    (match res2 with inr v => stm_val _ v
                                | inl s => stm_fail _ s
                     end)
                    Q)) -∗
      semWp2 δ1 δ2 (stm_foreign f1 es1) (stm_foreign f2 es2) Q.
  Proof.
    iIntros "H". rewrite fixpoint_semWp2_eq. cbn. iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod ("H" with "[$]") as "H". iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    by iMod ("H" $! _ _ _ _ _ _ (conj H H0)) as "H".
  Qed.

  Lemma semWp2_debugk {Γ τ} (s1 s2 : Stm Γ τ) :
    ⊢ ∀ Q δ1 δ2, semWp2 δ1 δ2 s1 s2 Q -∗ semWp2 δ1 δ2 (stm_debugk s1) (stm_debugk s2) Q.
  Proof.
    iIntros (Q δ1 δ2) "WPs". rewrite (fixpoint_semWp2_eq _ _ (stm_debugk s1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    now iFrame.
  Qed.

  Lemma semWp2_lemmak {Γ τ} {Δ} (l1 l2 : 𝑳 Δ) (es1 es2 : NamedEnv (Exp Γ) Δ) (s1 s2 : Stm Γ τ) :
    ⊢ ∀ Q δ1 δ2, semWp2 δ1 δ2 s1 s2 Q -∗ semWp2 δ1 δ2 (stm_lemmak l1 es1 s1) (stm_lemmak l2 es2 s2) Q.
  Proof.
    iIntros (Q δ1 δ2) "WPs". rewrite (fixpoint_semWp2_eq _ _ (stm_lemmak l1 es1 s1)). cbn.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (smallinvstep Hstep1); destruct (smallinvstep Hstep2); cbn.
    now iFrame.
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
    iApply semWp2_val.
    iModIntro; iExists v.
    repeat (iSplitR; try done).
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
    iIntros "tripk P". iPoseProof ("tripk" with "P") as "wpk".
    iApply semWp2_block.
    iApply (semWp2_mono with "wpk").
    iIntros (v1 δ1 v2 δ2) "(-> & -> & HR)".
    now repeat iSplitR.
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R).
  Proof.
    iIntros "trips1 trips2 P".
    iSpecialize ("trips1" with "P").
    iApply semWp2_seq.
    iApply (semWp2_mono with "[$]").
    iIntros (v1 δ1 v2 δ2) "(-> & -> & HQ)".
    by iApply "trips2".
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜ eval e1 δ = true ⌝ → semTriple δ P k Q) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
    iIntros "tripk P".
    iApply semWp2_assertk; first easy.
    iIntros (-> _).
    iApply (semWp2_mono with "[tripk P]").
    - by iApply "tripk".
    - iIntros (v1 δ1 v2 δ2) "(-> & -> & HQ)".
      now repeat iSplitR.
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Val ty.string) :
        forall (Q : Val τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    by iApply semWp2_fail_2.
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v)).
  Proof.
    iIntros "Hreg".
    iApply semWp2_read_register.
    iExists v, v.
    iFrame.
    iIntros "Hreg".
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
  Proof.
    iIntros "Hreg".
    iApply semWp2_write_register.
    iExists v, v.
    iFrame.
    iIntros "Hreg".
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R).
  Proof.
    iIntros "trips P".
    iSpecialize ("trips" with "P").
    iApply semWp2_assign.
    iApply (semWp2_mono with "trips").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & HR)".
    repeat iSplit; auto.
  Qed.

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
    iApply semWp2_bind.
    iApply (semWp2_mono with "trips").
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
    iIntros "tripbody P".
    iApply semWp2_call_inline_later.
    iModIntro.
    iSpecialize ("tripbody" with "P").
    iApply (semWp2_mono with "tripbody").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & HQ)".
    now iFrame.
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hdef".
    iApply (iris_rule_stm_call_inline_later with "Hdef").
  Qed.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q).
  Proof.
    iIntros "tripk P". iApply semWp2_debugk. now iApply "tripk".
  Qed.

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
    iIntros (Hnv Hnf Hnoop) "HPQ HP".
    rewrite fixpoint_semWp2_eq. cbn. rewrite Hnv Hnf.
    iIntros (γ1 γ2 μ1 μ2) "(Hregs & Hmem)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s12 δ12 γ12 μ12 s22 δ22 γ22 μ22) "(%Hstep1 & %Hstep2)".
    destruct (Hnoop _ _ _ _ _ _ Hstep1) as (-> & -> & -> & Hsteps & [[v ->]|[msg ->]]).
    - do 3 iModIntro. iMod "Hclose" as "_".
      iMod ("HPQ" $! v with "HP") as "HQ".
      iModIntro.
      rewrite semWp2_val.
      specialize (Hsteps s γ2 μ2 δ).
      destruct (Hnoop _ _ _ _ _ _ Hstep2) as (-> & -> & -> & ? & ?);
        iFrame "Hregs Hmem".
      admit.
    - do 3 iModIntro. iMod "Hclose" as "_".
      specialize (Hsteps s γ2 μ2 δ).
      destruct (Hnoop _ _ _ _ _ _ Hstep2) as (-> & -> & -> & ? & ?);
        iFrame "Hregs Hmem".
      iModIntro.
      iApply semWp2_fail_2.
      admit.
  (* Qed. *)
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
    iIntros "WPs WPrhs P".
    iSpecialize ("WPs" with "P").
    iApply semWp2_pattern_match.
    iApply (semWp2_mono with "WPs").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & HQ)".
    destruct pattern_match_val as [pc δpc] eqn:Heq.
    iSpecialize ("WPrhs" $! pc δpc δ1).
    change (pattern_match_val_reverse pat pc δpc) with
      (pattern_match_val_reverse' pat (existT pc δpc)).
    rewrite <- Heq.
    rewrite pattern_match_val_inverse_left.
    iSpecialize ("WPrhs" with "HQ").
    iApply (semWp2_mono with "WPrhs").
    iIntros (v21 δ21 v22 ď22) "(<- & <- & HR)".
    now do 2 (iSplitR; first by iPureIntro).
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

End IrisSignatureRules2.

Module Type IrisAdeqParameters2
  (Import B     : Base)
  (Import IPP  : IrisParameters2 B)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IP   : IrisPrelims B PROG SEM).

  Parameter Inline memGpreS2 : gFunctors -> Set.
  Parameter memΣ2 : gFunctors.
  Parameter memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ.
  Parameter mem_res2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.

    (* Definition mem_inv `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
    (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
    (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
    (*   )%I. *)

  Parameter mem_inv_init2 : forall `{mGS : memGpreS2 Σ} (μ1 μ2 : Memory),
                                         ⊢ |==> ∃ mG : memGS2 Σ, (mem_inv2 (mG := mG) μ1 μ2 ∗ mem_res2 (mG := mG) μ1 μ2)%I.

End IrisAdeqParameters2.

Module Type IrisAdequacy2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IAP   : IrisAdeqParameters2 B IB PROG SEM IB)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB)
  (Import IRules : IrisSignatureRules2 B SIG PROG SEM IB IPred).

  Import SmallStepNotations.

  Class sailGpreS2 Σ := SailGpreS2 { (* resources for the implementation side *)
                       sailGpresS_invGpreS2 : invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variables for tracking state of registers *)
                       reg_pre_inG2_left : inG Σ regUR;
                       reg_pre_inG2_right : inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS2 : memGpreS2 Σ
                     }.

  Existing Instance sailGpresS_invGpreS2.

  Definition sailΣ2 : gFunctors := #[ memΣ2 ; invΣ ; GFunctor regUR; GFunctor regUR].

  #[local] Instance subG_sailGpreS {Σ} : subG sailΣ2 Σ -> sailGpreS2 Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_GpreS2, subG_invΣ.
    - clear s2. solve_inG.
    - clear s1. solve_inG.
 Qed.

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

  Lemma own_RegStore_to_map_reg_pointsTos `{sailGS2 Σ} {γ1 γ2 : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
    NoDup l ->
    ⊢ own (A := regUR) (inG0 := @reg_inG _ sailRegGS2_sailRegGS_left) (@reg_gv_name _ sailRegGS2_sailRegGS_left) (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ1 r)))
                                      end) l)) ∗
      own (A := regUR) (inG0 := @reg_inG _ sailRegGS2_sailRegGS_right) (@reg_gv_name _ sailRegGS2_sailRegGS_right) (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ2 r)))
                                      end) l))
    -∗
      [∗ list] x ∈ l,
        let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo2 r (read_register γ1 r) (read_register γ2 r).
  Proof.
    iIntros (nodups) "[Hregs1 Hregs2]".
    iInduction l as [|[x r]] "IH".
    - now iFrame.
    - rewrite big_sepL_cons. cbn.
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ1 r)))).
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ2 r)))).
      rewrite ?auth_frag_op.
      iPoseProof (own_op reg_gv_name with "Hregs1") as "[Hreg1 Hregs1]".
      iDestruct (own_op reg_gv_name with "Hregs2") as "[Hreg2 Hregs2]".
      iFrame.
      iApply ("IH" with "[%] [$Hregs1] [$Hregs2]").
      + refine (NoDup_cons_1_2 (existT x r) l nodups).
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
  Qed.

  Definition own_regstore2 `{sailGS2 Σ} (γ1 γ2 : RegStore) : iProp Σ :=
    [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
      match x with | existT _ r => reg_pointsTo2 r (read_register γ1 r) (read_register γ2 r) end.

  Inductive NSteps {Γ : PCtx} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ) : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> nat -> Prop :=
  | nstep_refl : NSteps γ1 μ1 δ1 s1 γ1 μ1 δ1 s1 0
  | nstep_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : CStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> NSteps γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 n -> NSteps γ1 μ1 δ1 s1 γ3 μ3 δ3 s3 (S n).

  Lemma steps_to_nsteps {Γ : PCtx} {σ : Ty} {γ1 γ2 : RegStore} {μ1 μ2 : Memory} {δ1 δ2 : CStore Γ} {s1 s2 : Stm Γ σ} :
    Steps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 -> exists n, NSteps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 n.
  Proof.
    induction 1 as [|γ1 μ1 δ1 s1 γ2 γ3 μ2 μ3 δ2 δ3 s2 s3 eval evals [n nsteps]].
    - exists 0. constructor.
    - exists (S n). econstructor; eassumption.
  Qed.

  Lemma nsteps_to_steps {Γ : PCtx} {σ : Ty} {γ1 γ2 : RegStore} {μ1 μ2 : Memory} {δ1 δ2 : CStore Γ} {s1 s2 : Stm Γ σ} {n} :
    NSteps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 n -> Steps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.
  Proof.
    induction 1; econstructor; eassumption.
  Qed.

  (* TODO: move following 3 to where stm_val_stuck is defined? *)
  Lemma final_val_and_fail_None : forall {Γ τ} (s : Stm Γ τ),
      Final s -> stm_to_val s = None -> stm_to_fail s = None -> False.
  Proof. intros ? ? s. by destruct s. Qed.

  Lemma is_not_final : forall {Γ τ} (s : Stm Γ τ),
      stm_to_val s = None ->
      stm_to_fail s = None ->
      ~ Final s.
  Proof. intros ? ? s ? ? ?. by destruct s. Qed.

  Lemma can_step : forall {Γ τ} (s : Stm Γ τ) γ μ δ,
      ~ Final s ->
      ∃ γ' μ' δ' s', ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩.
  Proof.
    intros ? ? s **.
    pose proof (progress s) as [|Hprogress];
      first intuition.
    by apply Hprogress.
  Qed.

  Lemma adequacy {Γ} {σ} (s11 s21 : Stm Γ σ) {γ11 γ21 γ12} {μ11 μ21 μ12}
        {δ11 δ21 δ12 : CStore Γ} {s12 : Stm Γ σ} {Q : Val σ -> Val σ -> Prop} :
    ⟨ γ11, μ11, δ11, s11 ⟩ --->* ⟨ γ12, μ12, δ12, s12 ⟩ -> Final s12 ->
    (forall {Σ} `{sailGS2 Σ}, mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢ semWp2 δ11 δ21 s11 s21 (fun v1 _ v2 _ => ⌜ Q v1 v2 ⌝)) ->
    ResultOrFail s12 (fun v12 =>
                        exists γ22 μ22 δ22 v22,
                          ⟨ γ21, μ21, δ21, s21 ⟩ --->* ⟨ γ22, μ22, δ22, stm_val _ v22 ⟩ /\
                            Q v12 v22).
  Proof.
    intros Heval1 Hfinal Hwp.
    destruct (steps_to_nsteps Heval1) as [n Hevaln1].
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc n n _)).
    iIntros (Hinv) "Hcred".
    iMod (own_alloc ((● RegStore_to_map γ11 ⋅ ◯ RegStore_to_map γ11 ) : regUR)) as (regs1) "[Hregsown1 Hregsinv1]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    iMod (own_alloc ((● RegStore_to_map γ21 ⋅ ◯ RegStore_to_map γ21 ) : regUR)) as (regs2) "[Hregsown2 Hregsinv2]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_inv_init2 (mGS := mGS) μ11 μ21) as (memG) "[Hmem Rmem]".
    pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS reg_pre_inG2_left regs1) (SailRegGS reg_pre_inG2_right regs2)) memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem Hregsinv1 Hregsinv2]") as "Hwp2".
    { iApply own_RegStore_to_map_reg_pointsTos.
      apply finite.NoDup_enum.
      iSplitR "Hregsinv2"; iAssumption.
    }
    iAssert (regs_inv2 γ11 γ21) with "[Hregsown1 Hregsown2]" as "Hregs".
    { iSplitL "Hregsown1";
      now iApply own_RegStore_to_regs_inv.
    }
    clear Hwp.
    iStopProof.
    revert γ21 μ21 δ21 s21.
    induction Hevaln1.
    - iIntros (γ21 μ21 δ21 s21) "(Hcred & Hmem & Hwp2 & Hregs)".
      rewrite fixpoint_semWp2_eq.
      unfold Final in Hfinal.
      destruct s1 eqn:?; inversion Hfinal; cbn.
      + case_match.
        * iMod "Hwp2" as "%HQ".
          iApply fupd_mask_intro; first by set_solver.
          iIntros "_ !%".
          destruct s21; try inversion H.
          eexists _, _, _, _; split; first apply step_refl; auto.
        * by iMod "Hwp2" as "%".
      + iApply fupd_mask_intro; first by set_solver.
        by iIntros.
    - iIntros (γ21 μ21 δ21 s21) "(Hcred & Hmem & Hwp2 & Hregs)".
      specialize (IHHevaln1 (nsteps_to_steps Hevaln1) Hfinal).
      rewrite fixpoint_semWp2_eq. cbn.
      rewrite (stm_val_stuck H) (stm_fail_stuck H).
      case_match eqn:Evs21;
        try case_match eqn:Efs21;
        try by iMod "Hwp2".
      iSpecialize ("Hwp2" with "[$Hregs $Hmem]").
      iMod "Hwp2" as "Hwp2". iModIntro.
      pose proof (is_not_final s21 Evs21 Efs21) as Hnfinal21.
      destruct (can_step s21 γ21 μ21 δ21 Hnfinal21) as (γ22 & μ22 & δ22 & s22 & Hsteps21).
      iSpecialize ("Hwp2" $! _ _ _ _ _ _ _ _ (conj H Hsteps21)).
      iMod "Hwp2". iModIntro. iModIntro. iMod "Hwp2".
      iMod "Hwp2" as "([Hregs Hmem] & Hwp)".
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iMod (IHHevaln1 γ22 μ22 δ22 s22 with "[$Hregs $Hmem $Hwp $Hcred]") as "IH2".
      iModIntro.
      iApply (step_fupdN_mono with "IH2").
      iPureIntro.
      apply result_or_fail_mono.
      intros v (γ23 & μ23 & δ23 & v23 & Hsteps223 & HQ).
      repeat eexists; last eassumption.
      eapply step_trans.
      apply Hsteps21.
      apply Hsteps223.
  Qed.

  Lemma adequacy_gen {Γ σ} (s11 s21 : Stm Γ σ) {γ11 γ12 γ21} {μ11 μ12 μ21}
        {δ11 δ12 δ21 : CStore Γ} {s12 : Stm Γ σ} {Q : forall `{sailGS2 Σ}, Val σ -> CStore Γ -> Val σ -> CStore Γ -> iProp Σ}
        (φ : Prop) :
    ⟨ γ11, μ11, δ11, s11 ⟩ --->* ⟨ γ12, μ12, δ12, s12 ⟩ ->
    (forall `{sailGS2 Σ},
        mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢ |={⊤}=> semWp2 δ11 δ21 s11 s21 Q
          ∗ (∀ μ22, mem_inv2 μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝)
    )%I -> φ.
  Proof.
    intros Heval1 Hwp.
    destruct (steps_to_nsteps Heval1) as [n Hevaln1].
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc n n _)).
    iIntros (Hinv) "".
    iMod (own_alloc ((● RegStore_to_map γ11 ⋅ ◯ RegStore_to_map γ11 ) : regUR)) as (regs1) "[Hregsown1 Hregsinv1]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    iMod (own_alloc ((● RegStore_to_map γ21 ⋅ ◯ RegStore_to_map γ21 ) : regUR)) as (regs2) "[Hregsown2 Hregsinv2]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_inv_init2 (mGS := mGS) μ11 μ21) as (memG) "[Hmem Rmem]".
    pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS reg_pre_inG2_left regs1) (SailRegGS reg_pre_inG2_right regs2)) memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem Hregsinv1 Hregsinv2]") as "Hwp2".
    { iApply own_RegStore_to_map_reg_pointsTos.
      apply finite.NoDup_enum.
      iSplitR "Hregsinv2"; iAssumption.
    }
    iAssert (regs_inv2 γ11 γ21) with "[Hregsown1 Hregsown2]" as "Hregs".
    { iSplitL "Hregsown1";
      now iApply own_RegStore_to_regs_inv.
    }
    clear Hwp.
    iStopProof.
    revert γ21 μ21 δ21 s21.
    induction Hevaln1.
    - iIntros (γ21 μ21 δ21 s21) "(Hmem & Hwp2 & Hregs) Hcred".
      iMod "Hwp2" as "[_ Hcont]".
      now iMod ("Hcont" with "Hmem") as "%Hφ".
    - iIntros (γ21 μ21 δ21 s21) "(Hregs & Hwp2 & Hmem) Hcred".
      specialize (IHHevaln1 (nsteps_to_steps Hevaln1)).
      rewrite fixpoint_semWp2_eq; cbn.
      rewrite (stm_val_stuck H) (stm_fail_stuck H).
      repeat case_match;
        try (iMod "Hwp2" as "(H & _)";
             by iMod "H").
      iMod "Hwp2".
      iDestruct "Hwp2" as "(Hwp2 & Hinv)".
      iSpecialize ("Hwp2" with "[$Hregs $Hmem]").
      pose proof (is_not_final s21 H0 H1) as Hnfinal21.
      destruct (can_step s21 γ21 μ21 δ21 Hnfinal21) as (γ22 & μ22 & δ22 & s22 & Hsteps21).
      iMod "Hwp2" as "Hwp2". iModIntro.
      iSpecialize ("Hwp2" $! _ _ _ _ _ _ _ _ (conj H Hsteps21)).
      iMod "Hwp2". iModIntro. iModIntro. iMod "Hwp2".
      iDestruct "Hcred" as "(Hcred1 & Hcredn)".
      iMod "Hwp2" as "([Hregs Hmem] & Hwp2)".
      now iMod (IHHevaln1 with "[$Hmem $Hregs $Hwp2 $Hinv] Hcredn") as "IH".
  Qed.

End IrisAdequacy2.

Module Type IrisInstance2 (B : Base) (SIG : Signature B) (PROG : Program B)
  (SEM : Semantics B PROG) (IB : IrisBase2 B PROG SEM) (IAP : IrisAdeqParameters2 B IB PROG SEM IB) :=
  IrisPredicates2 B SIG PROG SEM IB <+ IrisSignatureRules2 B SIG PROG SEM IB
    <+ IrisAdequacy2 B SIG PROG SEM IB IAP.

(*  * The following module defines the parts of the Iris model that must depend on the Specification, not just on the Signature. *)
(*  * This is kept to a minimum (see comment for the IrisPredicates module). *)
(*  *)
Module IrisInstanceWithContracts2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import SPEC  : Specification B SIG PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IAP   : IrisAdeqParameters2 B IB PROG SEM IB)
  (Import II    : IrisInstance2 B SIG PROG SEM IB IAP)
  (Import PLOG  : ProgramLogicOn B SIG PROG SPEC).

  Section WithSailGS.
  Import ProgramLogic.
  Context {Σ} {sG : sailGS2 Σ}.

  Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
    (∀ σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | Some c => ValidContractSem (FunDef f) c
      | None => True
      end)%I.

  Definition ForeignSem :=
    ∀ (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ),
      ValidContractForeign (CEnvEx f) f.

  Definition LemmaSem : Prop :=
    forall (Δ : PCtx) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Lemma iris_rule_stm_call {Γ} (δ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ)
    (Q : Val σ -> CStore Γ -> iProp Σ) :
    CEnv f = Some c ->
    CTriple P c (evals es δ) (fun v => Q v δ) ->
    ⊢ ▷ ValidContractEnvSem CEnv -∗
       semTriple δ P (stm_call f es) Q.
  Proof.
    iIntros (ceq ctrip) "cenv P".
    iApply semWp2_call_inline_later.
    iModIntro.
    iSpecialize ("cenv" $! _ _ f).
    rewrite ceq. clear ceq.
    destruct c as [Σe δΔ req res ens]; cbn in *.
    iPoseProof (ctrip with "P") as (ι Heq) "[req consr]". clear ctrip.
    iPoseProof ("cenv" $! ι with "req") as "wpf0". rewrite Heq.
    iApply (semWp2_mono with "wpf0").
    iIntros (v1 δ1 ? ?) "(<- & <- & H)".
    do 2 (iSplitR; first by iPureIntro).
    now iApply "consr".
  Qed.

  Lemma iris_rule_stm_call_frame {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗
           semTriple δ P (stm_call_frame δΔ s) Q).
  Proof.
    iIntros "trips P".
    iSpecialize ("trips" with "P").
    iApply semWp2_call_frame.
    iApply (semWp2_mono with "trips").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & HQ)".
    now iFrame.
  Qed.

  Lemma iris_rule_stm_foreign
    {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ForeignSem ->
    CTriple P (CEnvEx f) (evals es δ) (λ v : Val τ, Q v δ) ->
    ⊢ semTriple δ P (stm_foreign f es) Q.
  Proof.
    iIntros (forSem ctrip) "P".
    specialize (forSem Δ τ f Γ es δ).
    destruct CEnvEx as [Σe δΔ req res ens]; cbn in *.
    iPoseProof (ctrip with "P") as "[%ι [%Heq [req consr]]]". clear ctrip.
    iPoseProof (forSem ι Heq with "req") as "WPf". clear forSem.
    iApply (semWp2_mono with "WPf").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & ens & ->)".
    do 2 (iSplitR; first by iPureIntro).
    by iApply "consr".
  Qed.

  Lemma iris_rule_stm_lemmak
    {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
    (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
    LemmaSem ->
    LTriple (evals es δ) P Q (LEnv l) ->
    ⊢ semTriple δ Q k R -∗
      semTriple δ P (stm_lemmak l es k) R.
  Proof.
    iIntros (lemSem ltrip) "tripk P". iApply semWp2_lemmak. iApply "tripk".
    specialize (lemSem _ l). remember (LEnv l) as contractL.
    clear - lemSem ltrip.
    destruct ltrip as [Ψ' pats req ens ent]; cbn in lemSem.
    iPoseProof (ent with "P") as (ι Heq) "[req consr]".
    iApply "consr". by iApply lemSem.
  Qed.

  Lemma sound_stm
    {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
    forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ),
      ForeignSem ->
      LemmaSem ->
      ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ ->
      ⊢ (□ ▷ ValidContractEnvSem CEnv -∗
          semTriple δ PRE s POST)%I.
  Proof.
    iIntros (PRE POST extSem lemSem triple) "#vcenv".
    iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips".
    - by iApply iris_rule_consequence.
    - by iApply iris_rule_frame.
    - by iApply iris_rule_pull.
    - by iApply iris_rule_exist.
    - iApply iris_rule_stm_val.
      by iApply H.
    - iApply iris_rule_stm_exp.
      by iApply H.
    - by iApply iris_rule_stm_let.
    - by iApply iris_rule_stm_block.
    - by iApply iris_rule_stm_seq.
    - by iApply iris_rule_stm_assertk.
    - by iApply iris_rule_stm_fail.
    - by iApply iris_rule_stm_read_register.
    - by iApply iris_rule_stm_write_register.
    - by iApply iris_rule_stm_assign.
    - by iApply iris_rule_stm_call.
    - by iApply iris_rule_stm_call_inline.
    - by iApply iris_rule_stm_call_frame.
    - by iApply iris_rule_stm_foreign.
    - by iApply iris_rule_stm_lemmak.
    - by iApply iris_rule_stm_bind.
    - by iApply iris_rule_stm_debugk.
    - by iApply iris_rule_stm_pattern_match.
  Qed.

  Lemma sound :
    ForeignSem -> LemmaSem -> ValidContractCEnv ->
    ⊢ ValidContractEnvSem CEnv.
  Proof.
    intros extSem lemSem vcenv.
    iLöb as "IH".
    iIntros (σs σ f).
    specialize (vcenv σs σ f).
    destruct (CEnv f) as [[]|];[|trivial].
    specialize (vcenv _ eq_refl).
    iIntros (ι).
    iApply (sound_stm extSem lemSem); [|trivial].
    apply (vcenv ι).
  Qed.

  End WithSailGS.
End IrisInstanceWithContracts2.
