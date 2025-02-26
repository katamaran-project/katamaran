(*****************************************************************************)
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
     Specification
     BinaryModel.

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

Module Type IrisBinaryWPParameters
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IP    : IrisParameters B)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB).

  Parameter reg_inv2       : forall `{sG : sailRegGS2 Σ}, RegStore -> RegStore -> iProp Σ.
  (* Parameter reg_inv_l      : forall `{sG : sailRegGS Σ}, RegStore -> iProp Σ.
  Parameter reg_inv_r      : forall `{sG : sailRegGS Σ}, RegStore -> iProp Σ.
  Parameter reg_inv2_split : forall `{sG : sailRegGS2 Σ} (γl γr : RegStore),
      reg_inv2 γl γr ⊣⊢ @reg_inv_l _ sailRegGS2_sailRegGS_left γl ∗ @reg_inv_r _ sailRegGS2_sailRegGS_right γr. *)
  Parameter mem_inv2   : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.
  (* Parameter mem_inv_l  : forall `{mG : memGS Σ}, Memory -> iProp Σ.
  Parameter mem_inv_r  : forall `{mG : memGS Σ}, Memory -> iProp Σ. *)
  Parameter mc_memGS_left : forall `{mG : memGS2 Σ}, memGS Σ.
  Parameter mc_memGS_right : forall `{mG : memGS2 Σ}, memGS Σ.
  Parameter mem_inv2_split : forall `{sG : sailGS2 Σ} (μl μr : Memory),
      mem_inv2 μl μr ⊣⊢ @mem_inv _ mc_memGS_left μl ∗ @mem_inv _ mc_memGS_right μr.
End IrisBinaryWPParameters.

(* IrisBinaryWPAsymmetric allows asymmetry between the executions. The left
   program is allowed to take zero or one step, the right one always needs to
   be able to take a step. *)

Module IrisBinaryWPAsymmetric (B : Base) (SIG : Signature B) (PROG : Program B)
  (SEM : Semantics B PROG) (IP : IrisParameters B) (IB : IrisBase2 B PROG SEM) (IPred : IrisPredicates2 B SIG PROG SEM IB)
  <: IrisBinaryWPParameters B SIG PROG SEM IP IB IPred.
  Import B SIG PROG SEM IP IB IPred.

  Definition reg_inv2   := @regs_inv2.
  Lemma reg_inv2_split : forall `{sG : sailRegGS2 Σ} (γl γr : RegStore),
      reg_inv2 _ γl γr ⊣⊢ @regs_inv _ sailRegGS2_sailRegGS_left γl ∗ @regs_inv _ sailRegGS2_sailRegGS_right γr.
  Proof. by rewrite /reg_inv2. Qed.
  
  Definition mem_inv2   := @mem_inv2.
  Parameter mc_memGS_left : forall `{mG : memGS2 Σ}, memGS Σ.
  Parameter mc_memGS_right : forall `{mG : memGS2 Σ}, memGS Σ.
  Parameter mem_inv2_split : forall `{sG : sailGS2 Σ} (μl μr : Memory),
      @mem_inv2 _ _ μl μr ⊣⊢ @mem_inv _ mc_memGS_left μl ∗ @mem_inv _ mc_memGS_right μr.
End IrisBinaryWPAsymmetric.

Module IrisBinaryWP
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IP    : IrisParameters B)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB)
  (Import IWP   : IrisBinaryWPParameters B SIG PROG SEM IP IB IPred).

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

  Definition Post Γ τ :=
    Val τ -> CStore Γ -> RegStore -> Memory -> iProp Σ.
  Canonical Structure PostO Γ τ := leibnizO (Post Γ τ).

  Definition Wp {Γ τ} {sG : sailRegGS Σ} {mG : memGS Σ} :=
    CStore Γ -d> Stm Γ τ -d> RegStore -d> Memory -d> Post Γ τ -d> iProp Σ.

  Definition Wp2 {Γ1 Γ2 τ} :=
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

           How does other work reason about invariants with fewer restrictions
           in the wp2?
           - SeLoC: wp2 requires lockstep, they also put limitations on the
             shapes of data (calendar example, always same length so that
             the loop of the program takes the same nr of steps in both
             executions)
           - "A machine-checked framework for relational sep. logic":
             Similar requirements about symmetric execution, they require
             that before each loop or branch statement the state is identical,
             i.e., the same nr of iterations for loops, the same branch is
             taken for branches
           - ReLoC: focuses on refinements. Interesting is that they have two
             rules that allow taking a step either on the left or right (for
             example, see the rule rel-pure-l).
   *)
  Ltac f_equiv_more_arities := match goal with
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1) (?g ?x ?y ?z1) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2) (?g ?x ?y ?z1 ?z2) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3) (?g ?x ?y ?z1 ?z2 ?z3) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3 ?z4) (?g ?x ?y ?z1 ?z2 ?z3 ?z4) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5) (?g ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5 ?z6) (?g ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5 ?z6) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5 ?z6 ?z7) (?g ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5 ?z6 ?z7) => solve [ simple apply H ]
  | H:_ ?f ?g |- ?R (?f ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5 ?z6 ?z7 ?z8) (?g ?x ?y ?z1 ?z2 ?z3 ?z4 ?z5 ?z6 ?z7 ?z8) => solve [ simple apply H ]
  end.

  Ltac solve_contractive_more_arities := solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | f_equiv_more_arities]).

  (* TODO: we actually need to "drag" the other stm and store too, so that we
     always have the same nr of ▷'s in each conjunct of semWp2. (similar to max_steps below) *)
  Definition semWp_fix {Γ τ} {sG : sailRegGS Σ} {mG : memGS Σ} (wp : @Wp _ _ sG mG) : @Wp _ _ sG mG :=
    (λ (δ : CStore Γ) (s : Stm Γ τ) (γ : RegStore) (μ : Memory) (POST : Post Γ τ),
      match stm_to_val s with
      | Some v => POST v δ γ μ
      | _      =>
          @regs_inv _ sG γ ∗ @mem_inv _ mG μ -∗
               (∀ (s' : Stm Γ τ) (δ' : CStore Γ)
                  (γ' : RegStore) (μ' : Memory),
                   ⌜⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩⌝ -∗ (* ={∅}▷=∗ *)
                    ▷ ((@regs_inv _ sG γ' ∗ @mem_inv _ mG μ') ∗ wp δ' s' γ' μ' POST))
      end)%I.
  Global Arguments semWp_fix {_}%_ctx_scope {_ _ _} wp /.

  Global Instance semWp_fix_Contractive {Γ τ sR mG} :
    Contractive (@semWp_fix Γ τ sR mG).
  Proof. unfold Wp; solve_contractive_more_arities. Qed.

  Definition semWp {Γ τ sR mG} : @Wp _ _ sR mG :=
    λ δ s POST, (fixpoint (@semWp_fix Γ τ sR mG)) δ s POST.

  Lemma fixpoint_semWp_fix_eq {Γ τ sR mG} (δ : CStore Γ) (s : Stm Γ τ) (γ : RegStore)
    (μ : Memory) (POST : Post Γ τ) :
    fixpoint (@semWp_fix _ _ sR mG) δ s γ μ POST ≡ @semWp_fix _ _ sR mG (fixpoint semWp_fix) δ s γ μ POST.
  Proof. exact: (fixpoint_unfold semWp_fix δ s γ μ POST). Qed.

  Lemma fixpoint_semWp_eq {Γ τ sR mG} (δ : CStore Γ) (s : Stm Γ τ)
    (γ : RegStore) (μ : Memory) (POST : Post Γ τ) :
    @semWp _ _ sR mG δ s γ μ POST ≡ @semWp_fix _ _ sR mG semWp δ s γ μ POST.
  Proof. by unfold semWp; rewrite fixpoint_semWp_fix_eq. Qed.

  Definition t_max_steps {Γ1 Γ2 τ} :=
    CStore Γ1 -d> CStore Γ2 -d> Stm Γ1 τ -d> Stm Γ2 τ -d> RegStore -d> RegStore-d> Memory -d> Memory -d> iProp Σ -d> iProp Σ.

  Definition max_steps_fix {Γ1 Γ2 τ} (max_steps : t_max_steps) : t_max_steps :=
    (λ (δ1 : CStore Γ1) (δ2 : CStore Γ2) (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (γ1 γ2 : RegStore) (μ1 μ2 : Memory) (POST : iProp Σ),
      match stm_to_val s1, stm_to_val s2 with
      | Some _, Some _ => POST
      | None  , Some _ =>  
          (∀ δ1' s1' γ1' μ1',
              ⌜⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩⌝ -∗
              ▷ max_steps δ1' δ2 s1' s2 γ1' γ2 μ1' μ2 POST)
      | Some _, None   =>
          (∀ δ2' s2' γ2' μ2',
              ⌜⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩⌝ -∗
              ▷ max_steps δ1 δ2' s1 s2' γ1 γ2' μ1 μ2' POST)
      | None  , None   =>
          (∀ δ1' δ2' s1' s2' γ1' γ2' μ1' μ2',
              ⌜⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩⌝ -∗
              ⌜⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩⌝ -∗
              ▷ max_steps δ1' δ2' s1' s2' γ1' γ2' μ1' μ2' POST)
      end)%I.
  Global Arguments max_steps_fix {_ _}%_ctx_scope {_} _ /.

  Global Instance max_steps_fix_Contractive {Γ1 Γ2 τ} :
    Contractive (@max_steps_fix Γ1 Γ2 τ).
  Proof. unfold t_max_steps; solve_contractive_more_arities. Qed.

  Definition max_steps {Γ1 Γ2 τ} : t_max_steps :=
    λ (δ1 : CStore Γ1) (δ2 : CStore Γ2) (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
      (γ1 γ2 : RegStore) (μ1 μ2 : Memory) (POST : iProp Σ),
      (fixpoint (@max_steps_fix Γ1 Γ2 τ)) δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST.

  Lemma fixpoint_max_steps_fix_eq {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (γ1 γ2 : RegStore) (μ1 μ2 : Memory)
    (POST : iProp Σ) :
    fixpoint max_steps_fix δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST ≡ max_steps_fix (fixpoint max_steps_fix) δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST.
  Proof. exact: (fixpoint_unfold max_steps_fix δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST). Qed.

  Lemma fixpoint_max_steps_eq {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (γ1 γ2 : RegStore) (μ1 μ2 : Memory)
    (POST : iProp Σ) :
    max_steps δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST ≡ max_steps_fix max_steps δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST.
  Proof. by unfold max_steps; rewrite fixpoint_max_steps_fix_eq. Qed.

  Definition semWp2 {Γ1 Γ2 τ} : Wp2 :=
    (λ (δ1 : CStore Γ1) (δ2 : CStore Γ2)
         (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
         (POST : Post2 Γ1 Γ2 τ),
       (∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
           ∃ (POST1 : Post Γ1 τ) (POST2 : Post Γ2 τ),
           (@semWp _ _ sailRegGS2_sailRegGS_left mc_memGS_left δ1 s1 γ1 μ1 POST1 ∗
            @semWp _ _ sailRegGS2_sailRegGS_right mc_memGS_right δ2 s2 γ2 μ2 POST2 ∗
            (max_steps δ1 δ2 s1 s2 γ1 γ2 μ1 μ2
            (∀ v1 δ1 γ1 μ1 v2 δ2 γ2 μ2, POST1 v1 δ1 γ1 μ1 ∗ POST2 v2 δ2 γ2 μ2 -∗ POST v1 δ1 v2 δ2)))))%I.
  End WithSailGS2.
End IrisBinaryWP.

Module IrisBinaryWPAsymmetricLaws
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IP    : IrisParameters B)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB).

  Module Export IWPP := IrisBinaryWPAsymmetric B SIG PROG SEM IP IB IPred.
  Module Export IWP := IrisBinaryWP B SIG PROG SEM IP IB IPred IWPP.

  Section WithSailGS2.
  Context `{sG : sailGS2 Σ}.

  Import SmallStepNotations.

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

  Axiom step_deterministic : forall {Γ τ} {γ : RegStore} {μ : Memory} {δ : CStore Γ}
    {s : Stm Γ τ},
    ∀ {γ1 μ1 δ1 s1 γ2 μ2 δ2 s2},
      ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ1, μ1, δ1, s1 ⟩ ->
      ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
      γ1 = γ2 ∧ μ1 = μ2 ∧ δ1 = δ2 ∧ s1 = s2.

  Lemma semWp_mono [Γ τ] {sR mG} (s : Stm Γ τ) (Q1 Q2 : Post Γ τ) (δ : CStore Γ)
    (γ : RegStore) (μ : Memory) :
    ⊢ @semWp _ _ _ sR mG δ s γ μ Q1 -∗ (∀ v δ γ μ, Q1 v δ γ μ -∗ Q2 v δ γ μ) -∗ @semWp Σ _ _ sR mG δ s γ μ Q2.
  Proof.
    iIntros "H HQ".
    iLöb as "IH" forall (δ s γ μ).
    rewrite ?fixpoint_semWp_eq; cbn.
    case_match eqn:Esv.
    - by iApply "HQ".
    - iIntros (* (? ?) *) "Hres".
      iIntros (? ? ? ?) "Hs".
      iSpecialize ("H" with "Hres Hs").
      iDestruct "H" as "($ & H)".
      iIntros "!>".
      iApply ("IH" with "H HQ").
  Qed.

  Lemma max_steps_mono {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (γ1 γ2 : RegStore) (μ1 μ2 : Memory)
    (POST1 POST2 : iProp Σ) :
    max_steps δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST1 -∗
    (POST1 -∗ POST2) -∗
    max_steps δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST2.
  Proof.
    iLöb as "IH" forall (δ1 δ2 s1 s2 γ1 γ2 μ1 μ2).
    iIntros "H HPOST".
    destruct (stm_to_val s1) eqn:Es1v, (stm_to_val s2) eqn:Es2v;
      rewrite ?fixpoint_max_steps_eq /max_steps_fix ?Es1v ?Es2v.
    - iApply ("HPOST" with "H").
    - iIntros (? ? ? ? Hs1).
      iSpecialize ("H" with "[]"); first eauto.
      iModIntro.
      iApply ("IH" with "H HPOST").
    - iIntros (? ? ? ? Hs2).
      iSpecialize ("H" with "[]"); first eauto.
      iModIntro.
      iApply ("IH" with "H HPOST").
    - iIntros (? ? ? ? ? ? ? ? Hs1 Hs2).
      iSpecialize ("H" with "[] []"); [eauto|eauto|].
      iModIntro.
      iApply ("IH" with "H HPOST").
  Qed.

  Lemma max_steps_vals {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (v1 v2 : Val τ) (γ1 γ2 : RegStore) (μ1 μ2 : Memory) (POST : iProp Σ) :
    max_steps δ1 δ2 (stm_val τ v1) (stm_val τ v2) γ1 γ2 μ1 μ2 POST ⊣⊢ POST.
  Proof. rewrite fixpoint_max_steps_eq; by cbn. Qed.

  Lemma max_steps_steps {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (γ1 γ2 : RegStore) (μ1 μ2 : Memory)
    (POST : iProp Σ) :
    ∀ δ1' δ2' s1' s2' γ1' γ2' μ1' μ2',
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩ ->
      ⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩ ->
      max_steps δ1 δ2 s1 s2 γ1 γ2 μ1 μ2 POST ⊢
      ▷ max_steps δ1' δ2' s1' s2' γ1' γ2' μ1' μ2' POST.
  Proof.
    iIntros (δ1' δ2' s1' s2' γ1' γ2' μ1' μ2' Hs1 Hs2) "H".
    rewrite fixpoint_max_steps_eq; cbn.
    stm_val_fail_stuck.
    now iSpecialize ("H" with "[] []"); [eauto|eauto|].
  Qed.

  Lemma semWp2_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (Q1 Q2 : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    ⊢ semWp2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWp2 δ1 δ2 s1 s2 Q2.
  Proof.
    unfold semWp2.
    (* iIntros "(%POST1 & %POST2 & H) HQ". *)
    iIntros "H HQ". iIntros (γ1 γ2 μ1 μ2).
    iDestruct ("H" $! γ1 γ2 μ1 μ2) as "(%POST1 & %POST2 & H)".
    iExists POST1, POST2.
    iDestruct "H" as "($ & $ & H)".
    iApply (max_steps_mono with "H").
    iIntros "H".
    iIntros (? ? ? ? ? ? ? ?) "HPOST".
    iSpecialize ("H" with "HPOST").
    iApply ("HQ" with "H").
  Qed.

  Lemma semWp_val {Γ τ sR mG} (v : Val τ) (Q : Post Γ τ) :
    forall δ γ μ,
      @semWp Σ _ _ sR mG δ (stm_val τ v) γ μ Q ⊣⊢ Q v δ γ μ.
  Proof.
    iIntros (δ γ μ).
    iSplit; iIntros "H";
      rewrite fixpoint_semWp_eq; cbn; auto.
  Qed.

  Lemma semWp2_val_1 {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
    forall δ1 δ2,
      Q v1 δ1 v2 δ2 ⊢ semWp2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q.
  Proof.
    iIntros (δ1 δ2) "HQ".
    rewrite /semWp2.
    iIntros (γ1 γ2 μ1 μ2).
    setoid_rewrite semWp_val.
    iExists (λ v' δ' γ' μ', ⌜v' = v1⌝ ∗ ⌜δ' = δ1⌝ ∗ ⌜γ' = γ1⌝ ∗ ⌜μ' = μ1⌝)%I.
    iExists (λ v' δ' γ' μ', ⌜v' = v2⌝ ∗ ⌜δ' = δ2⌝ ∗ ⌜γ' = γ2⌝ ∗ ⌜μ' = μ2⌝)%I.
    iSplitR; first auto. iSplitR; first auto.
    rewrite max_steps_vals.
    iIntros (? ? ? ? ? ? ? ?) "((-> & -> & -> & ->) & -> & -> & -> & ->)".
    now iFrame "HQ".
  Qed.

  (* TODO: bit annoying with the mem, regstore, but required for one direction... Seems odd, solve it properly. *)
  Lemma semWp2_val {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
    forall δ1 δ2 (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
      (* (reg_inv2 _ γ1 γ2 ∗ mem_inv2 _ μ1 μ2) ∗ *) semWp2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q
      ⊣⊢ (* (reg_inv2 _ γ1 γ2 ∗ mem_inv2 _ μ1 μ2) ∗ *) Q v1 δ1 v2 δ2.
  Proof.
    iIntros (δ1 δ2 γ1 γ2 μ1 μ2).
    rewrite /semWp2.
    iSplit; iIntros "H".
    - iSpecialize ("H" $! γ1 γ2 μ1 μ2).
      setoid_rewrite semWp_val.
      iDestruct "H" as "(%POST1 & %POST2 & Hl & Hr & H)".
      rewrite max_steps_vals.
      iSpecialize ("H" with "[$Hl $Hr]").
      iFrame "H".
    - now iApply semWp2_val_1.
  Qed.

  Lemma semWp2_step_fupd {Γ1 Γ2 τ} (δA : CStore Γ1) (δB : CStore Γ2)
    (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) (P :iProp Σ) Φ : 
    to_val {| conf_stm := eA; conf_store := δA |} = None ->
    to_val {| conf_stm := eB; conf_store := δB |} = None ->
    P -∗
    semWp2 δA δB eA eB (λ v1 δA v2 δB, P -∗ Φ v1 δA v2 δB) -∗
    semWp2 δA δB eA eB Φ.
  Proof.
    rewrite /semWp2 ?fixpoint_semWp_eq; cbn.
    (* iIntros (HeA HeB) "HP (%POST1 & %POST2 & H)". *)
    iIntros (HeA HeB) "HP H".
    iIntros (γ1 γ2 μ1 μ2). iDestruct ("H" $! γ1 γ2 μ1 μ2) as "(%POST1 & %POST2 & H)".
    iExists POST1, POST2.
    iDestruct "H" as "($ & $ & H)".
    iApply (max_steps_mono with "H").
    iIntros "H".
    iIntros (? ? ? ? ? ? ? ? ) "HPs".
    iSpecialize ("H" with "HPs").
    iApply ("H" with "HP").
  Qed.

  (* TODO: no longer hold with updated defs *)
  Lemma semWp_not_stuck {Γ τ sR mG} (s : Stm Γ τ) (δ : CStore Γ) (γ : RegStore) (μ : Memory) :
    ⊢ @semWp Σ _ _ sR mG δ s γ μ (λ v' δ' γ' μ', ∀ γ μ, ∃ γ' μ', ⌜⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', stm_val τ v' ⟩⌝).
  Proof.
    (* iLöb as "IH" forall (δ s (* γ μ *)). *)
    (* destruct (stm_to_val s) eqn:Esv. *)
    (* - destruct s; try discriminate; inversion Esv; subst. *)
    (*   rewrite semWp_val. iPureIntro. intros γ. intros μ. exists γ, μ. apply step_refl. *)
    (* - rewrite fixpoint_semWp_eq; cbn; rewrite Esv. *)
    (*   iIntros (γ μ) "Hres". *)
    (*   iIntros (? ? ? ? Hs). iIntros "!>". *)
    (*   iSpecialize ("IH" $! δ' s'). *)
  Admitted.

  Lemma semWp_exp {Γ τ sR mG} (Φ : Post Γ τ) e δ γ μ :
    Φ (eval e δ) δ γ μ ⊢ @semWp Σ _ _ sR mG δ (stm_exp e) γ μ Φ.
  Proof.
    rewrite fixpoint_semWp_eq; cbn.
    iIntros "HΦ".
    iIntros (* (γ μ) *) "Hres %s' %δ' %γ' %μ' %Hs".
    destruct (smallinvstep Hs).
    rewrite semWp_val.
    now iFrame "HΦ Hres".
  Qed.

  Lemma semWp2_exp {Γ τ} (Φ : Post2 Γ Γ τ) eA eB δA δB :
    Φ (eval eA δA) δA (eval eB δB) δB ⊢ semWp2 δA δB (stm_exp eA) (stm_exp eB) Φ.
  Proof.
    rewrite /semWp2.
    iIntros "HΦ". iIntros (γ1 γ2 μ1 μ2).
    iExists (λ v δ γ μ, ⌜v = eval eA δA⌝ ∗ ⌜δ = δA⌝ ∗ ⌜γ = γ1⌝ ∗ ⌜μ = μ1⌝)%I,
            (λ v δ γ μ, ⌜v = eval eB δB⌝ ∗ ⌜δ = δB⌝ ∗ ⌜γ = γ2⌝ ∗ ⌜μ = μ2⌝)%I.
    repeat iSplitR.
    - now iApply semWp_exp.
    - now iApply semWp_exp.
    - rewrite fixpoint_max_steps_eq; cbn.
      iIntros (? ? ? ? ? ? ? ? HeA HeB).
      destruct (smallinvstep HeA), (smallinvstep HeB).
      rewrite max_steps_vals. iModIntro.
      iIntros (? ? ? ? ? ? ? ?) "((-> & -> & -> & ->) & -> & -> & -> & ->)".
      iFrame "HΦ".
  Qed.

  Lemma semWp_fail {Γ τ sR mG} (m : string) (Q : Post Γ τ) (δ : CStore Γ) (γ : RegStore) (μ : Memory) :
    @semWp Σ _ _ sR mG δ (fail m)%exp γ μ Q ⊣⊢ True.
  Proof.
    iSplit; auto; iIntros "_".
    rewrite fixpoint_semWp_eq; cbn.
    iIntros (* (γ μ) *) "Hres".
    iIntros (? ? ? ? Hfail).
    discriminate_step.
  Qed.

  Lemma semWp_bind {Γ τ σ sR mG} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
                    (Q : Post Γ τ) (δ : CStore Γ) (γ : RegStore) (μ : Memory) :
    @semWp _ _ _ sR mG δ s γ μ (λ v1 δ1 γ μ, @semWp _ _ _ sR mG δ1 (k v1) γ μ Q) ⊢
    @semWp Σ _ _ sR mG δ (stm_bind s k) γ μ Q.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (δ s γ μ).
    rewrite ?fixpoint_semWp_eq; cbn.
    iIntros (* (γ μ) *) "Hres".
    iIntros (? ? ? ? Hs).
    destruct (smallinvstep Hs); cbn.
    - now iFrame "Hres H".
    - rewrite semWp_fail. now iFrame "Hres".
    - stm_val_fail_stuck.
      iSpecialize ("H" with "Hres []"); first eauto.
      iIntros "!>".
      iDestruct "H" as "($ & H)".
      iApply ("IH" with "H").
  Qed.

  Lemma not_final_expanded : ∀ {Γ τ} {s : Stm Γ τ},
      ~ Final s -> stm_to_val s = None ∧ stm_to_fail s = None.
  Proof.
    intros Γ τ s H; unfold Final in H; destruct s; auto; contradiction.
  Qed.

  Lemma stm_to_val_not_fail {Γ τ} {s : Stm Γ τ} :
    forall {v}, stm_to_val s = Some v -> stm_to_fail s = None.
  Proof. intros; by destruct s. Qed.

  Lemma semWp_step {Γ τ sR mG} {s : Stm Γ τ} (δ : CStore Γ) (γ : RegStore) (μ : Memory) (POST : Post Γ τ) :
    ~ Final s ->
    (∀ γ μ γ' μ' δ' s',
        (regs_inv γ ∗ @mem_inv _ mG μ) -∗
        ⌜⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩⌝ -∗
         ▷ ((regs_inv γ' ∗ @mem_inv _ mG μ') ∗ @semWp _ _ _ sR mG δ' s' γ' μ' POST)) ⊢
    @semWp Σ _ _ sR mG δ s γ μ POST.
  Proof.
    iIntros (Hf).
    rewrite fixpoint_semWp_eq; cbn.
    destruct (not_final_expanded Hf) as (-> & _).
    iIntros "H Hres %s' %δ' %γ' %μ' %Hs".
    iSpecialize ("H" with "Hres []"); first auto.
    done.
  Qed.

  Lemma semWp_frame_r {Γ τ sR mG} {s : Stm Γ τ} (δ : CStore Γ) (γ : RegStore) (μ : Memory) (POST : Post Γ τ) {Q} :
    @semWp _ _ _ sR mG δ s γ μ POST ∗ Q ⊢
    @semWp Σ _ _ sR mG δ s γ μ (λ v δ γ μ, POST v δ γ μ ∗ Q).
  Proof.
    iLöb as "IH" forall (δ s γ μ).
    rewrite ?fixpoint_semWp_eq; cbn.
    case_match eqn:Esv; first auto.
    iIntros "(H & HQ) Hres %s' %δ' %γ' %μ' %Hs".
    iSpecialize ("H" with "Hres []"); first eauto.
    iIntros "!>".
    iDestruct "H" as "($ & H)".
    iApply ("IH" with "[$H $HQ]").
  Qed.

  Let sG_left : sailRegGS Σ := @sailRegGS2_sailRegGS_left _ (@sailGS2_regGS2 _ sG).
  Let sG_right : sailRegGS Σ := @sailRegGS2_sailRegGS_right _ (@sailGS2_regGS2 _ sG).
  Let mG_left := mc_memGS_left.
  Let mG_right := mc_memGS_right.

  Lemma semWp2_step_with_res_sep {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
                     (δ1 : CStore Γ1) (δ2 : CStore Γ2) (POST : Post2 Γ1 Γ2 τ) :
    ~ Final s1 ->
    ~ Final s2 ->
    (∀ γ1 γ2 μ1 μ2 γ1' γ2' μ1' μ2' δ1' δ2' s1' s2',
      ⌜⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩⌝ -∗
      ⌜⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩⌝ -∗ 
       ∃ POST1 POST2,
       (@regs_inv _ sG_left γ1 ∗ @mem_inv _ mG_left μ1 -∗ ▷ ((@regs_inv _ sG_left γ1' ∗ @mem_inv _ mG_left μ1') ∗ @semWp _ _ _ sG_left mG_left δ1' s1' γ1' μ1' POST1))
       ∗ (@regs_inv _ sG_right γ2 ∗ @mem_inv _ mG_right μ2 -∗ ▷ ((@regs_inv _ sG_right γ2' ∗ @mem_inv _ mG_right μ2') ∗ @semWp _ _ _ sG_right mG_right δ2' s2' γ2' μ2' POST2))
       ∗ ▷ max_steps δ1' δ2' s1' s2' γ1' γ2' μ1' μ2' (∀ v1 δ1 γ1 μ1 v2 δ2 γ2 μ2, POST1 v1 δ1 γ1 μ1 ∗ POST2 v2 δ2 γ2 μ2 -∗ POST v1 δ1 v2 δ2)) -∗
      semWp2 δ1 δ2 s1 s2 POST.
  Proof.
    iIntros (Hs1 Hs2) "H".
    destruct (not_final_expanded Hs1) as (Hs1v & Hs1f).
    destruct (not_final_expanded Hs2) as (Hs2v & Hs2f).
    pose proof (progress s1) as Hstep1.
    pose proof (progress s2) as Hstep2.
    destruct Hstep1 as [|Hstep1]; first contradiction.
    destruct Hstep2 as [|Hstep2]; first contradiction.
    rewrite /(semWp2 δ1).
    iIntros (γ1 γ2 μ1 μ2). iSpecialize ("H" $! γ1 γ2 μ1 μ2).
    destruct (Hstep1 γ1 μ1 δ1) as (γ1' & μ1' & δ1' & s1' & Hsteps1).
    destruct (Hstep2 γ2 μ2 δ2) as (γ2' & μ2' & δ2' & s2' & Hsteps2).
    iSpecialize ("H" with "[] []"); [eauto|eauto|].
    iDestruct "H" as "(%POST1 & %POST2 & Hwp1 & Hwp2 & H)".
    iExists POST1, POST2.
    iSplitL "Hwp1"; [|iSplitL "Hwp2"].
    - rewrite (fixpoint_semWp_eq δ1); cbn; stm_val_fail_stuck.
      iIntros "Hres %s' %δ' %γ' %μ' %Hsteps1'".
      destruct (step_deterministic Hsteps1 Hsteps1') as (<- & <- & <- & <-).
      iApply ("Hwp1" with "Hres").
    - rewrite (fixpoint_semWp_eq δ2); cbn; stm_val_fail_stuck.
      iIntros "Hres %s' %δ' %γ' %μ' %Hsteps2'".
      destruct (step_deterministic Hsteps2 Hsteps2') as (<- & <- & <- & <-).
      iApply ("Hwp2" with "Hres").
    - rewrite (fixpoint_max_steps_eq δ1); cbn; stm_val_fail_stuck.
      iIntros (? ? ? ? ? ? ? ? Hsteps1' Hsteps2').
      destruct (step_deterministic Hsteps1 Hsteps1') as (<- & <- & <- & <-).
      destruct (step_deterministic Hsteps2 Hsteps2') as (<- & <- & <- & <-).
      iFrame "H".
  Qed.

  Lemma semWp2_val_r {Γ τ} (s1 : Stm Γ τ) (v2 : Val τ) (POST : Post2 Γ Γ τ)
                     (δ1 δ2 : CStore Γ) :
    (∀ γ1 γ2 μ1 μ2,
      ∃ (POST1 POST2 : Post Γ τ),
     @semWp _ _ _ sG_left mG_left δ1 s1 γ1 μ1 POST1 ∗
     POST2 v2 δ2 γ2 μ2 ∗
     max_steps δ1 δ2 s1 (stm_val τ v2) γ1 γ2 μ1 μ2
       (∀ v1 δ1 γ1 μ1 v2 δ2 γ2 μ2, POST1 v1 δ1 γ1 μ1 ∗ POST2 v2 δ2 γ2 μ2 -∗ POST v1 δ1 v2 δ2)) -∗
    semWp2 δ1 δ2 s1 (stm_val τ v2) POST.
  Proof.
    iIntros "H".
    rewrite /(semWp2 δ1).
    iIntros (γ1 γ2 μ1 μ2).
    iDestruct ("H" $! γ1 γ2 μ1 μ2) as "(%POST1 & %POST2 & Hwp & HPOST2 & H)".
    iExists POST1, POST2.
    iFrame "Hwp H".
    now rewrite semWp_val.
  Qed.

  Lemma semWp2_bind_l_alt {Γ τ σ} (s1 : Stm Γ σ) (s2 : Stm Γ τ) (k1 : Val σ → Stm Γ τ)
    (POSTs : Post Γ σ) (POST : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
    (∀ γ1 μ1, @semWp _ _ _ sG_left mG_left δ1 s1 γ1 μ1 POSTs) -∗
    (∀ v1 δ1 γ1 μ1, POSTs v1 δ1 γ1 μ1 -∗ semWp2 δ1 δ2 (k1 v1) s2 POST) -∗
    semWp2 δ1 δ2 (stm_bind s1 k1) s2 POST.
  Proof.
    iLöb as "IH" forall (δ1 s1 δ2 s2).
    iIntros "Hwp H".
    destruct (stm_to_val s2) eqn:Es2v.
    - destruct s2; try discriminate; inversion Es2v; subst.
      iApply semWp2_val_r.
      iIntros (γ1 γ2 μ1 μ2).
      iSpecialize ("Hwp" $! γ1 μ1).
      pose proof (progress (stm_bind s1 k1)).
      destruct H as [H|H]; first contradiction.
      specialize (H γ1 μ1 δ1).
      destruct H as (γ1' & μ1' & δ1' & s1' & H).
      destruct (smallinvstep H).
      + rewrite semWp_val.
        iSpecialize ("H" with "Hwp").
        rewrite /(semWp2 δ1).
        iDestruct ("H" $! γ1 γ2 μ1 μ2) as "(%POST1 & %POST2 & Hwp1 & Hwp2 & H)".
        iExists POST1, POST2.
        rewrite semWp_val. iFrame "Hwp2".
        iSplitL "Hwp1".
        { iApply semWp_bind. now rewrite semWp_val. }
        admit (* TODO: add lemma for max_steps, we get an additional later in the goal, which is fine *).
      + admit (* TODO: fail case *).
      + (* TODO: we can get the laters by ensuring each semWp takes the same nr of steps (similar to max_steps),
                 we can then pull the later "before" the ∃ with bi.later_exist *)
        rewrite (fixpoint_semWp_eq δ1 s); cbn; stm_val_fail_stuck.
        setoid_rewrite (fixpoint_semWp_eq δ1 (stm_bind s k1)); cbn; stm_val_fail_stuck.
        (* NOTE: be clever with the existentials, maybe that'll help us make progress here *)
        (* NOTE: make the problem simpler, use free monad, no sep logic, ... *)
  Admitted.

  Lemma semWp2_bind_alt {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
    (POSTs : Post2 Γ Γ σ) (POST : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 s1 s2 POSTs -∗
    (∀ v1 δ1 v2 δ2, POSTs v1 δ1 v2 δ2 -∗ semWp2 δ1 δ2 (k1 v1) (k2 v2) POST) -∗
    semWp2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) POST.
  Proof.
    iLöb as "IH" forall (δ1 δ2 s1 s2).
    iIntros "Hs Hk".
    iApply semWp2_step_with_res_sep; [eauto|eauto|].
    iIntros (γ1 γ2 μ1 μ2 γ1' γ2' μ1' μ2' δ1' δ2' s1' s2' Hs1 Hs2).
    destruct (smallinvstep Hs1), (smallinvstep Hs2).
    - rewrite (semWp2_val _ _ _ _ _ γ1 γ2 μ1 μ2).
      iSpecialize ("Hk" with "Hs").
      rewrite /(semWp2 δ1).
      iDestruct ("Hk" $! γ1 γ2 μ1 μ2) as "(%POST1 & %POST2 & Hwp1 & Hwp2 & H)".
      iExists POST1, POST2.
      iSplitL "Hwp1"; [|iSplitL "Hwp2"].
      + iIntros "$". iFrame "Hwp1".
      + iIntros "$". iFrame "Hwp2".
      + iFrame "H".
    - admit (* fail case *).
  Admitted.

  Lemma semWp2_bind {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
    (POST : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12 δ22 (k1 v1) (k2 v2) POST) ⊢
      semWp2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) POST.
  Proof.
  Admitted.

  Lemma semWp2_block {Γ1 Γ2 τ Δ1 Δ2} (δΔ1 : CStore Δ1) (δΔ2 : CStore Δ2) (s1 : Stm (Γ1 ▻▻ Δ1) τ) (s2 : Stm (Γ2 ▻▻ Δ2) τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ1 → Val τ → CStore Γ2 → iProp Σ) (δ1 : CStore Γ1) (δ2 : CStore Γ2),
        semWp2 (δ1 ►► δΔ1) (δ2 ►► δΔ2) s1 s2 (fun v1 δ21 v2 δ22 => Q v1 (env.drop Δ1 δ21) v2 (env.drop Δ2 δ22)) -∗
        semWp2 δ1 δ2 (stm_block δΔ1 s1) (stm_block δΔ2 s2) Q.
  Proof.
  Admitted.

  Lemma semWp2_let {Γ τ x σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm (Γ ▻ x∷σ) τ)
    (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
    ⊢ semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12.[x∷σ ↦ v1] δ22.[x∷σ ↦ v2] k1 k2 (fun v12 δ13 v22 δ23 => Q v12 (env.tail δ13) v22 (env.tail δ23)) ) -∗
        semWp2 δ1 δ2 (let: x ∷ σ := s1 in k1)%exp (let: x ∷ σ := s2 in k2)%exp Q.
  Proof.
  Admitted.

  Lemma semWp2_seq {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Stm Γ τ) :
    ⊢ ∀ (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ),
        semWp2 δ1 δ2 s1 s2 (fun v1 δ21 v2 δ22 => semWp2 δ21 δ22 k1 k2 Q) -∗ semWp2 δ1 δ2 (s1;;k1)%exp (s2;;k2)%exp Q.
  Proof.
  Admitted.

  Lemma semWp2_assertk {Γ τ} (e11 e21 : Exp Γ ty.bool) (e12 e22 : Exp Γ ty.string) (k1 k2 : Stm Γ τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        ⌜eval e11 δ1 = eval e21 δ2⌝ -∗
        (⌜eval e11 δ1 = true⌝ → ⌜eval e21 δ2 = true⌝ → semWp2 δ1 δ2 k1 k2 Q) -∗
        semWp2 δ1 δ2 (stm_assertk e11 e12 k1) (stm_assertk e21 e22 k2) Q.
  Proof.
  Admitted.

  Lemma semWp2_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg v1 v2 -∗ Q v1 δ1 v2 δ2)) -∗
        semWp2 δ1 δ2 (stm_read_register reg) (stm_read_register reg) Q.
  Proof.
  Admitted.

  Lemma semWp2_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e1 e2 : Exp Γ τ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ),
        (∃ v1 v2 : Val τ, reg_pointsTo2 reg v1 v2 ∗ (reg_pointsTo2 reg (eval e1 δ1) (eval e2 δ2) -∗ Q (eval e1 δ1) δ1 (eval e2 δ2) δ2)) -∗
        semWp2 δ1 δ2 (stm_write_register reg e1) (stm_write_register reg e2) Q.
  Proof.
  Admitted.

  (* TODO: notation for cstore update not working? (import env.notations doesn't solve it) Investigate and define lemma *)
  (* Lemma semWp2_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s1 s2 : Stm Γ τ) : *)
  (*   ⊢ ∀ (Q : Val τ → CStore Γ → Val τ → CStore Γ → iProp Σ) (δ1 δ2 : CStore Γ), *)
  (*       semWp2 δ1 δ2 s1 s2 (λ v1 δ21 v2 δ22, Q v1 (δ21 ⟪ x ↦ v1 ⟫) v2 (δ22 ⟪ x ↦ v2 ⟫)) -∗ *)
  (*       semWp2 δ1 δ2 (stm_assign x s1) (stm_assign x s2) Q. *)
  (* Proof. *)
  (* Admitted. *)

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
  Admitted.

  Lemma semWp2_foreign {Γ Δ τ} {f1 f2 : 𝑭𝑿 Δ τ} {es1 es2 : NamedEnv (Exp Γ) Δ} {Q δ1 δ2} :
    ⊢ (∀ γ1 γ2 μ1 μ2,
          (regs_inv2 γ1 γ2 ∗ mem_inv2 _ μ1 μ2)
          ={⊤,∅}=∗
      (∀ res1 γ1' μ1' res2 γ2' μ2',
        ⌜ ForeignCall f1 (evals es1 δ1) res1 γ1 γ1' μ1 μ1' ⌝
        ∗ ⌜ ForeignCall f2 (evals es2 δ2) res2 γ2 γ2' μ2 μ2' ⌝
        ={∅}▷=∗
         |={∅,⊤}=>
         (regs_inv2 γ1' γ2' ∗ mem_inv2 _ μ1' μ2') ∗
                    semWp2 δ1 δ2 (match res1 with inr v => stm_val _ v
                                             | inl s => stm_fail _ s
                                  end)
                    (match res2 with inr v => stm_val _ v
                                | inl s => stm_fail _ s
                     end)
                    Q)) -∗
      semWp2 δ1 δ2 (stm_foreign f1 es1) (stm_foreign f2 es2) Q.
  Proof.
  Admitted.

  Lemma semWp2_debugk {Γ τ} (s1 s2 : Stm Γ τ) :
    ⊢ ∀ Q δ1 δ2, semWp2 δ1 δ2 s1 s2 Q -∗ semWp2 δ1 δ2 (stm_debugk s1) (stm_debugk s2) Q.
  Proof.
  Admitted.

  Lemma semWp2_lemmak {Γ τ} {Δ} (l1 l2 : 𝑳 Δ) (es1 es2 : NamedEnv (Exp Γ) Δ) (s1 s2 : Stm Γ τ) :
    ⊢ ∀ Q δ1 δ2, semWp2 δ1 δ2 s1 s2 Q -∗ semWp2 δ1 δ2 (stm_lemmak l1 es1 s1) (stm_lemmak l2 es2 s2) Q.
  Proof.
  Admitted.
  End WithSailGS2.
End IrisBinaryWPAsymmetricLaws.

Module Type IrisSignatureRules2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB).

  (* We fix the binary wp to the asymmetric one. A different one would have
     different laws. *)
  Module Export IWPLaws := IrisBinaryWPAsymmetricLaws B SIG PROG SEM IB IPred.

  Section WithSailGS2.
  Context `{sG : sailGS2 Σ}.

Section Soundness.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗
           semWp2 δ δ s s (fun v1 δ1 v2 δ2 => ⌜ v1 = v2 ⌝ ∗ ⌜ δ1 = δ2 ⌝ ∗ POST v1 δ1)%I.
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
        {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "Htriple P".
    iApply (semWp2_mono with "[Htriple P]").
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
  (*   iPoseProof (semWp2_frame_l with "[HR Htriple]") as "Hwp". *)
  (*   { iSplitL "HR". iExact "HR". iExact "Htriple". } *)
  (*   iApply (semWp2_mono with "Hwp"). *)
  (*   iIntros (? ? ? ?) "($ & $ & $ & $)". *)
  (* Qed. *)
  Admitted.

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
    iApply semWp2_val_1.
    iSpecialize ("PQ" with "P").
    by iFrame.
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q).
  Proof.
    iIntros "PQ P".
    iApply semWp2_exp.
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
    iApply semWp2_let.
    iSpecialize ("Hs" with "P").
    iApply (semWp2_mono with "Hs").
    iIntros (v1 δ1 v2 δ2) "(<- & <- & Q)".
    iSpecialize ("Hk" $! v1 δ1 with "Q").
    iApply (semWp2_mono with "Hk").
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
