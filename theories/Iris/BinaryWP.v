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

Module Type IrisBinaryWPParameters
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB).

  #[local] Notation step_sig :=
    (forall {Γ τ},
        RegStore -> Memory -> CStore Γ ->
        RegStore -> Memory -> CStore Γ ->
        Stm Γ τ -> Stm Γ τ ->
        Prop).

  Parameter reg_inv    : forall `{sG : sailRegGS2 Σ}, RegStore -> RegStore -> iProp Σ.
  Parameter mem_inv    : forall `{sG : sailGS2 Σ}, Memory -> Memory -> iProp Σ.
  Parameter step_left  : step_sig.
  Parameter step_right : step_sig.

  Global Transparent step_left.
  Global Transparent step_right.
End IrisBinaryWPParameters.

(* TODO: provided so that case study still compiles, this is not what we actually want *)
Module IrisBinaryWPSymmetric (B : Base) (SIG : Signature B) (PROG : Program B)
  (SEM : Semantics B PROG) (IB : IrisBase2 B PROG SEM) (IPred : IrisPredicates2 B SIG PROG SEM IB)
  <: IrisBinaryWPParameters B SIG PROG SEM IB IPred.
  Import SEM IB.

  Definition reg_inv    := @regs_inv2.
  Definition mem_inv    := @mem_inv2_sail.
  Definition step_left  := @Step.
  Definition step_right := @Step.
End IrisBinaryWPSymmetric.

(* IrisBinaryWPAsymmetric allows asymmetry between the executions. The left
   program is allowed to take zero or one step, the right one always needs to
   be able to take a step. *)
Module IrisBinaryWPAsymmetric (B : Base) (SIG : Signature B) (PROG : Program B)
  (SEM : Semantics B PROG) (IB : IrisBase2 B PROG SEM) (IPred : IrisPredicates2 B SIG PROG SEM IB)
  <: IrisBinaryWPParameters B SIG PROG SEM IB IPred.
  Import B SIG PROG SEM IB IPred.

  Definition Step_zero_or_one {Γ : PCtx} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ)
    (γ2 : RegStore) (μ2 : Memory) (δ2 : CStore Γ) (s1 s2 : Stm Γ σ) : Prop :=
    match stm_to_val s1 with
    | Some v1 => s1 = s2 ∧ γ1 = γ2 ∧ δ1 = δ2 ∧ μ1 = μ2
    | _       =>
        match stm_to_fail s1 with
        | Some m1 => s1 = s2 ∧ γ1 = γ2 ∧ δ1 = δ2 ∧ μ1 = μ2
        | _       => ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩
        end
    end.

  Inductive StepsPlus (Γ : PCtx) (σ : Ty) (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ)
    : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> Prop :=
  | step_once : ∀ (γ2 : RegStore) (μ2 : Memory) (δ2 : CStore Γ) (s2 : Stm Γ σ),
                   ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
                   StepsPlus γ1 μ1 δ1 s1 γ2 μ2 δ2 s2
  | step_more : ∀ (γ2 γ3 : RegStore) (μ2 μ3 : Memory) (δ2 δ3 : CStore Γ) (s2 s3 : Stm Γ σ),
                   ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩
                   → StepsPlus γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 → StepsPlus γ1 μ1 δ1 s1 γ3 μ3 δ3 s3.

  (* Inductive StepsAtMostOnce (Γ : PCtx) (σ : Ty) (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ)
    : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> Prop :=
  | step_refl : StepsAtMostOnce γ1 μ1 δ1 s1 γ1 μ1 δ1 s1
  | step_one  : ∀ (γ2 γ3 : RegStore) (μ2 μ3 : Memory) (δ2 δ3 : CStore Γ) (s2 s3 : Stm Γ σ),
                   ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
                   StepsAtMostOnce γ1 μ1 δ1 s1 γ2 μ2 δ2 s2. *)
  Inductive StepsAtMostOnce (Γ : PCtx) (σ : Ty) (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ)
    : Stm Γ σ -> RegStore -> Memory -> CStore Γ -> Stm Γ σ -> Prop :=
  | step_val  : ∀ (v : Val σ), StepsAtMostOnce γ1 μ1 δ1 (stm_val σ v) γ1 μ1 δ1 (stm_val σ v) 
  | step_fail : ∀ (m : string), StepsAtMostOnce γ1 μ1 δ1 (stm_fail σ m) γ1 μ1 δ1 (stm_fail σ m) 
  | step_refl : ∀ (s : Stm Γ σ), StepsAtMostOnce γ1 μ1 δ1 s γ1 μ1 δ1 s
  | step_one  : ∀ (γ2 γ3 : RegStore) (μ2 μ3 : Memory) (δ2 δ3 : CStore Γ) (s1 s2 s3 : Stm Γ σ),
                   ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
                   StepsAtMostOnce γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.

  (* TODO: would rather use the brackets for other step definitions, but these don't work?
           Should move the definition and notation into SmallStep/Step.v and properly investigate... *)
  Notation "⟪ γ1 , μ1 , δ1 , s1 ⟫ --->? ⟪ γ2 , μ2 , δ2 , s2 ⟫" := (@Step_zero_or_one _ _ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2).
  (* TODO: maybe we should make it step one or more? feels odd to allow
     zero steps, that means one execution doesn't have to make any progress? *)

  Definition steps Γ σ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 :=
    @Steps Γ σ γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.
  #[global] Arguments steps Γ σ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 /.

  Definition steps_plus Γ σ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 :=
    @StepsPlus Γ σ γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.
  #[global] Arguments steps_plus Γ σ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 /.

  Definition steps_at_most_once Γ σ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 :=
    @StepsAtMostOnce Γ σ γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.
  #[global] Arguments steps_at_most_once Γ σ γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 /.

  Definition reg_inv    := @regs_inv2.
  Definition mem_inv    := @mem_inv2_sail.
  (* Definition step_left  := @Step_zero_or_one. *)
  (* Definition step_left  := steps. *)
  (* Definition step_left  := steps_plus. *)
  Definition step_left  := steps_at_most_once.
  #[global] Arguments step_left /.
  Definition step_right := @Step.
  #[global] Arguments step_right /.
End IrisBinaryWPAsymmetric.

Module IrisBinaryWP
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB)
  (Import IWP   : IrisBinaryWPParameters B SIG PROG SEM IB IPred).

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
    Val τ -> CStore Γ -> iProp Σ.
  Canonical Structure PostO Γ τ := leibnizO (Post Γ τ).

  Definition Wp {Γ τ} :=
    CStore Γ -d> Stm Γ τ -d> Post Γ τ -d> iProp Σ.

  Definition Wp2 {Γ1 Γ2 τ} :=
    CStore Γ1 -d> CStore Γ2 -d>
    Stm Γ1 τ -d> Stm Γ2 τ -d>
    Post2 Γ1 Γ2 τ -d>
    iProp Σ.

  (* TODO: no steps for val, fail, otherwise one of the following:
     - right has to take a step
     - left has to take a step
     - both take a step
     This forces progress but still allows steps to differ *)
  (* TODO: simplify by using Final? instead of explicit val, fail cases... *)
  Inductive StepsAtMostOnce (Γ1 Γ2 : PCtx) (σ : Ty) (γ1 γ2 : RegStore)
    (μ1 μ2 : Memory) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    Stm Γ1 σ -> RegStore -> Memory -> CStore Γ1 -> Stm Γ1 σ ->
    Stm Γ2 σ -> RegStore -> Memory -> CStore Γ2 -> Stm Γ2 σ -> Prop :=
  | step_vals  : ∀ (v1 v2 : Val σ), StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 (stm_val σ v1) γ1 μ1 δ1 (stm_val σ v1) (stm_val σ v2) γ2 μ2 δ2 (stm_val σ v2)
  | step_val_l : ∀ (v1 : Val σ) (γ2' : RegStore) (μ2' : Memory) (δ2' : CStore Γ2) (s2 s2' : Stm Γ2 σ),
      ⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 (stm_val σ v1) γ1 μ1 δ1 (stm_val σ v1) s2 γ2' μ2' δ2' s2'
  | step_val_r : ∀ (v2 : Val σ) (γ1' : RegStore) (μ1' : Memory) (δ1' : CStore Γ1) (s1 s1' : Stm Γ1 σ),
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 s1 γ1' μ1' δ1' s1' (stm_val σ v2) γ2 μ2 δ2 (stm_val σ v2)
  | step_fails  : ∀ (m1 m2 : string), StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 (stm_fail σ m1) γ1 μ1 δ1 (stm_fail σ m1) (stm_fail σ m2) γ2 μ2 δ2 (stm_fail σ m2)
  | step_fail_l : ∀ (m1 : string) (γ2' : RegStore) (μ2' : Memory) (δ2' : CStore Γ2) (s2 s2' : Stm Γ2 σ),
      ⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 (stm_fail σ m1) γ1 μ1 δ1 (stm_fail σ m1) s2 γ2' μ2' δ2' s2'
  | step_fail_r : ∀ (m2 : string) (γ1' : RegStore) (μ1' : Memory) (δ1' : CStore Γ1) (s1 s1' : Stm Γ1 σ),
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 s1 γ1' μ1' δ1' s1' (stm_fail σ m2) γ2 μ2 δ2 (stm_fail σ m2)
  (* | step_r : ∀ (s1 : Stm Γ1 σ) (γ2' : RegStore) (μ2' : Memory) (δ2' : CStore Γ2) (s2 s2' : Stm Γ2 σ),
      ⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 s1 γ1 μ1 δ1 s1 s2 γ2' μ2' δ2' s2'
  | step_l : ∀ (s2 : Stm Γ2 σ) (γ1' : RegStore) (μ1' : Memory) (δ1' : CStore Γ1) (s1 s1' : Stm Γ1 σ),
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 s1 γ1' μ1' δ1' s1' s2 γ2 μ2 δ2 s2. *)
  | step_lr : ∀ (γ1' : RegStore) (μ1' : Memory) (δ1' : CStore Γ1) (s1 s1' : Stm Γ1 σ)
      (γ2' : RegStore) (μ2' : Memory) (δ2' : CStore Γ2) (s2 s2' : Stm Γ2 σ),
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ1', μ1', δ1', s1' ⟩ ->
      ⟨ γ2, μ2, δ2, s2 ⟩ ---> ⟨ γ2', μ2', δ2', s2' ⟩ ->
      StepsAtMostOnce γ1 γ2 μ1 μ2 δ1 δ2 s1 γ1' μ1' δ1' s1' s2 γ2' μ2' δ2' s2'.

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
  end.

  Ltac solve_contractive_more_arities := solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | f_equiv_more_arities]).

  Definition semWp_fix {Γ τ} (wp : Wp) : Wp :=
    (λ (δ : CStore Γ) (s : Stm Γ τ) (POST : Post Γ τ),
      match stm_to_val s with
      | Some v => |={∅,⊤}=> POST v δ
      | _      => (* TODO: ignoring fail for now... *)
          (* TODO: only allowing right... incorporate left as well... *)
          (∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
              (reg_inv γ1 γ2 ∗ mem_inv μ1 μ2 -∗
               (∀ (s' : Stm Γ τ) (δ' : CStore Γ)
                  (γ' : RegStore) (μ' : Memory),
                   ⌜⟨ γ2, μ2, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩⌝ ={∅}▷=∗
                    (reg_inv γ1 γ' ∗ mem_inv μ1 μ') ∗ wp δ' s' POST)))
      end)%I.
  Global Arguments semWp_fix {_}%ctx_scope {_} wp /.

  Global Instance semWp_fix_Contractive {Γ τ} :
    Contractive (@semWp_fix Γ τ).
  Proof. unfold Wp; solve_contractive_more_arities. Qed.

  Definition semWp {Γ τ} : Wp :=
    λ δ s POST, (fixpoint (@semWp_fix Γ τ)) δ s POST.

  Lemma fixpoint_semWp_fix_eq {Γ τ} (δ : CStore Γ) (s : Stm Γ τ)
    (POST : Post Γ τ) :
    fixpoint semWp_fix δ s POST ≡ semWp_fix (fixpoint semWp_fix) δ s POST.
  Proof. exact: (fixpoint_unfold semWp_fix δ s POST). Qed.

  Lemma fixpoint_semWp_eq {Γ τ} (δ : CStore Γ) (s : Stm Γ τ)
    (POST : Post Γ τ) :
    semWp δ s POST ≡ semWp_fix semWp δ s POST.
  Proof. by unfold semWp; rewrite fixpoint_semWp_fix_eq. Qed.

  Definition semWp2_fix {Γ1 Γ2 τ}
    (wp : Wp2) : Wp2 :=
    (λ (δ1 : CStore Γ1) (δ2 : CStore Γ2)
         (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
         (POST : Post2 Γ1 Γ2 τ),
      match stm_to_val s1, stm_to_fail s1 with
      | Some v1, _       => semWp δ2 s2 (λ v2 δ2, POST v1 δ1 v2 δ2)
      (* | _      , Some m1 => |={∅,⊤}=> False *) (* TODO: not implemented yet, just false for now... *)
      | _      , _       =>
              (∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory),
                  (reg_inv γ1 γ2 ∗ mem_inv μ1 μ2 -∗
                   (∀ (s12 : Stm Γ1 τ) (δ12 : CStore Γ1)
                      (γ12 : RegStore) (μ12 : Memory),
                       ⌜⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ12, μ12, δ12, s12 ⟩ ⌝
                       ={∅}▷=∗
                            (reg_inv γ12 γ2 ∗ mem_inv μ12 μ2) ∗
                            wp δ12 δ2 s12 s2 POST)))
      end)%I.
  Global Arguments semWp2_fix {_ _}%ctx_scope {_} wp /.

  Global Instance semWp2_fix_Contractive {Γ1 Γ2 τ} :
    Contractive (@semWp2_fix Γ1 Γ2 τ).
  Proof.
    unfold Wp2.
    solve_contractive_more_arities.
  Qed.

  Definition semWp2_close {Γ1 Γ2 τ} : Wp2 :=
    λ δ1 δ2 s1 s2 POST, (fixpoint (@semWp2_fix Γ1 Γ2 τ)) δ1 δ2 s1 s2 POST.

  Lemma fixpoint_semWp2_fix_eq {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (POST : Post2 Γ1 Γ2 τ) :
    fixpoint semWp2_fix δ1 δ2 s1 s2 POST ≡ semWp2_fix (fixpoint semWp2_fix) δ1 δ2 s1 s2 POST.
  Proof. exact: (fixpoint_unfold semWp2_fix δ1 δ2 s1 s2 POST). Qed.

  Lemma fixpoint_semWp2_close_eq {Γ1 Γ2 τ} (δ1 : CStore Γ1) (δ2 : CStore Γ2)
    (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) (POST : Post2 Γ1 Γ2 τ) :
    semWp2_close δ1 δ2 s1 s2 POST ≡ semWp2_fix semWp2_close δ1 δ2 s1 s2 POST.
  Proof. by unfold semWp2_close; rewrite fixpoint_semWp2_fix_eq. Qed.

  Definition semWp2_open {Γ1 Γ2 τ} : Wp2 :=
    (λ (δ1 : CStore Γ1) (δ2 : CStore Γ2)
         (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
         (POST : Post2 Γ1 Γ2 τ),
      |={⊤,∅}=> semWp2_close δ1 δ2 s1 s2 POST)%I.
  Arguments semWp2_open _ _ _ /.

  Definition semWp2 {Γ1 Γ2 τ} := @semWp2_open Γ1 Γ2 τ.

  Lemma semWp2_unfold {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (δ1 : CStore Γ1) (δ2 : CStore Γ2) (POST : Post2 Γ1 Γ2 τ) :
    semWp2 δ1 δ2 s1 s2 POST ⊣⊢ |={⊤,∅}=> semWp2_close δ1 δ2 s1 s2 POST.
  Proof. by unfold semWp2, semWp2_open. Qed.
    
  End WithSailGS2.
End IrisBinaryWP.

Module IrisBinaryWPAsymmetricLaws
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB).

  Module Export IWPP := IrisBinaryWPAsymmetric B SIG PROG SEM IB IPred.
  Module Export IWP := IrisBinaryWP B SIG PROG SEM IB IPred IWPP.

  Section WithSailGS2.
  Context `{sG : sailGS2 Σ}.

  Import SmallStepNotations.

  Lemma semWp_mono [Γ τ] (s : Stm Γ τ) (Q1 Q2 : Post Γ τ) (δ : CStore Γ) :
    ⊢ semWp δ s Q1 -∗ (∀ v δ, Q1 v δ -∗ Q2 v δ) -∗ semWp δ s Q2.
  Proof.
    iIntros "H HQ".
    iLöb as "IH" forall (δ s).
    rewrite ?fixpoint_semWp_eq; cbn.
    case_match eqn:Esv.
    - iMod "H". iModIntro.
      by iApply "HQ".
    - iIntros (? ? ? ?) "Hres".
      iIntros (s' δ' γ' μ' Hs).
      iSpecialize ("H" with "Hres []"); first eauto.
      iMod "H". iIntros "!> !>". iMod "H" as "($ & H)".
      iModIntro. iApply ("IH" with "H HQ").
  Qed.

  Lemma semWp2_close_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (Q1 Q2 : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    ⊢ semWp2_close δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWp2_close δ1 δ2 s1 s2 Q2.
  Proof.
    iIntros "H HQ".
    iLöb as "IH" forall (δ1 δ2 s1 s2).
    rewrite (fixpoint_semWp2_close_eq _ _ s1).
    rewrite (fixpoint_semWp2_close_eq _ _ s1).
    cbn.
    repeat case_match; try done.
    - iApply (semWp_mono with "H HQ").
    - iIntros (γ1 γ2 μ1 μ2) "Hres".
      iSpecialize ("H" with "Hres").
      iIntros (? ? ? ?) "Hsteps".
      iSpecialize ("H" with "Hsteps").
      iMod "H". iIntros "!> !>". iMod "H" as "($ & H)".
      iModIntro. iApply ("IH" with "H HQ").
  Qed.

  Lemma semWp2_mono [Γ1 Γ2 τ] (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (Q1 Q2 : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    ⊢ semWp2 δ1 δ2 s1 s2 Q1 -∗ (∀ v1 δ1 v2 δ2, Q1 v1 δ1 v2 δ2 -∗ Q2 v1 δ1 v2 δ2) -∗ semWp2 δ1 δ2 s1 s2 Q2.
  Proof.
    rewrite ?semWp2_unfold.
    iIntros "H HQ". iMod "H". iModIntro.
    now iApply (semWp2_close_mono with "H").
  Qed.

  Lemma semWp_val {Γ τ} (v : Val τ) (Q : Post Γ τ) :
    forall δ,
      semWp δ (stm_val τ v) Q ⊣⊢ |={∅,⊤}=> Q v δ.
  Proof.
    iIntros (δ).
    iSplit; iIntros "H";
      rewrite fixpoint_semWp_eq; cbn; auto.
  Qed.

  Lemma semWp2_close_val_l {Γ1 Γ2 τ} (v1 : Val τ) (s2 : Stm Γ2 τ)
                           (Q : Post2 Γ1 Γ2 τ) :
    forall δ1 δ2,
      semWp2_close δ1 δ2 (stm_val τ v1) s2 Q ⊣⊢ semWp δ2 s2 (Q v1 δ1).
  Proof.
    intros δ1 δ2.
    iSplit; iIntros "H";
      rewrite fixpoint_semWp2_close_eq; cbn; done.
  Qed.

  Lemma semWp2_close_val {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
    forall δ1 δ2,
      (semWp2_close δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q) ⊣⊢ |={∅,⊤}=> Q v1 δ1 v2 δ2.
  Proof. intros; rewrite semWp2_close_val_l semWp_val; done. Qed.

  Lemma semWp2_val {Γ1 Γ2 τ} (v1 : Val τ) (v2 : Val τ) (Q : Post2 Γ1 Γ2 τ) :
    forall δ1 δ2,
      semWp2 δ1 δ2 (stm_val τ v1) (stm_val τ v2) Q ⊣⊢ |={⊤}=> Q v1 δ1 v2 δ2.
  Proof.
    iIntros (δ1 δ2).
    rewrite semWp2_unfold; rewrite semWp2_close_val.
    iSplit; iIntros "H".
    - now repeat iMod "H".
    - iMod "H".
      now iApply fupd_mask_intro_subseteq; first set_solver.
  Qed.

  Lemma fupd_semWp {Γ τ} (δ : CStore Γ) (s : Stm Γ τ) Φ :
    (|={∅}=> semWp δ s Φ) ⊢ semWp δ s Φ.
  Proof.
    rewrite fixpoint_semWp_eq; cbn.
    iIntros "H".
    repeat case_match;
      iMod "H"; done.
  Qed.

  Lemma semWp_fupd {Γ τ} (δ : CStore Γ) (s : Stm Γ τ) Φ :
    semWp δ s Φ ⊢ |={∅}=> semWp δ s Φ.
  Proof. by iIntros "H !>". Qed.

  Lemma semWp_fupd_intro {Γ τ} (δ : CStore Γ) (s : Stm Γ τ) Φ :
    (|={∅}=> semWp δ s (λ v δ, |={∅}=> Φ v δ)) ⊢ semWp δ s Φ.
  Proof.
    iLöb as "IH" forall (δ s).
    rewrite ?fixpoint_semWp_eq; cbn.
    case_match eqn:Esv.
    - iIntros "H".
      repeat iMod "H".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iMod "H". iMod "Hclose". done.
    - iIntros "H".
      iIntros (? ? ? ?) "Hres".
      iIntros (? ? ? ? Hs). iMod "H".
      iSpecialize ("H" with "Hres []"); first eauto.
      iMod "H". iIntros "!> !>". iMod "H" as "($ & H)".
      iSpecialize ("IH" with "[H]"); now iModIntro.
  Qed.

  Lemma fupd_semWp2_close {Γ1 Γ2 τ} (δA : CStore Γ1) (δB : CStore Γ2)
    (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) Φ : 
    (|={∅}=> semWp2_close δA δB eA eB Φ) ⊢ semWp2_close δA δB eA eB Φ.
  Proof.
    rewrite fixpoint_semWp2_close_eq; cbn.
    iIntros "H".
    repeat case_match.
    - by iApply fupd_semWp.
    - now repeat iMod "H".
  Qed.

  Lemma fupd_semWp2 {Γ1 Γ2 τ} E (δA : CStore Γ1) (δB : CStore Γ2)
    (eA : Stm Γ1 τ) (eB : Stm Γ2 τ) Φ : 
    (|={E}=> semWp2 δA δB eA eB Φ) ⊢ semWp2 δA δB eA eB Φ.
  Proof.
    rewrite ?semWp2_unfold.
    rewrite fixpoint_semWp2_close_eq; cbn; unfold semWp2_fix.
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
    rewrite ?semWp2_unfold ?fixpoint_semWp2_close_eq; cbn.
    iIntros (HeA HeB) "HP".
    repeat case_match;
      inversion HeA;
      inversion HeB; iIntros "H";
      try done.
    - iMod "H". iModIntro.
      iIntros (? ? ? ?) "Hres".
      iSpecialize ("H" with "Hres").
      iIntros (? ? ? ?) "Hsteps".
      iSpecialize ("H" with "Hsteps").
      iMod "H". iIntros "!> !>". iMod "H". iModIntro.
      iDestruct "H" as "($ & H)".
      iApply (semWp2_close_mono with "H").
      iIntros (? ? ? ?) "HPΦ".
      iApply ("HPΦ" with "HP").
  Qed.

  Lemma semWp_frame_l {Γ τ} (δ : CStore Γ) (s : Stm Γ τ) (POST : Post Γ τ)
                      (R : iProp Σ) :
    R ∗ semWp δ s POST -∗
    semWp δ s (λ v δ, R ∗ POST v δ).
  Proof.
    iIntros "(R & H)".
    iApply (semWp_mono with "H").
    iFrame "R"; auto.
  Qed.

  Lemma semWp2_frame_l {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    (δ1 : CStore Γ1) (δ2 : CStore Γ2) (POST : Post2 Γ1 Γ2 τ)
    (R : iProp Σ) :
    R ∗ semWp2 δ1 δ2 s1 s2 POST -∗
    semWp2 δ1 δ2 s1 s2 (fun v1 δ1 v2 δ2 => R ∗ POST v1 δ1 v2 δ2).
  Proof.
    iIntros "(R & Hwp)".
    iApply (semWp2_mono with "Hwp").
    iIntros; by iFrame.
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

  Lemma semWp_exp {Γ τ} (Φ : Post Γ τ) e δ :
    Φ (eval e δ) δ ⊢ |={⊤,∅}=> semWp δ (stm_exp e) Φ.
  Proof.
    rewrite fixpoint_semWp_eq; cbn.
    iIntros "HΦ".
    close_later "Hclose". iModIntro.
    iIntros (? ? ? ?) "Hres".
    iIntros (? ? ? ? Hs).
    destruct (smallinvstep Hs).
    iFrame "Hres". rewrite semWp_val.
    iIntros "!> !> !>". now iMod "Hclose".
  Qed.

  Lemma semWp2_exp {Γ τ} (Φ : Post2 Γ Γ τ) eA eB δA δB :
    Φ (eval eA δA) δA (eval eB δB) δB ⊢ semWp2 δA δB (stm_exp eA) (stm_exp eB) Φ.
  Proof.
    rewrite semWp2_unfold.
    rewrite fixpoint_semWp2_close_eq; cbn.
    iIntros "HΦ".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (γ11 γ21 μ11 μ21) "Hres".
    iIntros (s12 δ12 γ12 μ12 HeA).
    destruct (smallinvstep HeA).
    rewrite semWp2_close_val_l semWp_exp.
    iFrame "Hres". iMod "Hclose".
    now iMod "HΦ".
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
    rewrite (fixpoint_semWp2_close_eq _ _ s); cbn;
    semWp2_stuck_progress.

  Lemma semWp_fail {Γ τ} (m : string) (Q : Post Γ τ) (δ : CStore Γ) :
    semWp δ (fail m)%exp Q ⊣⊢ True.
  Proof.
    iSplit; auto; iIntros "_".
    rewrite fixpoint_semWp_eq; cbn.
    iIntros (? ? ? ?) "Hres".
    iIntros (? ? ? ? Hfail).
    discriminate_step.
  Qed.

  Lemma semWp2_close_fail_l {Γ1 Γ2 τ} (m1 : string) (s2 : Stm Γ2 τ)
    (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    semWp2_close δ1 δ2 (fail m1)%exp s2 Q ⊣⊢ True.
  Proof.
    iSplit; auto; iIntros "_".
    rewrite fixpoint_semWp2_close_eq; cbn.
    iIntros (? ? ? ?) "Hres".
    iIntros (? ? ? ? Hfail).
    discriminate_step.
  Qed.

  Lemma not_final_expanded : ∀ {Γ τ} (s : Stm Γ τ),
      ~ Final s -> stm_to_val s = None ∧ stm_to_fail s = None.
  Proof.
    intros Γ τ s H; unfold Final in H; destruct s; auto; contradiction.
  Qed.

  Lemma stm_to_val_not_fail {Γ τ} {s : Stm Γ τ} :
    forall {v}, stm_to_val s = Some v -> stm_to_fail s = None.
  Proof. intros; by destruct s. Qed.

  Lemma semWp2_close_val_step_r {Γ τ} (s21 s22 : Stm Γ τ) (v1 : Val τ)
    γ1 γ21 γ22 μ1 μ21 μ22 δ21 δ22 
    (Q : Post2 Γ Γ τ) (δ1 : CStore Γ) :
    ⟨ γ21, μ21, δ21, s21 ⟩ ---> ⟨ γ22, μ22, δ22, s22 ⟩ ->
    (reg_inv sailGS2_regGS2 γ1 γ21 ∗ mem_inv sG μ1 μ21) ∗ semWp2_close δ1 δ21 (stm_val τ v1) s21 Q ={∅}▷=∗
     ((reg_inv sailGS2_regGS2 γ1 γ22 ∗ mem_inv sG μ1 μ22) ∗ semWp2_close δ1 δ22 (stm_val τ v1) s22 Q).
  Proof.
    iIntros (Hsteps) "(Hres & Hwp)".
    rewrite fixpoint_semWp2_close_eq; cbn.
    rewrite fixpoint_semWp_eq; cbn.
    stm_val_fail_stuck. iSpecialize ("Hwp" with "Hres []"); first eauto.
    iMod "Hwp". iIntros "!> !>". iMod "Hwp" as "($ & Hwp)". iModIntro.
    rewrite fixpoint_semWp2_close_eq; cbn. done.
  Qed.

  Lemma semWp_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
                   (Q : Post Γ τ) (δ : CStore Γ) :
    semWp δ s (λ v δ, semWp δ (k v) Q) ⊢
    semWp δ (stm_bind s k) Q.
  Proof.
    iLöb as "IH" forall (s δ).
    iIntros "Hwp". rewrite (fixpoint_semWp_eq _ (stm_bind s k) _); cbn.
    iIntros (? ? ? ?) "Hres". iIntros (? ? ? ? Hs).
    destruct (smallinvstep Hs).
    - rewrite semWp_val. iFrame "Hres".
      iMod "Hwp". now close_later "Hclose".
    - iFrame "Hres". iIntros "!> !> !>".
      rewrite (fixpoint_semWp_eq _ _ Q); cbn.
      iIntros (? ? ? ?) "Hres".
      iIntros (? ? ? ? Hfail).
      discriminate_step.
    - rewrite fixpoint_semWp_eq; cbn.
      stm_val_fail_stuck.
      iSpecialize ("Hwp" with "Hres []"); first eauto.
      iMod "Hwp". iIntros "!> !>". iMod "Hwp" as "($ & Hwp)".
      iModIntro. now iApply ("IH" with "Hwp").
  Qed.

  Lemma semWp_step {Γ τ} (δ1 δ2 : CStore Γ) (s1 s2 : Stm Γ τ) (Q : Post Γ τ) :
    ∀ γ γ1 μ μ1 γ2 μ2,
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
      reg_inv _ γ γ1 ∗ mem_inv _ μ μ1 -∗
      semWp δ1 s1 Q -∗
      |={∅}▷=> (reg_inv _ γ γ2 ∗ mem_inv _ μ μ2) ∗ semWp δ2 s2 Q.
  Proof.
    iIntros (? ? ? ? ? ? Hs1) "Hres Hwp".
    rewrite fixpoint_semWp_eq; cbn.
    stm_val_fail_stuck.
    iSpecialize ("Hwp" with "Hres []"); first eauto.
    done.
  Qed.

  Lemma semWp2_close_right {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
                           (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    semWp2_close δ1 δ2 s1 s2 Q
    ⊢ |={⊤,∅}=> semWp δ2 s2 (λ v2 δ2', semWp2_close δ1 δ2' s1 (stm_val τ v2) Q).
  Proof.
    iLöb as "IH" forall (δ2 s2).
    iIntros "H".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    rewrite fixpoint_semWp_eq; cbn.
    case_match eqn:Es2v.
    - destruct s2; try discriminate; inversion Es2v; subst.
      now iMod "Hclose".
    - iIntros (? ? ? ?) "Hres".
      iIntros (? ? ? ? Hs2).
      iSpecialize ("IH" $! δ' s' with "[H Hres]").
      admit. (* resources (-.-') *)
  Admitted.

  Lemma semWp_bind_semWp2_close {Γ1 Γ2 τ σ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 σ)
    (k : Val σ -> Stm Γ2 τ) (Q : Post2 Γ1 Γ2 τ) (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    semWp δ2 s2 (λ v δ2', semWp2_close δ1 δ2' s1 (k v) Q) ⊢
    semWp2_close δ1 δ2 s1 (stm_bind s2 k) Q.
  Proof.
    iLöb as "IH" forall (δ1 s1).
    iIntros "H".
    rewrite fixpoint_semWp2_close_eq; cbn.
    case_match eqn:Es1v.
    - iApply semWp_bind.
      iApply (semWp_mono with "H").
      iIntros (v2 δ2').
      destruct s1; try discriminate.
      inversion Es1v; subst.
      rewrite semWp2_close_val_l.
      iIntros "H".
      iApply (semWp_mono with "H").
      iIntros (? ?) "$".
    - iIntros (? ? ? ?) "Hres".
      iIntros (? ? ? ? Hs1).
      iPoseProof (semWp_mono with "H [Hres]") as "H".
      { iIntros (v δ) "H".
        rewrite fixpoint_semWp2_close_eq; cbn.
        stm_val_fail_stuck.
        iSpecialize ("H" with "Hres []"); first eauto.
        iApply "H". }
      iIntros "!> !>".
      iSpecialize ("IH" with "[H]").
      { admit. (* Y u like dis? (-.-') RESOURCES lost... *) }
      iFrame "IH".
  Admitted.

  Lemma semWp2_close_bind {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
    (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
    semWp2_close δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2_close δ12 δ22 (k1 v1) (k2 v2) Q) ⊢
      semWp2_close δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
  Proof.
    iLöb as "IH" forall (δ1 s1).
    iIntros "Hwp".
    rewrite (fixpoint_semWp2_close_eq _ _ (stm_bind s1 k1) _ _); cbn.
    iIntros (? ? ? ?) "Hres".
    iIntros (? ? ? ? Hl).
    destruct (smallinvstep Hl).
    - rewrite fixpoint_semWp2_close_eq; cbn.
      iPoseProof (semWp_bind_semWp2_close with "Hwp") as "Hwp".
      iFrame "Hres Hwp". done.
    - iFrame "Hres". iIntros "!> !> !>".
      rewrite (fixpoint_semWp2_close_eq _ _ (fail s)%exp (stm_bind _ _) _); cbn.
      iIntros; discriminate_step.
    - rewrite fixpoint_semWp2_close_eq; cbn.
      stm_val_fail_stuck.
      iSpecialize ("Hwp" with "Hres []"); first eauto.
      iMod "Hwp". iIntros "!> !>". iMod "Hwp" as "($ & Hwp)". iModIntro.
      iApply ("IH" with "Hwp").
  Admitted.

  Lemma semWp2_bind {Γ τ σ} (s1 s2 : Stm Γ σ) (k1 k2 : Val σ → Stm Γ τ)
    (Q : Post2 Γ Γ τ) (δ1 δ2 : CStore Γ) :
    semWp2 δ1 δ2 s1 s2 (fun v1 δ12 v2 δ22 => semWp2 δ12 δ22 (k1 v1) (k2 v2) Q) ⊢
      semWp2 δ1 δ2 (stm_bind s1 k1) (stm_bind s2 k2) Q.
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
    iPoseProof (semWp2_frame_l with "[HR Htriple]") as "Hwp".
    { iSplitL "HR". iExact "HR". iExact "Htriple". }
    iApply (semWp2_mono with "Hwp").
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
    iApply semWp2_val.
    iSpecialize ("PQ" with "P").
    iModIntro; by iFrame.
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
