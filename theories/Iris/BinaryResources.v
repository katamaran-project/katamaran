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
  (Import B    : Base)
  (Import IB   : IrisParameters B).

  Parameter memGS2 : gFunctors -> Set.
  Existing Class memGS2.
  Parameter memGS2_memGS_left : forall `{memGS2 Σ}, memGS Σ.
  Parameter memGS2_memGS_right : forall `{memGS2 Σ}, memGS Σ.
  Parameter mem_inv2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.
  Parameter mem_inv2_mem_inv : forall `{mG : memGS2 Σ} (μ1 μ2 : Memory),
      mem_inv2 μ1 μ2 ⊣⊢ @mem_inv _ memGS2_memGS_left μ1 ∗ @mem_inv _ memGS2_memGS_right μ2.
End IrisParameters2.

Module Type IrisResources2
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B)
  (Import IP2  : IrisParameters2 B IP)
  (Import IR   : IrisResources B PROG SEM IPre IP).

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

  Definition reg_pointsTo2 `{sailRegGS2 Σ} {τ} : 𝑹𝑬𝑮 τ → RelVal τ → iProp Σ :=
    fun reg rv =>
    (@reg_pointsTo _ sailRegGS2_sailRegGS_left _ reg (ty.projLeft rv) ∗ @reg_pointsTo _ sailRegGS2_sailRegGS_right _ reg (ty.projRight rv))%I.

  Definition sailGS2_sailGS_left `{sG2 : sailGS2 Σ} : sailGS Σ :=
    {| sailGS_invGS     := sailGS2_invGS;
       sailGS_sailRegGS := sailRegGS2_sailRegGS_left;
       sailGS_memGS     := memGS2_memGS_left;
    |}.

  Definition sailGS2_sailGS_right `{sG2 : sailGS2 Σ} : sailGS Σ :=
    {| sailGS_invGS     := sailGS2_invGS;
       sailGS_sailRegGS := sailRegGS2_sailRegGS_right;
       sailGS_memGS     := memGS2_memGS_right;
    |}.

  #[export] Program Instance sailGS2_irisGS2 `{sailGS2 Σ} {Γ1 Γ2 τ} : irisGS2 (microsail_lang Γ1 τ) (microsail_lang Γ2 τ) Σ :=
    {|
      iris_invGS2 := sailGS2_invGS;
      state_interp2 σ1 σ2 κ := (regs_inv2 σ1.1 σ2.1 ∗ mem_inv2_sail σ1.2 σ2.2)%I;
      num_laters_per_step2 := fun _ => 0
    |}.

  Lemma sailGS2_sailGS_left_memGS_eq `{sG2 : sailGS2 Σ} :
    @sailGS_memGS _ (@sailGS2_sailGS_left _ sG2) = @memGS2_memGS_left _ (@sailGS2_memGS _ sG2).
  Proof. auto. Qed.

  Lemma sailGS2_sailGS_right_memGS_eq `{sG2 : sailGS2 Σ} :
    @sailGS_memGS _ (@sailGS2_sailGS_right _ sG2) = @memGS2_memGS_right _ (@sailGS2_memGS _ sG2).
  Proof. auto. Qed.

  Lemma reg_valid2 `{srGS: sailRegGS2 Σ} regstore1 regstore2 {τ} (r : 𝑹𝑬𝑮 τ) (rv : RelVal τ) :
    ⊢ (regs_inv2 regstore1 regstore2 -∗ reg_pointsTo2 r rv -∗ ⌜ read_register regstore1 r = ty.projLeft rv ⌝ ∗ ⌜ read_register regstore2 r = ty.projRight rv⌝)%I.
  Proof.
    unfold regs_inv2.
    iIntros "(regs1_inv & regs2_inv)".
    iIntros "(Hreg1 & Hreg2)".
    iSplit.
    - iApply (reg_valid with "regs1_inv Hreg1").
    - iApply (reg_valid with "regs2_inv Hreg2").
  Qed.

  Definition SomeRelVal : Type := sigT RelVal.


  Lemma reg_update2 `{srGS: sailRegGS2 Σ} regstore1 regstore2 {τ} r (rv1 rv2 : RelVal τ) :
    regs_inv2 regstore1 regstore2 -∗ reg_pointsTo2 r rv1 ==∗ regs_inv2 (write_register regstore1 r (ty.projLeft rv2)) (write_register regstore2 r (ty.projRight rv2)) ∗ reg_pointsTo2 r rv2.
    Proof.
      unfold regs_inv2.
      iIntros "(regs1_inv & regs2_inv)".
      iIntros "(Hreg1 & Hreg2)".
      unfold reg_pointsTo2.
      iAssert ((|==> regs_inv (write_register regstore1 r (ty.projLeft rv2)) ∗ r ↦ᵣ ty.projLeft rv2)%I) with "[regs1_inv Hreg1]" as "H1".
      { iApply (reg_update with "regs1_inv Hreg1"). }
      iAssert ((|==> regs_inv (write_register regstore2 r (ty.projRight rv2)) ∗ r ↦ᵣ ty.projRight rv2)%I) with "[regs2_inv Hreg2]" as "H2".
      { iApply (reg_update with "regs2_inv Hreg2"). }
      iMod "H1". iMod "H2".
      iModIntro.
      iDestruct "H1" as "(Hregs1_inv & Hreg1)".
      iDestruct "H2" as "(Hregs2_inv & Hreg2)".
      iFrame.
    Qed.

End IrisResources2.

Module Type IrisBase2 (B : Base) (PROG : Program B) (SEM : Semantics B PROG) :=
  IrisBase B PROG SEM <+ IrisParameters2 B <+ IrisResources2 B PROG SEM.

