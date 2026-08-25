(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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

From Katamaran Require Import
     Bitvector
     Environment
     Iris.Base
     RiscvPmp.Machine
     trace.
From stdpp Require Import namespaces.
Module ns := stdpp.namespaces.
From iris Require Import
  algebra.auth
     base_logic.lib.gen_heap
     base_logic.lib.invariants
     proofmode.tactics.

Set Implicit Arguments.

Import RiscvPmpProgram.
Import bv.notations.

Module Type RiscvPmpIrisBaseCommon <: IrisPrelims RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.
  Include IrisPrelims RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.

  (* Defines the memory ghost state. *)
  Definition MemVal : Set := Byte.

  Definition initMemMap μ := (list_to_map (map (fun a => (a , memory_ram μ a)) liveAddrs) : gmap Addr MemVal).

  Inductive WritePendingState :=
  | NothingPending : WritePendingState
  | Written : Event -> WritePendingState.

  Definition writePendingΣ := #[GFunctor (authR (optionUR (excl.exclR (leibnizO WritePendingState))))].

  Class writePending_preG Σ := WritePending_preG {
                                   writePending_pre_inG :: inG Σ (auth.authR (optionUR (excl.exclR (leibnizO WritePendingState))));
                                 }.

  Class writePendingG Σ := WritePendingG {
                               writePending_inG :: inG Σ (auth.authR (optionUR (excl.exclR (leibnizO WritePendingState))));
                               writePendingG_gname : gname
                             }.

  #[export] Instance writePendingΣ_preG `{writePendingG Σ} : writePending_preG Σ.
  Proof. constructor. typeclasses eauto. Defined.

  #[export] Instance subG_writePendingPreΣ {Σ}:
    subG writePendingΣ Σ →
    writePending_preG Σ.
  Proof. solve_inG. Qed.

  Definition nothingPending_auth `{writePendingG Σ} : iProp Σ :=
    own writePendingG_gname (● (Some (excl.Excl NothingPending) : optionUR (excl.exclR (leibnizO WritePendingState)))).
  Definition nothingPending `{writePendingG Σ} : iProp Σ :=
    own writePendingG_gname (◯ (Some (excl.Excl NothingPending) : optionUR (excl.exclR (leibnizO WritePendingState)))).
  Definition written_auth `{writePendingG Σ} e : iProp Σ :=
    own writePendingG_gname (● (Some (excl.Excl (Written e)) : optionUR (excl.exclR (leibnizO WritePendingState)))).
  Definition written `{writePendingG Σ} e : iProp Σ :=
    own writePendingG_gname (◯ (Some (excl.Excl (Written e)) : optionUR (excl.exclR (leibnizO WritePendingState)))).

  Lemma writePending_alloc `{!writePending_preG Σ} :
    ⊢ |==> ∃ tG : writePendingG Σ,
        nothingPending_auth ∗ nothingPending.
  Proof.
    iMod (own_alloc (● (Some (excl.Excl NothingPending): optionUR (excl.exclR (leibnizO WritePendingState))) ⋅ ◯ (Some (excl.Excl NothingPending) : optionUR (excl.exclR (leibnizO WritePendingState))))) as (γ) "[? ?]".
    { apply auth_both_valid_2; done. }
    iModIntro. iExists (WritePendingG _ γ). now iFrame.
  Qed.

  Lemma nothingPending_written `{writePendingG Σ} e :
    nothingPending_auth ∗ nothingPending ==∗
    written_auth e ∗ written e.
  Proof.
    rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply @option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  Lemma written_nothingPending `{writePendingG Σ} e :
    written_auth e ∗ written e ==∗
    nothingPending_auth ∗ nothingPending.
  Proof.
    rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply @option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* NOTE: no resource present for current `State`, since we do not wish to reason about it for now *)
  Class mcMemGS Σ :=
    McMemGS {
        (* ghost variable for tracking state of heap *)
        mc_ghGS :: gen_heapGS Addr MemVal Σ;
        (* tracking traces *)
        mc_gtGS :: traceG Trace Σ;
        mc_wpGS :: writePendingG Σ
      }.

  Class mcMemGS2 Σ :=
    McMemGS2 {
        (* two copies of the unary ghost variables *)
        mc_ghGS2_left : mcMemGS Σ
      ; mc_ghGS2_right : mcMemGS Σ
      }.

  Class mcMemPreGS Σ := {
      mc_ghPreGS :: gen_heapGpreS Addr MemVal Σ;
      mc_gtPreGS :: trace_preG Trace Σ;
      mc_wpPreGS :: writePending_preG Σ;
      }.
  #[export] Existing Instance mc_ghPreGS.
  #[export] Existing Instance mc_gtPreGS.
  #[export] Existing Instance mc_wpPreGS.

  Definition memGpreS : gFunctors -> Set := mcMemPreGS.
  Definition memΣ : gFunctors := #[gen_heapΣ Addr MemVal ; tracePreΣ Trace; writePendingΣ ].

  Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ.
  Proof. intros. solve_inG. Defined.

  Section SharedBinaryInvariant.
    Context {Σ : gFunctors} {mG : mcMemGS2 Σ}.

    (* TODO: add the above filter for mmio_pred. Important lemma, any valid
             mmio_pred without the filter, implies one with the filter. The
             non-filtered one is stronger, since it also says something about
             secret MMIO events (unary version). *)
    Definition femto_inv_mmio_ns : ns.namespace := (ns.ndot ns.nroot "inv_mmio").
    Definition interp_inv_mmio `{invGS Σ} (width : nat) : iProp Σ :=
      inv femto_inv_mmio_ns (∃ t1 t2,
            @tr_frag _ _ (@mc_gtGS _ mc_ghGS2_left) t1 ∗
              @tr_frag _ _ (@mc_gtGS _ mc_ghGS2_right) t2 ∗
              ∃ t, ( let mgl := mc_ghGS2_left in
                     ((⌜filter_adv_observable t1 = t⌝ ∗ nothingPending_auth)
                      ∨ ∃ e1, ⌜filter_adv_observable t1 = e1 :: t⌝ ∗ written_auth e1)
                   ∗ let mgr := mc_ghGS2_right in
                    ((⌜filter_adv_observable t2 = t⌝ ∗ nothingPending_auth)
                    ∨ ∃ e2, ⌜filter_adv_observable t2 = e2 :: t⌝ ∗ written_auth e2)
             )
        ).
  End SharedBinaryInvariant.


End RiscvPmpIrisBaseCommon.

Module Type LeftOrRight.

  Parameter leftOrRight : bool.
End LeftOrRight.

Module LeftOrRightLeft <: LeftOrRight.
  Definition leftOrRight := true.
End LeftOrRightLeft.

Module LeftOrRightRight <: LeftOrRight.
  Definition leftOrRight := false.
End LeftOrRightRight.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module Type RiscvPmpIrisBase (Import leftOrRight : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  <: IrisBase RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)

  Section RiscvPmpIrisParams.
    Definition memGS : gFunctors -> Set := mcMemGS2.

    Definition leftOrRightInstance `{mcMemGS2 Σ} : mcMemGS Σ :=
      if leftOrRight then mc_ghGS2_left else mc_ghGS2_right.
    #[export] Existing Instance leftOrRightInstance.

    Definition mem_inv : forall {Σ}, mcMemGS2 Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp memmap
                     ∗ ⌜ map_Forall (fun a v => memory_ram μ a = v) memmap ⌝
                     ∗ tr_auth (memory_trace μ)
        )%I.

  End RiscvPmpIrisParams.

  Include IrisResources RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  Include IrisWeakestPre RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  Include IrisTotalWeakestPre RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  Include IrisTotalPartialWeakestPre RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics RVPCOM.

  Import iris.program_logic.weakestpre.

  Definition WP_loop `{sg : sailGS Σ} : iProp Σ :=
    semWP env.nil (FunDef loop) (fun _ _ => True%I).
  Definition TWP_loop `{sg : sailGS Σ} : iProp Σ :=
    semTWP env.nil (FunDef loop) (fun _ _ => True%I).

  (* Useful instance for some of the Iris proofs *)
  #[export] Instance state_inhabited : Inhabited State.
  Proof. repeat constructor.
          - intros ty reg. apply val_inhabited.
          - intro. apply bv.bv_inhabited.
          - apply state_inhabited.
  Qed.

End RiscvPmpIrisBase.
