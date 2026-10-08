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

  Lemma writePending_agree `{writePendingG Σ} (s s' : WritePendingState) :
    own writePendingG_gname (● (Some (excl.Excl s) : optionUR (excl.exclR (leibnizO WritePendingState)))) -∗
    own writePendingG_gname (◯ (Some (excl.Excl s') : optionUR (excl.exclR (leibnizO WritePendingState)))) -∗
    ⌜s = s'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi _]%auth_both_valid_discrete.
    rewrite excl.Excl_included in Hi. apply leibniz_equiv in Hi. by subst.
  Qed.

  Lemma written_auth_nothingPending `{writePendingG Σ} e :
    written_auth e -∗ nothingPending -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (writePending_agree with "H1 H2") as %?.
  Qed.

  Lemma nothingPending_auth_written `{writePendingG Σ} e :
    nothingPending_auth -∗ written e -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (writePending_agree with "H1 H2") as %?.
  Qed.

  Lemma written_auth_written `{writePendingG Σ} e e' :
    written_auth e -∗ written e' -∗ ⌜e = e'⌝.
  Proof.
    iIntros "H1 H2".
    by iDestruct (writePending_agree with "H1 H2") as %[= ->].
  Qed.

  #[export] Instance nothingPending_auth_Timeless `{writePendingG Σ} :
    Timeless nothingPending_auth.
  Proof. unfold nothingPending_auth. apply _. Qed.

  #[export] Instance written_auth_Timeless `{writePendingG Σ} e :
    Timeless (written_auth e).
  Proof. unfold written_auth. apply _. Qed.

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

    (* The state of a single execution w.r.t. the adversary-observable trace
       `t` that both executions agree on. Either the observable part of this
       execution's trace is exactly `t`, or this execution is ahead by exactly
       one (observable) event `e`, which is recorded in the `written` ghost
       state until both executions are resynchronized. *)
    Definition side_inv (mGs : mcMemGS Σ) (t : Trace) : iProp Σ :=
      ∃ ts, @tr_frag _ _ (@mc_gtGS _ mGs) ts ∗
              ((⌜filter_adv_observable ts = t⌝ ∗ @nothingPending_auth _ (@mc_wpGS _ mGs))
               ∨ ∃ e, ⌜filter_adv_observable ts = e :: t⌝ ∗ @written_auth _ (@mc_wpGS _ mGs) e).

    #[export] Instance side_inv_Timeless mGs t : Timeless (side_inv mGs t).
    Proof. unfold side_inv. apply _. Qed.

    Definition interp_inv_mmio `{invGS Σ} (width : nat) : iProp Σ :=
      inv femto_inv_mmio_ns (∃ t, side_inv mc_ghGS2_left t ∗ side_inv mc_ghGS2_right t).

    (* If both executions have performed the same observable write, they can
       be resynchronized: the common observable trace is extended with that
       write and both executions return to the `nothingPending` state. *)
    Lemma written_nothingPending2 `{invGS Σ} (width : nat) (e : Event) E :
      ↑femto_inv_mmio_ns ⊆ E →
      interp_inv_mmio width -∗
      @written _ (@mc_wpGS _ mc_ghGS2_left) e -∗
      @written _ (@mc_wpGS _ mc_ghGS2_right) e ={E}=∗
      @nothingPending _ (@mc_wpGS _ mc_ghGS2_left) ∗
      @nothingPending _ (@mc_wpGS _ mc_ghGS2_right).
    Proof.
      iIntros (HE) "#Hinv Hl Hr".
      iInv "Hinv" as ">(%t & (%t1 & Hf1 & H1) & (%t2 & Hf2 & H2))" "Hclose".
      iDestruct "H1" as "[[_ Ha1] | (%e1 & %Ht1 & Ha1)]".
      { iDestruct (nothingPending_auth_written with "Ha1 Hl") as "[]". }
      iDestruct "H2" as "[[_ Ha2] | (%e2 & %Ht2 & Ha2)]".
      { iDestruct (nothingPending_auth_written with "Ha2 Hr") as "[]". }
      iDestruct (written_auth_written with "Ha1 Hl") as %->.
      iDestruct (written_auth_written with "Ha2 Hr") as %->.
      iMod (written_nothingPending with "[$Ha1 $Hl]") as "[Ha1 $]".
      iMod (written_nothingPending with "[$Ha2 $Hr]") as "[Ha2 $]".
      iApply "Hclose". iExists (e :: t).
      iSplitL "Hf1 Ha1"; iExists _; iFrame; by iLeft; iFrame.
    Qed.
  End SharedBinaryInvariant.

  Section WithMemory.
    Context {Σ : gFunctors} {mG : mcMemGS Σ}.

    (* TODO: change back to words instead of bytes... might be an easier first version
             and most likely still convenient in the future *)
    Definition interp_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      pointsto addr (DfracOwn 1) b ∗ ⌜¬ withinMMIO addr 1⌝.
    Definition ptstoSth : Addr -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Addr -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.

    Definition interp_ptstomem' {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ :=
      [∗ list] offset ∈ seq 0 width,
        interp_ptsto (addr + bv.of_nat offset) (get_byte offset bytes).
    Fixpoint interp_ptstomem {width : nat} (addr : Addr) : bv (width * byte) -> iProp Σ :=
      match width with
      | O   => fun _ => True
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView byte (w * byte) bytes in
            interp_ptsto addr byte ∗ interp_ptstomem (bv.one + addr) bytes
      end%I.

    (* TODO: introduce constant for nr of word bytes (replace 4) *)
    Definition interp_ptsto_instr (addr : Addr) (instr : AST) : iProp Σ :=
      (∃ v, @interp_ptstomem 4 addr v ∗ ⌜ pure_decode v = inr instr ⌝)%I.

    Fixpoint ptsto_instrs (a : Val ty_xlenbits) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs (bv.add a bv_instrsize) insts)%I
      | nil => True%I
      end.
    (* Arguments ptsto_instrs {Σ H} a%_Z_scope instrs%_list_scope : simpl never. *)

    Lemma ptsto_instrs_app {a : Val ty_xlenbits} {instrs1 instrs2 : list AST} :
      ptsto_instrs a (instrs1 ++ instrs2)
        ⊣⊢ ptsto_instrs a instrs1 ∗ ptsto_instrs (bv.add a (bv.of_nat (length instrs1 * bytes_per_instr))) instrs2.
    Proof.
      iRevert (a).
      iInduction instrs1 as [|i1 instrs1]; iIntros (a); cbn; iSplit.
      - rewrite <- bv.add_of_nat_0_r. now iIntros "$".
      - rewrite <- bv.add_of_nat_0_r. now iIntros "(_ & $)".
      - iIntros "($ & H)".
        iDestruct ("IHinstrs1" with "H") as "($ & H)".
        rewrite <- bv.add_assoc.
        now rewrite bv.of_nat_add.
      - iIntros "(($ & Hinstrs1) & Hinstrs2)".
        iSpecialize ("IHinstrs1" with "[$Hinstrs1 Hinstrs2]").
        { rewrite <- bv.add_assoc. now rewrite bv.of_nat_add. }
        done.
    Qed.

  End WithMemory.

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

    (* The ghost state of the other execution. *)
    Definition otherInstance `{mcMemGS2 Σ} : mcMemGS Σ :=
      if leftOrRight then mc_ghGS2_right else mc_ghGS2_left.

    (* View the body of the shared invariant from the perspective of this execution. *)
    Lemma inv_mmio_body_own_other `{mcMemGS2 Σ} t :
      side_inv mc_ghGS2_left t ∗ side_inv mc_ghGS2_right t ⊣⊢
      side_inv leftOrRightInstance t ∗ side_inv otherInstance t.
    Proof.
      unfold leftOrRightInstance, otherInstance.
      destruct leftOrRight; [done | apply bi.sep_comm].
    Qed.

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
