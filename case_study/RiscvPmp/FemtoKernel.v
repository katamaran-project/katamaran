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

From Coq Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Bitvector
     Notations
     Specification
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Import BlockVerificationDerived2.

  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Open Scope hex_Z_scope.

    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
(*     MAX := 2^30; *)
(* (*     assembly source: *) *)
(* CODE:   UTYPE #HERE ra RISCV_AUIPC *) (* 0 *)
(*         ADDI RA, RA, (ADV - #PREVHERE) *) (* 4 *)
(*         CSR pmpaddr0 ra r0 CSRRW; *) (* 8 *)
(*         UTYPE MAX ra RISCV_LUI; *) (* 12 *)
(*         CSR pmpaddr1 ra r0 CSRRW; *) (* 16 *)
(*         UTYPE (pure_pmpcfg_ent_to_bits { L := false; A := OFF; X := false; W := false; R := false }) ra RISCV_LUI; *) (* 20 *)
(*         CSR pmp0cfg ra r0 CSRRW; *) (* 24 *)
(*         UTYPE (pure_pmpcfg_ent_to_bits { L := false; A := TOR; X := true; W := true; R := true }) ra RISCV_LUI; *) (* 28 *)
(*         CSR pmp1cfg ra r0 CSRRW; *) (* 32 *)
(*         UTYPE #HERE ra RISCV_AUIPC *) (* 36 *)
(*         ADDI RA, RA, (ADV - #PREVHERE) *) (* 40 *)
(*         CSR epc ra r0 CSRRW; *) (* 44 *)
(*         UTYPE #HERE ra RISCV_AUIPC *) (* 48 *)
(*         ADDI RA, RA, (IH - #PREVHERE) *) (* 52 *)
(*         CSR Tvec ra r0 CSRRW; *) (* 56 *)
(*         UTYPE (pure_mstatus_to_bits { MPP := User }) ra RISCV_LUI; *) (* 60 *)
(*         CSR Mstatus ra r0 CSRRW; *) (* 64 *)
(*         MRET *) (* 68 *)

(*     IH: UTYPE 0 ra RISCV_AUIPC *) (* 72 *)
(*         load (#HERE - 4 - DATA) ra ra; *) (* 76 *)
(*         MRET *) (* 80 *)
(* DATA:   42 *) (* 84 *)
(* ADV:    ... (anything) *) (* 88 *)
(*     } *)

    Definition pure_privilege_to_bits : Privilege -> Xlenbits :=
      fun p => match p with | Machine => 3%Z | User => 0%Z end.

    Definition pure_mstatus_to_bits : Mstatus -> Xlenbits :=
      fun '(MkMstatus mpp) => Z.shiftl (pure_privilege_to_bits mpp) 11.

    Definition pure_pmpAddrMatchType_to_bits : PmpAddrMatchType -> Z:=
      fun mt => match mt with
                | OFF => 0%Z
                | TOR => 1%Z
                end.

    Definition pure_pmpcfg_ent_to_bits : Pmpcfg_ent -> Xlenbits :=
      fun ent =>
        match ent with
        | MkPmpcfg_ent L A X W R =>
            let l := Z.shiftl (if L then 1 else 0) 7 in
            let a := Z.shiftl (pure_pmpAddrMatchType_to_bits A) 3 in
            let x := Z.shiftl (if X then 1 else 0) 2 in
            let w := Z.shiftl (if W then 1 else 0) 1 in
            let r := Z.shiftl (if R then 1 else 0) 0 in
            Z.lor l (Z.lor a (Z.lor x (Z.lor w r)))
        end%Z.

    Definition femto_address_max := 2^30.
    Definition femto_pmpcfg_ent0 : Pmpcfg_ent := MkPmpcfg_ent false OFF false false false.
    Definition femto_pmpcfg_ent0_bits : Val ty_xlenbits := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent0.
    Definition femto_pmpcfg_ent1 : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
    Definition femto_pmpcfg_ent1_bits : Val ty_xlenbits := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent1.
    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, 88); (femto_pmpcfg_ent1, femto_address_max)]%list.

    Definition femto_mstatus := pure_mstatus_to_bits (MkMstatus User ).

    Example femtokernel_init : list AST :=
      [
        UTYPE 0 ra RISCV_AUIPC
      ; ITYPE 88 ra ra RISCV_ADDI
      ; CSR MPMPADDR0 ra zero CSRRW
      ; UTYPE femto_address_max ra RISCV_LUI
      ; CSR MPMPADDR1 ra zero CSRRW
      ; UTYPE femto_pmpcfg_ent0_bits ra RISCV_LUI
      ; CSR MPMP0CFG ra zero CSRRW
      ; UTYPE femto_pmpcfg_ent1_bits ra RISCV_LUI
      ; CSR MPMP1CFG ra zero CSRRW
      ; UTYPE 0 ra RISCV_AUIPC
      ; ITYPE 52 ra ra RISCV_ADDI
      ; CSR MEpc ra zero CSRRW
      ; UTYPE 0 ra RISCV_AUIPC
      ; ITYPE 24 ra ra RISCV_ADDI
      ; CSR MTvec ra zero CSRRW
      ; UTYPE femto_mstatus ra RISCV_LUI
      ; CSR MStatus ra zero CSRRW
      ; MRET
      ].

    Example femtokernel_handler : list AST :=
      [ UTYPE 0 ra RISCV_AUIPC
      ; LOAD 12 ra ra
      ; MRET
      ].

    Import asn.notations.
    Local Notation "a '↦[' n ']' xs" := (asn.chunk (chunk_user ptstomem [a; n; xs])) (at level 79).
    Local Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
    Local Notation "x + y" := (term_binop bop.plus x y) : exp_scope.

    Let Σ__femtoinit : LCtx := [].
    Let W__femtoinit : World := MkWorld Σ__femtoinit [].

    Example femtokernel_default_pmpcfg : Pmpcfg_ent :=
      {| L := false; A := OFF; X := false; W := false; R := false |}.

    (* DOMI: TODO: replace the pointsto chunk for 84 ↦ 42 with a corresponding invariant *)
    Example femtokernel_init_pre : Assertion {| wctx := [] ▻ ("a"::ty_xlenbits) ; wco := nil |} :=
        (term_var "a" = term_val ty_word 0) ∗
      (∃ "v", mstatus ↦ term_var "v") ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "v", x1 ↦ term_var "v") ∗
      (∃ "v", x2 ↦ term_var "v") ∗
      (∃ "v", x3 ↦ term_var "v") ∗
      (∃ "v", x4 ↦ term_var "v") ∗
      (∃ "v", x5 ↦ term_var "v") ∗
      (∃ "v", x6 ↦ term_var "v") ∗
      (∃ "v", x7 ↦ term_var "v") ∗
      (pmp0cfg ↦ term_val ty_pmpcfg_ent femtokernel_default_pmpcfg)  ∗
      (pmp1cfg ↦ term_val ty_pmpcfg_ent femtokernel_default_pmpcfg)  ∗
      (∃ "v", pmpaddr0 ↦ term_var "v") ∗
      (∃ "v", pmpaddr1 ↦ term_var "v") ∗
      (term_var "a" + (term_val ty_xlenbits 84) ↦ₘ term_val ty_xlenbits 42)%exp.

    Example femtokernel_init_post : Assertion  {| wctx := [] ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits) ; wco := nil |} :=
      (
        asn.formula (formula_eq (term_var "an") (term_var "a" + term_val ty_xlenbits 88)) ∗
          (∃ "v", mstatus ↦ term_var "v") ∗
          (mtvec ↦ (term_var "a" + term_val ty_xlenbits 72)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mepc ↦ term_var "v") ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          (∃ "v", x1 ↦ term_var "v") ∗
          (∃ "v", x2 ↦ term_var "v") ∗
          (∃ "v", x3 ↦ term_var "v") ∗
          (∃ "v", x4 ↦ term_var "v") ∗
          (∃ "v", x5 ↦ term_var "v") ∗
          (∃ "v", x6 ↦ term_var "v") ∗
          (∃ "v", x7 ↦ term_var "v") ∗
          (pmp0cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent0) ∗
          (pmp1cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent1) ∗
          (pmpaddr0 ↦ term_var "a" + term_val ty_xlenbits 88) ∗
          (pmpaddr1 ↦ term_val ty_xlenbits femto_address_max) ∗
          (term_var "a" + (term_val ty_xlenbits 84) ↦ₘ term_val ty_xlenbits 42)
      )%exp.

    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__femtoinit : 𝕊 Σ__femtoinit :=
      simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post).
      (* let vc1 := VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Print vc__femtoinit. *)

    Lemma sat__femtoinit : safeE vc__femtoinit.
    Proof.
      constructor. vm_compute. intros. auto.
    Qed.

    (* Even admitting this goes OOM :-) *)
    (* Lemma sat__femtoinit2 : SymProp.safe vc__femtoinit env.nil. *)
    (* Admitted. *)
    (* (* Proof. *) *)
    (* (*   destruct sat__femtoinit as [se]. *) *)
    (* (*   exact (proj1 (Erasure.erase_safe vc__femtoinit env.nil) se). *) *)
    (* (* Qed. *) *)


    Let Σ__femtohandler : LCtx := ["epc"::ty_exc_code; "mpp"::ty_privilege].
    Let W__femtohandler : World := MkWorld Σ__femtohandler [].

    Example femtokernel_handler_pre : Assertion {| wctx := ["epc"::ty_exc_code; "a" :: ty_xlenbits]; wco := nil |} :=
        (term_var "a" = term_val ty_word 72) ∗
      (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
      (mtvec ↦ term_val ty_word 72) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (mepc ↦ term_var "epc") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "v", x1 ↦ term_var "v") ∗
      (∃ "v", x2 ↦ term_var "v") ∗
      (∃ "v", x3 ↦ term_var "v") ∗
      (∃ "v", x4 ↦ term_var "v") ∗
      (∃ "v", x5 ↦ term_var "v") ∗
      (∃ "v", x6 ↦ term_var "v") ∗
      (∃ "v", x7 ↦ term_var "v") ∗
      (pmp0cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent0) ∗
      (pmp1cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent1) ∗
      (pmpaddr0 ↦ term_var "a" + term_val ty_xlenbits 16) ∗
      (pmpaddr1 ↦ term_val ty_xlenbits femto_address_max) ∗
      (term_var "a" + (term_val ty_xlenbits 12) ↦ₘ term_val ty_xlenbits 42)%exp.

    Example femtokernel_handler_post : Assertion {| wctx := ["epc"::ty_exc_code; "a" :: ty_xlenbits; "an"::ty_xlenbits]; wco := nil |} :=
      (
          (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
          (mtvec ↦ term_val ty_word 72) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (mepc ↦ term_var "epc") ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          (∃ "v", x1 ↦ term_var "v") ∗
          (∃ "v", x2 ↦ term_var "v") ∗
          (∃ "v", x3 ↦ term_var "v") ∗
          (∃ "v", x4 ↦ term_var "v") ∗
          (∃ "v", x5 ↦ term_var "v") ∗
          (∃ "v", x6 ↦ term_var "v") ∗
          (∃ "v", x7 ↦ term_var "v") ∗
          (pmp0cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent0) ∗
          (pmp1cfg ↦ term_val (ty.record rpmpcfg_ent) femto_pmpcfg_ent1) ∗
          (pmpaddr0 ↦ term_var "a" + term_val ty_xlenbits 16) ∗
          (pmpaddr1 ↦ term_val ty_xlenbits femto_address_max) ∗
          (term_var "a" + (term_val ty_xlenbits 12) ↦ₘ term_val ty_xlenbits 42) ∗
          asn.formula (formula_eq (term_var "an") (term_var "epc"))
      )%exp.

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)
    Definition vc__femtohandler : 𝕊 [] :=
      simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post).

      (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Print vc__femtohandler. *)

    Lemma sat__femtohandler : safeE vc__femtohandler.
    Proof.
      constructor. vm_compute. intros. auto.
    Qed.

  End FemtoKernel.

  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived.
  Import RiscvPmpIrisInstanceWithContracts.

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.

  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifShalExecutor.
  Import RiscvPmpIrisInstanceWithContracts.

  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived2.
  Import Shallow.Executor.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.
  (* Import Model.RiscvPmpModel. *)
  (* Import Model.RiscvPmpModel2. *)
  (* Import RiscvPmpIrisParams. *)
  (* Import RiscvPmpIrisPredicates. *)
  (* Import RiscvPmpIrisPrelims. *)
  (* Import RiscvPmpIrisResources. *)
  Import BlockVerificationDerived2Sound.
  (* Import RiscvPmpModelBlockVerif.PLOG. *)
  (* Import Sound. *)
  Import BlockVerificationDerived2Sem.

  Definition advAddrs := seqZ 88 (maxAddr - 88 + 1).

  (* Lemma liveAddr_split : liveAddrs = seqZ minAddr 88 ++ advAddrs. *)
  (* Proof. *)
  (*   unfold liveAddrs. *)
  (*   change 88%Z with (minAddr + 88)%Z at 2. *)
  (*   replace (maxAddr - minAddr + 1)%Z with (88 + (maxAddr - 88 - minAddr + 1))%Z by lia. *)
  (*   eapply seqZ_app; unfold minAddr, maxAddr; lia. *)
  (* Qed. *)

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (exists p2, Pmp_access x ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access.
    destruct (decide_pmp_access x ents p1 p2); [left|right]; intuition.
  Defined.

  Lemma liveAddr_filter_advAddr : filter
                 (λ x : Val ty_exc_code,
                    (∃ p : Val ty_access_type, Pmp_access x femto_pmpentries User p)%type)
                 liveAddrs = advAddrs.
  Proof.
    now compute.
  Qed.

  Lemma big_sepL_filter `{BiAffine PROP} {A : Type} {l : list A}
      {φ : A → Prop} (dec : ∀ x, Decision (φ x)) (Φ : A -> PROP) :
    ([∗ list] x ∈ filter φ l, Φ x) ⊣⊢
    ([∗ list] x ∈ l, ⌜φ x⌝ -∗ Φ x).
  Proof. induction l.
         - now cbn.
         - cbn.
           destruct (decide (φ a)) as [Hφ|Hnφ].
           + rewrite big_opL_cons.
             rewrite <-IHl.
             iSplit; iIntros "[Ha Hl]"; iFrame; try done.
             now iApply ("Ha" $! Hφ).
           + rewrite <-IHl.
             iSplit.
             * iIntros "Hl"; iFrame; iIntros "%Hφ"; intuition.
             * iIntros "[Ha Hl]"; now iFrame.
  Qed.

  Lemma memAdv_pmpPolicy `{sailGS Σ} :
    (ptstoSthL advAddrs ⊢
      interp_pmp_addr_access liveAddrs femto_pmpentries User)%I.
  Proof.
    iIntros "Hadv".
    unfold interp_pmp_addr_access.
    rewrite <-(big_sepL_filter).
    unfold ptstoSthL.
    now rewrite <- liveAddr_filter_advAddr.
  Qed.

  Definition femto_inv_ns : ns.namespace := (ns.ndot ns.nroot "femto_inv_ns").

  Import iris.base_logic.lib.invariants.
  (* This lemma transforms the postcondition of femtokernel_init into the precondition of the universal contract, so that we can use the UC to verify the invocation of untrusted code.
   *)

  (* DOMI: for simplicity, we're currently treating the femtokernel invariant on the private state not as a shared invariant but as a piece of private state to be framed off during every invocation of the adversary.  This is fine since for now we're assuming no concurrency... *)
  Definition femto_inv_fortytwo `{sailGS Σ} : iProp Σ :=
        (interp_ptsto 84 42).

  Local Notation "a '↦' t" := (reg_pointsTo a t) (at level 79).
  (* Local Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 79). *)

  Definition femto_handler_pre `{sailGS Σ} epc : iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
      (mtvec ↦ 72) ∗
      (∃ v, mcause ↦ v) ∗
      (mepc ↦ epc) ∗
      cur_privilege ↦ Machine ∗
      (∃ v, x1 ↦ v) ∗
      (∃ v, x2 ↦ v) ∗
      (∃ v, x3 ↦ v) ∗
      (∃ v, x4 ↦ v) ∗
      (∃ v, x5 ↦ v) ∗
      (∃ v, x6 ↦ v) ∗
      (∃ v, x7 ↦ v) ∗
      interp_pmp_entries femto_pmpentries ∗
      femto_inv_fortytwo ∗
      pc ↦ 72 ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs 72 femtokernel_handler.

    Example femto_handler_post `{sailGS Σ} epc : iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
        (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (mepc ↦ epc) ∗
        cur_privilege ↦ User ∗
        (∃ v, x1 ↦ v) ∗
        (∃ v, x2 ↦ v) ∗
        (∃ v, x3 ↦ v) ∗
        (∃ v, x4 ↦ v) ∗
        (∃ v, x5 ↦ v) ∗
        (∃ v, x6 ↦ v) ∗
        (∃ v, x7 ↦ v) ∗
        interp_pmp_entries femto_pmpentries ∗
        femto_inv_fortytwo ∗
        pc ↦ epc ∗
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs 72 femtokernel_handler.

  Definition femto_handler_contract `{sailGS Σ} : iProp Σ :=
    ∀ epc,
        femto_handler_pre epc -∗
          (femto_handler_post epc -∗ WP_loop) -∗
          WP_loop.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre.

  Import env.notations.
  Lemma femto_handler_verified : forall `{sailGS Σ}, ⊢ femto_handler_contract.
  Proof.
    iIntros (Σ sG epc) "Hpre Hk".
    iApply (sound_VC__addr $! 72 with "[Hpre] [Hk]").
    - exact sat__femtohandler.
    Unshelve.
    exact (env.snoc env.nil (_::ty_exc_code) epc).
    - iDestruct "Hpre" as "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & (Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1) & Hfortytwo & Hpc & Hnpc & Hhandler)".
      cbn.
      unfold femto_inv_fortytwo.
      now iFrame.
    - iIntros (an) "(Hpc & Hnpc & Hhandler & (Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & (Hpmp0cfg & Hpmp1cfg & Hpmpaddr0 & Hpmpaddr1 & Hfortytwo & %eq & _)))".
      cbn.
      iApply "Hk".
      unfold femto_handler_post.
      cbn in eq; destruct eq.
      now iFrame.
  Qed.

  Transparent femtokernel_handler_pre.

  Lemma femtokernel_hander_safe `{sailGS Σ} {mepcv}:
    ⊢ mstatus ↦ {| MPP := User |} ∗
       (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (mepc ↦ mepcv) ∗
        cur_privilege ↦ Machine ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
        femto_inv_fortytwo ∗
        (pc ↦ 72) ∗
        interp_pmp_addr_access liveAddrs femto_pmpentries User ∗
        (∃ v, nextpc ↦ v) ∗
        (* ptsto_instrs 0 femtokernel_init ∗  (domi: init code not actually needed anymore, can be dropped) *)
        ptsto_instrs 72 femtokernel_handler
        -∗
        WP_loop.
  Proof.
    unfold interp_gprs; cbn -[interp_pmp_entries].
    rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
    iIntros "".
    iLöb as "Hind".
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmpentries & Hfortytwo & Hpc & Hmem & Hnextpc & Hinstrs)".

    iApply (femto_handler_verified $! mepcv with "[Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hgprs Hpmpentries Hfortytwo Hpc Hinstrs Hnextpc] [Hmem]").
    - unfold femto_handler_pre; iFrame.
      iDestruct "Hgprs" as "(? & ? & ? & ? & ? & ? & ? & ? & _)".
      now iFrame.
    - iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hpmpentries & Hfortytwo & Hpc & Hnextpc & Hinstrs)".
      iApply LoopVerification.valid_semTriple_loop.
      iSplitL "Hmem Hnextpc Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hpmpentries Hpc".
      + unfold LoopVerification.Execution.
        iFrame.
        iSplitR "Hpc".
        * unfold interp_gprs; cbn -[interp_pmp_entries].
          rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
          now iFrame.
        * now iExists _.
      + iSplitL "".
        iModIntro.
        unfold LoopVerification.CSRMod.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.

        iSplitR "".
        iModIntro.
        unfold LoopVerification.Trap.
        iIntros "(Hmem & Hgprs & Hpmpentries & Hmcause & Hcurpriv & Hnextpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
        iApply "Hind".
        unfold interp_gprs; cbn -[interp_pmp_entries].
        rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
        iFrame.
        now iExists _.

        iModIntro.
        unfold LoopVerification.Recover.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.
  Qed.

  Lemma femtokernel_manualStep2 `{sailGS Σ} :
    ⊢ (∃ mpp, mstatus ↦ {| MPP := mpp |}) ∗
       (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
         (interp_ptsto 84 42) ∗
        (pc ↦ 88) ∗
        (∃ v, nextpc ↦ v) ∗
        (* ptsto_instrs 0 femtokernel_init ∗  (domi: init code not actually needed anymore, can be dropped) *)
        ptsto_instrs 72 femtokernel_handler ∗
        ptstoSthL advAddrs
        ={⊤}=∗
        ∃ mpp mepcv, LoopVerification.loop_pre User User 72 72 femto_pmpentries femto_pmpentries mpp mepcv.
  Proof.
    iIntros "([%mpp Hmst] & Hmtvec & [%mcause Hmcause] & [%mepc Hmepc] & Hcurpriv & Hgprs & Hpmpcfg & Hfortytwo & Hpc & Hnpc & Hhandler & Hmemadv)".
    iExists mpp, mepc.
    unfold LoopVerification.loop_pre, LoopVerification.Execution, interp_gprs.
    rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
    iFrame.

  (*   iMod (inv_alloc femto_inv_ns ⊤ (interp_ptsto (mG := sailGS_memGS) 84 42) with "Hfortytwo") as "#Hinv". *)
  (*   change (inv femto_inv_ns (84 ↦ₘ 42)) with femto_inv_fortytwo. *)
    iModIntro.

    iSplitL "Hmcause Hpc Hmemadv".
    iSplitL "Hmemadv".
    now iApply memAdv_pmpPolicy.
    iSplitL "Hmcause".
    now iExists mcause.
    iExists 88; iFrame.

    iSplitL "".
    iModIntro.
    unfold LoopVerification.CSRMod.
    iIntros "(_ & _ & _ & %eq & _)".
    inversion eq.

    iSplitL.
    unfold LoopVerification.Trap.
    iModIntro.
    iIntros "(Hmem & Hgprs & Hpmpents & Hmcause & Hcurpriv & Hnpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
    iApply femtokernel_hander_safe.
    iFrame.
    now iExists _.

    iModIntro.
    unfold LoopVerification.Recover.
    iIntros "(_ & _ & _ & %eq & _)".
    inversion eq.
  Qed.

  Definition femto_init_pre `{sailGS Σ} : iProp Σ :=
      ((∃ v, mstatus ↦ v) ∗
      (∃ v, mtvec ↦ v) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ v, mepc ↦ v) ∗
      cur_privilege ↦ Machine ∗
      (∃ v, x1 ↦ v) ∗
      (∃ v, x2 ↦ v) ∗
      (∃ v, x3 ↦ v) ∗
      (∃ v, x4 ↦ v) ∗
      (∃ v, x5 ↦ v) ∗
      (∃ v, x6 ↦ v) ∗
      (∃ v, x7 ↦ v) ∗
      pmp0cfg ↦ femtokernel_default_pmpcfg ∗
      pmp1cfg ↦ femtokernel_default_pmpcfg ∗
      (∃ v, pmpaddr0 ↦ v) ∗
      (∃ v, pmpaddr1 ↦ v) ∗
      femto_inv_fortytwo) ∗
      pc ↦ 0 ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs 0 femtokernel_init.

    Example femto_init_post `{sailGS Σ} : iProp Σ :=
      ((∃ v, mstatus ↦ v) ∗
        (mtvec ↦ 72) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        (∃ v, x1 ↦ v) ∗
        (∃ v, x2 ↦ v) ∗
        (∃ v, x3 ↦ v) ∗
        (∃ v, x4 ↦ v) ∗
        (∃ v, x5 ↦ v) ∗
        (∃ v, x6 ↦ v) ∗
        (∃ v, x7 ↦ v) ∗
        pmp0cfg ↦ femto_pmpcfg_ent0 ∗
        pmp1cfg ↦ femto_pmpcfg_ent1 ∗
        (pmpaddr0 ↦ 88) ∗
        (pmpaddr1 ↦ femto_address_max) ∗
        femto_inv_fortytwo) ∗
        pc ↦ 88 ∗
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs 0 femtokernel_init.

  Definition femto_init_contract `{sailGS Σ} : iProp Σ :=
    femto_init_pre -∗
      (femto_init_post -∗ WP_loop) -∗
          WP_loop.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.

  Lemma femto_init_verified : forall `{sailGS Σ}, ⊢ femto_init_contract.
  Proof.
    iIntros (Σ sG) "Hpre Hk".
    iApply (sound_VC__addr $! 0 with "[Hpre] [Hk]").
    - exact sat__femtoinit.
    Unshelve.
    exact env.nil.
    - unfold femto_init_pre.
      unfold asn.interpret; cbn -[ptsto_instrs].
      iDestruct "Hpre" as "[Hpre1 Hpre2]".
      now iFrame.
    - iIntros (an) "Hpost".
      iApply "Hk".
      unfold femto_init_post.
      cbn -[ptsto_instrs].
      iDestruct "Hpost" as "(Hpc & Hnpc & Hhandler & ([%eq _] & Hrest))".
      subst.
      iFrame.
  Qed.

  (* see above *)
  Transparent femtokernel_init_pre.

  Lemma femtokernel_init_safe `{sailGS Σ} :
    ⊢ (∃ v, mstatus ↦ v) ∗
      (∃ v, mtvec ↦ v) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ v, mepc ↦ v) ∗
      cur_privilege ↦ Machine ∗
      interp_gprs ∗
      reg_pointsTo pmp0cfg femtokernel_default_pmpcfg ∗
      (∃ v, reg_pointsTo pmpaddr0 v) ∗
      reg_pointsTo pmp1cfg femtokernel_default_pmpcfg ∗
      (∃ v, reg_pointsTo pmpaddr1 v) ∗
      (pc ↦ 0) ∗
      interp_ptsto 84 42 ∗
      ptstoSthL advAddrs ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs 0 femtokernel_init ∗
      ptsto_instrs 72 femtokernel_handler
      -∗
      WP_loop.
  Proof.
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hpc & Hfortytwo & Hadv & Hnextpc & Hinit & Hhandler)".
    unfold interp_gprs.
    rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
    iDestruct "Hgprs" as "(_ & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & _)".
    iApply (femto_init_verified with "[Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1 Hpc Hinit Hfortytwo Hnextpc]").
    - unfold femto_init_pre.
      iFrame.
    - iIntros "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hfortytwo) & Hpc & Hnextpc & Hinit)".
      iAssert (interp_pmp_entries femto_pmpentries) with "[Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1]" as "Hpmpents".
      { unfold interp_pmp_entries; cbn; iFrame. }
      iAssert interp_gprs with "[Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7]" as "Hgprs".
      { unfold interp_gprs.
        rewrite ?big_opS_union ?big_opS_singleton ?big_opS_empty; try set_solver.
        iFrame.
        now iExists 0.
      }
      iApply fupd_wp.
      iMod (femtokernel_manualStep2 with "[Hmstatus Hmtvec Hmcause Hgprs Hcurpriv Hpmpents Hfortytwo Hpc Hnextpc Hhandler Hadv Hmepc ]") as "[%mpp [%mepcv Hlooppre]]".
      { iFrame.
        iDestruct "Hmstatus" as "[%mst Hmstatus]".
        destruct mst as [mpp].
        now iExists mpp.
      }
      iApply (LoopVerification.valid_semTriple_loop $! User User 72 72 femto_pmpentries femto_pmpentries mpp mepcv).
      iModIntro.
      iExact "Hlooppre".
  Qed.

  Print Assumptions femtokernel_init_safe.
