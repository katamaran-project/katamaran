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
     SmallStep.Step
     RiscvPmpBoundedInts.BlockVer.Spec
     RiscvPmpBoundedInts.BlockVer.Verifier
     RiscvPmpBoundedInts.IrisModel
     RiscvPmpBoundedInts.IrisInstance
     RiscvPmpBoundedInts.Machine
     RiscvPmpBoundedInts.Sig.
From Katamaran Require
     RiscvPmpBoundedInts.Contracts
     RiscvPmpBoundedInts.LoopVerification
     RiscvPmpBoundedInts.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
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

Module inv := invariants.

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
(*         ADDI RA, RA, (IH - #PREVHERE) *) (* 40 *)
(*         CSR Tvec ra r0 CSRRW; *) (* 44 *)
(*         UTYPE #HERE ra RISCV_AUIPC *) (* 48 *)
(*         ADDI RA, RA, (ADV - #PREVHERE) *) (* 52 *)
(*         CSR epc ra r0 CSRRW; *) (* 56 *)
(*         UTYPE (pure_mstatus_to_bits { MPP := User }) ra RISCV_LUI; *) (* 60 *)
(*         CSR Mstatus ra r0 CSRRW; *) (* 64 *)
(*         MRET *) (* 68 *)

(*     IH: UTYPE 0 ra RISCV_AUIPC *) (* 72 *)
(*         load (#HERE - 4 - DATA) ra ra; *) (* 76 *)
(*         MRET *) (* 80 *)
(* DATA:   42 *) (* 84 *)
(* ADV:    ... (anything) *) (* 88 *)
(*     } *)

    Definition pure_privilege_to_bits {n} : Privilege -> bv n :=
      fun p => match p with | Machine => bv.of_N 3 | User => bv.zero end.

    Definition pure_mstatus_to_bits : Mstatus -> bv 20 :=
      fun '(MkMstatus mpp) => bv.app (@bv.zero 11) (pure_privilege_to_bits mpp).

    Definition pure_pmpAddrMatchType_to_bits : PmpAddrMatchType -> bv 4 :=
      fun mt => match mt with
                | OFF => bv.zero
                | TOR => bv.one _
                end.

    Definition pure_pmpcfg_ent_to_bits : Pmpcfg_ent -> Val (ty.bvec 20) :=
      fun ent =>
        match ent with
        | MkPmpcfg_ent L A X W R =>
            let l : bv 1 := bv.of_bool L in
            let a : bv 4 := pure_pmpAddrMatchType_to_bits A in
            let x : bv 1 := bv.of_bool X in
            let w : bv 1 := bv.of_bool W in
            let r : bv 1 := bv.of_bool R in
            bv.app r (bv.app w (bv.app x (bv.app a (bv.app l bv.zero))))
        end%Z.

    Definition femto_address_max : N := 2^19 - 1.
    Definition femto_pmpcfg_ent0 : Pmpcfg_ent := MkPmpcfg_ent false OFF false false false.
    Definition femto_pmpcfg_ent0_bits : Val (ty.bvec 20) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent0.
    Definition femto_pmpcfg_ent1 : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
    Definition femto_pmpcfg_ent1_bits : Val (ty.bvec 20) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent1.
    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N 88); (femto_pmpcfg_ent1, bv.of_N femto_address_max)]%list.

    Definition femto_mstatus := pure_mstatus_to_bits (MkMstatus User).

    Example femtokernel_init : list AST :=
      [
        UTYPE bv.zero ra RISCV_AUIPC
      ; ITYPE (bv.of_N 88) ra ra RISCV_ADDI
      ; CSR MPMPADDR0 ra zero CSRRW
      ; UTYPE (bv.of_N femto_address_max) ra RISCV_LUI
      ; CSR MPMPADDR1 ra zero CSRRW
      ; UTYPE femto_pmpcfg_ent0_bits ra RISCV_LUI
      ; CSR MPMP0CFG ra zero CSRRW
      ; UTYPE femto_pmpcfg_ent1_bits ra RISCV_LUI
      ; CSR MPMP1CFG ra zero CSRRW
      ; UTYPE bv.zero ra RISCV_AUIPC
      ; ITYPE (bv.of_N 36) ra ra RISCV_ADDI
      ; CSR MTvec ra zero CSRRW
      ; UTYPE bv.zero ra RISCV_AUIPC
      ; ITYPE (bv.of_N 40) ra ra RISCV_ADDI
      ; CSR MEpc ra zero CSRRW
      ; UTYPE femto_mstatus ra RISCV_LUI
      ; CSR MStatus ra zero CSRRW
      ; MRET
      ].

    Example femtokernel_handler : list AST :=
      [
        UTYPE bv.zero ra RISCV_AUIPC
      ; LOAD (bv.of_N 12) ra ra
      ; MRET
      ].

    Import asn.notations.
    (* Local Notation "a '↦[' n ']' xs" := (asn.chunk (chunk_user ptstomem [a; n; xs])) (at level 79). *)
    Local Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
    Local Notation "a '↦ᵣ' t" := (asn.chunk (chunk_user (ptstomem_readonly bytes_per_word) [a; t])) (at level 70).
    Local Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).
    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
    Local Notation asn_pmp_all_entries_unlocked l := (asn.formula (formula_user pmp_all_entries_unlocked [l])).

    Let Σ__femtoinit : LCtx := [].
    Let W__femtoinit : World := MkWorld Σ__femtoinit []%ctx.

    Example femtokernel_default_pmpcfg : Pmpcfg_ent :=
      {| L := false; A := OFF; X := false; W := false; R := false |}.

    (* DOMI: TODO: replace the pointsto chunk for 84 ↦ 42 with a corresponding invariant *)
    Example femtokernel_init_pre : Assertion {| wctx := [] ▻ ("a"::ty_xlenbits) ; wco := []%ctx |} :=
        (term_var "a" = term_val ty_word bv.zero) ∗
      (∃ "v", mstatus ↦ term_var "v") ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      ((∃ "v", x1 ↦ term_var "v") ∗
      (∃ "v", x2 ↦ term_var "v") ∗
      (∃ "v", x3 ↦ term_var "v") ∗
      (∃ "v", x4 ↦ term_var "v") ∗
      (∃ "v", x5 ↦ term_var "v") ∗
      (∃ "v", x6 ↦ term_var "v") ∗
      (∃ "v", x7 ↦ term_var "v")) ∗
      (∃ "a0", ∃ "a1",
          asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent femtokernel_default_pmpcfg ,ₜ term_var "a0");
                                      (term_val ty_pmpcfg_ent femtokernel_default_pmpcfg ,ₜ term_var "a1")])) ∗
      (term_var "a" + (term_val ty_xlenbits (bv.of_N 84)) ↦ᵣ term_val ty_xlenbits (bv.of_N 42))%exp.

    Example femtokernel_init_post : Assertion  {| wctx := [] ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits) ; wco := []%ctx |} :=
      (
        asn.formula (formula_relop bop.eq (term_var "an") (term_var "a" + term_val ty_xlenbits (bv.of_N 88))) ∗
          (∃ "v", mstatus ↦ term_var "v") ∗
          (mtvec ↦ (term_var "a" + term_val ty_xlenbits (bv.of_N 72))) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mepc ↦ term_var "v") ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          ((∃ "v", x1 ↦ term_var "v") ∗
          (∃ "v", x2 ↦ term_var "v") ∗
          (∃ "v", x3 ↦ term_var "v") ∗
          (∃ "v", x4 ↦ term_var "v") ∗
          (∃ "v", x5 ↦ term_var "v") ∗
          (∃ "v", x6 ↦ term_var "v") ∗
          (∃ "v", x7 ↦ term_var "v")) ∗
          (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 88));
                                       (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))])) ∗
          (asn_pmp_all_entries_unlocked (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 88));
                                       (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))])) ∗
          (term_var "a" + (term_val ty_xlenbits (bv.of_N 84)) ↦ᵣ term_val ty_xlenbits (bv.of_N 42))
      )%exp.

    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__femtoinit : 𝕊 Σ__femtoinit :=
      postprocess (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post).
      (* let vc1 := VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* (* Set Printing Depth 200. *) *)
    (* Eval vm_compute in vc__femtoinit. *)

    Lemma sat__femtoinit : safeE vc__femtoinit.
    Proof.
      now vm_compute.
    Qed.

    Let Σ__femtohandler : LCtx := ["epc"::ty_exc_code; "mpp"::ty_privilege].
    Let W__femtohandler : World := MkWorld Σ__femtohandler []%ctx.

    Example femtokernel_handler_pre : Assertion {| wctx := ["a" :: ty_xlenbits]; wco := []%ctx |} :=
        (term_var "a" = term_val ty_word (bv.of_N 72)) ∗
      (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
      (mtvec ↦ term_val ty_word (bv.of_N 72)) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "epc", mepc ↦ term_var "epc") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      ((∃ "v", x1 ↦ term_var "v") ∗
      (∃ "v", x2 ↦ term_var "v") ∗
      (∃ "v", x3 ↦ term_var "v") ∗
      (∃ "v", x4 ↦ term_var "v") ∗
      (∃ "v", x5 ↦ term_var "v") ∗
      (∃ "v", x6 ↦ term_var "v") ∗
      (∃ "v", x7 ↦ term_var "v")) ∗
      (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 16));
                                   (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))])) ∗
      (asn_pmp_all_entries_unlocked (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 16));
                                                (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))])) ∗
      (asn_pmp_addr_access (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 16));
                                   (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))]) (term_val ty_privilege User)) ∗
      (term_var "a" + (term_val ty_xlenbits (bv.of_N 12)) ↦ᵣ term_val ty_xlenbits (bv.of_N 42))%exp.

    Example femtokernel_handler_post : Assertion {| wctx := ["a" :: ty_xlenbits; "an"::ty_xlenbits]; wco := []%ctx |} :=
      (
          (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
          (mtvec ↦ term_val ty_word (bv.of_N 72)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "epc", (mepc ↦ term_var "epc" ∗
                     asn.formula
                         (formula_relop bop.eq (term_var "an")
                                     (term_var "epc")))) ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          ((∃ "v", x1 ↦ term_var "v") ∗
          (∃ "v", x2 ↦ term_var "v") ∗
          (∃ "v", x3 ↦ term_var "v") ∗
          (∃ "v", x4 ↦ term_var "v") ∗
          (∃ "v", x5 ↦ term_var "v") ∗
          (∃ "v", x6 ↦ term_var "v") ∗
          (∃ "v", x7 ↦ term_var "v")) ∗
          (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 16));
                                       (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))])) ∗
          (asn_pmp_all_entries_unlocked (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 16));
                                                    (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))])) ∗
          (asn_pmp_addr_access (term_list [(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ term_var "a" + term_val ty_xlenbits (bv.of_N 16));
                                       (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N femto_address_max))]) (term_val ty_privilege User)) ∗
          (term_var "a" + (term_val ty_xlenbits (bv.of_N 12)) ↦ᵣ term_val ty_xlenbits (bv.of_N 42)) ∗
        ⊤
      )%exp.

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)
    Definition vc__femtohandler : 𝕊 [] :=
      postprocess (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post).

      (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Compute vc__femtohandler. *)
    (* Print vc__femtohandler. *)

    Lemma sat__femtohandler : safeE vc__femtohandler.
    Proof.
      now vm_compute.
    Qed.

  End FemtoKernel.

  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
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

  Definition advAddrs : list (bv xlenbits) := bv.seqBv (bv.of_N 88) (lenAddr - 88).

  (* Lemma liveAddr_split : liveAddrs = seqZ minAddr 88 ++ advAddrs. *)
  (* Proof. *)
  (*   unfold liveAddrs. *)
  (*   change 88%Z with (minAddr + 88)%Z at 2. *)
  (*   replace (maxAddr - minAddr + 1)%Z with (88 + (maxAddr - 88 - minAddr + 1))%Z by lia. *)
  (*   eapply seqZ_app; unfold minAddr, maxAddr; lia. *)
  (* Qed. *)

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (exists p2, Pmp_access x (bv.of_nat 1) ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access.
    destruct (decide_pmp_access x (bv.of_nat 1) ents p1 p2); [left|right]; easy.
  Defined.

  Lemma liveAddr_filter_advAddr : filter
                 (λ x : Val ty_word ,
                    (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p)%type)
                 liveAddrs = advAddrs.
  Proof. now compute. Qed.

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

  (* Definition ptsto_readonly `{sailGS Σ} addr v : iProp Σ := *)
  (*       inv.inv femto_inv_ns (interp_ptsto addr v). *)
  Definition femto_inv_fortytwo `{sailGS Σ} : iProp Σ := @interp_ptstomem_readonly _ _ _ xlenbytes (bv.of_N 84) (bv.of_N 42).

  Local Notation "a '↦' t" := (reg_pointsTo a t) (at level 79).
  (* Local Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 79). *)

  Definition femto_handler_pre `{sailGS Σ} : iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
      (mtvec ↦ (bv.of_N 72)) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ epc, mepc ↦ epc) ∗
      cur_privilege ↦ Machine ∗
      interp_gprs ∗
      interp_pmp_entries femto_pmpentries ∗
      ⌜Pmp_all_entries_unlocked femto_pmpentries⌝ ∗
      interp_pmp_addr_access liveAddrs femto_pmpentries User ∗
      femto_inv_fortytwo ∗
      pc ↦ (bv.of_N 72) ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs (bv.of_N 72) femtokernel_handler.

    Example femto_handler_post `{sailGS Σ} : iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
        (mtvec ↦ (bv.of_N 72)) ∗
        (∃ v, mcause ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
        ⌜Pmp_all_entries_unlocked femto_pmpentries⌝ ∗
        interp_pmp_addr_access liveAddrs femto_pmpentries User ∗
        femto_inv_fortytwo ∗
        (∃ epc, mepc ↦ epc ∗
                pc ↦ epc) ∗
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs (bv.of_N 72) femtokernel_handler.

  Definition femto_handler_contract `{sailGS Σ} : iProp Σ :=
    femto_handler_pre -∗
        (femto_handler_post -∗ WP_loop) -∗
        WP_loop.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre.

  Import env.notations.
  Lemma femto_handler_verified : forall `{sailGS Σ}, ⊢ femto_handler_contract.
  Proof.
    iIntros (Σ sG) "Hpre Hk".
    iApply (sound_VC__addr $! (bv.of_N 72) with "[Hpre] [Hk]").
    - exact sat__femtohandler.
    Unshelve.
    exact [env].
    - cbv [femtokernel_handler_pre Logic.sep.lsep Logic.sep.lcar
           Logic.sep.land Logic.sep.lprop Logic.sep.lemp interpret_chunk
           Model.IProp Logic.sep.lex lptsreg PredicateDefIProp inst instprop_formula
           inst_term env.lookup ctx.view ctx.in_at ctx.in_valid inst_env
           env.map].
      cbn.
      iDestruct "Hpre" as "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp & Hfortytwo & Hpc & Hnpc & Hhandler)".
      rewrite Model.RiscvPmpModel2.gprs_equiv. cbn.
      now iFrame.
    - cbv [femtokernel_handler_pre Logic.sep.lsep Logic.sep.lcar
           Logic.sep.land Logic.sep.lprop Logic.sep.lemp interpret_chunk
           Model.IProp Logic.sep.lex lptsreg PredicateDefIProp inst instprop_formula
           inst_term env.lookup ctx.view ctx.in_at ctx.in_valid inst_env
           env.map femto_handler_post femtokernel_handler_post].
      cbn.
      iIntros (an) "(Hpc & Hnpc & Hhandler & Hmstatus & Hmtvec & Hmcause & [% (Hmepc & [%eq _])] & Hcurpriv & Hregs & Hpmp & [%Hcfg0L %Hcfg1L] & HaccM & Hfortytwo & _ & _)".
      cbn.
      iApply "Hk".
      cbn in eq; destruct eq.
      rewrite Model.RiscvPmpModel2.gprs_equiv.
      iFrame "Hmstatus Hmtvec Hmcause Hcurpriv Hregs Hpmp HaccM Hnpc Hhandler Hfortytwo".
      iSplitR; first done.
      iExists an; iFrame.
  Qed.

  Transparent femtokernel_handler_pre.
  Opaque interp_pmp_entries.

  Lemma femtokernel_hander_safe `{sailGS Σ} :
    ⊢ mstatus ↦ {| MPP := User |} ∗
       (mtvec ↦ (bv.of_N 72)) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ mepcv, mepc ↦ mepcv) ∗
        cur_privilege ↦ Machine ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
        ⌜Pmp_all_entries_unlocked femto_pmpentries⌝ ∗
        femto_inv_fortytwo ∗
        (pc ↦ (bv.of_N 72)) ∗
        interp_pmp_addr_access liveAddrs femto_pmpentries User ∗
        (∃ v, nextpc ↦ v) ∗
        (* ptsto_instrs 0 femtokernel_init ∗  (domi: init code not actually needed anymore, can be dropped) *)
        ptsto_instrs (bv.of_N 72) femtokernel_handler
        -∗
        WP_loop.
  Proof.
    cbn - [interp_pmp_entries]. iLöb as "Hind".
    iIntros "(Hmstatus & Hmtvec & Hmcause & [%mepcv Hmepc] & Hcurpriv & Hgprs & Hpmpentries & [%Hcfg0L %Hcfg1L] & #Hmem & Hpc & HaccU & Hnextpc & Hinstrs)".
    iApply (femto_handler_verified with "[-] []").
    - unfold femto_handler_pre, femto_pmpentries; iFrame.
      iSplitL "Hmepc"; first now iExists mepcv.
      iSplitR; first done.
      iExact "Hmem".
    - iIntros "(Hmstatus & Hmtvec & Hmcause & Hcurpriv & Hgprs & Hpmpentries & HpmpentriesL & HaccU & #Hmem' & [%epc (Hmepc & Hpc)] & Hnpc & Hhandler)".
      iApply LoopVerification.valid_semTriple_loop.
      iSplitL "Hmem Hmstatus Hmtvec Hmcause Hmepc Hpc Hcurpriv Hgprs Hpmpentries Hnpc HaccU".
      + unfold LoopVerification.Step_pre. cbn.
        iFrame "Hcurpriv Hmtvec Hpc Hnpc Hmcause Hmstatus Hpmpentries HaccU Hgprs".
        now iExists epc.
      + iSplitL "".
        { iModIntro.
          unfold LoopVerification.CSRMod.
          iIntros "(_ & _ & _ & %eq & _)".
          inversion eq.
        }

        iSplitR "".
        { iModIntro.
          unfold LoopVerification.Trap.
          iIntros "(HaccU & Hgprs & Hpmpentries & Hmcause & Hcurpriv & Hnextpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
          iApply "Hind".
          iFrame.
          iSplitR; first iExact "Hmem"; now iExists _.
        }

        { iModIntro.
          unfold LoopVerification.Recover.
          iIntros "(_ & _ & _ & %eq & _)".
          inversion eq.
        }
  Qed.

  Lemma femtokernel_manualStep2 `{sailGS Σ} :
    ⊢ (∃ mpp, mstatus ↦ {| MPP := mpp |}) ∗
       (mtvec ↦ (bv.of_N 72)) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
        ⌜Pmp_all_entries_unlocked femto_pmpentries⌝ ∗
         (@interp_ptstomem_readonly _ _ _ xlenbytes (bv.of_N 84) (bv.of_N 42)) ∗
        (pc ↦ (bv.of_N 88)) ∗
        (∃ v, nextpc ↦ v) ∗
        (* ptsto_instrs 0 femtokernel_init ∗  (domi: init code not actually needed anymore, can be dropped) *)
        ptsto_instrs (bv.of_N 72) femtokernel_handler ∗
        ptstoSthL advAddrs
        ={⊤}=∗
        ∃ mpp, LoopVerification.loop_pre User (bv.of_N 72) (bv.of_N 88) mpp femto_pmpentries.
  Proof.
    iIntros "([%mpp Hmst] & Hmtvec & [%mcause Hmcause] & [%mepc Hmepc] & Hcurpriv & Hgprs & Hpmpcfg & HpmpcfgL & Hfortytwo & Hpc & Hnpc & Hhandler & Hmemadv)".
    iExists mpp.
    unfold LoopVerification.loop_pre, LoopVerification.Step_pre, LoopVerification.Execution.
    iFrame.

    (* iMod (inv.inv_alloc femto_inv_ns ⊤ (interp_ptsto 84 42) with "Hfortytwo") as "#Hinv". *)
    (* change (inv.inv femto_inv_ns (interp_ptsto 84 42)) with femto_inv_fortytwo. *)
    iModIntro.

    iSplitL "Hmcause Hmepc Hmemadv".
    iSplitL "Hmcause".
    now iExists mcause.
    iSplitL "Hmepc".
    now iExists mepc.
    now iApply memAdv_pmpPolicy.

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
      interp_gprs ∗
      pmp0cfg ↦ femtokernel_default_pmpcfg ∗
      pmp1cfg ↦ femtokernel_default_pmpcfg ∗
      (∃ v, pmpaddr0 ↦ v) ∗
      (∃ v, pmpaddr1 ↦ v) ∗
      interp_ptstomem_readonly (width := xlenbytes) (bv.of_N 84) (bv.of_N 42)) ∗
      pc ↦ bv.zero ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs bv.zero femtokernel_init.

    Example femto_init_post `{sailGS Σ} : iProp Σ :=
      ((∃ v, mstatus ↦ v) ∗
        (mtvec ↦ (bv.of_N 72)) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        pmp0cfg ↦ femto_pmpcfg_ent0 ∗
        pmp1cfg ↦ femto_pmpcfg_ent1 ∗
        (pmpaddr0 ↦ (bv.of_N 88)) ∗
        (pmpaddr1 ↦ (bv.of_N femto_address_max)) ∗
        interp_ptstomem_readonly (width := xlenbytes) (bv.of_N 84) (bv.of_N 42)) ∗
        pc ↦ (bv.of_N 88) ∗
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs bv.zero femtokernel_init.

  Definition femto_init_contract `{sailGS Σ} : iProp Σ :=
    femto_init_pre -∗
      (femto_init_post -∗ WP_loop) -∗
          WP_loop.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.
  Transparent interp_pmp_entries.

  Lemma femto_init_verified : forall `{sailGS Σ}, ⊢ femto_init_contract.
  Proof.
    iIntros (Σ sG) "Hpre Hk".
    iApply (sound_VC__addr sat__femtoinit [env] $! bv.zero with "[Hpre] [Hk]").
    - unfold femto_init_pre. cbn -[ptsto_instrs].
      iDestruct "Hpre" as "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmp1cfg & [%pmpaddr0 Hpmpaddr0] & [%pmpaddr1 Hpmpaddr1] & Hfortytwo) & Hpc & Hnpc & Hinit)".
      rewrite Model.RiscvPmpModel2.gprs_equiv.
      iFrame "Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hgprs Hpmp0cfg Hpmp1cfg Hfortytwo Hpc Hnpc Hinit".
      repeat (iSplitR; first done).
      cbn.
      iExists pmpaddr0, pmpaddr1.
      now iFrame.
    - iIntros (an) "Hpost".
      iApply "Hk".
      unfold femto_init_post.
      cbn -[ptsto_instrs].
      iDestruct "Hpost" as "(Hpc & Hnpc & Hhandler & ([%eq _] & Hrest))".
      iDestruct "Hrest" as "(H1 & H2 & H3 & H4 & H5 & Hrest)".
      subst. iFrame.
      rewrite Model.RiscvPmpModel2.gprs_equiv. cbn -[ptsto_instrs].
      iDestruct "Hrest" as "(Hgprs & (Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1) & %Hunlocked & Hfortytwo)".
      now iFrame.
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
      (pc ↦ bv.zero) ∗
      interp_ptstomem_readonly (width := xlenbytes) (bv.of_N 84) (bv.of_N 42) ∗
      ptstoSthL advAddrs ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs bv.zero femtokernel_init ∗
      ptsto_instrs (bv.of_N 72) femtokernel_handler
      -∗
      WP_loop.
  Proof.
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hpc & Hfortytwo & Hadv & Hnextpc & Hinit & Hhandler)".
    iApply (femto_init_verified with "[Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hgprs Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1 Hpc Hinit Hfortytwo Hnextpc]").
    - unfold femto_init_pre.
      iFrame.
    - iIntros "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hfortytwo) & Hpc & Hnextpc & Hinit)".
      iAssert (interp_pmp_entries femto_pmpentries) with "[Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1]" as "Hpmpents".
      { unfold interp_pmp_entries; cbn; iFrame. }
      iApply fupd_wp.
      iMod (femtokernel_manualStep2 with "[Hmstatus Hmtvec Hmcause Hgprs Hcurpriv Hpmpents Hfortytwo Hpc Hnextpc Hhandler Hadv Hmepc ]") as "[%mpp Hlooppre]".
      { iFrame.
        iDestruct "Hmstatus" as "[%mst Hmstatus]".
        destruct mst as [mpp].
        iSplitL.
        now iExists mpp.
        now iPureIntro.
      }
      now iApply LoopVerification.valid_semTriple_loop.
  Qed.

  (* byte order correct? *)
  Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
    exists v0 v1 v2 v3, map μ (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ pure_decode (bv.app v0 (bv.app v1 (bv.app v2 v3))) = inr instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
    match instrs with
    | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
    | nil => True
    end.

  Import RiscvPmpSemantics.
  Import SmallStepNotations.

  Import iris.bi.big_op.
  Import iris.algebra.big_op.

  Lemma liveAddrs_split : liveAddrs = bv.seqBv (bv.of_N 0) 72 ++ bv.seqBv (bv.of_N 72) 12 ++ bv.seqBv (bv.of_N 84) 4 ++ advAddrs.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma intro_ptsto_instrs `{sailGS Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * N.of_nat (length instrs) + bv.bin a < bv.exp2 xlenbits)%N ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seqBv a (4 * length instrs), interp_ptsto a' (μ a'))
      ⊢ ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - rewrite Nat2N.inj_succ in Hrep.
      fold (length instrs) in Hrep.
      replace (4 * length (instr :: instrs)) with (4 + 4 * length instrs) by (cbn; lia).
      rewrite ?bv.seqBv_succ; try (rewrite ?bv.add_assoc ?bv.bin_add_small; cbn -[N.mul] in *; Lia.lia).
      destruct Hmeminstrs as [(v1 & v2 & v3 & v4 & Heq & Hv) Hmeminstrs].
      iDestruct "Hmem" as "(Hmema & Hmema1 & Hmema2 & Hmema3 & Hmem)".
      iSplitL "Hmema Hmema1 Hmema2 Hmema3".
      + unfold interp_ptsto_instr.
        iExists (bv.app v1 (bv.app v2 (bv.app v3 v4))).
        iSplitL; last done.
        unfold interp_ptstomem.
        replace v4 with (bv.app v4 bv.nil) by now rewrite bv.app_nil_r.
        rewrite ?bv.appView_app.
        inversion Heq.
        replace (bv.of_Z (Z.of_nat 0 + bv.unsigned a)) with a by now rewrite bv.of_Z_unsigned.
        replace (@bv.of_Z word (Z.of_nat 1 + bv.unsigned a)) with (bv.add (bv.one _) a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
        replace (@bv.of_Z word (Z.of_nat 2 + bv.unsigned a)) with (bv.add (bv.one word) (bv.add (bv.one word) a)).
        replace (@bv.of_Z word (Z.of_nat 3 + bv.unsigned a)) with (bv.add (bv.one word) (bv.add (bv.one word) (bv.add (bv.one word) a))).
        now iFrame.
        rewrite ?bv.add_assoc.
        change (bv.add _ (bv.one word)) with (@bv.of_Z xlenbits 3).
        now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
        rewrite ?bv.add_assoc.
        now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply "IH".
        { iPureIntro.
          rewrite bv.bin_add_small;
          cbn -[N.mul] in *;
          now Lia.lia.
        }
        { now iPureIntro. }
        now rewrite ?bv.add_assoc.
  Qed.

  Lemma intro_ptstoSthL `{sailGS Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, interp_ptsto a' (μ a')) ⊢ ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists (μ a).
      + now iApply IHl.
  Qed.

  Lemma femtokernel_splitMemory `{sailGS Σ} {μ : Memory} :
    mem_has_instrs μ (bv.of_N 0) femtokernel_init ->
    mem_has_instrs μ (bv.of_N 72) femtokernel_handler ->
    μ (bv.of_N 84) = (bv.of_N 42) ->
    @mem_res _ sailGS_memGS μ ⊢ |={⊤}=>
      ptsto_instrs (bv.of_N 0) femtokernel_init ∗
      ptsto_instrs (bv.of_N 72) femtokernel_handler ∗
      interp_ptstomem_readonly (width := xlenbytes) (bv.of_N 84) (bv.of_N 42) ∗
      ptstoSthL advAddrs.
  Proof.
    iIntros (Hinit Hhandler Hft) "Hmem".
    unfold mem_res, initMemMap.
    rewrite liveAddrs_split.
    rewrite ?map_app ?list_to_map_app ?big_sepM_union.
    iDestruct "Hmem" as "(Hinit & Hhandler & Hfortytwo & Hadv)".
    iSplitL "Hinit".
    now iApply (intro_ptsto_instrs (μ := μ)).
    iSplitL "Hhandler".
    now iApply (intro_ptsto_instrs (μ := μ)).
    iSplitL "Hfortytwo".
    - (* rewrite Hft. *)
      admit.
      (* iMod (inv.inv_alloc femto_inv_ns ⊤ (interp_ptstomem (width := word) (bv.of_N 84) (bv.of_N 42)) with "Hfortytwo") as "Hinv". *)
      (* now iModIntro. *)
    - now iApply (intro_ptstoSthL μ).
  Admitted.

  Lemma interp_ptsto_valid `{sailGS Σ} {μ a v} :
    ⊢ mem_inv _ μ -∗ interp_ptsto a v -∗ ⌜μ a = v⌝.
  Proof.
    unfold interp_ptsto, mem_inv.
    iIntros "(%memmap & Hinv & %link) Hptsto".
    iDestruct (gen_heap.gen_heap_valid with "Hinv Hptsto") as "%x".
    iPureIntro.
    now apply (map_Forall_lookup_1 _ _ _ _ link).
  Qed.

  Lemma femtokernel_endToEnd {γ γ' : RegStore} {μ μ' : Memory}
        {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} :
    mem_has_instrs μ (bv.of_N 0) femtokernel_init ->
    mem_has_instrs μ (bv.of_N 72) femtokernel_handler ->
    μ (bv.of_N 84) = (bv.of_N 42) ->
    read_register γ cur_privilege = Machine ->
    read_register γ pmp0cfg = femtokernel_default_pmpcfg ->
    read_register γ pmp1cfg = femtokernel_default_pmpcfg ->
    read_register γ pc = (bv.of_N 0) ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    μ' (bv.of_N 84) = (bv.of_N 42).
  Proof.
    intros μinit μhandler μft γcurpriv γpmp0cfg γpmp1cfg γpc steps.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) (μ' (bv.of_N 84) = (bv.of_N 42)) steps _).
    iIntros (Σ' H).
    unfold own_regstore.
    cbn.
    iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hpmp0cfg & Hpmp1cfg & Hpmpaddr0 & Hpmpaddr1 & _)".
    rewrite γcurpriv γpmp0cfg γpmp1cfg γpc.
    iMod (femtokernel_splitMemory with "Hmem") as "(Hinit & Hhandler & #Hfortytwo & Hadv)";
      try assumption.
    iModIntro.
    iSplitR "".
    - destruct (env.view δ).
      iApply femtokernel_init_safe.
      iFrame "Hfortytwo Hpc Hcurpriv Hpmp0cfg Hpmp1cfg Hinit Hadv Hhandler".
      iSplitL "Hmstatus". { now iExists _. }
      iSplitL "Hmtvec". { now iExists _. }
      iSplitL "Hmcause". { now iExists _. }
      iSplitL "Hmepc". { now iExists _. }
      iSplitL "Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7".
      {rewrite Model.RiscvPmpModel2.gprs_equiv. cbn.
       iSplitL "Hx1". { now iExists _. }
       iSplitL "Hx2". { now iExists _. }
       iSplitL "Hx3". { now iExists _. }
       iSplitL "Hx4". { now iExists _. }
       iSplitL "Hx5". { now iExists _. }
       iSplitL "Hx6". { now iExists _. }
       now iExists _.
      }
      iSplitL "Hpmpaddr0". { now iExists _. }
      iSplitL "Hpmpaddr1". { now iExists _. }
      now iExists _.
    - iIntros "Hmem".
      unfold interp_ptstomem_readonly.
      iInv "Hfortytwo" as ">Hptsto" "_".
      iDestruct "Hptsto" as "(Hptsto0 & Hptsto1 & Hptsto2 & Hptsto3)".
      iDestruct (interp_ptsto_valid with "Hmem Hptsto0") as "%res".
      iApply fupd_mask_intro; first set_solver.
      now iIntros "_".
  Qed.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)