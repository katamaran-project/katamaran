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
     BitvectorSolve
     Notations
     Specification
     SmallStep.Step
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.Model.
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
Import BlockVerification3.

  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Import BlockVerification3Sem.

    Open Scope hex_Z_scope.

    (* FIXED ADDRESSES *)
    (* The first address that is no longer used by the adversary, and hence the address at which the PMP entries should stop granting permission. Note that this address is currently also the first MMIO address. *)
    Definition adv_addr_end : N := N.of_nat maxAddr. (* Change once adversary gets access to MMIO*)
    (* Address where we will write in MMIO memory, and proof that our writes will indeed be within the MMIO region*)
    Definition mmio_write_addr : N := N.of_nat mmioStartAddr.
    Lemma write_word_is_MMIO: withinMMIO (bv.of_N mmio_write_addr) bytes_per_word.
    Proof.
      (* Avoid compute in case the list of MMIO addresses ever becomes longer *)
      repeat split; cbn; unfold mmioAddrs;
      eassert (mmioLenAddr = _) as -> by now compute. (* Get actual length so we can use successors *)
      all: rewrite 4!bv.seqBv_succ; repeat constructor.
    Qed.

    (* Aliases for registers *)
    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition t0 : RegIdx := [bv 5].

    Definition pure_privilege_to_bits {n} : Privilege -> bv n :=
      fun p => match p with | Machine => bv.of_N 3 | User => bv.zero end.

    Definition pure_mstatus_to_bits : Mstatus -> bv 20 :=
      fun '(MkMstatus mpp) => bv.app (@bv.zero 11) (pure_privilege_to_bits mpp).

    Definition pure_pmpAddrMatchType_to_bits : PmpAddrMatchType -> bv 4 :=
      fun mt => match mt with
                | OFF => bv.zero
                | TOR => bv.one
                end.

    Definition pure_pmpcfg_ent_to_bits : Pmpcfg_ent -> Val (ty.bvec byte) :=
      fun ent =>
        match ent with
        | MkPmpcfg_ent L A X W R =>
            let l : bv 1 := bv.of_bool L in
            let a : bv 4 := pure_pmpAddrMatchType_to_bits A in
            let x : bv 1 := bv.of_bool X in
            let w : bv 1 := bv.of_bool W in
            let r : bv 1 := bv.of_bool R in
            bv.app r (bv.app w (bv.app x (bv.app a l)))
        end%Z.

    (* Definitions for configuration bits of PMP entries *)
    Definition femto_pmpcfg_ent0 : Pmpcfg_ent := MkPmpcfg_ent false OFF false false false.
    Definition femto_pmpcfg_ent0_bits : Val (ty.bvec byte) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent0.
    Definition femto_pmpcfg_ent1 : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
    Definition femto_pmpcfg_ent1_bits : Val (ty.bvec byte) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent1.
    Definition femto_pmp0cfg_bits : Val (ty.bvec 32) := bv.zext (bv.app femto_pmpcfg_ent0_bits femto_pmpcfg_ent1_bits).

    (* Because of sign extension in the 12-bit immediate of ADDI/SW/LW, one cannot just take subranges to split immediates. Rather, the following function is used: *)
    (* See e.g.: https://stackoverflow.com/questions/50742420/risc-v-build-32-bit-constants-with-lui-and-addi *)
    Definition imm_split_bv (imm : bv 32) : (bv 12 * bv 20) :=
      let (lo , hi) := bv.appView 12 _ imm in
        if (base.decide (hi = (bv.ones 20))) then (lo , hi) (* Small negative numbers *)
        else if (bv.msb lo) (* Avoid incorrect sign-extension *)
             then (bv.of_Z (Z.of_N (bv.bin lo) - 4096), hi + bv.one)
             else (lo , hi).

    (* TODO: prove this spec for `imm_split_bv`*)
    (* Lemma imm_split_bv_spec lo hi imm : *)
    (*    (lo , hi) = imm_split_bv imm -> imm = bv.add (bv.shiftl (bv.zext hi) (@bv.of_N 12 12)) (bv.sext lo). *)

    Definition femto_pmp0cfg_bits_1 : Val (ty.bvec 12) := fst (imm_split_bv femto_pmp0cfg_bits).
    Definition femto_pmp0cfg_bits_2 : Val (ty.bvec 20) := snd (imm_split_bv femto_pmp0cfg_bits).

    (* ASTs with a very limited form of labels, that allow us to refer to the address of the current instruction *)
    (* TODO: have the symbolic executor work with these types of instructions directly? *)
    Inductive ASM :=
      | Instr (a: AnnotInstr)
      | RelInstr (f : N -> AnnotInstr).
    Local Coercion AST_AnnotAST (a : AST) := AnnotAST (a).
    Local Coercion AnnotAST_ASM (a : AnnotInstr) := Instr (a).
    Local Notation "'Λ' x , a" := (RelInstr (fun x => a))
      (at level 200) : list_scope.
    Local Arguments List.cons {_} & _ _. (* Allow projecting individual ASM into AST  - TODO: wrap `cons` in another definition so this bidirectionality does not interfere with lists *)

    (* The following definitions are required for layouting in memory, because otherwise we will count other things than instructions as taking up space *)
    Definition filter_AnnotInstr_AST (l : list AnnotInstr) := base.omap extract_AST l.
    Definition ASM_extract_AST (a : ASM) :=
      extract_AST
      (match a with
      | Instr a => a
      | RelInstr f => f 0%N end).
    Definition filter_ASM_AST (l : list ASM) := base.omap ASM_extract_AST l.

    (* Address resolution *)
    Fixpoint resolve_ASM (la : list ASM) (cur_off : N) : list AnnotInstr :=
      match la with
      | nil => nil
      | cons hd tl =>
          let hd' := (match hd with
          | Instr a => a
          | RelInstr f => f cur_off end) in
          let new_off : N :=
            (* Only instructions should increase the current offset, whereas lemma and debug calls will be filtered out in the end! *)
            (match BlockVerification3Sem.extract_AST hd' with
            | Some _ => (cur_off + N.of_nat xlenbytes)%N
            | _ => cur_off
            end) in
              cons hd' (resolve_ASM tl new_off)
       end.

    (* Init code is the same in both versions of the femtokernel, since MMIO memory is placed after the adversary code, hence not affecting initialization *)
    Example femtokernel_init_asm (handler_start : N) (adv_start : N): list ASM :=
      [
        UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, ITYPE (bv.of_N (adv_start - (x - 4))) ra ra RISCV_ADDI
      ; CSR MPMPADDR0 ra zero false CSRRW
      ; ITYPE (bv.of_N adv_addr_end) zero ra RISCV_ADDI
      ; CSR MPMPADDR1 ra zero false CSRRW
      ; UTYPE femto_pmp0cfg_bits_2 ra RISCV_LUI
      ; ITYPE femto_pmp0cfg_bits_1 ra ra RISCV_ADDI
      ; CSR MPMP0CFG ra zero false CSRRW
      ; UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, ITYPE (bv.of_N (handler_start - (x - 4))) ra ra RISCV_ADDI
      ; CSR MTvec ra zero false CSRRW
      ; ITYPE (bv.of_N (adv_start - handler_start)) ra ra RISCV_ADDI
      ; CSR MEpc ra zero false CSRRW
      ; CSR MStatus zero zero false CSRRW
      ; MRET
      ].

    Example femtokernel_init' (init_start : N) (handler_start : N) (adv_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_init_asm handler_start adv_start) init_start.

    Example femtokernel_handler_asm (data_start : N) : list ASM :=
      [
        UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, LOAD (bv.of_N (data_start - (x - 4))) ra ra false WORD
      ; MRET
      ].
    Example femtokernel_handler' (handler_start : N) (data_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm data_start) handler_start.

    Example femtokernel_mmio_handler_asm : list ASM :=
      [
        ITYPE (bv.of_N 42) zero t0 RISCV_ADDI
      ; UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, AnnotLemmaInvocation (close_mmio_write (bv.of_N (mmio_write_addr - (x - 4))) WORD) [nenv exp_val ty_xlenbits (bv.of_N (x - 4)); exp_val ty_xlenbits (bv.of_N 42)]%env (* TODO: notation to avoid lemma call copying LOAD instruction/internalize immediate as well?*)
      ; Λ x, STORE (bv.of_N (mmio_write_addr - (x - 4))) t0 ra WORD
      ; MRET
      ].
    Example femtokernel_mmio_handler' (handler_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm) handler_start.

    (* SIZES *)
    Definition init_size : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_init' 0 0 0))) * 4.

    Definition handler_size : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_handler' 0 0))) * 4.
    Definition mmio_handler_size : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_mmio_handler' 0))) * 4.
    (* Note: MMIO has no `data` region, hence no data size or address. *)
    Definition data_size : N := 4.

    (* ADDRESSES *)
    Definition init_addr     : N := 0.
    Definition handler_addr  : N := init_addr + init_size.
    (* NOTE: There is no data in the MMIO case, but we just keep *)
    Definition data_addr     : N := handler_addr + handler_size.
    Definition adv_addr      : N := data_addr + data_size.
    Definition mmio_adv_addr : N := handler_addr + mmio_handler_size.
    (* NOTE: We have set things up so that the `adv_addr` and the `mmio_adv_addr` are equal in both cases, such that we can reuse the proofs. Prove that this is the case here, to make sure that we gets stuck if we ever make changes that break this hypothesis. *)
    Lemma adv_mmio_eq : adv_addr = mmio_adv_addr. Proof. now compute. Qed.
    (* Since both are equal, we continue with just the `adv_addr` from now on *)

    (* CODE AND CONFIG SHORTANDS*)
    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
    (* Shorthand for the pmp entries in both Katamaran and Iris *)
    Local Notation asn_femto_pmpentries := ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr)));
                                       (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ term_val ty_xlenbits (bv.of_N adv_addr_end))])%list. (* NOTE: `first_addr` is usually equal to the logical variable `a` + `adv_start` *)
    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end)]%list.
    (* Definition of the femtokernel initialization procedure that works both for the legacy and the MMIO case, since the address of the adversary is equal in both cases *)
    Definition femtokernel_init_gen := femtokernel_init' init_addr handler_addr adv_addr.

    (* The code is different in both cases for the handler, so we cannot derive the concrete cases from the more general one. *)
    Definition femtokernel_handler := femtokernel_handler' handler_addr data_addr.
    Definition femtokernel_mmio_handler := femtokernel_mmio_handler' handler_addr.
    (* We reflect the booleans present in the contracts, but now at the meta level. This allows us to recycle large parts of the Katamaran and Iris contracts as part of the verification. *)
    Definition femtokernel_handler_gen (is_mmio : bool) := if is_mmio then femtokernel_mmio_handler else femtokernel_handler.

    Import asn.notations.
    Import RiscvPmp.Sig.
    (* Local Notation "a '↦[' n ']' xs" := (asn.chunk (chunk_user ptstomem [a; n; xs])) (at level 79). *)
    Local Notation "a '↦ₘ' t" := (asn.chunk (chunk_user ptsto [a; t])) (at level 70).
    Local Notation "a '↦ᵣ' t" := (asn.chunk (chunk_user (ptstomem_readonly bytes_per_word) [a; t])) (at level 70).
    Local Notation asn_inv_mmio := (asn.chunk (chunk_user (inv_mmio bytes_per_word) [env])). (* Fix word length at 4 for this example, as we do not perform any other writes*)
    Local Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Let Σ__femtoinit : LCtx := [].
    Let W__femtoinit : World := MkWorld Σ__femtoinit []%ctx.

    Example femtokernel_init_pre : Assertion {| wctx := [] ▻ ("a"::ty_xlenbits) ; wco := []%ctx |} :=
      (term_var "a" = term_val ty_word bv.zero) ∗
      (∃ "v", mstatus ↦ term_var "v") ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∗
      (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                      (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])).

    Example femtokernel_init_post: Assertion  {| wctx := [] ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits) ; wco := []%ctx |} :=
      (
        asn.formula (formula_relop bop.eq (term_var "an") (term_var "a" + term_val ty_xlenbits (bv.of_N adv_addr))) ∗
          (∃ "v", mstatus ↦ term_var "v") ∗
          (mtvec ↦ (term_var "a" + term_val ty_xlenbits (bv.of_N handler_addr))) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mepc ↦ term_var "v") ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          asn_regs_ptsto ∗
          asn_pmp_entries (term_list (asn_femto_pmpentries))
      )%exp.

    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__femtoinit : 𝕊 Σ__femtoinit :=
      postprocess (VC__addr femtokernel_init_pre femtokernel_init_gen femtokernel_init_post).
    (*   let vc1 := VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post in *)
    (*   let vc2 := Postprocessing.prune vc1 in *)
    (*   let vc3 := Postprocessing.solve_evars vc1 in *)
    (*   let vc4 := Postprocessing.solve_uvars vc3 in *)
    (*   let vc5 := Postprocessing.prune vc4 in *)
    (*   vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in vc__femtoinit. *)

    (* NOTE: For now we only get one case here, since the start of the adversary region is the same in both cases. If this were not the case, we would take a naive approach to verifying both versions of the initialization code here; we would require that `adv_start` takes one of the two values present in the two versions of the initialization code. A more general approach would verify the contract under a logical value for `adv_start`. This would require the block verifier to support taking a list of instructions that can depend on symbolic values as input (i.e. proper terms). *)
    Lemma sat__femtoinit : safeE vc__femtoinit.
    Proof.
      now vm_compute.
    Qed.

    Let Σ__femtohandler : LCtx := [].
    Let W__femtohandler : World := MkWorld Σ__femtohandler []%ctx.

    (* NOTE: in one case the handler reads (legacy) and in the other it writes (mmio). However, this does not have an impact on the shape of the contract, as we do not directly talk about the written/read value *)
    Example femtokernel_handler_pre (is_mmio : bool) : Assertion {| wctx := ["a" :: ty_xlenbits]; wco := []%ctx |} :=
      (term_var "a" = term_val ty_word (bv.of_N handler_addr)) ∗
      (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
      (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "epc", mepc ↦ term_var "epc") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∗
      asn_pmp_entries (term_list asn_femto_pmpentries) ∗ (* Different handler sizes cause different entries *)
      if negb is_mmio then
        (term_val ty_xlenbits (bv.of_N data_addr) ↦ᵣ term_val ty_xlenbits (bv.of_N 42))%exp
      else asn_inv_mmio.

    Example femtokernel_handler_post (is_mmio : bool) : Assertion {| wctx := ["a" :: ty_xlenbits; "an"::ty_xlenbits]; wco := []%ctx |} :=
          (mstatus ↦ term_val (ty.record rmstatus) {| MPP := User |}) ∗
          (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "epc", (mepc ↦ term_var "epc" ∗
                     asn.formula
                         (formula_relop bop.eq (term_var "an")
                                     (term_var "epc")))) ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          asn_regs_ptsto ∗
          asn_pmp_entries (term_list asn_femto_pmpentries) ∗ (* Different handler sizes cause different entries *)
          if negb is_mmio then
            (term_val ty_xlenbits (bv.of_N data_addr) ↦ᵣ term_val ty_xlenbits (bv.of_N 42))%exp
          else ⊤ (* Inv is persistent; don't repeat *).

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

    Definition vc__femtohandler (is_mmio : bool) : 𝕊 [] :=
      postprocess (VC__addr (femtokernel_handler_pre is_mmio) (femtokernel_handler_gen is_mmio) (femtokernel_handler_post is_mmio)).

      (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in vc__femtohandler. *)

    Lemma sat__femtohandler (is_mmio : bool) : safeE (vc__femtohandler is_mmio).
    Proof.
      destruct is_mmio.
      - (* For the mmio case, we still need to prove that our word falls within mmio *)
      vm_compute; constructor; cbn.
      split; [apply write_word_is_MMIO | auto].
      - now vm_compute.
    Qed.

    Definition femtoinit_stats :=
      SymProp.Statistics.count_to_stats
        (SymProp.Statistics.count_nodes
           (VC__addr femtokernel_init_pre femtokernel_init_gen (asn.sep femtokernel_init_post asn.debug))
           SymProp.Statistics.empty).
    (* Eval vm_compute in femtoinit_stats. *)

    (* There is currently no difference, because the adversary addresses are shared between both cases*)
    Definition femto_mmio_init_stats := femtoinit_stats.
    (* Eval vm_compute in femto_mmio_init_stats. *)

    Definition femtohandler_stats :=
      SymProp.Statistics.count_to_stats
        (SymProp.Statistics.count_nodes
           (VC__addr (femtokernel_handler_pre false) femtokernel_handler (asn.sep (femtokernel_handler_post false) asn.debug))
           SymProp.Statistics.empty).
    (* Eval vm_compute in femtohandler_stats. *)

    Definition femtohandler_mmio_stats :=
      SymProp.Statistics.count_to_stats
        (SymProp.Statistics.count_nodes
           (VC__addr (femtokernel_handler_pre true) femtokernel_mmio_handler (asn.sep (femtokernel_handler_post true) asn.debug))
           SymProp.Statistics.empty).
    (* Eval vm_compute in femtohandler_mmio_stats. *)

  End FemtoKernel.

  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
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
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.tactics.
  Import BlockVerificationDerived2.
  Import Shallow.Executor.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.
  Import BlockVerificationDerived2Sound.
  Import BlockVerificationDerived2Sem.
  Import BlockVerification3Sem.

  Definition advAddrs : list (bv xlenbits) := bv.seqBv (bv.of_N adv_addr) (N.to_nat adv_addr_end - N.to_nat adv_addr).

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (exists p2, Pmp_access x (bv.of_nat 1) ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access, Gen_Pmp_access.
    destruct (pmp_check_aux x (bv.of_nat 1) bv.zero ents p1 p2); [left|right]; easy.
  Defined.


  Lemma adv_is_live y : (y ∈ advAddrs)%stdpp → (y ∈ liveAddrs)%stdpp.
  Proof. unfold advAddrs, liveAddrs.
         apply bv.seqBv_sub_elem_of; now compute.
  Qed.

  Ltac case_if H :=
    let go P := (destruct P eqn:H) in
      match goal with
      | |- context [if ?P then _ else _] => go P
      | K: context [if ?P then _ else _] |- _ => go P
      end.

  Lemma adv_in_pmp x : (x ∈ advAddrs)%stdpp -> (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p).
  Proof.
    intro Hin. rewrite /femto_pmpentries.
    exists Read.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry].
    apply bv.seqBv_in' in Hin as [Hlo Hhi]; [|clear Hin; now compute].
    cbn in *. eassert (adv_addr = _) as -> by now compute.
    unfold bv.uleb, bv.ule, bv.ult, bv.ultb in *.
    set (y := bv.bin x) in *. (* Avoid this being simplified later on, just sub when we need it *)
    cbv -[N.le N.lt y] in Hlo,Hhi.
    case_if H; [now compute | clear H].
    case_if H.
    { rewrite bv.bin_add_small in H.
      - apply orb_prop in H as [|]; rewrite N.leb_le -/y /= in H; lia.
      - cbn. unfold N.of_nat. cbn. lia. }
    clear H. case_if H; first easy.
    { rewrite bv.bin_add_small /= -/y in H; last lia.
      apply andb_false_iff in H as [|]; rewrite N.leb_gt in H; solve_bv. }
  Qed.

  Lemma pmp_in_adv x : (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p) → (x ∈ advAddrs)%stdpp.
  Proof.
    intros [p HPmp]. rewrite /femto_pmpentries.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry] in HPmp. cbn in HPmp.
    case_if H; first now compute. clear H.
    unfold bv.uleb in *.
    case_if H; first by exfalso.
    apply orb_false_elim in H as [_ Hhi]. rewrite N.leb_gt in Hhi.
    case_if H'; last by exfalso.
    apply andb_prop in H' as [Hlo _]. rewrite N.leb_le in Hlo.
    apply bv.in_seqBv; exact.
  Qed.

  (* Use permutation rather than membership to avoid indexes *)
  Lemma allAddr_filter_advAddr : filter
                 (λ x : Val ty_word ,
                    (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p)%type)
                 all_addrs ≡ₚ advAddrs.
  Proof. rewrite (list_filter_iff _ (fun x => x ∈ advAddrs)); last split; auto using adv_in_pmp, pmp_in_adv.
    apply NoDup_Permutation.
    - apply NoDup_filter. rewrite all_addrs_eq. refine (bv.NoDup_seqbv _).
      rewrite bv.exp2_spec Nat2N.inj_pow. now cbn -[xlenbits].
    - apply bv.NoDup_seqbv. now compute.
    - intros x. rewrite elem_of_list_filter.
      split.
      + now intros [? ?].
      + split; [auto | apply addr_in_all_addrs].
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
      interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User)%I.
  Proof.
    iIntros "Hadv".
    unfold interp_pmp_addr_access.
    rewrite <-(big_sepL_filter).
    unfold ptstoSthL.
    rewrite -> (big_opL_permutation _ _ _ allAddr_filter_advAddr).
    iApply (big_sepL_mono with "Hadv"). iIntros (? ? Hsom) "Hptsto".
    unfold interp_addr_access_byte.
    apply elem_of_list_lookup_2, adv_is_live in Hsom.
    repeat case_decide; auto.
    iPureIntro. eapply mmio_ram_False; eauto.
  Qed.

  Definition femto_inv_fortytwo `{sailGS Σ} : iProp Σ := @interp_ptstomem_readonly _ _ _ xlenbytes (bv.of_N data_addr) (bv.of_N 42).
  Definition femto_inv_mmio `{sailGS Σ} := interp_inv_mmio bytes_per_word.

  Local Notation "a '↦' t" := (reg_pointsTo a t) (at level 79).
  (* Local Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 79). *)

  Definition femto_handler_pre `{sailGS Σ} (is_mmio : bool): iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
      (mtvec ↦ (bv.of_N handler_addr)) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ epc, mepc ↦ epc) ∗
      cur_privilege ↦ Machine ∗
      interp_gprs ∗
      interp_pmp_entries femto_pmpentries ∗
      (if negb is_mmio
        then femto_inv_fortytwo
        else femto_inv_mmio) ∗
      pc ↦ (bv.of_N handler_addr) ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio)).

    Example femto_handler_post `{sailGS Σ} (is_mmio : bool): iProp Σ :=
      (mstatus ↦ {| MPP := User |}) ∗
      (mtvec ↦ (bv.of_N handler_addr)) ∗
      (∃ v, mcause ↦ v) ∗
      cur_privilege ↦ User ∗
      interp_gprs ∗
      interp_pmp_entries femto_pmpentries ∗
      (if negb is_mmio
        then femto_inv_fortytwo
        else True%I) ∗
      (∃ epc, mepc ↦ epc ∗
              pc ↦ epc) ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio)).

  Definition femto_handler_contract `{sailGS Σ} (is_mmio : bool): iProp Σ :=
    femto_handler_pre is_mmio -∗
        (femto_handler_post is_mmio -∗ WP_loop) -∗
        WP_loop.

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre.

  Import env.notations.
  Lemma femto_handler_verified (is_mmio: bool): forall `{sailGS Σ}, ⊢ femto_handler_contract is_mmio.
  Proof.
    iIntros (Σ sG) "Hpre Hk".
    iApply (sound_VC__addr lemSemBlockVerif $! (bv.of_N handler_addr) with "[Hpre] [Hk]").
    - exact (sat__femtohandler is_mmio). Unshelve. exact [env].
    - cbv [femtokernel_handler_pre interpret_chunk lptsreg PredicateDefIProp
           inst instprop_formula inst_term env.lookup ctx.view ctx.in_at
           ctx.in_valid inst_env
           env.map].
      cbn.
      iDestruct "Hpre" as "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp & Hfortytwo & Hpc & Hnpc & Hhandler)".
      rewrite Model.RiscvPmpModel2.gprs_equiv. cbn.
      iFrame. destruct is_mmio; now iFrame.
    - cbv [femtokernel_handler_pre interpret_chunk lptsreg PredicateDefIProp
           inst instprop_formula inst_term env.lookup ctx.view ctx.in_at
           ctx.in_valid inst_env env.map femto_handler_post
           femtokernel_handler_post].
      cbn.
      iIntros (an) "(Hpc & Hnpc & Hhandler & Hmstatus & Hmtvec & Hmcause & [% (Hmepc & [%eq _])] & Hcurpriv & Hregs & Hpmp & Hfortytwo)".
      cbn.
      iApply "Hk".
      cbn in eq; destruct eq.
      rewrite Model.RiscvPmpModel2.gprs_equiv.
      iFrame "Hmstatus Hmtvec Hmcause Hcurpriv Hregs Hpmp Hnpc Hhandler".
      destruct is_mmio; cbn; iFrame.
      iSplit; auto.
      all: iExists an; iFrame.
  Qed.

  Transparent femtokernel_handler_pre.
  Opaque interp_pmp_entries.

  (* Needed when introducing the below conditional *)
  Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B).
  Proof. destruct b; apply _. Qed.

  Lemma femtokernel_handler_safe `{sailGS Σ} (is_mmio : bool) :
    ⊢ mstatus ↦ {| MPP := User |} ∗
       (mtvec ↦ (bv.of_N handler_addr)) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ mepcv, mepc ↦ mepcv) ∗
        cur_privilege ↦ Machine ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
        (if negb is_mmio
         then femto_inv_fortytwo
         else femto_inv_mmio) ∗
        (pc ↦ (bv.of_N handler_addr)) ∗
        interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User ∗ (* Not needed for handler, but required for the rest of execution *)
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio))
        -∗
        WP_loop.
  Proof.
    cbn - [interp_pmp_entries]. iLöb as "Hind".
    iIntros "(Hmstatus & Hmtvec & Hmcause & [%mepcv Hmepc] & Hcurpriv & Hgprs & Hpmpentries & #Hmem & Hpc & HaccU & Hnextpc & Hinstrs)".
    iApply (femto_handler_verified with "[$Hmstatus $Hmtvec $Hmcause Hmepc $Hcurpriv $Hgprs $Hpmpentries $Hpc $Hnextpc $Hinstrs $Hmem] [HaccU]");
      first by now iExists mepcv.
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hcurpriv & Hgprs & Hpmpentries & #Hmem' & [%epc (Hmepc & Hpc)] & Hnpc & Hhandler)".
    iApply (LoopVerification.valid_semTriple_loop with "[Hmem $Hmstatus $Hmtvec $Hmcause Hmepc $Hpc $Hcurpriv $Hgprs $Hpmpentries $Hnpc $HaccU Hhandler]").
    iSplitL "Hmepc"; first by now iExists epc.
    iSplitL "".
    { iModIntro.
      unfold LoopVerification.CSRMod.
      iIntros "(_ & _ & _ & %eq & _)".
      inversion eq.
    }

    iSplitR "".
    { iModIntro.
      unfold LoopVerification.Trap.
      iIntros "(HaccU & Hgprs & Hpmpentries & Hmcause & Hcurpriv & Hnextpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
      iApply ("Hind" with "[$Hmstatus $Hmtvec $Hmcause $Hmepc $Hcurpriv $Hpmpentries $Hpc $HaccU Hnextpc Hmem $Hgprs $Hhandler $Hmem]").
      now iExists _.
    }

    { iModIntro.
      unfold LoopVerification.Recover.
      iIntros "(_ & _ & _ & %eq & _)".
      inversion eq.
    }
  Qed.

  (* TODO: this lemma feels very incremental wrt to the last one; merge? *)
  Lemma femtokernel_manualStep2 `{sailGS Σ} (is_mmio : bool):
    ⊢ (∃ mpp, mstatus ↦ {| MPP := mpp |}) ∗
       (mtvec ↦ (bv.of_N handler_addr)) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        interp_pmp_entries femto_pmpentries ∗
        (if negb is_mmio
         then femto_inv_fortytwo
         else femto_inv_mmio) ∗
        (pc ↦ (bv.of_N adv_addr)) ∗
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio)) ∗
        ptstoSthL advAddrs
        ={⊤}=∗
        ∃ mpp, LoopVerification.loop_pre User (bv.of_N handler_addr) (bv.of_N adv_addr) mpp femto_pmpentries.
  Proof.
    iIntros "([%mpp Hmst] & Hmtvec & [%mcause Hmcause] & [%mepc Hmepc] & Hcurpriv & Hgprs & Hpmpcfg & #Hfortytwo & Hpc & Hnpc & Hhandler & Hmemadv)".
    iExists mpp.
    unfold LoopVerification.loop_pre, LoopVerification.Step_pre, LoopVerification.Execution.
    iFrame.
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
    iApply (femtokernel_handler_safe with "[$Hmem $Hgprs $Hpmpents $Hmcause $Hcurpriv Hnpc $Hpc $Hmtvec $Hmstatus $Hmepc $Hfortytwo $Hhandler]").
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
      pmp0cfg ↦ default_pmpcfg_ent ∗
      pmp1cfg ↦ default_pmpcfg_ent ∗
      (pmpaddr0 ↦ bv.zero) ∗
      (pmpaddr1 ↦ bv.zero)) ∗
      pc ↦ bv.zero ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen).

    Example femto_init_post `{sailGS Σ} : iProp Σ :=
      ((∃ v, mstatus ↦ v) ∗
        (mtvec ↦ (bv.of_N handler_addr)) ∗
        (∃ v, mcause ↦ v) ∗
        (∃ v, mepc ↦ v) ∗
        cur_privilege ↦ User ∗
        interp_gprs ∗
        pmp0cfg ↦ femto_pmpcfg_ent0 ∗
        pmp1cfg ↦ femto_pmpcfg_ent1 ∗
        (pmpaddr0 ↦ (bv.of_N adv_addr)) ∗
        (pmpaddr1 ↦ (bv.of_N adv_addr_end))) ∗
        pc ↦ (bv.of_N adv_addr) ∗
        (∃ v, nextpc ↦ v) ∗
        ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen).

  Definition femto_init_contract `{sailGS Σ} : iProp Σ :=
    femto_init_pre -∗
      (femto_init_post -∗ WP_loop) -∗
          WP_loop.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.
  Transparent interp_pmp_entries.

  Local Opaque femtokernel_init_gen. (* TODO: figure out why not having this makes the below proof spin in two places *)

  Lemma femto_init_verified : forall `{sailGS Σ}, ⊢ femto_init_contract.
  Proof.
    iIntros (Σ sG) "Hpre Hk".
    iApply (sound_VC__addr lemSemBlockVerif sat__femtoinit [env] $! bv.zero with "[Hpre] [Hk]").
    - unfold femto_init_pre. cbn -[ptsto_instrs].
      iDestruct "Hpre" as "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmp1cfg & Hpmpaddr0 & Hpmpaddr1) & Hpc & Hnpc & Hinit)".
      rewrite Model.RiscvPmpModel2.gprs_equiv.
      now iFrame "Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hgprs Hpmp0cfg Hpmp1cfg Hpc Hnpc Hinit Hpmpaddr0 Hpmpaddr1".
    - iIntros (an) "(Hpc & Hnpc & Hhandler & [%eq _] & (Hmstatus & Hmtvec & Hmcause & Hmepc & Hcp & (Hgprs & (Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1))))".
      iApply ("Hk" with "[Hpc $Hnpc $Hhandler $Hmstatus $Hmtvec $Hmcause $Hmepc $Hcp Hgprs $Hpmp0cfg $Hpmpaddr0 $Hpmp1cfg $Hpmpaddr1]").
      cbn in eq. subst.
      rewrite Model.RiscvPmpModel2.gprs_equiv.
      now iFrame.
  Qed.

  (* see above *)
  Transparent femtokernel_init_pre.

  Lemma femtokernel_init_safe `{sailGS Σ} (is_mmio : bool):
    ⊢ (∃ v, mstatus ↦ v) ∗
      (∃ v, mtvec ↦ v) ∗
      (∃ v, mcause ↦ v) ∗
      (∃ v, mepc ↦ v) ∗
      cur_privilege ↦ Machine ∗
      interp_gprs ∗
      reg_pointsTo pmp0cfg default_pmpcfg_ent ∗
      (reg_pointsTo pmpaddr0 bv.zero) ∗
      reg_pointsTo pmp1cfg default_pmpcfg_ent ∗
      (reg_pointsTo pmpaddr1 bv.zero) ∗
      (pc ↦ bv.zero) ∗
      (if negb is_mmio
        then femto_inv_fortytwo
        else femto_inv_mmio) ∗ (* This is not needed for the `init` code, but it is needed later on *)
      ptstoSthL advAddrs ∗
      (∃ v, nextpc ↦ v) ∗
      ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio))
      -∗
      WP_loop.
  Proof.
    iIntros "(Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & Hpc & Hfortytwo & Hadv & Hnextpc & Hinit & Hhandler)".
    iApply (femto_init_verified with "[$Hmstatus $Hmtvec $Hmcause $Hmepc $Hcurpriv $Hgprs $Hpmp0cfg $Hpmpaddr0 $Hpmp1cfg $Hpmpaddr1 $Hpc $Hinit $Hnextpc]").
    iIntros "((Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & Hgprs & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1) & Hpc & Hnextpc & Hinit)".
    iAssert (interp_pmp_entries femto_pmpentries) with "[Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1]" as "Hpmpents".
    { unfold interp_pmp_entries; cbn; iFrame. }
    iApply fupd_wp.
    iMod (femtokernel_manualStep2 with "[Hmstatus $Hmtvec $Hmcause $Hgprs $Hcurpriv $Hpmpents $Hfortytwo $Hpc $Hnextpc $Hhandler $Hadv $Hmepc ]") as "[%mpp Hlooppre]".
    {iDestruct "Hmstatus" as "[%mst Hmstatus]".
      destruct mst as [mpp].
      now iExists mpp.
    }
    now iApply LoopVerification.valid_semTriple_loop.
  Qed.

  Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
    exists v0 v1 v2 v3, map (memory_ram μ) (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

  (* byte order correct? *)
  Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
    exists w, mem_has_word μ a w /\ pure_decode w = inr instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
    match instrs with
    | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
    | nil => True
    end.

  Import RiscvPmpSemantics.
  Import RiscvPmpIrisAdeqParameters.
  Import SmallStepNotations.

  Import iris.bi.big_op.
  Import iris.algebra.big_op.

  (* Note that the split differs depending on whether or not we have an MMIO region! *)
  Lemma liveAddrs_split (is_mmio : bool): liveAddrs = bv.seqBv (bv.of_N init_addr) (N.to_nat init_size) ++ bv.seqBv (bv.of_N handler_addr) (if negb is_mmio then N.to_nat handler_size else N.to_nat mmio_handler_size) ++ (if negb is_mmio then bv.seqBv (bv.of_N data_addr) (N.to_nat data_size) else [](* There is no data; conjunct is just here for conformity *)) ++ advAddrs.
  Proof.
    (* TODO: scalable proof *)
    destruct is_mmio; by compute.
  Qed.

  Lemma intro_ptstomem_word `{sailGS Σ} v0 v1 v2 v3 (a : Val ty_word) :
    interp_ptsto (bv.of_Z (0 + bv.unsigned a)) v0 ∗
    interp_ptsto (bv.of_Z (1 + bv.unsigned a)) v1 ∗
    interp_ptsto (bv.of_Z (2 + bv.unsigned a)) v2 ∗
    interp_ptsto (bv.of_Z (3 + bv.unsigned a)) v3 ⊢
      interp_ptstomem (width := 4) a (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil)))).
  Proof.
    iIntros "(Hmema & Hmema1 & Hmema2 & Hmema3)".
    unfold interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    now iFrame.
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word2 `{sailGS Σ} {μ : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ a v ->
    ([∗ list] a' ∈ bv.seqBv a 4, interp_ptsto a' ((memory_ram μ) a')) ⊢ interp_ptstomem a v.
  Proof.
    iIntros (Hmhw) "Hmem".
    destruct Hmhw as (v0 & v1 & v2 & v3 & Heqμ & Heqv).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem" as "(Hmema & Hmema1 & Hmema2 & Hmema3 & _)".
    inversion Heqμ; subst.
    now iApply (intro_ptstomem_word with "[$Hmema $Hmema1 $Hmema2 $Hmema3]").
  Qed.

  Lemma intro_ptsto_instr `{sailGS Σ} {μ : Memory} {a : Val ty_word} {instr : AST} :
    (4 + bv.bin a < bv.exp2 xlenbits)%N ->
    mem_has_instr μ a instr ->
    ([∗ list] a' ∈ bv.seqBv a 4, interp_ptsto a' ((memory_ram μ) a'))
      ⊢ interp_ptsto_instr a instr.
  Proof.
    iIntros (Hrep (v & Hmhw & Heq)) "Hmem".
    iExists v.
    iSplitL; last done.
    now iApply (intro_ptstomem_word2 Hmhw).
  Qed.

  Lemma intro_ptsto_instrs `{sailGS Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * N.of_nat (length instrs) + bv.bin a < bv.exp2 xlenbits)%N ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seqBv a (4 * length instrs), interp_ptsto a' ((memory_ram μ) a'))
      ⊢ ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - rewrite Nat2N.inj_succ in Hrep.
      fold (length instrs) in Hrep.
      replace (4 * length (instr :: instrs)) with (4 + 4 * length instrs) by (cbn; lia).
      rewrite bv.seqBv_app; try (cbn -[N.of_nat N.mul] in *; Lia.lia).
      rewrite big_opL_app.
      destruct Hmeminstrs as [Hinstr Hmeminstrs].
      iDestruct "Hmem" as "[Hmema Hmema4]".
      iSplitL "Hmema".
      + iApply (intro_ptsto_instr with "Hmema"); auto; Lia.lia.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply ("IH" with "[%] [% //] [-]").
        * rewrite bv.bin_add_small;
          cbn -[N.mul] in *;
          now Lia.lia.
        * now rewrite ?bv.add_assoc.
  Qed.

  Lemma intro_ptstoSthL `{sailGS Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, interp_ptsto a' ((memory_ram μ) a')) ⊢ ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists ((memory_ram μ) a).
      + now iApply IHl.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto {Σ : gFunctors} {H : sailGS Σ} {s e} (μ : Memory):
    (minAddr <= N.to_nat (bv.bin s)) → N.to_nat (bv.bin s) + e <= minAddr + lenAddr →
    ([∗ list] y ∈ bv.seqBv s e, gen_heap.mapsto y (dfrac.DfracOwn 1) (memory_ram μ y)) ⊢ [∗ list] a' ∈ bv.seqBv s e, interp_ptsto a' (memory_ram μ a').
  Proof.
    iIntros (Hlow Hhi) "Hlist".
    iApply (big_sepL_mono with "Hlist"). intros ? ? Hsom. cbn.
    iIntros "$". iPureIntro.
    rewrite /= /not; apply mmio_ram_False.
    apply elem_of_list_lookup_2 in Hsom.
    refine (bv.seqBv_sub_elem_of _ _ Hsom).
    - solve_bv.
    - rewrite bv.bin_of_nat_small; last apply minAddr_rep. lia.
  Qed.

  Lemma femtokernel_splitMemory `{sailGS Σ} {μ : Memory} (is_mmio : bool):
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio)) ->
    (if negb is_mmio then mem_has_word μ (bv.of_N data_addr) (bv.of_N 42) else mmio_pred bytes_per_word (memory_trace μ)) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    @mem_res _ sailGS_memGS μ ⊢ |={⊤}=>
      ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio)) ∗
      (if negb is_mmio
      then femto_inv_fortytwo
      else femto_inv_mmio) ∗
      ptstoSthL advAddrs.
  Proof.
    iIntros (Hinit Hhandler Hft) "Hmem".
    unfold mem_res, initMemMap.
    rewrite (liveAddrs_split is_mmio).
    rewrite ?map_app ?list_to_map_app ?big_sepM_union.
    iDestruct "Hmem" as "[(Hinit & Hhandler & Hfortytwo & Hadv) Htr]".
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); compute; lia. }
    iSplitL "Hhandler". (* Need to solve the goal for both handlers *)
    { iApply (intro_ptsto_instrs (μ := μ)); [destruct is_mmio; easy..|].
      destruct is_mmio; iApply (sub_heap_mapsto_interp_ptsto with "Hhandler"); compute; lia. }
    iSplitL "Hfortytwo Htr".
    - (* Two cases; either we set up the trace invariant o memory invariant or the trace invariant. *)
      destruct (negb is_mmio).
      + iAssert (interp_ptstomem (bv.of_N data_addr) (bv.of_N 42)) with "[Hfortytwo]" as "Hfortytwo".
      { iApply (intro_ptstomem_word2 Hft).
        iApply (sub_heap_mapsto_interp_ptsto with "Hfortytwo"); compute; lia. }
      iMod (inv.inv_alloc femto_inv_ro_ns ⊤ (interp_ptstomem (bv.of_N data_addr) (bv.of_N 42)) with "Hfortytwo") as "Hinv".
      now iModIntro.
      + iApply (inv.inv_alloc). iExists _; now iFrame.
    - iApply (intro_ptstoSthL μ).
      iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); compute; lia.
  Qed.

  Lemma interp_ptsto_valid `{sailGS Σ} {μ a v} :
    ⊢ mem_inv _ μ -∗ interp_ptsto a v -∗ ⌜(memory_ram μ) a = v⌝.
  Proof.
    unfold interp_ptsto, mem_inv.
    iIntros "(%memmap & Hinv & %link & Htr) [Hptsto %Hmmio]".
    iDestruct (gen_heap.gen_heap_valid with "Hinv Hptsto") as "%x".
    iPureIntro.
    now apply (map_Forall_lookup_1 _ _ _ _ link).
  Qed.

  (* TODO: move to bitvector *)
  Lemma bv0_is_nil (x : bv 0) : x = bv.nil.
  Proof.
    destruct x as [bin wf].
    destruct bin; first by apply bv.bin_inj.
    by exfalso.
  Qed.

  (* TODO: use this lemma in earlier proofs, like `read_ram_works`? *)
  Lemma interp_ptstomem_valid `{sailGS Σ} {μ a v} :
    ⊢ mem_inv _ μ -∗ interp_ptstomem a v -∗ ⌜mem_has_word μ a v⌝.
  Proof.
    iIntros "Hinv Hptstomem".

    (* Prep hypotheses first *)
    do 4 destruct (bv.appView byte _ v) as [? v].
    (* rewrite (bv0_is_nil v). *)

    repeat iExists _.
    rewrite bv.app_nil_r. (* Get rid of annoying `nil` bv *)
    iSplit; last eauto.

    rewrite !ptstomem_bv_app.
    iDestruct "Hptstomem" as "(Ha0 & Ha1 & Ha2 & Ha3 & Htail)".
    iDestruct (interp_ptsto_valid with "Hinv Ha0") as "%Hm0".
    iDestruct (interp_ptsto_valid with "Hinv Ha1") as "%Hm1".
    iDestruct (interp_ptsto_valid with "Hinv Ha2") as "%Hm2".
    iDestruct (interp_ptsto_valid with "Hinv Ha3") as "%Hm3".

    iPureIntro.
    rewrite (bv0_is_nil v) bv.app_nil_r.
    rewrite !bv.seqBv_succ !map_cons.
    repeat f_equal; auto.
  Qed.


  Lemma femtokernel_endToEnd {γ γ' : RegStore} {μ μ' : Memory}
        {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} (is_mmio : bool) :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen is_mmio)) ->
    (if negb is_mmio then mem_has_word μ (bv.of_N data_addr) (bv.of_N 42) else mmio_pred bytes_per_word (memory_trace μ)) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    read_register γ cur_privilege = Machine ->
    read_register γ pmp0cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr0 = bv.zero ->
    read_register γ pmp1cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr1 = bv.zero ->
    read_register γ pc = (bv.of_N init_addr) ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    (if negb is_mmio then mem_has_word μ' (bv.of_N data_addr) (bv.of_N 42) else mmio_pred bytes_per_word (memory_trace μ')) (* The initial demands hold over the final state *).
  Proof.
    intros μinit μhandler μft γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc steps.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _).
    iIntros (Σ' H).
    unfold own_regstore.
    cbn.
    iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmtvec & Hmcause & Hmepc & Hcurpriv & H')".
    rewrite γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc.
    iMod (femtokernel_splitMemory is_mmio with "Hmem") as "(Hinit & Hhandler & #Hfortytwo & Hadv)";
      try assumption.
    iModIntro.
    iSplitR "".
    - destruct (env.view δ).
      iApply (femtokernel_init_safe is_mmio).

      Local Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
      repeat iDestruct "H'" as "(? & H')".  iFrame "∗ #".
      rewrite Model.RiscvPmpModel2.gprs_equiv. cbn.
      repeat (iRename select (_ ↦ _)%I into "Hp";
              iPoseProof (bi.exist_intro with "Hp") as "?").
      now iFrame.
    - iIntros "Hmem".
      (* Prove that this predicate follows from the invariants in both cases *)
      destruct (negb is_mmio).
      + iInv "Hfortytwo" as ">Hptsto" "_".
        iDestruct (interp_ptstomem_valid with "Hmem Hptsto") as "$".
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
      + iInv "Hfortytwo" as (t) ">[Hfrag %Hpred]" "_".
        iDestruct "Hmem" as "(%memmap & Hinv & %link & Htr)".
        iDestruct (trace.trace_full_frag_eq with "Htr Hfrag") as "->".
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
  Qed.

(* Print Assumptions femtokernel_endToEnd. *)

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
