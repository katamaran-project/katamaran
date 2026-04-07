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
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.PartialVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.trace
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

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.tactics.

  Import MicroSail.ShallowExecutor.

  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstancePredicates.
  Import RiscvPmpBlockVerifIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.


  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Import TermNotations.

    Open Scope hex_Z_scope.

    (* FIXED ADDRESSES *)
    (* The first address that is no longer used by the adversary, and hence the address at which the PMP entries should stop granting permission. Note that this address is currently also the first MMIO address. *)
    Definition adv_addr_end : N := maxAddr. (* Change once adversary gets access to MMIO*)
    (* Address where we will write in MMIO memory, and proof that our writes will indeed be within the MMIO region*)
    Definition mmio_write_addr : N := mmioStartAddr.

    Lemma write_word_is_MMIO: withinMMIO (bv.of_N mmio_write_addr) bytes_per_word.
    Proof.
      (* Avoid compute in case the list of MMIO addresses ever becomes longer *)
      repeat split; cbn; unfold mmioAddrs;
      eassert (mmioLenAddr = _) as -> by now compute. (* Get actual length so we can use successors *)
      all: apply bv.in_seqBv; now compute.
    Qed.

    (* Aliases for registers *)
    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition t0 : RegIdx := [bv 5].
    Definition t1 : RegIdx := [bv 6].
    Definition t2 : RegIdx := [bv 7].

    Definition pure_privilege_to_bits {n} : Privilege -> bv n :=
      fun p => match p with | Machine => bv.of_N 3 | User => bv.zero end.

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
        if bv.eqb hi (bv.ones 20) then (lo , hi) (* Small negative numbers *)
        else if (bv.msb lo) (* Avoid incorrect sign-extension *)
             then (bv.of_Z (Z.of_N (bv.bin lo) - 4096), (hi + bv.one)%bv)
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
            (match extract_AST hd' with
            | Some _ => (cur_off + N.of_nat xlenbytes)%N
            | _ => cur_off
            end) in
              cons hd' (resolve_ASM tl new_off)
       end.
    (* Init code is the same in both versions of the femtokernel, since MMIO memory is placed after the adversary code, hence not affecting initialization *)
    Example femtokernel_init_asm (handler_start : N) (adv_start : N) : list ASM :=
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
        ; ITYPE [bv 0x80] zero ra RISCV_ADDI
        ; CSR MStatus ra zero false CSRRW
        ; MRET
      ].

    Example femtokernel_init' (init_start : N) (handler_start : N) (adv_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_init_asm handler_start adv_start) init_start.

    Example femtokernel_mmio_handler_asm_block0 (mmio_handler_start_block2 : N) (data_start : N) : list ASM :=
      [
        UTYPE bv.zero t1 RISCV_AUIPC
        ; Λ current_pc, LOAD (bv.of_N (data_start - (current_pc - 4))) t1 t1 true WORD (* t1 <- data *)
        ; ITYPE bv.one t1 t1 RISCV_ANDI (* t1 <- mask t1 *) (* Todo: Maybe remove this line, and add a condition to the precondition. *)
        ; ITYPE bv.one t0 t2 RISCV_ANDI (* t2 <- mask t0 *)
        ; Λ current_pc, BTYPE (bv.of_N (mmio_handler_start_block2 - current_pc)) t1 t2 RISCV_BEQ (* branch if t1 = t2 *)
      ].

    Example femtokernel_mmio_handler_block0' (handler_start mmio_handler_start_block2 : N) (data_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block0 mmio_handler_start_block2 data_start) handler_start.


    Example femtokernel_mmio_handler_asm_block1 (data_start : N) : list ASM :=
      [
        ITYPE (bv.of_N mmio_write_addr) zero ra RISCV_ADDI (* works because mmio_write_addr fits into 12 bits. *)
        ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero;  exp_val ty_regno t0]%env (* TODO: notation to avoid lemma call copying LOAD instruction/internalize immediate as well?*)
        ; STORE bv.zero t0 ra WORD
        ; ITYPE bv.zero zero ra RISCV_ADDI    (* ra <- 0 *)
        ; UTYPE (bv.drop 12 (bv.of_N data_start)) ra RISCV_LUI   (* load upper 20 bits of data_start *)
        ; ITYPE (@bv.take 12 xlenbits (bv.of_N data_start)) ra ra RISCV_ADDI    (* load lower 12 bits of data_start *)
        ; STORE bv.zero t0 ra WORD
      ].

    Example femtokernel_mmio_handler_block1' (handler_start: N) (data_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block1 data_start) handler_start.

    Example femtokernel_mmio_handler_asm_block2 : list ASM :=
      [
         MRET
      ].

    Example femtokernel_mmio_handler_block2' (handler_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block2) handler_start.

    (* SIZES *)
    Definition instruction_size : N := N.of_nat bytes_per_instr.

    Definition init_size : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_init' 0 0 0))) * 4.

    Definition mmio_handler_size_block0 : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_mmio_handler_block0' 0 0 0))) * instruction_size.
    Definition mmio_handler_size_block1 : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_mmio_handler_block1' 0 0))) * instruction_size.
    Definition mmio_handler_size_block2 : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_mmio_handler_block2' 0))) * instruction_size.
    Definition mmio_handler_size : N := mmio_handler_size_block0 + mmio_handler_size_block1 + mmio_handler_size_block2.

    Definition data_size : N := 4.

    (* ADDRESSES *)
    Definition init_addr     : N := 0.
    Definition handler_addr  : N := init_addr + init_size.
    Definition mmio_handler_addr_block0  : N := handler_addr.
    Definition mmio_handler_addr_block1 : N := mmio_handler_addr_block0 + mmio_handler_size_block0.
    Definition mmio_handler_addr_block2 : N := mmio_handler_addr_block1 + mmio_handler_size_block1.
    Definition data_addr     : N := handler_addr + mmio_handler_size.
    Definition adv_addr      : N := data_addr + data_size.

    Compute femto_pmpcfg_ent0.
    Compute data_addr.
    Compute adv_addr.
    Compute mmioStartAddr.

    (* CODE AND CONFIG SHORTANDS *)
    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
    (* Shorthand for the pmp entries in both Katamaran and Iris *)
    Local Notation asn_femto_pmpentries a :=
      ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
        (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)))])%list.
    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end)]%list.

    (* Definition of the femtokernel initialization procedure. *)
    (* Note that the addresses we supply assume a base address of 0. The code however uses relative addresses and could be placed elsewhere in memory. *)
    Definition femtokernel_init_gen := femtokernel_init' init_addr handler_addr adv_addr.

    Definition femtokernel_mmio_handler_block0 := femtokernel_mmio_handler_block0' mmio_handler_addr_block0.
    Definition femtokernel_mmio_handler_block1 := femtokernel_mmio_handler_block1' mmio_handler_addr_block1.
    Definition femtokernel_mmio_handler_block2 := femtokernel_mmio_handler_block2' mmio_handler_addr_block2.
    (* We reflect the booleans present in the contracts, but now at the meta level. This allows us to recycle large parts of the Katamaran and Iris contracts as part of the verification. *)
    Definition femtokernel_handler_gen_block0 := femtokernel_mmio_handler_block0.
    Definition femtokernel_handler_gen_block1 := femtokernel_mmio_handler_block1.
    Definition femtokernel_handler_gen_block2 := femtokernel_mmio_handler_block2.

    Import asn.notations.
    Import RiscvPmp.Sig.
    (* Fix word length at 4 for this example, as we do not perform any other writes*)
    Local Notation asn_mmio_trace_state_inv := (asn.chunk (chunk_user (mmio_state_trace bytes_per_word) [env])).
    Local Notation asn_mmio_state_pred s := (asn.chunk (chunk_user (mmio_state bytes_per_word) [s])).

    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Example femtokernel_init_pre : Assertion ["a"::ty_xlenbits] :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      (∃ "v" , mscratch ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∅ ∗
      asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                  (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])
    .

    Import TermNotations.

    Example femtokernel_init_post: Assertion  ["a"::ty_xlenbits; ("an"::ty_xlenbits)] :=
      (
        (term_var "an" = term_var "a" +ᵇ (term_val ty_xlenbits (bv.of_N adv_addr)))%asn ∗
          (mtvec ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_addr)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
          (mepc ↦ term_var "an") ∗
          (∃ "v" , mscratch ↦ term_var "v") ∗
          mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool true; term_val ty.bool true ] ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          asn_regs_ptsto ∅ ∗
          asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a")))
      ).


    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__femtoinit : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition femtokernel_init_pre femtokernel_init_gen femtokernel_init_post wnil).
    Definition vc__femtoinit_unq : 𝕊 [] :=
      Postprocessing.unquantify vc__femtoinit.

    (* NOTE: For now this proof covers both the MMIO and non-MMIO Femtokernel variants, since the start of the adversary region is the same in both cases.
       If this were not the case, we would take a naive approach to verifying both versions of the initialization code here; we would require that `adv_start` takes one of the two values present in the two versions of the initialization code.
       A more general approach would verify the contract under a logical value for `adv_start`.
       This would require the block verifier to support taking a list of instructions that can depend on symbolic values as input (i.e. proper terms).
     *)

    Lemma sat__femtoinit : safeE vc__femtoinit.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* NOTE: in one case the handler reads (legacy) and in the other it writes (mmio). However, this does not have an impact on the shape of the contract, as we do not directly talk about the written/read value *)

    Example femtokernel_handler_pre : Assertion ["a" :: ty_xlenbits] :=
      (term_var "a" = term_val ty_word (bv.of_N handler_addr)) ∗
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
      (∃ "mie", mie ↦ term_var "mie") ∗
      (∃ "mip", mip ↦ term_var "mip") ∗
      (∃ "ms" , mscratch ↦ term_var "ms") ∗
      (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
      (∃ "cause", mcause ↦ term_var "cause") ∗
      (∃ "epc", mepc ↦ term_var "epc") ∗
      asn_regs_ptsto ∅ ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_addr)))) ∗ (* Different handler sizes cause different entries *)
      (∃ "oldvalue",  ∃ "s", (
          term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_size) ↦ₘ (term_var "oldvalue")
          ∗ (term_unop (uop.bvtake 1) (term_var "oldvalue") = term_var "s")
          ∗ asn_mmio_state_pred (term_var "s")
      ))
      ∗ asn_mmio_trace_state_inv.

    Example femtokernel_handler_post_block0 : Assertion ["a" :: ty_xlenbits; "an"::ty_xlenbits] :=
      (term_var "a" = term_val ty_word (bv.of_N handler_addr)) ∗
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
      (∃ "mie", mie ↦ term_var "mie") ∗
      (∃ "mip", mip ↦ term_var "mip") ∗
      (∃ "ms" , mscratch ↦ term_var "ms") ∗
      (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
      (∃ "cause", mcause ↦ term_var "cause") ∗
      (∃ "epc", mepc ↦ term_var "epc") ∗
      asn_regs_ptsto (gset_singleton x5) ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_addr)))) ∗ (* Different handler sizes cause different entries *)
      (∃ "oldvalue", ∃ "newvalue", ∃ "s", ∃ "s'",
          ((asn.chunk (chunk_ptsreg x5 (term_var "newvalue")))
           ∗ (term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_size)) ↦ₘ (term_var "oldvalue")
           ∗ (term_unop (uop.bvtake 1) (term_var "oldvalue") = term_var "s")
           ∗ asn_mmio_state_pred (term_var "s")
           ∗ (asn.or
             (
               (asn.formula (formula_user (mmio_state_prot bytes_per_word) [term_var "newvalue"; term_var "s"; term_var "s'"]))
              ∗ (term_unop (uop.bvtake 1) (term_var "newvalue") = term_var "s'")
              ∗ (term_var "an" = term_val ty_word (bv.of_N mmio_handler_addr_block1))
             )
             (
               (term_var "an" = term_val ty_word (bv.of_N mmio_handler_addr_block2))
             )
          ))
      ) ∗
      asn_mmio_trace_state_inv.

  Example femtokernel_handler_pre_block1 : Assertion ["a" :: ty_xlenbits] :=
    (term_var "a" = term_val ty_word (bv.of_N mmio_handler_addr_block1)) ∗
    (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
    (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
    (∃ "mie", mie ↦ term_var "mie") ∗
    (∃ "mip", mip ↦ term_var "mip") ∗
    (∃ "ms" , mscratch ↦ term_var "ms") ∗
    (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
    (∃ "cause", mcause ↦ term_var "cause") ∗
    (∃ "epc", mepc ↦ term_var "epc") ∗
    asn_regs_ptsto (gset_singleton x5) ∗
    cur_privilege ↦ term_val ty_privilege Machine ∗
    asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_addr_block1)))) ∗
    (∃ "newvalue", ∃ "oldvalue", ∃ "s",
        (
            (asn.chunk (chunk_ptsreg x5 (term_var "newvalue"))) (* new value in t0 *)
          ∗ (term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (mmio_handler_size_block1 + mmio_handler_size_block2))) ↦ₘ (term_var "oldvalue") (* old value in memory *)
          ∗ (asn_mmio_state_pred (term_var "s")) (* we have ownership of current state s *)
          ∗ (term_unop (uop.bvtake 1) (term_var "oldvalue") = term_var "s") (* the last bit of old value corresponds to our current state *)

          ∗ (∃ "s'", (asn.formula (formula_user (mmio_state_prot bytes_per_word) [term_var "newvalue"; term_var "s"; term_var "s'"]) ∗
                     (term_unop (uop.bvtake 1) (term_var "newvalue") = term_var "s'"))
            ) (* there exists a target state s' that satisfies mmio_state_prot when writing newvalue at our current state s *)
        )
    ) ∗
    asn_mmio_trace_state_inv.

  Example femtokernel_handler_post_block1 : Assertion ["a" :: ty_xlenbits; "an"::ty_xlenbits] :=
    (term_var "a" = term_val ty_word (bv.of_N mmio_handler_addr_block1)) ∗
    (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
    (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
    (∃ "mie", mie ↦ term_var "mie") ∗
    (∃ "mip", mip ↦ term_var "mip") ∗
    (∃ "ms" , mscratch ↦ term_var "ms") ∗
    (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
    (∃ "cause", mcause ↦ term_var "cause") ∗
    (∃ "epc", mepc ↦ term_var "epc") ∗
    (term_var "an" = term_val ty_word (bv.of_N mmio_handler_addr_block2)) ∗
    asn_regs_ptsto (gset_singleton x5) ∗
    cur_privilege ↦ term_val ty_privilege Machine ∗
    asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_addr_block1)))) ∗
    (∃ "newvalue", ∃ "s'",
        (
          (asn.chunk (chunk_ptsreg x5 (term_var "newvalue"))) (* new value in t0 *)
          ∗ (term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (mmio_handler_size_block1 + mmio_handler_size_block2)) ↦ₘ (term_var "newvalue")) (* new value in memory *)
          ∗ (asn_mmio_state_pred (term_var "s'")) (* we have ownership of current state s' *)
          ∗ (term_unop (uop.bvtake 1) (term_var "newvalue") = term_var "s'") (* the last bit of new value corresponds to the current state s' *)
        )
    ) ∗
    asn_mmio_trace_state_inv.

  Example femtokernel_handler_pre_block2 : Assertion ["a" :: ty_xlenbits] :=
    (term_var "a" = term_val ty_word (bv.of_N mmio_handler_addr_block2)) ∗
    (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
    (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
    (∃ "mie", mie ↦ term_var "mie") ∗
    (∃ "mip", mip ↦ term_var "mip") ∗
    (∃ "ms" , mscratch ↦ term_var "ms") ∗
    (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
    (∃ "cause", mcause ↦ term_var "cause") ∗
    (∃ "epc", mepc ↦ term_var "epc") ∗
    asn_regs_ptsto ∅ ∗
    cur_privilege ↦ term_val ty_privilege Machine ∗
    asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_addr_block2)))) ∗
    (∃ "somevalue",  ∃ "s", (
        term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_size_block2) ↦ₘ (term_var "somevalue") ∗
        (term_unop (uop.bvtake 1) (term_var "somevalue") = term_var "s") ∗
        asn_mmio_state_pred (term_var "s")
    )) ∗
    asn_mmio_trace_state_inv.

  Example femtokernel_handler_post : Assertion ["a" :: ty_xlenbits; "an"::ty_xlenbits] :=
    (term_var "a" = term_val ty_word (bv.of_N mmio_handler_addr_block2)) ∗
    (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
    (∃ "mie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool true; term_var "mie" ]) ∗
    (∃ "mie", mie ↦ term_var "mie") ∗
    (∃ "mip", mip ↦ term_var "mip") ∗
    (∃ "ms" , mscratch ↦ term_var "ms") ∗
    (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
    (∃ "cause", mcause ↦ term_var "cause") ∗
    (mepc ↦ term_var "an") ∗
    asn_regs_ptsto ∅ ∗
    cur_privilege ↦ term_val ty_privilege User ∗
    asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_addr_block2)))) ∗
    (∃ "somevalue",  ∃ "s", (
        term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N mmio_handler_size_block2) ↦ₘ (term_var "somevalue") ∗
        (term_unop (uop.bvtake 1) (term_var "somevalue") = term_var "s") ∗
        asn_mmio_state_pred (term_var "s")
    )) ∗
    asn_mmio_trace_state_inv.

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

    (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
    (* let vc2 := Postprocessing.prune vc1 in *)
    (* let vc3 := Postprocessing.solve_evars vc2 in *)
    (* let vc4 := Postprocessing.solve_uvars vc3 in *)
    (* let vc5 := Postprocessing.prune vc4 in *)
    (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in vc__femtohandler. *)


    Definition vc__femtohandler_block0 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     (femtokernel_handler_pre)
                     (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr)
                     (femtokernel_handler_post_block0) wnil).

    Definition vc__femtohandler_block1 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     (femtokernel_handler_pre_block1)
                     (femtokernel_handler_gen_block1 data_addr)
                     (femtokernel_handler_post_block1) wnil).

    Definition vc__femtohandler_block2 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     (femtokernel_handler_pre_block2)
                     (femtokernel_handler_gen_block2)
                     (femtokernel_handler_post) wnil).

Import Erasure.notations.
(* Eval vm_compute in Erasure.erase_symprop vc__femtohandler_block0. *)
(* Locate erase_symprop. *)

Import Erasure.notations.

   (* Prove that the verification condition that Katamaran creates for this block holds.
       I.e. we're just proving the verification condition for block0. *)
    Import Erasure.notations.
    Lemma sat__femtohandler_block0 : safeE (vc__femtohandler_block0).
    Proof.
      vm_compute.
      constructor; cbn. intros _ v0 v1.
      split; intros; auto.
      destruct (bv.view v0). destruct (bv.view v1).
      change [bv [32] 0x1] with (@bv.cons 31 true bv.zero) in H.
      rewrite bv.land_cons in H.
      rewrite bv.land_cons in H.
      rewrite bv.land_zero_r in H.
      rewrite bv.land_zero_r in H.
      simpl in H.
      rewrite bv.take_cons. simpl.
      rewrite bv.take_cons. simpl.
      destruct b; destruct b0; simpl in *; try contradiction.
      1, 2:
        split; auto;
        unfold Mmio_state_prot;
        intros; simpl;

        have ->: false = negb true; by auto;
        constructor; auto; simpl; try lia;

        change [bv [32] 0x1] with (@bv.cons 31 true bv.zero);
        rewrite bv.land_cons; rewrite bv.land_zero_r; auto.
      Qed.


    (* for debugging *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in Erasure.erase_symprop vc__femtohandler_block1. *)

    Lemma sat__femtohandler_block1 : safeE (vc__femtohandler_block1).
    Proof.
      vm_compute.
      constructor; cbn. bv_solve_Ltac.solveBvManual.
       eexists. eexists.
      repeat split; eauto.
      eexists. eexists. repeat split; eauto.
      1-4: eapply bv.in_seqBv'; now vm_compute.
    Qed.

    Import Erasure.notations.

    Lemma sat__femtohandler_block2 : safeE (vc__femtohandler_block2).
    Proof.
      vm_compute.
        constructor; cbn.
        intuition;
          bv_solve_Ltac.solveBvManual.
    Qed.

  End FemtoKernel.

  (* Avoid expanding interp_ptstomem when doing simplifications *)
  Arguments interp_ptstomem : simpl never.

  Definition advAddrs : list (bv xlenbits) := bv.seqBv (bv.of_N adv_addr) (adv_addr_end - adv_addr).

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
      now cbn -[xlenbits].
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

  Lemma memAdv_pmpPolicy `{sailGS Σ, iostateG IOState Σ} :
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

  Definition femto_mmio_pred `{sailGS Σ, iostateG IOState Σ} (t : Trace) (s : IOState) := mmio_trace_state_pred t s.

  Definition femto_handler_pre `{sailGS Σ} {rG : iostateG IOState Σ} a : iProp Σ :=
    asn.interpret femtokernel_handler_pre [ a ].
  (* Eval cbn in femto_handler_pre. *)

  Definition femto_handler_post_block0 `{sailGS Σ, iostateG IOState Σ} a an : iProp Σ :=
    asn.interpret femtokernel_handler_post_block0 [].[("a"∷ty_xlenbits) ↦ a ].[("an"∷ty_xlenbits) ↦ an ].
  (* Eval cbn in fun a an => femto_handler_post_block0 a an. *)

  Definition femto_handler_block0_contract `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    semTripleAnnotatedBlock femto_handler_pre (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr) femto_handler_post_block0.

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre.

  Import env.notations.

  (* Here we're proving the same contract as we did in lemma sat_femtohandler but for Iris. *)
  Lemma femto_handler_verified_block0 `{sailGS Σ, iostateG IOState Σ} : ⊢ femto_handler_block0_contract.
  Proof.
    iIntros (a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif $! a). (* Apply soundness lemma for Katamaran *)
    exact sat__femtohandler_block0. (* Apply soundness of the block (in Katamaran) *)
  Qed.

  Transparent femtokernel_handler_pre.

  Definition femto_handler_pre_block1 `{sailGS Σ, iostateG IOState Σ} a : iProp Σ :=
    asn.interpret femtokernel_handler_pre_block1 [ a ].
  (* Eval cbn in fun a => femto_handler_pre_block1 a. *)

  Definition femto_handler_post_block1 `{sailGS Σ, iostateG IOState Σ} a an : iProp Σ :=
    asn.interpret femtokernel_handler_post_block1 [].[("a"∷ty_xlenbits) ↦ a ].[("an"∷ty_xlenbits) ↦ an ].
  (* Eval cbn in fun a an => femto_handler_post_block1 a an. *)

  Definition femto_handler_block1_contract `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    semTripleAnnotatedBlock femto_handler_pre_block1 (femtokernel_handler_gen_block1 data_addr) femto_handler_post_block1.

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre_block1.
  Import env.notations.

  Lemma femto_handler_verified_block1 `{sailGS Σ, iostateG IOState Σ} :  ⊢ femto_handler_block1_contract.
  Proof.
    iIntros (a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif $! a).
    exact sat__femtohandler_block1.
  Qed.

  Transparent femtokernel_handler_pre_block1.

  Definition femto_handler_pre_block2 `{sailGS Σ, iostateG IOState Σ} a : iProp Σ :=
    asn.interpret femtokernel_handler_pre_block2 [ a ].
  (* Eval cbn in fun a => femto_handler_pre_block2 a. *)

  Definition femto_handler_post `{sailGS Σ, iostateG IOState Σ} a an : iProp Σ :=
    asn.interpret femtokernel_handler_post [].[("a"∷ty_xlenbits) ↦ a ].[("an"∷ty_xlenbits) ↦ an ].
  (* Eval cbn in fun a an => femto_handler_post a an. *)

  Definition femto_handler_block2_contract `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    semTripleAnnotatedBlock femto_handler_pre_block2 (femtokernel_handler_gen_block2) (femto_handler_post).

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre_block2.
  Import env.notations.

  Lemma femto_handler_verified_block2 `{sailGS Σ, iostateG IOState Σ} : ⊢ femto_handler_block2_contract.
  Proof.
    iIntros (a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif $! a).
    exact sat__femtohandler_block2.
  Qed.

  Transparent femtokernel_handler_pre_block2.
  Opaque interp_pmp_entries.

  (* Needed when introducing the below conditional *)
  Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B).
  Proof. destruct b; apply _. Qed.

  Definition femtoKernelAssumptions  `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
    blockVerifierAssumptions a ∗
    interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User ∗
    (* TODO: Remove ownership of init instructions *)
    ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST (femtokernel_init_gen)) ∗
    ptsto_instrs (bv.of_N mmio_handler_addr_block0) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr)) ∗
    ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr)) ∗
    ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2)).

  Definition femtoInitAssumptions `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
    blockVerifierAssumptions a ∗
      ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST (femtokernel_init_gen)) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr)) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr)) ∗
      ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2)).


  Opaque ptsto_instrs.
  Opaque femtokernel_init_gen.
  Opaque femtokernel_handler_gen_block0.
  Opaque femtokernel_handler_gen_block1.
  Opaque femtokernel_handler_gen_block2.

  Lemma femtokernel_handler_safe_block2 `{sailGS Σ, iostateG IOState Σ} a :
    ⊢ ▷ (femtoKernelAssumptions (bv.of_N handler_addr) ∗ femto_handler_pre (bv.of_N handler_addr) -∗ WP_loop) -∗ (* Tut: Assuming handler invocation is safe, and... *)
      femtoKernelAssumptions a ∗ femto_handler_pre_block2 a -∗
        WP_loop. (* then block2 is safe *)
  Proof.
    iIntros "IH (Hfemto & Hpre)".
    iAssert (⌜bv.of_N mmio_handler_addr_block2 = a⌝)%I as %Heqa.
    { iClear "IH Hfemto". cbn.
      by iDestruct "Hpre" as "([%Ha0 _] & _)".
    }
    subst.
    iDestruct "Hfemto" as "(Hblock & HaccU & Hinstrs & Hinstrs0 & Hinstrs1 & Hinstrs2)".
    iApply (femto_handler_verified_block2 with "[$Hpre $Hblock $Hinstrs2]").
    iIntros (an) "(Hblockver & Hinstrs2 & Hpost)".
    (* We have reached the end of block2 where the handler jumps back to the
       adversary in User mode. Use the universal contract to show that
       invoking the adversary is safe. *)
    iPoseProof (LoopVerification.valid_semTriple_loop with "[IH Hblockver Hpost HaccU Hinstrs Hinstrs0 Hinstrs1 Hinstrs2]") as "H".
    { (* Prove the precondition of the universal contract. *)
      rewrite /LoopVerification.loop_pre /LoopVerification.Step_pre.
      cbn - [femto_handler_pre].
      iDestruct "Hpost" as "([%Ha2 _] & _ & [%mpie Hmstatus] & Hmie & Hmip & Hmscratch & Hmtvec & Hmcause & Hmepc & Hgprs & Hcurpriv & Hpmpentries & Hpred & Hinv)".
      iSplitL "Hcurpriv Hmtvec Hblockver Hmcause Hmip Hmie Hmscratch Hmepc Hmstatus Hpmpentries HaccU Hgprs".
      { iDestruct "Hblockver" as "(Hpc & %npc & Hnpc)".
        iFrame "Hcurpriv Hmtvec Hpc Hnpc Hmcause Hmip Hmie Hmscratch Hmepc Hmstatus Hpmpentries HaccU".
        by iApply gprs_equiv.
      }
      (* Prove that the adversary cannot modify CSRs. *)
      iSplitR.
      { iModIntro.
        unfold LoopVerification.CSRMod.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.
      }
      (* Prove that it is safe for the adversary to invoke the interrupt handler. *)
      iSplitL "IH Hinstrs Hinstrs0 Hinstrs1 Hinstrs2 Hpred Hinv".
      { iModIntro.
        iIntros "(HaccU & Hgprs & Hpmpentries & Hmcause & Hmip & Hmie & Hmscratch & Hcurpriv & Hnpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
        iApply "IH".
        iSplitL "Hpc Hnpc HaccU Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
        { iFrame. }
        cbn.
        iSplitR. iSplit; auto.
        iSplitR. iSplit; auto.
        rewrite <- gprs_equiv.
        iFrame "Hmstatus Hmie Hmip Hmscratch Hmtvec Hmcause Hmepc Hgprs Hcurpriv Hpmpentries Hpred Hinv".
      }
      (* Prove that the adversary cannot MRET. *)
      { iModIntro.
        unfold LoopVerification.Recover.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.
      }
    }
    (* Prove that we can derive safety from the universal contract's post condition.  *)
    unfold WP_loop.
    iApply (semWP_mono with "H"). auto.
  Qed.

  Lemma femtokernel_handler_safe_block1 `{sailGS Σ, iostateG IOState Σ} a :
    ⊢ ▷ (femtoKernelAssumptions (bv.of_N handler_addr) ∗ femto_handler_pre (bv.of_N handler_addr) -∗ WP_loop) -∗
      femtoKernelAssumptions a ∗ femto_handler_pre_block1 a -∗
      WP_loop.
  Proof.
    iIntros "IH ((Hblockver & HaccU & Hinstrs & Hinstrs0 & Hinstrs1 & Hinstrs2) & Hpre)".
    iAssert (⌜bv.of_N mmio_handler_addr_block1 = a⌝)%I as %Heqa.
    { cbn. by iDestruct "Hpre" as "([%Ha0 _] & _)". }
    subst.
    iApply (femto_handler_verified_block1 with "[Hblockver Hpre Hinstrs1]").
    { iFrame "Hpre Hblockver Hinstrs1". }
    iIntros (an) "(Hblockver & Hinstrs1 & Hpost)".
    iApply (femtokernel_handler_safe_block2 with "[$IH]").
    iSplitL "Hblockver HaccU Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
    { iFrame. }
    cbn.
    iDestruct "Hpost" as "(_ & [%Han _] & Hmstatus & Hmie & Hmip & Hmscratch & Hmtvec & Hmcause & Hmepc & [%Han2 _] & Hgprs & Hcurpriv & Hpmpentries & Hpred & Hinv)".
    iSplitR. iSplit; auto.
    iSplitR. subst. iSplit; auto.
    iFrame "Hmstatus Hmie Hmip Hmscratch Hmtvec Hmcause Hmepc".
    iDestruct "Hpred" as "(%v & %s & Hx5 & Hmem & Hstate)".
    iSplitL "Hgprs Hx5".
    { iFrame. }
    subst.
    iFrame "Hcurpriv Hpmpentries Hmem".
    iDestruct "Hstate" as "[Hstate Hprot]". iFrame.
  Qed.

  Lemma femtokernel_handler_safe_block0 `{sailGS Σ, iostateG IOState Σ} a :
    ⊢ femtoKernelAssumptions a ∗ femto_handler_pre a -∗
      WP_loop.
  Proof.
    iLöb as "Hind".
    iIntros "(Hfemto & Hpre)".
    iAssert (⌜bv.of_N mmio_handler_addr_block0 = a⌝)%I as %Heqa.
    { cbn. by iDestruct "Hpre" as "([%Ha0 _] & _)". }
    subst.
    iDestruct "Hfemto" as "(Hblockver & HaccU & Hinstrs & Hinstrs0 & Hinstrs1 & Hinstrs2)".
    iApply (femto_handler_verified_block0 with "[$Hpre $Hblockver $Hinstrs0]").
    iIntros "%an (Hblockver & Hinstrs0 & Hpost0)".
    cbn - [femto_handler_pre].
    iDestruct "Hpost0" as "(_ & _ & Hmstatus & Hmie & Hmip & Hmscratch & Hmtvec & Hmcause & Hmepc & Hgprs & Hcurpriv & Hpmpentries & Hpred)".
    iDestruct "Hpred" as "((%vold & %vnew & %s & %s' & Hx5 & Hold & [#Hpold _] & Hstate & Hpred ) & #Hinv)".
    (* Tut: We destruct over the two cases even / odd number in t0 *)
    iDestruct "Hpred" as "[HpredL | HpredR]".
    - (* Tut: Case legal value i.e. we do not jump and therefore enter block1 *)
      iApply (femtokernel_handler_safe_block1 with "[]").
      + (* TODO: Fixme *)
        unfold mmio_handler_addr_block0.
        iExact "Hind".
      + iSplitL "Hblockver HaccU Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
        { iFrame. }
        cbn - [femto_handler_pre].
        iDestruct "HpredL" as "([%s_prot _] & [%Hprot _] & [%Han _])".
        subst.
        iSplitR; auto. iSplitR; auto.
        iFrame "Hmstatus Hmie Hmip Hmscratch Hmtvec Hmcause Hmepc Hgprs Hcurpriv Hpmpentries Hx5 Hold Hstate Hpold Hinv".
        iExists (bv.take 1 vnew). auto.
    - (* Tut: Case illegal value i.e. we jump and therefore enter block2 *)
      iApply (femtokernel_handler_safe_block2 with "[]").
      + (* TODO: Fixme2 *)
        unfold mmio_handler_addr_block0.
        iExact "Hind".
      + iSplitL "Hblockver HaccU Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
        { iFrame. }
        cbn - [femto_handler_pre].
        iDestruct "HpredR" as "[%Han _]".
        subst.
        iSplitR; auto. iSplitR; auto.
        iFrame "Hmstatus Hmie Hmip Hmscratch Hmtvec Hmcause Hmepc".
        iSplitL "Hgprs Hx5".
        { iFrame. }
        iFrame "Hcurpriv Hpmpentries Hold Hpold Hstate Hinv".
  Qed.

  (* TODO: this lemma feels very incremental wrt to the last one; merge? *)
  Lemma femtokernel_manualStep2 `{sailGS Σ, iostateG IOState Σ} :
    ⊢ femtoInitAssumptions (bv.of_N adv_addr) ∗
      femto_handler_post (bv.of_N mmio_handler_addr_block2) (bv.of_N adv_addr) ∗
       ptstoSthL advAddrs  (* Tut: we give up exclusive ownership of adv memory ONLY (notably not the mmio-trace and private state for handler and init) *)
        ={⊤}=∗
        ∃ mpp, LoopVerification.loop_pre User (bv.of_N handler_addr) (bv.of_N adv_addr) mpp femto_pmpentries.
       (* Tut: All preconditions for invoking the (universal) contract for the adversary holds *)
       (* The contract that states, adv has power according to pmp-policy*)
  Proof.
    iIntros "(Hfemto & Hpost & Hmemadv)".
    iDestruct "Hfemto" as "(Hblockver & Hinstrs & Hinstrs0 & Hinstrs1 & Hinstrs2)".

    iExists User.
    iModIntro.
    rewrite /LoopVerification.loop_pre /LoopVerification.Step_pre.
    cbn.
    iDestruct "Hpost" as "([%Ha2 _] & _ & [%mpie Hmstatus] & Hmie & Hmip & Hmscratch & Hmtvec & Hmcause & Hmepc & Hgprs & Hcurpriv & Hpmpentries & Hpred & #Hinv)".

    iSplitL "Hcurpriv Hmtvec Hblockver Hmcause Hmip Hmie Hmscratch Hmepc Hmstatus Hpmpentries Hmemadv Hgprs".
    { rewrite <- gprs_equiv.
      iDestruct "Hblockver" as "(Hpc & %npc & Hnpc)".
      iFrame "Hcurpriv Hmtvec Hpc Hnpc Hmcause Hmip Hmie Hmscratch Hmepc Hmstatus Hpmpentries Hgprs".
      now iApply memAdv_pmpPolicy.
    }

    iSplitR.
    { iModIntro.
      unfold LoopVerification.CSRMod.
      iIntros "(_ & _ & _ & %eq & _)".
      inversion eq. }

    iSplitL "Hpred Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
    {
      unfold LoopVerification.Trap.
      iModIntro.
      iIntros "(HaccU & Hgprs & Hpmpentries & Hmcause & Hmip & Hmie & Hmscratch & Hcurpriv & Hnpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
      iApply (femtokernel_handler_safe_block0 (bv.of_N handler_addr)).
      iSplitL "Hpc Hnpc HaccU Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
      { unfold femtoKernelAssumptions.
        (* TODO: Fixme3 *)
        unfold mmio_handler_addr_block0.
        iFrame.
      }
      cbn.
      iSplitR. iSplit; auto.
      iSplitR. iSplit; auto.
      rewrite <- gprs_equiv.
      iFrame "Hmstatus Hmie Hmip Hmscratch Hmtvec Hmcause Hmepc Hgprs Hcurpriv Hpmpentries Hpred Hinv".
    }
    {
      iModIntro.
      unfold LoopVerification.Recover.
      iIntros "(_ & _ & _ & %eq & _)".
      inversion eq.
    }
  Qed.


  Definition femto_init_pre `{sailGS Σ, iostateG IOState Σ} a : iProp Σ :=
    asn.interpret femtokernel_init_pre [].[("a"∷ty_xlenbits) ↦ a ].
  (* Eval cbn in fun a => femto_init_pre a. *)

  Definition femto_init_post `{sailGS Σ, iostateG IOState Σ} a an : iProp Σ :=
    asn.interpret femtokernel_init_post [].[("a"∷ty_xlenbits) ↦ a ].[("an"∷ty_xlenbits) ↦ an ].
  (* Eval cbn in fun a an => femto_init_post a an. *)

  Definition femto_init_contract `{sailGS Σ, iostateG IOState Σ} : iProp Σ :=
    semTripleAnnotatedBlock femto_init_pre (femtokernel_init_gen) femto_init_post.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.
  Transparent interp_pmp_entries.

  Local Opaque femtokernel_init_gen. (* TODO: figure out why not having this makes the below proof spin in two places *)

  Lemma femto_init_verified : forall `{sailGS Σ, iostateG IOState Σ}, ⊢ femto_init_contract.
  Proof.
    iIntros (Σ sG rG a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif $! a). (* Apply soundness lemma for Katamaran *)
    exact sat__femtoinit. (* Apply soundness of the block (in Katamaran) *)
  Qed.

  (* see above *)
  Transparent femtokernel_init_pre.

  Lemma femtokernel_init_safe `{sailGS Σ, iostateG IOState Σ} :
    ⊢ femtoInitAssumptions (bv.of_N init_addr) ∗
      femto_init_pre (bv.of_N init_addr) ∗
      (* interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User ∗ *)
      (∃ v, ∃ s, (@interp_ptstomem _ _ xlenbytes (bv.of_N data_addr) v) ∗
            interp_mmio_state_pred s ∗
            ⌜bv.take 1 v = s⌝
      ) ∗
      interp_mmio_trace_state_inv ∗
      ptstoSthL advAddrs -∗
      WP_loop.
  Proof.
    iIntros "(Hfemto & Hpre & Hstate & Htrace_state & Hmemadv)".
    iDestruct "Hfemto" as "(Hblockver & Hinstrs & Hinstrs0 & Hinstrs1 & Hinstrs2)".
    iApply (femto_init_verified with "[$Hpre $Hblockver $Hinstrs]").
    iIntros (an) "(Hblockver & Hinstrs & Hpost)".

    iAssert (⌜bv.of_N adv_addr = an⌝)%I as %Heqan.
    { by iDestruct "Hpost" as "([%Han _] & _)". }
    subst.

    iApply fupd_wp.
    iMod (femtokernel_manualStep2 with "[Hblockver Hinstrs Hinstrs0 Hinstrs1 Hinstrs2 Hmemadv Hpost Hstate Htrace_state]") as "[%mpp Hlooppre]".
    { iSplitL "Hblockver Hinstrs Hinstrs0 Hinstrs1 Hinstrs2".
      iFrame.
      iSplitR "Hmemadv"; [| iFrame].
      cbn.
      iSplitR. iSplit; auto.
      iSplitR. iSplit; auto.
      iDestruct "Hpost" as "([%Han _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmscratch & Hmstatus & Hcurpriv & Hgprs & Hpmpentries)".
      iFrame "Hmstatus Hmie Hmip Hmscratch Hmtvec Hmcause Hmepc Hgprs Hcurpriv".
      iFrame "Hpmpentries".
      iDestruct "Hstate" as "(%v & %s & Hmem & Hstate & Hprot)".
      iFrame.
    }
    iPoseProof (LoopVerification.valid_semTriple_loop with "Hlooppre") as "H".
    iApply (wp_mono with "H"). auto.
Qed.

(* THIS IS WHERE EVERYTHING HAS BEEN CHECKED TO MATCH UP. *)

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
  Lemma liveAddrs_split : liveAddrs = bv.seqBv (bv.of_N init_addr) init_size ++
                                        bv.seqBv (bv.of_N handler_addr) (mmio_handler_size_block0) ++
                                        bv.seqBv (bv.of_N mmio_handler_addr_block1) (mmio_handler_size_block1) ++
                                        bv.seqBv (bv.of_N mmio_handler_addr_block2) (mmio_handler_size_block2) ++
                                       (bv.seqBv (bv.of_N data_addr) data_size (* There is no data; conjunct is just here for conformity *)) ++ advAddrs.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma intro_ptstomem_word `{sailGS Σ, iostateG IOState Σ} v0 v1 v2 v3 (a : Val ty_word) :
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

  Lemma intro_ptstomem_word2 `{sailGS Σ, iostateG IOState Σ} {μ : Memory} {a : Val ty_word} {v : Val ty_word} :
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

  Lemma intro_ptsto_instr `{sailGS Σ, iostateG IOState Σ} {μ : Memory} {a : Val ty_word} {instr : AST} :
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

  Lemma intro_ptsto_instrs `{sailGS Σ, iostateG IOState Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * N.of_nat (length instrs) + bv.bin a < bv.exp2 xlenbits)%N ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length instrs)), interp_ptsto a' ((memory_ram μ) a'))
      ⊢ ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - rewrite Nat2N.inj_succ in Hrep.
      fold (length instrs) in Hrep.
      replace (4 * N.of_nat (length (instr :: instrs)))%N with (4 + 4 * N.of_nat (length instrs))%N by (cbn; lia).
      rewrite bv.seqBv_app; try (cbn -[N.of_nat N.mul] in *; Lia.lia).
      rewrite big_opL_app.
      destruct Hmeminstrs as [Hinstr Hmeminstrs].
      iDestruct "Hmem" as "[Hmema Hmema4]".
      cbv [ptsto_instrs].
      iSplitL "Hmema".
      + iApply (intro_ptsto_instr with "Hmema"); auto; Lia.lia.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply ("IH" with "[%] [% //] [-]").
        * rewrite bv.bin_add_small;
          cbn -[N.mul] in *;
          now Lia.lia.
        * now rewrite ?bv.add_assoc.
  Qed.

  Lemma intro_ptstoSthL `{sailGS Σ, iostateG IOState Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, interp_ptsto a' ((memory_ram μ) a')) ⊢ ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists ((memory_ram μ) a).
      + now iApply IHl.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto {Σ : gFunctors} {sG : sailGS Σ} {rG : iostateG IOState Σ} {s e} (μ : Memory):
    (minAddr <= bv.bin s)%N → (bv.bin s + e <= minAddr + lenAddr)%N →
    ([∗ list] y ∈ bv.seqBv s e, gen_heap.pointsto y (dfrac.DfracOwn 1) (memory_ram μ y)) ⊢ [∗ list] a' ∈ bv.seqBv s e, interp_ptsto a' (memory_ram μ a').
  Proof.
    iIntros (Hlow Hhi) "Hlist".
    iApply (big_sepL_mono with "Hlist"). intros ? ? Hsom. cbn.
    iIntros "$". iPureIntro.
    rewrite /= /not; apply mmio_ram_False.
    apply elem_of_list_lookup_2 in Hsom.
    refine (bv.seqBv_sub_elem_of _ _ Hsom).
    - solve_bv.
    - rewrite bv.bin_of_N_small; last apply minAddr_rep. lia.
  Qed.

  Lemma femtokernel_splitMemory `{sailGS Σ, iostate_preG IOState Σ} {μ : Memory} {s} {v} :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2)) ->
    mmio_trace_state_pred (memory_trace μ) s -> (* Demand a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    mem_has_word μ (bv.of_N data_addr) v ->
    @mem_res _ sailGS_memGS μ ⊢ |={⊤}=>
          ∃ (rG : iostateG IOState Σ),
          ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
          ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr)) ∗
          ptsto_instrs (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr)) ∗
          ptsto_instrs (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2)) ∗
          interp_mmio_trace_state_inv ∗
          (@interp_ptstomem _ _ xlenbytes (bv.of_N data_addr) v) ∗
          (interp_mmio_state_pred (bv_to s)) ∗
          ptstoSthL advAddrs.
  Proof.
    iIntros (Hinit Hhandler0 Hhandler1 Hhandler2 Hpred Hdata) "Hmres".
    unfold iost_res, mem_res, initMemMap.
    rewrite (liveAddrs_split).
    rewrite ?big_sepL_app.
    iDestruct "Hmres" as "[(Hinit & Hhandler0 & Hhandler1 & Hhandler2 & Hmem & Hadv) Htrfrag]".
    iMod (state_alloc_names s) as "(%iostate_name & Hstauth & Hstfrag)".
    pose (rG := IOStateG _ _ _ iostate_name : iostateG IOState Σ ).
    iExists rG.
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); now compute. }
    iSplitL "Hhandler0".
    { iApply (intro_ptsto_instrs (μ := μ)); auto. cbv. reflexivity.
      cbn. unfold mmio_handler_size.
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler0"); now compute. }
    iSplitL "Hhandler1".
    { iApply (intro_ptsto_instrs (μ := μ)); auto. cbv. reflexivity.
      cbn. unfold mmio_handler_size.
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler1"); now compute. }
    iSplitL "Hhandler2".
    { iApply (intro_ptsto_instrs (μ := μ)); auto. cbv. reflexivity.
      cbn. unfold mmio_handler_size.
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler2"); now compute. }
    iSplitL "Htrfrag Hstauth".
    {  unfold femto_mmio_pred. unfold interp_mmio_trace_state_inv.
      iMod (inv.inv_alloc femto_inv_mmio_ns ⊤ (∃ s t, tr_frag1 t ∗ st_auth1 s ∗ ⌜mmio_trace_state_pred t s⌝)%I with "[Htrfrag Hstauth]") as "Hinv".
      { iNext. iExists _, _. iFrame. auto. }
      iModIntro.
      unfold interp_mmio_state_pred.
      now iFrame. }
    iSplitL "Hmem".
    { iApply intro_ptstomem_word2; eauto.
      iApply sub_heap_mapsto_interp_ptsto; auto; by compute.  }
    iSplitL "Hstfrag".
    { destruct s; by iFrame. }
    iApply (intro_ptstoSthL μ).
    iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); now compute.
  Qed.

  Lemma interp_ptsto_valid `{sailGS Σ, iostateG IOState Σ} {μ a v} :
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
  Lemma interp_ptstomem_valid `{sailGS Σ, iostateG IOState Σ} {μ a v} :
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
    change 4%N with (N.succ (N.succ (N.succ (N.succ N.zero)))).
    rewrite !bv.seqBv_succ !map_cons.
    repeat f_equal; auto.
  Qed.

  Transparent ptsto_instrs.
  Opaque gprs_equiv.

  Lemma femtokernel_endToEnd  {γ γ' : RegStore} {μ μ' : Memory} {σ : IOState}
    {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_addr) (filter_AnnotInstr_AST (femtokernel_handler_gen_block0 mmio_handler_addr_block2 data_addr)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block1) (filter_AnnotInstr_AST (femtokernel_handler_gen_block1 data_addr)) ->
    mem_has_instrs μ (bv.of_N mmio_handler_addr_block2) (filter_AnnotInstr_AST (femtokernel_handler_gen_block2)) ->
    mmio_trace_state_pred (memory_trace μ) σ -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    read_register γ cur_privilege = Machine ->
    read_register γ mstatus = {| MPP := User; MPIE := false;  MIE := false |} ->
    read_register γ pmp0cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr0 = bv.zero ->
    read_register γ pmp1cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr1 = bv.zero ->
    read_register γ pc = (bv.of_N init_addr) ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    mem_has_word μ (bv.of_N data_addr) (if σ then bv.one else bv.zero) ->
    (∃ σ', mmio_trace_state_pred (memory_trace μ') σ'). (* The initial demands hold over the final state *)
  Proof.
    intros μinit μhandler0 μhandler1 μhandler2 μft γcurpriv γmstatus γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc steps Hmem.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _). (* inv trace satisfies protocol state *)
    iIntros (Σ' sG mpG).
    cbn.
    iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmie & Hmip & Hmtvec & Hmscratch & Hmepc & Hmcause & Hcurpriv & H')".
    rewrite γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc γmstatus.
    iMod (femtokernel_splitMemory with "Hmem") as "(%rG & Hinit & Hhandler0 & Hhandler1 & Hhandler2 & #Hinv & Hdata & Hstate & Hadv)"; try eassumption.
    iModIntro.
    iSplitR "".
    - destruct (env.view δ).  (* INV and frag of state *)
      iApply femtokernel_init_safe.
      cbn -[femtokernel_handler_gen_block0 femtokernel_handler_gen_block1 femtokernel_handler_gen_block2].
      iSplitL "Hpc Hnpc Hinit Hhandler0 Hhandler1 Hhandler2".
      { unfold femtoInitAssumptions. iFrame "Hpc Hnpc Hinit Hhandler0 Hhandler1 Hhandler2". }
      iSplitL "Hmstatus Hmie Hmip Hmtvec Hmscratch Hmepc Hmcause Hcurpriv H'".
      { iSplitR. iSplit; auto.
        iFrame "Hmtvec Hmcause Hmip Hmie Hmepc Hmscratch Hmstatus Hcurpriv".
        match goal with
        | |- context[asn.interpret ?a ?ι] =>
            let a' := eval vm_compute in a in
              change (asn.interpret a ι) with (asn.interpret a' ι)
        end.
        cbn.
        iDestruct "H'" as "(Hx01 & Hx02 & Hx03 & Hx04 & Hx05 & Hx06 & Hx07 & Hx08 & Hx09 & H')".
        iDestruct "H'" as "(Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 & H')".
        iDestruct "H'" as "(Hx20 & Hx21 & Hx22 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 & H')".
        iDestruct "H'" as "(Hx30 & Hx31 & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1 & _)".
        iFrame "Hx25 Hx17 Hx09 Hx21 Hx29 Hx13 Hx05".
        iFrame "Hx01 Hx23 Hx31 Hx15 Hx07 Hx19 Hx27".
        iFrame "Hx11 Hx03 Hx24 Hx16 Hx08 Hx20 Hx28".
        iFrame "Hx12 Hx04 Hx22 Hx30 Hx14 Hx06 Hx18".
        iFrame "Hx26 Hx10 Hx02".
        iFrame "Hpmp0cfg Hpmpaddr0 Hpmp1cfg Hpmpaddr1".
        auto.
      }
      iFrame "∗ #".
      iPureIntro. destruct σ; auto.
   -
     iIntros "Hmem". (* INV only *)
     iInv "Hinv" as  (s'' t) ">(Htrf & Hsta & %Hpred)" "_".
     iDestruct "Hmem" as "(%memmap & Hinv2 & %link & Htra)".
     iDestruct (trace.trace_full_frag_eq with "Htra Htrf") as "->".
     iApply fupd_mask_intro; first apply empty_subseteq. iIntros "_".
     iPureIntro. now eexists s''.
Qed.

(* Print Assumptions femtokernel_endToEnd. *)

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
