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
     RiscvPmp.BlockVer.TotalVerifier
     RiscvPmp.BlockVer.BinaryVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.LoopVerificationBinary
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
  Import Assembly.


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
    Proof. apply bounds_withinMMIO; now compute. Qed.

    (* We choose a start addr from which adversary (U-mode) is allowed to
       requests writes to MMIO. Currently we only reserve the first word of
       MMIO addresses as exclusive to M-mode. *)
    Definition mmio_write_adv : N := mmioStartAddr + (N.of_nat bytes_per_word).

    Lemma write_word_adv_is_MMIO :
        withinMMIO (bv.of_N mmio_write_adv) bytes_per_word.
    Proof. apply bounds_withinMMIO; now compute. Qed.

    (* Aliases for registers *)
    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition t0 : RegIdx := [bv 5].
    Definition mmio_write_arg_reg : RegIdx := [bv 10]. (* x10 = a0 *)
    Definition mmio_write_val_reg : RegIdx := [bv 11]. (* x11 = a1 *)

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
            (match extract_AST hd' with
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
      ; ITYPE [bv 0x80] zero ra RISCV_ADDI
      ; CSR MStatus ra zero false CSRRW
      ; MRET
      ].

    Example femtokernel_init' (init_start : N) (handler_start : N) (adv_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_init_asm handler_start adv_start) init_start.

    Example femtokernel_handler_asm : list ASM :=
      [
        ITYPE (bv.of_N 42) zero t0 RISCV_ADDI
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_xlenbits (bv.of_N 42)]%env (* TODO: notation to avoid lemma call copying LOAD instruction/internalize immediate as well?*)
      ; STORE (bv.of_N mmio_write_addr) t0 zero WORD (* works because mmio_write_addr fits into 12 bits. *)
      ; MRET
      ].
    Example femtokernel_handler' (handler_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm) handler_start.

    (* The trap handler is invoked for writes to MMIO. Only M-mode can access
       the MMIO addresses directly, but we provide (the only) a syscall that
       performs writes for U-mode for certain MMIO addresses. This requires
       some extra blocks, one for the entry, in which we check that the address,
       expected as an argument in `mmio_write_arg_reg` register, is one that
       can be written to be U-mode. If so, we perform the write with the value
       from the `mmio_write_val_reg` register. If not, we perform a "secret"
       write to an MMIO address that is only accessible to M-mode.
       Finally, we return control to the invoker of the syscall. *)
    (* Block structure:
       - femtokernel_handler_entry_asm
         -> Jumps to femtokernel_handler_secret_write_asm
         -> OR falls through to femtokernel_handler_write_asm
       - femtokernel_handler_write_asm
         -> ALWAYS jumps to femtokernel_handler_exit_asm
       - femtokernel_handler_secret_write_asm
         -> ALWAYS falls through to femtokernel_exit_asm
       - femtokernel_handler_exit_asm
         -> Jumps back to U-mode (MRET). End of handler code. *)
    Example femtokernel_handler_entry_asm (handler_write_size : N) : list AnnotInstr :=
      [ ADDI t0 zero (bv.of_N mmio_write_adv)
      ; BNE mmio_write_arg_reg t0 (bv.of_N (handler_write_size + N.of_nat bytes_per_instr)) (* If the requested write argument is not one the trap invoker can write to, we need to jump over (hence the + bytes_per_instr) the handler_write block. *)
      ].

    (* Perform the requested MMIO write on behalf of U-mode.
       Arguments: write_addr in a0, write_value in a1.
       Jumps to femtokernel_handler_exit_asm at the end of the block.*)
    Example femtokernel_handler_write_asm (handler_exit_addr : N) : list AnnotInstr :=
      [ ADDI t0 zero (bv.of_N 42)
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_adv) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_xlenbits (bv.of_N 42)]%env
      ; STORE (bv.of_N mmio_write_adv) t0 zero WORD (* works because mmio_write_adv fits into 12 bits. *)
      ; RISCV_JALR (bv.of_N handler_exit_addr) zero zero (* works because we the exit block addr fits into 12 bits *)
      ].

    (* Performs a "secret" MMIO write. The secret itself is read from the
       `data` address and then written to the MMIO address.
       Block falls through to femtokernel_handler_exit_asm. *)
    Example femtokernel_handler_secret_write_asm' (data_addr : N) : list ASM :=
      [ UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
      ; AnnotLemmaInvocation (close_mmio_write_mem (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_xlenbits (bv.of_N data_addr)]%env 
      ; STORE (bv.of_N mmio_write_addr) ra zero WORD (* works because mmio_write_adv fits into 12 bits. *)
      ; ADD ra zero zero (* We need to clear ra, as it contains the secret *)
      ].
    Example femtokernel_handler_secret_write_asm (secret_write_addr data_addr : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_secret_write_asm' data_addr) secret_write_addr.

    (* Recover from the trap. *)
    Example femtokernel_handler_exit_asm : list AnnotInstr :=
      [ MRET ].

    Definition Label       : Set := string.
    Definition Block       : Set := list AnnotInstr.

    Definition init                 : Label := "init".
    Definition handler_entry        : Label := "handler_entry".
    Definition handler_write        : Label := "handler_write".
    Definition handler_secret_write : Label := "handler_secret_write".
    Definition handler_exit         : Label := "handler_exit".

    Definition femtokernel_block_layout : list (Label * Block) :=
      [ (init                 , femtokernel_init' 0 0 0)
      ; (handler_entry        , femtokernel_handler_entry_asm 0)
      ; (handler_write        , femtokernel_handler_write_asm 0)
      ; (handler_secret_write , femtokernel_handler_secret_write_asm 0 0)
      ; (handler_exit         , femtokernel_handler_exit_asm) ]%list.

    Definition map_with_label {A B} (f : A -> B) (l : list (Label * A)) : list (Label * B) :=
      map (λ '(l, b), (l, f b)) l.

    Definition find_label {A} (label : Label) (l : list (Label * A)) (default : A) : A :=
      match find (λ '(l', _), String.eqb label l') l with
      | None   => default
      | Some e => snd e
      end.

    Fixpoint from_label {A} (label : Label) (l : list (Label * A)) : list (Label * A) :=
      match l with
      | [] => []
      | (e , a) :: l' =>
          if String.eqb e label
          then l
          else from_label label l'
      end%list.

    Definition block_size : list AST -> N :=
      N.of_nat ∘ Nat.mul bytes_per_instr  ∘ List.length.

    Definition annot_block_size : list AnnotInstr -> N :=
      block_size ∘ filter_AnnotInstr_AST.

    Definition femtokernel_block_sizes : list (Label * N) :=
      map_with_label annot_block_size femtokernel_block_layout.

    (* SIZES *)
    Definition init_size : N := find_label init femtokernel_block_sizes 0%N.
    Definition handler_entry_size : N := find_label handler_entry femtokernel_block_sizes 0%N.
    Definition handler_write_size : N := find_label handler_write femtokernel_block_sizes 0%N.
    Definition handler_secret_write_size : N := find_label handler_secret_write femtokernel_block_sizes 0%N.
    Definition handler_exit_size : N := find_label handler_exit femtokernel_block_sizes 0%N.
    Definition handler_size : N := handler_entry_size + handler_write_size + handler_secret_write_size + handler_exit_size.

    (* addrs_for_blocks returns a list of the same length as the given list of
       blocks, but with the address each block is located at. An initial address
       needs to be given for the first block, and all other blocks will be
       placed in sequence after another. *)
    Fixpoint addrs_for_blocks (bs : list (Label * list AST)) (init_addr : N) : list (Label * N) :=
      let f (acc : list (Label * N) * N) (b : Label * list AST) : list (Label * N) * N :=
        let '(label, b) := b in
        let '(addrs, curr) := acc in
        (cons (label , curr) addrs, (curr + block_size b)%N) in
      let '(addrs, end_addr) := foldl f ([]%list, init_addr) bs in
      reverse (cons ("_", end_addr) addrs). (* We choose the label _ for the end addr. *)

    (* ADDRESSES *)
    (* We fix the init addr to 0 for our femtokernel blocks *)
    Definition init_addr : N := 0.

    (* We compute all addresses w.r.t. the FemtoKernel block layout at once.
       Note that we also get the "end" or "exit" address of our kernel as
       part of this definition. So the resulting list has a length of:
       number of blocks + 1. *)
    Definition femtokernel_block_addrs : list (Label * N) :=
      addrs_for_blocks (map_with_label filter_AnnotInstr_AST femtokernel_block_layout) init_addr.

    (* Note that we need to use "Eval compute in ..." for all addresses.
       In proofs below, we often use cbn/simpl/..., which will hang if we
       don't compute here. *)
    Definition handler_entry_addr        : N :=
      Eval compute in find_label handler_entry femtokernel_block_addrs 0%N.
    Definition handler_write_addr        : N :=
      Eval compute in find_label handler_write femtokernel_block_addrs 0%N.
    Definition handler_secret_write_addr : N :=
      Eval compute in find_label handler_secret_write femtokernel_block_addrs 0%N.
    Definition handler_exit_addr         : N :=
      Eval compute in find_label handler_exit femtokernel_block_addrs 0%N.
    Definition data_addr                 : N :=
      Eval compute in snd (List.last femtokernel_block_addrs ("_", 0%N)).
    (* We allocate one word for the data addr *)
    Definition adv_addr                  : N :=
      data_addr + (N.of_nat bytes_per_word).

    Definition femtokernel_handler : list AnnotInstr :=
      (foldl app []%list ∘ map snd ∘ from_label handler_entry) femtokernel_block_layout.

    (* CODE AND CONFIG SHORTANDS*)
    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
    (* Shorthand for the pmp entries in both Katamaran and Iris *)
    Local Notation asn_femto_pmpentries a :=
      ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
        (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)))])%list.

    Definition pmp_cfg_to_term {Σ} : list PmpEntryCfg -> list (Term Σ (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      let term_cfg cfg := term_val ty_pmpcfg_ent cfg in
      let term_addr a  := term_val ty_xlenbits a in
      map (fun '(cfg , addr) => term_binop bop.pair (term_cfg cfg) (term_addr addr)).

    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end)]%list.

    Definition term_femto_pmpentries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      term_list (pmp_cfg_to_term femto_pmpentries).

    (* Definition of the femtokernel initialization procedure that works both for the legacy and the MMIO case, since the address of the adversary is equal in both cases *)
    (* note that the addresses we supply assume base address 0 but the code actually only uses relative addresses, so it's okay if it's placed elsewhere in memory.    *)
    Definition femtokernel_init_gen := femtokernel_init' init_addr handler_entry_addr adv_addr.

    Definition femtokernel_handler_entry := femtokernel_handler_entry_asm handler_write_size.
    Definition femtokernel_handler_write := femtokernel_handler_write_asm handler_exit_addr.
    Definition femtokernel_handler_secret_write := femtokernel_handler_secret_write_asm handler_secret_write_addr data_addr.
    Definition femtokernel_handler_exit := femtokernel_handler_exit_asm.

    Import asn.notations.
    Import RiscvPmp.Sig.
    Local Notation asn_inv_mmio := (asn.chunk (chunk_user (inv_mmio bytes_per_word) [env])). (* Fix word length at 4 for this example, as we do not perform any other writes*)
    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Definition post_mip_val : Val ty_Minterrupts :=
      MkMinterrupts false false false false false false.
    Definition term_post_mip_val {Σ} : Term Σ ty_Minterrupts :=
      term_val ty_Minterrupts post_mip_val.

    Definition Σ__csrs : LCtx :=
      ["mtvec" :: ty_xlenbits;
       "mcause" :: ty_xlenbits;
       "mepc" :: ty_xlenbits;
       "mie" :: ty_Minterrupts;
       "mip" :: ty_Minterrupts;
       "mstatus_mpie" :: ty.bool].

    Record CSRVals := mkCSRVals {
        vmtvec  : Val ty_xlenbits;
        vmcause : Val ty_xlenbits;
        vmepc   : Val ty_xlenbits;
        vmie    : Val ty_Minterrupts;
        vmip    : Val ty_Minterrupts;
        vmstatus_mpie : Val ty.bool;
      }.

    Definition CSRVals_Valuation (vals : CSRVals) : Valuation Σ__csrs :=
      [env]
        .["mtvec" ∷ ty_xlenbits ↦ vmtvec vals]
        .["mcause" ∷ ty_xlenbits ↦ vmcause vals]
        .["mepc" ∷ ty_xlenbits ↦ vmepc vals]
        .["mie" ∷ ty_Minterrupts ↦ vmie vals]
        .["mip" ∷ ty_Minterrupts ↦ vmip vals]
        .["mstatus_mpie" ∷ ty.bool ↦ vmstatus_mpie vals].

    Example femtokernel_init_pre : Assertion (Σ__csrs ▻▻ ["a"::ty_xlenbits]) :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      mtvec ↦ term_var "mtvec" ∗
      mcause ↦ term_var "mcause" ∗
      mip ↦ term_var "mip" ∗ mie ↦ term_var "mie" ∗
      mepc ↦ term_var "mepc" ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "x1", x1 ↦ term_var "x1") ∗
      (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                   (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])).

    Import TermNotations.

    Example femtokernel_init_post : Assertion (Σ__csrs ▻▻ ["a"::ty_xlenbits; ("an"::ty_xlenbits)]) :=
      (
        (term_var "an" = term_var "a" +ᵇ (term_val ty_xlenbits (bv.of_N adv_addr)))%asn ∗
          (mtvec ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)) ∗
          mcause ↦ term_var "mcause" ∗
          mip ↦ term_post_mip_val ∗ mie ↦ term_var "mie" ∗
          mepc ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N adv_addr) ∗
          mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool true; term_val ty.bool true ] ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          x1 ↦ term_val ty_xlenbits [bv 0x80] ∗
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

    Definition contract_femtoinit `{sailGS Σ} (a : Val ty_xlenbits) (csrs : CSRVals) : iProp Σ :=
      let ι__csrs := CSRVals_Valuation csrs in
      semTripleBlock
        (λ a, asn.interpret femtokernel_init_pre ι__csrs.["a" ∷ ty_xlenbits ↦ a])
        a (filter_AST femtokernel_init_gen)
        (λ a an, asn.interpret femtokernel_init_post ι__csrs.["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]).

    Lemma contract_femtoinit_verified : ∀ `{sailGS Σ} (a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtoinit a csrs.
    Proof.
      unfold contract_femtoinit. iIntros (Σ sg a csrs).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      vm_compute.
      apply sat__femtoinit.
    Qed.

    Definition femtokernel_handler_shared_pre (addr : N) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_entry_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      term_var "a" = term_val ty_xlenbits (bv.of_N addr) ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (mtvec ↦ term_val ty_word (bv.of_N handler_entry_addr)) ∗
       mcause ↦ term_var "mcause" ∗
      (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
      mepc ↦ term_var "mepc" ∗
      asn_pmp_entries term_femto_pmpentries ∗
      (* asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)))) ∗ (* Different handler sizes cause different entries *) *)
      asn_inv_mmio.

    Definition femtokernel_handler_shared_post (priv : Privilege) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
      cur_privilege ↦ term_val ty_privilege priv ∗
      mtvec ↦ term_val ty_word (bv.of_N handler_entry_addr) ∗
      mcause ↦ term_var "mcause" ∗
      mip ↦ term_post_mip_val ∗ mie ↦ term_var "mie" ∗
      mepc ↦ term_var "mepc" ∗
      asn_pmp_entries term_femto_pmpentries.
      (* asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)))). (* Different handler sizes cause different entries *) *)

    Example femtokernel_handler_entry_pre : Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_entry_addr) (sub_up1 (sub_cat_left _)) ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
      x5 ↦ term_var "x5" ∗
      x10 ↦ term_var "x10".

    Example femtokernel_handler_entry_post :
      Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post Machine) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
      (if: (term_var "x10" ?= term_val ty_xlenbits (bv.of_N mmio_write_adv))
       then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_entry_size)
       else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_entry_size + handler_write_size))) ∗
      x5 ↦ term_val ty_xlenbits (bv.of_N mmio_write_adv) ∗
      x10 ↦ term_var "x10".

    Example femtokernel_handler_write_pre : Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_write_addr) (sub_up1 (sub_cat_left _)) ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
      x5 ↦ term_var "x5".

    Example femtokernel_handler_write_post :
      Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post Machine) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
      term_var "an" = term_val ty_xlenbits (bv.of_N handler_exit_addr) ∗
      x5 ↦ term_val ty_xlenbits (bv.of_N 42).

    Example femtokernel_handler_secret_write_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_secret_write_addr) (sub_up1 (sub_cat_left _)) ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
      x1 ↦ term_var "x1" ∗
      term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    Example femtokernel_handler_secret_write_post :
      Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post Machine) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
      term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_secret_write_size) ∗
      x1 ↦ term_val ty_xlenbits bv.zero ∗
      term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    Example femtokernel_handler_exit_pre : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      femtokernel_handler_shared_pre handler_exit_addr ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ].

    Example femtokernel_handler_exit_post :
      Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      femtokernel_handler_shared_post User ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool true; term_var "mstatus_mpie" ] ∗
      term_var "an" = term_var "mepc".

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

    Definition vc__femtohandler_entry : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     femtokernel_handler_entry_pre
                     femtokernel_handler_entry
                     femtokernel_handler_entry_post wnil).

    Definition vc__femtohandler_write : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     femtokernel_handler_write_pre
                     femtokernel_handler_write
                     femtokernel_handler_write_post wnil).

    Definition vc__femtohandler_secret_write : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     femtokernel_handler_secret_write_pre
                     femtokernel_handler_secret_write
                     femtokernel_handler_secret_write_post wnil).

    Definition vc__femtohandler_exit : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     femtokernel_handler_exit_pre
                     femtokernel_handler_exit
                     femtokernel_handler_exit_post wnil).

      (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in vc__femtohandler. *)

    Import Erasure.notations.
    Lemma sat__femtohandler_entry : safeE vc__femtohandler_entry.
    Proof.
      (* We still need to prove that our word falls within mmio *)
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtohandler_write : safeE vc__femtohandler_write.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
      1-4: eapply bv.in_seqBv'; now vm_compute.
    Qed.

    Lemma sat__femtohandler_secret_write : safeE vc__femtohandler_secret_write.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
      1-4: eapply bv.in_seqBv'; now vm_compute.
      (* TODO: pull this into lemma: v = sext' v 0, but types are complaining when
               naively writing this down *)
      unfold bv.sext'.
      rewrite bv.ones_O.
      destruct (bv.view (@bv.zero 0)).
      rewrite ssrbool.if_same.
      now rewrite bv.app_nil_r.
    Qed.

    Lemma sat__femtohandler_exit : safeE vc__femtohandler_exit.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Section WithEnvNotations.
      Import env.notations.

      Definition contract_femtohandler_builder `{sailGS Σ} {Γ} (ι : Valuation Γ)
        (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
        (b : Block)
        (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
        : Val ty_xlenbits -> CSRVals -> iProp Σ :=
        fun a csrs =>
          let ι__csrs := CSRVals_Valuation csrs in
          semTripleBlock
            (λ a, asn.interpret PRE (ι__csrs ►► ι ►► env.nil.["a" ∷ ty_xlenbits ↦ a]))
            a (filter_AST b)
            (λ a an, asn.interpret POST (ι__csrs ►► ι ►► env.nil.["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an])).

      Definition contract_femtohandler_entry `{sailGS Σ} (x5 x10 : Val ty_xlenbits) : Val ty_xlenbits -> CSRVals -> iProp Σ :=
        contract_femtohandler_builder
          env.nil.["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10]
          femtokernel_handler_entry_pre
          femtokernel_handler_entry
          femtokernel_handler_entry_post.

      Lemma contract_femtohandler_entry_verified : ∀ `{sailGS Σ} (x5 x10 a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_entry x5 x10 a csrs.
      Proof.
        unfold contract_femtohandler_entry. iIntros (Σ sg x5 x10 a csrs).
        iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
        pose proof sat__femtohandler_entry as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_write `{sailGS Σ} (x5 : Val ty_xlenbits) : Val ty_xlenbits -> CSRVals -> iProp Σ :=
        contract_femtohandler_builder
          env.nil.["x5" ∷ ty_xlenbits ↦ x5]
          femtokernel_handler_write_pre
          femtokernel_handler_write
          femtokernel_handler_write_post.

      Lemma contract_femtohandler_write_verified : ∀ `{sailGS Σ} (x5 a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_write x5 a csrs.
      Proof.
        unfold contract_femtohandler_write. iIntros (Σ sg x5 a csrs).
        iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
        pose proof sat__femtohandler_write as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_secret_write `{sailGS Σ} (x1 secret : Val ty_xlenbits) : Val ty_xlenbits -> CSRVals -> iProp Σ :=
        contract_femtohandler_builder
          env.nil.["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret]
          femtokernel_handler_secret_write_pre
          femtokernel_handler_secret_write
          femtokernel_handler_secret_write_post.

      Lemma contract_femtohandler_secret_write_verified : ∀ `{sailGS Σ} (x1 secret a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_secret_write x1 secret a csrs.
      Proof.
        unfold contract_femtohandler_secret_write. iIntros (Σ sg x1 secret a csrs).
        iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
        pose proof sat__femtohandler_secret_write as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_exit `{sailGS Σ} : Val ty_xlenbits -> CSRVals -> iProp Σ :=
        contract_femtohandler_builder
          env.nil
          femtokernel_handler_exit_pre
          femtokernel_handler_exit
          femtokernel_handler_exit_post.

      Lemma contract_femtohandler_exit_verified : ∀ `{sailGS Σ} (a : Val ty_xlenbits) (csrs : CSRVals),
        ⊢ contract_femtohandler_exit a csrs.
      Proof.
        unfold contract_femtohandler_exit. iIntros (Σ sg a csrs).
        iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
        pose proof sat__femtohandler_exit as H.
        vm_compute; apply H.
      Qed.
    End WithEnvNotations.

    Definition femtoinit_stats :=
      SymProp.Statistics.count_to_stats
        (SymProp.Statistics.count_nodes
           (sannotated_block_verification_condition
              femtokernel_init_pre
              femtokernel_init_gen
              (asn.sep femtokernel_init_post asn.debug)
              wnil)
           SymProp.Statistics.empty).
    (* Eval vm_compute in femtoinit_stats. *)

    (* There is currently no difference, because the adversary addresses are shared between both cases*)
    Definition femto_init_stats := femtoinit_stats.
    (* Eval vm_compute in femto_init_stats. *)

    (* Definition femtohandler_stats := *)
    (*   SymProp.Statistics.count_to_stats *)
    (*     (SymProp.Statistics.count_nodes *)
    (*        (sannotated_block_verification_condition *)
    (*           femtokernel_handler_pre *)
    (*           femtokernel_handler *)
    (*           (asn.sep femtokernel_handler_post asn.debug) *)
    (*           wnil) *)
    (*        SymProp.Statistics.empty). *)
    (* Eval vm_compute in femtohandler_stats. *)

  End FemtoKernel.

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
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry] in HPmp.
    cbn in HPmp.
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

  Definition femto_inv_mmio `{sailGS Σ} := interp_inv_mmio bytes_per_word.

  Import env.notations.

  Opaque interp_pmp_entries.

  (* Needed when introducing the below conditional *)
  Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B).
  Proof. destruct b; apply _. Qed.

  Ltac set_to_list s l Hl Hel :=
    remember (elements s) as l eqn:Hel;
    assert (Hl : list_to_set l = s) by (subst; apply list_to_set_elements_L).

  Ltac set_subseteq_to_list :=
    match goal with
    | |- (?s1 : gset _) ⊆ (?s2 : gset _) =>
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let Hl1 := fresh "Hl" in
        let Hl2 := fresh "Hl" in
        let Hel1 := fresh "Hel" in
        let Hel2 := fresh "Hel" in
        set_to_list s1 l1 Hl1 Hel1;
        set_to_list s2 l2 Hl2 Hel2;
        vm_compute in Hel1;
        vm_compute in Hel2;
        rewrite <- Hl1, <- Hl2;
        apply list_to_set_subseteq;
        rewrite Hel1 Hel2
    end.

  Ltac solve_elem_of :=
    repeat (try apply elem_of_list_here;
            try apply elem_of_list_further).

  Ltac solve_list_subseteq :=
    repeat
      match goal with
      | |- []%list ⊆ ?l =>
          apply list_subseteq_nil
      | |- ?l1 ⊆ ?l2 =>
          apply list_subseteq_cons_iff
      | |- ?P ∧ ?q =>
          split
      | |- ?e ∈ ?l =>
          solve_elem_of
      end.

  Ltac solve_subseteq :=
    set_subseteq_to_list;
    solve_list_subseteq.

  Ltac reduce_big_sepS_big_sepL :=
    repeat
      match goal with
      | |- context[big_opS ?op ?f ?s] =>
          let l := fresh "l" in
          let Hl := fresh "Hl" in
          let Hel := fresh "Hel" in
          set_to_list s l Hl Hel;
          rewrite <- Hl;
          assert (Hdup : NoDup l) by (subst; apply NoDup_elements);
          rewrite (big_sepS_list_to_set _ _ Hdup);
          vm_compute in Hel;
          rewrite Hel
      end.

  Definition femtokernel_safe_shared_pre `{sailGS Σ} (addr : N) (b : Block) : iProp Σ :=
    exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
    (∃ v, mscratch ↦ᵣ v) ∗
    interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User. (* Not needed for handler, but required for the rest of execution *)

  Definition asn_iprop_pre `{sailGS Σ} {Γ} (asn : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits])) (csrs : CSRVals) (ι : Valuation Γ) (addr : Val ty_xlenbits) : iProp Σ :=
    asn.interpret asn (CSRVals_Valuation csrs ►► ι ►► env.nil.["a" ∷ ty_xlenbits ↦ addr]).

  Lemma femtokernel_handler_exit_safe `{sailGS Σ} (csrs : CSRVals) :
    ⊢ femtokernel_safe_shared_pre handler_exit_addr femtokernel_handler_exit ∗
      @asn_iprop_pre _ _ ctx.nil femtokernel_handler_exit_pre csrs env.nil (bv.of_N handler_exit_addr) ∗
      interp_gprs ∅ ∗
      ▷ (ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
         LoopVerification.Trap User (bv.of_N handler_entry_addr) femto_pmpentries -∗ WP_loop)
      -∗
      WP_loop.
  Proof.
    iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Htrap)".
    iPoseProof (contract_femtohandler_exit_verified (bv.of_N handler_exit_addr) csrs) as "H".
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    iSpecialize ("Htrap" with "[Hinstrs]"); first by iModIntro.
    iPoseProof (LoopVerification.valid_semTriple_loop with "[-]") as "Hk".
    - iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _])"; cbn in *.
      iFrame "Hpc Hnpc Hmstatus HaccU Hgprs Hmscratch Htrap".
      iSplitL "Hshared";
        first by repeat iDestruct "Hshared" as "($ & Hshared)".
      repeat iSplitL; iModIntro;
        unfold LoopVerification.CSRMod, LoopVerification.Recover.
      + iIntros "(? & ? & ? & ? & %eq & ?)".
        inversion eq.
      + iIntros "[% (_ & _ & _ & _ & _ & %eq & H)]".
        inversion eq.
    - iApply (semWP_mono with "Hk"); auto.
  Qed.

  Lemma femtokernel_handler_write_safe `{sailGS Σ} (vx5 : Val ty_xlenbits) (csrs : CSRVals) :
    ⊢ femtokernel_safe_shared_pre handler_write_addr femtokernel_handler_write ∗
      asn_iprop_pre femtokernel_handler_write_pre csrs env.nil.["x5" ∷ ty_xlenbits ↦ vx5] (bv.of_N handler_write_addr) ∗
      interp_gprs {[x5]} ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
      ▷ (ptsto_instrs (bv.of_N handler_write_addr) (filter_AST femtokernel_handler_write) -∗
         ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
         LoopVerification.Trap User (bv.of_N handler_entry_addr) femto_pmpentries -∗ WP_loop)
      -∗
      WP_loop.
  Proof.
    iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hexit & Htrap)".
    iPoseProof (contract_femtohandler_write_verified vx5 (bv.of_N handler_write_addr) csrs) as "H".
    iAssert (femto_inv_mmio)%I as "#Hinv".
    { iDestruct "Hpre" as "((_ & _ & _ & _ & _ & _ & _ & _ & _ & $) & _)". }
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx5)"; cbn in *.
    iAssert (interp_gprs ∅) with "[Hgprs Hx5]" as "Hgprs".
    { iApply (interp_gprs_with_excluded (exclude := {[x5]}));
        try solve_subseteq.
      iFrame "Hgprs".
      reduce_big_sepS_big_sepL.
      now iFrame "Hx5". }
    iApply femtokernel_handler_exit_safe.
    rewrite Han.
    iSpecialize ("Htrap" with "[Hinstrs]"); first by iModIntro.
    iFrame "Hpc Hexit Hnpc Hmscratch HaccU Hmstatus Hgprs Htrap Hinv"; cbn.
    repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
    now iPureIntro.
  Qed.

  Lemma femtokernel_handler_secret_write_safe `{sailGS Σ} (vx1 secret : Val ty_xlenbits) (csrs : CSRVals) :
    ⊢ femtokernel_safe_shared_pre handler_secret_write_addr femtokernel_handler_secret_write ∗
      asn_iprop_pre femtokernel_handler_secret_write_pre csrs env.nil.["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret] (bv.of_N handler_secret_write_addr) ∗
      interp_gprs {[x1]} ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
      ▷ (ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
         interp_ptstomem (bv.of_N data_addr) secret -∗
         ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
         LoopVerification.Trap User (bv.of_N handler_entry_addr) femto_pmpentries -∗ WP_loop)
      -∗
      WP_loop.
  Proof.
    iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hexit & Htrap)".
    iPoseProof (contract_femtohandler_secret_write_verified vx1 secret (bv.of_N handler_secret_write_addr) csrs) as "H".
    iAssert (femto_inv_mmio)%I as "#Hinv".
    { iDestruct "Hpre" as "((_ & _ & _ & _ & _ & _ & _ & _ & _ & $) & _)". }
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Haddr)"; cbn - [interp_ptstomem] in *.
    iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
    { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
        try solve_subseteq.
      iFrame "Hgprs".
      reduce_big_sepS_big_sepL.
      now iFrame "Hx1". }
    iApply femtokernel_handler_exit_safe.
    rewrite Han.
    iSpecialize ("Htrap" with "[Hinstrs] [Haddr]"); try by iModIntro.
    iFrame "Hpc Hexit Hnpc Hmscratch HaccU Hmstatus Hgprs Htrap Hinv"; cbn - [interp_ptstomem].
    repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
    now iPureIntro.
  Qed.

  Lemma femtokernel_handler_entry_safe `{sailGS Σ} (x5_val x10_val : Val ty_xlenbits) (csrs : CSRVals) :
    ⊢ femtokernel_safe_shared_pre handler_entry_addr femtokernel_handler_entry ∗
      asn_iprop_pre femtokernel_handler_entry_pre csrs env.nil.["x5" ∷ ty_xlenbits ↦ x5_val].["x10" ∷ ty_xlenbits ↦ x10_val] (bv.of_N handler_entry_addr) ∗
      interp_gprs {[ x1; x5; x10 ]} ∗
      (∃ v, x1 ↦ᵣ v) ∗
      (∃ (v : Val ty_xlenbits), interp_ptstomem (bv.of_N data_addr) v) ∗
      ptsto_instrs (bv.of_N handler_write_addr) (filter_AST femtokernel_handler_write) ∗
      ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
      ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit)
      -∗
      WP_loop.
  Proof.
    revert x5_val x10_val csrs.
    iLöb as "IH".
    iIntros (x5_val x10_val csrs) "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hx1 & Hdata & Hhwrite & Hhsecret & Hhexit)".
    iPoseProof (contract_femtohandler_entry_verified x5_val x10_val (bv.of_N handler_entry_addr) csrs) as "H".
    iAssert (femto_inv_mmio)%I as "#Hinv".
    { iDestruct "Hpre" as "((_ & _ & _ & _ & _ & _ & _ & _ & _ & $) & _)". }
    iApply (WP_loop_semTripleBlock with "Hpro Hpre H"). iClear "H".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx5 & Hx10)"; cbn - [interp_ptstomem].
    iAssert (interp_gprs {[ x1; x5 ]}) with "[Hgprs Hx10]" as "Hgprs".
    { iApply (interp_gprs_with_excluded_gen {[x1; x5]} (exclude2 := {[x10]}));
        try solve_subseteq.
      iFrame "Hgprs".
      reduce_big_sepS_big_sepL.
      now iFrame "Hx10". }
    case_match; cbn - [interp_ptstomem];
      iDestruct "Han" as "[-> _]".
    (* TODO: these two cases have almost the exact same proof script,
             only difference is in which lemma to apply (write <> secret_write),
             and how some framing introducing is done w.r.t. the ptsto_instrs (Hhsecret and Hhwrite) *)
    - iApply femtokernel_handler_write_safe; cbn - [interp_ptstomem].
      iFrame "Hpc Hnpc Hhwrite Hmscratch HaccU".
      repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
      iAssert (interp_gprs {[ x5 ]}) with "[Hgprs Hx1]" as "Hgprs".
      { iApply (interp_gprs_with_excluded_gen {[x5]} (exclude2 := {[x1]}));
        try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        now iFrame "Hx1". }
      iFrame "Hx5 Hgprs Hmstatus Hhexit Hinv".
      repeat iSplitR; auto.
      unfold LoopVerification.Trap.
      iModIntro. iIntros "Hhwrite Hhexit Htrap".
      iDestruct "Htrap" as "(Hpc & Hnpc & [%vmpie Hmstatus] & HaccU & Hgprs & Hcp & Hmtvec & [%vmcause Hmcause] & [%vmip Hmip] & [%vmie Hmie] & Hmscratch & [%vmepc Hmepc] & Hpmp)".
      iPoseProof (interp_gprs_with_excluded (exclude := {[x1; x5; x10]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([% Hx1] & [% Hx5] & [% Hx10] & _)".
      iApply ("IH" $! _ _ {|
                         vmtvec        := bv.of_N handler_entry_addr;
                         vmcause       := vmcause;
                         vmepc         := vmepc;
                         vmie          := vmie;
                         vmip          := vmip;
                         vmstatus_mpie := vmpie;
                |}); cbn.
      now iFrame "Hdata Hpc Hinstrs Hnpc Hmscratch HaccU Hcp Hmtvec Hmcause Hmip Hmie Hmepc Hpmp Hhwrite Hhsecret Hhexit Hmstatus Hx1 Hx5 Hx10 Hgprs Hinv".
    - iDestruct "Hx1" as "[% Hx1]".
      iDestruct "Hdata" as "[% Hdata]".
      iApply femtokernel_handler_secret_write_safe; cbn - [interp_ptstomem].
      iFrame "Hpc Hnpc Hhsecret Hmscratch HaccU".
      repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
      iAssert (interp_gprs {[ x1 ]}) with "[Hgprs Hx5]" as "Hgprs".
      { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}));
        try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        now iFrame "Hx5". }
      iFrame "Hx1 Hdata Hgprs Hmstatus Hhexit Hinv".
      repeat iSplitR; auto.
      unfold LoopVerification.Trap.
      iModIntro. iIntros "Hhsecret Hdata Hhexit Htrap".
      iDestruct "Htrap" as "(Hpc & Hnpc & [%vmpie Hmstatus] & HaccU & Hgprs & Hcp & Hmtvec & [%vmcause Hmcause] & [%vmip Hmip] & [%vmie Hmie] & Hmscratch & [%vmepc Hmepc] & Hpmp)".
      iPoseProof (interp_gprs_with_excluded (exclude := {[x1; x5; x10]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
      iApply ("IH" $! _ _ {|
                         vmtvec        := bv.of_N handler_entry_addr;
                         vmcause       := vmcause;
                         vmepc         := vmepc;
                         vmie          := vmie;
                         vmip          := vmip;
                         vmstatus_mpie := vmpie;
                |}); cbn - [interp_ptstomem].
      now iFrame "Hpc Hinstrs Hnpc Hmscratch HaccU Hcp Hmtvec Hmcause Hmip Hmie Hmepc Hpmp Hhwrite Hhsecret Hhexit Hmstatus Hx1 Hdata Hx5 Hx10 Hgprs Hinv".
  Qed.

  Definition ptsto_instrs_handler `{sailGS Σ} : iProp Σ :=
    ptsto_instrs (bv.of_N handler_entry_addr) (filter_AnnotInstr_AST femtokernel_handler_entry) ∗
    ptsto_instrs (bv.of_N handler_write_addr) (filter_AnnotInstr_AST femtokernel_handler_write) ∗
    ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AnnotInstr_AST femtokernel_handler_secret_write) ∗
    ptsto_instrs (bv.of_N handler_exit_addr) (filter_AnnotInstr_AST femtokernel_handler_exit).

  (* TODO: this lemma feels very incremental wrt to the last one; merge? *)
  Lemma femtokernel_manualStep2 `{sailGS Σ} :
    ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
      (mtvec ↦ᵣ (bv.of_N handler_entry_addr)) ∗
      (∃ v, mcause ↦ᵣ v) ∗
      (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
      (∃ v, mscratch ↦ᵣ v) ∗
      (∃ v, mepc ↦ᵣ v) ∗
      cur_privilege ↦ᵣ User ∗
      interp_gprs ∅ ∗
      interp_pmp_entries femto_pmpentries ∗
      femto_inv_mmio ∗
      (pc ↦ᵣ (bv.of_N adv_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs_handler ∗
      (∃ (v : Val ty_xlenbits), interp_ptstomem (bv.of_N data_addr) v) ∗
      ptstoSthL advAddrs
      ={⊤}=∗
      ∃ mpp, LoopVerification.loop_pre User (bv.of_N handler_entry_addr) (bv.of_N adv_addr) mpp femto_pmpentries.
  Proof.
    iIntros "([%mpp Hmst] & Hmtvec & Hmcause & Hmip & Hmie & Hmscratch & Hmepc & Hcurpriv & Hgprs & Hpmpcfg & #Hmmio & Hpc & Hnpc & (Hhentry & Hhwrite & Hhsecret & Hhexit) & Hdata & Hmemadv)".
    iExists mpp.
    unfold LoopVerification.loop_pre, LoopVerification.Step_pre, LoopVerification.Execution.
    iFrame "Hmst Hmtvec Hmcause Hmip Hmie Hmscratch Hmepc Hcurpriv Hgprs Hpmpcfg Hpc Hnpc".
    iModIntro.

    iSplitL "Hmemadv".
    now iApply memAdv_pmpPolicy.

    iSplitL "".
    iModIntro.
    unfold LoopVerification.CSRMod.
    iIntros "(_ & _&  _ & _ & %eq & _)".
    inversion eq.

    iSplitL.
    unfold LoopVerification.Trap.
    iModIntro.
    iIntros "(Hpc & Hnpc & [%vmpie Hmstatus] & Hmem & Hgprs & Hcurpriv & Hmtvec & [%vmcause Hmcause] & [%vmip Hmip] & [%vmie Hmie] & Hmscratch & [%vmepc Hmepc] & Hpmpents)".
    iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
      try solve_subseteq.
    reduce_big_sepS_big_sepL.
    iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
    iApply (femtokernel_handler_entry_safe _ _
                                     {|
                                       vmtvec        := bv.of_N handler_entry_addr;
                                       vmcause       := vmcause;
                                       vmepc         := vmepc;
                                       vmie          := vmie;
                                       vmip          := vmip;
                                       vmstatus_mpie := vmpie;
                                     |}).
    cbn - [interp_ptstomem].
    now iFrame "Hmepc Hgprs Hpmpents Hmcause Hmip Hmie Hmscratch Hcurpriv Hnpc Hpc Hmtvec Hmstatus Hmem Hhentry Hhwrite Hhsecret Hhexit Hmmio Hx1 Hx5 Hx10 Hdata".

    iModIntro.
    unfold LoopVerification.Recover.
    iIntros "(% & _ & _ & _ & _ & _ & %eq & _)".
    inversion eq.
  Qed.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.
  Transparent interp_pmp_entries.

  Local Opaque femtokernel_init_gen. (* TODO: figure out why not having this makes the below proof spin in two places *)

  (* see above *)
  Transparent femtokernel_init_pre.

  Lemma femtokernel_init_safe `{sailGS Σ} (csrs : CSRVals) :
    ⊢ exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
      ∗ ptsto_instrs_handler
      ∗ ptstoSthL advAddrs
      ∗ asn.interpret femtokernel_init_pre (CSRVals_Valuation csrs).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr]
      ∗ interp_gprs {[x1]}
      ∗ (∃ (v : Val ty_xlenbits), interp_ptstomem (bv.of_N data_addr) v)
      ∗ (∃ v, mscratch ↦ᵣ v)
      ∗ femto_inv_mmio (* This is not needed for the `init` code, but it is needed later on *)
        -∗
        WP_loop.
  Proof.
    iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hdata & Hmscratch & #Hmem)".
    iPoseProof (contract_femtoinit_verified (bv.of_N init_addr)) as "H".
    unfold contract_femtoinit; cbn - [asn_regs_ptsto].
    iDestruct "Hpre" as "([% _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hcurpriv & Hx1 & Hpmpentries)".
    iPoseProof (WP_loop_semTripleBlock _ _ _ _ with "Hpro [-Hmscratch Hhandler Hadv Hgprs Hdata] H") as "Hk";
      first (cbn - [asn_regs_ptsto]; iFrame "Hmstatus Hmtvec Hmcause Hmip Hmie Hmepc Hcurpriv Hpmpentries Hx1"; iPureIntro; auto).
    iApply "Hk".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hcurpriv & Hx1 & Hpmpentries)".
    iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
    { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      now iFrame "Hx1 Hgprs". }
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    rewrite ?bv.add_zero_l.
    iApply (fupd_semWP ⊤).
    iMod (femtokernel_manualStep2 with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hgprs $Hcurpriv $Hpmpentries $Hpc $Hnpc $Hmepc $Hmem $Hhandler $Hadv $Hdata]") as "[%mpp Hlooppre]".
    iModIntro.
    iPoseProof (LoopVerification.valid_semTriple_loop with "Hlooppre") as "Hk".
    iApply (semWP_mono with "Hk"); auto.
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
  Lemma liveAddrs_split : liveAddrs = bv.seqBv (bv.of_N init_addr) init_size ++ bv.seqBv (bv.of_N handler_entry_addr) handler_size ++ bv.seqBv (bv.of_N data_addr) (N.of_nat bytes_per_word) ++ advAddrs.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma handlerAddrs_split : @bv.seqBv xlenbits (bv.of_N handler_entry_addr) handler_size = bv.seqBv (bv.of_N handler_entry_addr) handler_entry_size ++ bv.seqBv (bv.of_N handler_write_addr) handler_write_size ++ bv.seqBv (bv.of_N handler_secret_write_addr) handler_secret_write_size ++ bv.seqBv (bv.of_N handler_exit_addr) handler_exit_size.
  Proof.
    (* TODO: scalable proof *)
    by compute.
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

  Lemma femtokernel_splitMemory `{sailGS Σ} {μ : Memory} (secret : Val ty_xlenbits) :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_entry_addr) (filter_AnnotInstr_AST femtokernel_handler_entry) ->
    mem_has_instrs μ (bv.of_N handler_write_addr) (filter_AnnotInstr_AST femtokernel_handler_write) ->
    mem_has_instrs μ (bv.of_N handler_secret_write_addr) (filter_AnnotInstr_AST femtokernel_handler_secret_write) ->
    mem_has_instrs μ (bv.of_N handler_exit_addr) (filter_AnnotInstr_AST femtokernel_handler_exit) ->
    mem_has_word μ (bv.of_N data_addr) secret ->
    mmio_pred bytes_per_word (memory_trace μ) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    @mem_res _ sailGS_memGS μ ⊢ |={⊤}=>
      ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
      ptsto_instrs_handler ∗
      interp_ptstomem (bv.of_N data_addr) secret ∗
      femto_inv_mmio ∗
      [∗ list] a ∈ advAddrs, a ↦ₘ memory_ram μ a.
  Proof.
    iIntros (Hinit Hhentry Hhwrite Hhsecret Hhexit Hdata Hft) "Hmem".
    unfold mem_res, initMemMap.
    rewrite liveAddrs_split.
    iDestruct "Hmem" as "[(Hinit & Hhandler & Hdata & Hadv) Htr]".
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); now compute. }
    iSplitL "Hhandler". (* Need to solve the goal for both handlers *)
    { unfold ptsto_instrs_handler.
      rewrite handlerAddrs_split.
      iDestruct "Hhandler" as "(Hhentry & Hhwrite & Hhsecret & Hhexit)".
      iSplitL "Hhentry".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhentry"); now compute. }
      iSplitL "Hhwrite".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhwrite"); now compute. }
      iSplitL "Hhsecret".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhsecret"); now compute. }
      iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hhexit"); now compute. }
    iSplitL "Hdata".
    { iApply (intro_ptstomem_word2 Hdata).
      iApply (sub_heap_mapsto_interp_ptsto with "Hdata"); now compute. }
    iSplitL "Htr".
    - (* Two cases; either we set up the trace invariant o memory invariant or the trace invariant. *)
      iApply (inv.inv_alloc). iExists _; now iFrame.
    - iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); now compute.
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
    change 4%N with (N.succ (N.succ (N.succ (N.succ N.zero)))).
    rewrite !bv.seqBv_succ !map_cons.
    repeat f_equal; auto.
  Qed.

  Lemma femtokernel_endToEnd {γ γ' : RegStore} {μ μ' : Memory}
        {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} (secret : Val ty_xlenbits) :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_entry_addr) (filter_AnnotInstr_AST femtokernel_handler_entry) ->
    mem_has_instrs μ (bv.of_N handler_write_addr) (filter_AnnotInstr_AST femtokernel_handler_write) ->
    mem_has_instrs μ (bv.of_N handler_secret_write_addr) (filter_AnnotInstr_AST femtokernel_handler_secret_write) ->
    mem_has_instrs μ (bv.of_N handler_exit_addr) (filter_AnnotInstr_AST femtokernel_handler_exit) ->
    mem_has_word μ (bv.of_N data_addr) secret ->
    mmio_pred bytes_per_word (memory_trace μ) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    read_register γ mstatus = {| MPP := User; MPIE := false; MIE := false |} ->
    read_register γ cur_privilege = Machine ->
    read_register γ pmp0cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr0 = bv.zero ->
    read_register γ pmp1cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr1 = bv.zero ->
    read_register γ pc = (bv.of_N init_addr) ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    mmio_pred bytes_per_word (memory_trace μ') (* The initial demands hold over the final state *).
  Proof.
    intros μinit μhentry μhwrite μhsecret μhexit μdata μft γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc steps.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _).
    iIntros (Σ' H).
    cbn.
    iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmie & Hmip & Hmtvec & Hmscratch & Hmepc & Hmcause & Hcurpriv & H')".
    rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc.
    iMod (femtokernel_splitMemory with "Hmem") as "(Hinit & Hhandler & Hdata & #Hmmio & Hadv)";
      try eassumption.
    iPoseProof (intro_ptstoSthL with "Hadv") as "Hadv".
    iModIntro.
    iSplitL.
    - destruct (env.view δ).

      iApply (femtokernel_init_safe {|
                         vmtvec        := read_register γ mtvec;
                         vmcause       := read_register γ mcause;
                         vmepc         := read_register γ mepc;
                         vmie          := read_register γ mie;
                         vmip          := read_register γ mip;
                         vmstatus_mpie := false;
                |}
               with "[-]").

      #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
      iFrame "∗ #". cbn - [interp_gprs].
      rewrite <- ?bi.sep_assoc.
      iSplitR; first auto.
      rewrite <- ?bi.sep_assoc.
      repeat first [iDestruct "H'" as "($ & H')"
                   | iDestruct "H'" as "(? & H')"].
      unfold interp_gprs; reduce_big_sepS_big_sepL; cbn.
      iAssert (□ ∀ r v, r ↦ᵣ v -∗ ∃ v, r ↦ᵣ v)%I as "#Heq".
      { iModIntro. iIntros (? v) "H". now iExists v. }
      repeat try (iRename select (_ ↦ᵣ _) into "Hpts";
                  iPoseProof ("Heq" with "Hpts") as "Hpts";
                  iFrame "Hpts").
    - iIntros "Hmem".
      iInv "Hmmio" as (t) ">[Hfrag %Hpred]" "_".
      iDestruct "Hmem" as "(%memmap & Hinv & %link & Htr)".
      iDestruct (trace.trace_full_frag_eq with "Htr Hfrag") as "->".
      iApply fupd_mask_intro; first set_solver.
      now iIntros "_".
  Qed.

(* Print Assumptions femtokernel_endToEnd. *)

  Section RelationalVerification.
    Import BinaryBlockVerifier.
    Import RiscvPmpBlockVerifIrisInstance2.
    Import IrisModelBinary.RiscvPmpIrisBase2.
    Import IrisInstanceBinary.RiscvPmpIrisInstancePredicates2.

    Notation "a '↦ᵣ' t" := (reg_pointsTo21 a t).

    Let femto_inv_mmio `{sailGS2 Σ} := interp_inv_mmio bytes_per_word.

    Definition UnaryPredicateDefIProp {Σ} (sG : sailGS Σ) :=
      @RiscvPmpBlockVerifIrisInstance.PredicateDefIProp _ sG.

    Definition asn_interpret_left `{sailGS2 Σ} : ∀ {Γ : LCtx}, Assertion Γ -> Valuation Γ -> iProp Σ :=
      @asn.interpret _ (UnaryPredicateDefIProp sailGS2_sailGS_left).

    Definition asn_interpret_right `{sailGS2 Σ} : ∀ {Γ : LCtx}, Assertion Γ -> Valuation Γ -> iProp Σ :=
      @asn.interpret _ (UnaryPredicateDefIProp sailGS2_sailGS_right).

    Definition interp_ptstomem2 `{memGS2 Σ} {width : nat} (addr : Addr) (v__l v__r : bv (width * byte)) : iProp Σ :=
      (@RiscvPmpIrisInstancePredicates.interp_ptstomem _ memGS2_memGS_left width addr v__l
       ∗ @RiscvPmpIrisInstancePredicates.interp_ptstomem _ memGS2_memGS_right width addr v__r)%I.

    Section WithAssertionNotations.
      Import asn.notations.
      Import TermNotations.
      Import bv.notations.

      (* We define _rel analogues of the non _rel version for the secret_write pre and post.
         The difference is that we omit the data ↦ secret, since we will have two different secrets. *)
      Example femtokernel_handler_secret_write_pre_rel : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_secret_write_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
        x1 ↦ term_var "x1".

      Example femtokernel_handler_secret_write_post_rel :
        Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post Machine) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_mpie"; term_val ty.bool false ] ∗
        term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_secret_write_size) ∗
        x1 ↦ term_val ty_xlenbits bv.zero.

    End WithAssertionNotations.

    Lemma femtokernel_handler_pre_persistent_preds `{sailGS2 Σ} (x5 x10 : Val ty_xlenbits) (csrs : CSRVals) :
      let Σ := (CSRVals_Valuation csrs).["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] in
      asn.interpret femtokernel_handler_entry_pre Σ -∗
     ⌜(@bv.unsigned xlenbits (bv.of_N handler_entry_addr) + Z.of_N (adv_addr - handler_entry_addr) < Z.of_N maxAddr)%Z⌝ ∗
      femto_inv_mmio ∗ asn.interpret femtokernel_handler_entry_pre Σ.
    Admitted.

    Lemma femto_inv_mmio_split `{sailGS2 Σ} :
      femto_inv_mmio -∗
      @FemtoKernel.femto_inv_mmio _ sailGS2_sailGS_left
      ∗ @FemtoKernel.femto_inv_mmio _ sailGS2_sailGS_right.
    Proof. iIntros "($ & $)". Qed.

    #[local] Ltac destruct_seps :=
      repeat (iRename select (_ ∗ _)%I into "H'";
              iDestruct "H'" as "(? & ?)");
      repeat (iRename select (∃ _, _)%I into "H'";
              iDestruct "H'" as "(% & ?)");
      repeat (iRename select (_ ∗ _)%I into "H'";
              iDestruct "H'" as "(? & ?)").

    #[local] Ltac solve_split :=
      iIntros; cbn - [RiscvPmpIrisInstancePredicates.interp_ptstomem];
      unfold reg_pointsTo21, reg_pointsTo2, interp_ptstomem2;
      destruct_seps;
      repeat (iRename select (reg_pointsTo _ _)%I into "H'";
              iFrame "H'");
      repeat (iRename select (RiscvPmpIrisInstancePredicates.interp_ptstomem _ _)%I into "H'";
              iFrame "H'");
      repeat (iRename select (⌜_⌝ ∧ emp)%I into "H'";
              iDestruct "H'" as "[#H' _]";
              try iFrame "H'"; try iDestruct "H'" as "?");
      try (iRename select (interp_inv_mmio _) into "Hmmio";
           iDestruct "Hmmio" as "#Hmmio";
           iPoseProof (femto_inv_mmio_split with "Hmmio") as "($ & $)");
      repeat (iRename select (⌜_ = _⌝)%I into "Heq";
              iDestruct "Heq" as "->");
      auto.

    Lemma femtokernel_init_pre_binary_split `{sailGS2 Σ} (csrs : CSRVals) :
      let Σ := (CSRVals_Valuation csrs).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr] in
      asn.interpret femtokernel_init_pre Σ -∗
      asn_interpret_left femtokernel_init_pre Σ ∗
      asn_interpret_right femtokernel_init_pre Σ.
    Proof. solve_split. Qed.

    Lemma femtokernel_handler_entry_pre_binary_split `{sailGS2 Σ} (x5 x10 : Val ty_xlenbits) (csrs : CSRVals) :
      let Σ := (CSRVals_Valuation csrs).["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] in
      asn.interpret femtokernel_handler_entry_pre Σ -∗
      asn_interpret_left femtokernel_handler_entry_pre Σ ∗
      asn_interpret_right femtokernel_handler_entry_pre Σ.
    Proof. solve_split. Qed.

    Lemma femtokernel_handler_write_pre_binary_split `{sailGS2 Σ} (x5 : Val ty_xlenbits) (csrs : CSRVals) :
      let Σ := (CSRVals_Valuation csrs).["x5" ∷ ty_xlenbits ↦ x5].["a" ∷ ty_xlenbits ↦ bv.of_N handler_write_addr] in
      asn.interpret femtokernel_handler_write_pre Σ -∗
      asn_interpret_left femtokernel_handler_write_pre Σ ∗
      asn_interpret_right femtokernel_handler_write_pre Σ.
    Proof. solve_split. Qed.

    Lemma femtokernel_handler_secret_write_pre_binary_split `{sailGS2 Σ} (x1 secret1 secret2 : Val ty_xlenbits) (csrs : CSRVals) :
      let Σ__csrs := (CSRVals_Valuation csrs) in
      let Σ__x1   := [env].["x1" ∷ ty_xlenbits ↦ x1] in
      let Σ__a    := [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] in
      let Σ__secret secret := Σ__csrs ►► Σ__x1 ►► [env].["secret" ∷ ty_xlenbits ↦ secret] ►► Σ__a in
      asn.interpret femtokernel_handler_secret_write_pre_rel (Σ__csrs ►► Σ__x1 ►► Σ__a) ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
      asn_interpret_left femtokernel_handler_secret_write_pre (Σ__secret secret1) ∗
      asn_interpret_right femtokernel_handler_secret_write_pre (Σ__secret secret2).
    Proof. solve_split. Qed.

    Lemma femtokernel_handler_exit_pre_binary_split `{sailGS2 Σ} (csrs : CSRVals) :
      let Σ := (CSRVals_Valuation csrs).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] in
      asn.interpret femtokernel_handler_exit_pre Σ -∗
      asn_interpret_left femtokernel_handler_exit_pre Σ ∗
      asn_interpret_right femtokernel_handler_exit_pre Σ.
    Proof. solve_split. Qed.

    Lemma femtokernel_init_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (csrs : CSRVals) :
      let ι__csrs := CSRVals_Valuation csrs in
      let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N init_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_init_post (Σ na1) -∗
      asn_interpret_right femtokernel_init_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_init_post (Σ na1).
    Proof.
    Admitted.

    Lemma femtokernel_handler_post_binary_combine `{sailGS2 Σ} (x5 x10 na1 na2 : Val ty_xlenbits) (csrs : CSRVals) :
      let ι__csrs := CSRVals_Valuation csrs in
      let Σ na := ι__csrs.["x5"∷ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a"∷ty_xlenbits ↦ bv.of_N handler_entry_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_handler_entry_post (Σ na1) -∗
      asn_interpret_right femtokernel_handler_entry_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_entry_post (Σ na1).
    Proof.
    Admitted.

    Definition ptsto_instrs_handler2 `{sailGS2 Σ} : iProp Σ :=
      @ptsto_instrs_handler _ sailGS2_sailGS_left
      ∗ @ptsto_instrs_handler _ sailGS2_sailGS_right.

    Definition femtokernel_safe_shared_pre2 `{sailGS2 Σ} (addr : N) (b : Block) : iProp Σ :=
      exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User. (* Not needed for handler, but required for the rest of execution *)

    Lemma femtokernel_handler_exit_safe_rel `{sailGS2 Σ} (csrs : CSRVals) :
      ⊢ femtokernel_safe_shared_pre2 handler_exit_addr femtokernel_handler_exit ∗
        asn.interpret femtokernel_handler_exit_pre (CSRVals_Valuation csrs).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] ∗
        interp_gprs ∅ ∗
        ▷ (ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.Trap User (bv.of_N handler_entry_addr) femto_pmpentries -∗ WP2_loop)
        -∗
        WP2_loop.
    Admitted.

    Lemma femtokernel_handler_write_safe_rel `{sailGS2 Σ} (vx5 : Val ty_xlenbits) (csrs : CSRVals) :
      ⊢ femtokernel_safe_shared_pre2 handler_write_addr femtokernel_handler_write ∗
        asn.interpret femtokernel_handler_write_pre (CSRVals_Valuation csrs).["x5" ∷ ty_xlenbits ↦ vx5].["a" ∷ ty_xlenbits ↦ bv.of_N handler_write_addr] ∗
        interp_gprs {[x5]} ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (ptsto_instrs (bv.of_N handler_write_addr) (filter_AST femtokernel_handler_write) -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.Trap User (bv.of_N handler_entry_addr) femto_pmpentries -∗ WP2_loop)
        -∗
        WP2_loop.
    Admitted.

    Lemma femtokernel_handler_secret_write_safe_rel `{sailGS2 Σ} (vx1 secret1 secret2 : Val ty_xlenbits) (csrs : CSRVals) :
      ⊢ femtokernel_safe_shared_pre2 handler_secret_write_addr femtokernel_handler_secret_write ∗
        asn.interpret femtokernel_handler_secret_write_pre_rel (CSRVals_Valuation csrs).["x1" ∷ ty_xlenbits ↦ vx1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] ∗
        interp_gprs {[x1]} ∗
        interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
           interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.Trap User (bv.of_N handler_entry_addr) femto_pmpentries -∗ WP2_loop)
        -∗
        WP2_loop.
    Admitted.

    Lemma femtokernel_handler_entry_safe_rel `{sailGS2 Σ} (x5_val x10_val : Val ty_xlenbits) (csrs : CSRVals) :
      ⊢ femtokernel_safe_shared_pre2 handler_entry_addr femtokernel_handler_entry ∗
        asn.interpret femtokernel_handler_entry_pre (CSRVals_Valuation csrs).["x5" ∷ ty_xlenbits ↦ x5_val].["x10" ∷ ty_xlenbits ↦ x10_val].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] ∗
        interp_gprs {[ x1; x5; x10 ]} ∗
        (∃ v, x1 ↦ᵣ v) ∗
        (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) ∗
        ptsto_instrs (bv.of_N handler_write_addr) (filter_AST femtokernel_handler_write) ∗
        ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit)
        -∗
        WP2_loop.
    Admitted.

    Lemma memAdv_pmpPolicy_binary `{sailGS2 Σ} :
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

    Lemma femtokernel_manualStep2_rel `{sailGS2 Σ} :
      ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
        (mtvec ↦ᵣ (bv.of_N handler_entry_addr)) ∗
        (∃ v, mcause ↦ᵣ v) ∗
        (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        (∃ v, mepc ↦ᵣ v) ∗
        cur_privilege ↦ᵣ User ∗
        interp_gprs ∅ ∗
        interp_pmp_entries femto_pmpentries ∗
        femto_inv_mmio ∗
        (pc ↦ᵣ (bv.of_N adv_addr)) ∗
        (∃ v, nextpc ↦ᵣ v) ∗
        ptsto_instrs_handler2 ∗
        (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) ∗
        ptstoSthL advAddrs
        ={⊤}=∗
        ∃ mpp, LoopVerificationBinary.loop_pre User (bv.of_N handler_entry_addr) (bv.of_N adv_addr) mpp femto_pmpentries.
    Admitted.

    Lemma femtokernel_init_safe_rel `{sailGS2 Σ} (csrs : CSRVals) :
      ⊢ exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
        ∗ ptsto_instrs_handler2
        ∗ ptstoSthL advAddrs
        ∗ asn.interpret femtokernel_init_pre (CSRVals_Valuation csrs).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr]
        ∗ interp_gprs {[x1]}
        ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2)
        ∗ (∃ v, mscratch ↦ᵣ v)
        ∗ femto_inv_mmio (* This is not needed for the `init` code, but it is needed later on *)
          -∗
          WP2_loop.
    Proof.
      iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hdata & Hmscratch & #Hmem)".
      iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_init_pre _) _ _
                                      (λ a na, asn.interpret femtokernel_init_post (CSRVals_Valuation csrs).["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na])
               with "Hpro Hpre []").

      iIntros "Hpre".
      iPoseProof (femtokernel_init_pre_binary_split csrs with "Hpre") as "(Hpre1 & Hpre2)".
      iPoseProof (@contract_femtoinit_verified _ sailGS2_sailGS_left (bv.of_N init_addr) csrs with "Hpre1") as "H1".
      iPoseProof (@contract_femtoinit_verified _ sailGS2_sailGS_right (bv.of_N init_addr) csrs with "Hpre2") as "H2".
      iApply (step_n_focus with "H1 H2").
      iIntros (na1 na2) "(H1 & H2)".
      now iPoseProof (femtokernel_init_post_binary_combine with "H1 H2") as "(<- & $)".
      iIntros (an) "(Hpost & Hepi)".
      cbn - [asn_regs_ptsto interp_pmp_entries].
      iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hcurpriv & Hx1 & Hpmpentries)".
      iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        now iFrame "Hx1 Hgprs". }
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      rewrite ?bv.add_zero_l.
      iApply (fupd_semWP2 ⊤).
      iMod (femtokernel_manualStep2_rel with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hgprs $Hcurpriv $Hpmpentries $Hpc $Hnpc $Hmepc $Hmem $Hhandler $Hdata $Hadv]") as "[%mpp Hlooppre]".
      iModIntro.
      iPoseProof (LoopVerificationBinary.valid_semTriple_loop with "Hlooppre") as "Hk".
      iApply (semWP2_mono with "Hk"); auto.
      iIntros (? ? ? ?) "(<- & <- & ?)"; iPureIntro; auto.
    Qed.

    Import IrisInstanceBinary.RiscvPmpIrisAdeqParams2.

    Lemma intro_ptstoSthL_binary `{sailGS2 Σ} (μ : Memory) (addrs : list Xlenbits)  :
      let memGS_left  := @sailGS_memGS _ sailGS2_sailGS_left in
      let memGS_right := @sailGS_memGS _ sailGS2_sailGS_right in
      ([∗ list] a' ∈ addrs, @RiscvPmpIrisInstancePredicates.interp_ptsto _ memGS_left a' ((memory_ram μ) a'))
      ∗ ([∗ list] a' ∈ addrs, @RiscvPmpIrisInstancePredicates.interp_ptsto _ memGS_right a' ((memory_ram μ) a'))
      ⊢ ptstoSthL addrs.
    Proof.
      induction addrs as [|a l]; cbn; auto.
      iIntros "[[Hmemal Hmeml] [Hmemar Hmemr]]".
      iSplitL "Hmemal Hmemar".
      - iExists ((memory_ram μ) a). iFrame "Hmemal Hmemar".
      - iApply IHl. iFrame "Hmeml Hmemr".
    Qed.

    Definition mem_has_instrs2 (μ1 μ2 : Memory) (a : Val ty_word)
      (instrs : list AST) : Prop :=
      mem_has_instrs μ1 a instrs ∧ mem_has_instrs μ2 a instrs.

    Lemma femtokernel_splitMemory_rel `{sailGS2 Σ} {μ1 μ2 : Memory} (secret1 secret2 : Val ty_xlenbits) :
      mem_has_instrs2 μ1 μ2 (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_entry_addr) (filter_AnnotInstr_AST femtokernel_handler_entry) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_write_addr) (filter_AnnotInstr_AST femtokernel_handler_write) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_secret_write_addr) (filter_AnnotInstr_AST femtokernel_handler_secret_write) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_exit_addr) (filter_AnnotInstr_AST femtokernel_handler_exit) ->
      mem_has_word μ1 (bv.of_N data_addr) secret1 ->
      mem_has_word μ2 (bv.of_N data_addr) secret2 ->
      mmio_pred bytes_per_word (memory_trace μ1) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      mmio_pred bytes_per_word (memory_trace μ2) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      Forall (λ a, memory_ram μ1 a = memory_ram μ2 a) advAddrs -> (* We require that the memory the adversary can access is indistinguishable in the left and right memory *)
      @mem_res2 _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
        ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
        ptsto_instrs_handler2 ∗
        interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
        femto_inv_mmio ∗
        ptstoSthL advAddrs.
    Proof.
      iIntros ([Hinit1 Hinit2] [Hhentry1 Hhentry2] [Hhwrite1 Hhwrite2] [Hhsecret1 Hhsecret2] [Hhexit1 Hhexit2] Hdata1 Hdata2 Hft1 Hft2 Hadv) "Hmem".
      iDestruct "Hmem" as "(Hmem1 & Hmem2)".
      iPoseProof (@femtokernel_splitMemory _ sailGS2_sailGS_left _ _ Hinit1 Hhentry1 Hhwrite1 Hhsecret1 Hhexit1 Hdata1 Hft1 with "Hmem1") as "H1".
      iPoseProof (@femtokernel_splitMemory _ sailGS2_sailGS_right _ _ Hinit2 Hhentry2 Hhwrite2 Hhsecret2 Hhexit2 Hdata2 Hft2 with "Hmem2") as "H2".
      iMod "H1" as "(Hinit1 & Hhandler1 & Hdata1 & Hinv1 & Hadv1)".
      iMod "H2" as "(Hinit2 & Hhandler2 & Hdata2 & Hinv2 & Hadv2)".
      unfold ptsto_instrs_handler2, interp_ptstomem2.
      rewrite ptsto_instrs_equiv.
      iCombine "Hinit1" "Hinit2" as "Hinit".
      iCombine "Hhandler1" "Hhandler2" as "Hhandler".
      iCombine "Hdata1" "Hdata2" as "Hdata".
      iFrame "Hinit Hhandler Hdata".
      iSplitL "Hinv1 Hinv2".
      - by iFrame "Hinv1 Hinv2".
      - unfold ptstoSthL, RiscvPmpIrisInstancePredicates.ptstoSthL,
          RiscvPmpIrisInstancePredicates.ptstoSth.
        iPoseProof (big_sepL_impl _ (λ k v, v ↦ₘ (memory_ram μ1 v))
                     with "Hadv2 []") as "Hadv2".
        { iModIntro. iIntros (k v HIn) "H".
          pose proof (Forall_lookup_1 _ _ _ _ Hadv HIn) as Heq.
          simpl in Heq. now rewrite Heq. }
        iApply (intro_ptstoSthL_binary with "[$Hadv1 $Hadv2]").
    Qed.

    Lemma femtokernel_rel_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ1' μ2 : Memory}
      {δ1 δ1' δ2 : CStore [ctx]} {m1 : string} {secret1 secret2 : Val ty_xlenbits} :
      mem_has_instrs2 μ1 μ2 (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_entry_addr) (filter_AnnotInstr_AST femtokernel_handler_entry) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_write_addr) (filter_AnnotInstr_AST femtokernel_handler_write) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_secret_write_addr) (filter_AnnotInstr_AST femtokernel_handler_secret_write) ->
      mem_has_instrs2 μ1 μ2 (bv.of_N handler_exit_addr) (filter_AnnotInstr_AST femtokernel_handler_exit) ->
      mem_has_word μ1 (bv.of_N data_addr) secret1 ->
      mem_has_word μ2 (bv.of_N data_addr) secret2 ->
      Forall (λ a : Addr, memory_ram μ1 a = memory_ram μ2 a) advAddrs -> (* We assume that the memory the adv has access to, before executing the kernel, contains the same values *)
      mmio_pred bytes_per_word (memory_trace μ1) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      mmio_pred bytes_per_word (memory_trace μ2) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      (∀ {σ : Ty} (r : Reg σ), read_register γ1 r = read_register γ2 r) -> (* We require that the initial values of all registers are the same, as we consider these to be public. The secrets in our verification are part of MMIO. *)
      read_register γ1 mstatus = {| MPP := User; MPIE := false; MIE := false |} ->
      read_register γ1 cur_privilege = Machine ->
      read_register γ1 pmp0cfg = default_pmpcfg_ent ->
      read_register γ1 pmpaddr0 = bv.zero ->
      read_register γ1 pmp1cfg = default_pmpcfg_ent ->
      read_register γ1 pmpaddr1 = bv.zero ->
      read_register γ1 pc = bv.of_N init_addr ->
      (* We require termination of the executions by using the fail statement.
         The proper shutdown is part of mmio_pred_final as an event, and when
         such a shutdown event is triggered, we step to fail.
         The IOShutdown event allows an "exit value" to be written, but we
         simply ignore it, same for the message of the fail statement. *)
      ⟨ γ1, μ1, δ1, fun_loop ⟩ --->* ⟨ γ1', μ1', δ1', fail m1 ⟩ ->
      ∃ γ2' μ2' δ2' s2',
        ⟨ γ2, μ2, δ2, fun_loop ⟩ --->* ⟨ γ2', μ2', δ2', s2' ⟩
        (* The initial demands hold over the final states *)
        ∧ mmio_pred_final bytes_per_word (memory_trace μ1') ∧ mmio_pred_final bytes_per_word (memory_trace μ2').
    Proof.
      intros μinit μhentry μhwrite μhsecret μhexit μdata1 μdata2 μadv μft1 μft2 γeq γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc steps1.
      eapply (wp2_strong_adequacy fun_loop γ2 μ2 δ2 steps1 (Q := fun _ _ v1 δ1' v2 δ2' => ⌜v1 = v2⌝ ∗ ⌜δ1' = δ2'⌝ ∗ femto_inv_mmio)%I); auto.
      iIntros (Σ sg).
      iSplitL.
      - iIntros "(Hmem & Hregs)".
           iMod (@femtokernel_splitMemory_rel _ _ _ _ secret1 secret2 with "Hmem") as "(Hinit & Hhandler & Hdata & #Hmmio & Hadv)";
             try assumption.
           destruct (env.view δ1), (env.view δ2).

           iPoseProof (femtokernel_init_safe_rel {|
                    vmtvec  := read_register γ1 mtvec;
                    vmcause := read_register γ1 mcause;
                    vmepc   := read_register γ1 mepc;
                    vmie    := read_register γ1 mie;
                    vmip    := read_register γ1 mip;
                     |}
                    with "[-]") as "H".
           { #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
             iFrame "∗ #". cbn - [interp_gprs].
             rewrite <- ?γeq.
             rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc.
             iDestruct "Hregs" as "($ & $ & Hregs)".
             rewrite <- ?bi.sep_assoc.
             iSplitR; first auto.
             rewrite <- ?bi.sep_assoc.
             repeat first [iDestruct "Hregs" as "($ & Hregs)"
                          | iDestruct "Hregs" as "(? & Hregs)"].
             unfold interp_gprs; reduce_big_sepS_big_sepL; cbn.
             iAssert (□ ∀ r v, (reg_pointsTo2 r v v -∗ ∃ v, reg_pointsTo21 r v))%I as "#Heq".
             { iModIntro. iIntros (? v) "H". iExists v. iFrame "H". }
             repeat try (iRename select (reg_pointsTo2 _ _ _) into "Hpts";
                         iPoseProof ("Heq" with "Hpts") as "Hpts";
                         iFrame "Hpts"). }
        iApply (semWP2_mono with "H").
        iFrame "Hmmio". iPureIntro; simpl; now intros.
      - iIntros (γ2' μ2' δ2' s2' v2 steps2 Hval) "(<- & -> & Hmmio) Hmem".
        iExists γ2', μ2', δ2', s2'.
        iDestruct "Hmem" as "[(%memmap1 & Hinv1 & %link1 & Htr1)
                              (%memmap2 & Hinv2 & %link2 & Htr2)]".

        admit.

        (* iDestruct "Hmmio" as "(Hmmio1 & Hmmio2)". *)
        (* iInv "Hmmio1" as ">(%t1 & Hfrag1 & %Hpred1)" "Hclose1". *)
        (* iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->". *)
        (* iSpecialize ("Hclose1" with "[Htr1]"). *)
        (* { iModIntro. iExists t1. admit. } *)

        (* iInv "Hmmio" as ">((%t1 & Hfrag1 & Hpred1) & (%t2 & Hfrag2 & Hpred2))" "_". *)
        (* iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->". *)
        (* iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->". *)
        (* iApply fupd_mask_intro; first set_solver. *)
        (* iIntros "_". iSplitR; auto. *)
        (* unfold mmio_pred_final. *)
        (* TODO
           - [ ] Require that a MMIOShutdown is issued at some point? There
                 are other possibilities to run into a [fail m], this might
                 give an issue here with mmio_pred_final.
           ODOT *)
    Admitted.

  End RelationalVerification.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
