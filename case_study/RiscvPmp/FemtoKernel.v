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

From Stdlib Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Base
     Bitvector
     Notations
     SmallStep.Step
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.TotalVerifier
     RiscvPmp.BlockVer.BinaryVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.
From Katamaran Require Import
  RiscvPmp.Contracts
  RiscvPmp.LoopVerification
  RiscvPmp.LoopVerificationBinary
  RiscvPmp.Model
  RiscvPmp.Everything
  RiscvPmp.UnaryAdequacy.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
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
Import iris.proofmode.proofmode.

Import MicroSail.ShallowExecutor.

Import Contracts.
Import Assembly.
Import ArchState (ArchState).

Locate RVPBASEl.
Import RVPCOM.
Import RVPV2.
Import RVPINST2.
Import RVPBASE2.
Import RVPPRED2.

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
    (* The system call number (passed in mmio_write_arg_reg, i.e. a0) with which
       U-mode asks the trap handler to power off the machine. The handler
       interprets a0 as follows:
       - mmio_write_adv: the public MMIO write, which also logs the secret
         (dispatch, not_zero and is_zero blocks);
       - shutdown_code: power off the machine (shutdown_check and shutdown blocks);
       - any other value: the secret write (secret_write block).
       The value 1 is arbitrary, but it must differ from mmio_write_adv (which
       is checked first) and fit in the 12-bit immediate of an ADDI. We avoid 0,
       as that is the value of a0 when U-mode does not set an argument. *)
    Definition shutdown_code : N := 1.

    Definition pure_privilege_to_bits {n} : Privilege -> bv n :=
      fun p => match p with | Machine => bv.of_N 3 | Supervisor => bv.one | User => bv.zero end.

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
             then (bv.of_Z (bv.unsigned lo - 4096), (hi + bv.one)%bv)
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
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero;  exp_val ty_regno t0]%env (* TODO: notation to avoid lemma call copying LOAD instruction/internalize immediate as well?*)
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
         -> Jumps to femtokernel_handler_shutdown_check_asm
         -> OR falls through to femtokernel_handler_dispatch_asm
       - femtokernel_handler_dispatch_asm
         -> Jumps to femtokernel_handler_is_zero_asm if the secret is zero
         -> OR falls through to femtokernel_handler_not_zero_asm
       - femtokernel_handler_not_zero_asm
         -> ALWAYS jumps to femtokernel_handler_exit_asm
       - femtokernel_handler_is_zero_asm
         -> ALWAYS jumps to femtokernel_handler_exit_asm
       - femtokernel_handler_shutdown_check_asm
         -> Jumps to femtokernel_handler_secret_write_asm
         -> OR falls through to femtokernel_handler_shutdown_asm
       - femtokernel_handler_shutdown_asm
         -> Powers off the machine. End of execution.
       - femtokernel_handler_secret_write_asm
         -> ALWAYS falls through to femtokernel_exit_asm
       - femtokernel_handler_exit_asm
         -> Jumps back to U-mode (MRET). End of handler code. *)
    Example femtokernel_handler_entry_asm (handler_skip_size : N) : list AnnotInstr :=
      [ ADDI t0 zero (bv.of_N mmio_write_adv)
      ; BNE mmio_write_arg_reg t0 (bv.of_N (handler_skip_size + N.of_nat bytes_per_instr)) (* If the requested write argument is not one the trap invoker can write to, we need to jump over (hence the + bytes_per_instr) the dispatch, not_zero and is_zero blocks. *)
      ].

    (* Perform the requested MMIO write on behalf of U-mode (the public
       acknowledgement, writing 42 to the adversary-visible MMIO address), and
       log the secret to the M-mode only MMIO address. The order in which both
       writes happen depends on the secret: if it is zero, the secret is logged
       first (is_zero block), otherwise the acknowledgement happens first (not_zero
       block). Both orders result in the same adversary-observable trace, but
       the two executions differ in their control flow. *)
    Example femtokernel_handler_dispatch_asm' (data_addr not_zero_size : N) : list ASM :=
      [ UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
      ; BEQ ra zero (bv.of_N (not_zero_size + N.of_nat bytes_per_instr)) (* Jump over the not_zero block if the secret is zero. *)
      ].
    Example femtokernel_handler_dispatch_asm (dispatch_addr data_addr not_zero_size : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_dispatch_asm' data_addr not_zero_size) dispatch_addr.

    (* First performs the public write, then the private write. *)
    Example femtokernel_handler_not_zero_asm' (data_addr exit_addr : N) : list ASM :=
      [ ADDI t0 zero (bv.of_N 42)
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_adv) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno t0]%env
      ; STORE (bv.of_N mmio_write_adv) t0 zero WORD (* works because mmio_write_adv fits into 12 bits. *)
      ; UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno ra]%env
      ; STORE (bv.of_N mmio_write_addr) ra zero WORD
      ; ADD ra zero zero (* We need to clear ra, as it contains the secret *)
      ; RISCV_JALR (bv.of_N exit_addr) zero zero (* works because the exit block addr fits into 12 bits *)
      ].
    Example femtokernel_handler_not_zero_asm (not_zero_addr data_addr exit_addr : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_not_zero_asm' data_addr exit_addr) not_zero_addr.

    (* First performs the private write, then the public write. *)
    Example femtokernel_handler_is_zero_asm' (data_addr exit_addr : N) : list ASM :=
      [ UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno ra]%env
      ; STORE (bv.of_N mmio_write_addr) ra zero WORD
      ; ADDI t0 zero (bv.of_N 42)
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_adv) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno t0]%env
      ; STORE (bv.of_N mmio_write_adv) t0 zero WORD
      ; ADD ra zero zero (* We need to clear ra, as it contains the secret *)
      ; RISCV_JALR (bv.of_N exit_addr) zero zero
      ].
    Example femtokernel_handler_is_zero_asm (is_zero_addr data_addr exit_addr : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_is_zero_asm' data_addr exit_addr) is_zero_addr.

    (* Checks whether the trap invoker requests to power off the machine, by
       passing shutdown_code as argument. If so, we fall through to the shutdown
       block, otherwise we jump over it to the secret write. In both cases, the
       shutdown address is prepared in t0 (it does not fit in a 12-bit
       immediate, hence the two ADDIs).
       NOTE: preparing t0 here, rather than in the shutdown block itself, is a
       limitation of WP2_loop_semTripleBlock_power_off, which only supports a
       block of a single instruction: the power tokens are handed to the block
       after the power check that precedes its (only) instruction, so they
       are not available for the power checks in between the instructions of
       a longer block. Lifting this would require a variant of that lemma for
       blocks `instrs ++ [instr]`, where only the final instruction uses the
       power tokens. *)
    Example femtokernel_handler_shutdown_check_asm (shutdown_size : N) : list AnnotInstr :=
      [ ADDI t0 zero (bv.of_N 2047)
      ; ADDI t0 t0 (bv.of_N 1021) (* t0 = mmioShutdownAddr *)
      ; ADDI ra zero (bv.of_N shutdown_code)
      ; BNE mmio_write_arg_reg ra (bv.of_N (shutdown_size + N.of_nat bytes_per_instr))
      ].

    (* Powers off the machine, with exit value 0. *)
    Example femtokernel_handler_shutdown_asm : list AnnotInstr :=
      [ AnnotLemmaInvocation (close_mmio_write (bv.of_N 0) WORD) [nenv exp_val ty_xlenbits mmioShutdownAddr; exp_val ty_regno zero]%env
      ; STORE (bv.of_N 0) zero t0 WORD
      ].

    (* Performs a "secret" MMIO write. The secret itself is read from the
       `data` address and then written to the MMIO address.
       Block falls through to femtokernel_handler_exit_asm. *)
    Example femtokernel_handler_secret_write_asm' (data_addr : N) : list ASM :=
      [ UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, LOAD (bv.of_N (data_addr - (x - 4))) ra ra false WORD
      ; AnnotLemmaInvocation (close_mmio_write (bv.of_N mmio_write_addr) WORD) [nenv exp_val ty_xlenbits bv.zero; exp_val ty_regno t0]%env 
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
    Definition handler_dispatch     : Label := "handler_dispatch".
    Definition handler_not_zero     : Label := "handler_not_zero".
    Definition handler_is_zero      : Label := "handler_is_zero".
    Definition handler_shutdown_check : Label := "handler_shutdown_check".
    Definition handler_shutdown     : Label := "handler_shutdown".
    Definition handler_secret_write : Label := "handler_secret_write".
    Definition handler_exit         : Label := "handler_exit".

    Definition femtokernel_block_layout : list (Label * Block) :=
      [ (init                 , femtokernel_init' 0 0 0)
      ; (handler_entry        , femtokernel_handler_entry_asm 0)
      ; (handler_dispatch     , femtokernel_handler_dispatch_asm 0 0 0)
      ; (handler_not_zero     , femtokernel_handler_not_zero_asm 0 0 0)
      ; (handler_is_zero      , femtokernel_handler_is_zero_asm 0 0 0)
      ; (handler_shutdown_check, femtokernel_handler_shutdown_check_asm 0)
      ; (handler_shutdown     , femtokernel_handler_shutdown_asm)
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
      block_size ∘ filter_AST.

    Definition femtokernel_block_sizes : list (Label * N) :=
      map_with_label annot_block_size femtokernel_block_layout.

    (* SIZES *)
    Definition init_size : N := find_label init femtokernel_block_sizes 0%N.
    Definition handler_entry_size : N := find_label handler_entry femtokernel_block_sizes 0%N.
    Definition handler_dispatch_size : N := find_label handler_dispatch femtokernel_block_sizes 0%N.
    Definition handler_not_zero_size : N := find_label handler_not_zero femtokernel_block_sizes 0%N.
    Definition handler_is_zero_size : N := find_label handler_is_zero femtokernel_block_sizes 0%N.
    Definition handler_shutdown_check_size : N := find_label handler_shutdown_check femtokernel_block_sizes 0%N.
    Definition handler_shutdown_size : N := find_label handler_shutdown femtokernel_block_sizes 0%N.
    Definition handler_secret_write_size : N := find_label handler_secret_write femtokernel_block_sizes 0%N.
    Definition handler_exit_size : N := find_label handler_exit femtokernel_block_sizes 0%N.
    Definition handler_size : N := handler_entry_size + handler_dispatch_size + handler_not_zero_size + handler_is_zero_size + handler_shutdown_check_size + handler_shutdown_size + handler_secret_write_size + handler_exit_size.

    (* addrs_for_blocks returns a list of the same length as the given list of
       blocks, but with the address each block is located at. An initial address
       needs to be given for the first block, and all other blocks will be
       placed in sequence after another. *)
    Definition addrs_for_blocks (bs : list (Label * list AST)) (init_addr : N) : list (Label * N) :=
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
      addrs_for_blocks (map_with_label filter_AST femtokernel_block_layout) init_addr.

    (* Note that we need to use "Eval compute in ..." for all addresses.
       In proofs below, we often use cbn/simpl/..., which will hang if we
       don't compute here. *)
    Definition handler_entry_addr        : N :=
      Eval compute in find_label handler_entry femtokernel_block_addrs 0%N.
    Definition handler_dispatch_addr     : N :=
      Eval compute in find_label handler_dispatch femtokernel_block_addrs 0%N.
    Definition handler_not_zero_addr          : N :=
      Eval compute in find_label handler_not_zero femtokernel_block_addrs 0%N.
    Definition handler_is_zero_addr         : N :=
      Eval compute in find_label handler_is_zero femtokernel_block_addrs 0%N.
    Definition handler_shutdown_check_addr : N :=
      Eval compute in find_label handler_shutdown_check femtokernel_block_addrs 0%N.
    Definition handler_shutdown_addr     : N :=
      Eval compute in find_label handler_shutdown femtokernel_block_addrs 0%N.
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
    Local Abbreviation asn_femto_pmpentries a :=
      ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
        (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)))])%list.
    (* TODO: this notation should already be defined elsewhere, but it's not available here... Find the module where it's defined and import it. *)
    Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).

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

    Definition femtokernel_handler_entry := femtokernel_handler_entry_asm (handler_dispatch_size + handler_not_zero_size + handler_is_zero_size).
    Definition femtokernel_handler_dispatch := femtokernel_handler_dispatch_asm handler_dispatch_addr data_addr handler_not_zero_size.
    Definition femtokernel_handler_not_zero := femtokernel_handler_not_zero_asm handler_not_zero_addr data_addr handler_exit_addr.
    Definition femtokernel_handler_is_zero := femtokernel_handler_is_zero_asm handler_is_zero_addr data_addr handler_exit_addr.
    Definition femtokernel_handler_shutdown_check := femtokernel_handler_shutdown_check_asm handler_shutdown_size.
    Definition femtokernel_handler_shutdown := femtokernel_handler_shutdown_asm.
    Definition femtokernel_handler_secret_write := femtokernel_handler_secret_write_asm handler_secret_write_addr data_addr.
    Definition femtokernel_handler_exit := femtokernel_handler_exit_asm.

    Import RiscvPmp.Sig.
    #[local] Abbreviation asn_inv_mmio := (asn.chunk (chunk_user (inv_mmio bytes_per_word) [env])). (* Fix word length at 4 for this example, as we do not perform any other writes*)
    #[local] Abbreviation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    #[local] Abbreviation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Definition post_mip_val : Val ty_Minterrupts :=
      MkMinterrupts false false false false false false false false false.
    Definition term_post_mip_val {Σ} : Term Σ ty_Minterrupts :=
      term_val ty_Minterrupts post_mip_val.

    Definition Σ__csrs : LCtx :=
      ["mtvec" :: ty_xlenbits;
       "mcause" :: ty_xlenbits;
       "mepc" :: ty_xlenbits;
       "mie" :: ty_Minterrupts;
       "mstatus_mpie" :: ty.bool;
       "mstatus_mpp" :: ty_privilege;
       "mstatus_spp" :: ty_privilege;
       "mstatus_spie" :: ty.bool;
       "mstatus_sie" :: ty.bool;
       "mideleg" :: ty_Minterrupts;
       "medeleg" :: ty_Medeleg;
       "scause" :: ty_xlenbits;
       "sscratch" :: ty_xlenbits;
       "sepc" :: ty_xlenbits;
       "stvec" :: ty_xlenbits].

    Definition csrs_valuation (archstate : ArchState) (vmie : Val ty_Minterrupts) : Valuation Σ__csrs :=
      let ms := ArchState.mstate archstate in
      let ss := ArchState.sstate archstate in
      [env]
        .["mtvec" ∷ ty_xlenbits ↦ ArchState.mtvec ms]
        .["mcause" ∷ ty_xlenbits ↦ ArchState.mcause ms]
        .["mepc" ∷ ty_xlenbits ↦ ArchState.mepc ms]
        .["mie" ∷ ty_Minterrupts ↦ vmie]
        .["mstatus_mpie" ∷ ty.bool ↦ ArchState.mpie ms]
        .["mstatus_mpp" ∷ ty_privilege ↦ ArchState.mpp ms]
        .["mstatus_spp" ∷ ty_privilege ↦ S_SPP (ArchState.sstatus ss)]
        .["mstatus_spie" ∷ ty.bool ↦ S_SPIE (ArchState.sstatus ss)]
        .["mstatus_sie" ∷ ty.bool ↦ S_SIE (ArchState.sstatus ss)]
        .["mideleg" ∷ ty_Minterrupts ↦ ArchState.mideleg ms]
        .["medeleg" ∷ ty_Medeleg ↦ ArchState.medeleg ms]
        .["scause" ∷ ty_xlenbits ↦ ArchState.scause ss]
        .["sscratch" ∷ ty_xlenbits ↦ ArchState.sscratch ss]
        .["sepc" ∷ ty_xlenbits ↦ ArchState.sepc ss]
        .["stvec" ∷ ty_xlenbits ↦ ArchState.stvec ss].

    Section WithAsnNotations.
      Import asn.notations.
      Import TermNotations.

      Example femtokernel_init_pre : Assertion (Σ__csrs ▻▻ ["a"::ty_xlenbits]) :=
        (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
          mtvec ↦ term_var "mtvec" ∗
          mcause ↦ term_var "mcause" ∗
          (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
          mepc ↦ term_var "mepc" ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false] ∗
      mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
      medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
          cur_privilege ↦ term_val ty_privilege Machine ∗
          (∃ "x1", x1 ↦ term_var "x1") ∗
          (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                       (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])).

      Example femtokernel_init_post : Assertion (Σ__csrs ▻▻ ["a"::ty_xlenbits; ("an"::ty_xlenbits)]) :=
        (
          (term_var "an" = term_var "a" +ᵇ (term_val ty_xlenbits (bv.of_N adv_addr)))%asn ∗
            (mtvec ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)) ∗
            mcause ↦ term_var "mcause" ∗
            mip ↦ term_post_mip_val ∗ mie ↦ term_var "mie" ∗
            mepc ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N adv_addr) ∗
          mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool true; term_val ty.bool false; term_val ty.bool true; term_val ty.bool false ] ∗
          mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
          medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
            cur_privilege ↦ term_val ty_privilege User ∗
            x1 ↦ term_val ty_xlenbits [bv 0x80] ∗
            asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a")))
        ).

      Definition femtokernel_handler_shared_pre (addr : N) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
        (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_entry_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
          term_var "a" = term_val ty_xlenbits (bv.of_N addr) ∗
          cur_privilege ↦ term_val ty_privilege Machine ∗
          (mtvec ↦ term_val ty_word (bv.of_N handler_entry_addr)) ∗
          mcause ↦ term_var "mcause" ∗
          (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
          mepc ↦ term_var "mepc" ∗
          sepc ↦ term_var "sepc" ∗
          scause ↦ term_var "scause" ∗
          sscratch ↦ term_var "sscratch" ∗
          stvec ↦ term_var "stvec" ∗
          mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
          medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
          asn_pmp_entries term_femto_pmpentries ∗
          (* asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)))) ∗ (* Different handler sizes cause different entries *) *)
          asn_inv_mmio.

      Definition femtokernel_handler_shared_post (priv : Term (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) ty_privilege) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
        cur_privilege ↦ priv ∗
          mtvec ↦ term_val ty_word (bv.of_N handler_entry_addr) ∗
          mcause ↦ term_var "mcause" ∗
          mip ↦ term_post_mip_val ∗ mie ↦ term_var "mie" ∗
          mepc ↦ term_var "mepc" ∗
          sepc ↦ term_var "sepc" ∗
          scause ↦ term_var "scause" ∗
          sscratch ↦ term_var "sscratch" ∗
          stvec ↦ term_var "stvec" ∗
          mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
          medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
          asn_pmp_entries term_femto_pmpentries.
      (* asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)))). (* Different handler sizes cause different entries *) *)

      Example femtokernel_handler_entry_pre : Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_entry_addr) (sub_up1 (sub_cat_left _)) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          x5 ↦ term_var "x5" ∗
          x10 ↦ term_var "x10".

      Example femtokernel_handler_entry_post :
        Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          (if: (term_var "x10" ?= term_val ty_xlenbits (bv.of_N mmio_write_adv))
           then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_entry_size)
           else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_entry_size + handler_dispatch_size + handler_not_zero_size + handler_is_zero_size))) ∗
          x5 ↦ term_val ty_xlenbits (bv.of_N mmio_write_adv) ∗
          x10 ↦ term_var "x10".

      Example femtokernel_handler_dispatch_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_dispatch_addr) (sub_up1 (sub_cat_left _)) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          x1 ↦ term_var "x1" ∗
          term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

      Example femtokernel_handler_dispatch_post :
        Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          (if: (term_var "secret" ?= term_val ty_xlenbits bv.zero)
           then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_dispatch_size + handler_not_zero_size))
           else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_dispatch_size)) ∗
          x1 ↦ term_var "secret" ∗
          term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

      (* The not_zero and is_zero blocks share their contract (modulo their address):
         both perform the (only) observable write of the handler, and log the
         secret to the M-mode only MMIO address. *)
      Definition femtokernel_handler_ack_pre (addr : N) : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre addr) (sub_up1 (sub_cat_left _)) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          asn.chunk (chunk_user nothingPending env.nil) ∗
          x1 ↦ term_var "x1" ∗
          x5 ↦ term_var "x5" ∗
          term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

      Example femtokernel_handler_ack_post :
        Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          term_var "an" = term_val ty_xlenbits (bv.of_N handler_exit_addr) ∗
          x1 ↦ term_val ty_xlenbits bv.zero ∗
          x5 ↦ term_val ty_xlenbits (bv.of_N 42) ∗
          term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret" ∗
          (* The (only) observable write of the handler. The event is fully
             determined, so that both executions agree on it. *)
          asn.chunk (chunk_user (written bytes_per_word)
                       [term_val ty_xlenbits (bv.of_N mmio_write_adv);
                        term_val (ty_bytes bytes_per_word) (bv.of_N 42)]).

      Example femtokernel_handler_not_zero_pre := femtokernel_handler_ack_pre handler_not_zero_addr.
      Example femtokernel_handler_is_zero_pre := femtokernel_handler_ack_pre handler_is_zero_addr.

      Example femtokernel_handler_secret_write_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_secret_write_addr) (sub_up1 (sub_cat_left _)) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          x1 ↦ term_var "x1" ∗
          term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

      Example femtokernel_handler_secret_write_post :
        Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_secret_write_size) ∗
                                          x1 ↦ term_val ty_xlenbits bv.zero ∗
                                          term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

      Example femtokernel_handler_shutdown_check_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_shutdown_check_addr) (sub_up1 (sub_cat_left _)) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          x1 ↦ term_var "x1" ∗
          x5 ↦ term_var "x5" ∗
          x10 ↦ term_var "x10".

      Example femtokernel_handler_shutdown_check_post :
        Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
          (if: (term_var "x10" ?= term_val ty_xlenbits (bv.of_N shutdown_code))
           then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_shutdown_check_size)
           else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_shutdown_check_size + handler_shutdown_size))) ∗
          x1 ↦ term_val ty_xlenbits (bv.of_N shutdown_code) ∗
          x5 ↦ term_val ty_xlenbits mmioShutdownAddr ∗
          x10 ↦ term_var "x10".

      (* Powering off the machine is observable by the adversary, and requires
         that the machine is still powered on. The power tokens are kept apart
         from the rest of the pre- and postcondition, as the relational
         verification hands them to the block separately. *)
      Example femtokernel_handler_shutdown_pre : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
        (femtokernel_handler_shared_pre handler_shutdown_addr ∗
           mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
           x5 ↦ term_val ty_xlenbits mmioShutdownAddr ∗
           asn.chunk (chunk_user nothingPending env.nil)) ∗
          asn.chunk (chunk_user Sig.powered [term_val ty.bool true]).

      Example femtokernel_handler_shutdown_post :
        Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        (term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_shutdown_size) ∗
           asn.chunk (chunk_user (Sig.written_shutdown bytes_per_word)
                        [term_val ty_xlenbits mmioShutdownAddr; term_val (ty_bytes bytes_per_word) bv.zero])) ∗
          asn.chunk (chunk_user Sig.powered [term_val ty.bool false]).

      Example femtokernel_handler_exit_pre : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
        femtokernel_handler_shared_pre handler_exit_addr ∗
          mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"].

      Example femtokernel_handler_exit_post :
        Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        femtokernel_handler_shared_post (term_var "mstatus_mpp") ∗
          mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_spp"; term_val ty.bool true; term_var "mstatus_spie"; term_var "mstatus_mpie"; term_var "mstatus_sie"] ∗
          term_var "an" = term_var "mepc".

    End WithAsnNotations.

      (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
      (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
      (*   Eval vm_compute in *)
      (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

      Definition vc__gen {Σ : LCtx} (pre : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
        (instrs : list AnnotInstr)
        (post : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits))
        : (Assertion (Σ ▻ "a"∷ty_xlenbits) → list AnnotInstr → Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) → Valid (λ Σ : World, 𝕊 Σ)) → 𝕊 [] :=
        fun sannotated_block_verification_condition =>
          postprocess2 (sannotated_block_verification_condition pre instrs post wnil).

    Definition vc__femtoinit__gen :=
      vc__gen femtokernel_init_pre femtokernel_init_gen femtokernel_init_post.

    Definition vc__femtoinit : 𝕊 [] :=
      vc__femtoinit__gen RVPTVl.sannotated_block_verification_condition.

    (* NOTE: For now this proof covers both the MMIO and non-MMIO Femtokernel variants, since the start of the adversary region is the same in both cases.
       If this were not the case, we would take a naive approach to verifying both versions of the initialization code here; we would require that `adv_start` takes one of the two values present in the two versions of the initialization code.
       A more general approach would verify the contract under a logical value for `adv_start`.
       This would require the block verifier to support taking a list of instructions that can depend on symbolic values as input (i.e. proper terms).
     *)
    Lemma sat__femtoinit : RVPTVl.safeE vc__femtoinit.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

    Definition vc__femtohandler_entry : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_entry_pre
                     femtokernel_handler_entry
                     femtokernel_handler_entry_post wnil).

    Definition vc__femtohandler_dispatch : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_dispatch_pre
                     femtokernel_handler_dispatch
                     femtokernel_handler_dispatch_post wnil).

    Definition vc__femtohandler_not_zero : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_not_zero_pre
                     femtokernel_handler_not_zero
                     femtokernel_handler_ack_post wnil).

    Definition vc__femtohandler_is_zero : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_is_zero_pre
                     femtokernel_handler_is_zero
                     femtokernel_handler_ack_post wnil).

    Definition vc__femtohandler_secret_write : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_secret_write_pre
                     femtokernel_handler_secret_write
                     femtokernel_handler_secret_write_post wnil).

    Definition vc__femtohandler_exit : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
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
    Lemma sat__femtohandler_entry : RVPTVl.safeE vc__femtohandler_entry.
    Proof.
      (* We still need to prove that our word falls within mmio *)
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* TODO: would rather write {n} (v : bv n), but eq with bv.sext' complains... *)
    Lemma sext'_zero (v : bv 32) : bv.sext' v 0 = v.
    Proof.
      unfold bv.sext'.
      rewrite bv.ones_O.
      destruct (bv.view (@bv.zero 0)).
      rewrite ssrbool.if_same.
      now rewrite bv.app_nil_r.
    Qed.

    Lemma sat__femtohandler_dispatch : RVPTVl.safeE vc__femtohandler_dispatch.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
      all: repeat match goal with
             | H : context [bv.sext' _ 0] |- _ => rewrite sext'_zero in H
             end;
           now rewrite ?sext'_zero.
    Qed.

    Lemma sat__femtohandler_not_zero : RVPTVl.safeE vc__femtohandler_not_zero.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual; rewrite ?sext'_zero; auto.
      all: try (eexists _, _; intuition).
      all: apply bounds_withinMMIO; now compute.
    Qed.

    Lemma sat__femtohandler_is_zero : RVPTVl.safeE vc__femtohandler_is_zero.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual; rewrite ?sext'_zero; auto.
      all: try (eexists _, _; intuition).
      all: apply bounds_withinMMIO; now compute.
    Qed.

    Lemma sat__femtohandler_secret_write : RVPTVl.safeE vc__femtohandler_secret_write.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual. eexists _, _. intuition.
      all: apply bounds_withinMMIO; now compute.
    Qed.

    Definition vc__femtohandler_shutdown_check : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_shutdown_check_pre
                     femtokernel_handler_shutdown_check
                     femtokernel_handler_shutdown_check_post wnil).

    Definition vc__femtohandler_shutdown : 𝕊 [] :=
      postprocess2 (RVPTVl.sannotated_block_verification_condition
                     femtokernel_handler_shutdown_pre
                     femtokernel_handler_shutdown
                     femtokernel_handler_shutdown_post wnil).

    Lemma sat__femtohandler_shutdown_check : RVPTVl.safeE vc__femtohandler_shutdown_check.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtohandler_shutdown : RVPTVl.safeE vc__femtohandler_shutdown.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual; rewrite ?sext'_zero; auto.
      all: try (eexists _, _; intuition).
      all: apply bounds_withinMMIO; now compute.
    Qed.

    Lemma sat__femtohandler_exit : RVPTVl.safeE vc__femtohandler_exit.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Section WithEnvNotations.
      Import env.notations.

      Definition ContractTy (Σ : gFunctors) := Val ty_xlenbits -> ArchState -> Val ty_Minterrupts -> iProp Σ.

      (* The contract of a block, independent of the Iris instance in which it
         is interpreted (see contract_left and contract_right below). *)
      Record BlockContract :=
        MkBlockContract
          { bc_ctx   : LCtx
          ; bc_args  : Valuation bc_ctx
          ; bc_pre   : Assertion (Σ__csrs ▻▻ bc_ctx ▻▻ ["a" :: ty_xlenbits])
          ; bc_block : Block
          ; bc_post  : Assertion (Σ__csrs ▻▻ bc_ctx ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits])
          }.
      Arguments MkBlockContract {bc_ctx} _ _ _ _.

      Definition contract_femtohandler_builder_gen
        {Σ : gFunctors} {Γ}
        (PredDef : PredicateDef (iProp Σ))
        (semTripleBlock_ :
          (Val ty_xlenbits -> iProp Σ) ->
          Val ty_xlenbits ->
          list AST ->
          (Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) ->
          iProp Σ)
        (ι : Valuation Γ)
        (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
        (b : Block)
        (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
        : ContractTy Σ :=
        fun a archstate vmie =>
          let ι__csrs := csrs_valuation archstate vmie in
          semTripleBlock_
            (λ a, @asn.interpret _ PredDef _ PRE
                    (ι__csrs ►► ι ►► env.nil.["a" ∷ ty_xlenbits ↦ a]))
            a (filter_AST b)
            (λ a an, @asn.interpret _ PredDef _ POST
                       (ι__csrs ►► ι ►► env.nil.["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an])).

      Definition contract_femtohandler_builder_left `{sG : RVPBASEl.sailGS Σ} {Γ}
        (ι : Valuation Γ)
        (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
        (b : Block)
        (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
        : ContractTy Σ :=
        contract_femtohandler_builder_gen
          (@RVPINSTl.PredicateDefIProp _ sG Instance.trivTrivGS)
          (@RVPTVl.semTripleBlock _ sG)
          ι PRE b POST.

      Definition contract_femtohandler_builder_right `{sG : RVPBASEr.sailGS Σ} {Γ}
        (ι : Valuation Γ)
        (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
        (b : Block)
        (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
        : ContractTy Σ :=
        contract_femtohandler_builder_gen
          (@RVPINSTr.PredicateDefIProp _ sG Instance.trivTrivGS)
          (@RVPTVr.semTripleBlock _ sG)
          ι PRE b POST.

      Definition contract_left `{sG : RVPBASEl.sailGS Σ} (c : BlockContract) : ContractTy Σ :=
        contract_femtohandler_builder_left (bc_args c) (bc_pre c) (bc_block c) (bc_post c).

      Definition contract_right `{sG : RVPBASEr.sailGS Σ} (c : BlockContract) : ContractTy Σ :=
        contract_femtohandler_builder_right (bc_args c) (bc_pre c) (bc_block c) (bc_post c).

      Definition contract_femtoinit : BlockContract :=
        MkBlockContract
          env.nil
          femtokernel_init_pre
          femtokernel_init_gen
          femtokernel_init_post.

      Lemma contract_femtoinit_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
          ⊢ (contract_left contract_femtoinit) a archstate vmie.
      Proof.
        simpl. iIntros (a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        vm_compute.
        apply sat__femtoinit.
      Qed.

      Lemma contract_femtoinit_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
          ⊢ (contract_right contract_femtoinit) a archstate vmie.
      Proof.
        simpl. iIntros (a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        vm_compute.
        apply sat__femtoinit.
      Qed.

      Definition contract_femtohandler_entry (x5 x10 : Val ty_xlenbits) : BlockContract :=
        MkBlockContract
          env.nil.["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10]
          femtokernel_handler_entry_pre
          femtokernel_handler_entry
          femtokernel_handler_entry_post.

      Lemma contract_femtohandler_entry_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left (contract_femtohandler_entry x5 x10)) a archstate vmie.
      Proof.
        simpl. iIntros (x5 x10 a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_entry as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_entry_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right (contract_femtohandler_entry x5 x10)) a archstate vmie.
      Proof.
        simpl. iIntros (x5 x10 a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_entry as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_dispatch (x1 secret : Val ty_xlenbits) : BlockContract :=
        MkBlockContract
          env.nil.["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret]
          femtokernel_handler_dispatch_pre
          femtokernel_handler_dispatch
          femtokernel_handler_dispatch_post.

      Lemma contract_femtohandler_dispatch_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left (contract_femtohandler_dispatch x1 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 secret a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_dispatch as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_dispatch_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right (contract_femtohandler_dispatch x1 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 secret a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_dispatch as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_not_zero (x1 x5 secret : Val ty_xlenbits) : BlockContract :=
        MkBlockContract
          env.nil.["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
          femtokernel_handler_not_zero_pre
          femtokernel_handler_not_zero
          femtokernel_handler_ack_post.

      Lemma contract_femtohandler_not_zero_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left (contract_femtohandler_not_zero x1 x5 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 x5 secret a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_not_zero as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_not_zero_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right (contract_femtohandler_not_zero x1 x5 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 x5 secret a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_not_zero as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_is_zero (x1 x5 secret : Val ty_xlenbits) : BlockContract :=
        MkBlockContract
          env.nil.["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
          femtokernel_handler_is_zero_pre
          femtokernel_handler_is_zero
          femtokernel_handler_ack_post.

      Lemma contract_femtohandler_is_zero_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left (contract_femtohandler_is_zero x1 x5 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 x5 secret a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_is_zero as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_is_zero_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right (contract_femtohandler_is_zero x1 x5 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 x5 secret a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_is_zero as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_secret_write (x1 secret : Val ty_xlenbits) : BlockContract :=
        MkBlockContract
          env.nil.["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret]
          femtokernel_handler_secret_write_pre
          femtokernel_handler_secret_write
          femtokernel_handler_secret_write_post.

      Lemma contract_femtohandler_secret_write_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left (contract_femtohandler_secret_write x1 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 secret a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_secret_write as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_secret_write_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right (contract_femtohandler_secret_write x1 secret)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 secret a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_secret_write as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_exit : BlockContract :=
        MkBlockContract
          env.nil
          femtokernel_handler_exit_pre
          femtokernel_handler_exit
          femtokernel_handler_exit_post.

      Lemma contract_femtohandler_exit_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left contract_femtohandler_exit) a archstate vmie.
      Proof.
        simpl. iIntros (a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_exit as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_exit_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right contract_femtohandler_exit) a archstate vmie.
      Proof.
        simpl. iIntros (a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_exit as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_shutdown_check (x1 x5 x10 : Val ty_xlenbits) : BlockContract :=
        MkBlockContract
          env.nil.["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10]
          femtokernel_handler_shutdown_check_pre
          femtokernel_handler_shutdown_check
          femtokernel_handler_shutdown_check_post.

      Lemma contract_femtohandler_shutdown_check_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left (contract_femtohandler_shutdown_check x1 x5 x10)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 x5 x10 a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_shutdown_check as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_shutdown_check_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right (contract_femtohandler_shutdown_check x1 x5 x10)) a archstate vmie.
      Proof.
        simpl. iIntros (x1 x5 x10 a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_shutdown_check as H.
        vm_compute; apply H.
      Qed.

      Definition contract_femtohandler_shutdown : BlockContract :=
        MkBlockContract
          env.nil
          femtokernel_handler_shutdown_pre
          femtokernel_handler_shutdown
          femtokernel_handler_shutdown_post.

      Lemma contract_femtohandler_shutdown_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left contract_femtohandler_shutdown) a archstate vmie.
      Proof.
        simpl. iIntros (a archstate vmie).
        iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
        pose proof sat__femtohandler_shutdown as H.
        vm_compute; apply H.
      Qed.

      Lemma contract_femtohandler_shutdown_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right contract_femtohandler_shutdown) a archstate vmie.
      Proof.
        simpl. iIntros (a archstate vmie).
        iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
        pose proof sat__femtohandler_shutdown as H.
        vm_compute; apply H.
      Qed.
    End WithEnvNotations.

  (*   Definition femtoinit_stats := *)
  (*     SymProp.Statistics.count_to_stats *)
  (*       (SymProp.Statistics.count_nodes *)
  (*          (sannotated_block_verification_condition *)
  (*             femtokernel_init_pre *)
  (*             femtokernel_init_gen *)
  (*             (asn.sep femtokernel_init_post asn.debug) *)
  (*             wnil) *)
  (*          SymProp.Statistics.empty). *)
  (*   (* Eval vm_compute in femtoinit_stats. *) *)

  (*   (* There is currently no difference, because the adversary addresses are shared between both cases*) *)
  (*   Definition femto_init_stats := femtoinit_stats. *)
  (*   (* Eval vm_compute in femto_init_stats. *) *)

  (*   (* Definition femtohandler_stats := *) *)
  (*   (*   SymProp.Statistics.count_to_stats *) *)
  (*   (*     (SymProp.Statistics.count_nodes *) *)
  (*   (*        (sannotated_block_verification_condition *) *)
  (*   (*           femtokernel_handler_pre *) *)
  (*   (*           femtokernel_handler *) *)
  (*   (*           (asn.sep femtokernel_handler_post asn.debug) *) *)
  (*   (*           wnil) *) *)
  (*   (*        SymProp.Statistics.empty). *) *)
  (*   (* Eval vm_compute in femtohandler_stats. *) *)

  End FemtoKernel.

  Definition advAddrs : list (bv xlenbits) := bv.seq (bv.of_N adv_addr) (Z.of_N (adv_addr_end - adv_addr)).

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (∃ p2, Pmp_access x (bv.of_nat 1) ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access, Gen_Pmp_access.
    destruct (pmp_check_aux x (bv.of_nat 1) bv.zero ents p1 p2); [left|right]; easy.
  Defined.

  Lemma adv_is_live y : (y ∈ advAddrs)%stdpp → (y ∈ liveAddrs)%stdpp.
  Proof. unfold advAddrs, liveAddrs.
         apply bv.seq_subseteq; now compute.
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
    apply bv.elem_of_seq_bounds in Hin as [Hlo Hhi]; [|clear Hin; now compute].
    cbn in *. eassert (Ha : adv_addr = _) by now compute.
    eassert (He : adv_addr_end = _) by now compute.
    rewrite Ha He in Hlo Hhi |- *. change (bv.unsigned (bv.of_N ?y)) with (Z.of_N y) in *.
    assert (bv.unsigned (bv.add x (bv.of_nat 1)) = bv.unsigned x + 1)%Z as H1.
    { rewrite -bv.unsigned_add_small; change (bv.unsigned (bv.of_nat 1)) with 1%Z; lia. }
    case_if H; [now compute | clear H].
    case_if H.
    { apply orb_prop in H as [H|H]; apply bv.uleb_ule, bv.ule_iff_unsigned_le in H;
        change (bv.unsigned (bv.of_N ?y)) with (Z.of_N y) in H; lia. }
    clear H. case_if H; first easy.
    apply andb_false_iff in H as [H|H]; apply bv.uleb_ugt, bv.ult_iff_unsigned_lt in H;
      change (bv.unsigned (bv.of_N ?y)) with (Z.of_N y) in H; lia.
  Qed.

  Lemma pmp_in_adv x : (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p) → (x ∈ advAddrs)%stdpp.
  Proof.
    intros [p HPmp]. rewrite /femto_pmpentries.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry] in HPmp.
    cbn in HPmp.
    case_if H; first now compute. clear H.
    case_if H; first by exfalso.
    apply orb_false_elim in H as [_ Hhi]. apply bv.uleb_ugt, bv.ult_iff_unsigned_lt in Hhi.
    case_if H'; last by exfalso.
    apply andb_prop in H' as [Hlo _]. apply bv.uleb_ule, bv.ule_iff_unsigned_le in Hlo.
    apply bv.elem_of_seq_bounds; first now compute.
    revert Hlo Hhi. rewrite -!bv.of_Z_N -!bv.unsigned_of_Z_small; try lia; now compute.
  Qed.

  (* Use permutation rather than membership to avoid indexes *)
  Lemma allAddr_filter_advAddr : filter
                 (λ x : Val ty_word ,
                    (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p)%type)
                 all_addrs ≡ₚ advAddrs.
  Proof. rewrite (list_filter_iff _ (fun x => x ∈ advAddrs)); last split; auto using adv_in_pmp, pmp_in_adv.
    apply NoDup_Permutation.
    - apply NoDup_filter. rewrite all_addrs_eq. apply bv.NoDup_seq.
      pose proof (Z.pow_nonneg 2 (Z.of_nat xlenbits)). lia.
    - apply bv.NoDup_seq. now compute.
    - intros x. rewrite list_elem_of_filter.
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

  Definition femto_inv_mmio `{invGS Σ} `{mcMemGS2 Σ} : iProp Σ := interp_inv_mmio bytes_per_word.

  (* Import env.notations. *)

  (* Opaque interp_pmp_entries. *)

  (* (* Needed when introducing the below conditional *) *)
  (* Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B). *)
  (* Proof. destruct b; apply _. Qed. *)

  Ltac set_to_list s l Hl Hel :=
    remember (elements s) as l eqn:Hel;
    assert (Hl : list_to_set l = s) by (subst; apply list_to_set_elements_L).

  Ltac set_subseteq_to_list :=
    match goal with
    | |- ?s1 ⊆@{gset _} ?s2 =>
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
        apply RVPPREDl.list_to_set_subseteq;
        rewrite Hel1 Hel2
    end.

  Ltac solve_elem_of :=
    repeat (try apply list_elem_of_here;
            try apply list_elem_of_further).

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

  Definition ptsto_instrs_handler `{mcMemGS Σ} : iProp Σ :=
    RVPCOM.ptsto_instrs (bv.of_N handler_entry_addr) (filter_AST femtokernel_handler_entry) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit).

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.
  Transparent interp_pmp_entries.

  Local Opaque femtokernel_init_gen. (* TODO: figure out why not having this makes the below proof spin in two places *)

  (* see above *)
  Transparent femtokernel_init_pre.

  Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
    ∃ v0 v1 v2 v3, map (memory_ram μ) (bv.seq a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

  (* byte order correct? *)
  Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
    ∃ w, mem_has_word μ a w /\ pure_decode w = inr instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
    match instrs with
    | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
    | nil => True
    end.

  (* The memory contains the code of the FemtoKernel, and the secret at the
     data address. *)
  Definition mem_has_femtokernel (μ : Memory) (secret : Val ty_xlenbits) : Prop :=
    mem_has_instrs μ (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∧
    mem_has_instrs μ (bv.of_N handler_entry_addr) (filter_AST femtokernel_handler_entry) ∧
    mem_has_instrs μ (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∧
    mem_has_instrs μ (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∧
    mem_has_instrs μ (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∧
    mem_has_instrs μ (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∧
    mem_has_instrs μ (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∧
    mem_has_instrs μ (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∧
    mem_has_instrs μ (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∧
    mem_has_word μ (bv.of_N data_addr) secret.

  (* The initial register values that the FemtoKernel relies on. *)
  Definition femto_init_regs (γ : RegStore) : Prop :=
    read_register γ mstatus = {| MPP := User; SPP := User; MPIE := false; SPIE := false; MIE := false; SIE := false |} ∧
    read_register γ cur_privilege = Machine ∧
    read_register γ pmp0cfg = default_pmpcfg_ent ∧
    read_register γ pmpaddr0 = bv.zero ∧
    read_register γ pmp1cfg = default_pmpcfg_ent ∧
    read_register γ pmpaddr1 = bv.zero ∧
    read_register γ pc = bv.of_N init_addr ∧
    read_register γ mideleg = Minterrupts_zero ∧
    read_register γ medeleg = Medeleg_zero.

  (* Import RiscvPmpSemantics. *)
  (* Import RiscvPmpIrisAdeqParameters. *)
  (* Import SmallStepNotations. *)

  (* Import iris.bi.big_op. *)
  (* Import iris.algebra.big_op. *)

  (* Note that the split differs depending on whether or not we have an MMIO region! *)
  Lemma liveAddrs_split : (liveAddrs = bv.seq (bv.of_N init_addr) (Z.of_N init_size) ++ bv.seq (bv.of_N handler_entry_addr) (Z.of_N handler_size) ++ bv.seq (bv.of_N data_addr) (Z.of_nat bytes_per_word) ++ advAddrs)%list.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma handlerAddrs_split : (@bv.seq xlenbits (bv.of_N handler_entry_addr) (Z.of_N handler_size) = bv.seq (bv.of_N handler_entry_addr) (Z.of_N handler_entry_size) ++ bv.seq (bv.of_N handler_dispatch_addr) (Z.of_N handler_dispatch_size) ++ bv.seq (bv.of_N handler_not_zero_addr) (Z.of_N handler_not_zero_size) ++ bv.seq (bv.of_N handler_is_zero_addr) (Z.of_N handler_is_zero_size) ++ bv.seq (bv.of_N handler_shutdown_check_addr) (Z.of_N handler_shutdown_check_size) ++ bv.seq (bv.of_N handler_shutdown_addr) (Z.of_N handler_shutdown_size) ++ bv.seq (bv.of_N handler_secret_write_addr) (Z.of_N handler_secret_write_size) ++ bv.seq (bv.of_N handler_exit_addr) (Z.of_N handler_exit_size))%list.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma intro_ptstomem_word `{mcMemGS Σ} v0 v1 v2 v3 (a : Val ty_word) :
    RVPCOM.interp_ptsto (bv.of_Z (0 + bv.unsigned a)) v0 ∗
    RVPCOM.interp_ptsto (bv.of_Z (1 + bv.unsigned a)) v1 ∗
    RVPCOM.interp_ptsto (bv.of_Z (2 + bv.unsigned a)) v2 ∗
    RVPCOM.interp_ptsto (bv.of_Z (3 + bv.unsigned a)) v3 ⊢
      RVPCOM.interp_ptstomem (width := 4) a (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil)))).
  Proof.
    iIntros "(Hmema & Hmema1 & Hmema2 & Hmema3)".
    unfold RVPCOM.interp_ptstomem.
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

  Lemma intro_ptstomem_word2 `{mcMemGS Σ} {μ : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ a v ->
    ([∗ list] a' ∈ bv.seq a 4, RVPCOM.interp_ptsto a' ((memory_ram μ) a')) ⊢ RVPCOM.interp_ptstomem a v.
  Proof.
    iIntros (Hmhw) "Hmem".
    destruct Hmhw as (v0 & v1 & v2 & v3 & Heqμ & Heqv).
    unfold bv.seq, seqZ. change (seq 0 ?x) with [0;1;2;3]%nat%list.
    cbn -[bv.add RVPCOM.interp_ptstomem word].
    iDestruct "Hmem" as "(Hmema & Hmema1 & Hmema2 & Hmema3 & _)".
    inversion Heqμ; subst.
    now iApply (intro_ptstomem_word with "[$Hmema $Hmema1 $Hmema2 $Hmema3]").
  Qed.

  Lemma intro_ptsto_instr `{mcMemGS Σ} {μ : Memory} {a : Val ty_word} {instr : AST} :
    (4 + bv.unsigned a < 2 ^ Z.of_nat xlenbits)%Z ->
    mem_has_instr μ a instr ->
    ([∗ list] a' ∈ bv.seq a 4, RVPCOM.interp_ptsto a' ((memory_ram μ) a'))
      ⊢ RVPCOM.interp_ptsto_instr a instr.
  Proof.
    iIntros (Hrep (v & Hmhw & Heq)) "Hmem".
    iExists v.
    iSplitL; last done.
    now iApply (intro_ptstomem_word2 Hmhw).
  Qed.

  Lemma intro_ptsto_instrs `{mcMemGS Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * Z.of_nat (length instrs) + bv.unsigned a < 2 ^ Z.of_nat xlenbits)%Z ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seq a (4 * Z.of_nat (length instrs)), RVPCOM.interp_ptsto a' ((memory_ram μ) a'))
      ⊢ RVPCOM.ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - replace (4 * Z.of_nat (length (instr :: instrs)))%Z
        with (4 + 4 * Z.of_nat (length instrs))%Z in * by (cbn; lia).
      rewrite bv.seq_add ?big_opL_app; [|lia..].
      destruct Hmeminstrs as [Hinstr Hmeminstrs].
      iDestruct "Hmem" as "[Hmema Hmema4]".
      iSplitL "Hmema".
      + iApply (intro_ptsto_instr with "Hmema"); auto; Lia.lia.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply ("IH" with "[%] [% //] [-]"); last done.
        pose proof (bv.unsigned_bounds a). change word with xlenbits in *.
        rewrite -bv.unsigned_add_small; change (bv.unsigned (bv.of_N 4)) with 4%Z; lia.
  Qed.

  Lemma intro_ptstoSthL `{mcMemGS Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, RVPCOM.interp_ptsto a' ((memory_ram μ) a')) ⊢ RVPCOM.ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists ((memory_ram μ) a).
      + now iApply IHl.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto `{mcMemGS Σ} {s e} (μ : Memory):
    (Z.of_N minAddr <= bv.unsigned s)%Z → (bv.unsigned s + e <= Z.of_N (minAddr + lenAddr))%Z →
    ([∗ list] y ∈ bv.seq s e, gen_heap.pointsto y (dfrac.DfracOwn 1) (memory_ram μ y)) ⊢ [∗ list] a' ∈ bv.seq s e, RVPCOM.interp_ptsto a' (memory_ram μ a').
  Proof.
    iIntros (Hlow Hhi) "Hlist".
    iApply (big_sepL_mono with "Hlist"). intros ? ? Hsom. cbn.
    iIntros "$". iPureIntro.
    rewrite /= withinMMIO_one /not; apply mmio_ram_False.
    eapply bv.seq_subseteq, list_elem_of_lookup_2, Hsom;
      change (bv.unsigned (bv.of_N minAddr)) with (Z.of_N minAddr); lia.
  Qed.

  Lemma femtokernel_splitMemory {Σ} {mG : mcMemGS Σ} {μ : Memory} (secret : Val ty_xlenbits) :
    mem_has_femtokernel μ secret ->
    ([∗ list] a' ∈ liveAddrs, gen_heap.pointsto a' (dfrac.DfracOwn 1) (memory_ram μ a')) ⊢
      RVPCOM.ptsto_instrs (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∗
      ptsto_instrs_handler ∗
      RVPCOM.interp_ptstomem (bv.of_N data_addr) secret ∗
      [∗ list] a ∈ advAddrs, RVPCOM.interp_ptsto a (memory_ram μ a).
  Proof.
    iIntros ((Hinit & Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit & Hdata)) "Hmem".
    rewrite liveAddrs_split.
    iDestruct "Hmem" as "(Hinit & Hhandler & Hdata & Hadv)".
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); now compute. }
    iSplitL "Hhandler". (* Need to solve the goal for both handlers *)
    { unfold ptsto_instrs_handler.
      rewrite handlerAddrs_split.
      iDestruct "Hhandler" as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      iSplitL "Hhentry".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhentry"); now compute. }
      iSplitL "Hhdispatch".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhdispatch"); now compute. }
      iSplitL "Hhnotzero".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhnotzero"); now compute. }
      iSplitL "Hhiszero".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhiszero"); now compute. }
      iSplitL "Hhcheck".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhcheck"); now compute. }
      iSplitL "Hhshutdown".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhshutdown"); now compute. }
      iSplitL "Hhsecret".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhsecret"); now compute. }
      iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hhexit"); now compute. }
    iSplitL "Hdata".
    { iApply (intro_ptstomem_word2 Hdata).
      iApply (sub_heap_mapsto_interp_ptsto with "Hdata"); now compute. }
    iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); now compute.
  Qed.

  Definition UnaryPredicateDefIProp__l {Σ} (sG : RVPBASEl.sailGS Σ) :=
    @RVPINSTl.PredicateDefIProp _ sG Instance.trivTrivGS.
  Definition UnaryPredicateDefIProp__r {Σ} (sG : RVPBASEr.sailGS Σ) :=
    @RVPINSTr.PredicateDefIProp _ sG Instance.trivTrivGS.

  (* The architectural state with which the femtokernel hands control to the
     adversary (or traps back): M-mode state is fixed by the kernel, except
     for the parts that the adversary can influence. *)
  Definition femto_archstate (priv : Privilege) (ms : ArchState.MState) (ss : ArchState.SState) (pc : Xlenbits) : ArchState :=
    {| ArchState.m := priv;
       ArchState.mstate :=
         {| ArchState.mtvec      := bv.of_N handler_entry_addr;
            ArchState.pmpentries := femto_pmpentries;
            ArchState.mpp        := ArchState.mpp ms;
            ArchState.mcause     := ArchState.mcause ms;
            ArchState.mscratch   := ArchState.mscratch ms;
            ArchState.mepc       := ArchState.mepc ms;
            ArchState.mpie       := ArchState.mpie ms;
            ArchState.mie        := ArchState.mie ms;
            ArchState.mideleg    := Minterrupts_zero;
            ArchState.medeleg    := Medeleg_zero |};
       ArchState.sstate := ss;
       ArchState.pc := pc |}.

  (* The architectural state with which the handler returns to the
     adversary: the pc is the address the handler returns to, everything else
     is fixed by the handler pre- and postconditions. *)
  Definition femto_return_archstate (archstate : ArchState) (vmscratch : Val ty_xlenbits) (an : Val ty_xlenbits) : ArchState :=
    femto_archstate (ArchState.mpp (ArchState.mstate archstate))
      {| ArchState.mtvec      := bv.of_N handler_entry_addr;
         ArchState.pmpentries := femto_pmpentries;
         ArchState.mpp        := User;
         ArchState.mcause     := ArchState.mcause (ArchState.mstate archstate);
         ArchState.mscratch   := vmscratch;
         ArchState.mepc       := ArchState.mepc (ArchState.mstate archstate);
         ArchState.mpie       := true;
         ArchState.mie        := ArchState.mpie (ArchState.mstate archstate);
         ArchState.mideleg    := Minterrupts_zero;
         ArchState.medeleg    := Medeleg_zero |}
      (ArchState.sstate archstate)
      an.

  (* The architectural state on entry of the trap handler, after a trap from
     S- or U-mode. *)
  Definition femto_handler_archstate (mpp : Privilege) (mpie : bool) (mcause mscratch mepc : Xlenbits)
    (ss : ArchState.SState) : ArchState :=
    {| ArchState.m      := Machine;
       ArchState.mstate :=
         {| ArchState.mtvec      := bv.of_N handler_entry_addr;
            ArchState.pmpentries := femto_pmpentries;
            ArchState.mpp        := mpp;
            ArchState.mpie       := mpie;
            ArchState.mie        := false;
            ArchState.mcause     := mcause;
            ArchState.mscratch   := mscratch;
            ArchState.mepc       := mepc;
            ArchState.mideleg    := Minterrupts_zero;
            ArchState.medeleg    := Medeleg_zero |};
       ArchState.sstate := ss;
       ArchState.pc     := bv.of_N handler_entry_addr |}.

  (* The architectural state with which the femtokernel first hands control
     to the adversary, after its initialization. *)
  Definition femto_adv_archstate (mpp : Privilege) (mpie mie : bool) (mcause mscratch mepc : Xlenbits)
    (stvec scause sscratch sepc : Xlenbits) : ArchState :=
    femto_archstate User
      (ArchState.mkMState (bv.of_N handler_entry_addr) femto_pmpentries mpp mpie mie
         mcause mscratch mepc Minterrupts_zero Medeleg_zero)
      (ArchState.mkSState stvec (MkSstatus User false false) scause sscratch sepc)
      (bv.of_N adv_addr).

  (* The architectural state in which the femtokernel starts executing. *)
  Definition femto_init_archstate (γ : RegStore) : ArchState :=
    {| ArchState.m      := Machine;
       ArchState.mstate :=
         {| ArchState.mtvec      := read_register γ mtvec;
            ArchState.pmpentries := [(default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero)];
            ArchState.mpp        := User;
            ArchState.mpie       := false;
            ArchState.mie        := false;
            ArchState.mcause     := read_register γ mcause;
            ArchState.mscratch   := read_register γ mscratch;
            ArchState.mepc       := read_register γ mepc;
            ArchState.mideleg    := Minterrupts_zero;
            ArchState.medeleg    := Medeleg_zero |};
       ArchState.sstate :=
         {| ArchState.stvec    := read_register γ stvec;
            ArchState.sstatus  := MkSstatus User false false;
            ArchState.scause   := read_register γ scause;
            ArchState.sscratch := read_register γ sscratch;
            ArchState.sepc     := read_register γ sepc |};
       ArchState.pc     := bv.of_N init_addr |}.

  (* Integrity of the FemtoKernel: a single execution of the FemtoKernel, together
     with arbitrary (unknown) U-mode code, only ever produces MMIO events that
     satisfy mmio_pred. This is a unary result: it uses the unary (left) Iris
     instance and unary adequacy.

     The unary block contracts of the FemtoKernel use the writePending ghost
     state for the observable MMIO write (nothingPending before the write,
     written after). Without a second execution to resynchronize with, we use the
     phantom execution of RVPADEQl: we carry its resources around in the
     universal contract (as part of R), and resynchronize with phantom_resync. *)
  Section Integrity.
    Import RVPCOM.
    Import RVPBASEl.
    Import RVPPREDl.
    Import RVPINSTl.
    Import RiscvPmpSemantics.SmallStepNotations.

    #[local] Existing Instance Instance.trivTrivGS.

    #[local] Instance sailGS_mcMemGS2 `{sG : RVPBASEl.sailGS Σ} : mcMemGS2 Σ :=
      RVPBASEl.sailGS_memGS.

    Section WithUnarySailGS.
      Context `{sG : RVPBASEl.sailGS Σ}.

      #[local] Notation "r '↦ᵣ' v" := (reg_pointsTo r v) (at level 70).
      #[local] Notation asn_interpret := (@asn.interpret _ (UnaryPredicateDefIProp__l sG) _).

      (* The resource that is threaded through the universal contract: the
         phantom execution's resources (RVPADEQl.phantom_res), together with
         this execution's nothingPending and power token. *)
      Definition phantom_res : iProp Σ := nothingPending ∗ powered_tok true ∗ RVPADEQl.phantom_res.

      Lemma loop_pre_WP_loop (archstate : ArchState) :
        LoopVerificationl.loop_pre phantom_res archstate ⊢ WP_loop.
      Proof.
        iIntros "H".
        iApply (semWP_mono with "[H]").
        { iApply (LoopVerificationl.valid_semTriple_loop with "H"). }
        by iIntros.
      Qed.

      Definition femtokernel_safe_shared_pre (addr : N) (b : Block) : iProp Σ :=
        RVPTVl.exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
          (∃ v, mscratch ↦ᵣ v) ∗
          interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User.

      Lemma femtokernel_handler_exit_safe (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
        ⊢ femtokernel_safe_shared_pre handler_exit_addr femtokernel_handler_exit ∗
          asn_interpret femtokernel_handler_exit_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] ∗
          interp_gprs ∅ ∗
          phantom_res ∗
          ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
               ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
               LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
          -∗
          WP_loop.
      Proof.
        iIntros "((Hpro & [%vmscratch Hmscratch] & HaccU) & Hpre & Hgprs & HR & Htrap)".
        iPoseProof (contract_femtohandler_exit_verified__l (bv.of_N handler_exit_addr) archstate vmie) as "Htrip".
        iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
        iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
        iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & [%Han _])"; cbn - [interp_ptstomem] in *.
        iAssert (interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries (ArchState.mpp (ArchState.mstate archstate))) with "[HaccU]" as "Hacc".
        { assert (Hmpp' : ArchState.mpp (ArchState.mstate archstate) = User ∨ ArchState.mpp (ArchState.mstate archstate) = Supervisor)
            by (destruct (ArchState.mpp (ArchState.mstate archstate)); auto; congruence).
          destruct Hmpp' as [Heq|Heq]; rewrite Heq; first iExact "HaccU".
          by iApply interp_pmp_addr_access_s_u_eq. }
        iApply (loop_pre_WP_loop (femto_return_archstate archstate vmscratch an)).
        unfold LoopVerificationl.loop_pre.
        iSplitR "HR Htrap Hinstrs".
        { unfold LoopVerificationl.Step_pre; cbn.
          iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
          auto. }
        iFrame "HR".
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationl.M_CSRMod_machine with "H'") as %Heq.
          cbn in Heq. contradiction. }
        iSplitL "Htrap Hinstrs".
        { iIntros "!> [H' HR]". iApply ("Htrap" $! (ArchState.mpp (ArchState.mstate archstate)) with "[//] Hinstrs H' HR"). }
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationl.MRET_machine with "H'") as %Heq.
          cbn in Heq. contradiction. }
        iIntros "!> [H' _]". iDestruct (LoopVerificationl.SRET_machine with "H'") as %Heq.
        cbn in Heq. contradiction.
      Qed.

      (* Run the dispatch block and, depending on the secret, the is_zero or
         not_zero block, which both perform the observable write. *)
      Lemma femtokernel_dispatch_path (vx1 vx5 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
        let ι__csrs := csrs_valuation archstate vmie in
        ⊢ femto_inv_mmio -∗
          RVPTVl.exec_instructions_prologue (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
          asn_interpret femtokernel_handler_dispatch_pre
            (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                     ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) -∗
          nothingPending -∗
          x5 ↦ᵣ vx5 -∗
          ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
          ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
          (∀ x1 x5 a an,
             asn_interpret femtokernel_handler_ack_post
               (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                        ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]) -∗
             pc ↦ᵣ an -∗
             (∃ v, nextpc ↦ᵣ v) -∗
             ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
             ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
             ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
             WP_loop) -∗
          WP_loop.
      Proof.
        iIntros (ι__csrs) "#Hinv Hpro Hpre Hnp Hx5 Hnz Hiz Hk".
        iPoseProof (contract_femtohandler_dispatch_verified__l vx1 secret (bv.of_N handler_dispatch_addr) archstate vmie) as "Htrip".
        iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
        iIntros (an) "(Hpost & Hpc & Hcode & Hnpc)".
        iEval (cbn - [interp_ptstomem]) in "Hpost".
        iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hdata)".
        case_match; iDestruct "Han" as "[-> _]".
        - (* The secret is zero: is_zero block. *)
          iPoseProof (contract_femtohandler_is_zero_verified__l secret vx5 secret (bv.of_N handler_is_zero_addr) archstate vmie) as "Htrip'".
          iApply (RVPTVl.WP_loop_semTripleBlock with "[Hpc Hiz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip'").
          + iFrame "Hpc Hiz Hnpc".
          + cbn - [interp_ptstomem].
            iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
            repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
            repeat iSplit; try iPureIntro; try done; by vm_compute.
          + iIntros (an') "(Hpost & Hpc & Hcode' & Hnpc)".
            iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hnz Hcode'").
        - (* The secret is not zero: not_zero block. *)
          iPoseProof (contract_femtohandler_not_zero_verified__l secret vx5 secret (bv.of_N handler_not_zero_addr) archstate vmie) as "Htrip'".
          iApply (RVPTVl.WP_loop_semTripleBlock with "[Hpc Hnz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip'").
          + iFrame "Hpc Hnz Hnpc".
          + cbn - [interp_ptstomem].
            iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
            repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
            repeat iSplit; try iPureIntro; try done; by vm_compute.
          + iIntros (an') "(Hpost & Hpc & Hcode' & Hnpc)".
            iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hcode' Hiz").
      Qed.

      Lemma femtokernel_handler_dispatch_safe (vx1 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
        ⊢ femto_inv_mmio -∗
          femtokernel_safe_shared_pre handler_dispatch_addr femtokernel_handler_dispatch ∗
          asn_interpret femtokernel_handler_dispatch_pre
            (csrs_valuation archstate vmie ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                                           ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) ∗
          interp_gprs {[x1]} ∗
          phantom_res ∗
          ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
          ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
          ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
          ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
             ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
             ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
             ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
             interp_ptstomem (bv.of_N data_addr) secret -∗
             ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
             LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
          -∗
          WP_loop.
      Proof.
        iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & (Hnp & Hpow & Hph) & Hhnz & Hhiz & Hhexit & Hk)".
        iPoseProof (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}) with "Hgprs") as "(Hregs & Hgprs)";
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        iDestruct "Hregs" as "([%vx5 Hx5] & _)".
        subst l; clear Hl Hdup.
        iApply (femtokernel_dispatch_path vx1 vx5 secret archstate vmie
                  with "Hinv Hpro Hpre Hnp Hx5 Hhnz Hhiz").
        iIntros (x1v x5v a an) "Hpost Hpc Hnpc Hcode Hhnz Hhiz".
        iEval (cbn - [interp_ptstomem]) in "Hpost".
        iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Hx5 & Hdata & Hw)"; subst an.
        (* Resynchronize with the phantom execution after the observable write. *)
        iApply (fupd_semWP ⊤).
        iMod (RVPADEQl.phantom_resync bytes_per_word with "Hinv Hph Hw") as "[Hph Hnp]"; first solve_ndisj.
        iModIntro.
        iAssert (interp_gprs ∅) with "[Hgprs Hx1 Hx5]" as "Hgprs".
        { iApply (interp_gprs_with_excluded (exclude := {[x1; x5]})); try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          iFrame "Hx1 Hx5". by cbn. }
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
          with "[Hk Hcode Hhnz Hhiz Hdata]" as "Hk".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit Htrap HR".
          iApply ("Hk" with "[//] Hcode Hhnz Hhiz Hdata Hhexit Htrap HR"). }
        iApply (femtokernel_handler_exit_safe _ _ Hmpp).
        iFrame "Hpc Hhexit Hnpc Hmscratch HaccU Hmstatus Hgprs Hk Hinv Hnp Hpow Hph"; cbn - [interp_ptstomem].
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        now iPureIntro.
      Qed.

      Lemma femtokernel_handler_secret_write_safe (vx1 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
        ⊢ femto_inv_mmio -∗
          femtokernel_safe_shared_pre handler_secret_write_addr femtokernel_handler_secret_write ∗
          asn_interpret femtokernel_handler_secret_write_pre
            (csrs_valuation archstate vmie ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                                           ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr]) ∗
          interp_gprs {[x1]} ∗
          phantom_res ∗
          ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
          ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
             ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
             interp_ptstomem (bv.of_N data_addr) secret -∗
             ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
             LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
          -∗
          WP_loop.
      Proof.
        iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & HR & Hhexit & Htrap)".
        iPoseProof (contract_femtohandler_secret_write_verified__l vx1 secret (bv.of_N handler_secret_write_addr) archstate vmie) as "Htrip".
        iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
        iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
        iEval (cbn - [interp_ptstomem]) in "Hpost".
        iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Hdata)".
        iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
        { iApply (interp_gprs_with_excluded (exclude := {[x1]})); try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          iFrame "Hx1". by cbn. }
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
          with "[Htrap Hinstrs Hdata]" as "Htrap".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit' Htrap' HR".
          iApply ("Htrap" with "[//] Hinstrs Hdata Hhexit' Htrap' HR"). }
        iApply (femtokernel_handler_exit_safe _ _ Hmpp).
        rewrite Han.
        iFrame "Hpc Hhexit Hnpc Hmscratch HaccU Hmstatus Hgprs Htrap Hinv HR"; cbn - [interp_ptstomem].
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        now iPureIntro.
      Qed.

      (* The shutdown check, followed by either powering off the machine, or by
         the secret write. *)
      Lemma femtokernel_handler_shutdown_check_safe (vx1 vx5 vx10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
        ⊢ femto_inv_mmio -∗
          femtokernel_safe_shared_pre handler_shutdown_check_addr femtokernel_handler_shutdown_check ∗
          asn_interpret femtokernel_handler_shutdown_check_pre
            (csrs_valuation archstate vmie ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["x5" ∷ ty_xlenbits ↦ vx5].["x10" ∷ ty_xlenbits ↦ vx10]
                                           ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr]) ∗
          interp_gprs {[x1; x5; x10]} ∗
          (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) ∗
          phantom_res ∗
          ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
          ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
          ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
          ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
             ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
             ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
             ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
             (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
             ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
             LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop)
          -∗
          WP_loop.
      Proof.
        iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & HR & Hhshutdown & Hhsecret & Hhexit & Hk)".
        iPoseProof (contract_femtohandler_shutdown_check_verified__l vx1 vx5 vx10 (bv.of_N handler_shutdown_check_addr) archstate vmie) as "Htrip".
        iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
        iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
        iEval (cbn - [interp_ptstomem]) in "Hpost".
        iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hx5 & Hx10)".
        case_match; iDestruct "Han" as "[-> _]".
        - (* Power off the machine. *)
          iDestruct "HR" as "(Hnp & Hpow & Hph)".
          iPoseProof (contract_femtohandler_shutdown_verified__l (bv.of_N handler_shutdown_addr) archstate vmie) as "Htrip'".
          iApply (RVPTVl.WP_loop_semTripleBlock with "[Hpc Hhshutdown Hnpc] [Hshared Hmstatus Hx5 Hnp Hpow] Htrip'").
          + iFrame "Hpc Hhshutdown Hnpc".
          + cbn - [interp_ptstomem].
            iFrame "Hinv Hmstatus Hx5 Hnp Hpow".
            repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
            repeat iSplit; try iPureIntro; try done; by vm_compute.
          + iIntros (an') "(Hpost & _)".
            iEval (cbn) in "Hpost". iDestruct "Hpost" as "(_ & Hoff)".
            unfold WP_loop.
            iApply (semWP_fun_loop_off with "[Hoff]"); [iExact "Hoff" | by iIntros].
        - (* Perform the secret write. *)
          iAssert (interp_gprs {[x1]}) with "[Hgprs Hx5 Hx10]" as "Hgprs".
          { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5; x10]})); try solve_subseteq.
            iFrame "Hgprs".
            reduce_big_sepS_big_sepL.
            iFrame "Hx5 Hx10". by cbn. }
          iDestruct "Hdata" as "(%secret & Hdata)".
          iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                     ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                     interp_ptstomem (bv.of_N data_addr) (secret : Val ty_xlenbits) -∗
                     ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                     LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
            with "[Hk Hinstrs Hhshutdown]" as "Hksecret".
          { iIntros "!>" (priv ms ss pc Hpriv) "Hhsecret Hdata Hhexit Htrap HR".
            iApply ("Hk" with "[//] Hinstrs Hhshutdown Hhsecret [Hdata] Hhexit Htrap HR").
            by iExists _. }
          iApply (femtokernel_handler_secret_write_safe _ secret _ _ Hmpp with "Hinv"); cbn - [interp_ptstomem].
          iFrame "Hhsecret Hpc Hnpc Hmscratch HaccU Hmstatus Hgprs Hhexit Hx1 Hdata HR Hksecret".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
      Qed.

      Lemma femtokernel_handler_entry_safe (x5_val x10_val : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
        ⊢ femto_inv_mmio -∗
          femtokernel_safe_shared_pre handler_entry_addr femtokernel_handler_entry ∗
          asn_interpret femtokernel_handler_entry_pre
            (csrs_valuation archstate vmie ►► [env].["x5" ∷ ty_xlenbits ↦ x5_val].["x10" ∷ ty_xlenbits ↦ x10_val]
                                           ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr]) ∗
          interp_gprs {[ x1; x5; x10 ]} ∗
          (∃ v, x1 ↦ᵣ v) ∗
          (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) ∗
          phantom_res ∗
          ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
          ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
          ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
          ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
          ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
          ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
          ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit)
          -∗
          WP_loop.
      Proof.
        iIntros "#Hinv".
        iLöb as "IH" forall (x5_val x10_val archstate vmie Hmpp).
        iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hx1 & Hdata & HR & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
        (* When the adversary traps back into the handler, we are back at the
           start of this lemma (with possibly different CSR values). *)
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs_handler ∗ (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
                   LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I with "[]" as "#Hk".
        { iIntros "!>" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap HR".
          iDestruct "Hhandler" as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
          assert (HU : User ≠ Machine) by auto.
          iPoseProof (LoopVerificationl.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                        Hpriv HU eq_refl with "Htrap") as "Htrap".
          unfold LoopVerificationl.M_Trap, LoopVerificationl.transition; cbn.
          iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie' Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp' _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
          iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
            try solve_subseteq.
          reduce_big_sepS_big_sepL.
          iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
          iApply ("IH" $! _ _
                    (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie' with "[//]").
          cbn - [interp_ptstomem].
          iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata HR Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
          auto. }
        iPoseProof (contract_femtohandler_entry_verified__l x5_val x10_val (bv.of_N handler_entry_addr) archstate vmie) as "Htrip".
        iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
        iIntros (an) "(Hpost & Hpc & Hinstrs & Hnpc)".
        iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & Han & Hx5 & Hx10)"; cbn - [interp_ptstomem].
        iDestruct "Hx1" as "[%vx1 Hx1]".
        case_match; cbn - [interp_ptstomem];
          iDestruct "Han" as "[-> _]".
        - (* Dispatch on the secret. *)
          iAssert (interp_gprs {[ x1; x5 ]}) with "[Hgprs Hx10]" as "Hgprs".
          { iApply (interp_gprs_with_excluded_gen {[x1; x5]} (exclude2 := {[x10]}));
              try solve_subseteq.
            iFrame "Hgprs".
            reduce_big_sepS_big_sepL.
            now iFrame "Hx10". }
          iAssert (interp_gprs {[ x1 ]}) with "[Hgprs Hx5]" as "Hgprs".
          { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}));
              try solve_subseteq.
            iFrame "Hgprs".
            reduce_big_sepS_big_sepL.
            now iFrame "Hx5". }
          iDestruct "Hdata" as "(%secret & Hdata)".
          iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                     ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
                     ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
                     ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
                     interp_ptstomem (bv.of_N data_addr) (secret : Val ty_xlenbits) -∗
                     ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                     LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
            with "[Hinstrs Hhcheck Hhshutdown Hhsecret]" as "Hkdispatch".
          { iIntros "!>" (priv ms ss pc Hpriv) "Hhdispatch Hhnotzero Hhiszero Hdata Hhexit Htrap HR".
            iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap HR").
            iSplitR "Hdata"; last by iExists _.
            iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit". }
          iApply (femtokernel_handler_dispatch_safe _ _ _ _ Hmpp with "Hinv"); cbn - [interp_ptstomem].
          iFrame "Hhdispatch Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hhnotzero Hhiszero Hhexit Hx1 Hdata HR Hkdispatch";
            repeat iSplitR; auto.
        - (* Check for a shutdown request. *)
          iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                     ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
                     ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
                     ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                     (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
                     ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                     LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop))%I
            with "[Hinstrs Hhdispatch Hhnotzero Hhiszero]" as "Hkcheck".
          { iIntros "!>" (priv ms ss pc Hpriv) "Hhcheck Hhshutdown Hhsecret Hdata Hhexit Htrap HR".
            iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap HR").
            iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata". }
          iApply (femtokernel_handler_shutdown_check_safe vx1 _ x10_val _ _ Hmpp with "Hinv"); cbn - [interp_ptstomem].
          iFrame "Hhcheck Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx1 Hx5 Hx10 Hdata HR Hhshutdown Hhsecret Hhexit Hkcheck";
            repeat iSplitR; auto.
      Qed.

      Lemma femtokernel_handler_safe :
        ⊢ femto_inv_mmio -∗
          ∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
            ptsto_instrs_handler ∗ (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) -∗
            LoopVerificationl.M_Trap (femto_archstate priv ms ss pc) -∗ phantom_res -∗ WP_loop.
      Proof.
        iIntros "#Hinv" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap HR".
        iDestruct "Hhandler" as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
        (* Traps from S-mode look the same as traps from U-mode *)
        assert (HU : User ≠ Machine) by auto.
        iPoseProof (LoopVerificationl.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                      Hpriv HU eq_refl with "Htrap") as "Htrap".
        unfold LoopVerificationl.M_Trap, LoopVerificationl.transition; cbn.
        iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
        iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
        iApply (femtokernel_handler_entry_safe _ _
                  (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie Hmpp with "Hinv").
        cbn - [interp_ptstomem].
        iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata HR Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
        auto.
      Qed.

      Lemma memAdv_pmpPolicy :
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
        apply list_elem_of_lookup_2, adv_is_live in Hsom.
        repeat case_decide; auto.
        iPureIntro. eapply mmio_ram_False; eauto.
      Qed.

      Lemma femtokernel_manualStep :
        ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; SPP := User; MPIE := mpie; SPIE := false; MIE := mie; SIE := false |}) ∗
          (mtvec ↦ᵣ (bv.of_N handler_entry_addr)) ∗
          (∃ v, mcause ↦ᵣ v) ∗
          (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
          (∃ v, mscratch ↦ᵣ v) ∗
          (∃ v, mepc ↦ᵣ v) ∗
          (∃ v, scause ↦ᵣ v) ∗
          (∃ v, sscratch ↦ᵣ v) ∗
          (∃ v, sepc ↦ᵣ v) ∗
          (∃ v, stvec ↦ᵣ v) ∗
          mideleg ↦ᵣ Minterrupts_zero ∗
          medeleg ↦ᵣ Medeleg_zero ∗
          cur_privilege ↦ᵣ User ∗
          interp_gprs ∅ ∗
          interp_pmp_entries femto_pmpentries ∗
          femto_inv_mmio ∗
          (pc ↦ᵣ (bv.of_N adv_addr)) ∗
          (∃ v, nextpc ↦ᵣ v) ∗
          ptsto_instrs_handler ∗
          (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v) ∗
          ptstoSthL advAddrs ∗
          phantom_res
          -∗
          WP_loop.
      Proof.
        iIntros "((%mpp & %mpie & %mie & Hmst) & Hmtvec & [%vmcause Hmcause] & Hmip & Hmie & [%vmscratch Hmscratch] & [%vmepc Hmepc] & [%vscause Hscause] & [%vsscratch Hsscratch] & [%vsepc Hsepc] & [%vstvec Hstvec] & Hmideleg & Hmedeleg & Hcurpriv & Hgprs & Hpmpcfg & #Hmmio & Hpc & Hnpc & Hhandler & Hdata & Hmemadv & HR)".
        iApply (loop_pre_WP_loop
                      (femto_adv_archstate mpp mpie mie vmcause vmscratch vmepc vstvec vscause vsscratch vsepc)).
        unfold LoopVerificationl.loop_pre.
        iSplitR "Hhandler Hdata HR".
        - unfold LoopVerificationl.Step_pre.
          cbn - [ptstoSthL interp_ptstomem].
          iFrame "Hgprs Hpmpcfg Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmst Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hsscratch Hmcause Hscause".
          iSplitR; first auto.
          by iApply memAdv_pmpPolicy.
        - iFrame "HR".
          iSplitR.
          { iIntros "!> [H' _]". iDestruct (LoopVerificationl.M_CSRMod_machine with "H'") as %Heq.
            cbn in Heq; discriminate Heq. }
          iSplitL "Hhandler Hdata".
          { iIntros "!> [H' HR]".
            iApply (femtokernel_handler_safe with "Hmmio [] [$Hhandler $Hdata] H' HR").
            iPureIntro; discriminate. }
          iSplitR.
          { iIntros "!> [H' _]". iDestruct (LoopVerificationl.MRET_machine with "H'") as %Heq.
            cbn in Heq; discriminate Heq. }
          iIntros "!> [H' _]". iDestruct (LoopVerificationl.SRET_machine with "H'") as %Heq.
          cbn in Heq; discriminate Heq.
      Qed.

      Lemma femtokernel_init_safe (archstate : ArchState) (vmie : Val ty_Minterrupts) :
        ⊢ RVPTVl.exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
          ∗ ptsto_instrs_handler
          ∗ ptstoSthL advAddrs
          ∗ asn_interpret femtokernel_init_pre (csrs_valuation archstate vmie ►► [env] ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N init_addr])
          ∗ interp_gprs {[x1]}
          ∗ (∃ v : Val ty_xlenbits, interp_ptstomem (bv.of_N data_addr) v)
          ∗ (∃ v, mscratch ↦ᵣ v)
          ∗ (∃ v : Val ty_scause, scause ↦ᵣ v)
          ∗ (∃ v : Val ty_xlenbits, sscratch ↦ᵣ v)
          ∗ (∃ v : Val ty_xlenbits, sepc ↦ᵣ v)
          ∗ (∃ v : Val ty_xlenbits, stvec ↦ᵣ v)
          ∗ femto_inv_mmio
          ∗ phantom_res
            -∗
            WP_loop.
      Proof.
        iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hdata & Hmscratch & Hscause & Hsscratch & Hsepc & Hstvec & #Hmem & HR)".
        iPoseProof (contract_femtoinit_verified__l (bv.of_N init_addr) archstate vmie) as "Htrip".
        iApply (RVPTVl.WP_loop_semTripleBlock with "Hpro [Hpre] Htrip"); first iExact "Hpre".
        iIntros (an) "(Hpost & Hepi)".
        cbn - [asn_regs_ptsto interp_pmp_entries].
        iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hmideleg & Hmedeleg & Hcurpriv & Hx1 & Hpmpentries)".
        iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
        { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
            try solve_subseteq.
          reduce_big_sepS_big_sepL.
          iFrame "Hgprs".
          iFrame "Hx1". by cbn. }
        iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
        rewrite ?bv.add_zero_l.
        iApply (femtokernel_manualStep with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hmepc $Hscause $Hsscratch $Hsepc $Hstvec $Hmideleg $Hmedeleg $Hcurpriv $Hgprs $Hpmpentries $Hmem $Hpc $Hnpc $Hhandler $Hdata $Hadv $HR]").
      Qed.
    End WithUnarySailGS.

    (* Integrity: starting from a memory that contains the FemtoKernel and whose
       MMIO trace satisfies mmio_pred, every reachable state still has a trace
       satisfying mmio_pred. Note that U-mode code is arbitrary. *)
    Lemma femtokernel_endToEnd {γ γ' : RegStore} {μ μ' : Memory}
          {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} (secret : Val ty_xlenbits) :
      mem_has_femtokernel μ secret ->
      mmio_pred bytes_per_word (memory_trace μ) ->
      fun_powered_on μ = true -> (* The machine starts powered on *)
      femto_init_regs γ ->
      ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
      mmio_pred bytes_per_word (memory_trace μ').
    Proof.
      intros μfk μpred μon
        (γmstatus & γcurpriv & γpmp0cfg & γpmpaddr0 & γpmp1cfg & γpmpaddr1 & γpc & γmideleg & γmedeleg) steps.
      refine (RVPADEQUACYl.adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _).
      iIntros (Σ sG mGS) "(Hmem & Hregs)".
      iDestruct "Hmem" as "(Hmem & Hfrag & Hnpa & Hnp & Hpw & Hfrago & Hnpao & Hph)".
      iPoseProof (femtokernel_splitMemory with "Hmem") as "(Hinit & Hhandler & Hdata & Hadv)"; try eassumption.
      iPoseProof (intro_ptstoSthL with "Hadv") as "Hadv".
      (* Allocate the shared invariant, with the phantom execution in sync. *)
      iMod (inv.inv_alloc femto_inv_mmio_ns ⊤
              (∃ t, side_inv bytes_per_word mc_ghGS2_left t ∗ side_inv bytes_per_word mc_ghGS2_right t)
             with "[Hfrag Hnpa Hfrago Hnpao]") as "#Hinv".
      { iNext. iExists (filter_adv_observable (memory_trace μ)).
        rewrite inv_mmio_body_own_other.
        iSplitL "Hfrag Hnpa".
        - iExists _. iFrame "Hfrag". iSplitR; first done. iLeft. by iFrame "Hnpa".
        - iExists _. iFrame "Hfrago". iSplitR; first done. iLeft. by iFrame "Hnpao". }
      iModIntro.
      iSplitL.
      - destruct (env.view δ).
        iApply (femtokernel_init_safe
                  (femto_init_archstate γ)
                  (read_register γ mie)
                  with "[-]").
        #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
        iEval (rewrite μon) in "Hpw".
        iFrame "Hinit Hhandler Hadv Hinv Hnp Hpw Hph Hdata".
        unfold RVPADEQUACYl.own_regstore. cbn - [interp_gprs].
        rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc γmideleg γmedeleg.
        iDestruct "Hregs" as "(Hpc & Hnpc & Hmstatus & Hmie & Hmip & Hmideleg & Hmedeleg & Hmtvec & Hmscratch & Hmepc & Hmcause & Hstvec & Hsscratch & Hsepc & Hscause & Hcp & Hx1 & Hregs)".
        iFrame "Hpc Hnpc Hmstatus Hmie Hmip Hmideleg Hmedeleg Hmtvec Hmscratch Hmepc Hmcause Hstvec Hsscratch Hsepc Hscause Hcp Hx1".
        iDestruct "Hregs" as "(Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 & Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 & Hx20 & Hx21 & Hx22 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 & Hx30 & Hx31 & Hp0 & Hp1 & Ha0 & Ha1 & _)".
        iFrame "Hp0 Hp1 Ha0 Ha1".
        iSplitR; first (iPureIntro; split; [by vm_compute | done]).
        unfold interp_gprs; reduce_big_sepS_big_sepL; cbn.
        iFrame.
      - iIntros "Hmem".
        iInv "Hinv" as ">(%t & Hsides)" "_".
        rewrite inv_mmio_body_own_other.
        iDestruct "Hsides" as "[(%ts & Hf & %Hpred & _) _]".
        iDestruct "Hmem" as "(%memmap & _ & _ & Htr & _)".
        iDestruct (trace.trace_full_frag_eq with "Htr Hf") as %->.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  End Integrity.

  Section RelationalVerification.

    Definition asn_interpret_left `{sailGS2 Σ} : ∀ {Γ : LCtx}, Assertion Γ -> Valuation Γ -> iProp Σ :=
      @asn.interpret _ (UnaryPredicateDefIProp__l sailGS2_sailGS_left).

    Definition asn_interpret_right `{sailGS2 Σ} : ∀ {Γ : LCtx}, Assertion Γ -> Valuation Γ -> iProp Σ :=
      @asn.interpret _ (UnaryPredicateDefIProp__r sailGS2_sailGS_right).

    Import LoopVerification.
    Import ArchState (ArchState).

    Definition interp_ptstomem2 `{mG : memGS2 Σ} {width : nat} (addr : Addr) (v__l v__r : bv (width * byte)) : iProp Σ :=
      (@RVPCOM.interp_ptstomem _ memGS_left width addr v__l
       ∗ @RVPCOM.interp_ptstomem _ memGS_right width addr v__r)%I.

    Section WithAssertionNotations.
      Import asn.notations.
      Import TermNotations.
      Import bv.notations.

      (* We define _rel analogues of the non _rel version for the secret_write pre and post.
         The difference is that we omit the data ↦ secret, since we will have two different secrets. *)
      Example femtokernel_handler_secret_write_pre_rel : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_secret_write_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        x1 ↦ term_var "x1".

      Example femtokernel_handler_dispatch_pre_rel : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_pre handler_dispatch_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        x1 ↦ term_var "x1".

      Example femtokernel_handler_ack_post_rel :
        Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
        femtokernel_handler_shared_post (term_val ty_privilege Machine) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        term_var "an" = term_val ty_xlenbits (bv.of_N handler_exit_addr) ∗
        x1 ↦ term_val ty_xlenbits bv.zero ∗
        x5 ↦ term_val ty_xlenbits (bv.of_N 42) ∗
        asn.chunk (chunk_user (Sig.written bytes_per_word)
                     [term_val ty_xlenbits (bv.of_N mmio_write_adv);
                      term_val (ty_bytes bytes_per_word) (bv.of_N 42)]).

      Example femtokernel_handler_secret_write_post_rel :
        Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
        asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_secret_write_size) ∗
        x1 ↦ term_val ty_xlenbits bv.zero.

    End WithAssertionNotations.

    #[local] Ltac destruct_seps :=
      repeat (iRename select (_ ∗ _)%I into "H'";
              iDestruct "H'" as "(? & ?)");
      repeat (iRename select (bi_exist _) into "H'";
              iDestruct "H'" as "(% & ?)");
      repeat (iRename select (_ ∗ _)%I into "H'";
              iDestruct "H'" as "(? & ?)").

    #[local] Ltac solve_split_generic :=
      iIntros; cbn - [RVPCOM.interp_ptstomem];
      unfold reg_pointsTo21, reg_pointsTo2, interp_ptstomem2, nothingPending2, written2, powered2;
      destruct_seps;
      repeat (iRename select (reg_pointsTo _ _)%I into "H'";
              iFrame "H'");
      repeat (iRename select (RVPCOM.nothingPending)%I into "H'";
              iFrame "H'");
      repeat (iRename select (RVPCOM.written _)%I into "H'";
              iFrame "H'");
      repeat (iRename select (RVPCOM.powered _)%I into "H'";
              iFrame "H'");
      repeat (iRename select (RVPCOM.interp_ptstomem _ _)%I into "H'";
              iFrame "H'");
      repeat (iRename select (⌜_⌝ ∧ emp)%I into "H'";
              iDestruct "H'" as "[#H' _]";
              try iFrame "H'"; try iDestruct "H'" as "?");
      try (iRename select (interp_inv_mmio _) into "Hmmio";
           iDestruct "Hmmio" as "#Hmmio");
      repeat (iRename select (⌜_ = _⌝)%I into "Heq";
              iDestruct "Heq" as "->");
      auto.

    Lemma sep_sep_swap {PROP : bi} (A B C D : PROP) :
      ((A ∗ C) ∗ (B ∗ D) ⊢ (A ∗ B) ∗ (C ∗ D))%I.
    Proof. iIntros "[[$ $] [$ $]]". Qed.

    #[local] Ltac solve_split_leaf :=
      first
        [ solve [ solve_split_generic ]
        | solve [ solve_split_generic; case_match; solve_split_generic ] ].

    #[local] Ltac solve_leaf :=
      first [ reflexivity | refine (bi.sep_elim_l _ _) | solve_split_leaf ].

    (* The binary assertion is a tree of pairs, while the goal is a pair of
       trees. We transpose the two trees node by node instead of framing
       each individual resource. *)
    #[local] Ltac split_tree :=
      first
        [ lazymatch goal with
          | |- ((?T1 ∗ ?T2) ⊢ (?L1 ∗ ?L2) ∗ (?R1 ∗ ?R2))%I =>
              transitivity ((L1 ∗ R1) ∗ (L2 ∗ R2))%I;
              [ apply bi.sep_mono | apply sep_sep_swap ]
          end; split_tree
        | solve_leaf ].

    #[local] Ltac combine_tree :=
      first
        [ lazymatch goal with
          | |- ((?L1 ∗ ?L2) ∗ (?R1 ∗ ?R2) ⊢ ?B1 ∗ ?B2)%I =>
              transitivity ((L1 ∗ R1) ∗ (L2 ∗ R2))%I;
              [ apply sep_sep_swap | apply bi.sep_mono ]
          end; combine_tree
        | solve_leaf ].

    #[local] Ltac extract_leaf :=
      first
        [ (etrans; [refine (bi.sep_elim_l _ _) |]; extract_leaf)
        | (etrans; [refine (bi.sep_elim_r _ _) |]; extract_leaf)
        | reflexivity
        | apply bi.and_elim_l ].

    #[local] Ltac find_eq x T :=
      lazymatch T with
      | context [(⌜x = ?X⌝ ∧ emp)%I] => X
      end.

    #[local] Ltac solve_binary_split :=
      iIntros; cbn - [RVPCOM.interp_ptstomem];
      iStopProof; split_tree.

    #[local] Ltac solve_persistent_preds :=
      iIntros; cbn - [RVPCOM.interp_ptstomem];
      unfold femto_inv_mmio; iStopProof;
      first
        [ apply bi.persistent_entails_l; [ unfold interp_inv_mmio; apply _
          | extract_leaf ]
        | solve_split_leaf ].

    #[local] Ltac combine_attempt :=
      lazymatch goal with
      | |- ((?L ∗ ?R) ⊢ ⌜?x = ?y⌝ ∗ ?B)%I =>
          let X := find_eq x L in
          let Y := find_eq y R in
          let T := type of L in
          transitivity (⌜x = y⌝ ∗ (L ∗ R))%I;
          [ apply bi.persistent_entails_l; [ apply _ |];
            transitivity ((⌜x = X⌝ ∗ ⌜y = Y⌝)%I : T);
            [ apply bi.sep_mono; extract_leaf
            | iIntros "[%E1 %E2]"; iPureIntro; congruence ]
          | iIntros "[%Heq [HL HR]]"; subst;
            iSplitL ""; [ iPureIntro; reflexivity | iStopProof; combine_tree ] ]
      end.

    #[local] Ltac solve_binary_combine :=
      intros; iIntros "HL HR"; cbn - [RVPCOM.interp_ptstomem];
      iStopProof;
      first
        [ combine_attempt
        | case_match; cbn - [RVPCOM.interp_ptstomem]; combine_attempt
        | solve_split_leaf ].

    Lemma femtokernel_handler_entry_pre_persistent_preds `{sailGS2 Σ} (x5 x10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] in
      asn.interpret femtokernel_handler_entry_pre Σ -∗
      femto_inv_mmio ∗ asn.interpret femtokernel_handler_entry_pre Σ.
    Proof. solve_persistent_preds. Qed.

    Lemma femtokernel_handler_secret_write_pre_persistent_preds `{sailGS2 Σ} (x1 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ x1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] in
      asn.interpret femtokernel_handler_secret_write_pre_rel Σ -∗
      femto_inv_mmio ∗ asn.interpret femtokernel_handler_secret_write_pre_rel Σ.
    Proof. solve_persistent_preds. Qed.

    Lemma femtokernel_init_pre_binary_split `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr] in
      asn.interpret femtokernel_init_pre Σ -∗
      asn_interpret_left femtokernel_init_pre Σ ∗
      asn_interpret_right femtokernel_init_pre Σ.
    Proof. solve_binary_split. Qed.

    Lemma femtokernel_handler_entry_pre_binary_split `{sailGS2 Σ} (x5 x10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] in
      asn.interpret femtokernel_handler_entry_pre Σ -∗
      asn_interpret_left femtokernel_handler_entry_pre Σ ∗
      asn_interpret_right femtokernel_handler_entry_pre Σ.
    Proof. solve_binary_split. Qed.

    Lemma femtokernel_handler_secret_write_pre_binary_split `{sailGS2 Σ} (x1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ__csrs := (csrs_valuation archstate vmie) in
      let Σ__x1   := [env].["x1" ∷ ty_xlenbits ↦ x1] in
      let Σ__a    := [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] in
      let Σ__secret secret := Σ__csrs ►► Σ__x1 ►► [env].["secret" ∷ ty_xlenbits ↦ secret] ►► Σ__a in
      asn.interpret femtokernel_handler_secret_write_pre_rel (Σ__csrs ►► Σ__x1 ►► Σ__a) ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
      asn_interpret_left femtokernel_handler_secret_write_pre (Σ__secret secret1) ∗
      asn_interpret_right femtokernel_handler_secret_write_pre (Σ__secret secret2).
    Proof. solve_split_leaf. Qed.

    Lemma femtokernel_handler_exit_pre_binary_split `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] in
      asn.interpret femtokernel_handler_exit_pre Σ -∗
      asn_interpret_left femtokernel_handler_exit_pre Σ ∗
      asn_interpret_right femtokernel_handler_exit_pre Σ.
    Proof. solve_binary_split. Qed.

    Lemma femtokernel_init_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N init_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_init_post (Σ na1) -∗
      asn_interpret_right femtokernel_init_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_init_post (Σ na1).
    Proof. solve_binary_combine. Qed.

    Lemma femtokernel_handler_entry_post_binary_combine `{sailGS2 Σ} (x5 x10 na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ na := ι__csrs.["x5"∷ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a"∷ty_xlenbits ↦ bv.of_N handler_entry_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_handler_entry_post (Σ na1) -∗
      asn_interpret_right femtokernel_handler_entry_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_entry_post (Σ na1).
    Proof. solve_binary_combine. Qed.

    Lemma femtokernel_handler_secret_write_post_binary_combine `{sailGS2 Σ} (x1 secret1 secret2 na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ__rel na := ι__csrs.["x1"∷ty_xlenbits ↦ x1].["a"∷ty_xlenbits ↦ bv.of_N handler_secret_write_addr].["an"∷ty_xlenbits ↦ na] in
      let Σ secret na := ι__csrs.["x1"∷ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret].["a"∷ty_xlenbits ↦ bv.of_N handler_secret_write_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_handler_secret_write_post (Σ secret1 na1) -∗
      asn_interpret_right femtokernel_handler_secret_write_post (Σ secret2 na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_secret_write_post_rel (Σ__rel na1)
      ∗ interp_ptstomem2 (bv.of_N data_addr) secret1 secret2.
    Proof. solve_split_leaf. Qed.

    Lemma femtokernel_handler_shutdown_check_pre_binary_split `{sailGS2 Σ} (x1 x5 x10 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr] in
      asn.interpret femtokernel_handler_shutdown_check_pre Σ -∗
      asn_interpret_left femtokernel_handler_shutdown_check_pre Σ ∗
      asn_interpret_right femtokernel_handler_shutdown_check_pre Σ.
    Proof. solve_binary_split. Qed.

    Lemma femtokernel_handler_shutdown_check_post_binary_combine `{sailGS2 Σ} (x1 x5 x10 na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ na := ι__csrs.["x1"∷ty_xlenbits ↦ x1].["x5"∷ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10].["a"∷ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_handler_shutdown_check_post (Σ na1) -∗
      asn_interpret_right femtokernel_handler_shutdown_check_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_shutdown_check_post (Σ na1).
    Proof. solve_binary_combine. Qed.

    Lemma femtokernel_handler_shutdown_pre_binary_split `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_addr] in
      asn.interpret femtokernel_handler_shutdown_pre Σ -∗
      asn_interpret_left femtokernel_handler_shutdown_pre Σ ∗
      asn_interpret_right femtokernel_handler_shutdown_pre Σ.
    Proof. solve_binary_split. Qed.

    Lemma femtokernel_handler_shutdown_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N handler_shutdown_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_handler_shutdown_post (Σ na1) -∗
      asn_interpret_right femtokernel_handler_shutdown_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_shutdown_post (Σ na1).
    Proof. solve_binary_combine. Qed.

    Lemma femtokernel_handler_exit_post_binary_combine `{sailGS2 Σ} (na1 na2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ na := ι__csrs.["a"∷ty_xlenbits ↦ bv.of_N handler_exit_addr].["an"∷ty_xlenbits ↦ na] in
      asn_interpret_left femtokernel_handler_exit_post (Σ na1) -∗
      asn_interpret_right femtokernel_handler_exit_post (Σ na2) -∗
      ⌜na1 = na2⌝ ∗ asn.interpret femtokernel_handler_exit_post (Σ na1).
    Proof. solve_binary_combine. Qed.

    Definition ptsto_instrs_handler2 `{sailGS2 Σ} : iProp Σ :=
      @ptsto_instrs_handler _ memGS_left
      ∗ @ptsto_instrs_handler _ memGS_right.

    Lemma ptsto_instrs_handler2_equiv `{sailGS2 Σ} :
      ptsto_instrs_handler2 ⊣⊢
        ptsto_instrs (bv.of_N handler_entry_addr) (filter_AST femtokernel_handler_entry) ∗
        ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
        ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
        ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
        ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
        ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
        ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit).
    Proof.
      unfold ptsto_instrs_handler2, ptsto_instrs_handler.
      rewrite !ptsto_instrs_equiv.
      iSplit.
      - iIntros "((Hhentry1 & Hhdispatch1 & Hhnotzero1 & Hhiszero1 & Hhcheck1 & Hhshutdown1 & Hhsecret1 & Hhexit1) & (Hhentry2 & Hhdispatch2 & Hhnotzero2 & Hhiszero2 & Hhcheck2 & Hhshutdown2 & Hhsecret2 & Hhexit2))".
        iFrame.
      - iIntros "((Hhentry1 & Hhentry2) & (Hhdispatch1 & Hhdispatch2) & (Hhnotzero1 & Hhnotzero2) & (Hhiszero1 & Hhiszero2) & (Hhcheck1 & Hhcheck2) & (Hhshutdown1 & Hhshutdown2) & (Hhsecret1 & Hhsecret2) & (Hhexit1 & Hhexit2))".
        iFrame.
    Qed.

    (* TODO: shouldn't be needed, probably defined elsewhere already? *)
    #[local] Notation "a '↦ᵣ' t" := (reg_pointsTo2 a t t).

    Definition femtokernel_safe_shared_pre2 `{sailGS2 Σ} (addr : N) (b : Block) : iProp Σ :=
      exec_instructions_prologue (bv.of_N addr) (filter_AST b) ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        @interp_pmp_addr_access _ sailGS2_memGS liveAddrs mmioAddrs femto_pmpentries User. (* Not needed for handler, but required for the rest of execution *)

    Lemma femtokernel_handler_exit_safe_rel `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femtokernel_safe_shared_pre2 handler_exit_addr femtokernel_handler_exit ∗
        asn.interpret femtokernel_handler_exit_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N handler_exit_addr] ∗
        interp_gprs ∅ ∗
        nothingPending2 ∗
        powered2 true ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
             ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
             LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
        -∗
        WP2_loop nothingPending2.
    Proof.
      iIntros "((Hpro & [%vmscratch Hmscratch] & HaccU) & Hpre & Hgprs & Hnp & Hpow & Htrap)".
      iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_exit_pre _) _ _
                (λ a na, asn.interpret femtokernel_handler_exit_post _)
               with "Hpow Hpro Hpre []").
      - iIntros "Hpre".
        iPoseProof (femtokernel_handler_exit_pre_binary_split with "Hpre")
          as "(Hpre1 & Hpre2)".
        iPoseProof (contract_femtohandler_exit_verified__l (bv.of_N handler_exit_addr) archstate vmie with "Hpre1") as "H1".
        iPoseProof (contract_femtohandler_exit_verified__r (bv.of_N handler_exit_addr) archstate vmie with "Hpre2") as "H2".
        iApply (step_n_focus with "H1 H2").
        iIntros (na1 na2) "(H1 & H2)".
        iApply (femtokernel_handler_exit_post_binary_combine with "H1 H2").
      - iIntros (an) "(Hpost & Hepi & Hpow)".
        iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
        iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & [%Han _])"; cbn - [interp_ptstomem] in *.
        iAssert (interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries (ArchState.mpp (ArchState.mstate archstate))) with "[HaccU]" as "Hacc".
        { assert (Hmpp' : ArchState.mpp (ArchState.mstate archstate) = User ∨ ArchState.mpp (ArchState.mstate archstate) = Supervisor)
            by (destruct (ArchState.mpp (ArchState.mstate archstate)); auto; congruence).
          destruct Hmpp' as [Heq|Heq]; rewrite Heq; first iExact "HaccU".
          by iApply interp_pmp_addr_access_s_u_eq. }
        iApply (LoopVerificationBinary.valid_semTriple_loop $! nothingPending2 (femto_return_archstate archstate vmscratch an)).
        unfold LoopVerificationBinary.loop_pre.
        iSplitR "Hnp Hpow Htrap Hinstrs".
        { unfold LoopVerificationBinary.Step_pre; cbn.
          iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
          auto. }
        iFrame "Hnp Hpow".
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.M_CSRMod_machine with "H'") as %Heq.
          cbn in Heq. contradiction. }
        iSplitL "Htrap Hinstrs".
        { iIntros "!> (H' & Hnp & Hpow)". iApply ("Htrap" $! (ArchState.mpp (ArchState.mstate archstate)) with "[//] Hinstrs H' Hnp Hpow"). }
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.MRET_machine with "H'") as %Heq.
          cbn in Heq. contradiction. }
        iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.SRET_machine with "H'") as %Heq.
        cbn in Heq. contradiction.
    Qed.

    Lemma femtokernel_handler_dispatch_pre_persistent_preds `{sailGS2 Σ} (x1 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ := (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ x1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr] in
      asn.interpret femtokernel_handler_dispatch_pre_rel Σ -∗
      femto_inv_mmio ∗ asn.interpret femtokernel_handler_dispatch_pre_rel Σ.
    Proof. solve_persistent_preds. Qed.

    Lemma femtokernel_handler_dispatch_pre_binary_split `{sailGS2 Σ} (x1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let Σ__csrs := (csrs_valuation archstate vmie) in
      let Σ__x1   := [env].["x1" ∷ ty_xlenbits ↦ x1] in
      let Σ__a    := [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr] in
      let Σ__secret secret := Σ__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret] ►► Σ__a in
      asn.interpret femtokernel_handler_dispatch_pre_rel (Σ__csrs ►► Σ__x1 ►► Σ__a) ∗
      interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
      asn_interpret_left femtokernel_handler_dispatch_pre (Σ__secret secret1) ∗
      asn_interpret_right femtokernel_handler_dispatch_pre (Σ__secret secret2).
    Proof. solve_split_leaf. Qed.

    (* The not_zero and is_zero blocks have the same postcondition, so both
       executions can be recombined at the exit block, independently of the
       path they took. *)
    Lemma femtokernel_handler_ack_post_binary_combine `{sailGS2 Σ}
      (x1l x5l x1r x5r al ar an1 an2 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      let Σ x1 x5 secret a an := ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                                         ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an] in
      asn_interpret_left femtokernel_handler_ack_post (Σ x1l x5l secret1 al an1) -∗
      asn_interpret_right femtokernel_handler_ack_post (Σ x1r x5r secret2 ar an2) -∗
      ⌜an1 = an2⌝ ∗ asn.interpret femtokernel_handler_ack_post_rel ι__csrs.["a" ∷ ty_xlenbits ↦ al].["an" ∷ ty_xlenbits ↦ an1]
      ∗ interp_ptstomem2 (bv.of_N data_addr) secret1 secret2.
    Proof. solve_binary_combine. Qed.

    Lemma femtokernel_handler_dispatch_nonempty : filter_AST femtokernel_handler_dispatch ≠ []%list.
    Proof. vm_compute. discriminate. Qed.

    Lemma femtokernel_handler_is_zero_nonempty : filter_AST femtokernel_handler_is_zero ≠ []%list.
    Proof. vm_compute. discriminate. Qed.

    Lemma femtokernel_handler_not_zero_nonempty : filter_AST femtokernel_handler_not_zero ≠ []%list.
    Proof. vm_compute. discriminate. Qed.

    (* A lemma that reasons on the path taken for the left execution, keeping the right execution untouched.
       We also have a _right variant of it. Bit annoying to have this duplication, should probably improve
       this at some point. The difference between the left and right lemmas is which modules (left or right)
       we need to prove it. *)
    Lemma femtokernel_dispatch_path_left `{sailGS2 Σ} (vx1 vx5 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      ⊢ femto_inv_mmio -∗
        @RVPTVl.exec_instructions_prologue _ sailGS2_sailGS_left (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
        asn_interpret_left femtokernel_handler_dispatch_pre
          (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                   ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) -∗
        @RVPCOM.nothingPending _ (@mc_wpGS _ (@mc_ghGS2_left _ sailGS2_memGS)) -∗
        powered_left true -∗
        @reg_pointsTo _ sailRegGS2_sailRegGS_left _ x5 vx5 -∗
        @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
        @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
        (∀ x1 x5 a an,
           asn_interpret_left femtokernel_handler_ack_post
             (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                      ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]) -∗
           @reg_pointsTo _ sailRegGS2_sailRegGS_left _ pc an -∗
           @reg_pointsTo _ sailRegGS2_sailRegGS_left _ nextpc an -∗
           @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
           @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
           @RVPCOM.ptsto_instrs _ memGS_left (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
           powered_left true -∗
           WP2_loop nothingPending2) -∗
        WP2_loop nothingPending2.
    Proof.
      iIntros (ι__csrs) "#Hinv Hpro Hpre Hnp Hp Hx5 Hnz Hiz Hk".
      iPoseProof (contract_femtohandler_dispatch_verified__l vx1 secret (bv.of_N handler_dispatch_addr) archstate vmie) as "Htrip".
      iApply (@WP2_loop_semTripleBlock_left _ _ _ _ (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) _
                femtokernel_handler_dispatch_nonempty with "Hp Hpro [Hpre] Htrip [Hnp Hx5 Hnz Hiz Hk]");
        first iExact "Hpre".
      iIntros (an) "(Hpost & (Hpc & Hcode & Hnpc) & Hp)".
      iEval (cbn - [RVPCOM.interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hdata)".
      case_match; iDestruct "Han" as "[-> _]".
      - (* The secret is zero: is_zero block. *)
        iPoseProof (contract_femtohandler_is_zero_verified__l secret vx5 secret (bv.of_N handler_is_zero_addr) archstate vmie) as "Htrip'".
        iApply (@WP2_loop_semTripleBlock_left _ _ _ _ (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) _
                  femtokernel_handler_is_zero_nonempty with "Hp [Hpc Hiz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hnz]").
        + iFrame "Hpc Hiz". by iExists _.
        + cbn - [RVPCOM.interp_ptstomem].
          iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
          iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hnz Hcode' Hp").
      - (* The secret is not zero: not_zero block. *)
        iPoseProof (contract_femtohandler_not_zero_verified__l secret vx5 secret (bv.of_N handler_not_zero_addr) archstate vmie) as "Htrip'".
        iApply (@WP2_loop_semTripleBlock_left _ _ _ _ (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) _
                  femtokernel_handler_not_zero_nonempty with "Hp [Hpc Hnz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hiz]").
        + iFrame "Hpc Hnz". by iExists _.
        + cbn - [RVPCOM.interp_ptstomem].
          iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
          iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hcode' Hiz Hp").
    Qed.

    (* Analogues to femtokernel_dispatch_path_left, see comment there. *)
    Lemma femtokernel_dispatch_path_right `{sailGS2 Σ} (vx1 vx5 secret : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      let ι__csrs := csrs_valuation archstate vmie in
      ⊢ femto_inv_mmio -∗
        @RVPTVr.exec_instructions_prologue _ sailGS2_sailGS_right (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
        asn_interpret_right femtokernel_handler_dispatch_pre
          (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ vx1].["secret" ∷ ty_xlenbits ↦ secret]
                   ►► [env].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr]) -∗
        @RVPCOM.nothingPending _ (@mc_wpGS _ (@mc_ghGS2_right _ sailGS2_memGS)) -∗
        powered_right true -∗
        @reg_pointsTo _ sailRegGS2_sailRegGS_right _ x5 vx5 -∗
        @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
        @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
        (∀ x1 x5 a an,
           asn_interpret_right femtokernel_handler_ack_post
             (ι__csrs ►► [env].["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
                      ►► [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]) -∗
           @reg_pointsTo _ sailRegGS2_sailRegGS_right _ pc an -∗
           @reg_pointsTo _ sailRegGS2_sailRegGS_right _ nextpc an -∗
           @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
           @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
           @RVPCOM.ptsto_instrs _ memGS_right (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
           powered_right true -∗
           WP2_loop nothingPending2) -∗
        WP2_loop nothingPending2.
    Proof.
      iIntros (ι__csrs) "#Hinv Hpro Hpre Hnp Hp Hx5 Hnz Hiz Hk".
      iPoseProof (contract_femtohandler_dispatch_verified__r vx1 secret (bv.of_N handler_dispatch_addr) archstate vmie) as "Htrip".
      iApply (@WP2_loop_semTripleBlock_right _ _ _ _ (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) _
                femtokernel_handler_dispatch_nonempty with "Hp Hpro [Hpre] Htrip [Hnp Hx5 Hnz Hiz Hk]");
        first iExact "Hpre".
      iIntros (an) "(Hpost & (Hpc & Hcode & Hnpc) & Hp)".
      iEval (cbn - [RVPCOM.interp_ptstomem]) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hdata)".
      case_match; iDestruct "Han" as "[-> _]".
      - (* The secret is zero: is_zero block. *)
        iPoseProof (contract_femtohandler_is_zero_verified__r secret vx5 secret (bv.of_N handler_is_zero_addr) archstate vmie) as "Htrip'".
        iApply (@WP2_loop_semTripleBlock_right _ _ _ _ (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) _
                  femtokernel_handler_is_zero_nonempty with "Hp [Hpc Hiz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hnz]").
        + iFrame "Hpc Hiz". by iExists _.
        + cbn - [RVPCOM.interp_ptstomem].
          iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
          iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hnz Hcode' Hp").
      - (* The secret is not zero: not_zero block. *)
        iPoseProof (contract_femtohandler_not_zero_verified__r secret vx5 secret (bv.of_N handler_not_zero_addr) archstate vmie) as "Htrip'".
        iApply (@WP2_loop_semTripleBlock_right _ _ _ _ (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) _
                  femtokernel_handler_not_zero_nonempty with "Hp [Hpc Hnz Hnpc] [Hshared Hmstatus Hnp Hx1 Hx5 Hdata] Htrip' [Hk Hcode Hiz]").
        + iFrame "Hpc Hnz". by iExists _.
        + cbn - [RVPCOM.interp_ptstomem].
          iFrame "Hinv Hmstatus Hnp Hx1 Hx5 Hdata".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
        + iIntros (an') "(Hpost & (Hpc & Hcode' & Hnpc) & Hp)".
          iApply ("Hk" with "Hpost Hpc Hnpc Hcode Hcode' Hiz Hp").
    Qed.

    Lemma femtokernel_handler_dispatch_safe_rel `{sailGS2 Σ} (vx1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femtokernel_safe_shared_pre2 handler_dispatch_addr femtokernel_handler_dispatch ∗
        asn.interpret femtokernel_handler_dispatch_pre_rel (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ vx1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_dispatch_addr] ∗
        interp_gprs {[x1]} ∗
        interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
        nothingPending2 ∗
        powered2 true ∗
        ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
        ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
           ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
           ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
           interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
        -∗
        WP2_loop nothingPending2.
    Proof.
      iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & Hnp & [Hpl Hpr] & Hhnz & Hhiz & Hhexit & Hk)".
      iPoseProof (femtokernel_handler_dispatch_pre_persistent_preds with "Hpre") as "(#Hinv & Hpre)".
      iPoseProof (femtokernel_handler_dispatch_pre_binary_split with "[$Hpre $Hdata]") as "(Hpre1 & Hpre2)".
      iPoseProof (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([%vx5 Hx5] & _)".
      subst l; clear Hl Hdup.
      unfold reg_pointsTo21, reg_pointsTo2. iDestruct "Hx5" as "[Hx5l Hx5r]".
      unfold exec_instructions_prologue, reg_pointsTo21, reg_pointsTo2.
      iDestruct "Hpro" as "([Hpcl Hpcr] & Hcode & [%npc [Hnpcl Hnpcr]])".
      iDestruct (ptsto_instrs_equiv with "Hcode") as "[Hcodel Hcoder]".
      iDestruct (ptsto_instrs_equiv with "Hhnz") as "[Hnzl Hnzr]".
      iDestruct (ptsto_instrs_equiv with "Hhiz") as "[Hizl Hizr]".
      iDestruct "Hnp" as "[Hnpl Hnpr]".
      (* Run the left execution until the exit block. *)
      iApply (femtokernel_dispatch_path_left vx1 vx5 secret1 archstate vmie
                with "Hinv [Hpcl Hcodel Hnpcl] Hpre1 Hnpl Hpl Hx5l Hnzl Hizl").
      { iFrame "Hpcl Hcodel". by iExists _. }
      iIntros (x1l x5l al anl) "Hpostl Hpcl Hnpcl Hcodel Hnzl Hizl Hpl".
      (* Run the right execution until the exit block. *)
      iApply (femtokernel_dispatch_path_right vx1 vx5 secret2 archstate vmie
                with "Hinv [Hpcr Hcoder Hnpcr] Hpre2 Hnpr Hpr Hx5r Hnzr Hizr").
      { iFrame "Hpcr Hcoder". by iExists _. }
      iIntros (x1r x5r ar anr) "Hpostr Hpcr Hnpcr Hcoder Hnzr Hizr Hpr".
      iDestruct (femtokernel_handler_ack_post_binary_combine with "Hpostl Hpostr") as "(<- & Hpost & Hdata)".
      iEval (cbn) in "Hpost".
      iDestruct "Hpost" as "(Hshared & Hmstatus & [%Han _] & Hx1 & Hx5 & [Hwl Hwr])"; subst anl.
      iApply (fupd_semWP2 ⊤).
      iMod (written_nothingPending2 bytes_per_word with "Hinv Hwl Hwr") as "Hnp"; first solve_ndisj.
      iModIntro.
      iAssert (∃ v, reg_pointsTo21 x1 v)%I with "[Hx1]" as "Hx1"; first by iExists _.
      iAssert (∃ v, reg_pointsTo21 x5 v)%I with "[Hx5]" as "Hx5"; first by iExists _.
      iAssert (interp_gprs ∅) with "[Hgprs Hx1 Hx5]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1; x5]})); try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        iFrame "Hx1 Hx5". by cbn. }
      iPoseProof (ptsto_instrs_equiv with "[$Hcodel $Hcoder]") as "Hhdispatch".
      iPoseProof (ptsto_instrs_equiv with "[$Hnzl $Hnzr]") as "Hhnz".
      iPoseProof (ptsto_instrs_equiv with "[$Hizl $Hizr]") as "Hhiz".
      iAssert (pc ↦ᵣ bv.of_N handler_exit_addr)%I with "[Hpcl Hpcr]" as "Hpc".
      { unfold reg_pointsTo2. iFrame "Hpcl Hpcr". }
      iAssert (nextpc ↦ᵣ bv.of_N handler_exit_addr)%I with "[Hnpcl Hnpcr]" as "Hnpc".
      { unfold reg_pointsTo2. iFrame "Hnpcl Hnpcr". }
      iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                 ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                 LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
        with "[Hk Hhdispatch Hhnz Hhiz Hdata]" as "Hk".
      { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit Htrap Hnp Hpow".
        iApply ("Hk" with "[//] Hhdispatch Hhnz Hhiz Hdata Hhexit Htrap Hnp Hpow"). }
      iApply (femtokernel_handler_exit_safe_rel _ _ Hmpp).
      iFrame "Hpc Hhexit Hmscratch HaccU Hmstatus Hgprs Hk Hinv Hnp Hpl Hpr"; cbn.
      iSplitL "Hnpc"; first by iExists _.
      repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
      now iPureIntro.
    Qed.

    Lemma femtokernel_handler_secret_write_safe_rel `{sailGS2 Σ} (vx1 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femtokernel_safe_shared_pre2 handler_secret_write_addr femtokernel_handler_secret_write ∗
        asn.interpret femtokernel_handler_secret_write_pre_rel (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ vx1].["a" ∷ ty_xlenbits ↦ bv.of_N handler_secret_write_addr] ∗
        interp_gprs {[x1]} ∗
        interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
        nothingPending2 ∗
        powered2 true ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
           interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
        -∗
        WP2_loop nothingPending2.
    Proof.
      iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & Hnp & Hpow & Hhexit & Htrap)".
      iPoseProof (femtokernel_handler_secret_write_pre_persistent_preds with "Hpre")
                   as "(#Hinv & Hpre)".
      iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_secret_write_pre_rel _) _ _
                (λ a na, asn.interpret femtokernel_handler_secret_write_post_rel _
                         ∗ interp_ptstomem2 (bv.of_N data_addr) secret1 secret2)%I
               with "Hpow Hpro Hpre [Hdata]").
      - iIntros "Hpre".
        iPoseProof (femtokernel_handler_secret_write_pre_binary_split with "[$Hpre $Hdata]")
          as "(Hpre1 & Hpre2)".
        iPoseProof (contract_femtohandler_secret_write_verified__l vx1 secret1 (bv.of_N handler_secret_write_addr) archstate vmie with "Hpre1") as "H1".
        iPoseProof (contract_femtohandler_secret_write_verified__r vx1 secret2 (bv.of_N handler_secret_write_addr) archstate vmie with "Hpre2") as "H2".
        iApply (step_n_focus with "H1 H2").
        iIntros (na1 na2) "(H1 & H2)".
        iApply (femtokernel_handler_secret_write_post_binary_combine with "H1 H2").
      - iIntros (an) "(Hpost & Hepi & Hpow)".
        iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
        iDestruct "Hpost" as "((Hshared & Hmstatus & [%Han _] & Hx1) & Hdata)"; cbn - [interp_ptstomem] in *.
        iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
        { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
            try solve_subseteq.
          iFrame "Hgprs".
          reduce_big_sepS_big_sepL.
          now iFrame "Hx1". }
        iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                   ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                   LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
          with "[Htrap Hinstrs Hdata]" as "Htrap".
        { iIntros "!>" (priv ms ss pc Hpriv) "Hhexit' Htrap' Hnp Hpow".
          iApply ("Htrap" with "[//] Hinstrs Hdata Hhexit' Htrap' Hnp Hpow"). }
        iApply (femtokernel_handler_exit_safe_rel _ _ Hmpp).
        rewrite Han.
        iFrame "Hpc Hhexit Hnpc Hmscratch HaccU Hmstatus Hgprs Htrap Hinv Hnp Hpow"; cbn - [interp_ptstomem].
        repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
        now iPureIntro.
    Qed.

    (* The shutdown check, followed by either powering off both machines, or by
       the secret write. The shutdown request is public, so both executions
       take the same branch. *)
    Lemma femtokernel_handler_shutdown_check_safe_rel `{sailGS2 Σ} (vx1 vx5 vx10 secret1 secret2 : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femto_inv_mmio -∗
        femtokernel_safe_shared_pre2 handler_shutdown_check_addr femtokernel_handler_shutdown_check ∗
        asn.interpret femtokernel_handler_shutdown_check_pre (csrs_valuation archstate vmie).["x1" ∷ ty_xlenbits ↦ vx1].["x5" ∷ ty_xlenbits ↦ vx5].["x10" ∷ ty_xlenbits ↦ vx10].["a" ∷ ty_xlenbits ↦ bv.of_N handler_shutdown_check_addr] ∗
        interp_gprs {[x1; x5; x10]} ∗
        interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
        nothingPending2 ∗
        powered2 true ∗
        ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
        ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) ∗
        ▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
           ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
           ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
           ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
           interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 -∗
           ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
           LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2)
        -∗
        WP2_loop nothingPending2.
    Proof.
      iIntros "#Hinv ((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hdata & Hnp & Hpow & Hhshutdown & Hhsecret & Hhexit & Hk)".
      iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_shutdown_check_pre _) _ _
                (λ a na, asn.interpret femtokernel_handler_shutdown_check_post _)
               with "Hpow Hpro Hpre []").
      - iIntros "Hpre".
        iPoseProof (femtokernel_handler_shutdown_check_pre_binary_split with "Hpre") as "(Hpre1 & Hpre2)".
        iPoseProof (contract_femtohandler_shutdown_check_verified__l vx1 vx5 vx10 (bv.of_N handler_shutdown_check_addr) archstate vmie with "Hpre1") as "H1".
        iPoseProof (contract_femtohandler_shutdown_check_verified__r vx1 vx5 vx10 (bv.of_N handler_shutdown_check_addr) archstate vmie with "Hpre2") as "H2".
        iApply (step_n_focus with "H1 H2").
        iIntros (na1 na2) "(H1 & H2)".
        iApply (femtokernel_handler_shutdown_check_post_binary_combine with "H1 H2").
      - iIntros (an) "(Hpost & Hepi & Hpow)".
        iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
        iEval (cbn - [interp_ptstomem]) in "Hpost".
        iDestruct "Hpost" as "(Hshared & Hmstatus & Han & Hx1 & Hx5 & Hx10)".
        case_match; iDestruct "Han" as "[-> _]".
        + (* Power off both machines. *)
          iAssert (semTripleBlock
                     (λ a, asn.interpret femtokernel_handler_shutdown_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ a])
                     (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown)
                     (λ a na, asn.interpret femtokernel_handler_shutdown_post (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ na]))%I
            as "Htrip'".
          { iIntros "Hpre".
            iPoseProof (femtokernel_handler_shutdown_pre_binary_split with "Hpre") as "(Hpre1 & Hpre2)".
            iPoseProof (contract_femtohandler_shutdown_verified__l (bv.of_N handler_shutdown_addr) archstate vmie with "Hpre1") as "H1".
            iPoseProof (contract_femtohandler_shutdown_verified__r (bv.of_N handler_shutdown_addr) archstate vmie with "Hpre2") as "H2".
            iApply (step_n_focus with "H1 H2").
            iIntros (na1 na2) "(H1 & H2)".
            iApply (femtokernel_handler_shutdown_post_binary_combine with "H1 H2"). }
          iApply (WP2_loop_semTripleBlock_power_off with "Hpow [Hpc Hhshutdown Hnpc] [Hshared Hmstatus Hx5 Hnp] Htrip'").
          * iFrame "Hpc Hhshutdown Hnpc".
          * cbn - [interp_ptstomem].
            iFrame "Hinv Hmstatus Hx5 Hnp".
            repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
            repeat iSplit; try iPureIntro; try done; by vm_compute.
          * iIntros "!>" (an') "(Hpost & _ & [Hoffl Hoffr])".
            iEval (cbn) in "Hpost". iDestruct "Hpost" as "(_ & [Hwl Hwr])".
            iApply (fupd_semWP2 ⊤).
            iMod (written_nothingPending2 bytes_per_word with "Hinv Hwl Hwr") as "Hnp"; first solve_ndisj.
            iModIntro. unfold WP2_loop.
            iApply (semWP2_fun_loop_off with "Hoffl Hoffr").
            iIntros "_ _". iFrame "Hnp". done.
        + (* Perform the secret write. *)
          iAssert (interp_gprs {[x1]}) with "[Hgprs Hx5 Hx10]" as "Hgprs".
          { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5; x10]})); try solve_subseteq.
            iFrame "Hgprs".
            reduce_big_sepS_big_sepL.
            iFrame "Hx5 Hx10". by cbn. }
          iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                     ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                     interp_ptstomem2 (bv.of_N data_addr) (secret1 : Val ty_xlenbits) secret2 -∗
                     ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                     LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
            with "[Hk Hinstrs Hhshutdown]" as "Hksecret".
          { iIntros "!>" (priv ms ss pc Hpriv) "Hhsecret Hdata Hhexit Htrap Hnp Hpow".
            iApply ("Hk" with "[//] Hinstrs Hhshutdown Hhsecret Hdata Hhexit Htrap Hnp Hpow"). }
          iApply (femtokernel_handler_secret_write_safe_rel _ _ _ _ _ Hmpp); cbn - [interp_ptstomem].
          iFrame "Hhsecret Hpc Hnpc Hmscratch HaccU Hmstatus Hgprs Hhexit Hx1 Hdata Hnp Hpow Hksecret Hinv".
          repeat iDestruct "Hshared" as "($ & Hshared)". iFrame "Hshared".
          repeat iSplit; try iPureIntro; try done; by vm_compute.
    Qed.

    Lemma femtokernel_handler_entry_safe_rel `{sailGS2 Σ} (x5_val x10_val : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts) (Hmpp : ArchState.mpp (ArchState.mstate archstate) ≠ Machine) :
      ⊢ femtokernel_safe_shared_pre2 handler_entry_addr femtokernel_handler_entry ∗
        asn.interpret femtokernel_handler_entry_pre (csrs_valuation archstate vmie).["x5" ∷ ty_xlenbits ↦ x5_val].["x10" ∷ ty_xlenbits ↦ x10_val].["a" ∷ ty_xlenbits ↦ bv.of_N handler_entry_addr] ∗
        interp_gprs {[ x1; x5; x10 ]} ∗
        (∃ v, x1 ↦ᵣ v) ∗
        (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) ∗
        nothingPending2 ∗
        powered2 true ∗
        ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
        ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
        ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
        ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
        ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
        ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
        ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit)
        -∗
        WP2_loop nothingPending2.
    Proof.
      iLöb as "IH" forall (x5_val x10_val archstate vmie Hmpp).
      iIntros "((Hpro & Hmscratch & HaccU) & Hpre & Hgprs & Hx1 & Hdata & Hnp & Hpow & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      iPoseProof (femtokernel_handler_entry_pre_persistent_preds with "Hpre")
                   as "(#Hinv & Hpre)".
      (* When the adversary traps back into the handler, we are back at the
         start of this lemma (with possibly different CSR values). *)
      iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                 ptsto_instrs_handler2 ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) -∗
                 LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I with "[]" as "#Hk".
      { iIntros "!>" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap Hnp Hpow".
        iDestruct (ptsto_instrs_handler2_equiv with "Hhandler") as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
        assert (HU : User ≠ Machine) by auto.
        iPoseProof (LoopVerificationBinary.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                      Hpriv HU eq_refl with "Htrap") as "Htrap".
        unfold LoopVerificationBinary.M_Trap, LoopVerificationBinary.transition; cbn.
        iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie' Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp' _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
        iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
        iApply ("IH" $! _ _
                  (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie' with "[//]").
        cbn - [interp_ptstomem].
        iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata Hnp Hpow Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
        auto. }
      iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_handler_entry_pre _) _ _
                (λ a na, asn.interpret femtokernel_handler_entry_post _)
               with "Hpow Hpro Hpre []").
      - iIntros "Hpre".
        iPoseProof (femtokernel_handler_entry_pre_binary_split with "Hpre")
          as "(Hpre1 & Hpre2)".
        iPoseProof (contract_femtohandler_entry_verified__l x5_val x10_val (bv.of_N handler_entry_addr) archstate vmie with "Hpre1") as "H1".
        iPoseProof (contract_femtohandler_entry_verified__r x5_val x10_val (bv.of_N handler_entry_addr) archstate vmie with "Hpre2") as "H2".
        iApply (step_n_focus with "H1 H2").
        iIntros (na1 na2) "(H1 & H2)".
        iApply (femtokernel_handler_entry_post_binary_combine with "H1 H2").
      - iIntros (an) "(Hpost & Hepi & Hpow)".
        iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
        iDestruct "Hpost" as "((Hcurpriv & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hsepc & Hscause & Hsscratch & Hstvec & Hmideleg & Hmedeleg & Hpmp) & Hmstatus & Han & Hx5 & Hx10)"; cbn - [interp_ptstomem].
        iDestruct "Hx1" as "[% Hx1]".
        case_match; cbn - [interp_ptstomem];
          iDestruct "Han" as "[-> _]".
        + (* Dispatch on the secret. *)
          iAssert (interp_gprs {[ x1; x5 ]}) with "[Hgprs Hx10]" as "Hgprs".
          { iApply (interp_gprs_with_excluded_gen {[x1; x5]} (exclude2 := {[x10]}));
              try solve_subseteq.
            iFrame "Hgprs".
            reduce_big_sepS_big_sepL.
            now iFrame "Hx10". }
          iAssert (interp_gprs {[ x1 ]}) with "[Hgprs Hx5]" as "Hgprs".
          { iApply (interp_gprs_with_excluded_gen {[x1]} (exclude2 := {[x5]}));
              try solve_subseteq.
            iFrame "Hgprs".
            reduce_big_sepS_big_sepL.
            now iFrame "Hx5". }
          iDestruct "Hdata" as "(%secret1 & %secret2 & Hdata)".
          iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                     ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) -∗
                     ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) -∗
                     ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) -∗
                     interp_ptstomem2 (bv.of_N data_addr) (secret1 : Val ty_xlenbits) secret2 -∗
                     ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                     LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
            with "[Hinstrs Hhcheck Hhshutdown Hhsecret]" as "Hkdispatch".
          { iIntros "!>" (priv ms ss pc Hpriv) "Hhdispatch Hhnotzero Hhiszero Hdata Hhexit Htrap Hnp Hpow".
            iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap Hnp Hpow").
            iSplitR "Hdata"; last by iExists _, _.
            iApply ptsto_instrs_handler2_equiv.
            iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit". }
          iApply (femtokernel_handler_dispatch_safe_rel _ _ _ _ _ Hmpp); cbn - [interp_ptstomem].
          iFrame "Hhdispatch Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hhnotzero Hhiszero Hhexit Hx1 Hdata Hnp Hpow Hkdispatch";
            repeat iSplitR; auto.
        + (* Check for a shutdown request. *)
          iDestruct "Hdata" as "(%secret1 & %secret2 & Hdata)".
          iAssert (▷ (∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
                     ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) -∗
                     ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) -∗
                     ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) -∗
                     interp_ptstomem2 (bv.of_N data_addr) (secret1 : Val ty_xlenbits) secret2 -∗
                     ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit) -∗
                     LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2))%I
            with "[Hinstrs Hhdispatch Hhnotzero Hhiszero]" as "Hkcheck".
          { iIntros "!>" (priv ms ss pc Hpriv) "Hhcheck Hhshutdown Hhsecret Hdata Hhexit Htrap Hnp Hpow".
            iApply ("Hk" with "[//] [Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit Hdata] Htrap Hnp Hpow").
            iSplitR "Hdata"; last by iExists _, _.
            iApply ptsto_instrs_handler2_equiv.
            iFrame "Hinstrs Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit". }
          iApply (femtokernel_handler_shutdown_check_safe_rel _ _ _ _ _ _ _ Hmpp with "Hinv"); cbn - [interp_ptstomem].
          iFrame "Hhcheck Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx1 Hx5 Hx10 Hdata Hnp Hpow Hhshutdown Hhsecret Hhexit Hkcheck";
            repeat iSplitR; auto.
    Qed.

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
      apply list_elem_of_lookup_2, adv_is_live in Hsom.
      repeat case_decide; auto.
      iPureIntro. eapply mmio_ram_False; eauto.
    Qed.

    Lemma femtokernel_handler_safe_rel `{sailGS2 Σ} :
      ⊢ femto_inv_mmio -∗
        ∀ priv ms ss pc, ⌜priv ≠ Machine⌝ -∗
          ptsto_instrs_handler2 ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) -∗
          LoopVerificationBinary.M_Trap (femto_archstate priv ms ss pc) -∗ nothingPending2 -∗ powered2 true -∗ WP2_loop nothingPending2.
    Proof.
      iIntros "#Hinv" (priv ms ss pc Hpriv) "(Hhandler & Hdata) Htrap Hnp Hpow".
      iDestruct (ptsto_instrs_handler2_equiv with "Hhandler") as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      (* Traps from S-mode look the same as traps from U-mode *)
      assert (HU : User ≠ Machine) by auto.
      iPoseProof (LoopVerificationBinary.M_Trap_SU_irrelevant (femto_archstate priv ms ss pc) (femto_archstate User ms ss pc)
                    Hpriv HU eq_refl with "Htrap") as "Htrap".
      unfold LoopVerificationBinary.M_Trap, LoopVerificationBinary.transition; cbn.
      iDestruct "Htrap" as "(HaccU & Hgprs & Hpmp & [%vmie Hmie] & Hmip & Hcurpriv & Hpc & Hnpc & Hmtvec & [%vstvec Hstvec] & [%vspp [%vmpie [%vspie [%vsie [%vmpp (Hmstatus & [%Hmpp _])]]]]] & [%vmepc Hmepc] & [%vsepc Hsepc] & Hmideleg & Hmedeleg & [%vmscratch Hmscratch] & [%vmcause Hmcause] & [%vsscratch Hsscratch] & [%vscause Hscause])".
      iPoseProof (interp_gprs_with_excluded (exclude := {[x1;x5;x10]}) with "Hgprs") as "(Hregs & Hgprs)";
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      iDestruct "Hregs" as "([% Hx5] & Hx1 & [% Hx10] & _)".
      iApply (femtokernel_handler_entry_safe_rel _ _
                (femto_handler_archstate vmpp vmpie vmcause vmscratch vmepc (ArchState.mkSState vstvec (MkSstatus vspp vspie vsie) vscause vsscratch vsepc)) vmie Hmpp).
      cbn - [interp_ptstomem].
      iFrame "Hhentry Hpc Hnpc Hmscratch HaccU Hcurpriv Hmtvec Hmcause Hmip Hmie Hmepc Hsepc Hscause Hsscratch Hstvec Hmideleg Hmedeleg Hpmp Hinv Hmstatus Hgprs Hx5 Hx10 Hx1 Hdata Hnp Hpow Hhdispatch Hhnotzero Hhiszero Hhcheck Hhshutdown Hhsecret Hhexit".
      auto.
    Qed.

    Lemma femtokernel_manualStep2_rel `{sailGS2 Σ} :
      ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; SPP := User; MPIE := mpie; SPIE := false; MIE := mie; SIE := false |}) ∗
        (mtvec ↦ᵣ (bv.of_N handler_entry_addr)) ∗
        (∃ v, mcause ↦ᵣ v) ∗
        (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        (∃ v, mepc ↦ᵣ v) ∗
        (∃ v, scause ↦ᵣ v) ∗
        (∃ v, sscratch ↦ᵣ v) ∗
        (∃ v, sepc ↦ᵣ v) ∗
        (∃ v, stvec ↦ᵣ v) ∗
        mideleg ↦ᵣ Minterrupts_zero ∗
        medeleg ↦ᵣ Medeleg_zero ∗
        cur_privilege ↦ᵣ User ∗
        interp_gprs ∅ ∗
        interp_pmp_entries femto_pmpentries ∗
        femto_inv_mmio ∗
        (pc ↦ᵣ (bv.of_N adv_addr)) ∗
        (∃ v, nextpc ↦ᵣ v) ∗
        ptsto_instrs_handler2 ∗
        (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2) ∗
        ptstoSthL advAddrs ∗
        nothingPending2 ∗
        powered2 true
        ={⊤}=∗
        ∃ mpp mcause mscratch mepc scause sscratch sepc stvec mpie mie, LoopVerificationBinary.loop_pre nothingPending2
               (femto_adv_archstate mpp mpie mie mcause mscratch mepc stvec scause sscratch sepc).
    Proof.
      iIntros "((%mpp & %mpie & %mie & Hmst) & Hmtvec & [%vmcause Hmcause] & Hmip & Hmie & [%vmscratch Hmscratch] & [%vmepc Hmepc] & [%vscause Hscause] & [%vsscratch Hsscratch] & [%vsepc Hsepc] & [%vstvec Hstvec] & Hmideleg & Hmedeleg & Hcurpriv & Hgprs & Hpmpcfg & #Hmmio & Hpc & Hnpc & Hhandler & Hdata & Hmemadv & Hnp & Hpow)".
      cbn - [ptstoSthL interp_ptstomem LoopVerificationBinary.loop_pre femto_archstate ptsto_instrs_handler2].
      iExists mpp, vmcause, vmscratch, vmepc, vscause, vsscratch, vsepc, vstvec, mpie, mie.
      iModIntro.
      unfold LoopVerificationBinary.loop_pre.
      iSplitR "Hhandler Hdata Hnp Hpow".
      - unfold LoopVerificationBinary.Step_pre.
        cbn - [ptstoSthL interp_ptstomem].
        iFrame "Hgprs Hpmpcfg Hmie Hmip Hcurpriv Hpc Hnpc Hmtvec Hstvec Hmst Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hsscratch Hmcause Hscause".
        iSplitR; first auto.
        by iApply memAdv_pmpPolicy_binary.
      - iFrame "Hnp Hpow".
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.M_CSRMod_machine with "H'") as %Heq.
          cbn in Heq; discriminate Heq. }
        iSplitL "Hhandler Hdata".
        { iIntros "!> (H' & Hnp & Hpow)".
          iApply (femtokernel_handler_safe_rel with "Hmmio [] [$Hhandler $Hdata] H' Hnp Hpow").
          iPureIntro; discriminate. }
        iSplitR.
        { iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.MRET_machine with "H'") as %Heq.
          cbn in Heq; discriminate Heq. }
        iIntros "!> [H' _]". iDestruct (LoopVerificationBinary.SRET_machine with "H'") as %Heq.
        cbn in Heq; discriminate Heq.
    Qed.

    Lemma femtokernel_init_safe_rel `{sailGS2 Σ} (archstate : ArchState) (vmie : Val ty_Minterrupts) :
      ⊢ exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
        ∗ ptsto_instrs_handler2
        ∗ ptstoSthL advAddrs
        ∗ asn.interpret femtokernel_init_pre (csrs_valuation archstate vmie).["a" ∷ ty_xlenbits ↦ bv.of_N init_addr]
        ∗ interp_gprs {[x1]}
        ∗ (∃ (v1 v2 : Val ty_xlenbits), interp_ptstomem2 (bv.of_N data_addr) v1 v2)
        ∗ (∃ v, mscratch ↦ᵣ v)
        ∗ (∃ v : Val ty_scause, scause ↦ᵣ v)
        ∗ (∃ v : Val ty_xlenbits, sscratch ↦ᵣ v)
        ∗ (∃ v : Val ty_xlenbits, sepc ↦ᵣ v)
        ∗ (∃ v : Val ty_xlenbits, stvec ↦ᵣ v)
        ∗ femto_inv_mmio
        ∗ nothingPending2
        ∗ powered2 true
          -∗
          WP2_loop nothingPending2.
    Proof.
      iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hdata & Hmscratch & Hscause & Hsscratch & Hsepc & Hstvec & #Hmem & Hnp & Hpow)".
      iApply (WP2_loop_semTripleBlock (λ a, asn.interpret femtokernel_init_pre _) _ _
                                      (λ a na, asn.interpret femtokernel_init_post (csrs_valuation archstate vmie).["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na])
               with "Hpow Hpro Hpre []").
      iIntros "Hpre".
      iPoseProof (femtokernel_init_pre_binary_split archstate vmie with "Hpre") as "(Hpre1 & Hpre2)".
      iPoseProof (contract_femtoinit_verified__l (bv.of_N init_addr) archstate vmie with "Hpre1") as "H1".
      iPoseProof (contract_femtoinit_verified__r (bv.of_N init_addr) archstate vmie with "Hpre2") as "H2".
      iApply (step_n_focus with "H1 H2").
      iIntros (na1 na2) "(H1 & H2)".
      now iPoseProof (femtokernel_init_post_binary_combine with "H1 H2") as "(<- & $)".
      iIntros (an) "(Hpost & Hepi & Hpow)".
      cbn - [asn_regs_ptsto interp_pmp_entries].
      iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hmideleg & Hmedeleg & Hcurpriv & Hx1 & Hpmpentries)".
      iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
          try solve_subseteq.
        reduce_big_sepS_big_sepL.
        now iFrame "Hx1 Hgprs". }
      iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
      rewrite ?bv.add_zero_l.
      iApply (fupd_semWP2 ⊤).
      iMod (femtokernel_manualStep2_rel with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hmepc $Hscause $Hsscratch $Hsepc $Hstvec $Hmideleg $Hmedeleg $Hcurpriv $Hgprs $Hpmpentries $Hmem $Hpc $Hnpc $Hhandler $Hdata $Hadv $Hnp $Hpow]") as "(%mpp & %mcause & %mscratch & %mepc & %scause & %sscratch & %sepc & %stvec & %mpie & %mie & Hlooppre)".
      iModIntro.
      iApply (LoopVerificationBinary.valid_semTriple_loop with "Hlooppre").
    Qed.

    Lemma intro_ptstoSthL_binary `{sailGS2 Σ} (μ : Memory) (addrs : list Xlenbits)  :
      ([∗ list] a' ∈ addrs, @RVPCOM.interp_ptsto _ memGS_left a' ((memory_ram μ) a'))
      ∗ ([∗ list] a' ∈ addrs, @RVPCOM.interp_ptsto _ memGS_right a' ((memory_ram μ) a'))
      ⊢ ptstoSthL addrs.
    Proof.
      induction addrs as [|a l]; cbn; auto.
      iIntros "[[Hmemal Hmeml] [Hmemar Hmemr]]".
      iSplitL "Hmemal Hmemar".
      - iExists ((memory_ram μ) a). iFrame "Hmemal Hmemar".
      - iApply IHl. iFrame "Hmeml Hmemr".
    Qed.

    Definition obs_equiv (t1 t2 : Trace) : Prop :=
      filter_adv_observable t1 = filter_adv_observable t2.

    Lemma femtokernel_splitMemory_rel `{sailGS2 Σ} {μ1 μ2 : Memory} (secret1 secret2 : Val ty_xlenbits) :
      mem_has_femtokernel μ1 secret1 ->
      mem_has_femtokernel μ2 secret2 ->
      mmio_pred bytes_per_word (memory_trace μ1) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      mmio_pred bytes_per_word (memory_trace μ2) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      obs_equiv (memory_trace μ1) (memory_trace μ2) -> (* Both executions start with the same adversary-observable history *)
      fun_powered_on μ1 = true -> fun_powered_on μ2 = true -> (* Both machines start powered on *)
      List.Forall (λ a, memory_ram μ1 a = memory_ram μ2 a) advAddrs -> (* We require that the memory the adversary can access is indistinguishable in the left and right memory *)
      RVPADEQ2.mem_res2 μ1 μ2 ⊢ |={⊤}=>
        ptsto_instrs (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∗
        ptsto_instrs_handler2 ∗
        interp_ptstomem2 (bv.of_N data_addr) secret1 secret2 ∗
        femto_inv_mmio ∗
        nothingPending2 ∗
        powered2 true ∗
        ptstoSthL advAddrs.
    Proof.
      iIntros (Hfk1 Hfk2 Hpred1 Hpred2 Hobs Hon1 Hon2 Hadv) "Hmem".
      iDestruct "Hmem" as "((Hmem1 & Htr1 & Hauth1 & Hnp1 & Hpw1) & (Hmem2 & Htr2 & Hauth2 & Hnp2 & Hpw2))".
      iDestruct (femtokernel_splitMemory (mG := memGS_left) Hfk1 with "Hmem1")
        as "(Hinit1 & Hhandler1 & Hdata1 & Hadv1)".
      iDestruct (femtokernel_splitMemory (mG := memGS_right) Hfk2 with "Hmem2")
        as "(Hinit2 & Hhandler2 & Hdata2 & Hadv2)".
      (* Both executions start in sync, with the same observable history. *)
      iMod (inv.inv_alloc RVPCOM.femto_inv_mmio_ns ⊤
              (∃ t, side_inv bytes_per_word mc_ghGS2_left t ∗ side_inv bytes_per_word mc_ghGS2_right t)
             with "[Htr1 Htr2 Hauth1 Hauth2]") as "#Hinv".
      { iNext. iExists (filter_adv_observable (memory_trace μ1)).
        iSplitL "Htr1 Hauth1".
        - iExists _. iFrame "Htr1". iSplitR; first done. iLeft. by iFrame "Hauth1".
        - iExists _. iFrame "Htr2". iSplitR; first done. iLeft. iFrame "Hauth2". rewrite /obs_equiv in Hobs. by rewrite Hobs. }
      iModIntro.
      rewrite ptsto_instrs_equiv.
      unfold ptsto_instrs_handler2, interp_ptstomem2, nothingPending2, femto_inv_mmio, interp_inv_mmio.
      iEval (rewrite Hon1) in "Hpw1". iEval (rewrite Hon2) in "Hpw2".
      iFrame "Hinit1 Hinit2 Hhandler1 Hhandler2 Hdata1 Hdata2 Hnp1 Hnp2 Hpw1 Hpw2 Hinv".
      iApply (intro_ptstoSthL_binary μ1 with "[$Hadv1 Hadv2]").
      iApply (big_sepL_impl with "Hadv2").
      iIntros "!>" (k a HIn) "H".
      pose proof (Forall_lookup_1 _ _ _ _ Hadv HIn) as Heq.
      cbn in Heq. by rewrite Heq.
    Qed.

    Import RiscvPmpSemantics.SmallStepNotations.

    Lemma femtokernel_rel_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ1' μ2 : Memory}
      {δ1 δ1' δ2 : CStore [ctx]} {s1' : Stm [ctx] ty.unit} {v1 : IVal ty.unit} {secret1 secret2 : Val ty_xlenbits} :
      mem_has_femtokernel μ1 secret1 ->
      mem_has_femtokernel μ2 secret2 ->
      Forall (λ a : Addr, memory_ram μ1 a = memory_ram μ2 a) advAddrs -> (* We assume that the memory the adv has access to, before executing the kernel, contains the same values *)
      mmio_pred bytes_per_word (memory_trace μ1) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      mmio_pred bytes_per_word (memory_trace μ2) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
      obs_equiv (memory_trace μ1) (memory_trace μ2) -> (* Both executions start with the same adversary-observable history *)
      fun_powered_on μ1 = true -> fun_powered_on μ2 = true -> (* Both machines start powered on *)
      (∀ {σ : Ty} (r : Reg σ), read_register γ1 r = read_register γ2 r) -> (* We require that the initial values of all registers are the same, as we consider these to be public. The secrets in our verification are part of MMIO. *)
      femto_init_regs γ1 ->
      (* For every terminating execution of the left machine, the right machine
         also terminates, with the same result (a value or a failure). *)
      ⟨ γ1, μ1, δ1, fun_loop ⟩ --->* ⟨ γ1', μ1', δ1', s1' ⟩ ->
      stm_to_val s1' = Some v1 ->
      ∃ γ2' μ2' δ2' s2',
        ⟨ γ2, μ2, δ2, fun_loop ⟩ --->* ⟨ γ2', μ2', δ2', s2' ⟩
        ∧ stm_to_val s2' = Some v1
        (* Confidentiality: adversary cannot distinguish both executions *)
        ∧ obs_equiv (memory_trace μ1') (memory_trace μ2')
        (* Integrity: both executions only performed allowed MMIO events *)
        ∧ mmio_pred bytes_per_word (memory_trace μ1')
        ∧ mmio_pred bytes_per_word (memory_trace μ2').
    Proof.
      intros μfk1 μfk2 μadv μft1 μft2 μobs μon1 μon2 γeq
        (γmstatus & γcurpriv & γpmp0cfg & γpmpaddr0 & γpmp1cfg & γpmpaddr1 & γpc & γmideleg & γmedeleg) steps1 Hval1.
      eapply (wp2_strong_adequacy fun_loop γ2 μ2 δ2 steps1 Hval1
                (Q := fun _ _ v1 δ1' v2 δ2' => ⌜v1 = v2⌝ ∗ ⌜δ1' = δ2'⌝ ∗ femto_inv_mmio ∗ nothingPending2)%I).
      iIntros (Σ sg).
      iSplitL.
      - iIntros "(Hmem & Hregs)".
        iMod (femtokernel_splitMemory_rel μfk1 μfk2 μft1 μft2 μobs μon1 μon2 μadv with "Hmem")
          as "(Hinit & Hhandler & Hdata & #Hmmio & Hnp & Hpow & Hadv)".
        destruct (env.view δ1), (env.view δ2).
        iPoseProof (femtokernel_init_safe_rel (femto_init_archstate γ1)
                     (read_register γ1 mie)
                     with "[-]") as "H".
        { #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
          iFrame "∗ #". cbn - [interp_gprs].
          rewrite <- ?γeq.
          rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc γmideleg γmedeleg.
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
        iModIntro.
        iApply (semWP2_mono with "H").
        iIntros (? ? ? ?) "($ & $ & $)". iFrame "Hmmio".
      - iIntros (γ2' μ2' δ2' s2' v2 steps2 Hval) "(%Hv & _ & #Hmmio & [Hnpl Hnpr]) Hmem".
        iDestruct "Hmem" as "[(%memmap1 & Hinv1 & %link1 & Htr1 & _)
                              (%memmap2 & Hinv2 & %link2 & Htr2 & _)]".
        iInv "Hmmio" as ">(%t & (%t1 & Hf1 & %Hpred1 & H1) & (%t2 & Hf2 & %Hpred2 & H2))" "_".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hf1") as %<-.
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hf2") as %<-.
        iAssert (⌜filter_adv_observable (memory_trace μ1') = t⌝)%I with "[H1 Hnpl]" as %Hobs1.
        { iDestruct "H1" as "[[%Heq _] | (%e & _ & Hauth)]"; first done.
          iDestruct (RVPCOM.written_auth_nothingPending with "Hauth Hnpl") as "[]". }
        iAssert (⌜filter_adv_observable (memory_trace μ2') = t⌝)%I with "[H2 Hnpr]" as %Hobs2.
        { iDestruct "H2" as "[[%Heq _] | (%e & _ & Hauth)]"; first done.
          iDestruct (RVPCOM.written_auth_nothingPending with "Hauth Hnpr") as "[]". }
        iApply fupd_mask_intro; first set_solver. iIntros "_".
        iPureIntro. exists γ2', μ2', δ2', s2'.
        split; first done. split; first by rewrite Hval Hv.
        split; first by rewrite /obs_equiv Hobs1 Hobs2.
        done.
    Qed.

  End RelationalVerification.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
