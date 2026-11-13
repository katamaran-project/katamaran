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
     SmallStep.Step
     RiscvPmp.GVT.PmpCheck
     RiscvPmp.GVT.Spec
     RiscvPmp.GVT.TotalVerifier
     RiscvPmp.GVT.IrisModel
     RiscvPmp.GVT.IrisInstance
     RiscvPmp.GVT.Machine
     RiscvPmp.GVT.Logic
     RiscvPmp.GVT.trace
     RiscvPmp.iostate
     RiscvPmp.GVT.Sig
     RiscvPmp.GVT.Target
     RiscvPmp.GVT.StopButtonSMode.Layout.
From Katamaran Require
     RiscvPmp.GVT.Contracts
     RiscvPmp.GVT.LoopVerification
     RiscvPmp.GVT.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram
.

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

  Import RiscvPmp.GVT.Contracts.
  Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
  Import RiscvPmpIrisInstancePredicates.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpShallowExec.

  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Import TermNotations.

    Open Scope hex_Z_scope.

    (* FIXED ADDRESSES *)
    (* All addresses come from the target (Target.v) and the kernel's layout
       on it (Layout.v); nothing below uses a literal address. *)

    (* The first address that is no longer used by the adversary. *)
    Definition adv_addr_end : N := maxAddr.
    (* The LED word, where the kernel's observable writes go, and proof that
       those writes are within the MMIO region. *)
    Definition mmio_dev_addr : N := Layout.led_sim.
    Definition mmio_read_addr : N := mmioProtoStartAddr + 4.

    (* Registers of the button's virtio-mmio device *)
    Definition virtio (off : N) : N := Target.virtio_base + off.

    Lemma write_word_is_MMIO: withinMMIO (bv.of_N mmio_dev_addr) bytes_per_word.
    Proof. apply bounds_withinMMIO; now compute. Qed.

    Lemma write_interrupt_is_MMIO: withinMMIO (bv.of_N mmio_read_addr) bytes_per_word.
    Proof. apply bounds_withinMMIO; now compute. Qed.

    (* Aliases for registers *)
    Definition zero : RegIdx := [bv 0].
    Definition ra   : RegIdx := [bv 1].
    Definition sp   : RegIdx := [bv 2].
    Definition t0   : RegIdx := [bv 5].
    Definition t1   : RegIdx := [bv 6].
    Definition t2   : RegIdx := [bv 7].
    Definition a0   : RegIdx := [bv 10].
    Definition a1   : RegIdx := [bv 11].
    Definition a6   : RegIdx := [bv 16].
    Definition a7   : RegIdx := [bv 17].
    Definition t3   : RegIdx := [bv 28].
    Definition t4   : RegIdx := [bv 29].
    Definition t5   : RegIdx := [bv 30].
    Definition t6   : RegIdx := [bv 31].


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

    (* adv_addr_end (= maxAddr) no longer fits in a 12-bit immediate. *)
    Definition adv_addr_end_1 : Val (ty.bvec 12) := fst (imm_split_bv (bv.of_N adv_addr_end)).
    Definition adv_addr_end_2 : Val (ty.bvec 20) := snd (imm_split_bv (bv.of_N adv_addr_end)).

    (* Absolute addresses: `lui rd, %hi(v); addi rd, rd, %lo(v)` *)
    Definition hi20 (v : N) : bv 20 := snd (imm_split_bv (bv.of_N v)).
    Definition lo12 (v : N) : bv 12 := fst (imm_split_bv (bv.of_N v)).

    (* PC-relative offsets, computed in Z so that backward targets (loops,
       calls to earlier code) do not truncate to 0 as `bv.of_N (a - b)` does. *)
    Definition rel {n} (target cur : N) : bv n := bv.of_Z (Z.of_N target - Z.of_N cur).
    (* `la rd, sym` = `auipc rd, %pcrel_hi(sym); addi rd, rd, %pcrel_lo(sym)`,
       both relative to the address of the auipc. *)
    Definition pcrel_hi (target auipc_pc : N) : bv 20 := snd (imm_split_bv (rel target auipc_pc)).
    Definition pcrel_lo (target auipc_pc : N) : bv 12 := fst (imm_split_bv (rel target auipc_pc)).

    (* Pseudo-instructions *)
    Local Abbreviation LI rd imm   := (ITYPE imm zero rd RISCV_ADDI).
    Local Abbreviation MV rd rs    := (ITYPE bv.zero rs rd RISCV_ADDI).
    Local Abbreviation CSRW csr rs := (CSR csr rs zero false CSRRW).
    Local Abbreviation CSRR rd csr := (CSR csr zero rd false CSRRS).
    Local Abbreviation CSRS csr rs := (CSR csr rs zero false CSRRS).
    Local Abbreviation CSRC csr rs := (CSR csr rs zero false CSRRC).
    Local Abbreviation RET         := (RISCV_JALR bv.zero ra zero).
    (* Placeholder for instructions the model does not support yet ([MODEL]):
       keeps the layout identical to the binary. *)
    Local Abbreviation NOP         := (ITYPE bv.zero zero zero RISCV_ADDI).

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


        (* ====================================================================== *)
    (*  .text                                                                  *)
    (* ====================================================================== *)

    (* 0x000 : reset vector *)
    Example femtokernel_entry_asm (init_start : N) : list ASM :=
      [
        Λ x, RISCV_JAL (rel init_start x) zero                    (* j femto_init *)
      ].
    Example femtokernel_entry' (start init_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_entry_asm init_start) start.

    (* 0x004 .. 0x108 : virtio_btn_init, straight-line, ends in ret *)
    Example femtokernel_virtio_init_asm (virtq_mem rx_buf rx_used_seen : N) : list ASM :=
      [
        (* reset; ACKNOWLEDGE; ACKNOWLEDGE | DRIVER *)
          UTYPE (hi20 (virtio 0x070)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x070)) t0 t0 RISCV_ADDI            (* VIRTIO_STATUS *)
        ; STORE bv.zero zero t0 WORD
        ; LI t1 bv.one
        ; STORE bv.zero t1 t0 WORD
        ; LI t1 [bv 0x003]
        ; STORE bv.zero t1 t0 WORD

        (* no features *)
        ; UTYPE (hi20 (virtio 0x024)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x024)) t0 t0 RISCV_ADDI            (* VIRTIO_DRIVER_FEAT_SEL *)
        ; STORE bv.zero zero t0 WORD
        ; UTYPE (hi20 (virtio 0x020)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x020)) t0 t0 RISCV_ADDI            (* VIRTIO_DRIVER_FEATURES *)
        ; STORE bv.zero zero t0 WORD

        (* legacy queue setup: page size, queue 0, 1 entry, align 4096, PFN *)
        ; UTYPE (hi20 (virtio 0x028)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x028)) t0 t0 RISCV_ADDI            (* VIRTIO_GUEST_PAGE_SIZE *)
        ; UTYPE [bv 0x00001] t1 RISCV_LUI                         (* t1 <- 4096 *)
        ; STORE bv.zero t1 t0 WORD
        ; UTYPE (hi20 (virtio 0x030)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x030)) t0 t0 RISCV_ADDI            (* VIRTIO_QUEUE_SEL *)
        ; STORE bv.zero zero t0 WORD
        ; UTYPE (hi20 (virtio 0x038)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x038)) t0 t0 RISCV_ADDI            (* VIRTIO_QUEUE_NUM *)
        ; LI t1 bv.one
        ; STORE bv.zero t1 t0 WORD
        ; UTYPE (hi20 (virtio 0x03c)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x03c)) t0 t0 RISCV_ADDI            (* VIRTIO_QUEUE_ALIGN *)
        ; UTYPE [bv 0x00001] t1 RISCV_LUI
        ; STORE bv.zero t1 t0 WORD
        ; Λ x, UTYPE (pcrel_hi virtq_mem x) t1 RISCV_AUIPC        (* la t1, virtq_mem *)
        ; Λ x, ITYPE (pcrel_lo virtq_mem (x - 4)) t1 t1 RISCV_ADDI
        ; SHIFTIOP [bv 0xc] t1 t1 RISCV_SRLI                      (* t1 <- virtq_mem >> 12 *)
        ; UTYPE (hi20 (virtio 0x040)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x040)) t0 t0 RISCV_ADDI            (* VIRTIO_QUEUE_PFN *)
        ; STORE bv.zero t1 t0 WORD

        (* descriptor 0 := { addr = rx_buf, len = 4, flags = WRITE, next = 0 } *)
        ; Λ x, UTYPE (pcrel_hi virtq_mem x) t0 RISCV_AUIPC        (* la t0, virtq_mem *)
        ; Λ x, ITYPE (pcrel_lo virtq_mem (x - 4)) t0 t0 RISCV_ADDI
        ; Λ x, UTYPE (pcrel_hi rx_buf x) t1 RISCV_AUIPC           (* la t1, rx_buf *)
        ; Λ x, ITYPE (pcrel_lo rx_buf (x - 4)) t1 t1 RISCV_ADDI
        ; STORE bv.zero t1 t0 WORD                                (* desc.addr lo *)
        ; STORE [bv 0x004] zero t0 WORD                           (* desc.addr hi *)
        ; LI t2 [bv 0x004]
        ; STORE [bv 0x008] t2 t0 WORD                             (* desc.len *)
        ; LI t2 [bv 0x002]
        ; STORE [bv 0x00c] t2 t0 HALF                             (* desc.flags = VIRTQ_DESC_F_WRITE *)
        ; STORE [bv 0x00e] zero t0 HALF                           (* desc.next *)

        (* avail ring := { flags = 0, idx = 1, ring[0] = 0 } *)
        ; STORE [bv 0x010] zero t0 HALF                           (* avail.flags *)
        ; STORE [bv 0x014] zero t0 HALF                           (* avail.ring[0] *)
        ; LI t2 bv.one
        ; STORE [bv 0x012] t2 t0 HALF                             (* avail.idx *)
        ; NOP                                                     (* [MODEL] fence iorw, iorw *)

        (* rx_used_seen <- used.idx *)
        ; Λ x, UTYPE (pcrel_hi virtq_mem x) t0 RISCV_AUIPC        (* la t0, virtq_mem *)
        ; Λ x, ITYPE (pcrel_lo virtq_mem (x - 4)) t0 t0 RISCV_ADDI
        ; UTYPE [bv 0x00001] t1 RISCV_LUI
        ; RTYPE t1 t0 t0 RISCV_ADD                                (* t0 <- used ring (virtq_mem + 4096) *)
        ; LOAD [bv 0x002] t0 t3 true HALF                         (* t3 <- used.idx *)
        ; Λ x, UTYPE (pcrel_hi rx_used_seen x) t4 RISCV_AUIPC     (* la t4, rx_used_seen *)
        ; Λ x, ITYPE (pcrel_lo rx_used_seen (x - 4)) t4 t4 RISCV_ADDI
        ; STORE bv.zero t3 t4 WORD

        (* DRIVER_OK, kick queue 0 *)
        ; UTYPE (hi20 (virtio 0x070)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x070)) t0 t0 RISCV_ADDI            (* VIRTIO_STATUS *)
        ; LI t1 [bv 0x007]                                        (* ACK | DRIVER | DRIVER_OK *)
        ; STORE bv.zero t1 t0 WORD
        ; UTYPE (hi20 (virtio 0x050)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x050)) t0 t0 RISCV_ADDI            (* VIRTIO_QUEUE_NOTIFY *)
        ; STORE bv.zero zero t0 WORD
        ; RET
      ].
    Example femtokernel_virtio_init' (start virtq_mem rx_buf rx_used_seen : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_virtio_init_asm virtq_mem rx_buf rx_used_seen) start.

    (* ---------------------------------------------------------------------- *)
    (* virtio_btn_irq_handler: returns in t1 the OR of all decoded events      *)
    (* (bit 3 = reset, bit 4 = stop).                                          *)
    (* ---------------------------------------------------------------------- *)

    (* 0x10c .. 0x14c : ack, load used.idx and rx_used_seen; falls through *)
    Example femtokernel_virtio_irq_asm_block0 (virtq_mem rx_used_seen : N) : list ASM :=
      [
          ITYPE [bv 0xffc] sp sp RISCV_ADDI                       (* sp <- sp - 4 *)
        ; STORE bv.zero ra sp WORD                                (* push ra *)
        ; UTYPE (hi20 (virtio 0x060)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x060)) t0 t0 RISCV_ADDI            (* BUTTON_INTERRUPT (InterruptStatus) *)
        ; LOAD bv.zero t0 t1 false WORD
        ; UTYPE (hi20 (virtio 0x064)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x064)) t0 t0 RISCV_ADDI            (* VIRTIO_INT_ACK *)
        ; STORE bv.zero t1 t0 WORD
        ; Λ x, UTYPE (pcrel_hi virtq_mem x) t0 RISCV_AUIPC        (* la t0, virtq_mem *)
        ; Λ x, ITYPE (pcrel_lo virtq_mem (x - 4)) t0 t0 RISCV_ADDI
        ; UTYPE [bv 0x00001] t1 RISCV_LUI
        ; RTYPE t1 t0 t0 RISCV_ADD                                (* t0 <- used ring *)
        ; LOAD [bv 0x002] t0 t4 true HALF                         (* t4 <- used.idx *)
        ; Λ x, UTYPE (pcrel_hi rx_used_seen x) t2 RISCV_AUIPC     (* la t2, rx_used_seen *)
        ; Λ x, ITYPE (pcrel_lo rx_used_seen (x - 4)) t2 t2 RISCV_ADDI
        ; LOAD bv.zero t2 t3 false WORD                           (* t3 <- rx_used_seen *)
        ; LI t6 bv.zero                                           (* t6 <- 0 (accumulated events) *)
      ].
    Example femtokernel_virtio_irq_block0' (start virtq_mem rx_used_seen : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_virtio_irq_asm_block0 virtq_mem rx_used_seen) start.

    (* 0x150 : loop head *)
    Example femtokernel_virtio_irq_asm_loop_head (loop_exit : N) : list ASM :=
      [
        Λ x, BTYPE (rel loop_exit x) t4 t3 RISCV_BEQ              (* beq t3, t4, exit *)
      ].
    Example femtokernel_virtio_irq_loop_head' (start loop_exit : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_virtio_irq_asm_loop_head loop_exit) start.

    (* 0x154 .. 0x160 : read the event byte, call the decoder *)
    Example femtokernel_virtio_irq_asm_loop_body (rx_buf handle_byte_start : N) : list ASM :=
      [
          Λ x, UTYPE (pcrel_hi rx_buf x) t5 RISCV_AUIPC           (* la t5, rx_buf *)
        ; Λ x, ITYPE (pcrel_lo rx_buf (x - 4)) t5 t5 RISCV_ADDI
        ; LOAD bv.zero t5 a0 true BYTE                            (* a0 <- event byte *)
        ; Λ x, RISCV_JAL (rel handle_byte_start x) ra             (* call virtio_btn_handle_byte *)
      ].
    Example femtokernel_virtio_irq_loop_body' (start rx_buf handle_byte_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_virtio_irq_asm_loop_body rx_buf handle_byte_start) start.

    (* 0x164 .. 0x16c : accumulate and loop *)
    Example femtokernel_virtio_irq_asm_loop_tail (loop_head : N) : list ASM :=
      [
          RTYPE t1 t6 t6 RISCV_OR                                 (* t6 <- t6 | t1 *)
        ; ITYPE bv.one t3 t3 RISCV_ADDI                           (* t3++ *)
        ; Λ x, RISCV_JAL (rel loop_head x) zero                   (* j loop_head *)
      ].
    Example femtokernel_virtio_irq_loop_tail' (start loop_head : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_virtio_irq_asm_loop_tail loop_head) start.

    (* 0x170 .. 0x1ac : store rx_used_seen, re-post the buffer, return *)
    Example femtokernel_virtio_irq_asm_exit (virtq_mem rx_used_seen : N) : list ASM :=
      [
          Λ x, UTYPE (pcrel_hi rx_used_seen x) t2 RISCV_AUIPC     (* la t2, rx_used_seen *)
        ; Λ x, ITYPE (pcrel_lo rx_used_seen (x - 4)) t2 t2 RISCV_ADDI
        ; STORE bv.zero t3 t2 WORD                                (* rx_used_seen <- t3 *)
        ; Λ x, UTYPE (pcrel_hi virtq_mem x) t0 RISCV_AUIPC        (* la t0, virtq_mem *)
        ; Λ x, ITYPE (pcrel_lo virtq_mem (x - 4)) t0 t0 RISCV_ADDI
        ; LOAD [bv 0x012] t0 t5 true HALF                         (* t5 <- avail.idx *)
        ; ITYPE bv.one t5 t5 RISCV_ADDI
        ; STORE [bv 0x012] t5 t0 HALF                             (* avail.idx++ *)
        ; NOP                                                     (* [MODEL] fence iorw, iorw *)
        ; UTYPE (hi20 (virtio 0x050)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x050)) t0 t0 RISCV_ADDI            (* VIRTIO_QUEUE_NOTIFY *)
        ; STORE bv.zero zero t0 WORD
        ; MV t1 t6                                                (* return value *)
        ; LOAD bv.zero sp ra false WORD                           (* pop ra *)
        ; ITYPE [bv 0x004] sp sp RISCV_ADDI
        ; RET
      ].
    Example femtokernel_virtio_irq_exit' (start virtq_mem rx_used_seen : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_virtio_irq_asm_exit virtq_mem rx_used_seen) start.

    (* ---------------------------------------------------------------------- *)
    (* virtio_btn_handle_byte: 'r' -> t1 = 8, 's' -> t1 = 16, else t1 = 24     *)
    (* ---------------------------------------------------------------------- *)

    (* 0x1b0 .. 0x1b4 *)
    Example femtokernel_handle_byte_asm_block0 (is_r_start : N) : list ASM :=
      [
          LI t2 [bv 0x072]                                        (* 'r' *)
        ; Λ x, BTYPE (rel is_r_start x) t2 a0 RISCV_BEQ
      ].
    Example femtokernel_handle_byte_block0' (start is_r_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handle_byte_asm_block0 is_r_start) start.

    (* 0x1b8 .. 0x1bc *)
    Example femtokernel_handle_byte_asm_block1 (is_s_start : N) : list ASM :=
      [
          LI t2 [bv 0x073]                                        (* 's' *)
        ; Λ x, BTYPE (rel is_s_start x) t2 a0 RISCV_BEQ
      ].
    Example femtokernel_handle_byte_block1' (start is_s_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handle_byte_asm_block1 is_s_start) start.

    (* 0x1c0 .. 0x1c4 *)
    Example femtokernel_handle_byte_asm_other : list ASM :=
      [
          LI t1 [bv 0x018]                                        (* reset | stop *)
        ; RET
      ].
    Example femtokernel_handle_byte_other' (start : N) : list AnnotInstr :=
      resolve_ASM femtokernel_handle_byte_asm_other start.

    (* 0x1c8 .. 0x1cc : is_r *)
    Example femtokernel_handle_byte_asm_is_r : list ASM :=
      [
          LI t1 [bv 0x008]
        ; RET
      ].
    Example femtokernel_handle_byte_is_r' (start : N) : list AnnotInstr :=
      resolve_ASM femtokernel_handle_byte_asm_is_r start.

    (* 0x1d0 .. 0x1d4 : is_s *)
    Example femtokernel_handle_byte_asm_is_s : list ASM :=
      [
          LI t1 [bv 0x010]
        ; RET
      ].
    Example femtokernel_handle_byte_is_s' (start : N) : list AnnotInstr :=
      resolve_ASM femtokernel_handle_byte_asm_is_s start.

    (* ---------------------------------------------------------------------- *)
    (* femto_init                                                              *)
    (* ---------------------------------------------------------------------- *)

    (* 0x1d8 .. 0x2ac : trap vector, iostate, M-mode stack, PMP; ends in a
       call to virtio_btn_init *)
    Example femtokernel_init_asm_block0
      (handler_start iostate kernel_stack_top virtio_init_start : N) : list ASM :=
      [
          Λ x, UTYPE (pcrel_hi handler_start x) t0 RISCV_AUIPC    (* la t0, femto_handler *)
        ; Λ x, ITYPE (pcrel_lo handler_start (x - 4)) t0 t0 RISCV_ADDI
        ; CSRW MTvec t0

        ; UTYPE (hi20 iostate) t0 RISCV_LUI                       (* li t0, KERNEL_RAM_IOSTATE *)
        ; ITYPE (lo12 iostate) t0 t0 RISCV_ADDI
        ; STORE bv.zero zero t0 WORD                              (* iostate <- 0 (SGo) *)

        ; LI a0 bv.zero                                           (* [MODEL] csrr a0, mhartid: single hart, id 0 *)

        ; Λ x, UTYPE (pcrel_hi kernel_stack_top x) sp RISCV_AUIPC (* la sp, __kernel_stack_top *)
        ; Λ x, ITYPE (pcrel_lo kernel_stack_top (x - 4)) sp sp RISCV_ADDI
        ; CSRW MScratch sp

        (* PMP regions (TOR), deny-list for S-mode: even entries RWX, odd
           entries R-X; see Layout.v for the regions. `li t0, REGIONn` is a
           lone lui where the binary has one, which needs the low 12 bits
           of that region to be zero (checked below the layout). *)
        ; UTYPE (hi20 Layout.region0) t0 RISCV_LUI                (* REGION0_ADDR: CLINT *)
        ; CSRW MPMPADDR0 t0
        ; UTYPE (hi20 Layout.region1) t0 RISCV_LUI                (* REGION1_ADDR: CLINT end *)
        ; CSRW MPMPADDR1 t0
        ; UTYPE (hi20 Layout.region2) t0 RISCV_LUI
        ; ITYPE (lo12 Layout.region2) t0 t0 RISCV_ADDI            (* REGION2_ADDR: PLIC priority[button] *)
        ; CSRW MPMPADDR2 t0
        ; UTYPE (hi20 Layout.region3) t0 RISCV_LUI
        ; ITYPE (lo12 Layout.region3) t0 t0 RISCV_ADDI            (* REGION3_ADDR *)
        ; CSRW MPMPADDR3 t0
        ; UTYPE [bv 0x0d0f1] t0 RISCV_LUI
        ; ITYPE [bv 0xd0f] t0 t0 RISCV_ADDI                       (* PMPCFG0 = 0x0d0f0d0f *)
        ; CSRW MPMP0CFG t0

        ; UTYPE (hi20 Layout.region4) t0 RISCV_LUI
        ; ITYPE (lo12 Layout.region4) t0 t0 RISCV_ADDI            (* REGION4_ADDR: PLIC enable, M context *)
        ; CSRW MPMPADDR4 t0
        ; UTYPE (hi20 Layout.region5) t0 RISCV_LUI
        ; ITYPE (lo12 Layout.region5) t0 t0 RISCV_ADDI            (* REGION5_ADDR: PLIC enable, S context *)
        ; CSRW MPMPADDR5 t0
        ; UTYPE (hi20 Layout.region6) t0 RISCV_LUI                (* REGION6_ADDR: PLIC threshold, M context *)
        ; CSRW MPMPADDR6 t0
        ; UTYPE (hi20 Layout.region7) t0 RISCV_LUI
        ; ITYPE (lo12 Layout.region7) t0 t0 RISCV_ADDI            (* REGION7_ADDR: PLIC threshold, S context *)
        ; CSRW MPMPADDR7 t0
        ; UTYPE [bv 0x0d0f1] t0 RISCV_LUI
        ; ITYPE [bv 0xd0f] t0 t0 RISCV_ADDI                       (* PMPCFG1 = 0x0d0f0d0f *)
        ; CSRW MPMP1CFG t0

        ; UTYPE (hi20 Layout.region8) t0 RISCV_LUI
        ; ITYPE (lo12 Layout.region8) t0 t0 RISCV_ADDI            (* REGION8_ADDR: virtio slots *)
        ; CSRW MPMPADDR8 t0
        ; UTYPE (hi20 Layout.region9) t0 RISCV_LUI                (* REGION9_ADDR: adv_start *)
        ; CSRW MPMPADDR9 t0
        ; UTYPE (hi20 Layout.region10) t0 RISCV_LUI               (* REGION10_ADDR: kernel_ram_start *)
        ; CSRW MPMPADDR10 t0
        ; UTYPE (hi20 Layout.region11) t0 RISCV_LUI               (* REGION11_ADDR: adversary_ram_start *)
        ; CSRW MPMPADDR11 t0
        ; UTYPE [bv 0x0d0f1] t0 RISCV_LUI
        ; ITYPE [bv 0xd0f] t0 t0 RISCV_ADDI                       (* PMPCFG2 = 0x0d0f0d0f *)
        ; CSRW MPMP2CFG t0

        ; UTYPE (hi20 Layout.region12) t0 RISCV_LUI               (* REGION12_ADDR: ram_end *)
        ; CSRW MPMPADDR12 t0
        ; LI t0 [bv 0x00f]                                        (* PMPCFG3 = 0x0000000f *)
        ; CSRW MPMP3CFG t0

        ; Λ x, RISCV_JAL (rel virtio_init_start x) ra             (* call virtio_btn_init *)
      ].
    Example femtokernel_init_block0' (start handler_start iostate kernel_stack_top virtio_init_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_init_asm_block0 handler_start iostate kernel_stack_top virtio_init_start) start.

    (* 0x2b0 .. 0x330 : PLIC, interrupt enables, delegation, drop to S-mode.
       NOTE: `lui t0, %hi(ADV_START)` alone is only correct if adv_start is
       4 KiB aligned (low 12 bits 0); the binary has no addi here. *)
    Example femtokernel_init_asm_block1 (adv_start : N) : list ASM :=
      [
        (* PLIC: enable source 8 (virtio-mmio) for context 0 *)
          UTYPE (hi20 Target.plic_base) t0 RISCV_LUI              (* PLIC_BASE *)
        ; UTYPE (hi20 (Target.plic_enable0 - Target.plic_base)) t1 RISCV_LUI
        ; RTYPE t1 t0 t0 RISCV_ADD                                (* PLIC_BASE + PLIC_ENABLE0 (enable, M context) *)
        ; LI t2 [bv 0x100]                                        (* 1 << 8 *)
        ; STORE bv.zero t2 t0 WORD
        ; UTYPE (hi20 Target.plic_threshold0) t0 RISCV_LUI        (* threshold, M context *)
        ; LI t1 bv.zero
        ; STORE bv.zero t1 t0 WORD
        ; UTYPE (hi20 Target.plic_base) t0 RISCV_LUI
        ; LI t1 bv.one
        ; STORE [bv 0x020] t1 t0 WORD                             (* priority[8] <- 1; 0x20 = 4 * Target.virtio_irq *)

        (* mie. One assignment rather than two csrs: the kernel sets its own
           interrupt policy and must not inherit bits the firmware left in
           mie. This also keeps mie out of the read-modify-write path, which
           the model cannot fold back to a literal record. *)
        ; UTYPE [bv 0x00001] t0 RISCV_LUI
        ; ITYPE [bv 0xa88] t0 t0 RISCV_ADDI                       (* 0xa88: MSIE | MTIE | SEIE | MEIE *)
        ; CSRW Mie t0

        (* delegation *)
        ; UTYPE [bv 0xfffff] t0 RISCV_LUI
        ; ITYPE [bv 0x57f] t0 t0 RISCV_ADDI                       (* 0xfffff57f *)
        ; CSRW Medeleg t0
        ; LI t0 [bv 0x222]                                        (* SSIP | STIP | SEIP *)
        ; CSRW Mideleg t0
        ; LI t0 [bv 0x007]
        ; NOP                                                     (* [MODEL] csrw mcounteren, t0 (CY | TM | IR) *)

        (* mstatus.MPP <- S *)
        ; UTYPE [bv 0x00002] t0 RISCV_LUI
        ; ITYPE [bv 0x800] t0 t0 RISCV_ADDI                       (* MSTATUS_MPP_M = 0x1800 *)
        ; CSRC MStatus t0
        ; UTYPE [bv 0x00001] t0 RISCV_LUI
        ; ITYPE [bv 0x800] t0 t0 RISCV_ADDI                       (* MPP_S = 0x800 *)
        ; CSRS MStatus t0

        ; UTYPE (hi20 adv_start) t0 RISCV_LUI                     (* t0 <- ADV_START *)
        ; CSRW MEpc t0
        ; MRET
      ].
    Example femtokernel_init_block1' (start adv_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_init_asm_block1 adv_start) start.

    (* ====================================================================== *)
    (*  .femto_handler (directly follows .text, at 0x31c)                      *)
    (* ====================================================================== *)

    (* 0x334 .. 0x370 : switch to M stack, save context, interrupt? *)
    Example femtokernel_handler_asm_block0 (isr_start : N) : list ASM :=
      [
          CSR MScratch sp sp false CSRRW                          (* swap sp, mscratch *)
        ; ITYPE [bv 0xfd0] sp sp RISCV_ADDI                       (* sp <- sp - 48 *)
        ; STORE [bv 0x000] ra sp WORD
        ; STORE [bv 0x004] t0 sp WORD
        ; STORE [bv 0x008] t1 sp WORD
        ; STORE [bv 0x00c] t2 sp WORD
        ; STORE [bv 0x010] t3 sp WORD
        ; STORE [bv 0x014] t4 sp WORD
        ; STORE [bv 0x018] t5 sp WORD
        ; STORE [bv 0x01c] t6 sp WORD
        ; STORE [bv 0x020] a0 sp WORD
        ; STORE [bv 0x024] a1 sp WORD
        ; STORE [bv 0x028] a6 sp WORD
        ; STORE [bv 0x02c] a7 sp WORD
        ; CSRR t1 MCause
        ; Λ x, BTYPE (rel isr_start x) zero t1 RISCV_BLT          (* bltz t1, __isr *)
      ].
    Example femtokernel_handler_block0' (start isr_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm_block0 isr_start) start.

    (* 0x374 .. 0x378 : ecall from S-mode? *)
    Example femtokernel_handler_asm_block1 (sbi_ecall_start : N) : list ASM :=
      [
          LI t2 [bv 0x009]                                        (* E_S_EnvCall *)
        ; Λ x, BTYPE (rel sbi_ecall_start x) t2 t1 RISCV_BEQ
      ].
    Example femtokernel_handler_block1' (start sbi_ecall_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm_block1 sbi_ecall_start) start.

    (* 0x37c .. 0x388 : fault on the guarded LED word? *)
    (* TODO [MODEL]: the binary reads mtval into t2 here. Without it, t2 still
       holds 9 (handler_block1), so the branch to update_mmio is never taken in
       the model. Needs an mtval CSR that the trap handler sets on faults. *)
    Example femtokernel_handler_asm_block2 (led_sim update_mmio_start : N) : list ASM :=
      [
          NOP                                                     (* [MODEL] csrr t2, mtval *)
        ; UTYPE (hi20 led_sim) t3 RISCV_LUI                       (* li t3, KERNEL_RAM_LED_SIM *)
        ; ITYPE (lo12 led_sim) t3 t3 RISCV_ADDI
        ; Λ x, BTYPE (rel update_mmio_start x) t3 t2 RISCV_BEQ
      ].
    Example femtokernel_handler_block2' (start led_sim update_mmio_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm_block2 led_sim update_mmio_start) start.

    (* 0x38c : any other exception: skip the faulting instruction *)
    Example femtokernel_handler_asm_block3 (skip_done_start : N) : list ASM :=
      [
        Λ x, RISCV_JAL (rel skip_done_start x) zero               (* j __skip_done *)
      ].
    Example femtokernel_handler_block3' (start skip_done_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm_block3 skip_done_start) start.

    (* __isr, 0x378 .. 0x390 : strip interrupt bit; virtio button pending? *)
    Example femtokernel_isr_asm_block0 (button_start : N) : list ASM :=
      [
          SHIFTIOP bv.one t1 t1 RISCV_SLLI
        ; SHIFTIOP bv.one t1 t1 RISCV_SRLI                        (* t1 <- mcause & ~msb *)
        ; MV t2 t1                                                (* t2 <- interrupt code *)
        ; UTYPE (hi20 (virtio 0x060)) t0 RISCV_LUI
        ; ITYPE (lo12 (virtio 0x060)) t0 t0 RISCV_ADDI            (* BUTTON_INTERRUPT *)
        ; LOAD bv.zero t0 t1 false WORD
        ; Λ x, BTYPE (rel button_start x) zero t1 RISCV_BNE       (* bnez t1, __button *)
      ].
    Example femtokernel_isr_block0' (start button_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_isr_asm_block0 button_start) start.

    (* 0x3ac .. 0x3b0 *)
    Example femtokernel_isr_asm_block1 (mtip_start : N) : list ASM :=
      [
          LI t1 [bv 0x007]                                        (* M timer *)
        ; Λ x, BTYPE (rel mtip_start x) t1 t2 RISCV_BEQ
      ].
    Example femtokernel_isr_block1' (start mtip_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_isr_asm_block1 mtip_start) start.

    (* 0x3b4 .. 0x3b8 *)
    Example femtokernel_isr_asm_block2 (forward_start : N) : list ASM :=
      [
          LI t1 [bv 0x00b]                                        (* M external *)
        ; Λ x, BTYPE (rel forward_start x) t1 t2 RISCV_BEQ
      ].
    Example femtokernel_isr_block2' (start forward_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_isr_asm_block2 forward_start) start.

    (* 0x3bc *)
    Example femtokernel_isr_asm_block3 (unhandled_start : N) : list ASM :=
      [
        Λ x, RISCV_JAL (rel unhandled_start x) zero               (* j __unhandled *)
      ].
    Example femtokernel_isr_block3' (start unhandled_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_isr_asm_block3 unhandled_start) start.

    (* __mtip, 0x3a8 .. 0x3c0 : disarm M timer, raise STIP *)
    Example femtokernel_mtip_asm (rr_start : N) : list ASM :=
      [
          UTYPE (hi20 Target.clint_mtimecmp0) t0 RISCV_LUI        (* MTIMECMP0 *)
        ; LI t1 [bv 0xfff]                                        (* -1 *)
        ; STORE bv.zero t1 t0 WORD
        ; STORE [bv 0x004] t1 t0 WORD
        ; LI t0 [bv 0x020]                                        (* STIP *)
        ; CSRS Mip t0
        ; Λ x, RISCV_JAL (rel rr_start x) zero                    (* j __rr *)
      ].
    Example femtokernel_mtip' (start rr_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mtip_asm rr_start) start.

    (* __forward_s_mode, 0x3c4 .. 0x408 : emulate a trap into S-mode *)
    Example femtokernel_forward_s_mode_asm (rr_start : N) : list ASM :=
      [
          CSRR t0 MEpc
        ; CSRW SEpc t0
        ; CSRR t0 MCause
        ; CSRW SCause t0
        ; NOP                                                     (* [MODEL] csrr t0, mtval *)
        ; NOP                                                     (* [MODEL] csrw stval, t0 *)
        ; CSRR t0 MStatus
        ; UTYPE [bv 0xffffe] t1 RISCV_LUI
        ; ITYPE [bv 0x7ff] t1 t1 RISCV_ADDI                       (* ~MPP = 0xffffe7ff *)
        ; RTYPE t1 t0 t0 RISCV_AND
        ; UTYPE [bv 0x00001] t1 RISCV_LUI
        ; ITYPE [bv 0x800] t1 t1 RISCV_ADDI                       (* MPP_S = 0x800 *)
        ; RTYPE t1 t0 t0 RISCV_OR
        ; ITYPE [bv 0x080] t0 t0 RISCV_ORI                        (* MPIE *)
        ; CSRW MStatus t0
        ; CSRR t0 STvec
        ; CSRW MEpc t0                                            (* mret lands in stvec *)
        ; Λ x, RISCV_JAL (rel rr_start x) zero                    (* j __rr *)
      ].
    Example femtokernel_forward_s_mode' (start rr_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_forward_s_mode_asm rr_start) start.

    (* __sbi_ecall, 0x40c .. 0x420 *)
    Example femtokernel_sbi_ecall_asm_block0 (sbi_time_start : N) : list ASM :=
      [
          CSRR t0 MEpc
        ; ITYPE [bv 0x004] t0 t0 RISCV_ADDI
        ; CSRW MEpc t0                                            (* skip ecall *)
        ; UTYPE [bv 0x54495] t0 RISCV_LUI
        ; ITYPE [bv 0xd45] t0 t0 RISCV_ADDI                       (* SBI_EXT_TIME = 0x54494d45 *)
        ; Λ x, BTYPE (rel sbi_time_start x) t0 a7 RISCV_BEQ
      ].
    Example femtokernel_sbi_ecall_block0' (start sbi_time_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_ecall_asm_block0 sbi_time_start) start.

    (* 0x43c .. 0x444 *)
    Example femtokernel_sbi_ecall_asm_block1 (sbi_srst_start : N) : list ASM :=
      [
          UTYPE [bv 0x53525] t0 RISCV_LUI
        ; ITYPE [bv 0x354] t0 t0 RISCV_ADDI                       (* SBI_EXT_SRST = 0x53525354 *)
        ; Λ x, BTYPE (rel sbi_srst_start x) t0 a7 RISCV_BEQ
      ].
    Example femtokernel_sbi_ecall_block1' (start sbi_srst_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_ecall_asm_block1 sbi_srst_start) start.

    (* 0x448 .. 0x450 : unknown extension *)
    Example femtokernel_sbi_ecall_asm_block2 (sbi_done_start : N) : list ASM :=
      [
          LI a0 [bv 0xffe]                                        (* SBI_ERR_NOT_SUPPORTED = -2 *)
        ; STORE [bv 0x020] a0 sp WORD
        ; Λ x, RISCV_JAL (rel sbi_done_start x) zero
      ].
    Example femtokernel_sbi_ecall_block2' (start sbi_done_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_ecall_asm_block2 sbi_done_start) start.

    (* __sbi_time, 0x43c .. 0x440 *)
    Example femtokernel_sbi_time_asm_block0 (sbi_notsup_start : N) : list ASM :=
      [
          LI t0 bv.zero
        ; Λ x, BTYPE (rel sbi_notsup_start x) t0 a6 RISCV_BNE     (* fid <> set_timer *)
      ].
    Example femtokernel_sbi_time_block0' (start sbi_notsup_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_time_asm_block0 sbi_notsup_start) start.

    (* 0x45c .. 0x480 : set_timer(a1:a0) *)
    Example femtokernel_sbi_time_asm_block1 (sbi_done_start : N) : list ASM :=
      [
          UTYPE (hi20 Target.clint_mtimecmp0) t0 RISCV_LUI        (* MTIMECMP0 *)
        ; LI t1 [bv 0xfff]
        ; STORE [bv 0x004] t1 t0 WORD                             (* hi <- -1 first *)
        ; STORE bv.zero a0 t0 WORD
        ; STORE [bv 0x004] a1 t0 WORD
        ; LI t0 [bv 0x020]                                        (* STIP *)
        ; CSRC Mip t0
        ; LI a0 bv.zero
        ; LI a1 bv.zero
        ; Λ x, RISCV_JAL (rel sbi_done_start x) zero
      ].
    Example femtokernel_sbi_time_block1' (start sbi_done_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_time_asm_block1 sbi_done_start) start.

    (* __sbi_notsup, 0x46c .. 0x470 *)
    Example femtokernel_sbi_notsup_asm (sbi_done_start : N) : list ASM :=
      [
          LI a0 [bv 0xffe]
        ; Λ x, RISCV_JAL (rel sbi_done_start x) zero
      ].
    Example femtokernel_sbi_notsup' (start sbi_done_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_notsup_asm sbi_done_start) start.

    (* __sbi_srst, 0x474 .. 0x478 *)
    Example femtokernel_sbi_srst_asm (sbi_notsup_start : N) : list ASM :=
      [
          LI t0 bv.zero
        ; Λ x, BTYPE (rel sbi_notsup_start x) t0 a6 RISCV_BNE
      ].
    Example femtokernel_sbi_srst' (start sbi_notsup_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_srst_asm sbi_notsup_start) start.

    (* __sbi_srst_loop, 0x47c .. 0x480 : halt *)
    Example femtokernel_sbi_srst_loop_asm (sbi_srst_loop_start : N) : list ASM :=
      [
          NOP                                                     (* [MODEL] wfi *)
        ; Λ x, RISCV_JAL (rel sbi_srst_loop_start x) zero
      ].
    Example femtokernel_sbi_srst_loop' (start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_srst_loop_asm start) start.

    (* __sbi_done, 0x484 .. 0x48c : write a0/a1 into the saved frame *)
    Example femtokernel_sbi_done_asm (rr_start : N) : list ASM :=
      [
          STORE [bv 0x020] a0 sp WORD
        ; STORE [bv 0x024] a1 sp WORD
        ; Λ x, RISCV_JAL (rel rr_start x) zero
      ].
    Example femtokernel_sbi_done' (start rr_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_sbi_done_asm rr_start) start.

    (* __button, 0x490 : call into .text *)
    Example femtokernel_button_asm_block0 (virtio_irq_start : N) : list ASM :=
      [
        Λ x, RISCV_JAL (rel virtio_irq_start x) ra                (* call virtio_btn_irq_handler *)
      ].
    Example femtokernel_button_block0' (start virtio_irq_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_button_asm_block0 virtio_irq_start) start.

    (* 0x4ac .. 0x4f4 : iostate <- (~reset /\ iostate) \/ stop; PLIC claim/complete *)
    Example femtokernel_button_asm_block1 (iostate rr_start : N) : list ASM :=
      [
          UTYPE (hi20 iostate) t0 RISCV_LUI
        ; ITYPE (lo12 iostate) t0 t0 RISCV_ADDI
        ; LOAD bv.zero t0 t2 false WORD                           (* t2 <- iostate *)
        ; ITYPE bv.one t2 t2 RISCV_ANDI

        ; MV t3 t1
        ; SHIFTIOP [bv 0x3] t3 t3 RISCV_SRLI
        ; ITYPE bv.one t3 t3 RISCV_ANDI                           (* t3 <- reset *)

        ; MV t4 t1
        ; SHIFTIOP [bv 0x4] t4 t4 RISCV_SRLI
        ; ITYPE bv.one t4 t4 RISCV_ANDI                           (* t4 <- stop *)

        ; ITYPE bv.one t3 t3 RISCV_XORI                           (* t3 <- ~reset *)
        ; RTYPE t3 t2 t2 RISCV_AND
        ; RTYPE t4 t2 t2 RISCV_OR
        ; STORE bv.zero t2 t0 WORD                                (* store new iostate *)

        ; UTYPE (hi20 Target.plic_claim0) t1 RISCV_LUI
        ; ITYPE (lo12 Target.plic_claim0) t1 t1 RISCV_ADDI        (* PLIC claim/complete, M context *)
        ; LOAD bv.zero t1 t2 false WORD                           (* claim *)
        ; STORE bv.zero t2 t1 WORD                                (* complete *)
        ; Λ x, RISCV_JAL (rel rr_start x) zero
      ].
    Example femtokernel_button_block1' (start iostate rr_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_button_asm_block1 iostate rr_start) start.

    (* __update_mmio, 0x4e0 .. 0x504 : LED write only in SGo; falls through
       into __skip_done *)
    Example femtokernel_update_mmio_asm (iostate led_sim : N) : list ASM :=
      [
          UTYPE (hi20 iostate) t0 RISCV_LUI
        ; ITYPE (lo12 iostate) t0 t0 RISCV_ADDI
        ; LOAD bv.zero t0 t2 false WORD                           (* t2 <- iostate *)
        ; ITYPE bv.one t2 t2 RISCV_ANDI
        ; ITYPE bv.one t2 t2 RISCV_XORI                           (* invert: SGo = 0, SStop = 1 *)
        ; SHIFTIOP [bv 0x5] t2 t2 RISCV_SLLI                      (* mask bit 5 (LED) *)
        ; RTYPE t2 a0 a0 RISCV_AND                                (* a0 <- a0 /\ t2 *)
        ; UTYPE (hi20 led_sim) t0 RISCV_LUI
        ; ITYPE (lo12 led_sim) t0 t0 RISCV_ADDI
        ; STORE bv.zero a0 t0 WORD                                (* LED <- a0 *)
      ].
    Example femtokernel_update_mmio' (start iostate led_sim : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_update_mmio_asm iostate led_sim) start.

    (* __skip_done, 0x508 .. 0x51c : advance mepc past the trapping instruction *)
    Example femtokernel_skip_done_asm_loop (skip_done_start : N) : list ASM :=
      [
          CSRR t0 MEpc
        ; LOAD bv.zero t0 t1 false HALF                           (* lh t1, 0(t0) *)
        ; ITYPE [bv 0x002] t0 t0 RISCV_ADDI
        ; ITYPE [bv 0x003] t1 t1 RISCV_ANDI
        ; LI t2 [bv 0x003]
        ; Λ x, BTYPE (rel skip_done_start x) t2 t1 RISCV_BNE
      ].
    Example femtokernel_skip_done_loop' (start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_skip_done_asm_loop start) start.

    (* 0x538 .. 0x540 *)
    Example femtokernel_skip_done_asm_exit (rr_start : N) : list ASM :=
      [
          ITYPE [bv 0x002] t0 t0 RISCV_ADDI
        ; CSRW MEpc t0
        ; Λ x, RISCV_JAL (rel rr_start x) zero
      ].
    Example femtokernel_skip_done_exit' (start rr_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_skip_done_asm_exit rr_start) start.

    (* __unhandled, 0x52c .. 0x530 : halt *)
    Example femtokernel_unhandled_asm (unhandled_start : N) : list ASM :=
      [
          NOP                                                     (* [MODEL] wfi *)
        ; Λ x, RISCV_JAL (rel unhandled_start x) zero
      ].
    Example femtokernel_unhandled' (start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_unhandled_asm start) start.

    (* __rr, 0x534 .. 0x56c : restore context and return *)
    Example femtokernel_rr_asm : list ASM :=
      [
          LOAD [bv 0x000] sp ra false WORD
        ; LOAD [bv 0x004] sp t0 false WORD
        ; LOAD [bv 0x008] sp t1 false WORD
        ; LOAD [bv 0x00c] sp t2 false WORD
        ; LOAD [bv 0x010] sp t3 false WORD
        ; LOAD [bv 0x014] sp t4 false WORD
        ; LOAD [bv 0x018] sp t5 false WORD
        ; LOAD [bv 0x01c] sp t6 false WORD
        ; LOAD [bv 0x020] sp a0 false WORD
        ; LOAD [bv 0x024] sp a1 false WORD
        ; LOAD [bv 0x028] sp a6 false WORD
        ; LOAD [bv 0x02c] sp a7 false WORD
        ; ITYPE [bv 0x030] sp sp RISCV_ADDI
        ; CSR MScratch sp sp false CSRRW                          (* swap back *)
        ; MRET
      ].
    Example femtokernel_rr' (start : N) : list AnnotInstr :=
      resolve_ASM femtokernel_rr_asm start.


    (* ====================================================================== *)
    (*  Layout                                                                 *)
    (* ====================================================================== *)

    Definition Label       : Set := string.
    Definition Block       : Set := list AnnotInstr.

    Definition entry              : Label := "entry".
    Definition virtio_init        : Label := "virtio_init".
    Definition virtio_irq_block0  : Label := "virtio_irq_block0".
    Definition virtio_irq_head    : Label := "virtio_irq_head".
    Definition virtio_irq_body    : Label := "virtio_irq_body".
    Definition virtio_irq_tail    : Label := "virtio_irq_tail".
    Definition virtio_irq_exit    : Label := "virtio_irq_exit".
    Definition handle_byte_block0 : Label := "handle_byte_block0".
    Definition handle_byte_block1 : Label := "handle_byte_block1".
    Definition handle_byte_other  : Label := "handle_byte_other".
    Definition handle_byte_is_r   : Label := "handle_byte_is_r".
    Definition handle_byte_is_s   : Label := "handle_byte_is_s".
    Definition init_block0        : Label := "init_block0".
    Definition init_block1        : Label := "init_block1".
    Definition handler_block0     : Label := "handler_block0".
    Definition handler_block1     : Label := "handler_block1".
    Definition handler_block2     : Label := "handler_block2".
    Definition handler_block3     : Label := "handler_block3".
    Definition isr_block0         : Label := "isr_block0".
    Definition isr_block1         : Label := "isr_block1".
    Definition isr_block2         : Label := "isr_block2".
    Definition isr_block3         : Label := "isr_block3".
    Definition mtip               : Label := "mtip".
    Definition forward_s_mode     : Label := "forward_s_mode".
    Definition sbi_ecall_block0   : Label := "sbi_ecall_block0".
    Definition sbi_ecall_block1   : Label := "sbi_ecall_block1".
    Definition sbi_ecall_block2   : Label := "sbi_ecall_block2".
    Definition sbi_time_block0    : Label := "sbi_time_block0".
    Definition sbi_time_block1    : Label := "sbi_time_block1".
    Definition sbi_notsup         : Label := "sbi_notsup".
    Definition sbi_srst           : Label := "sbi_srst".
    Definition sbi_srst_loop      : Label := "sbi_srst_loop".
    Definition sbi_done           : Label := "sbi_done".
    Definition button_block0      : Label := "button_block0".
    Definition button_block1      : Label := "button_block1".
    Definition update_mmio        : Label := "update_mmio".
    Definition skip_done_loop     : Label := "skip_done_loop".
    Definition skip_done_exit     : Label := "skip_done_exit".
    Definition unhandled          : Label := "unhandled".
    Definition rr                 : Label := "rr".

    (* In binary order; the sizes do not depend on the arguments. *)
    Definition femtokernel_block_layout : list (Label * Block) :=
      [ (entry             , femtokernel_entry' 0 0)                     (* 0x000 *)
      ; (virtio_init       , femtokernel_virtio_init' 0 0 0 0)           (* 0x004 *)
      ; (virtio_irq_block0 , femtokernel_virtio_irq_block0' 0 0 0)       (* 0x10c *)
      ; (virtio_irq_head   , femtokernel_virtio_irq_loop_head' 0 0)      (* 0x150 *)
      ; (virtio_irq_body   , femtokernel_virtio_irq_loop_body' 0 0 0)    (* 0x154 *)
      ; (virtio_irq_tail   , femtokernel_virtio_irq_loop_tail' 0 0)      (* 0x164 *)
      ; (virtio_irq_exit   , femtokernel_virtio_irq_exit' 0 0 0)         (* 0x170 *)
      ; (handle_byte_block0, femtokernel_handle_byte_block0' 0 0)        (* 0x1b0 *)
      ; (handle_byte_block1, femtokernel_handle_byte_block1' 0 0)        (* 0x1b8 *)
      ; (handle_byte_other , femtokernel_handle_byte_other' 0)           (* 0x1c0 *)
      ; (handle_byte_is_r  , femtokernel_handle_byte_is_r' 0)            (* 0x1c8 *)
      ; (handle_byte_is_s  , femtokernel_handle_byte_is_s' 0)            (* 0x1d0 *)
      ; (init_block0       , femtokernel_init_block0' 0 0 0 0 0)         (* 0x1d8 *)
      ; (init_block1       , femtokernel_init_block1' 0 0)               (* 0x2b0 *)
      ; (handler_block0    , femtokernel_handler_block0' 0 0)            (* 0x334 *)
      ; (handler_block1    , femtokernel_handler_block1' 0 0)            (* 0x374 *)
      ; (handler_block2    , femtokernel_handler_block2' 0 0 0)          (* 0x37c *)
      ; (handler_block3    , femtokernel_handler_block3' 0 0)            (* 0x38c *)
      ; (isr_block0        , femtokernel_isr_block0' 0 0)                (* 0x390 *)
      ; (isr_block1        , femtokernel_isr_block1' 0 0)                (* 0x3ac *)
      ; (isr_block2        , femtokernel_isr_block2' 0 0)                (* 0x3b4 *)
      ; (isr_block3        , femtokernel_isr_block3' 0 0)                (* 0x3bc *)
      ; (mtip              , femtokernel_mtip' 0 0)                      (* 0x3c0 *)
      ; (forward_s_mode    , femtokernel_forward_s_mode' 0 0)            (* 0x3dc *)
      ; (sbi_ecall_block0  , femtokernel_sbi_ecall_block0' 0 0)          (* 0x424 *)
      ; (sbi_ecall_block1  , femtokernel_sbi_ecall_block1' 0 0)          (* 0x43c *)
      ; (sbi_ecall_block2  , femtokernel_sbi_ecall_block2' 0 0)          (* 0x448 *)
      ; (sbi_time_block0   , femtokernel_sbi_time_block0' 0 0)           (* 0x454 *)
      ; (sbi_time_block1   , femtokernel_sbi_time_block1' 0 0)           (* 0x45c *)
      ; (sbi_notsup        , femtokernel_sbi_notsup' 0 0)                (* 0x484 *)
      ; (sbi_srst          , femtokernel_sbi_srst' 0 0)                  (* 0x48c *)
      ; (sbi_srst_loop     , femtokernel_sbi_srst_loop' 0)               (* 0x494 *)
      ; (sbi_done          , femtokernel_sbi_done' 0 0)                  (* 0x49c *)
      ; (button_block0     , femtokernel_button_block0' 0 0)             (* 0x4a8 *)
      ; (button_block1     , femtokernel_button_block1' 0 0 0)           (* 0x4ac *)
      ; (update_mmio       , femtokernel_update_mmio' 0 0 0)             (* 0x4f8 *)
      ; (skip_done_loop    , femtokernel_skip_done_loop' 0)              (* 0x520 *)
      ; (skip_done_exit    , femtokernel_skip_done_exit' 0 0)            (* 0x538 *)
      ; (unhandled         , femtokernel_unhandled' 0)                   (* 0x544 *)
      ; (rr                , femtokernel_rr' 0)                          (* 0x54c *)
      ]%list.                                                            (* end: 0x588 *)

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
    Definition instruction_size : N := N.of_nat bytes_per_instr.
    Definition data_size : N := N.of_nat xlenbytes.

    (* ADDRESSES *)

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
    (* The kernel is loaded at the start of RAM. *)
    Definition init_addr : N := Eval compute in Layout.code_start.

    Definition femtokernel_block_addrs : list (Label * N) :=
      addrs_for_blocks (map_with_label filter_AnnotInstr_AST femtokernel_block_layout) init_addr.

    (* Note that we need to use "Eval compute in ..." for all addresses.
       In proofs below, we often use cbn/simpl/..., which will hang if we
       don't compute here. *)

    Definition data_addr                 : N :=
      Eval compute in snd (List.last femtokernel_block_addrs ("_", 0%N)).
    (* We allocate one word for the data addr *)

    (* KERNEL DATA AND THE S-MODE PAYLOAD
       Linker symbols, placed on the target by Layout.v. As for the block
       addresses, we compute them here so cbn/simpl do not get stuck on
       them later. *)
    Definition iostate_addr          : N := Eval compute in Layout.iostate.          (* KERNEL_RAM_IOSTATE *)
    Definition rx_used_seen_addr     : N := Eval compute in Layout.rx_used_seen.     (* rx_used_seen *)
    Definition kernel_stack_top_addr : N := Eval compute in Layout.kernel_stack_top. (* __kernel_stack_top *)
    Definition adv_addr              : N := Eval compute in Layout.adv_start.        (* ADV_START *)
    (* Device memory in the model (see Target.v) *)
    Definition led_sim_addr          : N := Eval compute in Layout.led_sim.          (* KERNEL_RAM_LED_SIM *)
    Definition virtq_mem_addr        : N := Eval compute in Layout.virtq_mem.        (* virtq_mem *)
    Definition rx_buf_addr           : N := Eval compute in Layout.rx_buf.           (* rx_buf *)

    (* We compute all addresses w.r.t. the FemtoKernel block layout at once.
       Note that we also get the "end" or "exit" address of our kernel as
       part of this definition. So the resulting list has a length of:
       number of blocks + 1. *)

    Definition entry_addr              : N := Eval compute in find_label entry              femtokernel_block_addrs 0%N.
    Definition virtio_init_addr        : N := Eval compute in find_label virtio_init        femtokernel_block_addrs 0%N.
    Definition virtio_irq_block0_addr  : N := Eval compute in find_label virtio_irq_block0  femtokernel_block_addrs 0%N.
    Definition virtio_irq_head_addr    : N := Eval compute in find_label virtio_irq_head    femtokernel_block_addrs 0%N.
    Definition virtio_irq_body_addr    : N := Eval compute in find_label virtio_irq_body    femtokernel_block_addrs 0%N.
    Definition virtio_irq_tail_addr    : N := Eval compute in find_label virtio_irq_tail    femtokernel_block_addrs 0%N.
    Definition virtio_irq_exit_addr    : N := Eval compute in find_label virtio_irq_exit    femtokernel_block_addrs 0%N.
    Definition handle_byte_block0_addr : N := Eval compute in find_label handle_byte_block0 femtokernel_block_addrs 0%N.
    Definition handle_byte_block1_addr : N := Eval compute in find_label handle_byte_block1 femtokernel_block_addrs 0%N.
    Definition handle_byte_other_addr  : N := Eval compute in find_label handle_byte_other  femtokernel_block_addrs 0%N.
    Definition handle_byte_is_r_addr   : N := Eval compute in find_label handle_byte_is_r   femtokernel_block_addrs 0%N.
    Definition handle_byte_is_s_addr   : N := Eval compute in find_label handle_byte_is_s   femtokernel_block_addrs 0%N.
    Definition init_block0_addr        : N := Eval compute in find_label init_block0        femtokernel_block_addrs 0%N.
    Definition init_block1_addr        : N := Eval compute in find_label init_block1        femtokernel_block_addrs 0%N.
    Definition handler_block0_addr     : N := Eval compute in find_label handler_block0     femtokernel_block_addrs 0%N.
    Definition handler_block1_addr     : N := Eval compute in find_label handler_block1     femtokernel_block_addrs 0%N.
    Definition handler_block2_addr     : N := Eval compute in find_label handler_block2     femtokernel_block_addrs 0%N.
    Definition handler_block3_addr     : N := Eval compute in find_label handler_block3     femtokernel_block_addrs 0%N.
    Definition isr_block0_addr         : N := Eval compute in find_label isr_block0         femtokernel_block_addrs 0%N.
    Definition isr_block1_addr         : N := Eval compute in find_label isr_block1         femtokernel_block_addrs 0%N.
    Definition isr_block2_addr         : N := Eval compute in find_label isr_block2         femtokernel_block_addrs 0%N.
    Definition isr_block3_addr         : N := Eval compute in find_label isr_block3         femtokernel_block_addrs 0%N.
    Definition mtip_addr               : N := Eval compute in find_label mtip               femtokernel_block_addrs 0%N.
    Definition forward_s_mode_addr     : N := Eval compute in find_label forward_s_mode     femtokernel_block_addrs 0%N.
    Definition sbi_ecall_block0_addr   : N := Eval compute in find_label sbi_ecall_block0   femtokernel_block_addrs 0%N.
    Definition sbi_ecall_block1_addr   : N := Eval compute in find_label sbi_ecall_block1   femtokernel_block_addrs 0%N.
    Definition sbi_ecall_block2_addr   : N := Eval compute in find_label sbi_ecall_block2   femtokernel_block_addrs 0%N.
    Definition sbi_time_block0_addr    : N := Eval compute in find_label sbi_time_block0    femtokernel_block_addrs 0%N.
    Definition sbi_time_block1_addr    : N := Eval compute in find_label sbi_time_block1    femtokernel_block_addrs 0%N.
    Definition sbi_notsup_addr         : N := Eval compute in find_label sbi_notsup         femtokernel_block_addrs 0%N.
    Definition sbi_srst_addr           : N := Eval compute in find_label sbi_srst           femtokernel_block_addrs 0%N.
    Definition sbi_srst_loop_addr      : N := Eval compute in find_label sbi_srst_loop      femtokernel_block_addrs 0%N.
    Definition sbi_done_addr           : N := Eval compute in find_label sbi_done           femtokernel_block_addrs 0%N.
    Definition button_block0_addr      : N := Eval compute in find_label button_block0      femtokernel_block_addrs 0%N.
    Definition button_block1_addr      : N := Eval compute in find_label button_block1      femtokernel_block_addrs 0%N.
    Definition update_mmio_addr        : N := Eval compute in find_label update_mmio        femtokernel_block_addrs 0%N.
    Definition skip_done_loop_addr     : N := Eval compute in find_label skip_done_loop     femtokernel_block_addrs 0%N.
    Definition skip_done_exit_addr     : N := Eval compute in find_label skip_done_exit     femtokernel_block_addrs 0%N.
    Definition unhandled_addr          : N := Eval compute in find_label unhandled          femtokernel_block_addrs 0%N.
    Definition rr_addr                 : N := Eval compute in find_label rr                 femtokernel_block_addrs 0%N.


    (* Sanity check against the binary: offsets relative to its load address
       0x80000000, here init_addr. *)
    Goal (handler_block0_addr - init_addr = 0x328 /\ update_mmio_addr - init_addr = 0x4ec
          /\ rr_addr - init_addr = 0x540 /\ data_addr - init_addr = 0x57c)%N.
    Proof. repeat split; now vm_compute. Qed.

    (* The kernel's code ends before the S-mode payload starts. *)
    Goal (data_addr <= adv_addr)%N.
    Proof. now vm_compute. Qed.

    (* Addresses the binary loads with a lone `lui`: their low 12 bits must
       be zero, otherwise the model would load a different value than the
       symbol. If one of these fails, the layout violates an alignment
       assumption of the code (or the code needs an `addi`). *)
    Goal lo12 Target.clint_mtimecmp0 = bv.zero
         /\ lo12 Target.plic_base = bv.zero
         /\ lo12 (Target.plic_enable0 - Target.plic_base) = bv.zero
         /\ lo12 Target.plic_threshold0 = bv.zero
         /\ lo12 adv_addr = bv.zero
         /\ lo12 Layout.region0 = bv.zero /\ lo12 Layout.region1 = bv.zero
         /\ lo12 Layout.region6 = bv.zero /\ lo12 Layout.region9 = bv.zero
         /\ lo12 Layout.region10 = bv.zero /\ lo12 Layout.region11 = bv.zero
         /\ lo12 Layout.region12 = bv.zero.
    Proof. repeat split; now vm_compute. Qed.

    (* The LED word is where IO events are recorded. *)
    Goal led_sim_addr = mmio_dev_addr.
    Proof. now vm_compute. Qed.

  End FemtoKernel.
