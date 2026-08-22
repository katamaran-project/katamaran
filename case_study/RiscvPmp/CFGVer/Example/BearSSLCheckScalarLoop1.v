(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and this disclaimer.                            *)
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

(* ========================================================================= *)
(* Example/BearSSLCheckScalarLoop1.v — BearSSL P-256 `check_scalar` loop 1.   *)
(*                                                                           *)
(* Promoted from the ZZByteLoop1* throwaway probes (PLAN-byte-memory.md §6   *)
(* step 2 / PLAN-check-scalar-full.md §3) once the byte-granular Iris wiring *)
(* (gen_contract_noninterferent_rel_bytes, EndToEnd.v) landed.  The first    *)
(* byte-granular (lbu) example in the repo -- klen fixed at the real P-256   *)
(* value 32, not left parametric in the trip count.                         *)
(*                                                                           *)
(* The instruction list and reg/byte spec definitions below are             *)
(* STATEMENT-RELEVANT: the noninterference theorem in                        *)
(* BearSSLCheckScalarLoop1Result.v references them by name.  The contract    *)
(* and valid_* VC proof are not.                                            *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

(* ------------------------------------------------------------------------ *)
(* ORIGINAL C — BearSSL src/ec/ec_p256_m62.c:1610 (commit 79c060e), loop 1:  *)
(*                                                                           *)
(*     z = 0;                                                                *)
(*     for (u = 0; u < klen; u++) { z |= k[u]; }                             *)
(*                                                                           *)
(* Not term-walled (z occurs once per iteration) and byte-loads via `lbu`,   *)
(* so it isolates the byte-memory plumbing from loop 2's mask accumulator.   *)
(*                                                                           *)
(* REAL clang 18.1.3 --target=riscv32 -march=rv32i -mabi=ilp32 -O2 output    *)
(* for `uint32_t loop1(const unsigned char *k, size_t klen)`:                *)
(*                                                                           *)
(*     li      a2, 0                                                         *)
(*     beqz    a1, .LBB0_3                                                   *)
(*     add     a1, a0, a1                                                    *)
(* .LBB0_2:                                                                  *)
(*     lbu     a3, 0(a0)      <-- the loop body verified below               *)
(*     addi    a0, a0, 1                                                     *)
(*     or      a2, a2, a3                                                    *)
(*     bne     a0, a1, .LBB0_2                                               *)
(* .LBB0_3:                                                                  *)
(*     mv      a0, a2                                                        *)
(*     ret                                                                   *)
(*                                                                           *)
(* Verified here is the LOOP (.LBB0_2), with the prologue's effects moved    *)
(* into the precondition: A0 = &k[0], A1 = &k[32] (the end pointer clang     *)
(* computes as a0+klen), A2 = 0.  The loop-exit test is a POINTER COMPARE on *)
(* two base-relative addresses, not a counter-vs-zero test -- clang's own    *)
(* choice, and exactly the driver (B) pointer-compare cost PLAN-check-       *)
(* scalar-full.md's Phase 1 (try_bvadd_cancel_spec) closed.                  *)
(* ------------------------------------------------------------------------ *)

(* -12 in 13-bit two's complement: the BNE sits at byte offset 12 and jumps
   back to offset 0 (branch immediates are relative to the branch's own
   address).  Same constant as Countdown.v's back_12_offset. *)
Definition loop1_back_offset : bv 13 := bv.of_N 8180.

Definition loop1_instrs : list AST :=
  [ LBU A3 A0 (bv.of_N 0)                   (* lbu  a3, 0(a0) *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI      (* addi a0, a0, 1 *)
  ; RTYPE A3 A2 A2 RISCV_OR                 (* or   a2, a2, a3 *)
  ; BNE A0 A1 loop1_back_offset             (* bne  a0, a1, .LBB0_2 *)
  ].

(* The 4 instructions occupy p+0..p+15, so k[] starts at p+16 -- contiguous
   right after the code, as every other example's data is.

   A0 = &k[0] = p+16 and A1 = &k[32] = p+48 are ADDRESSES: public, and
   base-relative, hence PVBaseOff (the _rel family).  A2 is the accumulator,
   pinned to 0 on entry; it becomes secret as soon as the first byte is OR'd
   in.  A3 receives the loaded byte, so it is private. *)
Definition loop1_reg_specs_rel : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 16)
  ; (A1, true,  PVBaseOff 48)
  ; (A2, true,  PVConst (bv.of_N 0))
  ; (A3, false, PVExist)
  ].

(* 8 byte-expanded word entries at offsets 16, 20, ..., 44 -- covering k[0..31]
   (the real P-256 klen).  The declaration unit stays a WORD (stride 4) even
   though the chunks handed to the executor are bytes -- that is what keeps
   the trusted layer (Noninterference.v's mem_spec) untouched. *)
Definition loop1_byte_specs_rel : list mem_spec_rel :=
  [ (16%N, false, PVExist); (20%N, false, PVExist)
  ; (24%N, false, PVExist); (28%N, false, PVExist)
  ; (32%N, false, PVExist); (36%N, false, PVExist)
  ; (40%N, false, PVExist); (44%N, false, PVExist)
  ].

(* Base bound 48: the last declared byte (k[31]) sits at offset 47, so the
   width-1 access bound needs unsigned p + 48 <= lenAddr.  Fuel 136 = 4*32+8
   (one demonic step per instruction per of the 32 trips, plus slack for the
   fall-through exit step) -- matches ZZByteLoop1Common.v's formula at n=32. *)
Definition loop1_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia loop1_reg_specs_rel [] loop1_byte_specs_rel
    loop1_instrs [] 48
    (pcOutOfInstrs_exitCond ia loop1_instrs) 136.

(* TRUSTED-SURFACE ANCHOR (AnnotInstr migration, PLAN-annotinstr.md).
   The end theorem states noninterferent_strong over `loop1_instrs` while the
   EndToEnd bridges now conclude over `strip instrs`.  This is what makes
   those the SAME statement, and it MUST close by `reflexivity` -- if it
   ever needs more, the migration has changed what is being proved and
   must stop.  An auditor checks one thing: that `strip` is a plain
   projection. *)
Lemma strip_id_loop1_instrs : strip loop1_instrs = loop1_instrs.
Proof. reflexivity. Qed.

Lemma valid_loop1_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (loop1_cfg_contract_param ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
