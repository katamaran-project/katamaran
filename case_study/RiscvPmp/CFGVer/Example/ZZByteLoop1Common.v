(* ========================================================================= *)
(* Example/ZZByteLoop1Common.v — THROWAWAY, PLAN-byte-memory.md §6 step 2.    *)
(*                                                                           *)
(* BearSSL check_scalar LOOP 1 (`z |= k[u]`), parameterised on the trip count *)
(* N so the byte-memory cost curve can be fitted over N = 4, 8, 16.  Loop 1   *)
(* rather than loop 2 because it byte-loads but is NOT term-walled (z occurs  *)
(* once per iteration), so it isolates the byte plumbing from loop 2's        *)
(* accumulator.                                                              *)
(*                                                                           *)
(* REAL clang 18.1.3 --target=riscv32 -march=rv32i -mabi=ilp32 -O2 output for *)
(*                                                                           *)
(*     uint32_t loop1(const unsigned char *k, size_t klen) {                  *)
(*         uint32_t z = 0; size_t u;                                          *)
(*         for (u = 0; u < klen; u ++) { z |= k[u]; }                         *)
(*         return z;                                                          *)
(*     }                                                                      *)
(*                                                                           *)
(*     loop1:                                                                 *)
(*             li      a2, 0                                                  *)
(*             beqz    a1, .LBB0_3                                            *)
(*             add     a1, a0, a1                                             *)
(*     .LBB0_2:                                                               *)
(*             lbu     a3, 0(a0)      <-- the loop body verified below        *)
(*             addi    a0, a0, 1                                              *)
(*             or      a2, a2, a3                                             *)
(*             bne     a0, a1, .LBB0_2                                        *)
(*     .LBB0_3:                                                               *)
(*             mv      a0, a2                                                 *)
(*             ret                                                            *)
(*                                                                           *)
(* Verified here is the LOOP (.LBB0_2), with the prologue's effects moved into *)
(* the precondition: A0 = &k[0], A1 = &k[N] (the end pointer clang computes as *)
(* a0+klen), A2 = 0.  Note the loop-exit test is a POINTER COMPARE on two      *)
(* base-relative addresses, not a counter-vs-zero test as in                   *)
(* Example/KeyScheduleLoop.v -- that is clang's own choice here.               *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

(* -12 in 13-bit two's complement: the BNE sits at byte offset 12 and jumps
   back to offset 0 (branch immediates are relative to the branch's OWN
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

   A0 = &k[0] = p+16 and A1 = &k[N] = p+16+N are ADDRESSES: public, and
   base-relative, hence PVBaseOff (the _rel family).  A2 is the accumulator,
   pinned to 0 on entry; it becomes secret as soon as the first byte is OR'd
   in.  A3 receives the loaded byte, so it is private. *)
Definition loop1_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 16)
  ; (A1, true,  PVBaseOff (16 + n)%N)
  ; (A2, true,  PVConst (bv.of_N 0))
  ; (A3, false, PVExist)
  ].

(* n/4 byte-expanded word entries at offsets 16, 20, ..., 16+n-4.  The
   declaration unit stays a WORD (stride 4) even though the chunks handed to
   the executor are bytes -- that is what keeps the trusted layer untouched.
   n must be a multiple of 4. *)
Definition loop1_byte_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((16 + 4 * N.of_nat i)%N, false, PVExist))
      (seq 0 (Nat.div (N.to_nat n) 4)).

(* bound = 16 + n: the last declared byte sits at offset 16+n-1, so the
   width-1 access bound needs unsigned p + 16 + n <= lenAddr. *)
Definition loop1_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia (loop1_reg_specs_rel n) [] (loop1_byte_specs_rel n)
    loop1_instrs [] (16 + n)%N
    (pcOutOfInstrs_exitCond ia loop1_instrs)
    (Nat.add (Nat.mul 4 (N.to_nat n)) 8).
