(* ========================================================================= *)
(* Example/ZZByteLoop2Common.v — THROWAWAY, PLAN-check-scalar-full.md §4.      *)
(*                                                                           *)
(* BearSSL check_scalar LOOP 2 (`c |= -EQ0(c) & CMP(k[u], n[u])`), parameterised*)
(* on the trip count/byte count N so the cost curve can be fitted over        *)
(* N = 4, 8, 16, 32.  Both k[] and n[] are byte-loaded (`lbu`) and advance in  *)
(* lockstep; the loop-exit test compares the ADVANCING n-POINTER against its  *)
(* own end pointer (A1 vs A2) -- A0 (k-pointer) is incremented but never      *)
(* compared, trusting the caller that both arrays have the same length.       *)
(*                                                                           *)
(* Per §4's guidance, n[] (P256_N, the curve-order constant) is tried as      *)
(* PUBLIC-BUT-UNPINNED (PVExist, is_pub = true) FIRST, not PVConst: loop 2's   *)
(* chain is branch-free, so nothing branches on the comparison, and           *)
(* publicness is all noninterference needs -- the deferred word_byte/        *)
(* PVConst subrange work should not be necessary.                            *)
(*                                                                           *)
(* REAL clang 18.1.3 --target=riscv32 -march=rv32i -mabi=ilp32 -O2 output for  *)
(*                                                                           *)
(*     int32_t loop2(const uint8_t *k, const uint8_t *n, size_t klen) {       *)
(*         int32_t c = 0; size_t u;                                          *)
(*         for (u = 0; u < klen; u++)                                        *)
(*             c |= -(int32_t)EQ0(c) & CMP((uint32_t)k[u], (uint32_t)n[u]);   *)
(*         return c;                                                         *)
(*     }                                                                     *)
(*                                                                           *)
(* (GT/CMP/EQ0 as in BearSSLCheckScalar.v's header.) Compiled standalone      *)
(* rather than reusing check_scalar_step's 16-instr body: clang picked a      *)
(* SHORTER comparison sequence here (two `sltu` + `neg`/`or`, not the         *)
(* XOR-based GT formula) -- a different but equally branch-free idiom.       *)
(* Listing:                                                                  *)
(*                                                                           *)
(*     li      a3, 0                                                         *)
(*     beqz    a2, .LBB0_3                                                   *)
(*     add     a2, a1, a2                                                    *)
(* .LBB0_2:                                                                  *)
(*     lbu     a4, 0(a0)      <-- the loop body verified below               *)
(*     lbu     a5, 0(a1)                                                     *)
(*     sltu    a6, a5, a4                                                    *)
(*     sltu    a4, a4, a5                                                    *)
(*     neg     a4, a4                                                        *)
(*     or      a4, a4, a6                                                    *)
(*     snez    a5, a3                                                        *)
(*     addi    a5, a5, -1                                                    *)
(*     and     a4, a5, a4                                                    *)
(*     or      a3, a4, a3                                                    *)
(*     addi    a1, a1, 1                                                     *)
(*     addi    a0, a0, 1                                                     *)
(*     bne     a1, a2, .LBB0_2                                               *)
(* .LBB0_3:                                                                  *)
(*     mv      a0, a3                                                        *)
(*     ret                                                                   *)
(*                                                                           *)
(* Verified here is the LOOP (.LBB0_2), prologue effects moved into the       *)
(* precondition: A0 = &k[0], A1 = &n[0], A2 = &n[N] (n1's end, NOT k's),      *)
(* A3 = 0.  Translated with tools/asm_to_ast.py.                             *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

(* -48 in 13-bit two's complement (8192 - 48 = 8144): the BNE sits at byte
   offset 48 (12 instructions in) and jumps back to offset 0. *)
Definition loop2_back_offset : bv 13 := bv.of_N 8144.

Definition loop2_instrs : list AST :=
  [ LBU A4 A0 (bv.of_N 0)                    (* lbu  a4, 0(a0) *)
  ; LBU A5 A1 (bv.of_N 0)                    (* lbu  a5, 0(a1) *)
  ; RTYPE A4 A5 A6 RISCV_SLTU                (* sltu a6, a5, a4 *)
  ; RTYPE A5 A4 A4 RISCV_SLTU                (* sltu a4, a4, a5 *)
  ; RTYPE A4 X0 A4 RISCV_SUB                 (* neg  a4, a4 *)
  ; RTYPE A6 A4 A4 RISCV_OR                  (* or   a4, a4, a6 *)
  ; RTYPE A3 X0 A5 RISCV_SLTU                (* snez a5, a3 *)
  ; ITYPE (bv.of_Z (-1)) A5 A5 RISCV_ADDI    (* addi a5, a5, -1 *)
  ; RTYPE A4 A5 A4 RISCV_AND                 (* and  a4, a5, a4 *)
  ; RTYPE A4 A3 A3 RISCV_OR                  (* or   a3, a4, a3 *)
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI       (* addi a1, a1, 1 *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI       (* addi a0, a0, 1 *)
  ; BNE A1 A2 loop2_back_offset              (* bne  a1, a2, .LBB0_2 *)
  ].

(* 13 instructions * 4 bytes = 52, so k[] starts at p+52.  A0 = &k[0] = p+52,
   A1 = &n[0] = p+52+n, A2 = &n[N] = p+52+n+n (n = byte count = N here).
   A3 is the accumulator, pinned to 0 on entry, becoming secret as soon as
   the first comparison is OR'd in.  A4-A6 are private scratch. *)
Definition loop2_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 52)
  ; (A1, true,  PVBaseOff (52 + n)%N)
  ; (A2, true,  PVBaseOff (52 + n + n)%N)
  ; (A3, true,  PVConst (bv.of_N 0))
  ; (A4, false, PVExist)
  ; (A5, false, PVExist)
  ; (A6, false, PVExist)
  ].

(* k[]: n/4 SECRET byte-expanded word entries at offsets 52, 56, ..., 52+n-4. *)
Definition loop2_k_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((52 + 4 * N.of_nat i)%N, false, PVExist))
      (seq 0 (Nat.div (N.to_nat n) 4)).

(* n[]: n/4 PUBLIC-BUT-UNPINNED byte-expanded word entries at offsets
   52+n, 52+n+4, ..., 52+2n-4 -- tried as PVExist per §4, not PVConst. *)
Definition loop2_n_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((52 + n + 4 * N.of_nat i)%N, true, PVExist))
      (seq 0 (Nat.div (N.to_nat n) 4)).

Definition loop2_byte_specs_rel (n : N) : list mem_spec_rel :=
  loop2_k_specs_rel n ++ loop2_n_specs_rel n.

(* bound = 52 + 2n: the last declared byte (n[N-1]) sits at offset 52+2n-1,
   so the width-1 access bound needs unsigned p + 52 + 2n <= lenAddr. *)
Definition loop2_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia (loop2_reg_specs_rel n) [] (loop2_byte_specs_rel n)
    loop2_instrs [] (52 + n + n)%N
    (pcOutOfInstrs_exitCond ia loop2_instrs)
    (Nat.add (Nat.mul 13 (N.to_nat n)) 20).
