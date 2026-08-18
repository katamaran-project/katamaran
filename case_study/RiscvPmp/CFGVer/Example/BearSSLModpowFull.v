(*==========================================================================*)
(* Example/BearSSLModpowFull.v — BearSSL `modpow_opt` window lookup, the     *)
(* COMPLETE nested loop (not just the loop body).                           *)
(*                                                                           *)
(* Companion to Example/BearSSLModpow.v, which verifies the 5-instruction    *)
(* inner-loop BODY in isolation (registers only, the granularity of the      *)
(* paper's own minimal reproducer).  This file verifies the whole function:  *)
(* both loops, the real memory traffic, and the loop control flow.           *)
(*                                                                           *)
(* The instruction list and reg/mem spec definitions below are               *)
(* STATEMENT-RELEVANT: the noninterference theorem in                        *)
(* BearSSLModpowFullResult.v references them by name.  The contract and      *)
(* valid_* VC proof are not.                                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------ *)
(* ORIGINAL C — BearSSL src/int/i31_modpow2.c (commit 79c060e), inside       *)
(* `br_i31_modpow_opt`, verbatim loop structure:                            *)
(*                                                                           *)
(*     for (u = 1; u < ((uint32_t)1 << k); u ++) {                           *)
(*         uint32_t mask = -EQ(u, bits);                                     *)
(*         for (v = 1; v < mwlen; v ++) {                                    *)
(*             t2[v] |= mask & base[v];                                      *)
(*         }                                                                 *)
(*         base += mwlen;                                                    *)
(*     }                                                                     *)
(*                                                                           *)
(* with EQ/NOT from src/inner.h (bodies quoted in BearSSLMuladd.v).          *)
(* `bits` is the SECRET exponent window; `u` is the public loop index.       *)
(*                                                                           *)
(* WHY THE BOUNDS ARE RUNTIME ARGUMENTS.  In the real code `mwlen` and       *)
(* `1 << k` are runtime values, so the compiled function contains genuine    *)
(* nested loops.  Compiling with the sizes as compile-time constants makes   *)
(* clang fully unroll, which would defeat the point of this file — the       *)
(* loop control flow is exactly what BearSSLModpow.v does NOT cover.  So the *)
(* C below takes num_win and mwlen as parameters, matching the original, and *)
(* the CONTRACT pins them to concrete public values (4 and 4).  The verified *)
(* binary therefore has the real loop structure; only the trip counts are    *)
(* fixed, and they are public — the paper's finding is about `bits`.         *)
(*                                                                           *)
(*     void modpow_win(uint32_t *t2, const uint32_t *base, uint32_t bits,    *)
(*                     uint32_t num_win, uint32_t mwlen) { ... }             *)
(*                                                                           *)
(* clang 18.1.3 --target=riscv32 -march=rv32i -mabi=ilp32 -O2 gives the      *)
(* 28-instruction listing below (translated with tools/asm_to_ast.py; the    *)
(* trailing `ret` dropped as in every other example).  Every branch is on a  *)
(* PUBLIC value — num_win, mwlen, or a loop counter derived from them.  The  *)
(* secret `bits` reaches only the `xor`/`snez`/`addi` mask chain at          *)
(* instructions 12-14, i.e. it is used as a VALUE and never as a branch      *)
(* condition.  (That `snez` is a SLTU on secret-derived data, which is what  *)
(* the fun_bool_to_bits/bop.bvcons fix unlocked — see BearSSLMuladd.v.)      *)
(*                                                                           *)
(* Register assignment per the RISC-V calling convention: A0 = t2,           *)
(* A1 = base, A2 = bits, A3 = num_win, A4 = mwlen; A5/A6/A7 and T0-T6 are    *)
(* compiler scratch.  Label positions: .LBB0_2 = instr 8 (outer latch),      *)
(* .LBB0_3 = instr 11 (outer header), .LBB0_5 = instr 18 (inner header),     *)
(* .LBB0_6 = instr 28 = one past the end, so both exits fall out of the      *)
(* instruction range and pcOutOfInstrs_exitCond covers them with no          *)
(* extra_exit_offs.                                                          *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition modpow_win_full_instrs : list AST :=
  [ ITYPE (bv.of_Z 2) X0 A5 RISCV_ADDI      (* li    a5, 2 *)
  ; BTYPE (bv.of_Z 108) A5 A3 RISCV_BLTU    (* bltu  a3, a5, .LBB0_6 *)
  ; ITYPE (bv.of_Z (-1)) A4 A6 RISCV_ADDI   (* addi  a6, a4, -1 *)
  ; ITYPE (bv.of_Z 4) A0 A0 RISCV_ADDI      (* addi  a0, a0, 4 *)
  ; ITYPE (bv.of_Z 4) A1 A1 RISCV_ADDI      (* addi  a1, a1, 4 *)
  ; SHIFTIOP (bv.of_Z 2) A4 A7 RISCV_SLLI   (* slli  a7, a4, 2 *)
  ; ITYPE (bv.of_Z 1) X0 T0 RISCV_ADDI      (* li    t0, 1 *)
  ; RISCV_JAL (bv.of_Z 16) X0               (* j     .LBB0_3 *)
  ; ITYPE (bv.of_Z 1) T0 T0 RISCV_ADDI      (* addi  t0, t0, 1     .LBB0_2 *)
  ; RTYPE A7 A1 A1 RISCV_ADD                (* add   a1, a1, a7 *)
  ; BTYPE (bv.of_Z 72) A3 T0 RISCV_BEQ      (* beq   t0, a3, .LBB0_6 *)
  ; BTYPE (bv.of_Z (-12)) A5 A4 RISCV_BLTU  (* bltu  a4, a5, .LBB0_2  .LBB0_3 *)
  ; RTYPE A2 T0 T1 RISCV_XOR                (* xor   t1, t0, a2 *)
  ; RTYPE T1 X0 T1 RISCV_SLTU               (* snez  t1, t1 *)
  ; ITYPE (bv.of_Z (-1)) T1 T1 RISCV_ADDI   (* addi  t1, t1, -1 *)
  ; ITYPE (bv.of_Z 0) A1 T2 RISCV_ADDI      (* mv    t2, a1 *)
  ; ITYPE (bv.of_Z 0) A0 T3 RISCV_ADDI      (* mv    t3, a0 *)
  ; ITYPE (bv.of_Z 0) A6 T4 RISCV_ADDI      (* mv    t4, a6 *)
  ; LOAD (bv.of_Z 0) T2 T5 false WORD       (* lw    t5, 0(t2)     .LBB0_5 *)
  ; LOAD (bv.of_Z 0) T3 T6 false WORD       (* lw    t6, 0(t3) *)
  ; RTYPE T5 T1 T5 RISCV_AND                (* and   t5, t1, t5 *)
  ; RTYPE T5 T6 T5 RISCV_OR                 (* or    t5, t6, t5 *)
  ; STORE (bv.of_Z 0) T5 T3 WORD            (* sw    t5, 0(t3) *)
  ; ITYPE (bv.of_Z (-1)) T4 T4 RISCV_ADDI   (* addi  t4, t4, -1 *)
  ; ITYPE (bv.of_Z 4) T3 T3 RISCV_ADDI      (* addi  t3, t3, 4 *)
  ; ITYPE (bv.of_Z 4) T2 T2 RISCV_ADDI      (* addi  t2, t2, 4 *)
  ; BTYPE (bv.of_Z (-32)) X0 T4 RISCV_BNE   (* bnez  t4, .LBB0_5 *)
  ; RISCV_JAL (bv.of_Z (-76)) X0            (* j     .LBB0_2 *)
  ].

(* ------------------------------------------------------------------------ *)
(* DATA LAYOUT.  28 instructions = 112 bytes of code, so the arrays start at *)
(* base+112, contiguous right after the code (the countdown_mem pattern —    *)
(* genuinely caller-chosen pointers are still an open TODO).                 *)
(*                                                                           *)
(*   t2   : base+112 .. base+124   (4 words; t2[0] is the i31 length header, *)
(*                                  untouched — the loop starts at v=1)      *)
(*   base : base+128 .. base+172   (3 windows x 4 words, same header skip)   *)
(*                                                                           *)
(* A0 = &t2[0] = p+112 and A1 = &base[0] = p+128; instructions 3-4 bump both *)
(* by 4 to reach index 1.  The inner loop touches t2[1..3] = p+116/120/124   *)
(* and, per outer iteration u = 1/2/3, base[1..3] of window u-1 at           *)
(* p+132/136/140, p+148/152/156, p+164/168/172 (A1 advances by mwlen*4 = 16  *)
(* each outer iteration, via A7).  All 16 words are declared: the caller     *)
(* really does own both whole arrays, including the two header words the     *)
(* loop skips.  Bound = 172 (last data offset) + 4 (word) = 176.             *)
(*                                                                           *)
(* PUBLICNESS.  Everything the paper cares about is secret: the exponent     *)
(* window A2 (bits), the accumulator t2[], and the candidate table base[].   *)
(* Public: the two loop bounds A3/A4, pinned to 4 — these are the trip       *)
(* counts, which are not secret in BearSSL (they come from the key size and  *)
(* the window width).  They must be public: they control branches, and a     *)
(* branch condition on a NonSyncVal is False by construction.                *)
(* ------------------------------------------------------------------------ *)

Definition modpow_win_full_reg_specs_rel : list reg_spec_rel :=
  [(A0, false, PVBaseOff 112);            (* &t2[0]   *)
   (A1, false, PVBaseOff 128);            (* &base[0] *)
   (A2, false, PVExist);                  (* bits — SECRET *)
   (A3, true, PVConst (bv.of_N 4));       (* num_win = 1 << k, public *)
   (A4, true, PVConst (bv.of_N 4));       (* mwlen, public *)
   (A5, false, PVExist); (A6, false, PVExist); (A7, false, PVExist);
   (T0, false, PVExist); (T1, false, PVExist); (T2, false, PVExist);
   (T3, false, PVExist); (T4, false, PVExist); (T5, false, PVExist);
   (T6, false, PVExist)].

Definition modpow_win_full_mem_specs_rel : list mem_spec_rel :=
  [(112%N, false, PVExist); (116%N, false, PVExist);
   (120%N, false, PVExist); (124%N, false, PVExist);
   (128%N, false, PVExist); (132%N, false, PVExist);
   (136%N, false, PVExist); (140%N, false, PVExist);
   (144%N, false, PVExist); (148%N, false, PVExist);
   (152%N, false, PVExist); (156%N, false, PVExist);
   (160%N, false, PVExist); (164%N, false, PVExist);
   (168%N, false, PVExist); (172%N, false, PVExist)].

(* Executed steps at num_win = mwlen = 4: 8 (prologue) + 3 outer iterations x
   38 (1 header + 6 setup + 3 x 9 inner + 1 j + 3 latch) = 122.  Fuel 150
   leaves slack — tight fuel surfaces as a bare False deep in the VC. *)
Definition modpow_win_full_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_classed ia modpow_win_full_reg_specs_rel modpow_win_full_mem_specs_rel
    modpow_win_full_instrs [] 176
    (pcOutOfInstrs_exitCond ia modpow_win_full_instrs) 150.

Lemma valid_modpow_win_full_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (modpow_win_full_cfg_contract_param ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
