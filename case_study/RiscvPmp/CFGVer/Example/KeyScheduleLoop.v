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


(* ========================================================================= *)
(* Example/KeyScheduleLoop.v — small-N (N=2) feasibility spike toward the    *)
(* full Botan GHASH::key_schedule loop (src/lib/utils/ghash/ghash.cpp,       *)
(* current master, commit 77cc8fe6):                                        *)
(*   for (i = 0; i != 2; ++i)                                                *)
(*     for (j = 0; j != 64; ++j) {                                           *)
(*       m_HM[4*j+2*i] = H[0]; m_HM[4*j+2*i+1] = H[1];                       *)
(*       const uint64_t carry = CT::Mask<uint64_t>::expand(H[1] & 1)          *)
(*                                 .if_set_return(R);                        *)
(*       H[1] = (H[1] >> 1) | (H[0] << 63);                                  *)
(*       H[0] = (H[0] >> 1) ^ carry;                                         *)
(*     }                                                                     *)
(* i.e. 128 iterations of: masking step (same as Example/Precompute.v) +    *)
(* store the evolving H into an advancing table slot, wrapped in a          *)
(* backward-branching loop. This file tests the genuinely NEW machinery     *)
(* (per-iteration table write at an advancing address, inside a backward    *)
(* branch) at a small trip count (N=2) BEFORE attempting the real N=128:    *)
(* deliberately reuses precompute's 32-bit-H simplification (NOT the real   *)
(* uint64_t pair) since the real H is a register PAIR whose masking step    *)
(* needs a 64-bit "0 - x" negation of a single secret bit -- i.e. the SAME  *)
(* sltu-borrow-chain gap already flagged as open in TODO.md ("Botan         *)
(* CT::Mask / 64-bit-subtraction gap"). This spike is orthogonal to that    *)
(* gap: it is purely about the loop/table-write shape. Hand-authored        *)
(* directly (like Countdown.v), not compiled -- clang would fully unroll a  *)
(* 2-trip loop, defeating the point of exercising a genuine backward        *)
(* branch.                                                                  *)
(*                                                                           *)
(* The instruction list and reg/mem spec definitions below are               *)
(* STATEMENT-RELEVANT: the noninterference theorems in Results.v reference   *)
(* them by name.  The contract and valid_* VC proofs are not.                *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

    (* -52 in 13-bit two's complement: branch immediates are relative to the
       BNE instruction's OWN address (pc 52, the 14th instruction), not the
       total code length (56) -- jumps back to pc 0, the start of the loop
       body. *)
    Definition key_schedule_loop2_back_offset : bv 13 := bv.of_N 8140.

    (* Loop body (14 instructions):
       [1-10] precompute's masking step, verbatim (updates H = A0):
              H = (H >> 1) ^ (0 - (H & 1))   -- 32-bit analogue of the real
              64-bit CT::Mask-based carry computation.
       [11]   sw   a0, 0(a3)    -- table[i] := H
       [12]   addi a3, a3, 4    -- table pointer += 1 word
       [13]   addi a4, a4, -1   -- loop counter -= 1
       [14]   bne  a4, x0, back -- loop while counter != 0
       A0 = H (secret, evolves); A1/A2 = masking scratch (private); A3 =
       table write pointer (public, base-relative); A4 = loop counter
       (public, pinned to N=2 -- the trip count itself is not secret). *)
    Definition key_schedule_loop2_instrs : list AST :=
      [ ITYPE (bv.of_Z 1) A0 A1 RISCV_ANDI      (* andi    a1, a0, 1 *)
      ; ITYPE (bv.of_Z (-1)) A1 A2 RISCV_XORI   (* not     a2, a1 *)
      ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI   (* addi    a1, a1, -1 *)
      ; RTYPE A2 A1 A1 RISCV_AND                (* and     a1, a1, a2 *)
      ; SHIFTIOP (bv.of_Z 31) A1 A1 RISCV_SRLI  (* srli    a1, a1, 31 *)
      ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI   (* addi    a1, a1, -1 *)
      ; UTYPE (bv.of_Z 921600) A2 RISCV_LUI     (* lui     a2, 921600 *)
      ; RTYPE A2 A1 A1 RISCV_AND                (* and     a1, a1, a2 *)
      ; SHIFTIOP (bv.of_Z 1) A0 A0 RISCV_SRLI   (* srli    a0, a0, 1 *)
      ; RTYPE A0 A1 A0 RISCV_XOR                (* xor     a0, a1, a0 *)
      ; STORE (bv.of_Z 0) A0 A3 WORD             (* sw      a0, 0(a3) *)
      ; ITYPE (bv.of_Z 4) A3 A3 RISCV_ADDI       (* addi    a3, a3, 4 *)
      ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI    (* addi    a4, a4, -1 *)
      ; BNE A4 X0 key_schedule_loop2_back_offset (* bne     a4, x0, back *)
      ].

    Definition key_schedule_loop2_exitCond : bv xlenbits -> bool :=
      pcOutOfInstrs_exitCond init_addr key_schedule_loop2_instrs.

    (* Table lives right after the 14*4 = 56-byte code region, matching the
       countdown_mem/cmovznz4 "data hardcoded contiguously after the code"
       pattern. *)
    Definition key_schedule_loop2_reg_specs : list reg_spec :=
      [(A0, false, None); (A1, false, None); (A2, false, None);
       (A3, false, Some (bv.of_N 56));
       (A4, true, Some (bv.of_N 2))].

    (* Table words are private (their value is derived from the secret H,
       and may legitimately differ between worlds), addresses are fixed. *)
    Definition key_schedule_loop2_mem_specs : list mem_full_spec :=
      [(bv.of_N 56, false, None); (bv.of_N 60, false, None)].

    (* Parametric-base version: the table is base-relative (p+56/p+60), so
       this needs gen_contract_rel (like cmovznz4_param/countdown_mem_param),
       not the memory-less gen_contract_param.
       Supersedes the removed concrete-base pair key_schedule_loop2_cfg_contract
       / valid_key_schedule_loop2_cfg_contract (see MvSwap.v for the
       rationale). *)
    Definition key_schedule_loop2_reg_specs_rel : list reg_spec_rel :=
      [(A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist);
       (A3, false, PVBaseOff 56);
       (A4, true, PVConst (bv.of_N 2))].

    Definition key_schedule_loop2_mem_specs_rel : list mem_spec_rel :=
      [(56%N, false, PVExist); (60%N, false, PVExist)].

    Definition key_schedule_loop2_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_rel ia key_schedule_loop2_reg_specs_rel key_schedule_loop2_mem_specs_rel
        key_schedule_loop2_instrs [] 64
        (pcOutOfInstrs_exitCond ia key_schedule_loop2_instrs) 40.

    Lemma valid_key_schedule_loop2_cfg_contract_param (ia : N) :
      ValidCFGVerifierContract (key_schedule_loop2_cfg_contract_param ia).
    Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
