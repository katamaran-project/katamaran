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
(* Example/Countdown.v — register countdown loop + memory countdown loop.   *)
(*                                                                           *)
(* The instruction list and reg/mem spec definitions below are               *)
(* STATEMENT-RELEVANT: the noninterference theorems in Results.v reference   *)
(* them by name.  The contracts and valid_* VC proofs are not.               *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

    (* -4 in 13-bit two's complement: branches jump back 4 bytes (one instruction) *)
    Definition back_offset : bv 13 := bv.of_N 8188.

    (* -1 in 12-bit two's complement: ADDI immediate for decrement *)
    Definition neg_one_12 : bv 12 := bv.of_N 4095.

    (* Countdown program: X1 starts at 2 and counts down to 0.
       addr 0: ADDI X1 X1 (-1)  -- decrement X1
       addr 4: BNE X1 X0 (-4)   -- if X1 != 0, jump back to addr 0
       addr 8: exit (exitCond satisfied)
       Concrete execution: X1=2→1, BNE taken; X1=1→0, BNE not taken; exit.
       Backward branch actually fires, demonstrating CFGVer handles loops. *)
    Definition countdown_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 8).

    (* ===== Phase 4.2: base-parametric countdown VC (backward branch) =========
       Supersedes the removed concrete-base pair countdown_cfg_contract /
       valid_countdown_cfg_contract (see MvSwap.v for the rationale).
       countdown_exitCond is definitionally `pcOutOfInstrs_exitCond 0 instrs`
       (both reduce to `fun v => bv.ugeb v (bv.of_N 8)`), so the parametric
       contract reuses pcOutOfInstrs_exitCond directly -- no hand-rolled
       exitCond needed, matching the cmovznz4/set_X2 style. This was the
       untested case flagged before starting: the BNE back_offset (-4 in
       13-bit two's complement) jumps BACKWARD to the first instruction. The
       open question was whether the term-table executor's constant folding
       (peval_bvadd) still collapses the backward jump's next-pc term down to
       the canonical offset-0 key `p` the same way it collapses forward jumps
       to `c ⊕ p` -- CONFIRMED: the existing offset-agnostic tail closes the
       VC with zero changes. *)
    Definition countdown_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_param ia [(X1, true, Some (bv.of_N 2))] []
        [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset] []
        (pcOutOfInstrs_exitCond ia [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]) 5.

    Lemma valid_countdown_cfg_contract_param (ia : N) :
      ValidCFGVerifierContract (countdown_cfg_contract_param ia).
    Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
    (* ===== end Phase 4.2 spike ===== *)


    (* Memory countdown: 4 instructions + a data word at address 16.
       addr  0: LOAD  imm=16 rs1=X2 rd=X1  -- X1 := mem[X2+16]
       addr  4: ADDI  X1 X1 (-1)            -- X1 := X1 - 1
       addr  8: STORE imm=16 rs2=X1 rs1=X2  -- mem[X2+16] := X1
       addr 12: BNE   X1 X0 (-12)           -- if X1 ≠ 0, jump back to addr 0
       Data:    mem[X2+16] = 2 initially.
       Two iterations: 2→1 (branch), 1→0 (fall-through); exit at pc=16.

       X2 is a dedicated base-holding register (pre-initialized to the
       program's own load address, see countdown_mem_reg_specs_rel's
       PVBaseOff 0 below), NOT X0 (RISC-V's architecturally hardwired-zero
       register, per Machine.v's rX/wX special-casing of index 0). The
       original version used X0 + imm=16, giving an ABSOLUTE address 16
       regardless of where the code is loaded -- that cannot be made
       base-relative without changing which register the address is
       computed from, since X0 can only ever hold 0. Using X2 instead makes
       the counter word live at base+16 (contiguous right after the 4
       instructions, matching every other example's data layout), enabling
       a genuine parametric-base version. At base 0, X2 = 0, so this is
       behaviorally identical to the old X0-based program. *)
    Definition back_12_offset : bv 13 := bv.of_N 8180.

    Definition countdown_mem_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 16).

    Definition countdown_mem_instrs : list AST :=
      [ LOAD (bv.of_N 16) X2 X1 false WORD
      ; ADDI X1 X1 neg_one_12
      ; STORE (bv.of_N 16) X1 X2 WORD
      ; BNE X1 X0 back_12_offset ].

    (* ===== Phase 4.2: base-parametric countdown_mem VC ======================
       Supersedes the removed concrete-base pair countdown_mem_cfg_contract /
       valid_countdown_mem_cfg_contract (see MvSwap.v for the rationale).
       X2 holds the base (PVBaseOff 0 = p+0 = p), so the counter word's
       address (via LOAD/STORE off X2, imm 16) is genuinely p+16 --
       base-RELATIVE, needing gen_contract_rel_classed/mem_spec_rel like
       cmovznz4's
       data pointers, not the constant-only gen_contract_param. Bound = 20
       (last accessed byte offset 16 + 4 = the data word's own width). *)
    Definition countdown_mem_reg_specs_rel : list reg_spec_rel :=
      [(X1, false, PVExist); (X2, false, PVBaseOff 0)].

    Definition countdown_mem_mem_specs_rel : list mem_spec_rel :=
      [(16%N, true, PVConst (bv.of_N 2))].

    Definition countdown_mem_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_rel_classed ia countdown_mem_reg_specs_rel countdown_mem_mem_specs_rel
        countdown_mem_instrs [] 20
        (pcOutOfInstrs_exitCond ia countdown_mem_instrs) 10.

    Lemma valid_countdown_mem_cfg_contract_param (ia : N) :
      ValidCFGVerifierContract (countdown_mem_cfg_contract_param ia).
    Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
    (* ===== end Phase 4.2 ===== *)
