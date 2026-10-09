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
(* Example/Cmovznz4.v — HACL* cmovznz4 (clang -O2 RV32I), all variants.     *)
(*                                                                           *)
(* The instruction list and reg/mem spec definitions below are               *)
(* STATEMENT-RELEVANT: the noninterference theorems in Results.v reference   *)
(* them by name.  The contracts and valid_* VC proofs are not.               *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

    (* ------------------------------------------------------------------ *)
    (* cmovznz4 (HACL*'s FStar_UInt64_eq_mask-based conditional move),      *)
    (* compiled to RV32I by clang -O2 (godbolt, -march=rv32i -mabi=ilp32). *)
    (* Straight-line program, no branches, no loops. Registers per the     *)
    (* RISC-V calling convention: A0 = cin, A1 = x, A2 = y, A3 = r;         *)
    (* A4-A7, T0, T1 are compiler-chosen scratch registers.                *)
    (*                                                                       *)
    (* This concrete contract fixes A1/A2/A3 to concrete addresses right     *)
    (* after the instruction region (116/132/148), exactly like              *)
    (* countdown_mem's loop counter at a fixed address -- this fits the      *)
    (* gen_contract/gen_mem_asn (literal-address) machinery. The start       *)
    (* address is no longer hardcoded: cmovznz4_noninterferent_param proves  *)
    (* noninterference for an ARBITRARY base, with base-relative x/y/r       *)
    (* pointers (see cmovznz4_*_specs_rel), and this base-0 contract is a     *)
    (* corollary of it.                                                       *)
    (*                                                                       *)
    (* Trailing `ret` (jalr x0, ra, 0) is deliberately NOT included: its     *)
    (* target is the symbolic link register `ra`, and the executor's table *)
    (* lookup needs a pc that matches a known table key at every step, so  *)
    (* it cannot step through a jump to an unconstrained destination. The  *)
    (* program instead exits at the fall-through, one past the last real   *)
    (* instruction -- the single exit address every generated contract has *)
    (* (PLAN-exit-targets.md).                                             *)
    (* ------------------------------------------------------------------ *)
    Definition cmovznz4_instrs : list AST :=
      [ RTYPE A0 X0 A4 RISCV_SUB               (* neg     a4, a0 *)
      ; RTYPE A4 A0 A0 RISCV_OR                (* or      a0, a0, a4 *)
      ; SHIFTIOP (bv.of_Z 31) A0 A4 RISCV_SRAI (* srai    a4, a0, 31 *)
      ; LOAD (bv.of_Z 0) A2 A5 false WORD      (* lw      a5, 0(a2) *)
      ; SHIFTIOP (bv.of_Z 31) A0 A0 RISCV_SRLI (* srli    a0, a0, 31 *)
      ; LOAD (bv.of_Z 0) A1 A6 false WORD      (* lw      a6, 0(a1) *)
      ; ITYPE (bv.of_Z (-1)) A0 A0 RISCV_ADDI  (* addi    a0, a0, -1 *)
      ; RTYPE A4 A5 A7 RISCV_AND               (* and     a7, a5, a4 *)
      ; LOAD (bv.of_Z 4) A2 T0 false WORD      (* lw      t0, 4(a2) *)
      ; RTYPE A0 A6 A5 RISCV_AND               (* and     a5, a6, a0 *)
      ; LOAD (bv.of_Z 4) A1 A6 false WORD      (* lw      a6, 4(a1) *)
      ; RTYPE A7 A5 A7 RISCV_OR                (* or      a7, a5, a7 *)
      ; RTYPE A4 T0 T0 RISCV_AND               (* and     t0, t0, a4 *)
      ; LOAD (bv.of_Z 8) A2 T1 false WORD      (* lw      t1, 8(a2) *)
      ; RTYPE A0 A6 A5 RISCV_AND               (* and     a5, a6, a0 *)
      ; RTYPE T0 A5 A6 RISCV_OR                (* or      a6, a5, t0 *)
      ; LOAD (bv.of_Z 8) A1 A5 false WORD      (* lw      a5, 8(a1) *)
      ; RTYPE A4 T1 T0 RISCV_AND               (* and     t0, t1, a4 *)
      ; LOAD (bv.of_Z 12) A2 A2 false WORD     (* lw      a2, 12(a2) *)
      ; LOAD (bv.of_Z 12) A1 A1 false WORD     (* lw      a1, 12(a1) *)
      ; RTYPE A0 A5 A5 RISCV_AND               (* and     a5, a5, a0 *)
      ; RTYPE T0 A5 A5 RISCV_OR                (* or      a5, a5, t0 *)
      ; RTYPE A4 A2 A2 RISCV_AND               (* and     a2, a2, a4 *)
      ; RTYPE A1 A0 A0 RISCV_AND               (* and     a0, a0, a1 *)
      ; RTYPE A2 A0 A0 RISCV_OR                (* or      a0, a0, a2 *)
      ; STORE (bv.of_Z 0) A7 A3 WORD           (* sw      a7, 0(a3) *)
      ; STORE (bv.of_Z 4) A6 A3 WORD           (* sw      a6, 4(a3) *)
      ; STORE (bv.of_Z 8) A5 A3 WORD           (* sw      a5, 8(a3) *)
      ; STORE (bv.of_Z 12) A0 A3 WORD          (* sw      a0, 12(a3) *)
      ].

    (* All of cin (A0), x and y are secret here: this is the genuine
       LOAD-of-secret case that method-Y unlocks. The loaded secret words
       (x[i], y[i]) flow through fun_extend_value's union match
       [KMemValue (pat_var "result")], which takes the same branch in both
       worlds (the KMemValue constructor is statically determined), so the
       match succeeds WITHOUT secLeak on the loaded word. Non-interference
       still holds because the addresses touched (fixed 116/132/148 bases)
       are data-independent -- only the values are secret. r[0..3] is
       private as before. x[0..3]/y[0..3]/r[0..3] all private. *)
    (* Step 5 (init_addr parameterization): the SAME cmovznz4 program, loaded at
       a genuinely nonzero, 4-aligned start address instead of 0. cmovznz4 is a
       straight-line program (no jumps/branches) and every LOAD/STORE is
       register-relative, not pc-relative, so the instruction stream itself
       (cmovznz4_instrs) needs no change at all -- only the register-init
       values and data addresses (previously hardcoded right after the
       instruction region at 0+116/132/148) shift by cmovznz4_start. *)
    Definition cmovznz4_start : N := 256%N.

    (* ===== Phase 4.2: base-parametric cmovznz4 VC ========================
       This supersedes BOTH removed concrete-base contract/VC pairs
       (cmovznz4_cfg_contract / valid_cmovznz4_cfg_contract at base 0, and
       cmovznz4_cfg_contract_at_start / valid_cmovznz4_cfg_contract_at_start at
       base 256): cmovznz4_noninterferent and cmovznz4_noninterferent_at_start
       are both corollaries of the parametric theorem, so re-proving those two
       VCs cost 31 s of the file's compile time for nothing.
       Parametric contract (Σ = ["p"]) built with gen_contract_rel_classed
       (the classed-existential builder: the 12 data words become ONE grouped
       existential rather than 12 -- PLAN-classed-existentials.md) from the
       base-relative specs below, so the data pointers A1/A2/A3 hold
       p+116 / p+132 / p+148 and the 12 data words live at p+116 .. p+160
       (bop.bvadd terms), NOT constants.  peval DOES fold a
       load address (p+132)+4 into p+136 to match the mem chunk, so solve_vc
       reduces the whole 29-instruction program to a fixed family of address
       bounds goals.  The tail below closes them uniformly (offset-agnostic):
       every base/instr RelVal is SyncVal via its secLeak; the pc-fetch and
       lower bounds fall to lia against the precondition base bound; the
       bvadd-wrapped load/store upper bounds go through bv.bin_add_small
       (no-overflow) then lia + an exp2 transit.  See memory
       project-cfgver-symbolic-base-poc. *)
    Definition cmovznz4_reg_specs_rel : list reg_spec_rel :=
      [(A0, Secret);
       (A1, Known (PVBaseOff 116));   (* x base *)
       (A2, Known (PVBaseOff 132));   (* y base *)
       (A3, Known (PVBaseOff 148));   (* r base *)
       (A4, Secret); (A5, Secret); (A6, Secret);
       (A7, Secret); (T0, Secret); (T1, Secret)].

    Definition cmovznz4_mem_specs_rel : list mem_spec_rel :=
      [(116%N, Secret); (120%N, Secret);
       (124%N, Secret); (128%N, Secret);
       (132%N, Secret); (136%N, Secret);
       (140%N, Secret); (144%N, Secret);
       (148%N, Secret); (152%N, Secret);
       (156%N, Secret); (160%N, Secret)].

    (* Base bound 164 = 160 (last data offset, r[3]) + 4 (word). *)
    Definition cmovznz4_cfg_contract_param : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_rel_classed cmovznz4_reg_specs_rel cmovznz4_mem_specs_rel
        cmovznz4_instrs 164 35.

    (* TRUSTED-SURFACE ANCHOR (AnnotInstr migration, PLAN-annotinstr.md).
       The end theorems in Cmovznz4Result.v state noninterferent_strong over
       `cmovznz4_instrs` while the EndToEnd bridges now conclude over
       `strip instrs`.  This lemma is what makes those the SAME statement, and
       it must close by `reflexivity` — if it ever needs more, the migration
       has changed what is being proved and must stop.  An auditor checks one
       thing: that `strip` is a plain projection. *)
    Lemma strip_id_cmovznz4 : strip cmovznz4_instrs = cmovznz4_instrs.
    Proof. reflexivity. Qed.

    Lemma valid_cmovznz4_cfg_contract_param :
      cfg_vc cmovznz4_cfg_contract_param (cfg_instrs cmovznz4_cfg_contract_param).
    Proof. solve_param_vc. Qed.
    (* ===== end Phase 4.2 ===== *)
