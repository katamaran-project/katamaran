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
(* Example/Precompute.v — 32-bit-word analogue of Botan's GHASH::key_schedule*)
(* masking step (src/lib/utils/ghash/ghash.cpp, current CT::Mask-based       *)
(* master), compiled to RV32I by clang -O2 (-march=rv32i -mabi=ilp32).       *)
(*                                                                           *)
(* The instruction list and reg spec definitions below are                   *)
(* STATEMENT-RELEVANT: the noninterference theorems in Results.v reference   *)
(* them by name.  The contract and valid_* VC proofs are not.                *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract.

From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import asn.notations.
Import TermNotations.

    (* ------------------------------------------------------------------ *)
    (* 32-bit-word analogue of Botan's GHASH::key_schedule inner masking    *)
    (* step (src/lib/utils/ghash/ghash.cpp lines ~149-152, current master,  *)
    (* commit 77cc8fe6):                                                    *)
    (*   const uint64_t carry = CT::Mask<uint64_t>::expand(H1 & 1)           *)
    (*                            .if_set_return(R);                        *)
    (*   H0 = (H0 >> 1) ^ carry;                                             *)
    (* standalone-compiled by inlining CT::Mask/ct_is_zero/value_barrier     *)
    (* (Botan src/lib/utils/{ct_utils.h,bit_ops.h,value_barrier.h}) into a   *)
    (* `precompute32(H)` function -- see the fix commit 53b0cfde58 ("Add     *)
    (* more value barriers to avoid compiler induced side channels", which  *)
    (* cites this exact case study's arXiv preprint). The real Botan code   *)
    (* operates on uint64_t (H0/H1 register PAIRS), whose "x - 1" needs a    *)
    (* borrow-detecting `sltu` when lowered to RV32I (no carry flag) -- and  *)
    (* that `sltu`'s condition (secret-derived) is a case CFGVer's current   *)
    (* relop/secLeak model cannot yet clear (see project TODO). Scaling H    *)
    (* down to a native uint32_t sidesteps that: `x - 1` is then a single    *)
    (* RV32I subtraction with no borrow-chain comparison at all. Compiled    *)
    (* with clang 15.0.0 (the SAME compiler version that still miscompiles   *)
    (* the old raw-multiply `R * (H1 & 1)` form into a `beqz` branch) at     *)
    (* -O2 -march=rv32i -mabi=ilp32: branch-free AND sltu-free, register-to- *)
    (* register only (A0 = H, also the result; A1/A2 compiler scratch). No   *)
    (* LOAD/STORE at all, so there is no data memory to model. *)
    (* ------------------------------------------------------------------ *)
    Definition precompute_instrs : list AST :=
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
      ].

    (* H (A0) is the secret GHASH key material; A1/A2 (compiler scratch)
       only ever carry values derived from the secret, never addresses
       (there is no memory access anywhere in this program), so all three
       stay private/independent per world. *)
    Definition precompute_reg_specs : list reg_spec :=
      [(A0, false, None); (A1, false, None); (A2, false, None)].

    Definition precompute_cfg_contract : CFGVerifierContract :=
      gen_contract init_addr precompute_reg_specs [] precompute_instrs []
        (pcOutOfInstrs_exitCond init_addr precompute_instrs) 16.

    Lemma valid_precompute_cfg_contract : ValidCFGVerifierContract precompute_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

    (* Parametric-base headline (∀ init_addr), same shape as set_X2_to_42_param:
       no memory in this program, so gen_contract_param (not _rel) suffices --
       there is nothing base-relative to concretize. *)
    Definition precompute_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_param ia precompute_reg_specs [] precompute_instrs []
        (pcOutOfInstrs_exitCond ia precompute_instrs) 16.

    Lemma valid_precompute_cfg_contract_param (ia : N) :
      ValidCFGVerifierContract (precompute_cfg_contract_param ia).
    Proof.
      intros. vm_compute. solve_vc.
      all: repeat match goal with
           | Hs : RiscvPmpSignature.secLeak ?x |- _ =>
               is_var x; destruct x as [?|? ?]; [ | destruct Hs ]
           end.
      all: cbn in *; unfold bv.unsigned in *.
      all: try rewrite bv.bin_add_small.
      all: repeat match goal with
           | |- context [bv.bin ?b] =>
               assert_fails (is_var b);
               let vv := eval vm_compute in (bv.bin b) in change (bv.bin b) with vv
           end.
      all: try lia.
      all: apply N.le_lt_trans with (m := 1024%N); [lia | vm_compute; reflexivity].
    Qed.
