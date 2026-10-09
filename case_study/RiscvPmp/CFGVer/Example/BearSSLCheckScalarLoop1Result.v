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
(* Example/BearSSLCheckScalarLoop1Result.v — end-to-end noninterference for   *)
(* BearSSL P-256 `check_scalar` loop 1 (klen = 32, byte-granular memory).     *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE — see BearSSLMuladdResult.v for the rationale   *)
(* behind the Example/<Prog>Result.v split.  Deliberately separate from      *)
(* Example/BearSSLCheckScalarLoop1.v so the Adequacy->EndToEnd chain builds  *)
(* in parallel with the examples rather than ahead of all of them.          *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.BearSSLCheckScalarLoop1.

(* The first byte-granular (lbu) example proved end-to-end in the repo,
   universal in the base address, from the single symbolic-base VC
   valid_loop1_cfg_contract_param via the byte-granular base-relative bridge
   gen_contract_noninterferent_rel_bytes_simple.  Bound 48 = last declared
   byte's offset (47) + 1, rounded up to the base bound the contract states. *)
(* code: init_addr .. init_addr+15 (4 instructions); k follows. *)
Definition check_scalar_loop1_data : list region :=
  [ Bytes 32 Secret ].    (* k[0..31] at init_addr+16 *)
Definition check_scalar_loop1_regs (ia : N) : list reg_spec :=
  [ (A0, Known (bv.of_N (ia + 16)));            (* &k[0]  *)
    (A1, Known (bv.of_N (ia + 48)));            (* &k[32] *)
    (A2, Known (bv.of_N 0));                    (* accumulator *)
    (A3, Secret) ].
Lemma check_scalar_loop1_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length loop1_instrs)) check_scalar_loop1_data ->
  noninterferent_strong init_addr loop1_instrs
    (init_addr + 4 * N.of_nat (length loop1_instrs))
    (check_scalar_loop1_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length loop1_instrs)) check_scalar_loop1_data).
Proof.
  intros Hfit.
  apply (ni_of_cells (regs' := map (concretize_reg init_addr) loop1_reg_specs_rel)
                     (cs := map (concretize_mem init_addr) loop1_byte_specs_rel)).
  - apply compile_clear; lia.
  - reflexivity.
  - apply perm_of_eq. cbn. simpl. solve_cells_eq.
  - unfold fits, layout_size in Hfit. simpl in Hfit.
    eapply (gen_contract_noninterferent_rel_bytes_simple (bound := 48)).
    + apply Prelude.nodup_fixed; reflexivity.
    + intros [|[|[|[|[|[|[|[|i]]]]]]]] spec H; cbn in H;
        try (inversion H; subst; cbn; lia); try discriminate.
    + simpl. lia.
    + simpl. lia.
    + solve_valid valid_loop1_cfg_contract_param.
Qed.

(* SANITY CHECK (PLAN-spec-layer D20): the universal theorem at the
   default load address init_addr = 0 -- its premise is satisfiable there. *)
Lemma check_scalar_loop1_noninterferent :
  noninterferent_strong init_addr loop1_instrs
    (init_addr + 4 * N.of_nat (length loop1_instrs))
    (check_scalar_loop1_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length loop1_instrs)) check_scalar_loop1_data).
Proof.
  apply check_scalar_loop1_noninterferent_param.
  unfold fits; vm_compute; reflexivity.
Qed.
