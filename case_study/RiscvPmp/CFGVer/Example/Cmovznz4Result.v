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
(* Example/Cmovznz4Result.v — end-to-end noninterference theorem(s) for        *)
(* cmovznz4 (29 instrs, 12 data words, base-relative).         *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/Cmovznz4.v.  This file is deliberately SEPARATE from      *)
(* Example/Cmovznz4.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Cmovznz4.

(* code: init_addr .. init_addr+115 (29 instructions); the data follows. *)
Definition cmovznz4_data : list region :=
  [ Array 4 Secret        (* x[0..3]  at init_addr+116 *)
  ; Array 4 Secret        (* y[0..3]  at init_addr+132 *)
  ; Array 4 Secret ].     (* r[0..3]  at init_addr+148 *)

Definition cmovznz4_regs (ia : N) : list reg_spec :=
  [ (A0, Secret);                                        (* cin *)
    (A1, Known (bv.of_N (ia + 116)));                    (* &x  *)
    (A2, Known (bv.of_N (ia + 132)));                    (* &y  *)
    (A3, Known (bv.of_N (ia + 148)));                    (* &r  *)
    (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret); (T0, Secret); (T1, Secret) ].

(* cmovznz4 verified end-to-end for a UNIVERSAL load address, from the single
   symbolic-base VC valid_cmovznz4_cfg_contract_param via the base-relative
   bridge gen_contract_noninterferent_rel_classed_simple. *)
Lemma cmovznz4_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length cmovznz4_instrs)) cmovznz4_data ->
  noninterferent_strong init_addr cmovznz4_instrs
    (init_addr + 4 * N.of_nat (length cmovznz4_instrs))
    (cmovznz4_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length cmovznz4_instrs)) cmovznz4_data).
Proof.
  intros Hfit.
  apply (ni_of_cells (regs' := map (concretize_reg init_addr) cmovznz4_reg_specs_rel)
                     (cs := map (concretize_mem init_addr) cmovznz4_mem_specs_rel)).
  - apply compile_clear; lia.
  - apply compile_in_range; [lia | assumption].
  - reflexivity.
  - apply perm_of_eq. cbn. simpl. solve_cells_eq.
  - unfold fits, layout_size in Hfit. simpl in Hfit.
    eapply (gen_contract_noninterferent_rel_classed_simple (bound := 164)).
    + apply Prelude.nodup_fixed; reflexivity.
    + intros [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]] spec H; cbn in H;
        try (inversion H; subst; cbn; lia); try discriminate.
    + simpl. lia.
    + simpl. lia.
    + solve_valid valid_cmovznz4_cfg_contract_param.
Qed.

(* SANITY CHECKS (PLAN-spec-layer D20): the universal theorem at the default
   load address init_addr = 0 and at the nonzero cmovznz4_start = 256 -- its
   premise is satisfiable there, so it is not vacuous. *)
Lemma cmovznz4_noninterferent :
  noninterferent_strong init_addr cmovznz4_instrs
    (init_addr + 4 * N.of_nat (length cmovznz4_instrs))
    (cmovznz4_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length cmovznz4_instrs)) cmovznz4_data).
Proof.
  apply cmovznz4_noninterferent_param.
  unfold fits; vm_compute; reflexivity.
Qed.

Lemma cmovznz4_noninterferent_at_start :
  noninterferent_strong cmovznz4_start cmovznz4_instrs
    (cmovznz4_start + 4 * N.of_nat (length cmovznz4_instrs))
    (cmovznz4_regs cmovznz4_start)
    (compile (cmovznz4_start + 4 * N.of_nat (length cmovznz4_instrs)) cmovznz4_data).
Proof.
  apply cmovznz4_noninterferent_param.
  unfold fits; vm_compute; reflexivity.
Qed.
