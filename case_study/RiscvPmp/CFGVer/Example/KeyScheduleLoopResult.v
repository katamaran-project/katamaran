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
(* Example/KeyScheduleLoopResult.v — end-to-end noninterference theorem(s) for        *)
(* key_schedule_loop2 (small-N=2 GHASH loop spike).            *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/KeyScheduleLoop.v.  This file is deliberately SEPARATE from      *)
(* Example/KeyScheduleLoop.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.KeyScheduleLoop.

(* Phase 4.2 headline #4: key_schedule_loop2 (small-N=2 feasibility spike
   toward the full Botan GHASH::key_schedule loop -- see the header comment
   in Example/KeyScheduleLoop.v) verified end-to-end for a UNIVERSAL base
   address, from the single symbolic-base VC
   valid_key_schedule_loop2_cfg_contract_param -- confirms a backward
   branch whose body both re-runs secret arithmetic AND stores to an
   advancing (base-relative) table address works with the same reusable
   bridge and offset-agnostic tail as every other example. *)
(* code: init_addr .. init_addr+55 (14 instructions); the table follows. *)
Definition key_schedule_loop2_data : list region :=
  [ Array 2 Secret ].     (* table[0..1] at init_addr+56 *)
Definition key_schedule_loop2_regs (ia : N) : list reg_spec :=
  [ (A0, Secret); (A1, Secret); (A2, Secret);   (* H and two scratch registers *)
    (A3, Known (bv.of_N (ia + 56)));            (* &table[0] *)
    (A4, Known (bv.of_N 2)) ].                  (* trip count *)
Lemma key_schedule_loop2_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length key_schedule_loop2_instrs)) key_schedule_loop2_data ->
  noninterferent_strong init_addr key_schedule_loop2_instrs
    (init_addr + 4 * N.of_nat (length key_schedule_loop2_instrs))
    (key_schedule_loop2_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length key_schedule_loop2_instrs)) key_schedule_loop2_data).
Proof.
  intros Hfit.
  apply (ni_of_cells (regs' := map (concretize_reg init_addr) key_schedule_loop2_reg_specs_rel)
                     (cs := map (concretize_mem init_addr) key_schedule_loop2_mem_specs_rel)).
  - apply compile_clear; lia.
  - apply compile_in_range; [lia | assumption].
  - reflexivity.
  - apply perm_of_eq. cbn. simpl. solve_cells_eq.
  - unfold fits, layout_size in Hfit. simpl in Hfit.
    eapply (gen_contract_noninterferent_rel_classed_simple (bound := 64)).
    + apply Prelude.nodup_fixed; reflexivity.
    + intros [|[|i]] spec H; cbn in H;
        try (inversion H; subst; cbn; lia); try discriminate.
    + simpl. lia.
    + simpl. lia.
    + solve_valid valid_key_schedule_loop2_cfg_contract_param.
Qed.

(* SANITY CHECK (PLAN-spec-layer D20): the universal theorem at the
   default load address init_addr = 0 -- its premise is satisfiable there. *)
Lemma key_schedule_loop2_noninterferent :
  noninterferent_strong init_addr key_schedule_loop2_instrs
    (init_addr + 4 * N.of_nat (length key_schedule_loop2_instrs))
    (key_schedule_loop2_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length key_schedule_loop2_instrs)) key_schedule_loop2_data).
Proof.
  apply key_schedule_loop2_noninterferent_param.
  unfold fits; vm_compute; reflexivity.
Qed.
