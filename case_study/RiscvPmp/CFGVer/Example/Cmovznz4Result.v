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

(* Phase 4.2 headline #2: cmovznz4 (29 instrs, 12 data words, base-relative
   data pointers) verified end-to-end for a UNIVERSAL base address, from the
   single symbolic-base VC valid_cmovznz4_cfg_contract_param via the reusable
   base-relative bridge gen_contract_noninterferent_rel_classed_simple.  The
   concrete reg /
   mem specs are the base-relative specs concretized at init_addr. *)
Lemma cmovznz4_noninterferent_param (init_addr : N) :
  (init_addr + 164 < lenAddr)%N ->
  noninterferent_strong init_addr cmovznz4_instrs
    (pcOutOfInstrs_exitCond init_addr cmovznz4_instrs)
    (map (concretize_reg init_addr) cmovznz4_reg_specs_rel)
    (map (concretize_mem init_addr) cmovznz4_mem_specs_rel).
Proof.
  intros Hb.
  (* `<- strip_id_cmovznz4` restates the goal over `strip cmovznz4_instrs`, the
     form the bridge now concludes.  reflexivity-equal, so the theorem above is
     literally the same statement as before the AnnotInstr migration — that is
     the invariant, and this rewrite is where it is discharged. *)
  rewrite <- strip_id_cmovznz4.
  eapply gen_contract_noninterferent_rel_classed_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - intros [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]] spec H; cbn in H;
      try (inversion H; subst; cbn; f_equal; lia); try discriminate.
  - cbn. lia.
  - exact Hb.
  - exact (valid_cmovznz4_cfg_contract_param init_addr).
Qed.

(* The two concrete cmovznz4 results are now corollaries of the universal-base
   theorem above: the single source of truth is valid_cmovznz4_cfg_contract_param.
   The concrete reg/mem specs are exactly the base-relative specs concretized at
   the respective base (init_addr = 0, and cmovznz4_start = 256), so the
   conclusions coincide definitionally (checked by vm_compute). *)
Lemma cmovznz4_noninterferent :
  noninterferent_strong init_addr cmovznz4_instrs (pcOutOfInstrs_exitCond init_addr cmovznz4_instrs)
    cmovznz4_reg_specs cmovznz4_mem_specs.
Proof.
  ni_rel_corollary cmovznz4_noninterferent_param
    cmovznz4_reg_specs_rel cmovznz4_mem_specs_rel init_addr.
Qed.

(* Fully end-to-end at the genuinely nonzero start address cmovznz4_start = 256,
   as a corollary of the universal-base version. *)
Lemma cmovznz4_noninterferent_at_start :
  noninterferent_strong cmovznz4_start cmovznz4_instrs
    (pcOutOfInstrs_exitCond cmovznz4_start cmovznz4_instrs)
    cmovznz4_reg_specs_at_start cmovznz4_mem_specs_at_start.
Proof.
  ni_rel_corollary cmovznz4_noninterferent_param
    cmovznz4_reg_specs_rel cmovznz4_mem_specs_rel cmovznz4_start.
Qed.

