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
(* Example/PrecomputeResult.v — end-to-end noninterference theorem(s) for        *)
(* precompute (Botan GHASH::key_schedule masking step).        *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/Precompute.v.  This file is deliberately SEPARATE from      *)
(* Example/Precompute.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Precompute.

(* Phase 4.2 headline #3: precompute (Botan's GHASH::key_schedule masking
   step, 32-bit-word analogue, 10 instrs, no memory) verified end-to-end
   for a UNIVERSAL base address, from the single symbolic-base VC
   valid_precompute_cfg_contract_param -- no per-address vm_compute. *)
Lemma precompute_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length precompute_instrs)) [] ->
  noninterferent_strong init_addr precompute_instrs (init_addr + 4 * N.of_nat (length precompute_instrs))
    precompute_reg_specs (compile (init_addr + 4 * N.of_nat (length precompute_instrs)) []).
Proof.
  intros Hbound.
  apply (ni_of_cells (regs' := precompute_reg_specs) (cs := []));
    [apply compile_clear; lia | apply compile_in_range; [lia | assumption] | reflexivity | reflexivity |].
  (* The `strip` restatement this proof used to open with is GONE: the
     EndToEnd bridges now conclude over `instrs` itself, not `strip
     instrs`, because cfg_instrs is a `list AST` (PLAN-contract-ast
     Phase 3).  And since 2026-09-23 the annotated list does not enter HERE
     at all: the hint list, the strip equation and the block obligations are
     sealed inside ValidCFGVerifierContract, which `solve_valid` supplies from
     this example's own VC.  No statement in this file names an annotation. *)
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - exact (fits_nil Hbound).
  - solve_valid valid_precompute_cfg_contract_param.
Qed.

(* The concrete result at init_addr = 0, as a corollary. *)
(* SANITY CHECK (PLAN-spec-layer D20): the parametric theorem at the
   default load address init_addr = 0. *)
Lemma precompute_noninterferent :
  noninterferent_strong init_addr precompute_instrs (init_addr + 4 * N.of_nat (length precompute_instrs))
    precompute_reg_specs (compile (init_addr + 4 * N.of_nat (length precompute_instrs)) []).
Proof.
  apply precompute_noninterferent_param.
  unfold fits, layout_size, init_addr, lenAddr. cbn. lia.
Qed.

