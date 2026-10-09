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
(* Example/SetX2Result.v — end-to-end noninterference theorem(s) for        *)
(* set_X2_to_42.                                               *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/SetX2.v.  This file is deliberately SEPARATE from      *)
(* Example/SetX2.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.SetX2.

(* The program, named once so the statements below read as text. *)
Definition set_X2_to_42_instrs : list AST := [ADDI X2 X0 (bv.of_N 42)].

(* Phase 4.2 headline: set_X2_to_42 verified end-to-end for a UNIVERSAL base
   address, from the single symbolic-base VC valid_set_X2_to_42_param — no
   per-address vm_compute.  The (init_addr + 4 < lenAddr) premise is the base
   bound the fetch obligations need; it is the `(bound)` the plan anticipated. *)
Lemma set_X2_to_42_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length set_X2_to_42_instrs)) [] ->
  noninterferent_strong init_addr set_X2_to_42_instrs (init_addr + 4 * N.of_nat (length set_X2_to_42_instrs))
    [(X2, Secret)] (compile (init_addr + 4 * N.of_nat (length set_X2_to_42_instrs)) []).
Proof.
  intros Hbound.
  apply (ni_of_cells (regs' := [(X2, Secret)]) (cs := []));
    [apply compile_clear; lia | reflexivity | reflexivity |].
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
  - solve_valid valid_set_X2_to_42_param.
Qed.

(* The concrete result at init_addr = 0, as a corollary -- this was
   missing before (set_X2 had only the parametric headline). *)
(* SANITY CHECK (PLAN-spec-layer D20): the parametric theorem at the
   default load address init_addr = 0. *)
Lemma set_X2_to_42_noninterferent :
  noninterferent_strong init_addr set_X2_to_42_instrs (init_addr + 4 * N.of_nat (length set_X2_to_42_instrs))
    [(X2, Secret)] (compile (init_addr + 4 * N.of_nat (length set_X2_to_42_instrs)) []).
Proof.
  apply set_X2_to_42_noninterferent_param.
  unfold fits, layout_size, init_addr, lenAddr. cbn. lia.
Qed.

