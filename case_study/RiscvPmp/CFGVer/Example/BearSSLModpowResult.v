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
(* Example/BearSSLModpowResult.v — end-to-end noninterference for the        *)
(* BearSSL `modpow_opt` window-lookup step.                                  *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE — see BearSSLMuladdResult.v for the rationale   *)
(* behind the Example/<Prog>Result.v split.                                  *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.BearSSLModpow.

(* Bound: 5 instructions * 4 bytes = 20. *)
Lemma modpow_win_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length modpow_win_instrs)) [] ->
  noninterferent_strong init_addr modpow_win_instrs (init_addr + 4 * N.of_nat (length modpow_win_instrs))
    modpow_win_reg_specs (compile (init_addr + 4 * N.of_nat (length modpow_win_instrs)) []).
Proof.
  intros Hbound.
  apply (ni_of_cells (regs' := modpow_win_reg_specs) (cs := []));
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
  - solve_valid valid_modpow_win_cfg_contract_param.
Qed.

(* SANITY CHECK (PLAN-spec-layer D20): the parametric theorem at the
   default load address init_addr = 0. *)
Lemma modpow_win_noninterferent :
  noninterferent_strong init_addr modpow_win_instrs (init_addr + 4 * N.of_nat (length modpow_win_instrs))
    modpow_win_reg_specs (compile (init_addr + 4 * N.of_nat (length modpow_win_instrs)) []).
Proof.
  apply modpow_win_noninterferent_param.
  unfold fits, layout_size, init_addr, lenAddr. cbn. lia.
Qed.
