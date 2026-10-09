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
(* Example/CountdownResult.v — end-to-end noninterference theorem(s) for        *)
(* countdown (backward branch) and countdown_mem.              *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/Countdown.v.  This file is deliberately SEPARATE from      *)
(* Example/Countdown.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Countdown.

(* The program, named once so the statements below read as text. *)
Definition countdown_instrs : list AST := [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset].

(* Phase 4.2: countdown verified end-to-end for a UNIVERSAL base address,
   from the single symbolic-base VC valid_countdown_cfg_contract_param --
   confirms the BACKWARD branch (BNE back_offset) case works with the exact
   same offset-agnostic tail as the forward-only programs (cmovznz4/set_X2). *)
Lemma countdown_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length countdown_instrs)) [] ->
  noninterferent_strong init_addr countdown_instrs (init_addr + 4 * N.of_nat (length countdown_instrs))
    [(X1, Known (bv.of_N 2))] (compile (init_addr + 4 * N.of_nat (length countdown_instrs)) []).
Proof.
  intros Hbound.
  apply (ni_of_cells (regs' := [(X1, Known (bv.of_N 2))]) (cs := []));
    [apply compile_clear; lia | reflexivity | reflexivity |].
  (* The `strip` restatement this proof used to open with is GONE: the
     EndToEnd bridges now conclude over `instrs` itself, not `strip
     instrs`, because cfg_instrs is a `list AST` (PLAN-contract-ast
     Phase 3).  And since 2026-09-23 the annotated list does not enter HERE
     at all: the hint list, the strip equation and the block obligations are
     sealed inside ValidCFGVerifierContract, which `solve_valid` supplies from
     this example's own VC.  No statement in this file names an annotation. *)
  (* This theorem's program is an INLINE literal (countdown_mem_instrs belongs
     to countdown_mem_noninterferent_param below -- CountdownResult.v is the one
     MIXED file, and a script that assumed one program per Result file put the
     wrong rewrite here).  Same job done locally: restate over `strip <literal>`,
     the form the EndToEnd bridges now conclude, reflexivity-equal so the
     theorem above is unchanged. *)
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - exact (fits_nil Hbound).
  - solve_valid valid_countdown_cfg_contract_param.
Qed.

(* The concrete result is a corollary of the universal-base theorem above:
   its exit address is the same `init_addr + 8`, so no vm_compute/rewrite is
   needed here at all. *)
(* SANITY CHECK (PLAN-spec-layer D20): the parametric theorem at the
   default load address init_addr = 0. *)
Lemma countdown_noninterferent :
  noninterferent_strong init_addr countdown_instrs (init_addr + 4 * N.of_nat (length countdown_instrs))
    [(X1, Known (bv.of_N 2))] (compile (init_addr + 4 * N.of_nat (length countdown_instrs)) []).
Proof.
  apply countdown_noninterferent_param.
  unfold fits, layout_size, init_addr, lenAddr. cbn. lia.
Qed.

(* code: init_addr .. init_addr+15 (4 instructions); the counter follows. *)
Definition countdown_mem_data : list region :=
  [ Word (Known (bv.of_N 2)) ].   (* the counter, at init_addr+16 *)
Definition countdown_mem_regs (ia : N) : list reg_spec :=
  [ (X1, Secret);
    (X2, Known (bv.of_N ia)) ].   (* the base, held in X2 *)
Lemma countdown_mem_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length countdown_mem_instrs)) countdown_mem_data ->
  noninterferent_strong init_addr countdown_mem_instrs
    (init_addr + 4 * N.of_nat (length countdown_mem_instrs))
    (countdown_mem_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length countdown_mem_instrs)) countdown_mem_data).
Proof.
  intros Hfit.
  apply (ni_of_cells (regs' := map (concretize_reg init_addr) countdown_mem_reg_specs_rel)
                     (cs := map (concretize_mem init_addr) countdown_mem_mem_specs_rel)).
  - apply compile_clear; lia.
  - apply perm_of_eq; cbn; rewrite N.add_0_r; reflexivity.
  - apply perm_of_eq. cbn. solve_cells_eq.
  - unfold fits, layout_size, lenAddr in Hfit. cbn in Hfit.
    eapply gen_contract_noninterferent_rel_classed_simple.
    + apply Prelude.nodup_fixed; reflexivity.
    + intros [|i] spec H; cbn in H;
        try (inversion H; subst; cbn; lia); try discriminate.
    + unfold lenAddr. cbn. lia.
    + unfold lenAddr. cbn. lia.
    + solve_valid valid_countdown_mem_cfg_contract_param.
Qed.

(* SANITY CHECK (PLAN-spec-layer D20): the universal theorem at the
   default load address init_addr = 0 -- its premise is satisfiable there. *)
Lemma countdown_mem_noninterferent :
  noninterferent_strong init_addr countdown_mem_instrs
    (init_addr + 4 * N.of_nat (length countdown_mem_instrs))
    (countdown_mem_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length countdown_mem_instrs)) countdown_mem_data).
Proof.
  apply countdown_mem_noninterferent_param.
  unfold fits, layout_size, init_addr, lenAddr. cbn. lia.
Qed.
