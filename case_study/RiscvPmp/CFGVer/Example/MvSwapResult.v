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
(* Example/MvSwapResult.v — end-to-end noninterference theorem(s) for        *)
(* the 3-instruction register swap.                            *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/MvSwap.v.  This file is deliberately SEPARATE from      *)
(* Example/MvSwap.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.MvSwap.

(* Phase 4.2: swap verified end-to-end for a UNIVERSAL base address, from
   the single symbolic-base VC valid_swap_cfg_contract_param. *)
Lemma swap_noninterferent_param (init_addr : N) :
  (init_addr + 12 < lenAddr)%N ->
  noninterferent_strong init_addr [MV X3 X2; MV X2 X1; MV X1 X3]
    (pcOutOfInstrs_exitCond init_addr [MV X3 X2; MV X2 X1; MV X1 X3])
    [(X1, false, None); (X2, false, None); (X3, false, None)] [].
Proof.
  intros Hbound.
  (* This program builds its instruction list INLINE in the contract
     literal, so there is no named object to hang a strip_id_* anchor
     on (unlike the nine that have one).  Same job, done locally: the
     goal is restated over `strip <literal>`, the form the EndToEnd
     bridges now conclude, and it is reflexivity-equal so the theorem
     above is unchanged. *)
  assert (Hstrip : strip [MV X3 X2; MV X2 X1; MV X1 X3] = [MV X3 X2; MV X2 X1; MV X1 X3]) by reflexivity.
  rewrite <- Hstrip.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_swap_cfg_contract_param init_addr).
Qed.

Lemma swap_noninterferent :
  noninterferent_strong init_addr [MV X3 X2; MV X2 X1; MV X1 X3]
    (pcOutOfInstrs_exitCond init_addr [MV X3 X2; MV X2 X1; MV X1 X3])
    [(X1, false, None); (X2, false, None); (X3, false, None)] [].
Proof.
  apply swap_noninterferent_param.
  unfold init_addr, lenAddr; lia.
Qed.

