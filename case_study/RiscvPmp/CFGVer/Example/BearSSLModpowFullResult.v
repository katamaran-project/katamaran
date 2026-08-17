(* ========================================================================= *)
(* Example/BearSSLModpowFullResult.v — end-to-end noninterference theorem     *)
(* for the COMPLETE BearSSL modpow_opt window lookup (28 instrs, two nested   *)
(* loops, 16 data words, base-relative).                                     *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Companion to BearSSLModpowResult.v, which states the same property for the *)
(* 5-instruction inner-loop BODY in isolation.  This file covers the whole    *)
(* function: both loops, the loop control flow, and the real memory traffic.  *)
(*                                                                           *)
(* This file is deliberately SEPARATE from Example/BearSSLModpowFull.v:       *)
(* requiring EndToEnd (and so Adequacy) here keeps the example itself         *)
(* EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on building in    *)
(* parallel with the examples instead of ahead of all of them.                *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.BearSSLModpowFull.

(* Bound 176 = 172 (last data offset, base[3] of the last window) + 4 (word).

   What this says: for ANY base address, and for any two initial states that
   agree on the PUBLIC data — the two loop bounds A3/A4 (pinned to 4) and
   nothing else — the two runs emit the same leakage trace.  The secret
   exponent window A2, the accumulator array t2[] and the whole candidate
   table base[] may differ arbitrarily between the two worlds.  In particular
   the trace is independent of `bits`, which is precisely the quantity the
   "Breaking Bad" finding (Table 10) is about. *)
Lemma modpow_win_full_noninterferent_param (init_addr : N) :
  (init_addr + 176 < lenAddr)%N ->
  noninterferent_strong init_addr modpow_win_full_instrs
    (pcOutOfInstrs_exitCond init_addr modpow_win_full_instrs)
    (map (concretize_reg init_addr) modpow_win_full_reg_specs_rel)
    (map (concretize_mem init_addr) modpow_win_full_mem_specs_rel).
Proof.
  intros Hb.
  eapply gen_contract_noninterferent_rel_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - intros [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]] spec H; cbn in H;
      try (inversion H; subst; cbn; f_equal; lia); try discriminate.
  - cbn. lia.
  - exact Hb.
  - exact (valid_modpow_win_full_cfg_contract_param init_addr).
Qed.

Lemma modpow_win_full_noninterferent :
  noninterferent_strong init_addr modpow_win_full_instrs
    (pcOutOfInstrs_exitCond init_addr modpow_win_full_instrs)
    (map (concretize_reg init_addr) modpow_win_full_reg_specs_rel)
    (map (concretize_mem init_addr) modpow_win_full_mem_specs_rel).
Proof.
  apply modpow_win_full_noninterferent_param.
  unfold init_addr, lenAddr; lia.
Qed.
