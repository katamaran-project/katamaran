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
(* code: init_addr .. init_addr+111 (28 instructions); the data follows. *)
Definition modpow_win_full_data : list region :=
  [ Array 4 Secret        (* t2[0..3]    at init_addr+112 *)
  ; Array 12 Secret ].    (* base[0..11] at init_addr+128 *)
Definition modpow_win_full_regs (ia : N) : list reg_spec :=
  [ (A0, Known (bv.of_N (ia + 112)));           (* &t2[0]   *)
    (A1, Known (bv.of_N (ia + 128)));           (* &base[0] *)
    (A2, Secret);                               (* bits     *)
    (A3, Known (bv.of_N 4));                    (* num_win = 1 << k *)
    (A4, Known (bv.of_N 4));                    (* mwlen    *)
    (A5, Secret); (A6, Secret); (A7, Secret);
    (T0, Secret); (T1, Secret); (T2, Secret); (T3, Secret);
    (T4, Secret); (T5, Secret); (T6, Secret) ].
Lemma modpow_win_full_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length modpow_win_full_instrs)) modpow_win_full_data ->
  noninterferent_strong init_addr modpow_win_full_instrs
    (init_addr + 4 * N.of_nat (length modpow_win_full_instrs))
    (modpow_win_full_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length modpow_win_full_instrs)) modpow_win_full_data).
Proof.
  intros Hfit.
  apply (ni_of_cells (regs' := map (concretize_reg init_addr) modpow_win_full_reg_specs_rel)
                     (cs := map (concretize_mem init_addr) modpow_win_full_mem_specs_rel)).
  - apply compile_clear; lia.
  - reflexivity.
  - apply perm_of_eq. cbn. simpl. solve_cells_eq.
  - unfold fits, layout_size in Hfit. simpl in Hfit.
    eapply (gen_contract_noninterferent_rel_classed_simple (bound := 176)).
    + apply Prelude.nodup_fixed; reflexivity.
    + intros [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]] spec H; cbn in H;
        try (inversion H; subst; cbn; lia); try discriminate.
    + simpl. lia.
    + simpl. lia.
    + solve_valid valid_modpow_win_full_cfg_contract_param.
Qed.

(* SANITY CHECK (PLAN-spec-layer D20): the universal theorem at the
   default load address init_addr = 0 -- its premise is satisfiable there. *)
Lemma modpow_win_full_noninterferent :
  noninterferent_strong init_addr modpow_win_full_instrs
    (init_addr + 4 * N.of_nat (length modpow_win_full_instrs))
    (modpow_win_full_regs init_addr)
    (compile (init_addr + 4 * N.of_nat (length modpow_win_full_instrs)) modpow_win_full_data).
Proof.
  apply modpow_win_full_noninterferent_param.
  unfold fits; vm_compute; reflexivity.
Qed.
