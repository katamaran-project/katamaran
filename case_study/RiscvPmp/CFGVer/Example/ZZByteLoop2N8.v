(* THROWAWAY — PLAN-check-scalar-full.md §4, loop 2 at trip count N = 8. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZByteLoop2Common.

Lemma valid_loop2_n8 (ia : N) :
  ValidCFGVerifierContract (loop2_cfg_contract_param 8 ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.

Print Assumptions valid_loop2_n8.
