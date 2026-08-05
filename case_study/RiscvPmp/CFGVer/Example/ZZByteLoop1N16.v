(* THROWAWAY — PLAN-byte-memory.md §6 step 2, loop 1 at trip count N = 16. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZByteLoop1Common.

Lemma valid_loop1_n16 (ia : N) :
  ValidCFGVerifierContract (loop1_cfg_contract_param 16 ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
