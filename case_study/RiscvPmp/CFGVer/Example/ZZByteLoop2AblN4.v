(* THROWAWAY — diagnostic ablation, PLAN-check-scalar-full.md §4 follow-up. N = 4. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZByteLoop2AblCommon.

Lemma valid_loop2_abl_n4 (ia : N) :
  ValidCFGVerifierContract (loop2_cfg_contract_param 4 ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.

Print Assumptions valid_loop2_abl_n4.
