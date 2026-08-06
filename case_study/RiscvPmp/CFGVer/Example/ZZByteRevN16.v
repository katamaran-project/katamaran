(* THROWAWAY heap-order probe at N = 16 (PLAN-byte-memory §10). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZByteRevCommon.

Lemma valid_rev_n16 (ia : N) :
  ValidCFGVerifierContract (rev_cfg_contract_param 16 ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
