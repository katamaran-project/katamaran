(* THROWAWAY ABLATION — counter-exit variant at N = 16 (PLAN-byte-memory §10). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZByteCtrCommon.

Lemma valid_ctr_n16 (ia : N) :
  ValidCFGVerifierContract (ctr_cfg_contract_param 16 ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
