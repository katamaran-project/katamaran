(* THROWAWAY ABLATION — counter-exit variant at N = 32 (PLAN-byte-memory §10). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZByteCtrCommon.

Lemma valid_ctr_n32 (ia : N) :
  ValidCFGVerifierContract (ctr_cfg_contract_param 32 ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
