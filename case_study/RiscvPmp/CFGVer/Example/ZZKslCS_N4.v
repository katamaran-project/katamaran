From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkSharedCommon.
Lemma valid_zzkcs_n4 (ia : N) : ValidCFGVerifierContract (zzkcs_cfg_contract_param 4%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
