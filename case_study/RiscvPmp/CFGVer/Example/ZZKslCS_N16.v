From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkSharedCommon.
Lemma valid_zzkcs_n16 (ia : N) : ValidCFGVerifierContract (zzkcs_cfg_contract_param 16%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
