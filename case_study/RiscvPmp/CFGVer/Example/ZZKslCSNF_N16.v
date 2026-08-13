From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkSharedNoFbCommon.
Lemma valid_zzkcsnf_n16 (ia : N) : ValidCFGVerifierContract (zzkcsnf_cfg_contract_param 16%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
