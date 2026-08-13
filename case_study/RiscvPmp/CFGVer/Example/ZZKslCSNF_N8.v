From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkSharedNoFbCommon.
Lemma valid_zzkcsnf_n8 (ia : N) : ValidCFGVerifierContract (zzkcsnf_cfg_contract_param 8%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
