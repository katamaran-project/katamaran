From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkPaddedCommon.
Lemma valid_zzkcp_n4 (ia : N) : ValidCFGVerifierContract (zzkcp_cfg_contract_param 4%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
