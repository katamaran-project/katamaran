From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkPaddedCommon.
Lemma valid_zzkcp_n16 (ia : N) : ValidCFGVerifierContract (zzkcp_cfg_contract_param 16%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
