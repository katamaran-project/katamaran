From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkDistinctCommon.
Lemma valid_zzkcd_n4 (ia : N) : ValidCFGVerifierContract (zzkcd_cfg_contract_param 4%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
