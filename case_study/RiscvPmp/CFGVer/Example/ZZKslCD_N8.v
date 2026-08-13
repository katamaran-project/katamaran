From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkDistinctCommon.
Lemma valid_zzkcd_n8 (ia : N) : ValidCFGVerifierContract (zzkcd_cfg_contract_param 8%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
