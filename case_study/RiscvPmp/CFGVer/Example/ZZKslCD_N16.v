From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslChunkDistinctCommon.
Lemma valid_zzkcd_n16 (ia : N) : ValidCFGVerifierContract (zzkcd_cfg_contract_param 16%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
