From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslNUsedFlatCommon.
Lemma valid_zzknuf_n4 (ia : N) : ValidCFGVerifierContract (zzknuf_cfg_contract_param 4%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
