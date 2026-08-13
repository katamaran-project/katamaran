From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZKslNUsedFlatCommon.
Lemma valid_zzknuf_n8 (ia : N) : ValidCFGVerifierContract (zzknuf_cfg_contract_param 8%N ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
