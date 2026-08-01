From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
From Katamaran Require Import RiscvPmp.CFGVer.Example.KeyScheduleLoop.
Lemma ctl_ksl : ValidCFGVerifierContract (key_schedule_loop2_cfg_contract_param 0).
Proof.
  intros. vm_compute.
  solve_vc.
  all: (let n := numgoals in idtac "KSL after solve_vc:" n).
  solve_symbase_fetch.
  all: (let n := numgoals in idtac "KSL after fetch:" n).
Admitted.
