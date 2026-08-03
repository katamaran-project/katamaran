From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Lemma stgp_8 : ValidCFGVerifierContract (zzn_contract 8).
Proof.
  intros.
  Time vm_compute.
  Time solve_vc.
  all: (let g := numgoals in idtac "PARAM N=8 goals after solve_vc:" g).
  all: solve_symbase_fetch.
Time Qed.
