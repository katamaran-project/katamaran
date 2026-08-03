From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Lemma stgp_16 : ValidCFGVerifierContract (zzn_contract 16).
Proof.
  intros.
  Time vm_compute.
  Time solve_vc.
  all: (let g := numgoals in idtac "PARAM N=16 goals after solve_vc:" g).
  all: solve_symbase_fetch.
Time Qed.
