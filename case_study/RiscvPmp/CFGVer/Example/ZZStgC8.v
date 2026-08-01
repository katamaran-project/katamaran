From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Lemma stgc_8 : ValidCFGVerifierContract (zzc_contract 8).
Proof.
  intros.
  Time vm_compute.
  Time solve_vc.
  all: (let g := numgoals in idtac "CONC N=8 goals after solve_vc:" g).
Time Qed.
