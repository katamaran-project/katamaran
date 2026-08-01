From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Set Printing Depth 100000.
Lemma goalsp1 : ValidCFGVerifierContract (zzn_contract 1).
Proof.
  intros. vm_compute. solve_vc.
  all: (match goal with |- ?G => idtac "===GOAL==="; idtac G end).
Admitted.
