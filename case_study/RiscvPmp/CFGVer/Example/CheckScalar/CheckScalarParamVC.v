(* Example/CheckScalar/CheckScalarParamVC.v -- the whole check_scalar's VC at
   symbolic klen, both loops as blocks. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParam.

Lemma valid_cs : cfg_vc cs cs_annot.
Proof. Time solve_mb_vc. Qed.
