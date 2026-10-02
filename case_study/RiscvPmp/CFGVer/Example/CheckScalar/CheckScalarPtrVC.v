(* Example/CheckScalar/CheckScalarPtrVC.v -- check_scalar's VC with k a pointer. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParam.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarPtr.

Lemma valid_csp : cfg_vc csp cs_annot.
Proof. Time solve_mb_vc. Qed.
