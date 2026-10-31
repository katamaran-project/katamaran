(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarPtr.v -- check_scalar with k a REAL        *)
(* POINTER ARGUMENT: anywhere in memory, not laid out after the code         *)
(* (PLAN-general-endtoend.md A3 probe).  Same instructions, loop blocks and  *)
(* ghost annotations as CheckScalarParam.v; the contract is the generator     *)
(* form gen_prog_contract, so the end theorem needs no hand-written ImplPre. *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamInstrs.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParam.

(* A0 = k, A1 = klen (public), ra = the exit p + 144, the rest scratch *)
Definition csp_regs : list (reg_spec_q csCtx) :=
  [ (A0, Known (PVVar "k")); (A1, Known (PVVar "l")); (X1, Known (PVOff "p" 144))
  ; (A2, Secret); (A3, Secret); (A4, Secret)
  ; (A5, Secret); (A6, Secret); (A7, Secret) ].

(* P256_N right after the code; k's bytes wherever k points *)
Definition csp_data : list (data_spec csCtx) :=
  [ DBytes false (term_val ty_xlenbits (bv.of_N 32)) "vN"
  ; DPtr (term_var "k")
  ; DBytes false (term_var "l") "vK" ]%list.

Definition csp : @CFGVerifierContract (csCtx ▻▻ data_vctx csp_data) :=
  gen_prog_contract "p" _ csp_regs (asn.formula formula_true) 144 csp_data cs_instrs 40
    (asn.formula formula_true).
