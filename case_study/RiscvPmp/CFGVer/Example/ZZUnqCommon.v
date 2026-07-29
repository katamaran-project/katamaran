(* ========================================================================= *)
(* ZZUnqCommon.v -- THROWAWAY diagnostic support file (delete after use).     *)
(*                                                                           *)
(* Phase B.5 of PLAN-unquantify-gate.md: the actual demonicv census delta    *)
(* after running the ported unquantify (Symbolic/Propositions.v) over the    *)
(* flat reproducer's VC, both raw and postprocess-first (the composition     *)
(* main actually uses). Definitions only, no vm_compute -- see ZZCommon.v's  *)
(* header for why heavy Evals are split one-per-process.                    *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZCommon.

(* Control baseline: postprocess alone, no unquantify -- isolates
   unquantify's own marginal contribution from postprocess's. *)
Definition zzn_postprocess_nc (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (postprocess (CFG_VC_triple p exits P i fl))).

Definition zzn_unq_nc (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (unquantify (CFG_VC_triple p exits P i fl))).

Definition zzn_postprocess_unq_nc (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (unquantify (postprocess (CFG_VC_triple p exits P i fl)))).
