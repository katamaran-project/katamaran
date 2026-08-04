(* ========================================================================= *)
(* ZZExpandDump.v — THROWAWAY diagnostic (delete after use).                  *)
(*                                                                           *)
(* Dumps the raw symbolic term the executor actually builds for clang's       *)
(* branchless "is-nonzero mask" idiom                                        *)
(*                                                                           *)
(*     snez a2, a0        (= sltu a2, x0, a0)                                *)
(*     addi a2, a2, -1                                                       *)
(*                                                                           *)
(* i.e. mask = [a0 <> 0] - 1 = -[a0 = 0], the BearSSL EQ0 / Botan            *)
(* CT::Mask::expand shape.  Purpose: write the peval recognizer for the       *)
(* planned `uop.expand` against the executor's REAL output instead of         *)
(* against a shape inferred from Machine.v.  A peval rule whose pattern       *)
(* never matches is invisible — everything still compiles, there is just no   *)
(* effect — so the ground truth is worth one probe.                          *)
(*                                                                           *)
(* Why the BNE: the accumulator/mask term is never *observed* by the VC on    *)
(* its own (postconditions are trivial by design and nothing leaks an ALU     *)
(* result), so it would not appear in the dump at all.  Branching on it       *)
(* forces it into a real formula_relop.  That requires the branch condition   *)
(* to be public, hence A0 is declared PUBLIC and symbolic: private would      *)
(* collapse the formula to False (secret-data-walls) and a pinned constant    *)
(* would fold the whole chain away.                                          *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
Import SymProp.notations.
Set Printing Depth 100000.
Set Printing Width 250.

Definition zzexp_instrs : list AST :=
  [ RTYPE A0 X0 A2 RISCV_SLTU              (* snez a2, a0     *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI  (* addi a2, a2, -1 *)
  ; BNE A2 X0 (bv.of_N 8)                  (* bne  a2, x0, +8 -> out of instrs = exit *)
  ; NOP
  ].

Definition zzexp_reg_specs : list reg_spec :=
  [(A0, true, None); (A2, true, None)].

Definition zzexp_contract (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_param ia zzexp_reg_specs [] zzexp_instrs []
    (pcOutOfInstrs_exitCond ia zzexp_instrs) 8.

(* Postprocessed: ~96% of raw nodes are discarded, so this is the readable
   one.  It is also the shape the SOLVER has already had a pass over, which
   is itself worth knowing — a raw dump is in ZZExpandDumpRaw.v. *)
Eval vm_compute in
  (cfg_map (zzexp_contract 0) (fun ia p exits P i ec fl =>
     postprocess (CFG_VC_triple p exits P i fl))).
