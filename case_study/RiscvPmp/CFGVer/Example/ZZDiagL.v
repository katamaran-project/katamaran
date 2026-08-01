(* ========================================================================= *)
(* ZZDiagL.v — THROWAWAY.  Body-length x trip-count factorial.                *)
(*                                                                           *)
(* alloc(N) has an exact quadratic term at body length L=14.  Is the         *)
(* quadratic in TRIPS^2 or in TOTAL-STEPS^2 (= (L*N)^2)?  Fit the quadratic  *)
(* coefficient c(L) at three body lengths and see how it scales:             *)
(*   c(L) ~ L    => quadratic is L * trips^2   (per-trip cost grows w/ trips) *)
(*   c(L) ~ L^2  => quadratic is (L*N)^2       (per-step cost grows w/ steps) *)
(*                                                                           *)
(* All three share zzf's design: A3 is NOT advanced, so exactly one memory    *)
(* cell for every N, and A0 is written from A1 so every term stays O(1).     *)
(* Only the number of leading `addi a0,a1,1` changes.                        *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZDiagCommon.

Definition zz_addi : AST := ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI.

Definition zz_tail (back : bv 13) : list AST :=
  [ STORE (bv.of_Z 0) A0 A3 WORD
  ; ITYPE (bv.of_Z 0) A3 A3 RISCV_ADDI
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 back ].

(* L = 9: 5 addi + 4 tail.  BNE sits at index 8, byte offset 32, so the
   backward displacement to offset 0 is -32, i.e. 2^13 - 32 = 8160. *)
Definition zz9_instrs : list AST :=
  List.repeat zz_addi 5 ++ zz_tail (bv.of_N 8160).

(* L = 24: 20 addi + 4 tail.  BNE at index 23, offset 92 -> 2^13 - 92 = 8100. *)
Definition zz24_instrs : list AST :=
  List.repeat zz_addi 20 ++ zz_tail (bv.of_N 8100).

(* Fuel is generous: the ablation showed excess fuel costs +0.04% at 4.4x. *)
Definition zzL_contract (instrs : list AST) (n : nat)
  : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs n) [(56%N, false, PVExist)]
    instrs [] 60
    (pcOutOfInstrs_exitCond 0 instrs)
    (30 * n + 40).

Definition zz9_dc  (n : nat) : DC :=
  cfg_map (zzL_contract zz9_instrs n) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).

Definition zz24_dc (n : nat) : DC :=
  cfg_map (zzL_contract zz24_instrs n) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).
