(* ========================================================================= *)
(* ZZCommon.v — THROWAWAY diagnostic support file (delete after use).         *)
(*                                                                           *)
(* Definitions only, no vm_compute: the flat reproducer plus the SymProp node *)
(* census.  Split out from ZZProbeNodes.v because running several heavy Evals *)
(* in ONE coqc process contaminates their timings -- the same computation     *)
(* measured 0.68/1.09/1.13 s at N=1 and 15.9/16.2/20.8 s at N=4 across runs,  *)
(* and within-run growth ratios flipped direction between runs (5.08->5.99 in *)
(* one, 5.72->2.60 in another).  Peak RSS differed 3.30 vs 5.35 GB, so later  *)
(* Evals run under materially different GC conditions.                       *)
(*                                                                           *)
(* So: ONE Eval per process.  ZZRun1/ZZRun2/ZZRun4.v each require this file   *)
(* and do exactly one measurement.                                          *)
(* ========================================================================= *)

(* Export, not Import: downstream probe files need Prelude's notations (𝕊, the
   N numeral scope).  With a bare Import they printed raw BinNums and could not
   even name 𝕊 -- the Require-vs-Require-Import landmine in CFGVer/CLAUDE.md. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzn_back_offset : bv 13 := bv.of_N 8140.

(* 10x `addi a0, a1, 1` -- A0 written from A1, never from itself, so every
   symbolic term stays O(1) forever -- then key_schedule_loop2's tail verbatim. *)
Definition zzn_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; STORE (bv.of_Z 0) A0 A3 WORD
  ; ITYPE (bv.of_Z 4) A3 A3 RISCV_ADDI
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzn_back_offset
  ].

Definition zzn_reg_specs (n : nat) : list reg_spec_rel :=
  [(A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist);
   (A3, false, PVBaseOff 56);
   (A4, true, PVConst (bv.of_N (N.of_nat n)))].

Definition zzn_mem_specs (n : nat) : list mem_spec_rel :=
  List.map (fun k => ((56 + 4 * N.of_nat k)%N, false, PVExist)) (List.seq 0 n).

Definition zzn_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs n) (zzn_mem_specs n)
    zzn_instrs [] (56 + 4 * N.of_nat n)%N
    (pcOutOfInstrs_exitCond 0 zzn_instrs) (14 * n + 12).

Record NC : Set := MkNC
  { nc_angbin     : N
  ; nc_dembin     : N
  ; nc_blockchild : N   (* binary nodes with a `block` child = solver-killed forks *)
  ; nc_block      : N
  ; nc_error      : N
  ; nc_assertk    : N
  ; nc_assumek    : N
  ; nc_angelicv   : N
  ; nc_demonicv   : N
  ; nc_asserteq   : N
  ; nc_assumeeq   : N
  ; nc_debug      : N
  }.

Definition ncadd (a b : NC) : NC :=
  MkNC (nc_angbin a + nc_angbin b) (nc_dembin a + nc_dembin b)
       (nc_blockchild a + nc_blockchild b) (nc_block a + nc_block b)
       (nc_error a + nc_error b) (nc_assertk a + nc_assertk b)
       (nc_assumek a + nc_assumek b) (nc_angelicv a + nc_angelicv b)
       (nc_demonicv a + nc_demonicv b) (nc_asserteq a + nc_asserteq b)
       (nc_assumeeq a + nc_assumeeq b) (nc_debug a + nc_debug b).

Definition is_block {Σ} (s : 𝕊 Σ) : N :=
  match s with SymProp.block => 1 | _ => 0 end.

(* Arms mirror SymProp.Statistics.size exactly (Propositions.v:1020). *)
Fixpoint ncount {Σ} (s : 𝕊 Σ) : NC :=
  match s with
  | SymProp.angelic_binary o1 o2 =>
      ncadd (MkNC 1 0 (is_block o1 + is_block o2) 0 0 0 0 0 0 0 0 0)
            (ncadd (ncount o1) (ncount o2))
  | SymProp.demonic_binary o1 o2 =>
      ncadd (MkNC 0 1 (is_block o1 + is_block o2) 0 0 0 0 0 0 0 0 0)
            (ncadd (ncount o1) (ncount o2))
  | SymProp.error msg => MkNC 0 0 0 0 1 0 0 0 0 0 0 0
  | SymProp.block     => MkNC 0 0 0 1 0 0 0 0 0 0 0 0
  | SymProp.assertk fml msg k => ncadd (MkNC 0 0 0 0 0 1 0 0 0 0 0 0) (ncount k)
  | SymProp.assumek fml k     => ncadd (MkNC 0 0 0 0 0 0 1 0 0 0 0 0) (ncount k)
  | SymProp.angelicv b k      => ncadd (MkNC 0 0 0 0 0 0 0 1 0 0 0 0) (ncount k)
  | SymProp.demonicv b k      => ncadd (MkNC 0 0 0 0 0 0 0 0 1 0 0 0) (ncount k)
  | @SymProp.assert_vareq _ x σ xIn t msg k =>
      ncadd (MkNC 0 0 0 0 0 0 0 0 0 1 0 0) (ncount k)
  | @SymProp.assume_vareq _ x σ xIn t k =>
      ncadd (MkNC 0 0 0 0 0 0 0 0 0 0 1 0) (ncount k)
  | SymProp.debug b k         => ncadd (MkNC 0 0 0 0 0 0 0 0 0 0 0 1) (ncount k)
  end.

Definition zzn_raw_nc (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (CFG_VC_triple p exits P i fl)).
