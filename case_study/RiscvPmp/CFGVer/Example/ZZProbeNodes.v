(* ========================================================================= *)
(* ZZProbeNodes.v — THROWAWAY diagnostic probe (delete after use).           *)
(*                                                                           *)
(* Question: is the planned A1 ablation (null solver_generic's fact list)    *)
(* CONFOUNDED by path explosion?  A1 destroys the solver's ability to refute *)
(* a branch against the ACCUMULATED path condition, so any fork whose dead   *)
(* side is only refutable that way would stop being pruned -- inflating the  *)
(* tree for a reason unrelated to the walk's cost.                           *)
(*                                                                           *)
(* This measures how much branch-pruning the solver is ACTUALLY doing in the *)
(* baseline.  It works because we count the RAW tree, before `prune`: a      *)
(* solver-killed fork is still visible there as a binary node with a         *)
(* SymProp.block child (assume_pathcondition returns block when              *)
(* combined_solver says None).                                              *)
(*                                                                           *)
(* Reading the result:                                                       *)
(*   nc_blockchild ~ 0  => no forks are being killed by the solver; every    *)
(*                         branch is resolved by peval before a fork is      *)
(*                         built.  A1 cannot cause path explosion => SAFE.   *)
(*   nc_blockchild > 0  => the solver IS pruning forks; A1 is confounded =>  *)
(*                         use the fact-list TRUNCATION variant instead      *)
(*                         (window k over wco, with `size` as a built-in     *)
(*                         explosion detector).                              *)
(*                                                                           *)
(* NOTE nc_angbin will NOT be ~0: the CFG executor makes an angelic          *)
(* exit-vs-execute choice at every step by design.  The discriminating       *)
(* metric is nc_blockchild, not the raw binary count.                        *)
(*                                                                           *)
(* nc_angelicv/nc_demonicv are recorded too: they count logic variables,     *)
(* i.e. they measure |wctx| growth directly -- the other surviving suspect   *)
(* (wco persistence across world extensions) scales with that.               *)
(*                                                                           *)
(* Subject: the growing-heap baseline from ZZProbeHeap.v (variant G), which  *)
(* is the faithful key_schedule_loop2 shape with the ALU chain flattened.    *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition zzn_back_offset : bv 13 := bv.of_N 8140.

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

(* ---------------------------------------------------------------------- *)
(* Node-kind census.  One traversal, one Eval, so the (expensive) raw     *)
(* tree is built only once per N.                                        *)
(* ---------------------------------------------------------------------- *)

Record NC : Set := MkNC
  { nc_angbin     : N   (* angelic_binary  -- exit-vs-execute choice, expected linear *)
  ; nc_dembin     : N   (* demonic_binary                                            *)
  ; nc_blockchild : N   (* binary nodes with a `block` child = SOLVER-KILLED FORKS    *)
  ; nc_block      : N
  ; nc_error      : N
  ; nc_assertk    : N
  ; nc_assumek    : N
  ; nc_angelicv   : N   (* angelic logic vars  -- |wctx| growth                       *)
  ; nc_demonicv   : N   (* demonic logic vars  -- |wctx| growth                       *)
  ; nc_asserteq   : N
  ; nc_assumeeq   : N
  ; nc_debug      : N
  }.

Definition nc0 : NC := MkNC 0 0 0 0 0 0 0 0 0 0 0 0.

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

Goal True. idtac "ZZ === raw node census, N=1 ===". exact I. Qed.
Time Eval vm_compute in (zzn_raw_nc 1).

Goal True. idtac "ZZ === raw node census, N=2 ===". exact I. Qed.
Time Eval vm_compute in (zzn_raw_nc 2).

Goal True. idtac "ZZ === raw node census, N=4 ===". exact I. Qed.
Time Eval vm_compute in (zzn_raw_nc 4).
