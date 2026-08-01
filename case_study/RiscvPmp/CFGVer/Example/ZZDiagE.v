(* THROWAWAY: HYPOTHESIS TEST.
   sexec_cfg_addr re-persists BOTH tables at every step (Verifier.v:369):
     sexec_cfg_addr n' (persist_itableW θ1 tbl) (persist_etable θ1 exits) ...
   and is_exit does a peval-compare against every exit entry per step.
   So exit-table size is a per-step cost knob that does NOT change the number
   of steps, the heap, the instruction table, or the tree.

   Δ(N) = alloc(24 extra exits, N) − alloc(0 extra exits, N):
     Δ linear in N    => per-step cost is CONSTANT  => hypothesis REFUTED
     Δ quadratic in N => per-step cost grows with steps taken => CONFIRMED

   Offsets 100..192 step 4: 24 entries, none colliding with the real
   instruction offsets 0..52 or the real exit at 56, so is_exit still fails
   on every one and the tree must be unchanged (census is the control). *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZDiagCommon.

Definition extra_exits_24 : list N :=
  List.map (fun k => (100 + 4 * N.of_nat k)%N) (List.seq 0 24).

Definition zze_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs n) [(56%N, false, PVExist)]
    zzf_instrs extra_exits_24 60
    (pcOutOfInstrs_exitCond 0 zzf_instrs) (14 * n + 12).

Definition zze_dc (n : nat) : DC :=
  cfg_map (zze_contract n) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).
