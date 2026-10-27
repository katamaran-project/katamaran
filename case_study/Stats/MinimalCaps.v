(* Size statistics of the verification conditions of the MinimalCaps case study:
   the raw symbolic execution tree vs. the VC after postprocessing. *)

From Stdlib Require Import
     NArith.NArith
     Strings.String
     Lists.List.
From Katamaran Require Import
     Base
     MinimalCaps.Machine
     MinimalCaps.Logic
     MinimalCaps.Sig
     MinimalCaps.Contracts.Definitions.

Import MinCapsSignature.
Import MinCapsProgram.
Import MinCapsSpecification.
Import MinCapsProgramLogic.
Import MinCapsExecutor.
Import Symbolic.Statistics.

Ltac show name t :=
  let r := eval vm_compute in (vc_stats_to_list t) in idtac name r.

Goal True.
  Time show "VCSTAT read_reg fuel=1" (vc_stats 1 read_reg).
  Time show "VCSTAT read_reg_cap fuel=1" (vc_stats 1 read_reg_cap).
  Time show "VCSTAT read_reg_num fuel=1" (vc_stats 1 read_reg_num).
  Time show "VCSTAT write_reg fuel=1" (vc_stats 1 write_reg).
  Time show "VCSTAT next_pc fuel=1" (vc_stats 1 next_pc).
  Time show "VCSTAT update_pc fuel=1" (vc_stats 1 update_pc).
  Time show "VCSTAT update_pc_perm fuel=1" (vc_stats 1 update_pc_perm).
  Time show "VCSTAT is_correct_pc fuel=1" (vc_stats 1 is_correct_pc).
  Time show "VCSTAT is_perm fuel=1" (vc_stats 1 MinCapsProgram.is_perm).
  Time show "VCSTAT add_pc fuel=1" (vc_stats 1 add_pc).
  Time show "VCSTAT read_mem fuel=1" (vc_stats 1 read_mem).
  Time show "VCSTAT write_mem fuel=1" (vc_stats 1 write_mem).
  Time show "VCSTAT read_allowed fuel=1" (vc_stats 1 read_allowed).
  Time show "VCSTAT write_allowed fuel=1" (vc_stats 1 write_allowed).
  Time show "VCSTAT within_bounds fuel=1" (vc_stats 1 within_bounds).
  Time show "VCSTAT perm_to_bits fuel=1" (vc_stats 1 perm_to_bits).
  Time show "VCSTAT perm_from_bits fuel=1" (vc_stats 1 perm_from_bits).
  Time show "VCSTAT and_perm fuel=1" (vc_stats 1 and_perm).
  Time show "VCSTAT is_sub_perm fuel=1" (vc_stats 1 is_sub_perm).
  Time show "VCSTAT is_within_range fuel=1" (vc_stats 1 is_within_range).
  Time show "VCSTAT abs fuel=1" (vc_stats 1 abs).
  Time show "VCSTAT is_not_zero fuel=1" (vc_stats 1 is_not_zero).
  Time show "VCSTAT can_incr_cursor fuel=1" (vc_stats 1 can_incr_cursor).
  Time show "VCSTAT exec_jalr_cap fuel=1" (vc_stats 1 exec_jalr_cap).
  Time show "VCSTAT exec_cjalr fuel=1" (vc_stats 1 exec_cjalr).
  Time show "VCSTAT exec_cjal fuel=1" (vc_stats 1 exec_cjal).
  Time show "VCSTAT exec_bne fuel=1" (vc_stats 1 exec_bne).
  Time show "VCSTAT exec_ld fuel=1" (vc_stats 1 exec_ld).
  Time show "VCSTAT exec_sd fuel=1" (vc_stats 1 exec_sd).
  Time show "VCSTAT exec_addi fuel=1" (vc_stats 1 exec_addi).
  Time show "VCSTAT exec_add fuel=1" (vc_stats 1 exec_add).
  Time show "VCSTAT exec_sub fuel=1" (vc_stats 1 exec_sub).
  Time show "VCSTAT exec_slt fuel=1" (vc_stats 1 exec_slt).
  Time show "VCSTAT exec_slti fuel=1" (vc_stats 1 exec_slti).
  Time show "VCSTAT exec_sltu fuel=1" (vc_stats 1 exec_sltu).
  Time show "VCSTAT exec_sltiu fuel=1" (vc_stats 1 exec_sltiu).
  Time show "VCSTAT exec_cmove fuel=1" (vc_stats 1 exec_cmove).
  Time show "VCSTAT exec_cincoffset fuel=1" (vc_stats 1 exec_cincoffset).
  Time show "VCSTAT exec_candperm fuel=1" (vc_stats 1 exec_candperm).
  Time show "VCSTAT exec_csetbounds fuel=1" (vc_stats 1 exec_csetbounds).
  Time show "VCSTAT exec_csetboundsimm fuel=1" (vc_stats 1 exec_csetboundsimm).
  Time show "VCSTAT exec_cgettag fuel=1" (vc_stats 1 exec_cgettag).
  Time show "VCSTAT exec_cgetperm fuel=1" (vc_stats 1 exec_cgetperm).
  Time show "VCSTAT exec_cgetbase fuel=1" (vc_stats 1 exec_cgetbase).
  Time show "VCSTAT exec_cgetlen fuel=1" (vc_stats 1 exec_cgetlen).
  Time show "VCSTAT exec_cgetaddr fuel=1" (vc_stats 1 exec_cgetaddr).
  Time show "VCSTAT exec_fail fuel=1" (vc_stats 1 exec_fail).
  Time show "VCSTAT exec_ret fuel=1" (vc_stats 1 exec_ret).
  Time show "VCSTAT exec_instr fuel=1" (vc_stats 1 exec_instr).
  Time show "VCSTAT exec fuel=1" (vc_stats 1 exec).
  Time show "VCSTAT step fuel=1" (vc_stats 1 step).
Abort.
