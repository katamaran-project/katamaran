(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.ZArith
     Classes.EquivDec
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Specification
     MinimalCaps.Machine
     MinimalCaps.Contracts.Verification.

Section Statistics.
  Import MinCapsExecutor.
  Import List.ListNotations.

  Definition all_functions : list { Δ & { σ & Fun Δ σ } } :=
    [ existT _ (existT _ read_reg);
      existT _ (existT _ read_reg_cap);
      existT _ (existT _ read_reg_num);
      existT _ (existT _ write_reg);
      existT _ (existT _ next_pc);
      existT _ (existT _ update_pc);
      existT _ (existT _ add_pc);
      existT _ (existT _ read_mem);
      existT _ (existT _ write_mem);
      existT _ (existT _ read_allowed);
      existT _ (existT _ write_allowed);
      existT _ (existT _ within_bounds);
      existT _ (existT _ perm_to_bits);
      existT _ (existT _ perm_from_bits);
      existT _ (existT _ and_perm);
      existT _ (existT _ is_sub_perm);
      existT _ (existT _ is_within_range);
      existT _ (existT _ abs);
      existT _ (existT _ is_not_zero);
      existT _ (existT _ can_incr_cursor);
      existT _ (existT _ exec_jalr_cap);
      existT _ (existT _ exec_cjalr);
      existT _ (existT _ exec_cjal);
      existT _ (existT _ exec_bne);
      existT _ (existT _ exec_cmove);
      existT _ (existT _ exec_ld);
      existT _ (existT _ exec_sd);
      existT _ (existT _ exec_cincoffset);
      existT _ (existT _ exec_candperm);
      existT _ (existT _ exec_csetbounds);
      existT _ (existT _ exec_csetboundsimm);
      existT _ (existT _ exec_cgettag);
      existT _ (existT _ exec_addi);
      existT _ (existT _ exec_add);
      existT _ (existT _ exec_sub);
      existT _ (existT _ exec_slt);
      existT _ (existT _ exec_slti);
      existT _ (existT _ exec_sltu);
      existT _ (existT _ exec_sltiu);
      existT _ (existT _ exec_cgetperm);
      existT _ (existT _ exec_cgetbase);
      existT _ (existT _ exec_cgetlen);
      existT _ (existT _ exec_cgetaddr);
      existT _ (existT _ exec_fail);
      existT _ (existT _ exec_ret);
      existT _ (existT _ exec_instr);
      existT _ (existT _ exec);
      existT _ (existT _ step);
      existT _ (existT _ loop)
    ]%list.

  Definition symbolic_stats : Stats :=
    List.fold_right
      (fun '(existT _ (existT _ f)) r =>
         match Symbolic.Statistics.calc f with
         | Some s => plus_stats s r
         | None   => r
         end)
      empty_stats
      all_functions.

  Goal True.
    idtac "Symbolic branching statistics:".
    let t := eval compute in symbolic_stats in idtac t.
  Abort.

  (* The counting of the shallow nodes is too slow in Ltac. Hence there is and
     alternative command line solution. *)

End Statistics.
