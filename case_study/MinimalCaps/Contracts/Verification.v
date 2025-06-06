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
     MinimalCaps.Machine
     MinimalCaps.Sig
     MinimalCaps.Contracts.Definitions
     Notations
     Specification
     MicroSail.ShallowExecutor
     MicroSail.SymbolicExecutor
     Symbolic.Solver.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Import MinCapsSpecification.

Module Import MinCapsExecutor :=
  MakeExecutor MinCapsBase MinCapsSignature MinCapsProgram MinCapsSpecification.
Module Import MinCapsShallowExec :=
  MakeShallowExecutor MinCapsBase MinCapsSignature MinCapsProgram MinCapsSpecification.

(*** MinCapsValidContracts ***)
(* In this module we prove that all specified contracts are valid. *)
Module MinCapsValidContracts.
  Import MinCapsExecutor.
  Import MinCapsSignature.

  Local Ltac solve :=
    repeat
      (repeat
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | H: Empty_set |- _ => destruct H
         | |- forall _, _ => cbn [Val snd]; intro
         | |- False \/ _ =>  right
         | |- _ \/ False =>  left
         | |- _ \/ exists _, _ =>  left (* avoid existentials, bit fishy but fine for now *)
         | |- _ /\ _ => constructor
         | |- VerificationCondition _ =>
             constructor;
             cbv [SymProp.safe env.remove env.lookup bop.eval is_true
                               inst inst_term instprop_formula env.Env_rect];
             cbn
         | |- Obligation _ _ _ => constructor; cbn
         | |- Debug _ _ => constructor
         | |- Debug _ True \/ _ => left
         | |- (_ \/ _) \/ _ => rewrite or_assoc
         | |- context[Z.leb ?x ?y] =>
             destruct (Z.leb_spec x y)
         end;
       cbn [List.length andb is_true Val snd];
       subst; try congruence; try lia;
       auto
      ).

  Import MinCapsContractNotations.

  Definition ValidContractReflect {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractReflect c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithErasure {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractWithErasure c (FunDef f)
    | None => False
    end.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContract c (FunDef f)
    | None => False
    end.

  Ltac symbolic_simpl :=
    apply Symbolic.validcontract_with_erasure_sound;
    compute;
    constructor;
    cbn.

  Lemma valid_contract_read_reg : ValidContractReflect read_reg.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_reg_cap : ValidContractReflect read_reg_cap.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_reg_num : ValidContractReflect read_reg_num.
  Proof. reflexivity. Qed.

  Lemma valid_contract_write_reg : ValidContractReflect write_reg.
  Proof. reflexivity. Qed.

  Lemma valid_contract_next_pc : ValidContractReflect next_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_update_pc : ValidContractReflect update_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_update_pc_perm : ValidContractReflect update_pc_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_correct_pc : ValidContractReflect is_correct_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_perm : ValidContractReflect MinCapsProgram.is_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_add_pc : ValidContractReflect add_pc.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_mem : ValidContractReflect read_mem.
  Proof. reflexivity. Qed.

  Lemma valid_contract_write_mem : ValidContractReflect write_mem.
  Proof. reflexivity. Qed.

  Lemma valid_contract_read_allowed : ValidContractReflect read_allowed.
  Proof. reflexivity. Qed.

  Lemma valid_contract_write_allowed : ValidContractReflect write_allowed.
  Proof. reflexivity. Qed.

  Lemma valid_contract_within_bounds : ValidContractReflect within_bounds.
  Proof. reflexivity. Qed.

  Lemma valid_contract_perm_to_bits : ValidContractReflect perm_to_bits.
  Proof. reflexivity. Qed.

  Lemma valid_contract_perm_from_bits : ValidContractReflect perm_from_bits.
  Proof. reflexivity. Qed.

  Lemma valid_contract_and_perm : ValidContractReflect and_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_sub_perm : ValidContractReflect is_sub_perm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_within_range : ValidContractReflect is_within_range.
  Proof. reflexivity. Qed.

  Lemma valid_contract_abs : ValidContractReflect abs.
  Proof. reflexivity. Qed.

  Lemma valid_contract_is_not_zero : ValidContractReflect is_not_zero.
  Proof. reflexivity. Qed.

  Lemma valid_contract_can_incr_cursor : ValidContractReflect can_incr_cursor.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_jalr_cap : ValidContractReflect exec_jalr_cap.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cjalr : ValidContractReflect exec_cjalr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cjal : ValidContractReflect exec_cjal.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_bne : ValidContractReflect exec_bne.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cmove : ValidContractReflect exec_cmove.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_ld : ValidContractReflect exec_ld.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sd : ValidContractReflect exec_sd.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cincoffset : ValidContractReflect exec_cincoffset.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_candperm : ValidContractReflect exec_candperm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_csetbounds : ValidContractReflect exec_csetbounds.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_csetboundsimm : ValidContractReflect exec_csetboundsimm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgettag : ValidContractReflect exec_cgettag.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_addi : ValidContractReflect exec_addi.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_add : ValidContractReflect exec_add.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sub : ValidContractReflect exec_sub.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_slt : ValidContractReflect exec_slt.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_slti : ValidContractReflect exec_slti.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sltu : ValidContractReflect exec_sltu.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_sltiu : ValidContractReflect exec_sltiu.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetperm : ValidContractReflect exec_cgetperm.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetbase : ValidContractReflect exec_cgetbase.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetlen : ValidContractReflect exec_cgetlen.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_cgetaddr : ValidContractReflect exec_cgetaddr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_fail : ValidContractReflect exec_fail.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_ret : ValidContractReflect exec_ret.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec_instr : ValidContractReflect exec_instr.
  Proof. reflexivity. Qed.

  Lemma valid_contract_exec : ValidContractReflect exec.
  Proof. reflexivity. Qed.

  Lemma valid_contract_step : ValidContractReflect step.
  Proof. reflexivity. Qed.

  Lemma valid_contract_reflect : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractReflect f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractReflect in Hvc.
    rewrite Hcenv in Hvc.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContract f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    apply Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros; destruct f.
    - apply (valid_contract_reflect _ H valid_contract_read_reg).
    - apply (valid_contract_reflect _ H valid_contract_read_reg_cap).
    - apply (valid_contract_reflect _ H valid_contract_read_reg_num).
    - apply (valid_contract_reflect _ H valid_contract_write_reg).
    - apply (valid_contract_reflect _ H valid_contract_next_pc).
    - apply (valid_contract_reflect _ H valid_contract_update_pc).
    - apply (valid_contract_reflect _ H valid_contract_update_pc_perm).
    - apply (valid_contract_reflect _ H valid_contract_is_correct_pc).
    - apply (valid_contract_reflect _ H valid_contract_is_perm).
    - apply (valid_contract_reflect _ H valid_contract_add_pc).
    - apply (valid_contract_reflect _ H valid_contract_read_mem).
    - apply (valid_contract_reflect _ H valid_contract_write_mem).
    - apply (valid_contract_reflect _ H valid_contract_read_allowed).
    - apply (valid_contract_reflect _ H valid_contract_write_allowed).
    - apply (valid_contract_reflect _ H valid_contract_within_bounds).
    - apply (valid_contract_reflect _ H valid_contract_perm_to_bits).
    - apply (valid_contract_reflect _ H valid_contract_perm_from_bits).
    - apply (valid_contract_reflect _ H valid_contract_and_perm).
    - apply (valid_contract_reflect _ H valid_contract_is_sub_perm).
    - apply (valid_contract_reflect _ H valid_contract_is_within_range).
    - apply (valid_contract_reflect _ H valid_contract_abs).
    - apply (valid_contract_reflect _ H valid_contract_is_not_zero).
    - apply (valid_contract_reflect _ H valid_contract_can_incr_cursor).
    - apply (valid_contract_reflect _ H valid_contract_exec_jalr_cap).
    - apply (valid_contract_reflect _ H valid_contract_exec_cjalr).
    - apply (valid_contract_reflect _ H valid_contract_exec_cjal).
    - apply (valid_contract_reflect _ H valid_contract_exec_bne).
    - apply (valid_contract_reflect _ H valid_contract_exec_ld).
    - apply (valid_contract_reflect _ H valid_contract_exec_sd).
    - apply (valid_contract_reflect _ H valid_contract_exec_addi).
    - apply (valid_contract_reflect _ H valid_contract_exec_add).
    - apply (valid_contract_reflect _ H valid_contract_exec_sub).
    - apply (valid_contract_reflect _ H valid_contract_exec_slt).
    - apply (valid_contract_reflect _ H valid_contract_exec_slti).
    - apply (valid_contract_reflect _ H valid_contract_exec_sltu).
    - apply (valid_contract_reflect _ H valid_contract_exec_sltiu).
    - apply (valid_contract_reflect _ H valid_contract_exec_cmove).
    - apply (valid_contract_reflect _ H valid_contract_exec_cincoffset).
    - apply (valid_contract_reflect _ H valid_contract_exec_candperm).
    - apply (valid_contract_reflect _ H valid_contract_exec_csetbounds).
    - apply (valid_contract_reflect _ H valid_contract_exec_csetboundsimm).
    - apply (valid_contract_reflect _ H valid_contract_exec_cgettag).
    - apply (valid_contract_reflect _ H valid_contract_exec_cgetperm).
    - apply (valid_contract_reflect _ H valid_contract_exec_cgetbase).
    - apply (valid_contract_reflect _ H valid_contract_exec_cgetlen).
    - apply (valid_contract_reflect _ H valid_contract_exec_cgetaddr).
    - apply (valid_contract_reflect _ H valid_contract_exec_fail).
    - apply (valid_contract_reflect _ H valid_contract_exec_ret).
    - apply (valid_contract_reflect _ H valid_contract_exec_instr).
    - apply (valid_contract_reflect _ H valid_contract_exec).
    - apply (valid_contract_reflect _ H valid_contract_step).
    - cbn in H; inversion H.
  Qed.


(*   Goal True. idtac "Timing before: minimalcaps". Abort. *)
(*   Lemma valid_contracts : forall {Δ τ} (f : Fun Δ τ), *)
(*       ValidContractReflect f. *)
(*   Proof. *)
(*   (* destruct f; reflexivity. *)
(* Qed. *) *)
(*   Admitted. *)
(*   Goal True. idtac "Timing after: minimalcaps". Abort. *)

  Goal True. idtac "Assumptions for minimalcaps contracts:". Abort.
  Print Assumptions ValidContracts.
End MinCapsValidContracts.
