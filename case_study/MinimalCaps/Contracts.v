(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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

From MinimalCaps Require Import
     Machine.

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     SemiConcrete.Outcome
     Sep.Spec
     Symbolic.Mutator
     Syntax.

From MicroSail Require Environment.
From MicroSail Require Sep.Logic.
From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.proofmode Require tactics.
From stdpp Require namespaces.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope ctx_scope.

Inductive Predicate : Set :=
  ptsreg
| ptsto
| safe.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module Export MinCapsAssertionKit <:
  (AssertionKit MinCapsTermKit MinCapsProgramKit).

  Export MinCapsProgramKit.

  Definition 𝑷 := Predicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | ptsreg => [ty_enum regname, ty_word]
    | ptsto => [ty_addr, ty_int]
    | safe => [ty_word]
    end.
  Instance 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.
End MinCapsAssertionKit.

Module MinCapsSymbolicContractKit <:
  SymbolicContractKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.
  Module Export ASS := Assertions MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

  Open Scope env_scope.

  Local Notation "r '↦r' t" := (asn_chunk (chunk_pred ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t)))) (at level 100).
  Local Notation "a '↦m' t" := (asn_chunk (chunk_pred ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t)))) (at level 100).
  (* Arguments asn_prop [_] & _. *)

  (*
      @pre true;
      @post result = (p = r ∨ p = rw);
      bool read_allowed(p : perm);

      @pre true;
      @post result = (p = rw);
      bool write_allowed(p : perm);

      @pre true;
      @post result = (e = none ∨ ∃ e'. e = inl e' ∧ e' >= a);
      bool upper_bound(a : addr, e : option addr);

      @pre true;
      @post ∃ b,e,a,p. c = mkcap(b,e,a,p) ∧ result = (a >= b && (e = none ∨ e = inl e' ∧ e' >= a));
      bool within_bounds(c : capability);

      regInv(r) = ∃ w : word. r ↦ w * safe(w)
      machInv = regInv(r1) * regInv(r2) * regInv(r3) * regInv(r4) * ∃ c : cap. pc ↦ c * safe(c)

      @pre machInv;
      @post machInv;
      bool exec_sd(lv : lv, hv : memval, immediate : Z)

      @pre machInv;
      @post machInv;
      bool exec_ld(lv : lv, hv : memval, immediate : Z)

      @pre machInv;
      @post machInv;
      bool exec_jr(lv : lv)

      @pre machInv;
      @post machInv;
      bool exec_bnez(lv : lv, immediate : Z)

      @pre machInv;
      @post machInv;
      bool exec_mv(lv : lv, rv : ty_rv)

      @pre machInv;
      @post machInv;
      bool exec_ret

      @pre machInv;
      @post machInv;
      bool exec_instr(i : instr)

      @pre machInv;
      @post machInv;
      bool exec

      @pre machInv;
      @post machInv;
      unit loop
   *)

  Definition sep_contract_read_reg : SepContract ["reg" ∶ ty_enum regname ] ty_word :=
    {| sep_contract_logic_variables := ["reg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "reg"]%arg;
       sep_contract_precondition    := term_var "reg" ↦r term_var "w";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         (asn_eq (term_var "w") (term_var "result") ✱
                 term_var "reg" ↦r term_var "w")
    |}.

  Definition sep_contract_read_reg_cap : SepContract ["reg" ∶ ty_enum regname ] ty_cap :=
    {| sep_contract_logic_variables := ["reg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "reg"]%arg;
       sep_contract_precondition    := term_var "reg" ↦r term_var "w";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         (asn_exist "c" ty_cap (
                      asn_eq (term_var "result") (term_var "c") ✱
                             asn_eq (term_var "w") (term_inr (term_var "c"))
                    ) ✱ 
                    term_var "reg" ↦r term_var "w")
    |}.

  Definition sep_contract_read_reg_num : SepContract ["reg" ∶ ty_enum regname ] ty_int :=
    {| sep_contract_logic_variables := ["reg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "reg"]%arg;
       sep_contract_precondition    := term_var "reg" ↦r term_var "w";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         (asn_exist "n" ty_int (
                      asn_eq (term_var "result") (term_var "n") ✱
                             asn_eq (term_var "w") (term_inl (term_var "n"))
                    ) ✱
                    term_var "reg" ↦r term_var "w")
    |}.

  Definition sep_contract_write_reg : SepContract ["reg" ∶ ty_enum regname, "w"  ∶ ty_word] ty_unit :=
    {| sep_contract_logic_variables := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "wo" ∶ ty_word];
       sep_contract_localstore      := [term_var "reg", term_var "w"]%arg;
       sep_contract_precondition    := term_var "reg" ↦r term_var "wo";
       sep_contract_result          := "result";
       sep_contract_postcondition   := term_var "reg" ↦r term_var "w";
    |}.

  Definition sep_contract_next_pc : SepContract ctx_nil ty_cap :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         pc ↦ term_var "opc" ✱
            asn_eq (term_var "result")
            (term_record capability
                         [ (term_projrec (term_var "opc") "cap_permission"),
                           (term_projrec (term_var "opc") "cap_begin"),
                           (term_projrec (term_var "opc") "cap_end"),
                           (term_binop binop_plus (term_projrec (term_var "opc") "cap_cursor") (term_lit ty_int 1))]);
    |}.

  Definition sep_contract_update_pc : SepContract ctx_nil ty_unit :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap ];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_exist "npc" ty_cap (pc ↦ term_var "npc")
    |}.

  Definition sep_contract_read_mem : SepContract ["a" ∶ ty_addr ] ty_memval :=
    {| sep_contract_logic_variables := ["a" ∶ ty_addr, "n" ∶ ty_int];
       sep_contract_localstore      := [term_var "a"]%arg;
       sep_contract_precondition    := term_var "a" ↦m term_var "n";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         term_var "a" ↦m term_var "n" ✱
                  asn_eq (term_var "result") (term_var "n");
    |}.

  Definition sep_contract_write_mem : SepContract ["a" ∶ ty_addr, "v" ∶ ty_memval ] ty_unit :=
    {| sep_contract_logic_variables := ["a" ∶ ty_addr, "v" ∶ ty_memval, "ov" ∶ ty_memval];
       sep_contract_localstore      := [term_var "a", term_var "v"]%arg;
       sep_contract_precondition    := term_var "a" ↦m term_var "ov";
       sep_contract_result          := "result";
       sep_contract_postcondition   := term_var "a" ↦m term_var "v";
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_reg     => Some sep_contract_read_reg
      | read_reg_cap => Some sep_contract_read_reg_cap
      | read_reg_num => Some sep_contract_read_reg_num
      | write_reg    => Some sep_contract_write_reg
      | next_pc      => Some sep_contract_next_pc
      | update_pc    => Some sep_contract_update_pc
      | read_mem     => Some sep_contract_read_mem
      | write_mem    => Some sep_contract_write_mem
      | _            => None
      end.

  Definition sep_contract_open_ptsreg : SepContract ["reg" ∶ ty_enum regname] ty_unit :=
    {| sep_contract_logic_variables := [ "r" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "r"]%arg;
       sep_contract_precondition    := term_var "r" ↦r term_var "w";
       sep_contract_result          := "result_open_ptsreg";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_open_ptsreg") (term_lit ty_unit tt) ✱
         asn_match_enum
           regname (term_var "r")
           (fun k => match k with
                     | R0 => reg0 ↦ term_var "w"
                     | R1 => reg1 ↦ term_var "w"
                     | R2 => reg2 ↦ term_var "w"
                     | R3 => reg3 ↦ term_var "w"
                     end)
    |}.

  Definition regtag_to_reg (R : RegName) : Reg ty_word :=
    match R with
    | R0 => reg0
    | R1 => reg1
    | R2 => reg2
    | R3 => reg3
    end.

  Definition sep_contract_close_ptsreg (r : RegName) : SepContract ctx_nil ty_unit :=
    {| sep_contract_logic_variables := ["w" ∶ ty_word];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := regtag_to_reg r ↦ term_var "w";
       sep_contract_result          := "_";
       sep_contract_postcondition   := term_enum regname r ↦r term_var "w"
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | rM =>
        MkSepContract
          _ _
          ["address" ∶ ty_int]
          [term_var "address"]%arg
          asn_false
          "result"
          asn_true
      | wM =>
        MkSepContract
          _ _
          ["address" ∶ ty_int, "mem_value" ∶ ty_int]
          [term_var "address", term_var "mem_value"]%arg
          asn_false
          "result"
          asn_true
      | dI =>
        MkSepContract
          _ _
          ["code" ∶ ty_int]
          [term_var "code"]%arg
          asn_false
          "result"
          asn_true
      | @ghost _ f =>
        match f in FunGhost Δ return SepContract Δ ty_unit with
        | open_ptsreg    => sep_contract_open_ptsreg
        | close_ptsreg r => sep_contract_close_ptsreg r
        end
      end.

End MinCapsSymbolicContractKit.

Module MinCapsMutators :=
  Mutators
    MinCapsTermKit
    MinCapsProgramKit
    MinCapsAssertionKit
    MinCapsSymbolicContractKit.
Import MinCapsMutators.
Import DynMutV2.

Local Ltac solve :=
  repeat
    (repeat intro;
     repeat
       match goal with
       | H: NamedEnv _ _ |- _ => unfold NamedEnv in H
       | H: Env _ ctx_nil |- _ => dependent elimination H
       | H: Env _ (ctx_snoc _ _) |- _ => dependent elimination H
       | H: _ /\ _ |- _ => destruct H
       | H: Empty_set |- _ => destruct H
       | |- _ /\ _ => constructor
       end;
     cbn [List.length];
     subst; try congruence; try lia;
     auto
    ).

Local Notation "r '↦' t" := (chunk_ptsreg r t) (at level 100, only printing).
Local Notation "r '↦r' t" := (chunk_pred ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t))) (at level 100, only printing).
Local Notation "a '↦m' t" := (chunk_pred ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t))) (at level 100, only printing).

Lemma valid_contract_read_reg : ValidContractDynMut sep_contract_read_reg fun_read_reg.
Proof. compute; solve. Qed.

Lemma valid_contract_read_reg_cap : ValidContractDynMut sep_contract_read_reg_cap fun_read_reg_cap.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_read_reg_num : ValidContractDynMut sep_contract_read_reg_num fun_read_reg_num.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_write_reg : ValidContractDynMut sep_contract_write_reg fun_write_reg.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_next_pc : ValidContractDynMut sep_contract_next_pc fun_next_pc.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_update_pc : ValidContractDynMut sep_contract_update_pc fun_update_pc.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

