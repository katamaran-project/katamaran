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
| safe
| csafe.

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
    | csafe => [ty_cap]
    end.
  Instance 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.
End MinCapsAssertionKit.

Module MinCapsSymbolicContractKit <:
  SymbolicContractKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.
  Module Export ASS := Assertions MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

  Open Scope env_scope.

  Local Notation "r '↦r' t" := (asn_chunk (chunk_user ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t)))) (at level 100).
  Local Notation "a '↦m' t" := (asn_chunk (chunk_user ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t)))) (at level 100).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty_unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_safe w := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ w)))).
  (* Arguments asn_prop [_] & _. *)

  (* regInv(r) = ∃ w : word. r ↦ w * safe(w) *)
  Definition regInv {Σ} (r : RegName) (w : string) : Assertion Σ :=
    asn_exist w ty_word
              (term_lit (ty_enum regname) r ↦r (@term_var _ _ _ inctx_zero) ✱
                asn_safe (@term_var _ _ _ inctx_zero)).

  (* regInv(r) = ∃ c : cap. r ↦ c * csafe(c) *)
  Definition regInvCap {Σ} (r : Reg ty_cap) : Assertion Σ :=
    asn_exist "c" ty_cap
              (r ↦ term_var "c" ✱
                 asn_chunk (chunk_user csafe (env_nil ► (ty_cap ↦ (term_var "c"))))).

  (* machInv = regInv(r1) * regInv(r2) * regInv(r3) * regInv(r4) * regInvCap(pc) *)
  Definition machInv {Σ} : Assertion Σ :=
    (regInv R0 "w0") ✱ (regInv R1 "w1") ✱ (regInv R2 "w2") ✱ (regInv R3 "w3") ✱ (regInvCap pc).

  Definition sep_contract_read_reg : SepContract ["rreg" ∶ ty_enum regname ] ty_word :=
    {| sep_contract_logic_variables := ["rreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "rreg"]%arg;
       sep_contract_precondition    := term_var "rreg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_read_reg") (term_var "w") ✱
         term_var "rreg" ↦r term_var "w";
    |}.

  Definition sep_contract_read_reg_cap : SepContract ["creg" ∶ ty_enum regname ] ty_cap :=
    {| sep_contract_logic_variables := ["creg" ∶ ty_enum regname];
       sep_contract_localstore      := [term_var "creg"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result_read_reg_cap";
       sep_contract_postcondition   := machInv;
    |}.

  Definition sep_contract_read_reg_num : SepContract ["nreg" ∶ ty_enum regname ] ty_int :=
    {| sep_contract_logic_variables := ["nreg" ∶ ty_enum regname];
       sep_contract_localstore      := [term_var "nreg"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result_read_reg_num";
       sep_contract_postcondition   := machInv;
    |}.

  Definition sep_contract_write_reg : SepContract ["wreg" ∶ ty_enum regname, "w"  ∶ ty_word] ty_unit :=
    {| sep_contract_logic_variables := ["wreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "wreg", term_var "w"]%arg;
       sep_contract_precondition    := asn_exist "old_word" ty_word (term_var "wreg" ↦r term_var "old_word");
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_eq (term_var "result") (term_lit ty_unit tt) ✱
         term_var "wreg" ↦r term_var "w";
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
    {| sep_contract_logic_variables := ctx_nil;
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := regInvCap pc;
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_eq (term_var "result") (term_lit ty_unit tt) ✱
         regInvCap pc
    |}.

  Definition sep_contract_add_pc : SepContract ["offset" ∶ ty_int] ty_unit :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap, "offset" ∶ ty_int];
       sep_contract_localstore      := [term_var "offset"]%arg;
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "_";
       sep_contract_postcondition   := asn_exist "npc" ty_cap (pc ↦ term_var "npc");
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

  Definition sep_contract_read_allowed : SepContract ["p" ∶ ty_perm ] ty_bool :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_bool (term_lit ty_bool true);
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_match_enum permission (term_var "p")
                        (fun p => match p with
                                 | R  => asn_eq (term_var "result") (term_lit ty_bool true)
                                 | RW => asn_eq (term_var "result") (term_lit ty_bool true)
                                 | _  => asn_eq (term_var "result") (term_lit ty_bool false)
                               end);
    |}.

  Definition sep_contract_write_allowed : SepContract ["p" ∶ ty_perm ] ty_bool :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_bool (term_lit ty_bool true);
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_match_enum permission (term_var "p")
                        (fun p => match p with
                                 | RW => asn_eq (term_var "result") (term_lit ty_bool true)
                                 | _  => asn_eq (term_var "result") (term_lit ty_bool false)
                               end);
    |}.

  Definition sep_contract_upper_bound : SepContract ["a" ∶ ty_addr, "e" ∶ ty_option ty_addr ] ty_bool :=
    {| sep_contract_logic_variables := ["a" ∶ ty_addr, "e" ∶ ty_option ty_addr ];
       sep_contract_localstore      := [term_var "a", term_var "e"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := 
          asn_match_option ty_addr (term_var "e") "e'"
                           (asn_eq (term_var "result")
                                   (term_binop binop_le (term_var "a") (term_var "e'")))
                           (asn_eq (term_var "result") (term_lit ty_bool true)); 
    |}.

  (* 
      @pre true;
      @post ∃ b,e,a,p. c = mkcap(b,e,a,p) ∧ result = (a >= b && (e = none ∨ e = inl e' ∧ e' >= a));
      bool within_bounds(c : capability);
   *)
  Definition sep_contract_within_bounds : SepContract ["c" ∶ ty_cap] ty_bool := 
    {| sep_contract_logic_variables := ["c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "c"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_exist
           "b" ty_addr
           (asn_exist
              "e" (ty_option ty_addr)
              (asn_exist
                 "a" ty_addr
                 (asn_eq (term_var "b") (term_projrec (term_var "c") "cap_begin") ✱
                         asn_eq (term_var "e") (term_projrec (term_var "c") "cap_end") ✱
                         asn_eq (term_var "a") (term_projrec (term_var "c") "cap_cursor") ✱
                         asn_match_option ty_addr (term_var "e") "e'"
                         (asn_eq (term_var "result")
                                 (term_binop binop_and
                                             (term_binop binop_le (term_var "b") (term_var "a"))
                                             (term_binop binop_le (term_var "a") (term_var "e'"))))
                         (asn_eq (term_var "result") 
                                 (term_binop binop_le (term_var "b") (term_var "a"))))))
                     |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_jr(lv : lv) *)
  Definition sep_contract_exec_jr : SepContract ["lv" ∶ ty_lv] ty_bool :=
    {| sep_contract_logic_variables := ["lv" ∶ ty_lv, "c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "lv"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_jalr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_jalr : SepContract ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
    {| sep_contract_logic_variables := ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv];
       sep_contract_localstore      := [term_var "lv1", term_var "lv2"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_j(offset : Z) *)
  Definition sep_contract_exec_j : SepContract ["offset" ∶ ty_int] ty_bool :=
    {| sep_contract_logic_variables := ["offset" ∶ ty_int];
       sep_contract_localstore      := [term_var "offset"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_jal(lv : lv, offset : Z) *)
  Definition sep_contract_exec_jal : SepContract ["lv" ∶ ty_lv, "offset" ∶ ty_int] ty_bool :=
    {| sep_contract_logic_variables := ["lv" ∶ ty_lv, "offset" ∶ ty_int];
       sep_contract_localstore      := [term_var "lv", term_var "offset"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_bnez(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_bnez : SepContract ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool :=
    {| sep_contract_logic_variables := ["lv" ∶ ty_lv, "immediate" ∶ ty_int];
       sep_contract_localstore      := [term_var "lv", term_var "immediate"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_mv(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_mv : SepContract ["lv" ∶ ty_lv, "hv" ∶ ty_hv] ty_bool :=
    {| sep_contract_logic_variables := ["lv" ∶ ty_lv, "hv" ∶ ty_hv];
       sep_contract_localstore      := [term_var "lv", term_var "hv"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_ld(lv : lv, hv : memval, immediate : Z) *)
  Definition sep_contract_exec_ld : SepContract ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool :=
    {| sep_contract_logic_variables := ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int];
       sep_contract_localstore      := [term_var "lv", term_var "hv", term_var "immediate"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_sd(hv : memval, lv : lv, immediate : Z) *)
  Definition sep_contract_exec_sd : SepContract ["hv" ∶ ty_hv, "lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool :=
    {| sep_contract_logic_variables := ["hv" ∶ ty_hv, "lv" ∶ ty_lv, "immediate" ∶ ty_int];
       sep_contract_localstore      := [term_var "hv", term_var "lv", term_var "immediate"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_addi(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_addi : SepContract ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool :=
    {| sep_contract_logic_variables := ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int];
       sep_contract_localstore      := [term_var "lv", term_var "hv", term_var "immediate"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_add(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_add : SepContract ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool :=
    {| sep_contract_logic_variables := ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv];
       sep_contract_localstore      := [term_var "lv1", term_var "lv2", term_var "lv3"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (* @pre machInv;
     @post machInv;
     bool exec_ret *)
  Definition sep_contract_exec_ret : SepContract ε ty_bool :=
    {| sep_contract_logic_variables := ctx_nil;
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_instr(i : instr) *)
  Definition sep_contract_exec_instr : SepContract ["i" ∶ ty_instr] ty_bool :=
    {| sep_contract_logic_variables := ["i" ∶ ty_instr];
       sep_contract_localstore      := [term_var "i"]%arg;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec *)
  Definition sep_contract_exec : SepContract ε ty_bool :=
    {| sep_contract_logic_variables := ctx_nil;
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  (*
      @pre machInv;
      @post machInv;
      unit loop *)
  Definition sep_contract_loop : SepContract ε ty_unit :=
    {| sep_contract_logic_variables := ctx_nil;
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "result";
       sep_contract_postcondition   := machInv;
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_allowed  => Some sep_contract_read_allowed
      | write_allowed => Some sep_contract_write_allowed
      | upper_bound   => Some sep_contract_upper_bound
      | within_bounds => Some sep_contract_within_bounds
      | read_reg      => Some sep_contract_read_reg
      | read_reg_cap  => Some sep_contract_read_reg_cap
      | read_reg_num  => Some sep_contract_read_reg_num
      | write_reg     => Some sep_contract_write_reg
      | next_pc       => Some sep_contract_next_pc
      | add_pc        => Some sep_contract_add_pc
      | update_pc     => Some sep_contract_update_pc
      | read_mem      => Some sep_contract_read_mem
      | write_mem     => Some sep_contract_write_mem
      | exec_jr       => Some sep_contract_exec_jr
      | exec_jalr     => Some sep_contract_exec_jalr
      | exec_j        => Some sep_contract_exec_j
      | exec_jal      => Some sep_contract_exec_jal
      | exec_bnez     => Some sep_contract_exec_bnez
      | exec_mv       => Some sep_contract_exec_mv
      | exec_ld       => Some sep_contract_exec_ld
      | exec_sd       => Some sep_contract_exec_sd
      | exec_addi     => Some sep_contract_exec_addi
      | exec_add      => Some sep_contract_exec_add
      | exec_ret      => Some sep_contract_exec_ret
      | exec_instr    => Some sep_contract_exec_instr
      | exec          => Some sep_contract_exec
      | loop          => Some sep_contract_loop
      | _             => None
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

  (* TODO: add persistent predicates? *)
  Definition sep_contract_duplicate_safe : SepContract ["reg" ∶ ty_enum regname] ty_unit :=
    {| sep_contract_logic_variables := ["reg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "reg"]%arg;
       sep_contract_precondition    := term_var "reg" ↦r term_var "w" ✱ asn_safe (term_var "w");
       sep_contract_result          := "result_duplicate_safe";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_duplicate_safe") (term_lit ty_unit tt) ✱
         term_var "reg" ↦r term_var "w" ✱
         asn_safe (term_var "w") ✱
         asn_safe (term_var "w")
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
        | duplicate_safe => sep_contract_duplicate_safe
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
Local Notation "r '↦r' t" := (chunk_user ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t))) (at level 100, only printing).
Local Notation "a '↦m' t" := (chunk_user ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t))) (at level 100, only printing).
Local Notation safew w := (chunk_user safe (env_nil ► (ty_word ↦ w))).

Lemma valid_contract_read_reg : ValidContractDynMut sep_contract_read_reg fun_read_reg.
Proof. compute; solve. Qed.

Lemma valid_contract_read_reg_cap : ValidContractDynMut sep_contract_read_reg_cap fun_read_reg_cap.
Proof. compute; solve. Abort.

Lemma valid_contract_read_reg_num : ValidContractDynMut sep_contract_read_reg_num fun_read_reg_num.
Proof. compute; solve. Abort.

Lemma valid_contract_write_reg : ValidContractDynMut sep_contract_write_reg fun_write_reg.
Proof. compute; solve. Qed.

Lemma valid_contract_next_pc : ValidContractDynMut sep_contract_next_pc fun_next_pc.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_add_pc : ValidContractDynMut sep_contract_add_pc fun_add_pc.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_update_pc : ValidContractDynMut sep_contract_update_pc fun_update_pc.
Proof. Abort.

Lemma valid_contract_read_allowed : ValidContractDynMut sep_contract_read_allowed fun_read_allowed.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_write_allowed : ValidContractDynMut sep_contract_write_allowed fun_write_allowed.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_upper_bound : ValidContractDynMut sep_contract_upper_bound fun_upper_bound.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_within_bounds : ValidContractDynMut sep_contract_within_bounds fun_within_bounds.
Proof.
  (* apply dynmutevarreflect_sound. *)
  compute - [NamedEnv Lit Error valid_obligation].
  (* compute; solve. Qed. *)
Abort.
(*
Lemma valid_contract_exec_jr : ValidContractDynMut sep_contract_exec_jr fun_exec_jr.
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_jalr : ValidContractDynMut sep_contract_exec_jalr fun_exec_jalr.
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_j : ValidContractDynMut sep_contract_exec_j fun_exec_j.
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_jal : ValidContractDynMut sep_contract_exec_jal fun_exec_jal.
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_bnez : ValidContractDynMut sep_contract_exec_bnez fun_exec_bnez.
Proof. compute; solve. Admitted.
*)

Ltac debug_satisfy_forget_post :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let x := fresh "POST" in
    generalize P; intros x
  end.

Ltac debug_satisfy_remember_post :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let x := fresh "POST" in
    remember P as x
  end.

Ltac debug_satisfy_eval_cbn_inputs :=
  match goal with
  | |- outcome_satisfy (?f ?Σ ?ζ ?s) ?P =>
    let Σ' := eval cbn in Σ in
    let ζ' := eval cbn in ζ in
    let s' := eval cbn in s in
    change_no_check (outcome_satisfy (f Σ' ζ' s') P)
  end.

Ltac debug_satisfy_eval_cbv :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let o' := eval cbv - [NamedEnv Lit Error valid_obligation] in o in
    change_no_check (outcome_satisfy o' P); cbn [outcome_satisfy]
  end.

Close Scope exp.
Close Scope env.

Lemma valid_contract_exec_mv : ValidContractDynMut sep_contract_exec_mv fun_exec_mv.
Proof. apply dynmutevarreflect_sound; now compute. Qed.

Lemma valid_contract_exec_ld : ValidContractDynMut sep_contract_exec_ld fun_exec_ld.
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_sd : ValidContractDynMut sep_contract_exec_sd fun_exec_sd.
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_addi : TwoPointO.ValidContractDynMutDebug sep_contract_exec_addi fun_exec_addi.
Proof.
  (* apply dynmutevarreflect_sound. *)
  compute - [NamedEnv Lit Error valid_obligation].
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_add : TwoPointO.ValidContractDynMutDebug sep_contract_exec_add fun_exec_add.
Proof.
  compute.
  (* apply dynmutevarreflect_sound. *)
  compute - [NamedEnv Lit Error valid_obligation].
Proof. compute; solve. Admitted.

Lemma valid_contract_exec_ret : ValidContractDynMut sep_contract_exec_ret fun_exec_ret.
Proof. compute; solve. Qed.

Lemma valid_contract_exec_instr : ValidContractDynMut sep_contract_exec_instr fun_exec_instr.
Proof. compute; solve. Qed.

Lemma valid_contract_exec : ValidContractDynMut sep_contract_exec fun_exec.
Proof. compute; solve. Admitted.

Lemma valid_contract_loop : ValidContractDynMut sep_contract_loop fun_loop.
Proof. compute; solve. Qed.
