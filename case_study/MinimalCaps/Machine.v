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

From Coq Require Import
     Strings.String
     ZArith.ZArith.
From Equations Require Import
     Equations.
From MicroSail Require Import
     Syntax.
From MinimalCaps Require Export
     Values.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.

(*** TERMS ***)

Module MinCapsTermKit <: TermKit.
  Module valuekit := MinCapsValueKit.
  Module Export VAL := Syntax.Values.Values valuekit.

  (* VARIABLES *)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.
  Definition fresh := Context.fresh (T := Ty).

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | read_reg       : Fun ["rreg" ∶ ty_enum regname ] ty_word
  | read_reg_cap   : Fun ["creg" ∶ ty_enum regname ] ty_cap
  | read_reg_num   : Fun ["nreg" ∶ ty_enum regname ] ty_int
  | write_reg      : Fun ["wreg" ∶ ty_enum regname,
                          "w"  ∶ ty_word
                         ] ty_unit
  | next_pc        : Fun ctx_nil ty_cap
  | update_pc      : Fun ctx_nil ty_unit
  | add_pc         : Fun ["offset" ∶ ty_int] ty_unit
  | read_mem       : Fun ["c"   ∶ ty_cap ] ty_memval
  | write_mem      : Fun ["c"   ∶ ty_cap,
                          "v"   ∶ ty_memval
                         ] ty_unit
  | read_allowed   : Fun ["p"   ∶ ty_perm ] ty_bool
  | write_allowed  : Fun ["p"   ∶ ty_perm ] ty_bool
  (* | sub_perm       : Fun ["p1"  ∶ ty_perm, *)
  (*                         "p2"  ∶ ty_perm *)
  (*                        ] ty_bool *)
  | upper_bound    : Fun ["a"   ∶ ty_addr,
                          "e"   ∶ ty_addr
                         ] ty_bool
  | within_bounds  : Fun ["c"   ∶ ty_cap ] ty_bool
  | compute_rv     : Fun ["rv" ∶ ty_rv] ty_word
  | compute_rv_num : Fun ["rv" ∶ ty_rv] ty_int
  | perm_to_bits   : Fun ["p" ∶ ty_perm] ty_int
  | exec_jr        : Fun ["lv" ∶ ty_lv] ty_bool
  | exec_jalr      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv ] ty_bool
  | exec_j         : Fun ["offset" ∶ ty_int] ty_bool
  | exec_jal       : Fun ["lv" ∶ ty_lv, "offset" ∶ ty_int] ty_bool
  | exec_bnez      : Fun ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_mv        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_bool
  | exec_ld        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_sd        : Fun ["hv" ∶ ty_hv, "lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_addi      : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_add       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_getp      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_getb      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_gete      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_geta      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_ret       : Fun ε ty_bool
  | exec_instr     : Fun ["i" ∶ ty_instr] ty_bool
  | exec           : Fun ε ty_bool
  | loop           : Fun ε ty_unit
  .

  Inductive FunGhost : Ctx (𝑿 * Ty) -> Set :=
  | open_ptsreg : FunGhost ["reg" ∶ ty_enum regname]
  | close_ptsreg (R : RegName) : FunGhost ctx_nil
  | duplicate_safe : FunGhost ["w" ∶ ty_word]
  | csafe_move_cursor : FunGhost ["c" ∶ ty_cap, "c'" ∶ ty_cap]
  | lift_csafe : FunGhost ["c" ∶ ty_cap]
  | specialize_safe_to_cap : FunGhost ["c" ∶ ty_cap]
  | int_safe : FunGhost ["i" ∶ ty_int]
  .

  Inductive FunX : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_memval
  (* write memory *)
  | wM    : FunX ["address" ∶ ty_int, "new_value" ∶ ty_memval] ty_unit
  | dI    : FunX ["code" ∶ ty_int] ty_instr
  | ghost {Δ} (f : FunGhost Δ): FunX Δ ty_unit
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : Ctx (𝑿 * Ty) -> Ty -> Set := FunX.

  Inductive Reg : Ty -> Set :=
  | pc   : Reg ty_cap
  | reg0 : Reg ty_word
  | reg1 : Reg ty_word
  | reg2 : Reg ty_word
  | reg3 : Reg ty_word.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive Signature NoConfusion for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg).
  Proof.
    intros [? []] [? []]; cbn;
      first
        [ left; now apply eq_refl
        | right; intros e; dependent elimination e
        ].
  Defined.

End MinCapsTermKit.

(*** PROGRAM ***)

Module MinCapsProgramKit <: (ProgramKit MinCapsTermKit).
  Module Export TM := Terms MinCapsTermKit.

  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'a'"  := (@exp_var _ "a" _ _) : exp_scope.
  Local Notation "'c'"  := (@exp_var _ "c" _ _) : exp_scope.
  Local Notation "'e'"  := (@exp_var _ "e" _ _) : exp_scope.
  Local Notation "'hv'" := (@exp_var _ "hv" _ _) : exp_scope.
  Local Notation "'rv'" := (@exp_var _ "rv" _ _) : exp_scope.
  Local Notation "'i'"  := (@exp_var _ "i" _ _) : exp_scope.
  Local Notation "'lv'" := (@exp_var _ "lv" _ _) : exp_scope.
  Local Notation "'n'"  := (@exp_var _ "n" _ _) : exn_scope.
  Local Notation "'p'"  := (@exp_var _ "p" _ _) : exp_scope.
  Local Notation "'p1'" := (@exp_var _ "p1" _ _) : exp_scope.
  Local Notation "'p2'" := (@exp_var _ "p2" _ _) : exp_scope.
  Local Notation "'q'"  := (@exp_var _ "q" _ _) : exp_scope.
  Local Notation "'r'"  := (@exp_var _ "r" _ _) : exp_scope.
  Local Notation "'w'"  := (@exp_var _ "w" _ _) : exp_scope.
  Local Notation "'x'"  := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'immediate'" := (@exp_var _ "immediate" _ _) : exp_scope.
  Local Notation "'offset'" := (@exp_var _ "offset" _ _) : exp_scope.

  Local Notation "'c'"  := "c" : string_scope.
  Local Notation "'e'"  := "e" : string_scope.
  Local Notation "'hv'" := "hv" : string_scope.
  Local Notation "'rv'" := "rv" : string_scope.
  Local Notation "'i'"  := "i" : string_scope.
  Local Notation "'lv'" := "lv" : string_scope.
  Local Notation "'n'"  := "n" : string_scope.
  Local Notation "'p'"  := "p" : string_scope.
  Local Notation "'q'"  := "q" : string_scope.
  Local Notation "'r'"  := "r" : string_scope.
  Local Notation "'w'"  := "w" : string_scope.
  Local Notation "'immediate'" := "immediate" : string_scope.
  Local Notation "'offset'" := "offset" : string_scope.

  Notation stm_call_external := stm_foreign.

  Notation "'callghost' f" :=
    (stm_foreign (ghost f) env_nil)
    (at level 10, f at next level) : exp_scope.

  Definition fun_read_reg : Stm ["rreg" ∶ ty_enum regname ] ty_word :=
    stm_call_external (ghost open_ptsreg) [exp_var "rreg"]%arg ;;
    match: exp_var "rreg" in regname with
    | R0 => let: "x" := stm_read_register reg0 in callghost (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_read_register reg1 in callghost (close_ptsreg R1) ;; stm_exp x
    | R2 => let: "x" := stm_read_register reg2 in callghost (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_read_register reg3 in callghost (close_ptsreg R3) ;; stm_exp x
    end.

  Definition fun_read_reg_cap : Stm ["creg" ∶ ty_enum regname ] ty_cap :=
    let: w := call read_reg (exp_var "creg") in
    match: w with
    | inl i => fail "Err [read_reg_cap]: expect register to hold a capability"
    | inr c => stm_exp c
    end.

  Definition fun_read_reg_num : Stm ["nreg" ∶ ty_enum regname ] ty_int :=
    let: w := call read_reg (exp_var "nreg") in
    match: w with
    | inl i => stm_exp i
    | inr c => fail "Err [read_reg_num]: expect register to hold a number"
    end.

  Definition fun_write_reg : Stm ["wreg" ∶ ty_enum regname,
                                  "w" ∶ ty_word
                                 ] ty_unit :=
    stm_call_external (ghost open_ptsreg) [exp_var "wreg"]%arg ;;
    match: exp_var "wreg" in regname with
    | R0 => let: "x" := stm_write_register reg0 (exp_var "w") in callghost (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_write_register reg1 (exp_var "w") in callghost (close_ptsreg R1) ;; stm_exp x
    | R2 => let: "x" := stm_write_register reg2 (exp_var "w") in callghost (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_write_register reg3 (exp_var "w") in callghost (close_ptsreg R3) ;; stm_exp x
    end ;; stm_lit ty_unit tt.

  Definition fun_next_pc : Stm ctx_nil ty_cap :=
    let: "c" := stm_read_register pc in
    stm_match_record capability (exp_var "c")
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "cap_permission" "perm")
       "cap_begin" "beg")
       "cap_end" "end")
       "cap_cursor" "cur")
      (exp_record capability
         [ exp_var "perm",
           exp_var "beg",
           exp_var "end",
           exp_var "cur" + lit_int 1 ]).

  Definition fun_update_pc : Stm ctx_nil ty_unit :=
    let: "opc" := stm_read_register pc in
    let: "npc" := call next_pc in
    stm_call_external (ghost csafe_move_cursor) [exp_var "opc", exp_var "npc"]%arg ;;
    stm_write_register pc (exp_var "npc") ;;
    stm_lit ty_unit tt.

  Definition fun_add_pc : Stm ["offset" ∶ ty_int ] ty_unit :=
    let: "opc" := stm_read_register pc in
    stm_match_record capability (exp_var "opc")
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "cap_permission" "perm")
       "cap_begin" "beg")
       "cap_end" "end")
       "cap_cursor" "cur")
      (let: "npc" := (exp_record capability
           [ exp_var "perm",
             exp_var "beg",
             exp_var "end",
             exp_var "cur" + exp_var "offset" ]) in
       stm_call_external (ghost csafe_move_cursor) [exp_var "opc", exp_var "npc"]%arg ;;
       stm_write_register pc (exp_var "npc")) ;;
    stm_lit ty_unit tt.

  Definition fun_read_allowed : Stm ["p" ∶ ty_perm] ty_bool :=
    match: p in permission with
    | R   => stm_lit ty_bool true
    | RW  => stm_lit ty_bool true
    | _   => stm_lit ty_bool false
    end.

  Definition fun_write_allowed : Stm ["p" ∶ ty_perm] ty_bool :=
    match: p in permission with
    | RW  => stm_lit ty_bool true
    | _   => stm_lit ty_bool false
    end.

  (* Definition fun_sub_perm : Stm ["p1" ∶ ty_perm, "p2" ∶ ty_perm] ty_bool := *)
  (*   match: p1 in permission with *)
  (*   | O   => stm_lit ty_bool true *)
  (*   | R   => call read_allowed p2 *)
  (*   | RW  => let: "r" := call read_allowed p2 in *)
  (*            let: "w" := call write_allowed p2 in *)
  (*            stm_exp (exp_var "r" && exp_var "w") *)
  (*   end. *)

  Definition fun_within_bounds : Stm ["c" ∶ ty_cap ] ty_bool :=
    stm_match_record capability (exp_var "c")
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
      "cap_permission" "p")
      "cap_begin" "b")
      "cap_end" "e")
      "cap_cursor" "a")
      (let: "u" := call upper_bound (exp_var "a") (exp_var "e") in
       stm_exp ((exp_var "b" <= exp_var "a") && exp_var "u")).

  Definition fun_upper_bound : Stm ["a"   ∶ ty_addr, "e"   ∶ ty_addr] ty_bool :=
    stm_exp (a <= e).

  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty_cap.
    Let bool : Ty := ty_bool.
    Let int : Ty := ty_int.
    Let word : Ty := ty_word.

    Definition fun_exec_sd : Stm [hv ∶ ty_hv, lv ∶ ty_lv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv") (fun _ => stm_lit ty_unit tt) ;;
      let: "base_cap" ∶ cap  := call read_reg_cap lv in
      stm_match_record
        capability (exp_var "base_cap")
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
        (let: "c" ∶ cap := exp_record capability
                             [ exp_var "perm",
                               exp_var "beg",
                               exp_var "end",
                               exp_var "cursor" + exp_var "immediate"
                             ] in
         let: w ∶ ty_word := call read_reg hv in
         stm_call_external (ghost duplicate_safe) [exp_var w]%arg ;;
         stm_call_external (ghost specialize_safe_to_cap) [exp_var "base_cap"]%arg ;;
         stm_call_external (ghost csafe_move_cursor) [exp_var "base_cap", exp_var "c"]%arg ;;
         stm_call_external (ghost lift_csafe) [exp_var "base_cap"]%arg ;;
         call write_mem c w ;;
         call update_pc ;;
         stm_lit ty_bool true).

    Definition fun_exec_ld : Stm [lv ∶ ty_lv, hv ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_lit ty_unit tt) ;;
      let: "base_cap" ∶ cap  := call read_reg_cap hv in
      stm_match_record
        capability (exp_var "base_cap")
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
        (let: "c" ∶ cap := exp_record capability
                             [ exp_var "perm",
                               exp_var "beg",
                               exp_var "end",
                               exp_var "cursor" + exp_var "immediate"
                             ] in
         stm_call_external (ghost specialize_safe_to_cap) [exp_var "base_cap"]%arg ;;
         stm_call_external (ghost csafe_move_cursor) [exp_var "base_cap", exp_var "c"]%arg ;;
         stm_call_external (ghost lift_csafe) [exp_var "base_cap"]%arg ;;
         let: n ∶ ty_memval := call read_mem c in
         stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
         call write_reg lv (exp_var n) ;;
         call update_pc ;;
         stm_lit ty_bool true).

    Definition fun_exec_addi : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_lit ty_unit tt) ;;
      let: "v" ∶ ty_int := call read_reg_num (exp_var "hv") in
      let: "res" ∶ ty_int := stm_exp (exp_var "v" + exp_var "immediate") in
      stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
      call write_reg (exp_var "lv") (exp_inl (exp_var "res")) ;;
      stm_call_external (ghost int_safe) [exp_var "res"]%arg ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_add : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv ] ty_bool :=
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv3") (fun _ => stm_lit ty_unit tt) ;;
      let: "v1" ∶ int := call read_reg_num (exp_var "lv2") in
      let: "v2" ∶ int := call read_reg_num (exp_var "lv3") in
      let: "res" ∶ int := stm_exp (exp_var "v1" + exp_var "v2") in
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_lit ty_unit tt) ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      stm_call_external (ghost int_safe) [exp_var "res"]%arg ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_perm_to_bits : Stm ["p" ∶ ty_perm] ty_int :=
      match: exp_var "p" in permission with
      | O => stm_lit ty_int 0%Z
      | R => stm_lit ty_int 1%Z
      | RW => stm_lit ty_int 2%Z
      end.

    Definition fun_exec_getp : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_lit ty_unit tt) ;;
      let: c ∶ cap := call read_reg_cap (exp_var "lv2") in
      stm_match_record
        capability (exp_var c)
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
        (let: "i" ∶ ty_int := call perm_to_bits (exp_var "perm") in
         call write_reg (exp_var "lv1") (exp_inl (exp_var "i")) ;;
         stm_call_external (ghost int_safe) [exp_var "i"]%arg ;;
         call update_pc ;;
         stm_lit ty_bool true).

    Definition fun_exec_getb : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_lit ty_unit tt) ;;
      let: c ∶ cap := call read_reg_cap (exp_var "lv2") in
      stm_match_record
        capability (exp_var c)
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
        (call write_reg (exp_var "lv1") (exp_inl (exp_var "beg")) ;;
         stm_call_external (ghost int_safe) [exp_var "beg"]%arg ;;
         call update_pc ;;
         stm_lit ty_bool true).

    Definition fun_exec_gete : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_lit ty_unit tt) ;;
      let: c ∶ cap := call read_reg_cap (exp_var "lv2") in
      stm_match_record
        capability (exp_var c)
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
        (call write_reg (exp_var "lv1") (exp_inl (exp_var "end")) ;;
         stm_call_external (ghost int_safe) [exp_var "end"]%arg ;;
         call update_pc ;;
         stm_lit ty_bool true).

    Definition fun_exec_geta : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_lit ty_unit tt) ;;
      let: c ∶ cap := call read_reg_cap (exp_var "lv2") in
      stm_match_record
        capability (exp_var c)
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
        (call write_reg (exp_var "lv1") (exp_inl (exp_var "cursor")) ;;
         stm_call_external (ghost int_safe) [exp_var "cursor"]%arg ;;
         call update_pc ;;
         stm_lit ty_bool true).

    Definition fun_compute_rv : Stm [rv ∶ ty_rv] ty_word :=
      stm_match_sum rv
                    "r" (call read_reg r)
                    "n" (stm_exp (exp_inl (exp_var n))).

    Definition fun_compute_rv_num : Stm [rv ∶ ty_rv] ty_int :=
      let: w ∶ ty_word := call compute_rv rv in
      match: w with
      | inl i => stm_exp i
      | inr c => fail "Err [read_reg_num]: expect register to hold a number"
      end.

    Definition fun_exec_ret : Stm ε ty_bool :=
      stm_exp lit_false.

    Definition fun_exec_mv : Stm [lv ∶ ty_lv, hv ∶ ty_hv] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_lit ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
      let: w ∶ word := call read_reg (exp_var hv) in
      stm_call_external (ghost duplicate_safe) [exp_var w]%arg ;;
      call write_reg lv (exp_var w) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_jr : Stm ["lv" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
      let: "c" ∶ ty_cap := call read_reg_cap (exp_var "lv") in
      stm_write_register pc (exp_var "c") ;;
      stm_call_external (ghost duplicate_safe) [exp_inr (exp_var "c")]%arg ;;
      stm_call_external (ghost specialize_safe_to_cap) [exp_var "c"]%arg ;;
      stm_lit ty_bool true.

    Definition fun_exec_jalr : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      stm_call_external (ghost csafe_move_cursor) [exp_var "opc", exp_var "npc"]%arg ;;
      stm_call_external (ghost lift_csafe) [exp_var "npc"]%arg ;;
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_lit ty_unit tt) ;;
      call write_reg (exp_var "lv1") (exp_inr (exp_var "npc")) ;;
      call exec_jr (exp_var "lv2").

    Definition fun_exec_j : Stm [offset ∶ ty_int ] ty_bool :=
      call add_pc (exp_binop binop_times (exp_var offset) (lit_int 2)) ;;
      stm_lit ty_bool true.

    Definition fun_exec_jal : Stm [lv ∶ ty_lv, offset ∶ ty_int] ty_bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      stm_call_external (ghost csafe_move_cursor) [exp_var "opc", exp_var "npc"]%arg ;;
      stm_call_external (ghost lift_csafe) [exp_var "npc"]%arg ;;
      stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
      call write_reg lv (exp_inr (exp_var "npc")) ;;
      call exec_j offset.

    Definition fun_exec_bnez : Stm ["lv" ∶ ty_lv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_lit ty_unit tt) ;;
      let: "c" ∶ ty_int := call read_reg_num (exp_var "lv") in
      stm_if (exp_binop binop_eq (exp_var "c") (lit_int 0))
             (call update_pc ;; stm_lit ty_bool true)
             (call add_pc (exp_var "immediate") ;; stm_lit ty_bool true).

    Definition fun_exec_instr : Stm [i ∶ ty_instr] ty_bool :=
      stm_match_union_alt
        instruction (exp_var i)
        (fun K =>
           match K with
           | kjr   => MkAlt (pat_var lv) (call exec_jr lv)
           | kjalr => MkAlt (pat_pair "lv1" "lv2") (call exec_jalr (exp_var "lv1") (exp_var "lv2"))
           | kj    => MkAlt (pat_var offset) (call exec_j offset)
           | kjal  => MkAlt (pat_pair lv offset) (call exec_jal lv offset)
           | kbnez => MkAlt (pat_pair lv immediate) (call exec_bnez lv immediate)
           | kmv   => MkAlt (pat_pair lv hv) (call exec_mv lv hv)
           | kld   => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_ld (exp_var lv) (exp_var hv) (exp_var immediate))
           | ksd   => MkAlt (pat_tuple [hv , lv , immediate])
                            (call exec_sd (exp_var hv) (exp_var lv) (exp_var immediate))
           | kaddi => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_addi (exp_var lv) (exp_var hv) (exp_var immediate))
           | kadd  => MkAlt (pat_tuple ["lv1" , "lv2" , "lv3"])
                            (call exec_add (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | kgetp => MkAlt (pat_pair lv lv) (call exec_getp lv lv)
           | kgetb => MkAlt (pat_pair lv lv) (call exec_getb lv lv)
           | kgete => MkAlt (pat_pair lv lv) (call exec_gete lv lv)
           | kgeta => MkAlt (pat_pair lv lv) (call exec_geta lv lv)
           | kret  => MkAlt pat_unit (call exec_ret)
           end).

    Definition fun_read_mem : Stm ["c" ∶ ty_cap] ty_memval :=
      stm_match_record
        capability (exp_var "c")
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
         (let: p ∶ bool := call read_allowed (exp_var "perm") in
         stm_assert p (lit_string "Err: [read_mem] no read permission") ;;
         let: q ∶ bool := call within_bounds c in
         stm_assert q (lit_string "Err: [read_mem] out of bounds") ;;
         foreign rM (exp_var "cursor")).

    Definition fun_write_mem : Stm ["c" ∶ ty_cap, "v" ∶ ty_memval ] ty_unit :=
      stm_match_record
        capability (exp_var "c")
        (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
         "cap_permission" "perm")
         "cap_begin" "beg")
         "cap_end" "end")
         "cap_cursor" "cursor")
         (let: p ∶ bool := call write_allowed (exp_var "perm") in
         stm_assert p (lit_string "Err: [write_mem] no read permission") ;;
         let: q ∶ bool := call within_bounds c in
         stm_assert q (lit_string "Err: [write_mem] out of bounds") ;;
         foreign wM (exp_var "cursor") (exp_var "v")).

    Definition fun_exec : Stm ε ty_bool :=
      let: "c" := stm_read_register pc in
      let: n ∶ ty_memval := call read_mem c in
      match: (exp_var "n") with
      | inl n => 
        let: i ∶ ty_instr := foreign dI (exp_var n) in
        call exec_instr i
      | inr c => fail "Err [exec]: instructions cannot be capabilities"
      end.

    Definition fun_loop : Stm ε ty_unit :=
      let: "r" := call exec in
      if: exp_var "r"
      then call loop
      else stm_lit ty_unit tt.

  End ExecStore.

  Program Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | read_reg       => fun_read_reg
    | read_reg_cap   => fun_read_reg_cap
    | read_reg_num   => fun_read_reg_num
    | write_reg      => fun_write_reg
    | next_pc        => fun_next_pc
    | update_pc      => fun_update_pc
    | add_pc         => fun_add_pc
    | read_mem       => fun_read_mem
    | write_mem      => fun_write_mem
    | read_allowed   => fun_read_allowed
    | write_allowed  => fun_write_allowed
    (* | sub_perm       => fun_sub_perm *)
    | upper_bound    => fun_upper_bound
    | within_bounds  => fun_within_bounds
    | perm_to_bits   => fun_perm_to_bits
    | exec_jr        => fun_exec_jr
    | exec_jalr      => fun_exec_jalr
    | exec_j         => fun_exec_j
    | exec_jal       => fun_exec_jal
    | exec_bnez      => fun_exec_bnez
    | exec_mv        => fun_exec_mv
    | exec_ld        => fun_exec_ld
    | exec_sd        => fun_exec_sd
    | exec_addi      => fun_exec_addi
    | exec_add       => fun_exec_add
    | exec_getp      => fun_exec_getp
    | exec_getb      => fun_exec_getb
    | exec_gete      => fun_exec_gete
    | exec_geta      => fun_exec_geta
    | exec_ret       => fun_exec_ret
    | exec_instr     => fun_exec_instr
    | compute_rv     => fun_compute_rv
    | compute_rv_num => fun_compute_rv_num
    | exec           => fun_exec
    | loop           => fun_loop
    end.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* MEMORY *)
  Definition Memory := Addr -> (Z + Capability).

  Definition fun_rM (μ : Memory) (addr : Lit ty_int) : Lit ty_memval :=
    μ addr.

  Definition fun_wM (μ : Memory) (addr : Lit ty_int) (val : Lit ty_memval) : Memory :=
    fun addr' => if Z.eqb addr addr' then val else μ addr'.

  Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) :
    forall (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
    match f with
    | rM      => fun args res γ γ' μ μ' =>
                   let addr := (args ‼ "address")%exp in
                   (γ' , μ' , res) = (γ , μ , inr (fun_rM μ addr))
    | wM      => fun args res γ γ' μ μ' =>
                   let addr := (args ‼ "address")%exp in
                   let val  := (args ‼ "new_value")%exp in
                   (γ' , μ' , res) = (γ , fun_wM μ addr val , inr tt)
    | dI      => fun args res γ γ' μ μ' =>
                   let code := (args ‼ "code")%exp in
                   (* Non-deterministically return any possible result *)
                   (exists res' : Lit (ty_sum ty_string ty_instr),
                     (γ' , μ' , res) = (γ , μ , res'))%type
    | ghost f => fun _ res γ γ' μ μ' =>
                   (γ' , μ' , res) = (γ , μ , inr tt)
    end.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args. exists γ, μ, (inr ret), (inr ret). reflexivity.
    - exists γ, μ, (inr tt). reflexivity.
  Qed.

End MinCapsProgramKit.
