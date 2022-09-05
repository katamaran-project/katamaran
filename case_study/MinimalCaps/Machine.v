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
     Strings.String
     ZArith.ZArith.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Program
     Semantics.Registers
     Syntax.BinOps.
From Katamaran Require Export
     MinimalCaps.Base.

From stdpp Require Import finite decidable.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.

(*** Program ***)

Import MinCapsBase.
Module Export MinCapsProgram <: Program MinCapsBase.

Section FunDeclKit.
  Inductive Fun : PCtx -> Ty -> Set :=
  | read_reg           : Fun ["rreg" ∷ ty.enum regname ] ty.word
  | read_reg_cap       : Fun ["creg" ∷ ty.enum regname ] ty.cap
  | read_reg_num       : Fun ["nreg" ∷ ty.enum regname ] ty.int
  | write_reg          : Fun ["wreg" ∷ ty.enum regname;
                              "w"  ∷ ty.word
                             ] ty.unit
  | next_pc            : Fun [] ty.cap
  | update_pc          : Fun [] ty.unit
  | update_pc_perm     : Fun ["c" :: ty.cap] ty.cap
  | is_correct_pc      : Fun ["c" :: ty.cap] ty.bool
  | is_perm            : Fun ["p" :: ty.perm; "p'" :: ty.perm] ty.bool
  | add_pc             : Fun ["offset" ∷ ty.int] ty.unit
  | read_mem           : Fun ["c"   ∷ ty.cap ] ty.memval
  | write_mem          : Fun ["c"   ∷ ty.cap;
                              "v"   ∷ ty.memval
                             ] ty.unit
  | read_allowed       : Fun ["p"   ∷ ty.perm ] ty.bool
  | write_allowed      : Fun ["p"   ∷ ty.perm ] ty.bool
  | upper_bound        : Fun ["a"   ∷ ty.addr;
                              "e"   ∷ ty.addr
                             ] ty.bool
  | within_bounds      : Fun ["c"   ∷ ty.cap ] ty.bool
  | perm_to_bits       : Fun ["p" ∷ ty.perm] ty.int
  | perm_from_bits     : Fun ["i" ∷ ty.int] ty.perm
  | and_perm           : Fun ["p1" :: ty.perm; "p2" :: ty.perm] ty.perm
  | is_sub_perm        : Fun ["p" ∷ ty.perm; "p'" ∷ ty.perm] ty.bool
  | is_within_range    : Fun ["b'" ∷ ty.addr; "e'" ∷ ty.addr;
                              "b" ∷ ty.addr; "e" ∷ ty.addr] ty.bool
  | abs                : Fun ["i" ∷ ty.int] ty.int
  | exec_jalr          : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv ] ty.bool
  | exec_jal           : Fun ["lv" ∷ ty.lv; "offset" ∷ ty.int] ty.bool
  | exec_bne           : Fun ["lv1" ∷ ty.lv; "lv2" :: ty.lv; "immediate" ∷ ty.int] ty.bool
  | exec_cmove         : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv ] ty.bool
  | exec_ld            : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool
  | exec_sd            : Fun ["hv" ∷ ty.hv; "lv" ∷ ty.lv; "immediate" ∷ ty.int] ty.bool
  | exec_cincoffsetimm : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv] ty.bool
  | exec_candperm      : Fun ["lv" :: ty.lv; "hv1" :: ty.hv; "hv2" :: ty.hv] ty.bool
  | exec_csetbounds    : Fun ["lv" ∷ ty.lv; "hv1" ∷ ty.hv; "hv2" ∷ ty.hv] ty.bool
  | exec_csetboundsimm : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool
  | exec_cgettag       : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool
  | exec_addi          : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool
  | exec_add           : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool
  | exec_sub           : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool
  | exec_slt           : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool
  | exec_slti          : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool
  | exec_sltu          : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool
  | exec_sltiu         : Fun ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool
  | exec_cgetperm      : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool
  | exec_cgetbase      : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool
  | exec_cgetlen       : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool
  | exec_cgetaddr      : Fun ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool
  | exec_fail          : Fun [] ty.bool
  | exec_ret           : Fun [] ty.bool
  | exec_instr         : Fun ["i" ∷ ty.instr] ty.bool
  | exec               : Fun [] ty.bool
  | step               : Fun [] ty.unit
  | loop               : Fun [] ty.unit
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∷ ty.int] ty.memval
  (* write memory *)
  | wM    : FunX ["address" ∷ ty.int; "new_value" ∷ ty.memval] ty.unit
  | dI    : FunX ["code" ∷ ty.int] ty.instr
  .

  Inductive Lem : PCtx -> Set :=
  | open_ptsreg                : Lem ["reg" :: ty.enum regname]
  | close_ptsreg (R : RegName) : Lem []
  | open_gprs                  : Lem []
  | close_gprs                 : Lem []
  | safe_move_cursor           : Lem ["c'" :: ty.cap; "c" :: ty.cap]
  | safe_sub_perm              : Lem ["c'" :: ty.cap; "c" :: ty.cap]
  | safe_within_range          : Lem ["c'" :: ty.cap; "c" :: ty.cap]
  | int_safe                   : Lem ["i" :: ty.int]
  | correctPC_subperm_R        : Lem ["c" :: ty.cap]
  | subperm_not_E              : Lem ["p" :: ty.perm; "p'" :: ty.perm]
  | safe_to_execute            : Lem ["c" :: ty.cap]
  .

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

End FunDeclKit.

Include FunDeclMixin MinCapsBase.

Section FunDefKit.

  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'a'"  := (@exp_var _ "a" _ _) : exp_scope.
  Local Notation "'c'"  := (@exp_var _ "c" _ _) : exp_scope.
  Local Notation "'e'"  := (@exp_var _ "e" _ _) : exp_scope.
  Local Notation "'hv'" := (@exp_var _ "hv" _ _) : exp_scope.
  Local Notation "'rv'" := (@exp_var _ "rv" _ _) : exp_scope.
  Local Notation "'i'"  := (@exp_var _ "i" _ _) : exp_scope.
  Local Notation "'lv'" := (@exp_var _ "lv" _ _) : exp_scope.
  Local Notation "'n'"  := (@exp_var _ "n" _ _) : exp_scope.
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

  Notation "'use' 'lemma' f args" := (stm_lemma f args%env) (at level 10, f at next level) : exp_scope.
  Notation "'use' 'lemma' f" := (stm_lemma f env.nil) (at level 10, f at next level) : exp_scope.

  (* NOTE: need to wrap s around parentheses when using this notation (not a real let binding!) *)
  Notation "'let*:' '[' perm ',' beg ',' en ',' cur ']' ':=' cap 'in' s" :=
    (stm_match_record capability cap
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "cap_permission" perm)
       "cap_begin" beg)
       "cap_end" en)
       "cap_cursor" cur)
    s) (at level 10) : exp_scope.

  Definition lemma_correctPC_not_E {Γ} (cap : Stm Γ ty.cap) : Stm Γ ty.unit :=
    let: "c" := cap in
    use lemma correctPC_subperm_R [exp_var "c"] ;;
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
    (let: "tmp" := exp_val ty.perm R in
     use lemma subperm_not_E [exp_var "tmp"; exp_var "perm"]).

  Definition fun_read_reg : Stm ["rreg" ∷ ty.enum regname] ty.word :=
    use lemma open_gprs ;;
    let: "x" := match: exp_var "rreg" in regname with
                | R0 =>
                    use lemma int_safe [exp_val ty.int 0%Z] ;;
                    exp_inl (exp_val ty.int 0%Z)
                | R1 => stm_read_register reg1
                | R2 => stm_read_register reg2
                | R3 => stm_read_register reg3
                end in
    use lemma close_gprs ;;
    stm_exp x.

  Definition fun_read_reg_cap : Stm ["creg" ∷ ty.enum regname] ty.cap :=
    let: w := call read_reg (exp_var "creg") in
    match: w with
    | inl i => fail "Err [read_reg_cap]: expect register to hold a capability"
    | inr c =>
        let*: ["p", "b", "e", "a"] := exp_var "c" in (* force record *)
        (exp_var "c")
    end.

  Definition fun_read_reg_num : Stm ["nreg" ∷ ty.enum regname ] ty.int :=
    let: w := call read_reg (exp_var "nreg") in
    match: w with
    | inl i => stm_exp i
    | inr c => fail "Err [read_reg_num]: expect register to hold a number"
    end.

  Definition fun_write_reg : Stm ["wreg" ∷ ty.enum regname; "w" ∷ ty.word] ty.unit :=
    use lemma open_gprs ;;
    match: exp_var "wreg" in regname with
    | R0 => stm_val ty.unit tt
    | R1 => stm_write_register reg1 (exp_var "w") ;; stm_val ty.unit tt
    | R2 => stm_write_register reg2 (exp_var "w") ;; stm_val ty.unit tt
    | R3 => stm_write_register reg3 (exp_var "w") ;; stm_val ty.unit tt
    end ;;
    use lemma close_gprs.

  Definition fun_next_pc : Stm [] ty.cap :=
    let: "c" := stm_read_register pc in
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
      (exp_record capability
         [ exp_var "perm";
           exp_var "beg";
           exp_var "end";
           exp_var "cur" + exp_int 1 ]).

  Definition fun_update_pc : Stm [] ty.unit :=
    let: "opc" := stm_read_register pc in
    let: "npc" := call next_pc in
    lemma_correctPC_not_E (exp_var "opc") ;;
    use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
    stm_write_register pc (exp_var "npc") ;;
    stm_val ty.unit tt.

  Definition fun_update_pc_perm : Stm ["c" :: ty.cap] ty.cap :=
    let*: ["p" , "b" , "e" , "a"] := (exp_var "c") in
    (match: exp_var "p" in permission with
     | E => let: "p" := exp_val ty.perm R in
            use lemma safe_to_execute [exp_var "c"] ;;
            exp_record capability
                       [ exp_var "p" ;
                         exp_var "b" ;
                         exp_var "e" ;
                         exp_var "a" ]
     | _ => exp_var "c"
     end).

  Definition fun_is_correct_pc : Stm ["c" :: ty.cap] ty.bool :=
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
    (let: "tmp1" := call is_perm (exp_var "perm") (exp_val ty.perm R) in
     let: "tmp2" := call is_perm (exp_var "perm") (exp_val ty.perm RW) in
     if: (exp_var "beg" <= exp_var "cur") && (exp_var "cur" < exp_var "end")
          && (exp_var "tmp1" || exp_var "tmp2")
     then stm_val ty.bool true
     else stm_val ty.bool false).

  Definition fun_is_perm : Stm ["p" :: ty.perm; "p'" :: ty.perm] ty.bool :=
    match: exp_var "p" in permission with
    | O  => match: exp_var "p'" in permission with
            | O => stm_val ty.bool true
            | _ => stm_val ty.bool false
            end
    | R  => match: exp_var "p'" in permission with
            | R => stm_val ty.bool true
            | _ => stm_val ty.bool false
            end
    | RW => match: exp_var "p'" in permission with
            | RW => stm_val ty.bool true
            | _  => stm_val ty.bool false
            end
    | E  => match: exp_var "p'" in permission with
            | E => stm_val ty.bool true
            | _ => stm_val ty.bool false
            end
    end.

  Definition fun_add_pc : Stm ["offset" ∷ ty.int] ty.unit :=
    let: "opc" := stm_read_register pc in
    let*: ["perm", "beg", "end", "cur"] := (exp_var "opc") in
    (let: "npc" := (exp_record capability
                               [ exp_var "perm";
                                 exp_var "beg";
                                 exp_var "end";
                                 exp_var "cur" + exp_var "offset" ]) in
     lemma_correctPC_not_E (exp_var "opc") ;;
     use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
     stm_write_register pc (exp_var "npc") ;;
     stm_val ty.unit tt).

  Definition fun_read_allowed : Stm ["p" ∷ ty.perm] ty.bool :=
    call is_sub_perm (exp_val (ty.enum permission) R) (exp_var "p").

  Definition fun_write_allowed : Stm ["p" ∷ ty.perm] ty.bool :=
    call is_sub_perm (exp_val (ty.enum permission) RW) (exp_var "p").

  (* Definition fun_sub_perm : Stm ["p1" ∷ ty.perm; "p2" ∷ ty.perm] ty.bool := *)
  (*   match: p1 in permission with *)
  (*   | O   => stm_val ty.bool true *)
  (*   | R   => call read_allowed p2 *)
  (*   | RW  => let: "r" := call read_allowed p2 in *)
  (*            let: "w" := call write_allowed p2 in *)
  (*            stm_exp (exp_var "r" && exp_var "w") *)
  (*   end. *)

  Definition fun_within_bounds : Stm ["c" ∷ ty.cap] ty.bool :=
    let*: ["p", "b", "e", "a"] := (exp_var "c") in
    (let: "u" := call upper_bound (exp_var "a") (exp_var "e") in
     (exp_var "b" <= exp_var "a") && exp_var "u").

  Definition fun_upper_bound : Stm ["a" ∷ ty.addr; "e" ∷ ty.addr] ty.bool :=
    a <= e.

  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty.cap.
    Let bool : Ty := ty.bool.
    Let int : Ty := ty.int.
    Let word : Ty := ty.word.

    Definition fun_exec_sd : Stm [hv ∷ ty.hv; lv ∷ ty.lv; "immediate" ∷ ty.int] ty.bool :=
      let: "base_cap" :: cap  := call read_reg_cap lv in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm";
                                       exp_var "beg";
                                       exp_var "end";
                                       exp_var "cursor" + exp_var "immediate"
                                     ] in
       let: p :: bool := call write_allowed (exp_var "perm") in
       stm_assert p (exp_string "Err: [store] no read permission") ;;
       let: w :: ty.word := call read_reg hv in
       let: "tmp" := exp_val ty.perm RW in
       use lemma subperm_not_E [exp_var "tmp"; exp_var "perm"] ;;
       use lemma safe_move_cursor [exp_var "c"; exp_var "base_cap"] ;;
       call write_mem c w ;;
       call update_pc ;;
       stm_val ty.bool true).

    Definition fun_exec_ld : Stm [lv ∷ ty.lv; hv ∷ ty.hv; "immediate" ∷ ty.int] ty.bool :=
      let: "base_cap" :: cap  := call read_reg_cap hv in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm";
                                       exp_var "beg";
                                       exp_var "end";
                                       exp_var "cursor" + exp_var "immediate"
                                     ] in
       let: p :: bool := call read_allowed (exp_var "perm") in
       stm_assert p (exp_string "Err: [load] no read permission") ;;                 
       let: "tmp" := exp_val ty.perm R in
       use lemma subperm_not_E [exp_var "tmp"; exp_var "perm"] ;;
       use lemma safe_move_cursor [exp_var "c"; exp_var "base_cap"] ;;
       let: n :: ty.memval := call read_mem c in
       call write_reg lv n ;;
       call update_pc ;;
       stm_val ty.bool true).

    Definition fun_exec_cincoffsetimm : Stm ["lv" ∷ ty.lv; "hv" ∷ ty.hv] ty.bool :=
      let: "base_cap" :: cap  := call read_reg_cap (exp_var "lv") in
      let: "offset" :: ty.int := call read_reg_num (exp_var "hv") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (match: exp_var "perm" in permission with
       | E => fail "Err: [cincoffsetimm] not permitted on enter capability"
       | _ =>
           let: "c" :: cap := exp_record capability
                                         [ exp_var "perm";
                                           exp_var "beg";
                                           exp_var "end";
                                           exp_var "cursor" + exp_var "offset"
                                         ] in
           use lemma safe_move_cursor [exp_var "c"; exp_var "base_cap"] ;;
           call write_reg (exp_var "lv") (exp_inr (exp_var "c")) ;;
           call update_pc ;;
           stm_val ty.bool true
       end).

    Definition fun_exec_candperm : Stm ["lv" :: ty.lv; "hv1" :: ty.hv; "hv2" :: ty.hv] ty.bool :=
      let: "cs_val" := call read_reg_cap (exp_var "hv1") in
      let: "rs_val" := call read_reg_num (exp_var "hv2") in
      let*: ["p", "b", "e", "a"] := exp_var "cs_val" in
      let: "p'" := call perm_from_bits (exp_var "rs_val") in
      let: "new_p"  := call and_perm (exp_var "p") (exp_var "p'") in
      let: "new_cap" :: cap := exp_record capability
                                          [ exp_var "new_p";
                                            exp_var "b";
                                            exp_var "e";
                                            exp_var "a"
                                          ] in
       use lemma safe_sub_perm [exp_var "new_cap"; exp_var "cs_val"] ;;
      call write_reg (exp_var "lv") (exp_inr (exp_var "new_cap")) ;;
      stm_val ty.bool true.

    Definition fun_exec_addi : Stm ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool :=
      let: "v" :: ty.int := call read_reg_num (exp_var "hv") in
      let: "res" :: ty.int := stm_exp (exp_var "v" + exp_var "immediate") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "lv") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_add : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      let: "res" :: int := stm_exp (exp_var "v1" + exp_var "v2") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_sub : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      let: "res" :: int := stm_exp (exp_var "v1" - exp_var "v2") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_abs : Stm ["i" ∷ ty.int] ty.int :=
      if: exp_var "i" < (exp_val ty.int 0%Z)
      then exp_var "i" * (exp_val ty.int (-1)%Z)
      else exp_var "i".

    Definition fun_exec_slt : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      (if: exp_var "v1" < exp_var "v2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_slti : Stm ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "hv") in
      let: "v2" :: int := exp_var "immediate" in
      (if: exp_var "v1" < exp_var "v2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "lv") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "lv") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_sltu : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv; "lv3" ∷ ty.lv] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "uv1" :: int := call abs (exp_var "v1") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      let: "uv2" :: int := call abs (exp_var "v2") in
      (if: exp_var "uv1" < exp_var "uv2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_sltiu : Stm ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "hv") in
      let: "uv1" :: int := call abs (exp_var "v1") in
      let: "v2" :: int := exp_var "immediate" in
      let: "uv2" :: int := call abs (exp_var "v2") in
      (if: exp_var "uv1" < exp_var "uv2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "lv") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "lv") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_perm_to_bits : Stm ["p" ∷ ty.perm] ty.int :=
      match: exp_var "p" in permission with
      | O  => stm_val ty.int 0%Z
      | R  => stm_val ty.int 1%Z
      | RW => stm_val ty.int 2%Z
      | E  => stm_val ty.int 3%Z
      end.

    Definition fun_perm_from_bits : Stm ["i" ∷ ty.int] ty.perm :=
      if: exp_var "i" = exp_val ty.int 1%Z
      then exp_val ty.perm R
      else if: exp_var "i" = exp_val ty.int 2%Z
           then exp_val ty.perm RW
           else if: exp_var "i" = exp_val ty.int 3%Z
                then exp_val ty.perm E
                else exp_val ty.perm O.

    Definition fun_and_perm : Stm ["p1" :: ty.perm; "p2" :: ty.perm] ty.perm :=
      match: exp_var "p1" in permission with
      | O  => exp_val ty.perm O
      | R  => match: exp_var "p2" in permission with
              | R  => exp_val ty.perm R
              | RW => exp_val ty.perm R
              | _  => exp_val ty.perm O
              end
      | RW => match: exp_var "p2" in permission with
              | R  => exp_val ty.perm R
              | RW => exp_val ty.perm RW
              | _  => exp_val ty.perm O
              end
      | E  => match: exp_var "p2" in permission with
              | E => exp_val ty.perm E
              | _ => exp_val ty.perm O
              end
      end.

    Definition fun_is_sub_perm : Stm ["p" ∷ ty.perm; "p'" ∷ ty.perm] ty.bool :=
      match: exp_var "p" in permission with
      | O =>
        stm_val ty.bool true
      | E => match: exp_var "p'" in permission with
             | O => stm_val ty.bool false
             | _ => stm_val ty.bool true
             end
      | R => match: exp_var "p'" in permission with
            | O => stm_val ty.bool false
            | E => stm_val ty.bool false
            | _ =>
              stm_val ty.bool true
            end
      | RW => match: exp_var "p'" in permission with
             | RW =>
               stm_val ty.bool true
            | _ => stm_val ty.bool false
            end
      end.

    Definition fun_is_within_range : Stm ["b'" ∷ ty.addr; "e'" ∷ ty.addr;
                                          "b" ∷ ty.addr; "e" ∷ ty.addr] ty.bool :=
      (exp_var "b" <= exp_var "b'") && (exp_var "e'" <= exp_var "e").

    Definition fun_exec_csetbounds : Stm ["lv" ∷ ty.lv; "hv1" ∷ ty.hv; "hv2" ∷ ty.hv]
                                     ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "hv1") in
      let*: ["p", "b", "e", "a"] := exp_var "c" in
      let: "new_begin" :: ty.int :=  exp_var "a" in
      let: "rs_val" :: ty.int := call read_reg_num (exp_var "hv2") in
      let: "new_end" :: ty.int := (exp_var "new_begin") + (exp_var "rs_val") in
      match: exp_var "p" in permission with
       | E => fail "Err: [csetbounds] not permitted on enter capability"
       | _ =>
           let: "b" :: ty.bool :=
             call is_within_range (exp_var "new_begin") (exp_var "new_end")
                                  (exp_var "b")         (exp_var "e") in
           stm_assert (exp_var "b") (exp_string "Err: [csetbounds] tried to increase range of authority") ;;
           let: "c'" :: cap := exp_record capability
                                          [ exp_var "p";
                                            exp_var "new_begin";
                                            exp_var "new_end";
                                            exp_var "a"
                                          ] in
           use lemma safe_within_range [exp_var "c'"; exp_var "c"] ;;
           call write_reg (exp_var "lv") (exp_inr (exp_var "c'")) ;;
           call update_pc ;;
           stm_val ty.bool true
       end.

    Definition fun_exec_csetboundsimm : Stm ["lv" ∷ ty.lv; "hv" ∷ ty.hv; "immediate" ∷ ty.int]
                                      ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "hv") in
      let*: ["p", "b", "e", "a"] := exp_var "c" in
      let: "new_begin" :: ty.int :=  exp_var "a" in
      let: "new_end" :: ty.int := (exp_var "new_begin") + (exp_var "immediate") in
      match: exp_var "p" in permission with
       | E => fail "Err: [csetboundsimm] not permitted on enter capability"
       | _ =>
           let: "b" :: ty.bool :=
             call is_within_range (exp_var "new_begin") (exp_var "new_end")
                                  (exp_var "b")         (exp_var "e") in
           stm_assert (exp_var "b") (exp_string "Err: [csetboundsimm] tried to increase range of authority") ;;
           let: "c'" :: cap := exp_record capability
                                          [ exp_var "p";
                                            exp_var "new_begin";
                                            exp_var "new_end";
                                            exp_var "a"
                                          ] in
           use lemma safe_within_range [exp_var "c'"; exp_var "c"] ;;
           call write_reg (exp_var "lv") (exp_inr (exp_var "c'")) ;;
           call update_pc ;;
           stm_val ty.bool true
       end.

    Definition fun_exec_cgettag : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool :=
      let: w :: ty.word := call read_reg (exp_var "lv2") in
      match: w with
      | inl i =>
        use lemma int_safe [exp_val ty.int 0%Z] ;;
        call write_reg (exp_var "lv1") (exp_inl (exp_val ty.int 0%Z))
      | inr c =>
        use lemma int_safe [exp_val ty.int 1%Z] ;;
        call write_reg (exp_var "lv1") (exp_inl (exp_val ty.int 1%Z))
      end ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetperm : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      let: "i" :: ty.int := call perm_to_bits (exp_var "perm") in
      use lemma int_safe [exp_var "i"] ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "i")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetbase : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      use lemma int_safe [exp_var "beg"] ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "beg")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetlen : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      let: "res" := (exp_var "end") - (exp_var "beg") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetaddr : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      use lemma int_safe [exp_var "cursor"] ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "cursor")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_fail : Stm [] ty.bool :=
      fail "machine failed".

    Definition fun_exec_ret : Stm [] ty.bool :=
      stm_exp exp_false.

    Definition fun_exec_cmove : Stm [lv ∷ ty.lv; hv ∷ ty.hv] ty.bool :=
      let: w :: word := call read_reg hv in
      call write_reg lv w ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_jalr : Stm ["lv1" ∷ ty.lv; "lv2" ∷ ty.lv] ty.bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      lemma_correctPC_not_E (exp_var "opc") ;;
      use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
      call write_reg (exp_var "lv1") (exp_inr (exp_var "npc")) ;;
      let: "c" :: ty.cap := call read_reg_cap (exp_var "lv2") in
      let: "c" := call update_pc_perm (exp_var "c") in
      stm_write_register pc (exp_var "c") ;;
      stm_val ty.bool true.

    Definition fun_exec_jal : Stm [lv ∷ ty.lv; offset ∷ ty.int] ty.bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      lemma_correctPC_not_E (exp_var "opc") ;;
      use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
      call write_reg lv (exp_inr (exp_var "npc")) ;;
      call add_pc (exp_binop bop.times offset (exp_int 2)) ;;
      stm_val ty.bool true.

    Definition fun_exec_bne : Stm ["lv1" ∷ ty.lv; "lv2" :: ty.lv; "immediate" ∷ ty.int] ty.bool :=
      let: "a" :: ty.int := call read_reg_num (exp_var "lv1") in
      let: "b" :: ty.int := call read_reg_num (exp_var "lv2") in
      stm_if (exp_binop bop.eq (exp_var "a") (exp_var "b"))
             (call update_pc ;; stm_val ty.bool true)
             (call add_pc (exp_var "immediate") ;; stm_val ty.bool true).

    Definition fun_exec_instr : Stm [i ∷ ty.instr] ty.bool :=
      stm_match_union_alt
        instruction (exp_var i)
        (fun K =>
           match K with
           | kjalr          => MkAlt (pat_pair "lv1" "lv2")
                                     (call exec_jalr (exp_var "lv1") (exp_var "lv2"))
           | kjal           => MkAlt (pat_pair lv offset)
                                     (call exec_jal lv offset)
           | kbne           => MkAlt (pat_tuple ("lv1" , "lv2" , immediate))
                                     (call exec_bne (exp_var "lv1") (exp_var "lv2") immediate)
           | kcmove         => MkAlt (pat_pair lv hv)
                                     (call exec_cmove lv hv)
           | kld            => MkAlt (pat_tuple (lv , hv , immediate))
                                     (call exec_ld lv hv immediate)
           | ksd            => MkAlt (pat_tuple (hv , lv , immediate))
                                     (call exec_sd hv lv immediate)
           | kcincoffsetimm => MkAlt (pat_pair lv hv)
                                     (call exec_cincoffsetimm lv hv)
           | kcandperm      => MkAlt (pat_tuple (lv , "hv1" , "hv2"))
                                     (call exec_candperm lv (exp_var "hv1") (exp_var "hv2"))
           | kcsetbounds    => MkAlt (pat_tuple (lv , "hv1" , "hv2"))
                                     (call exec_csetbounds lv (exp_var "hv1") (exp_var "hv2"))
           | kcsetboundsimm => MkAlt (pat_tuple (lv , hv , immediate))
                                     (call exec_csetboundsimm lv hv immediate)
           | kaddi          => MkAlt (pat_tuple (lv , hv , immediate))
                                     (call exec_addi lv hv immediate)
           | kadd           => MkAlt (pat_tuple ("lv1" , "lv2" , "lv3"))
                                     (call exec_add (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | ksub           => MkAlt (pat_tuple ("lv1" , "lv2" , "lv3"))
                                     (call exec_sub (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | kslt           => MkAlt (pat_tuple ("lv1" , "lv2" , "lv3"))
                                     (call exec_slt (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | kslti          => MkAlt (pat_tuple (lv , hv , immediate))
                                     (call exec_slti lv hv immediate)
           | ksltu          => MkAlt (pat_tuple ("lv1" , "lv2" , "lv3"))
                                     (call exec_sltu (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | ksltiu         => MkAlt (pat_tuple (lv , hv , immediate))
                                     (call exec_sltiu lv hv immediate)
           | kcgettag       => MkAlt (pat_pair "lv1" "lv2")
                                     (call exec_cgettag (exp_var "lv1") (exp_var "lv2"))
           | kcgetperm      => MkAlt (pat_pair "lv1" "lv2")
                                     (call exec_cgetperm (exp_var "lv1") (exp_var "lv2"))
           | kcgetbase      => MkAlt (pat_pair "lv1" "lv2")
                                     (call exec_cgetbase (exp_var "lv1") (exp_var "lv2"))
           | kcgetlen       => MkAlt (pat_pair "lv1" "lv2")
                                     (call exec_cgetlen (exp_var "lv1") (exp_var "lv2"))
           | kcgetaddr      => MkAlt (pat_pair "lv1" "lv2")
                                     (call exec_cgetaddr (exp_var "lv1") (exp_var "lv2"))
           | kfail          => MkAlt pat_unit
                                     (call exec_fail)
           | kret           => MkAlt pat_unit
                                     (call exec_ret)
           end).

    Definition fun_read_mem : Stm ["c" ∷ ty.cap] ty.memval :=
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: q :: bool := call within_bounds c in
       stm_assert q (exp_string "Err: [read_mem] out of bounds") ;;
       foreign rM (exp_var "cursor")).

    Definition fun_write_mem : Stm ["c" ∷ ty.cap; "v" ∷ ty.memval] ty.unit :=
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: q :: bool := call within_bounds c in
       stm_assert q (exp_string "Err: [write_mem] out of bounds") ;;
       foreign wM (exp_var "cursor") (exp_var "v")).

    Definition fun_exec : Stm [] ty.bool :=
      let: "c" := stm_read_register pc in
      (let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
       use lemma correctPC_subperm_R [exp_var "c"] ;;
       let: n :: ty.memval := call read_mem c in
       match: n with
       | inl n => 
           let: i :: ty.instr := foreign dI n in
           call exec_instr i
       | inr c => fail "Err [exec]: instructions cannot be capabilities"
       end).

    Definition fun_step : Stm [] ty.unit :=
      let: "tmp1" := stm_read_register pc in
      let: "tmp2" := call is_correct_pc (exp_var "tmp1") in
      if: exp_var "tmp2"
      then
        call exec ;;
        stm_val ty.unit tt
      else
        fail "Err [step]: incorrect PC".

    Definition fun_loop : Stm [] ty.unit :=
      call step ;; call loop.

  End ExecStore.

  Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | read_reg           => fun_read_reg
    | read_reg_cap       => fun_read_reg_cap
    | read_reg_num       => fun_read_reg_num
    | write_reg          => fun_write_reg
    | next_pc            => fun_next_pc
    | update_pc          => fun_update_pc
    | update_pc_perm     => fun_update_pc_perm
    | is_correct_pc      => fun_is_correct_pc
    | is_perm            => fun_is_perm
    | add_pc             => fun_add_pc
    | read_mem           => fun_read_mem
    | write_mem          => fun_write_mem
    | read_allowed       => fun_read_allowed
    | write_allowed      => fun_write_allowed
    | upper_bound        => fun_upper_bound
    | within_bounds      => fun_within_bounds
    | perm_to_bits       => fun_perm_to_bits
    | perm_from_bits     => fun_perm_from_bits
    | and_perm           => fun_and_perm
    | is_sub_perm        => fun_is_sub_perm
    | is_within_range    => fun_is_within_range
    | abs                => fun_abs
    | exec_jalr          => fun_exec_jalr
    | exec_jal           => fun_exec_jal
    | exec_bne           => fun_exec_bne
    | exec_cmove         => fun_exec_cmove
    | exec_ld            => fun_exec_ld
    | exec_sd            => fun_exec_sd
    | exec_cincoffsetimm => fun_exec_cincoffsetimm
    | exec_candperm      => fun_exec_candperm
    | exec_csetbounds    => fun_exec_csetbounds
    | exec_csetboundsimm => fun_exec_csetboundsimm
    | exec_addi          => fun_exec_addi
    | exec_add           => fun_exec_add
    | exec_sub           => fun_exec_sub
    | exec_slt           => fun_exec_slt
    | exec_slti          => fun_exec_slti
    | exec_sltu          => fun_exec_sltu
    | exec_sltiu         => fun_exec_sltiu
    | exec_cgettag       => fun_exec_cgettag
    | exec_cgetperm      => fun_exec_cgetperm
    | exec_cgetbase      => fun_exec_cgetbase
    | exec_cgetlen       => fun_exec_cgetlen
    | exec_cgetaddr      => fun_exec_cgetaddr
    | exec_fail          => fun_exec_fail
    | exec_ret           => fun_exec_ret
    | exec_instr         => fun_exec_instr
    | exec               => fun_exec
    | step               => fun_step
    | loop               => fun_loop
    end.

End FunDefKit.

Include DefaultRegStoreKit MinCapsBase.

Section ForeignKit.
  Definition Memory := Addr -> (Z + Capability).

  Definition fun_rM (μ : Memory) (addr : Val ty.int) : Val ty.memval :=
    μ addr.

  Definition fun_wM (μ : Memory) (addr : Val ty.int) (val : Val ty.memval) : Memory :=
    fun addr' => if Z.eqb addr addr' then val else μ addr'.

  #[derive(equations=no)]
  Equations ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop :=
    ForeignCall rM [addr] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , inr (fun_rM μ addr));
    ForeignCall wM [addr; val] res γ γ' μ μ' =>
      (γ' , μ' , res) = (γ , fun_wM μ addr val , inr tt);
    ForeignCall dI [code] res γ γ' μ μ' :=
      (* Non-deterministically return any possible result *)
      exists res' : Val (ty.sum ty.string ty.instr),
        (γ' , μ' , res) = (γ , μ , res').

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f; env.destroy args.
    - repeat eexists; constructor.
    - repeat eexists; constructor.
    - exists γ, μ, (inr ret), (inr ret). reflexivity.
  Qed.
End ForeignKit.

Include ProgramMixin MinCapsBase.

End MinCapsProgram.
