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
     Program.Tactics
     Strings.String
     ZArith.ZArith.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Syntax.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)

Inductive Permission : Set :=
  O | R | RW.

Inductive RegName : Set :=
  R0 | R1 | R2 | R3.

Definition LV : Set := RegName.
Definition HV : Set := RegName.
Definition RV : Set := LV + Z.

Inductive Instruction : Set :=
| jmp      (lv : LV)
| jnz      (lv : LV) (rv : RV)
| move     (lv : LV) (rv : RV)
| load     (lv : LV) (hv : HV)
| store    (hv : HV) (rv : RV)
(* | lt       (lv : LV) (rv1 rv2 : RV) *)
(* | plus     (lv : LV) (rv1 rv2 : RV) *)
(* | minus    (lv : LV) (rv1 rv2 : RV) *)
(* | lea      (lv : LV) (rv : RV) *)
(* | restrict (lv : LV) (rv : RV) *)
(* | subseg   (lv : LV) (rv1 rv2 : RV) *)
(* | isptr    (lv : LV) (rv : RV) *)
(* | getp     (lv lv' : LV) *)
(* | getb     (lv lv' : LV) *)
(* | gete     (lv lv' : LV) *)
(* | geta     (lv lv' : LV) *)
| fail
| halt.

Inductive InstructionConstructor : Set :=
| kjmp
| kjnz
| kmove
| kload
| kstore
(* | klt *)
(* | kplus *)
(* | kminus *)
(* | klea *)
(* | krestrict *)
(* | ksubseg *)
(* | kisptr *)
(* | kgetp *)
(* | kgetb *)
(* | kgete *)
(* | kgeta *)
| kfail
| khalt.

Section Records.
  Local Set Primitive Projections.

  Definition Addr : Set := Z.

  Record Capability : Set :=
    MkCap
      { cap_permission : Permission;
        cap_begin      : Addr;
        cap_end        : option Addr;
        cap_cursor     : Addr;
      }.

End Records.

(** Enums **)
Inductive Enums : Set :=
| permission
| regname.

(** Unions **)
Inductive Unions : Set :=
| instruction.

(** Records **)
Inductive Records : Set :=
| capability.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Capability.
  Derive NoConfusion for Permission.
  Derive NoConfusion for RegName.
  Derive NoConfusion for Enums.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Records.
  Derive NoConfusion for Instruction.
  Derive NoConfusion for InstructionConstructor.

End TransparentObligations.

Derive EqDec for Permission.
Derive EqDec for Capability.
Derive EqDec for RegName.

Derive EqDec for Enums.
Derive EqDec for Unions.
Derive EqDec for Records.
Derive EqDec for Instruction.
Derive EqDec for InstructionConstructor.

Module MinCapsTypeKit <: TypeKit.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬𝑲 (e : 𝑬) : Set :=
    match e with
    | permission => Permission
    | regname    => RegName
    end.
  Program Instance Blastable_𝑬𝑲 e : Blastable (𝑬𝑲 e) :=
    {| blast v POST := POST v |}.
  Solve All Obligations with auto.

  Definition 𝑼        := Unions.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    | instruction => Instruction
    end.
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.
  Program Instance Blastable_𝑼𝑲 U : Blastable (𝑼𝑲 U) :=
    match U with
    | instruction => {| blast v POST := POST v |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  Definition 𝑹        := Records.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    | capability => Capability
    end.

  Definition 𝑿        := string.

  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲_eq_dec : forall (e : 𝑬), EqDec (𝑬𝑲 e).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑼_eq_dec := Unions_eqdec.
  Definition 𝑼𝑻_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑻 u).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑼𝑲_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑲 u).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑹_eq_dec := Records_eqdec.
  Definition 𝑹𝑻_eq_dec : forall (r : 𝑹), EqDec (𝑹𝑻 r).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑿_eq_dec := string_dec.

  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.
  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.

End MinCapsTypeKit.
Module MinCapsTypes := Types MinCapsTypeKit.
Import MinCapsTypes.

Definition ty_hv : Ty := ty_enum regname.
Definition ty_lv : Ty := ty_enum regname.
Definition ty_rv : Ty := (ty_sum (ty_enum regname) ty_int).
Definition ty_word : Ty := ty_sum ty_int (ty_record capability).
Definition ty_memval : Ty := ty_int.
Definition ty_addr : Ty := ty_int.
Definition ty_perm : Ty := ty_enum permission.
Definition ty_instr : Ty := ty_union instruction.

(*** TERMS ***)

Module MinCapsTermKit <: (TermKit MinCapsTypeKit).
  Module TY := MinCapsTypes.

  (** UNIONS **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | instruction => fun K =>
      match K with
      | kjmp      => ty_lv
      | kjnz      => ty_prod ty_lv ty_rv
      | kmove     => ty_prod ty_lv ty_rv
      | kload     => ty_prod ty_lv ty_hv
      | kstore    => ty_prod ty_lv ty_rv
      (* | klt       => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kplus     => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kminus    => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | klea      => ty_prod ty_lv ty_rv *)
      (* | krestrict => ty_prod ty_lv ty_rv *)
      (* | ksubseg   => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kisptr    => ty_prod ty_lv ty_rv *)
      (* | kgetp     => ty_prod ty_lv ty_lv *)
      (* | kgetb     => ty_prod ty_lv ty_lv *)
      (* | kgete     => ty_prod ty_lv ty_lv *)
      (* | kgeta     => ty_prod ty_lv ty_lv *)
      | kfail     => ty_unit
      | khalt     => ty_unit
      end
    end.

  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | existT kjmp      lv                 => jmp lv
      | existT kjnz      (lv , rv)          => jnz lv rv
      | existT kmove     (lv , rv)          => move lv rv
      | existT kload     (lv , hv)          => load lv hv
      | existT kstore    (hv , rv)          => store hv rv
      (* | existT klt       (lv , (rv1 , rv2)) => lt lv rv1 rv2 *)
      (* | existT kplus     (lv , (rv1 , rv2)) => plus lv rv1 rv2 *)
      (* | existT kminus    (lv , (rv1 , rv2)) => minus lv rv1 rv2 *)
      (* | existT klea      (lv , rv)          => lea lv rv *)
      (* | existT krestrict (lv , rv)          => restrict lv rv *)
      (* | existT ksubseg   (lv , (rv1 , rv2)) => subseg lv rv1 rv2 *)
      (* | existT kisptr    (lv , rv)          => isptr lv rv *)
      (* | existT kgetp     (lv , lv')         => getp lv lv' *)
      (* | existT kgetb     (lv , lv')         => getb lv lv' *)
      (* | existT kgete     (lv , lv')         => gete lv lv' *)
      (* | existT kgeta     (lv , lv')         => geta lv lv' *)
      | existT kfail     tt                 => fail
      | existT khalt     tt                 => halt
      end
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    | instruction => fun Kv =>
      match Kv with
      | jmp lv            => existT kjmp      lv
      | jnz lv rv         => existT kjnz      (lv , rv)
      | move lv rv        => existT kmove     (lv , rv)
      | load lv hv        => existT kload     (lv , hv)
      | store hv rv       => existT kstore    (hv , rv)
      (* | lt lv rv1 rv2     => existT klt       (lv , (rv1 , rv2)) *)
      (* | plus lv rv1 rv2   => existT kplus     (lv , (rv1 , rv2)) *)
      (* | minus lv rv1 rv2  => existT kminus    (lv , (rv1 , rv2)) *)
      (* | lea lv rv         => existT klea      (lv , rv) *)
      (* | restrict lv rv    => existT krestrict (lv , rv) *)
      (* | subseg lv rv1 rv2 => existT ksubseg   (lv , (rv1 , rv2)) *)
      (* | isptr lv rv       => existT kisptr    (lv , rv) *)
      (* | getp lv lv'       => existT kgetp     (lv , lv') *)
      (* | getb lv lv'       => existT kgetb     (lv , lv') *)
      (* | gete lv lv'       => existT kgete     (lv , lv') *)
      (* | geta lv lv'       => existT kgeta     (lv , lv') *)
      | fail              => existT kfail     tt
      | halt              => existT khalt     tt
      end
    end.
  Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold U (𝑼_unfold U Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) }),
      𝑼_unfold U (𝑼_fold U Kv) = Kv.
  Proof.
    intros [] [[] x]; cbn in x;
      repeat match goal with
             | x: unit     |- _ => destruct x
             | x: prod _ _ |- _ => destruct x
             end; auto.
  Qed.

  (** RECORDS **)
  Definition 𝑹𝑭  : Set := string.

  Definition 𝑹𝑭_Ty (R : 𝑹) : Ctx (𝑹𝑭 * Ty) :=
    match R with
    | capability => [ "cap_permission" ∶ ty_perm,
                      "cap_begin"      ∶ ty_addr,
                      "cap_end"        ∶ ty_option ty_addr,
                      "cap_cursor"     ∶ ty_addr
                    ]
    end.

  Definition 𝑹_fold (R : 𝑹) : NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R :=
    match R with
    | capability =>
      fun fields =>
        MkCap
          (fields ‼ "cap_permission")
          (fields ‼ "cap_begin")
          (fields ‼ "cap_end")
          (fields ‼ "cap_cursor")
    end%lit.

  Definition 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Lit (𝑹𝑭_Ty R) :=
    match R  with
    | capability =>
      fun c=>
        env_nil
          ► "cap_permission" ∶ ty_perm ↦ cap_permission c
          ► "cap_begin"      ∶ ty_addr            ↦ cap_begin c
          ► "cap_end"        ∶ ty_option ty_addr  ↦ cap_end c
          ► "cap_cursor"     ∶ ty_addr            ↦ cap_cursor c
    end%env.
  Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold R (𝑹_unfold R Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold R (𝑹_fold R Kv) = Kv.
  Proof. intros []; now apply Forall_forall. Qed.

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | read_reg       : Fun ["reg" ∶ ty_enum regname ] ty_word
  | read_reg_cap   : Fun ["reg" ∶ ty_enum regname ] (ty_record capability)
  | read_reg_num   : Fun ["reg" ∶ ty_enum regname ] ty_int
  | write_reg      : Fun ["reg" ∶ ty_enum regname,
                          "w"  ∶ ty_word
                         ] ty_unit
  | update_pc      : Fun ctx_nil ty_unit
  | read_mem       : Fun ["a"   ∶ ty_addr ] ty_memval
  | write_mem      : Fun ["a"   ∶ ty_addr,
                          "v"   ∶ ty_memval
                         ] ty_unit
  | read_allowed   : Fun ["p"   ∶ ty_perm ] ty_bool
  | write_allowed  : Fun ["p"   ∶ ty_perm ] ty_bool
  | sub_perm       : Fun ["p1"  ∶ ty_perm,
                          "p2"  ∶ ty_perm
                         ] ty_bool
  | upper_bound    : Fun ["a"   ∶ ty_addr,
                          "e"   ∶ ty_option ty_addr
                         ] ty_bool
  | within_bounds  : Fun ["c"   ∶ ty_record capability ] ty_bool
  | compute_rv     : Fun ["rv" ∶ ty_rv] ty_word
  | compute_rv_num : Fun ["rv" ∶ ty_rv] ty_int
  | exec_move      : Fun ["lv" ∶ ty_lv, "rv" ∶ ty_rv ] ty_unit
  | exec_load      : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_unit
  | exec_store     : Fun ["lv" ∶ ty_lv, "rv" ∶ ty_rv ] ty_unit
  .

  Inductive FunX : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_int
  (* write memory *)
  | wM    : FunX ["address" ∶ ty_int, "mem_value" ∶ ty_int] ty_unit
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : Ctx (𝑿 * Ty) -> Ty -> Set := FunX.

  Inductive Reg : Ty -> Set :=
    | pc   : Reg (ty_record capability)
    | reg0 : Reg ty_word
    | reg1 : Reg ty_word
    | reg2 : Reg ty_word
    | reg3 : Reg ty_word.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec {σ τ} (x : 𝑹𝑬𝑮 σ) (y : 𝑹𝑬𝑮 τ) : {x ≡ y}+{~ x ≡ y}.
  Proof.
    destruct x; destruct y; cbn;
      first
        [ left; now apply teq_refl with eq_refl
        | right; intros [eqt eqr];
          try rewrite <- (Eqdep_dec.eq_rect_eq_dec Ty_eq_dec) in eqr; discriminate
        ].
  Defined.

  Definition 𝑨𝑫𝑫𝑹 : Set := Empty_set.

End MinCapsTermKit.
Module MinCapsTerms := Terms MinCapsTypeKit MinCapsTermKit.
Import MinCapsTerms.

(*** PROGRAM ***)

Module MinCapsProgramKit <: (ProgramKit MinCapsTypeKit MinCapsTermKit).
  Module TM := MinCapsTerms.

  Local Notation "'c'"  := (@exp_var _ "c" _ _) : exp_scope.
  Local Notation "'hv'" := (@exp_var _ "hv" _ _) : exp_scope.
  Local Notation "'rv'" := (@exp_var _ "rv" _ _) : exp_scope.
  Local Notation "'i'"  := (@exp_var _ "i" _ _) : exp_scope.
  Local Notation "'lv'" := (@exp_var _ "lv" _ _) : exp_scope.
  Local Notation "'n'"  := (@exp_var _ "n" _ _) : exn_scope.
  Local Notation "'p'"  := (@exp_var _ "p" _ _) : exp_scope.
  Local Notation "'q'"  := (@exp_var _ "q" _ _) : exp_scope.
  Local Notation "'r'"  := (@exp_var _ "r" _ _) : exp_scope.
  Local Notation "'w'"  := (@exp_var _ "w" _ _) : exp_scope.

  Local Notation "'c'"  := "c" : string_scope.
  Local Notation "'hv'" := "hv" : string_scope.
  Local Notation "'rv'" := "rv" : string_scope.
  Local Notation "'i'"  := "i" : string_scope.
  Local Notation "'lv'" := "lv" : string_scope.
  Local Notation "'n'"  := "n" : string_scope.
  Local Notation "'p'"  := "p" : string_scope.
  Local Notation "'q'"  := "q" : string_scope.
  Local Notation "'r'"  := "r" : string_scope.
  Local Notation "'w'"  := "w" : string_scope.

  Definition fun_read_reg : Stm ["reg" ∶ ty_enum regname ] ty_word :=
    match: exp_var "reg" in regname with
    | R0 => stm_read_register reg0
    | R1 => stm_read_register reg1
    | R2 => stm_read_register reg2
    | R3 => stm_read_register reg3
    end.

  Definition fun_read_reg_cap : Stm ["reg" ∶ ty_enum regname ] (ty_record capability) :=
    let: w := call read_reg (exp_var "reg") in
    match: w with
    | inl i => fail "Err [read_reg_cap]: expect register to hold a capability"
    | inr c => stm_exp c
    end.

  Definition fun_read_reg_num : Stm ["reg" ∶ ty_enum regname ] ty_int :=
    let: w := call read_reg (exp_var "reg") in
    match: w with
    | inl i => stm_exp i
    | inr c => fail "Err [read_reg_num]: expect register to hold a number"
    end.

  Definition fun_write_reg : Stm ["r" ∶ ty_enum regname,
                                  "w" ∶ ty_word
                                 ] ty_unit :=
    match: exp_var "r" in regname with
    | R0 => stm_write_register reg0 (exp_var "w")
    | R1 => stm_write_register reg1 (exp_var "w")
    | R2 => stm_write_register reg2 (exp_var "w")
    | R3 => stm_write_register reg3 (exp_var "w")
    end ;; stm_lit ty_unit tt.

  Definition fun_update_pc : Stm ctx_nil ty_unit :=
    let: "c" := stm_read_register pc in
    stm_write_register pc
      (exp_record capability
                      [ ((exp_var "c")․"cap_permission"),
                        ((exp_var "c")․"cap_begin"),
                        ((exp_var "c")․"cap_end"),
                        ((exp_var "c")․"cap_cursor") + lit_int 1
                      ]%exp%arg) ;;
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

  Definition fun_sub_perm : Stm ["p" ∶ ty_perm, "q" ∶ ty_perm] ty_bool :=
    match: p in permission with
    | O   => stm_lit ty_bool true
    | R   => call read_allowed q
    | RW  => let: "r" := call read_allowed q in
             let: "w" := call write_allowed q in
             stm_exp (exp_var "r" && exp_var "w")
    end.

  Definition fun_within_bounds : Stm ["c" ∶ ty_record capability ] ty_bool :=
    stm_match_record capability (exp_var "c")
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
      "cap_permission" "p")
      "cap_begin" "b")
      "cap_end" "e")
      "cap_cursor" "a")
      (let: "u" := call upper_bound (exp_var "a") (exp_var "e") in
       stm_exp (exp_var "u" && (exp_var "b" <= exp_var "a"))).

  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty_record capability.
    Let bool : Ty := ty_bool.
    Let int : Ty := ty_int.
    Let word : Ty := ty_word.

    Definition fun_exec_store : Stm [lv ∶ ty_lv, rv ∶ ty_rv] ty_unit :=
      let: c ∶ cap  := call read_reg_cap lv in
      let: p ∶ bool := call write_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_store] no write permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_store] out of bounds") ;;
      let: w ∶ int := call compute_rv_num rv in
      call write_mem c․cursor w ;;
      call update_pc.

    Definition fun_exec_load : Stm [lv ∶ ty_lv, hv ∶ ty_hv] ty_unit :=
      let: c ∶ cap  := call read_reg_cap hv in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_load] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_load] out of bounds") ;;
      let: n ∶ ty_memval := call read_mem c․cursor in
      call write_reg lv (exp_inl (exp_var n)) ;;
      call update_pc.

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


    Definition fun_exec_move : Stm [lv ∶ ty_lv, rv ∶ ty_rv] ty_unit :=
      let: w ∶ word := call compute_rv (exp_var rv) in
      call write_reg lv (exp_var w) ;;
      call update_pc.

    Definition fun_exec_instr : Stm [i ∶ ty_instr] ty_unit :=
      stm_match_union instruction (exp_var i)
                      (fun K => match K with
                            | kjmp => alt _ (pat_var lv) (stm_exp (exp_lit _ ty_unit tt))
                            | kjnz => alt _ (pat_pair lv rv) (stm_exp (exp_lit _ ty_unit tt))
                            | kmove => alt _ (pat_pair lv rv) (call exec_move lv rv)
                            | kload => alt _ (pat_pair lv hv) (call exec_load (exp_var lv) (exp_var hv))
                            | kstore => alt _ (pat_pair lv rv) (call exec_store (exp_var lv) (exp_var rv))
                            | kfail => alt _ pat_unit (stm_exp (exp_lit _ ty_unit tt))
                            | khalt => alt _ pat_unit (stm_exp (exp_lit _ ty_unit tt))
                            end).

  End ExecStore.

  Program Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | read_reg       => fun_read_reg
    | read_reg_cap   => fun_read_reg_cap
    | read_reg_num   => fun_read_reg_num
    | write_reg      => fun_write_reg
    | update_pc      => fun_update_pc
    | read_mem       => _
    | write_mem      => _
    | read_allowed   => fun_read_allowed
    | write_allowed  => fun_write_allowed
    | sub_perm       => fun_sub_perm
    | upper_bound    => _
    | within_bounds  => fun_within_bounds
    | exec_move      => fun_exec_move
    | exec_load      => fun_exec_load
    | exec_store     => fun_exec_store
    | compute_rv     => fun_compute_rv
    | compute_rv_num => fun_compute_rv_num
    end.
  Admit Obligations of Pi.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* MEMORY *)
  Definition Memory := Z -> option Z.

  Definition fun_rM (μ : Memory) (addr : Lit ty_int) : string + Lit ty_int :=
    match μ addr with
    | Some v => inr v
    | None   => inl "Err [fun_rM]: invalid address"
    end.

  Definition fun_wM (μ : Memory) (addr val : Lit ty_int) : Memory :=
    fun addr' => if Z.eqb addr addr' then Some val else μ addr'.

  Inductive CallEx : forall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
  | callex_rM {addr : Z} {γ : RegStore} {μ : Memory} :
      CallEx rM (env_snoc env_nil (_ , ty_int) addr)
             (fun_rM μ addr)
             γ γ μ μ
  | callex_wM {addr val : Z} {γ : RegStore} {μ : Memory} :
      CallEx wM (env_snoc (env_snoc env_nil (_ , ty_int) addr) (_ , ty_int) val)
             (inr tt)
             γ γ μ (fun_wM μ addr val)
  .

  Definition ExternalCall := @CallEx.

  Lemma ExternalProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ExternalCall f args res γ γ' μ μ'.
  Proof. destruct f; cbn; repeat depelim args; repeat eexists; constructor. Qed.

End MinCapsProgramKit.

Module MinCapsPrograms :=
  Programs MinCapsTypeKit MinCapsTermKit MinCapsProgramKit.
Import MinCapsPrograms.
Import MinCapsProgramKit.

(*** CONTRACTS ***)

Module MinCapsContracts.
  Module MinCapsAssertionKit <:
    (AssertionKit MinCapsTypeKit MinCapsTermKit MinCapsProgramKit).
    Module PM := Programs MinCapsTypeKit MinCapsTermKit MinCapsProgramKit.

    Definition 𝑷 := Empty_set.
    Definition 𝑷_Ty : 𝑷 -> Ctx Ty := fun p => match p with end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := fun p => match p with end.
  End MinCapsAssertionKit.

  Module MinCapsAssertions :=
    Assertions MinCapsTypeKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.
  Import MinCapsAssertions.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

  Module MinCapsSymbolicContractKit <:
    SymbolicContractKit MinCapsTypeKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.
    Module ASS := MinCapsAssertions.

    Open Scope env_scope.

    (* Arguments asn_prop [_] & _. *)

    (*
      v : word
      @pre reg ↦ v;
      @post reg ↦ v * result = v;
      word read_reg(reg : regname);

      c : capability
      @pre reg ↦ (inr c);
      @post reg ↦ (inr c) * result = c;
      cap read_reg_cap(reg: regname);

      n : int
      @pre reg ↦ (inl n);
      @post reg ↦ (inl n) * result = n;
      int read_reg_num(reg: regname);

      w : word
      @pre reg ↦ w;
      @post reg ↦ rv;
      unit write_reg(reg : regname, rv : rv);

      @pre pc ↦ mkcap(b,e,a,p);
      @post pc ↦ mkcap(b,e,suc a,p);
      unit update_pc();

      hv : memval
      @pre a ↦m hv;
      @post a ↦m hv * result = hv;
      hv read_mem(a : addr);

      hv : memval
      @pre a ↦m hv;
      @post  a ↦m v;
      unit write_mem(a : addr, v : memval);

      @pre true;
      @post result == (p == r ∨ p == rw);
      bool read_allowed(p : perm);

      @pre true;
      @post result == (p == rw);
      bool write_allowed(p : perm);

      @pre true;
      @post ?;
      bool sub_perm(p1 : perm, p2 : perm);

      @pre ?;
      @post ?;
      bool upper_bound(a : addr, e : option addr);

      @pre ?;
      @post ?;
      bool within_bounds(c : capability);

      @pre ?;
      @post ?;
      unit exec_store(lv : lv, hv : memval)
    *)

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
          | read_reg =>
             @sep_contract_result
             ["reg" ∶ ty_enum regname]
             ty_word
             ["reg" ∶ ty_enum regname]
             [term_var "reg"]%arg
             "result"
             asn_true
             asn_true
          | read_reg_cap =>
             @sep_contract_result
             ["reg" ∶ ty_enum regname]
             (ty_record capability)
             ["reg" ∶ ty_enum regname]
             [term_var "reg"]%arg
             "result"
             asn_true
             asn_true
          | read_reg_num =>
             @sep_contract_result
             ["reg" ∶ ty_enum regname]
             ty_int
             ["reg" ∶ ty_enum regname]
             [term_var "reg"]%arg
             "result"
             asn_true
             asn_true
          | write_reg =>
             @sep_contract_result
               ["reg" ∶ ty_enum regname,
                "rv" ∶ ty_rv
               ]
               ty_unit
               ["reg" ∶ ty_enum regname,
                "rv" ∶ ty_rv
               ]
               [term_var "reg", term_var "rv"]%arg
               "result"
               asn_true
               asn_true
          | update_pc =>
             @sep_contract_result
               ε
               ty_unit
               ε
               env_nil%arg
               "result"
               asn_true
               asn_true
          | read_mem =>
             @sep_contract_result
               ["a" ∶ ty_addr]
               ty_hv
               ["a" ∶ ty_addr]
               [term_var "a"]%arg
               "result"
               asn_true
               asn_true
          | write_mem =>
             @sep_contract_result
               ["a" ∶ ty_addr, "v" ∶ ty_memval]
               ty_unit
               ["a" ∶ ty_addr, "v" ∶ ty_memval]
               [term_var "a", term_var "v"]%arg
               "result"
               asn_true
               asn_true
          | read_allowed =>
             @sep_contract_result
               ["p" ∶ ty_perm]
               ty_bool
               ["p" ∶ ty_perm]
               [term_var "p"]%arg
               "result"
               asn_true
               asn_true
          | write_allowed =>
             @sep_contract_result
               ["p" ∶ ty_perm]
               ty_bool
               ["p" ∶ ty_perm]
               [term_var "p"]%arg
               "result"
               asn_true
               asn_true
          | sub_perm =>
             @sep_contract_result
               ["p1" ∶ ty_perm, "p2" ∶ ty_perm]
               ty_bool
               ["p1" ∶ ty_perm, "p2" ∶ ty_perm]
               [term_var "p1", term_var "p2"]%arg
               "result"
               asn_true
               asn_true
          | upper_bound =>
             @sep_contract_result
               ["a" ∶ ty_addr, "e" ∶ ty_option ty_addr]
               ty_bool
               ["a" ∶ ty_addr, "e" ∶ ty_option ty_addr]
               [term_var "a", term_var "e"]%arg
               "result"
               asn_true
               asn_true
          | within_bounds =>
             @sep_contract_result
               ["c" ∶ ty_record capability]
               ty_bool
               ["c" ∶ ty_record capability]
               [term_var "c"]%arg
               "result"
               asn_true
               asn_true
          | exec_store =>
             @sep_contract_result
               ["lv" ∶ ty_lv, "hv" ∶ ty_memval]
               ty_unit
               ["lv" ∶ ty_lv, "hv" ∶ ty_memval]
               [term_var "lv", term_var "hv"]%arg
               "result"
               asn_true
               asn_true
        (* | abs => *)
        (*   @sep_contract_result *)
        (*     ["x" ∶ ty_int] *)
        (*     ty_int *)
        (*     ["x" ∶ ty_int] *)
        (*     [term_var "x"]%arg *)
        (*     "result" *)
        (*     asn_true *)
        (*     (@asn_prop *)
        (*        ["x" ∶ ty_int, "result" ∶ ty_int] *)
        (*        (fun x result => result = Z.abs x)) *)
        (*     (* (asn_if *) *)
        (*     (*    (term_binop binop_lt (term_var "x") (term_lit ty_int 0)) *) *)
        (*     (*    (asn_bool (term_binop binop_eq (term_var "result") (term_neg (term_var "x")))) *) *)
        (*     (*    (asn_bool (term_binop binop_eq (term_var "result") (term_var "x")))) *) *)
        (* | cmp => *)
        (*   @sep_contract_result *)
        (*     ["x" ∶ ty_int, "y" ∶ ty_int] *)
        (*     (ty_enum ordering) *)
        (*     ["x" ∶ ty_int, "y" ∶ ty_int] *)
        (*     [term_var "x", term_var "y"]%arg *)
        (*     "result" *)
        (*     asn_true *)
        (*     (asn_match_enum *)
        (*        ordering (term_var "result") *)
        (*        (fun result => *)
        (*           match result with *)
        (*           | LT => asn_bool (term_binop binop_lt (term_var "x") (term_var "y")) *)
        (*           | EQ => asn_bool (term_binop binop_eq (term_var "x") (term_var "y")) *)
        (*           | GT => asn_bool (term_binop binop_gt (term_var "x") (term_var "y")) *)
        (*           end)) *)
        (* | gcd => *)
        (*   @sep_contract_result *)
        (*     ["x" ∶ ty_int, "y" ∶ ty_int] *)
        (*     ty_int *)
        (*     ["x" ∶ ty_int, "y" ∶ ty_int] *)
        (*     [term_var "x", term_var "x"]%arg *)
        (*     "result" *)
        (*     asn_true *)
        (*     (@asn_prop *)
        (*        ["x" ∶ ty_int, "y" ∶ ty_int, "result" ∶ ty_int] *)
        (*        (fun x y result => result = Z.gcd x y)) *)
        (* | gcdloop => *)
        (*   @sep_contract_result *)
        (*     ["x" ∶ ty_int, "y" ∶ ty_int] *)
        (*     ty_int *)
        (*     ["x" ∶ ty_int, "y" ∶ ty_int] *)
        (*     [term_var "x", term_var "x"]%arg *)
        (*     "result" *)
        (*     (asn_bool (term_binop binop_le (term_lit ty_int 0) (term_var "x")) ✱ *)
        (*      asn_bool (term_binop binop_le (term_lit ty_int 0) (term_var "y"))) *)
        (*     (@asn_prop *)
        (*        ["x" ∶ ty_int, "y" ∶ ty_int, "result" ∶ ty_int] *)
        (*        (fun x y result => result = Z.gcd x y)) *)
        (* | msum => sep_contract_none _ _ *)
        (* | @length σ => *)
        (*   @sep_contract_result *)
        (*     ["xs" ∶ ty_list σ ] *)
        (*     ty_int *)
        (*     ["xs" ∶ ty_list σ ] *)
        (*     [term_var "xs"]%arg *)
        (*     "result" *)
        (*     asn_true *)
        (*     (@asn_prop *)
        (*        ["xs" ∶ ty_list σ, "result" ∶ ty_int] *)
        (*        (fun xs result => result = Z.of_nat (Datatypes.length xs))) *)
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with end.

  End MinCapsSymbolicContractKit.

  Module MinCapsMutators :=
    Mutators
      MinCapsTypeKit
      MinCapsTermKit
      MinCapsProgramKit
      MinCapsAssertionKit
      MinCapsSymbolicContractKit.
  Import MinCapsMutators.

  Local Ltac solve :=
    repeat
      (repeat intro;
       repeat
         match goal with
         | H: NamedEnv _ _ |- _ => unfold NamedEnv in H
         | H: Env _ ctx_nil |- _ => dependent destruction H
         | H: Env _ (ctx_snoc _ _) |- _ => dependent destruction H
         | H: _ /\ _ |- _ => destruct H
         | |- _ /\ _ => constructor
         end;
       compute
       - [Pos.of_succ_nat List.length Pos.succ Z.pos_sub Z.succ Z.of_nat Z.add
          Z.gtb Z.eqb Z.ltb Lit
         ] in *;
       cbn [List.length];
       subst; try congruence; try lia;
       auto
      ).

  Lemma valid_contract_length {σ} : ValidContractDynMut (CEnv (@length σ)) (Pi length).
  Proof.
    constructor.
    - solve.
    - exists [term_var "ys"]%arg; solve.
  Qed.
  Hint Resolve valid_contract_length : contracts.

  Lemma valid_contract_cmp : ValidContractDynMut (CEnv cmp) (Pi cmp).
  Proof.
    constructor.
    { exists LT; solve. }
    constructor.
    { exists EQ; solve. }
    constructor.
    { exists GT; solve. }
    { solve.
      destruct (Z.gtb_spec db db0); try discriminate.
      destruct (Z.eqb_spec db db0); try discriminate.
      destruct (Z.ltb_spec db db0); try discriminate.
      lia.
    }
  Qed.
  Hint Resolve valid_contract_cmp : contracts.

End MinimalCapsContracts.
