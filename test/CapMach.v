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
  O | E | R | RX | RW | RWX.

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
| lt       (lv : LV) (rv1 rv2 : RV)
| plus     (lv : LV) (rv1 rv2 : RV)
| minus    (lv : LV) (rv1 rv2 : RV)
| lea      (lv : LV) (rv : RV)
| restrict (lv : LV) (rv : RV)
| subseg   (lv : LV) (rv1 rv2 : RV)
| isptr    (lv : LV) (rv : RV)
| getp     (lv lv' : LV)
| getb     (lv lv' : LV)
| gete     (lv lv' : LV)
| geta     (lv lv' : LV)
| fail
| halt.

Inductive InstructionConstructor : Set :=
| kjmp
| kjnz
| kmove
| kload
| kstore
| klt
| kplus
| kminus
| klea
| krestrict
| ksubseg
| kisptr
| kgetp
| kgetb
| kgete
| kgeta
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

Module CapTypeKit <: TypeKit.

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

End CapTypeKit.
Module CapTypes := Types CapTypeKit.
Import CapTypes.

Definition ty_hv : Ty := ty_enum regname.
Definition ty_lv : Ty := ty_enum regname.
Definition ty_rv : Ty := (ty_sum (ty_enum regname) ty_int).
Definition ty_addr : Ty := ty_int.

(*** TERMS ***)

Module CapTermKit <: (TermKit CapTypeKit).
  Module TY := CapTypes.

  (** UNIONS **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | instruction => fun K =>
      match K with
      | kjmp      => ty_lv
      | kjnz      => ty_prod ty_lv ty_rv
      | kmove     => ty_prod ty_lv ty_rv
      | kload     => ty_prod ty_lv ty_hv
      | kstore    => ty_prod ty_hv ty_rv
      | klt       => ty_prod ty_lv (ty_prod ty_rv ty_rv)
      | kplus     => ty_prod ty_lv (ty_prod ty_rv ty_rv)
      | kminus    => ty_prod ty_lv (ty_prod ty_rv ty_rv)
      | klea      => ty_prod ty_lv ty_rv
      | krestrict => ty_prod ty_lv ty_rv
      | ksubseg   => ty_prod ty_lv (ty_prod ty_rv ty_rv)
      | kisptr    => ty_prod ty_lv ty_rv
      | kgetp     => ty_prod ty_lv ty_lv
      | kgetb     => ty_prod ty_lv ty_lv
      | kgete     => ty_prod ty_lv ty_lv
      | kgeta     => ty_prod ty_lv ty_lv
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
      | existT klt       (lv , (rv1 , rv2)) => lt lv rv1 rv2
      | existT kplus     (lv , (rv1 , rv2)) => plus lv rv1 rv2
      | existT kminus    (lv , (rv1 , rv2)) => minus lv rv1 rv2
      | existT klea      (lv , rv)          => lea lv rv
      | existT krestrict (lv , rv)          => restrict lv rv
      | existT ksubseg   (lv , (rv1 , rv2)) => subseg lv rv1 rv2
      | existT kisptr    (lv , rv)          => isptr lv rv
      | existT kgetp     (lv , lv')         => getp lv lv'
      | existT kgetb     (lv , lv')         => getb lv lv'
      | existT kgete     (lv , lv')         => gete lv lv'
      | existT kgeta     (lv , lv')         => geta lv lv'
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
      | lt lv rv1 rv2     => existT klt       (lv , (rv1 , rv2))
      | plus lv rv1 rv2   => existT kplus     (lv , (rv1 , rv2))
      | minus lv rv1 rv2  => existT kminus    (lv , (rv1 , rv2))
      | lea lv rv         => existT klea      (lv , rv)
      | restrict lv rv    => existT krestrict (lv , rv)
      | subseg lv rv1 rv2 => existT ksubseg   (lv , (rv1 , rv2))
      | isptr lv rv       => existT kisptr    (lv , rv)
      | getp lv lv'       => existT kgetp     (lv , lv')
      | getb lv lv'       => existT kgetb     (lv , lv')
      | gete lv lv'       => existT kgete     (lv , lv')
      | geta lv lv'       => existT kgeta     (lv , lv')
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
    | capability => [ "cap_permission" ∶ ty_enum permission,
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
          ► "cap_permission" ∶ ty_enum permission ↦ cap_permission c
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
  | read_reg       : Fun ["reg" ∶ ty_enum regname ] (ty_sum ty_int (ty_record capability))
  | read_reg_cap   : Fun ["reg" ∶ ty_enum regname ] (ty_record capability)
  | write_reg      : Fun ["reg" ∶ ty_enum regname,
                          "rv"  ∶ ty_rv
                         ] ty_unit
  | update_pc      : Fun ctx_nil ty_unit
  | read_mem       : Fun ["a"   ∶ ty_addr ] ty_hv
  | write_mem      : Fun ["a"   ∶ ty_addr,
                          "v"   ∶ ty_int
                         ] ty_unit
  | read_allowed   : Fun ["p"   ∶ ty_enum permission ] ty_bool
  | write_allowed  : Fun ["p"   ∶ ty_enum permission ] ty_bool
  | exec_allowed   : Fun ["p"   ∶ ty_enum permission ] ty_bool
  | sub_perm       : Fun ["p1"  ∶ ty_enum permission,
                          "p2"  ∶ ty_enum permission
                         ] ty_bool
  | upper_bound    : Fun ["a"   ∶ ty_addr,
                          "e"   ∶ ty_option ty_addr
                         ] ty_bool
  | within_bounds  : Fun ["c"   ∶ ty_record capability ] ty_bool
  | exec_store     : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_unit
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.

  Inductive Reg : Ty -> Set :=
    | pc   : Reg (ty_sum ty_int (ty_record capability))
    | reg0 : Reg (ty_sum ty_int (ty_record capability))
    | reg1 : Reg (ty_sum ty_int (ty_record capability))
    | reg2 : Reg (ty_sum ty_int (ty_record capability))
    | reg3 : Reg (ty_sum ty_int (ty_record capability)).

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

End CapTermKit.
Module CapTerms := Terms CapTypeKit CapTermKit.
Import CapTerms.

(*** PROGRAM ***)

Module CapProgramKit <: (ProgramKit CapTypeKit CapTermKit).
  Module TM := CapTerms.

  Local Coercion stm_exp : Exp >-> Stm.
  Local Open Scope exp_scope.
  Local Open Scope stm_scope.

  Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
  Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

  Definition fun_read_reg : Stm ["reg" ∶ ty_enum regname ]
                                (ty_sum ty_int (ty_record capability)) :=
    match: exp_var "reg" in regname with
    | R0 => stm_read_register reg0
    | R1 => stm_read_register reg1
    | R2 => stm_read_register reg2
    | R3 => stm_read_register reg3
    end.

  Definition fun_read_reg_cap : Stm ["reg" ∶ ty_enum regname ] (ty_record capability) :=
    let: "wc" := call read_reg (exp_var "reg") in
    stm_match_sum (exp_var "wc")
      "w" (fail "Err [read_reg_cap]: expect register to hold a capability")
      "c" (stm_exp (exp_var "c")).

  Definition fun_write_reg : Stm ["reg" ∶ ty_enum regname,
                                  "wc"  ∶ ty_sum ty_int (ty_record capability)
                                 ] ty_unit :=
    match: exp_var "reg" in regname with
    | R0 => stm_write_register reg0 (exp_var "wc")
    | R1 => stm_write_register reg1 (exp_var "wc")
    | R2 => stm_write_register reg2 (exp_var "wc")
    | R3 => stm_write_register reg3 (exp_var "wc")
    end ;; stm_lit ty_unit tt.

  Definition fun_update_pc : Stm ctx_nil ty_unit :=
    let: "pc" := stm_read_register pc in
    stm_match_sum (exp_var "pc")
      "w" (fail "PC is not a capability")
      "c" (stm_match_record capability (exp_var "c")
             (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
                "cap_permission" "p") "cap_begin" "b") "cap_end" "e") "cap_cursor" "a")
             (stm_write_register pc
                (exp_inr
                   (exp_record capability
                      [ exp_var "p",
                        exp_var "b",
                        exp_var "e",
                        exp_var "a" + lit_int 1
                      ]%arg)) ;;
              stm_lit ty_unit tt)).

  Definition fun_read_allowed : Stm ["p" ∶ ty_enum permission ] ty_bool :=
    stm_match_enum permission
      (exp_var "p")
      (fun p : Permission =>
         stm_lit ty_bool
                 match p with
                 | R | RX | RW | RWX => true
                 | _                 => false
                 end).

  Definition fun_write_allowed : Stm ["p" ∶ ty_enum permission ] ty_bool :=
    stm_match_enum permission
      (exp_var "p")
      (fun p : Permission =>
         stm_lit ty_bool
                 match p with
                 | RW | RWX => true
                 | _        => false
                 end).

  Definition fun_exec_allowed : Stm ["p" ∶ ty_enum permission ] ty_bool :=
    stm_match_enum permission
      (exp_var "p")
      (fun p : Permission =>
         stm_lit ty_bool
                 match p with
                 | E | RX | RWX => true
                 | _            => false
                 end).

  Definition fun_sub_perm : Stm ["p1"  ∶ ty_enum permission,
                                 "p2"  ∶ ty_enum permission
                                ] ty_bool :=
    stm_match_enum permission
      (exp_var "p1")
      (fun p1 : Permission =>
         match p1 with
         | O   => stm_lit ty_bool true
         | E   => call exec_allowed (exp_var "p2")
         | R   => call read_allowed (exp_var "p2")
         | RX  => let: "r" := call read_allowed (exp_var "p2") in
                  let: "x" := call exec_allowed (exp_var "p2") in
                  stm_exp (exp_var "r" && exp_var "x")
         | RW  => let: "r" := call read_allowed (exp_var "p2") in
                  let: "w" := call write_allowed (exp_var "p2") in
                  stm_exp (exp_var "r" && exp_var "w")
         | RWX => let: "r" := call read_allowed (exp_var "p2") in
                  let: "w" := call write_allowed (exp_var "p2") in
                  let: "x" := call exec_allowed (exp_var "p2") in
                  stm_exp (exp_var "r" && exp_var "w" && exp_var "x")
         end).

  Definition fun_within_bounds : Stm ["c" ∶ ty_record capability ] ty_bool :=
    stm_match_record capability (exp_var "c")
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
      "cap_permission" "p")
      "cap_begin" "b")
      "cap_end" "e")
      "cap_cursor" "a")
      (let: "u" := call upper_bound (exp_var "a") (exp_var "e") in
       stm_exp (exp_var "u" && (exp_var "b" <= exp_var "a"))).

  Definition fun_exec_store : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_unit :=
    let: "c"  := call read_reg_cap (exp_var "lv") in
    let: "wa" := call write_allowed (exp_projrec (exp_var "c") "cap_permission") in
    let: "wb" := call within_bounds (exp_var "c") in
    stm_assert
      (exp_var "wa" && exp_var "wb")
      (exp_lit _ ty_string "Err: [exec_store] assert failed") ;;
    let: "wc2" := call read_reg (exp_var "hv") in
    stm_match_sum (exp_var "wc2")
      "w"  (call write_mem (exp_projrec (exp_var "c") "cap_cursor") (exp_var "w"))
      "c2" (fail "Err: [exec_store] Can't write caps to mem") ;;
    call update_pc.

  Program Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f in (Fun c t) return (Stm c t) with
    | read_reg      => fun_read_reg
    | read_reg_cap  => fun_read_reg_cap
    | write_reg     => fun_write_reg
    | update_pc     => fun_update_pc
    | read_mem      => _
    | write_mem     => _
    | read_allowed  => fun_read_allowed
    | write_allowed => fun_write_allowed
    | exec_allowed  => fun_exec_allowed
    | sub_perm      => fun_sub_perm
    | upper_bound   => _
    | within_bounds => fun_within_bounds
    | exec_store    => fun_exec_store
    end.
  Admit Obligations of Pi.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  Definition Memory : Set := Empty_set.
  Definition read_memory (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) : Lit ty_int :=
    match addr with end.
  Definition write_memory (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Lit ty_int) : Memory :=
    match addr with end.

End CapProgramKit.

Module CapPrograms :=
  Programs CapTypeKit CapTermKit CapProgramKit.
Import CapPrograms.
Import CapProgramKit.
