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
     Syntax
     Symbolic.Mutator
     Symbolic.Outcome.

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
(* | fail *)
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
(* | kfail *)
| khalt.

Section Records.
  Local Set Primitive Projections.

  Definition Addr : Set := Z.

  Record Capability : Set :=
    MkCap
      { cap_permission : Permission;
        cap_begin      : Addr;
        cap_end        : Addr + unit;
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
Definition ty_rv : Ty := ty_sum (ty_enum regname) ty_int.
Definition ty_cap : Ty := ty_record capability.
Definition ty_word : Ty := ty_sum ty_int ty_cap.
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
      (* | kfail     => ty_unit *)
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
      (* | existT kfail     tt                 => fail *)
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
      (* | fail              => existT kfail     tt *)
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
  | read_reg_cap   : Fun ["reg" ∶ ty_enum regname ] ty_cap
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
  (* | sub_perm       : Fun ["p1"  ∶ ty_perm, *)
  (*                         "p2"  ∶ ty_perm *)
  (*                        ] ty_bool *)
  | upper_bound    : Fun ["a"   ∶ ty_addr,
                          "e"   ∶ ty_option ty_addr
                         ] ty_bool
  | within_bounds  : Fun ["c"   ∶ ty_cap ] ty_bool
  | compute_rv     : Fun ["rv" ∶ ty_rv] ty_word
  | compute_rv_num : Fun ["rv" ∶ ty_rv] ty_int
  | exec_jmp       : Fun ["lv" ∶ ty_lv] ty_bool
  | exec_jnz       : Fun ["lv" ∶ ty_lv, "rv" ∶ ty_rv] ty_bool
  | exec_move      : Fun ["lv" ∶ ty_lv, "rv" ∶ ty_rv ] ty_bool
  | exec_load      : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_bool
  | exec_store     : Fun ["lv" ∶ ty_lv, "rv" ∶ ty_rv ] ty_bool
  | exec_halt      : Fun ε ty_bool
  | exec_instr     : Fun ["i" ∶ ty_instr] ty_bool
  | exec           : Fun ε ty_bool
  | loop           : Fun ε ty_unit
  .

  Inductive FunGhost : Set :=
  | open_ptsreg
  | close_ptsreg0
  | close_ptsreg1
  | close_ptsreg2
  | close_ptsreg3
  .

  Inductive FunX : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_int
  (* write memory *)
  | wM    : FunX ["address" ∶ ty_int, "mem_value" ∶ ty_int] ty_unit
  | dI    : FunX ["code" ∶ ty_int] ty_instr
  | ghost (f : FunGhost) : FunX ctx_nil ty_unit
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : Ctx (𝑿 * Ty) -> Ty -> Set := FunX.

  Inductive Reg : Ty -> Set :=
    | pc   : Reg ty_cap
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

  Notation "'callghost' f" :=
    (stm_call_external (ghost f) env_nil)
    (at level 10, f global) : stm_scope.

  Definition fun_read_reg : Stm ["reg" ∶ ty_enum regname ] ty_word :=
    callghost open_ptsreg ;;
    match: exp_var "reg" in regname with
    | R0 => let: "x" := stm_read_register reg0 in callghost close_ptsreg0 ;; stm_exp x
    | R1 => let: "x" := stm_read_register reg1 in callghost close_ptsreg0 ;; stm_exp x
    | R2 => let: "x" := stm_read_register reg2 in callghost close_ptsreg0 ;; stm_exp x
    | R3 => let: "x" := stm_read_register reg3 in callghost close_ptsreg0 ;; stm_exp x
    end.

  Definition fun_read_reg_cap : Stm ["reg" ∶ ty_enum regname ] ty_cap :=
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

  Definition fun_write_reg : Stm ["reg" ∶ ty_enum regname,
                                  "w" ∶ ty_word
                                 ] ty_unit :=
    match: exp_var "reg" in regname with
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
       stm_exp (exp_var "u" && (exp_var "b" <= exp_var "a"))).

  Definition fun_upper_bound : Stm ["a"   ∶ ty_addr, "e"   ∶ ty_option ty_addr] ty_bool :=
    match: e with
    | inl e => stm_exp (a <= e)
    | inr "_" => stm_exp (lit_bool true)
    end.
  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty_cap.
    Let bool : Ty := ty_bool.
    Let int : Ty := ty_int.
    Let word : Ty := ty_word.

    Definition fun_exec_store : Stm [lv ∶ ty_lv, rv ∶ ty_rv] ty_bool :=
      let: c ∶ cap  := call read_reg_cap lv in
      let: p ∶ bool := call write_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_store] no write permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_store] out of bounds") ;;
      let: w ∶ int := call compute_rv_num rv in
      call write_mem c․cursor w ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_load : Stm [lv ∶ ty_lv, hv ∶ ty_hv] ty_bool :=
      let: c ∶ cap  := call read_reg_cap hv in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_load] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_load] out of bounds") ;;
      let: n ∶ ty_memval := call read_mem c․cursor in
      call write_reg lv (exp_inl (exp_var n)) ;;
      call update_pc ;;
      stm_lit ty_bool true.

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

    Definition fun_exec_halt : Stm ε ty_bool :=
      stm_exp (exp_lit _ ty_bool false).

    Definition fun_exec_move : Stm [lv ∶ ty_lv, rv ∶ ty_rv] ty_bool :=
      let: w ∶ word := call compute_rv (exp_var rv) in
      call write_reg lv (exp_var w) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_jmp : Stm [lv ∶ ty_lv] ty_bool :=
      let: "c" ∶ ty_cap := call read_reg_cap lv in
      stm_write_register pc c ;;
      stm_lit ty_bool true.

    Definition fun_exec_jnz : Stm [lv ∶ ty_lv, rv ∶ ty_rv ] ty_bool :=
      let: "c" ∶ ty_int := call compute_rv_num (exp_var rv) in
      stm_if (exp_binop binop_eq c (exp_lit _ ty_int 0))
             (call update_pc ;; stm_lit ty_bool true)
             (call exec_jmp lv).

    Definition fun_exec_instr : Stm [i ∶ ty_instr] ty_bool :=
      stm_match_union instruction (exp_var i)
                      (fun K => match K with
                            | kjmp => alt _ (pat_var lv) (call exec_jmp lv)
                            | kjnz => alt _ (pat_pair lv rv) (call exec_jnz lv rv)
                            | kmove => alt _ (pat_pair lv rv) (call exec_move lv rv)
                            | kload => alt _ (pat_pair lv hv) (call exec_load (exp_var lv) (exp_var hv))
                            | kstore => alt _ (pat_pair lv rv) (call exec_store (exp_var lv) (exp_var rv))
                            | khalt => alt _ pat_unit (call exec_halt)
                            end).

    Definition fun_read_mem : Stm ["a"   ∶ ty_addr ] ty_memval :=
      callex rM a.

    Definition fun_write_mem : Stm ["a"   ∶ ty_addr, "v" ∶ ty_memval ] ty_unit :=
      callex wM a (exp_var "v").

    Definition fun_exec : Stm ε ty_bool :=
      let: "c" := stm_read_register pc in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_load] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_load] out of bounds") ;;
      let: n ∶ ty_memval := call read_mem c․cursor in
      let: i ∶ ty_instr := callex dI (exp_var n) in
      call exec_instr i.

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
    | update_pc      => fun_update_pc
    | read_mem       => fun_read_mem
    | write_mem      => fun_write_mem
    | read_allowed   => fun_read_allowed
    | write_allowed  => fun_write_allowed
    (* | sub_perm       => fun_sub_perm *)
    | upper_bound    => fun_upper_bound
    | within_bounds  => fun_within_bounds
    | exec_jmp       => fun_exec_jmp
    | exec_jnz       => fun_exec_jnz
    | exec_move      => fun_exec_move
    | exec_load      => fun_exec_load
    | exec_store     => fun_exec_store
    | exec_halt      => fun_exec_halt
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
  Definition Memory := Z -> option Z.

  Definition fun_rM (μ : Memory) (addr : Lit ty_int) : string + Lit ty_int :=
    match μ addr with
    | Some v => inr v
    | None   => inl "Err [fun_rM]: invalid address"
    end.

  Definition fun_wM (μ : Memory) (addr val : Lit ty_int) : Memory :=
    fun addr' => if Z.eqb addr addr' then Some val else μ addr'.

  Definition fun_dI (code : Lit ty_int) : string + Lit ty_instr :=
    (* TODO: actually decode to non-trivial instructions? *)
    inr halt.

  Inductive CallEx : forall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
  | callex_rM {addr : Z} {γ : RegStore} {μ : Memory} :
      CallEx rM (env_snoc env_nil (_ , ty_int) addr)
             (fun_rM μ addr)
             γ γ μ μ
  | callex_wM {addr val : Z} {γ : RegStore} {μ : Memory} :
      CallEx wM (env_snoc (env_snoc env_nil (_ , ty_int) addr) (_ , ty_int) val)
             (inr tt)
             γ γ μ (fun_wM μ addr val)
  | callex_dI {code : Z} {γ : RegStore} {μ : Memory} :
      CallEx dI (env_snoc env_nil (_ , ty_int) code)
             (fun_dI code)
             γ γ μ μ
  | callex_ghost {fg : FunGhost} {γ : RegStore} {μ : Memory} :
      CallEx (ghost fg) env_nil (inr tt) γ γ μ μ
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

Inductive Predicate : Set :=
  ptsreg
| ptsto
| safe.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module MinCapsContracts.
  Module MinCapsAssertionKit <:
    (AssertionKit MinCapsTypeKit MinCapsTermKit MinCapsProgramKit).
    Module PM := Programs MinCapsTypeKit MinCapsTermKit MinCapsProgramKit.

    Definition 𝑷 := Predicate.
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | ptsreg => [ty_enum regname, ty_word]
      | ptsto => [ty_addr, ty_int]
      | safe => [ty_word]
      end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.
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

    Local Notation "r '↦r' t" := (asn_chunk (chunk_pred ptsreg (env_nil ► ty_enum regname ↦ r ► ty_word ↦ t))) (at level 100).
    Local Notation "a '↦m' t" := (asn_chunk (chunk_pred ptsto (env_nil ► ty_addr ↦ a ► ty_int ↦ t))) (at level 100).
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
      bool exec_store(lv : lv, hv : memval)

      @pre machInv;
      @post machInv;
      bool exec_load(lv : lv, hv : memval)

      @pre machInv;
      @post machInv;
      bool exec_jmp(lv : lv)

      @pre machInv;
      @post machInv;
      bool exec_jnz(lv : lv, rv : ty_rv)

      @pre machInv;
      @post machInv;
      bool exec_move(lv : lv, rv : ty_rv)

      @pre machInv;
      @post machInv;
      bool exec_halt

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


    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
          | read_reg =>
             sep_contract_result
             ["reg" ∶ ty_enum regname, "w" ∶ ty_word]
             [term_var "reg"]%arg
             "result"
             (term_var "reg" ↦r term_var "w")
             (* domi: strange that I have to manually specify Σ here *)
             (asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_word]) (fun reg w result => result = w) ✱
              term_var "reg" ↦r term_var "w")
          | read_reg_cap =>
             sep_contract_result
             ["reg" ∶ ty_enum regname, "w" ∶ ty_word]
             [term_var "reg"]%arg
             "result"
             (term_var "reg" ↦r term_var "w")
             (asn_exist "c" ty_cap (
                          asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_cap, "c" ∶ ty_cap]) (fun reg w result c => result = c) ✱
                          asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_cap, "c" ∶ ty_cap]) (fun reg w result c => w = inr c)
                        ) ✱
              term_var "reg" ↦r term_var "w")
          | read_reg_num =>
             sep_contract_result
             ["reg" ∶ ty_enum regname, "w" ∶ ty_word]
             [term_var "reg"]%arg
             "result"
             (term_var "reg" ↦r term_var "w")
             (asn_exist "n" ty_int (
                          asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_int, "n" ∶ ty_int]) (fun reg w result n => result = n) ✱
                          asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_int, "n" ∶ ty_int]) (fun reg w result n => w = inl n)
                        ) ✱
              term_var "reg" ↦r term_var "w")
          | write_reg =>
             sep_contract_result
               ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "wo" ∶ ty_word]
               [term_var "reg", term_var "w"]%arg
               "result"
               (term_var "reg" ↦r term_var "wo")
               (term_var "reg" ↦r term_var "w")
          | update_pc =>
             sep_contract_result
               ["opc" ∶ ty_cap]
               env_nil%arg
               "result"
               (pc ↦ term_var "opc")
               (asn_exist "npc" ty_cap (pc ↦ term_var "npc"))
          | read_mem =>
             sep_contract_result
               ["a" ∶ ty_addr, "n" ∶ ty_int]
               [term_var "a"]%arg
               "result"
               (term_var "a" ↦m term_var "n")
               (term_var "a" ↦m term_var "n" ✱
                asn_prop (Σ := ["a" ∶ ty_addr, "n" ∶ ty_int, "result" ∶ ty_int]) (fun _ n res => res = n))
          | write_mem =>
             sep_contract_result
               ["a" ∶ ty_addr, "v" ∶ ty_memval, "ov" ∶ ty_memval]
               [term_var "a", term_var "v"]%arg
               "result"
               (term_var "a" ↦m term_var "ov")
               (term_var "a" ↦m term_var "v")
          | read_allowed =>
             sep_contract_result
               ["p" ∶ ty_perm]
               [term_var "p"]%arg
               "result"
               asn_true
               asn_true
          | write_allowed =>
             sep_contract_result
               ["p" ∶ ty_perm]
               [term_var "p"]%arg
               "result"
               asn_true
               asn_true
          | upper_bound =>
             sep_contract_result
               ["a" ∶ ty_addr, "e" ∶ ty_option ty_addr]
               [term_var "a", term_var "e"]%arg
               "result"
               asn_true
               asn_true
          | within_bounds =>
             sep_contract_result
               ["c" ∶ ty_cap]
               [term_var "c"]%arg
               "result"
               asn_true
               asn_true
          | compute_rv =>
             sep_contract_result
               ["rv" ∶ ty_rv]
               [term_var "rv"]%arg
               "result"
               asn_true
               asn_true
          | compute_rv_num =>
             sep_contract_result
               ["rv" ∶ ty_rv]
               [term_var "rv"]%arg
               "result"
               asn_true
               asn_true
          | exec_jmp =>
             sep_contract_result
               ["lv" ∶ ty_lv]
               [term_var "lv"]%arg
               "result"
               asn_true
               asn_true
          | exec_jnz =>
             sep_contract_result
               ["lv" ∶ ty_lv, "rv" ∶ ty_rv]
               [term_var "lv", term_var "rv"]%arg
               "result"
               asn_true
               asn_true
          | exec_move =>
             sep_contract_result
               ["lv" ∶ ty_lv, "rv" ∶ ty_rv]
               [term_var "lv", term_var "rv"]%arg
               "result"
               asn_true
               asn_true
          | exec_load =>
             sep_contract_result
               ["lv" ∶ ty_lv, "hv" ∶ ty_hv ]
               [term_var "lv", term_var "hv"]%arg
               "result"
               asn_true
               asn_true
          | exec_store =>
             sep_contract_result
               ["lv" ∶ ty_lv, "rv" ∶ ty_rv]
               [term_var "lv", term_var "rv"]%arg
               "result"
               asn_true
               asn_true
          | exec_halt =>
             sep_contract_result
               ε
               env_nil%arg
               "result"
               asn_true
               asn_true
          | exec_instr =>
             sep_contract_result
               ["i" ∶ ty_instr]
               [term_var "i"]%arg
               "result"
               asn_true
               asn_true
          | exec =>
             sep_contract_result
               ε
               env_nil%arg
               "result"
               asn_true
               asn_true
          | loop =>
             sep_contract_result
               ε
               env_nil%arg
               "result"
               asn_true
               asn_true
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | rM =>
          sep_contract_result
            ["address" ∶ ty_int]
            [term_var "address"]%arg
            "result"
            asn_true
            asn_true
          | wM =>
             sep_contract_result
               ["address" ∶ ty_int, "mem_value" ∶ ty_int]
               [term_var "address", term_var "mem_value"]%arg
               "result"
               asn_true
               asn_true
          | dI =>
             sep_contract_result
               ["code" ∶ ty_int]
               [term_var "code"]%arg
               "result"
               asn_true
               asn_true
          | ghost open_ptsreg =>
            sep_contract_result
              [ "r" ∶ ty_enum regname, "w" ∶ ty_word]
              env_nil
              "result"
              (term_var "r" ↦r term_var "w")
              (asn_match_enum regname (term_var "r")
                              (fun k => match k with
                                     | R0 => reg0 ↦ term_var "w"
                                     | R1 => reg1 ↦ term_var "w"
                                     | R2 => reg2 ↦ term_var "w"
                                     | R3 => reg3 ↦ term_var "w"
                                     end))
          | ghost close_ptsreg0 =>
            sep_contract_result
              [ "w" ∶ ty_word]
              env_nil
              "result"
              (reg0 ↦ term_var "w")
              (term_enum regname R0 ↦r term_var "w")
          | ghost close_ptsreg1 =>
            sep_contract_result
              [ "w" ∶ ty_word]
              env_nil
              "result"
              (reg1 ↦ term_var "w")
              (term_enum regname R1 ↦r term_var "w")
          | ghost close_ptsreg2 =>
            sep_contract_result
              [ "w" ∶ ty_word]
              env_nil
              "result"
              (reg2 ↦ term_var "w")
              (term_enum regname R2 ↦r term_var "w")
          | ghost close_ptsreg3 =>
            sep_contract_result
              [ "w" ∶ ty_word]
              env_nil
              "result"
              (reg3 ↦ term_var "w")
              (term_enum regname R3 ↦r term_var "w")
        end.

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
         | H: Env _ ctx_nil |- _ => dependent elimination H
         | H: Env _ (ctx_snoc _ _) |- _ => dependent elimination H
         | H: _ /\ _ |- _ => destruct H
         | H: Empty_set |- _ => destruct H
         | |- _ /\ _ => constructor
         end;
       cbn [List.length];
       subst; try congruence; try omega;
       auto
      ).

  Lemma valid_contract_read_reg_wp : ValidContract (CEnv read_reg) (Pi read_reg).
  Proof.
    solve.
  Qed.
  Hint Resolve valid_contract_read_reg_wp : contracts.


  Lemma valid_contract_read_reg : ValidContractDynMut (CEnv read_reg) (Pi read_reg).
  Proof.
    solve.
    admit.
  Qed.

End MinimalCapsContracts.
