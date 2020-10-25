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
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Syntax
     Symbolic.Mutator
     Symbolic.Outcome.

From MicroSail Require Environment.
From MicroSail Require Iris.Model.
From MicroSail Require Sep.Logic.
From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.bi Require interface big_op.
From iris.proofmode Require tactics.
From stdpp Require namespaces.

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
| jr       (lv : LV)
| j        (offset : Z)
| bnez     (lv : LV) (immediate : Z)
| mv       (lv : LV) (hv : HV)
| ld       (lv : LV) (hv : HV) (immediate : Z)
| sd       (hv : HV) (lv : LV) (immediate : Z)
| addi     (lv : LV) (hv : HV) (immediate : Z)
| add      (lv1 : LV) (lv2 : LV) (lv3 : LV)
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
| ret.

Inductive InstructionConstructor : Set :=
| kjr
| kj
| kbnez
| kmv
| kld
| ksd
| kaddi
| kadd
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
| kret.

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

Section Finite.

  Import stdpp.finite.
  Import ListNotations.

  Global Program Instance Permission_finite : Finite Permission :=
    {| enum := [O;R;RW] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance RegName_finite : Finite RegName :=
    {| enum := [R0;R1;R2;R3] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance InstructionConstructor_finite :
    Finite InstructionConstructor :=
    {| enum := [kjr;kj;kbnez;kmv;kld;ksd;kaddi;kadd;kret] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

End Finite.

Module MinCapsTypeKit <: TypeKit.

  Import stdpp.finite.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (e : 𝑬) : Set :=
    match e with
    | permission => Permission
    | regname    => RegName
    end.
  Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).
  Instance 𝑬𝑲_finite (E : 𝑬) : Finite (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).

  (** UNIONS **)
  Definition 𝑼        := Unions.
  Definition 𝑼_eq_dec := Unions_eqdec.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    | instruction => Instruction
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.
  Instance 𝑼𝑲_eq_dec U : EqDec (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).
  Instance 𝑼𝑲_finite U : Finite (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).

  (** RECORDS **)
  Definition 𝑹        := Records.
  Definition 𝑹_eq_dec := Records_eqdec.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    | capability => Capability
    end.
  Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
    ltac:(destruct R; auto with typeclass_instances).

  (* VARIABLES *)
  Definition 𝑿        := string.
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
      | kjr       => ty_lv
      | kj        => ty_int
      | kbnez     => ty_prod ty_lv ty_int
      | kmv       => ty_prod ty_lv ty_hv
      | kld       => ty_tuple [ty_lv, ty_hv, ty_int]
      | ksd       => ty_tuple [ty_hv, ty_lv, ty_int]
      | kaddi     => ty_tuple [ty_lv, ty_hv, ty_int]
      | kadd      => ty_tuple [ty_lv, ty_lv, ty_lv]
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
      | kret      => ty_unit
      end
    end.

  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | existT kjr       lv                 => jr lv
      | existT kj        offset             => j offset
      | existT kbnez     (lv , immediate)   => bnez lv immediate
      | existT kmv       (lv , hv)          => mv lv hv
      | existT kld       (tt , lv , hv , immediate) => ld lv hv immediate
      | existT ksd       (tt , hv , lv , immediate) => sd hv lv immediate
      | existT kaddi     (tt , lv , hv , immediate) => addi lv hv immediate
      | existT kadd      (tt , lv1 , lv2 , lv3)     => add lv1 lv2 lv3
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
      | existT kret      tt                 => ret
      end
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    | instruction => fun Kv =>
      match Kv with
      | jr  lv             => existT kjr   lv
      | j offset           => existT kj    offset
      | bnez lv immediate  => existT kbnez (lv , immediate)
      | mv lv hv           => existT kmv   (lv , hv)
      | ld lv hv immediate => existT kld   (tt , lv , hv , immediate)
      | sd hv lv immediate => existT ksd   (tt , hv , lv , immediate)
      | addi lv hv immediate => existT kaddi (tt , lv , hv , immediate)
      | add lv1 lv2 lv3      => existT kadd (tt , lv1 , lv2 , lv3)
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
      | ret                => existT kret  tt
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
  (* Proof. intros []; now apply Forall_forall. Qed. *)
  Admitted.

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | read_reg       : Fun ["reg" ∶ ty_enum regname ] ty_word
  | read_reg_cap   : Fun ["reg" ∶ ty_enum regname ] ty_cap
  | read_reg_num   : Fun ["reg" ∶ ty_enum regname ] ty_int
  | write_reg      : Fun ["reg" ∶ ty_enum regname,
                          "w"  ∶ ty_word
                         ] ty_unit
  | update_pc      : Fun ctx_nil ty_unit
  | add_pc         : Fun ["offset" ∶ ty_int] ty_unit
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
  | exec_jr        : Fun ["lv" ∶ ty_lv] ty_bool
  | exec_j         : Fun ["offset" ∶ ty_int] ty_bool
  | exec_bnez      : Fun ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_mv        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_bool
  | exec_ld        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_sd        : Fun ["hv" ∶ ty_hv, "lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_addi      : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_add       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_ret       : Fun ε ty_bool
  | exec_instr     : Fun ["i" ∶ ty_instr] ty_bool
  | exec           : Fun ε ty_bool
  | loop           : Fun ε ty_unit
  .

  Inductive FunGhost : Ctx (𝑿 * Ty) -> Set :=
  | open_ptsreg : FunGhost ["reg" ∶ ty_enum regname]
  | close_ptsreg (R : RegName) : FunGhost ctx_nil
  .

  Inductive FunX : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_int
  (* write memory *)
  | wM    : FunX ["address" ∶ ty_int, "mem_value" ∶ ty_int] ty_unit
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

  Notation "'callghost' f" :=
    (stm_call_external (ghost f) env_nil)
    (at level 10, f at next level) : stm_scope.

  Definition fun_read_reg : Stm ["reg" ∶ ty_enum regname ] ty_word :=
    stm_call_external (ghost open_ptsreg) [exp_var "reg"]%arg ;;
    match: exp_var "reg" in regname with
    | R0 => let: "x" := stm_read_register reg0 in callghost (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_read_register reg1 in callghost (close_ptsreg R1) ;; stm_exp x
    | R2 => let: "x" := stm_read_register reg2 in callghost (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_read_register reg3 in callghost (close_ptsreg R3) ;; stm_exp x
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
    stm_call_external (ghost open_ptsreg) [exp_var "reg"]%arg ;;
    match: exp_var "reg" in regname with
    | R0 => let: "x" := stm_write_register reg0 (exp_var "w") in callghost (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_write_register reg1 (exp_var "w") in callghost (close_ptsreg R1) ;; stm_exp x
    | R2 => let: "x" := stm_write_register reg2 (exp_var "w") in callghost (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_write_register reg3 (exp_var "w") in callghost (close_ptsreg R3) ;; stm_exp x
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

  Definition fun_add_pc : Stm ["offset" ∶ ty_int ] ty_unit :=
    let: "c" := stm_read_register pc in
    stm_write_register pc
      (exp_record capability
                      [ ((exp_var "c")․"cap_permission"),
                        ((exp_var "c")․"cap_begin"),
                        ((exp_var "c")․"cap_end"),
                        ((exp_var "c")․"cap_cursor") + (exp_var "offset")
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

    Definition fun_exec_sd : Stm [hv ∶ ty_hv, lv ∶ ty_lv, "immediate" ∶ ty_int ] ty_bool :=
      let: "base_cap" ∶ cap  := call read_reg_cap lv in
      let: "c" ∶ cap  := stm_exp (exp_record capability
                      [ ((exp_var "base_cap")․"cap_permission"),
                        ((exp_var "base_cap")․"cap_begin"),
                        ((exp_var "base_cap")․"cap_end"),
                        ((exp_var "base_cap")․"cap_cursor") + (exp_var "immediate")
                      ]%exp%arg) in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_sd] no write permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_sd] out of bounds") ;;
      let: w ∶ int := call read_reg_num hv in
      call write_mem c․cursor w ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_ld : Stm [lv ∶ ty_lv, hv ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      let: "base_cap" ∶ cap  := call read_reg_cap hv in
      let: "c" ∶ cap  := stm_exp (exp_record capability
                      [ ((exp_var "base_cap")․"cap_permission"),
                        ((exp_var "base_cap")․"cap_begin"),
                        ((exp_var "base_cap")․"cap_end"),
                        ((exp_var "base_cap")․"cap_cursor") + (exp_var "immediate")
                      ]%exp%arg) in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_ld] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_ld] out of bounds") ;;
      let: n ∶ ty_memval := call read_mem c․cursor in
      call write_reg lv (exp_inl (exp_var n)) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_addi : Stm [lv ∶ ty_lv, hv ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      let: "v" ∶ int := call read_reg_num hv in
      let: "res" ∶ int := stm_exp (exp_var "v" + exp_var "immediate") in
      call write_reg lv (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_add : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv ] ty_bool :=
      let: "v1" ∶ int := call read_reg_num (exp_var "lv2") in
      let: "v2" ∶ int := call read_reg_num (exp_var "lv3") in
      let: "res" ∶ int := stm_exp (exp_var "v1" + exp_var "v2") in
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
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

    Definition fun_exec_ret : Stm ε ty_bool :=
      stm_exp (exp_lit _ ty_bool false).

    Definition fun_exec_mv : Stm [lv ∶ ty_lv, hv ∶ ty_hv] ty_bool :=
      let: w ∶ word := call read_reg (exp_var hv) in
      call write_reg lv (exp_var w) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_jr : Stm [lv ∶ ty_lv] ty_bool :=
      let: "c" ∶ ty_cap := call read_reg_cap lv in
      stm_write_register pc c ;;
      stm_lit ty_bool true.

    Definition fun_exec_j : Stm [offset ∶ ty_int ] ty_bool :=
      call update_pc ;;
      call add_pc (exp_var offset) ;;
      stm_lit ty_bool true.

    Definition fun_exec_bnez : Stm [lv ∶ ty_lv, immediate ∶ ty_int ] ty_bool :=
      let: "c" ∶ ty_int := call read_reg_num (exp_var lv) in
      stm_if (exp_binop binop_eq c (exp_lit _ ty_int 0))
             (call update_pc ;; stm_lit ty_bool true)
             (call add_pc (exp_var immediate) ;; stm_lit ty_bool true).

    Definition fun_exec_instr : Stm [i ∶ ty_instr] ty_bool :=
      stm_match_union_alt
        instruction (exp_var i)
        (fun K =>
           match K with
           | kjr   => MkAlt (pat_var lv) (call exec_jr lv)
           | kj    => MkAlt (pat_var offset) (call exec_j offset)
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
           | kret  => MkAlt pat_unit (call exec_ret)
           end).

    Definition fun_read_mem : Stm ["a"   ∶ ty_addr ] ty_memval :=
      callex rM a.

    Definition fun_write_mem : Stm ["a"   ∶ ty_addr, "v" ∶ ty_memval ] ty_unit :=
      callex wM a (exp_var "v").

    Definition fun_exec : Stm ε ty_bool :=
      let: "c" := stm_read_register pc in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (exp_lit _ ty_string "Err: [exec_ld] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (exp_lit _ ty_string "Err: [exec_ld] out of bounds") ;;
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
    | add_pc         => fun_add_pc
    | read_mem       => fun_read_mem
    | write_mem      => fun_write_mem
    | read_allowed   => fun_read_allowed
    | write_allowed  => fun_write_allowed
    (* | sub_perm       => fun_sub_perm *)
    | upper_bound    => fun_upper_bound
    | within_bounds  => fun_within_bounds
    | exec_jr        => fun_exec_jr
    | exec_j         => fun_exec_j
    | exec_bnez      => fun_exec_bnez
    | exec_mv        => fun_exec_mv
    | exec_ld        => fun_exec_ld
    | exec_sd        => fun_exec_sd
    | exec_addi      => fun_exec_addi
    | exec_add       => fun_exec_add
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
  Definition Memory := Addr -> Z.

  Definition fun_rM (μ : Memory) (addr : Lit ty_int) : Lit ty_int :=
    μ addr.

  Definition fun_wM (μ : Memory) (addr val : Lit ty_int) : Memory :=
    fun addr' => if Z.eqb addr addr' then val else μ addr'.

  Definition fun_dI (code : Lit ty_int) : string + Lit ty_instr :=
    (* TODO: actually decode to non-trivial instructions? *)
    inr ret.

  Inductive CallEx : forall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
  | callex_rM {addr : Z} {γ : RegStore} {μ : Memory} :
      CallEx rM (env_snoc env_nil (_ , ty_int) addr)
             (inr (fun_rM μ addr))
             γ γ μ μ
  | callex_wM {addr val : Z} {γ : RegStore} {μ : Memory} :
      CallEx wM (env_snoc (env_snoc env_nil (_ , ty_int) addr) (_ , ty_int) val)
             (inr tt)
             γ γ μ (fun_wM μ addr val)
  | callex_dI {code : Z} {γ : RegStore} {μ : Memory} :
      CallEx dI (env_snoc env_nil (_ , ty_int) code)
             (fun_dI code)
             γ γ μ μ
  | callex_ghost {Δ} {fg : FunGhost Δ} {δ : NamedEnv Lit Δ} {γ : RegStore} {μ : Memory} :
      CallEx (ghost fg) δ (inr tt) γ γ μ μ
  .

  Definition ExternalCall := @CallEx.

  Lemma ExternalProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ExternalCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat eexists; constructor.
  Qed.

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
           (* domi: strange that I have to manually specify Σ here *)
           (asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_word]) (fun reg w result => result = w) ✱
                     term_var "reg" ↦r term_var "w")
      |}.

    Definition sep_contract_read_reg_cap : SepContract ["reg" ∶ ty_enum regname ] ty_cap :=
      {| sep_contract_logic_variables := ["reg" ∶ ty_enum regname, "w" ∶ ty_word];
         sep_contract_localstore      := [term_var "reg"]%arg;
         sep_contract_precondition    := term_var "reg" ↦r term_var "w";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           (asn_exist "c" ty_cap (
                        asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_cap, "c" ∶ ty_cap]) (fun reg w result c => result = c) ✱
                        asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_cap, "c" ∶ ty_cap]) (fun reg w result c => w = inr c)
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
                        asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_int, "n" ∶ ty_int]) (fun reg w result n => result = n) ✱
                        asn_prop (Σ := ["reg" ∶ ty_enum regname, "w" ∶ ty_word, "result" ∶ ty_int, "n" ∶ ty_int]) (fun reg w result n => w = inl n)
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
           asn_prop (Σ := ["a" ∶ ty_addr, "n" ∶ ty_int, "result" ∶ ty_int]) (fun _ n res => res = n);
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
        | update_pc    => Some sep_contract_update_pc
        | read_mem     => Some sep_contract_read_mem
        | write_mem    => Some sep_contract_write_mem
        | _            => None
        end.

    Definition sep_contract_open_ptsreg : SepContract ["reg" ∶ ty_enum regname] ty_unit :=
      {| sep_contract_logic_variables := [ "r" ∶ ty_enum regname, "w" ∶ ty_word];
         sep_contract_localstore      := [term_var "r"]%arg;
         sep_contract_precondition    := term_var "r" ↦r term_var "w";
         sep_contract_result          := "_";
         sep_contract_postcondition   :=
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
       subst; try congruence; try lia;
       auto
      ).

  Lemma valid_contract_read_reg : ValidContractDynMutEvar sep_contract_read_reg fun_read_reg.
  Proof. compute; solve. Qed.

  Lemma valid_contract_read_reg_cap : ValidContractDynMutEvar sep_contract_read_reg_cap fun_read_reg_cap.
  Proof.
    split;
      [ compute; auto
      | exists (term_var "result"); compute; firstorder congruence
      ].
  Qed.

  Lemma valid_contract_read_reg_num : ValidContractDynMutEvar sep_contract_read_reg_num fun_read_reg_num.
  Proof.
    split;
      [ exists (term_var "result"); compute; firstorder congruence
      | compute; auto
      ].
  Qed.

  Lemma valid_contract_write_reg : ValidContractDynMutEvar sep_contract_write_reg fun_write_reg.
  Proof. apply dynmutevarreflect_sound; now compute. Qed.

  Lemma valid_contract_update_pc : ValidContractDynMutEvar sep_contract_update_pc fun_update_pc.
  Proof.
    exists (TM.term_record
              capability
              [TM.term_projrec (TM.term_var "opc") "cap_permission",
               TM.term_projrec (TM.term_var "opc") "cap_begin",
               TM.term_projrec (TM.term_var "opc") "cap_end",
               TM.term_binop
                 binop_plus
                 (TM.term_projrec (TM.term_var "opc") "cap_cursor")
                 (TM.term_lit TY.ty_int 1)]%arg).
    compute; solve.
  Qed.

End MinCapsContracts.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsModel.
  Import MinCapsContracts.
  Import MicroSail.Iris.Model.

  Module MinCapsIrisHeapKit <: IrisHeapKit MinCapsTypeKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.

    Section WithIrisNotations.

    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.tactics.

    Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z Z Σ.
    Definition memG : gFunctors -> Set := fun Σ => gh.gen_heapG Z Z Σ.
    Definition memΣ : gFunctors := gh.gen_heapΣ Z Z.

    Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Z) (V := Z).

    Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_ctx (hG := hG) memmap ∗
                                ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Definition liveAddrs : list Addr := [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%Z.

    Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        ([∗ list] a ∈ liveAddrs, mapsto (hG := hG) a 1 (μ a)) %I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
        ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
    Proof.
      iIntros (Σ μ gHP).

      iMod (gen_heap_init (gen_heapPreG0 := gHP) (L := Addr) (V := Z) empty) as (gH) "inv".
      iMod (gen_heap_alloc _ 9%Z (μ 9) _ with "inv") as "(inv & res9 & _)".
      iMod (gen_heap_alloc _ 8%Z (μ 8) _ with "inv") as "(inv & res8 & _)".
      iMod (gen_heap_alloc _ 7%Z (μ 7) _ with "inv") as "(inv & res7 & _)".
      iMod (gen_heap_alloc _ 6%Z (μ 6) _ with "inv") as "(inv & res6 & _)".
      iMod (gen_heap_alloc _ 5%Z (μ 5) _ with "inv") as "(inv & res5 & _)".
      iMod (gen_heap_alloc _ 4%Z (μ 4) _ with "inv") as "(inv & res4 & _)".
      iMod (gen_heap_alloc _ 3%Z (μ 3) _ with "inv") as "(inv & res3 & _)".
      iMod (gen_heap_alloc _ 2%Z (μ 2) _ with "inv") as "(inv & res2 & _)".
      iMod (gen_heap_alloc _ 1%Z (μ 1) _ with "inv") as "(inv & res1 & _)".
      iMod (gen_heap_alloc _ 0%Z (μ 0) _ with "inv") as "(inv & res0 & _)".
      iModIntro.

      pose (refmap := list_to_map (map (fun a => (a, μ a)) liveAddrs) : gmap Z Z).
      iExists (gH).
      cbn.
      iFrame.
      iExists refmap.
      iFrame.
      iPureIntro.
      repeat rewrite map_Forall_insert; trivial.
      repeat split; trivial.
      by apply map_Forall_empty.

      Unshelve.
      all: try rewrite !lookup_insert_ne; try apply lookup_empty; lia.
    Qed.

    Import MinCapsAssertions.
    (* huh: I'm supposed to instantiate the class, right? *)

    Definition lpred_inst {Σ} (p : Predicate) (ts : Env Lit (MinCapsAssertionKit.𝑷_Ty p)) (mG : memG Σ) : iProp Σ :=
      (match p return Env Lit (MinCapsAssertionKit.𝑷_Ty p) -> iProp Σ with
      | ptsreg => fun _ => False%I
      | ptsto => fun ts' => mapsto (hG := mG) (env_head ts') 1 (env_head (env_tail ts'))%Z
      | safe => fun _ => False%I
      end) ts.

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

End MinCapsModel.
