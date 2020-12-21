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
     ZArith.ZArith.
From stdpp Require
     finite.
From Equations Require Import
     Equations.
From MicroSail Require Import
     Syntax.Types.

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
| jalr     (lv1 : LV) (lv2 : LV)
| j        (offset : Z)
| jal      (lv : LV) (offset : Z)
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
| kjalr
| kj
| kjal
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
    {| enum := [kjr;kjalr;kj;kjal;kbnez;kmv;kld;ksd;kaddi;kadd;kret] |}.
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

End MinCapsTypeKit.
