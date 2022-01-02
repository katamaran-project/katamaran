(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From stdpp Require
     finite.
From Equations Require Import
     Equations.
From Katamaran Require Export
     Prelude Tactics.

Module Type EnumTypeKit.
  (* Names of enum type constructors. *)
  Parameter Inline 𝑬 : Set. (* input: \MIE *)
  Declare Instance 𝑬_eq_dec : EqDec 𝑬.
  (* Names of enum data constructors. *)
  Parameter Inline 𝑬𝑲 : 𝑬 -> Set.
  Declare Instance 𝑬𝑲_eq_dec : forall (e : 𝑬), EqDec (𝑬𝑲 e).
  Declare Instance 𝑬𝑲_finite : forall E, finite.Finite (𝑬𝑲 E).
End EnumTypeKit.

Module Type UnionTypeKit.
  (* Names of union type constructors. *)
  Parameter Inline 𝑼   : Set. (* input: \MIU *)
  Declare Instance 𝑼_eq_dec : EqDec 𝑼.
  (* Union types. *)
  Parameter Inline 𝑼𝑻  : 𝑼 -> Set.
  Declare Instance 𝑼𝑻_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑻 u).
  (* Names of union data constructors. *)
  Parameter Inline 𝑼𝑲  : 𝑼 -> Set.
  Declare Instance 𝑼𝑲_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑲 u).
  Declare Instance 𝑼𝑲_finite : forall U, finite.Finite (𝑼𝑲 U).
End UnionTypeKit.

Module Type RecordTypeKit.
  (* Names of record type constructors. *)
  Parameter Inline 𝑹  : Set. (* input: \MIR *)
  Declare Instance 𝑹_eq_dec : EqDec 𝑹.
  (* Record types. *)
  Parameter Inline 𝑹𝑻  : 𝑹 -> Set.
  Declare Instance 𝑹𝑻_eq_dec : forall (r : 𝑹), EqDec (𝑹𝑻 r).
End RecordTypeKit.

Module Type TypeKit :=
  EnumTypeKit <+ UnionTypeKit <+ RecordTypeKit.

Module NoEnums <: EnumTypeKit.
  Definition 𝑬          := Empty_set.
  Definition 𝑬𝑲 (E : 𝑬) := Empty_set.

  Instance 𝑬_eq_dec : EqDec 𝑬 := Empty_set_EqDec.
  Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E)  := Empty_set_EqDec.
  Instance 𝑬𝑲_finite (E : 𝑬) : finite.Finite (𝑬𝑲 E) := finite.Empty_set_finite.
End NoEnums.

Module NoUnions <: UnionTypeKit.
  Definition 𝑼          := Empty_set.
  Definition 𝑼𝑻 (U : 𝑼) := Empty_set.
  Definition 𝑼𝑲 (U : 𝑼) := Empty_set.

  Instance 𝑼_eq_dec : EqDec 𝑼 := Empty_set_EqDec.
  Instance 𝑼𝑻_eq_dec (U : 𝑼) : EqDec (𝑼𝑻 U)  := Empty_set_EqDec.
  Instance 𝑼𝑲_eq_dec (U : 𝑼) : EqDec (𝑼𝑲 U)  := Empty_set_EqDec.
  Instance 𝑼𝑲_finite (U : 𝑼) : finite.Finite (𝑼𝑲 U) := finite.Empty_set_finite.
End NoUnions.

Module NoRecords <: RecordTypeKit.
  Definition 𝑹          := Empty_set.
  Definition 𝑹𝑻 (R : 𝑹) := Empty_set.
  Instance 𝑹_eq_dec : EqDec 𝑹 := Empty_set_EqDec.
  Instance 𝑹𝑻_eq_dec (R : 𝑹) : EqDec (𝑹𝑻 R) := Empty_set_EqDec.
End NoRecords.

Module DefaultTypeKit <: TypeKit :=
  NoEnums <+ NoUnions <+ NoRecords.
