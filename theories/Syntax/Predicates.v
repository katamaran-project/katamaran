(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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

From Katamaran Require Import
     Context
     Environment
     Prelude
     Base.

From Equations Require Import
     Equations.

Class IsDuplicable (T : Type) :=
  { is_duplicable : T -> bool
  }.

Module Type PurePredicateKit (Import B : Base).
  (** Pure Predicates *)
  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Parameter Inline 𝑷_inst : forall p : 𝑷, env.abstract Val (𝑷_Ty p) Prop.

  #[export] Declare Instance 𝑷_eq_dec : EqDec 𝑷.

End PurePredicateKit.

Module Type HeapPredicateKit (Import B : Base).
  (** Heap Predicates *)
  (* Predicate names. *)
  Parameter Inline 𝑯  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑯_Ty : 𝑯 -> Ctx Ty.
  (* Duplicable? *)
  #[export] Declare Instance 𝑯_is_dup : IsDuplicable 𝑯.

  #[export] Declare Instance 𝑯_eq_dec : EqDec 𝑯.

  Parameter 𝑯_precise : forall p : 𝑯, option (Precise 𝑯_Ty p).

End HeapPredicateKit.

Module Type PredicateKit (B : Base) :=
  PurePredicateKit B <+ HeapPredicateKit B.

Module DefaultPurePredicateKit (Import B : Base) <: PurePredicateKit B.

  Definition 𝑷 := Empty_set.
  Definition 𝑷_Ty : 𝑷 -> Ctx Ty := fun p => match p with end.
  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop := match p with end.
  #[export] Instance 𝑷_eq_dec : EqDec 𝑷 := fun p => match p with end.

End DefaultPurePredicateKit.

Module DefaultHeapPredicateKit (Import B : Base) <: HeapPredicateKit B.

  Definition 𝑯 := Empty_set.
  Definition 𝑯_Ty : 𝑯 -> Ctx Ty := fun p => match p with end.
  #[export] Instance 𝑯_eq_dec : EqDec 𝑯 := fun p => match p with end.
  #[export] Instance 𝑯_is_dup : IsDuplicable 𝑯 := { is_duplicable := fun p => match p with end }.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) := None.

End DefaultHeapPredicateKit.

Module DefaultPredicateKit (B : Base) :=
  DefaultPurePredicateKit B <+ DefaultHeapPredicateKit B.
