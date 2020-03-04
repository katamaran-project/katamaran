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

From Coq Require Import String.

Set Implicit Arguments.

Delimit Scope outcome_scope with out.

Inductive Outcome (A: Type) : Type :=
| outcome_pure (a: A)
| outcome_demonic {I : Type} (os: I -> Outcome A)
| outcome_angelic {I : Type} (os: I -> Outcome A)
| outcome_fail (msg: string)
.
Arguments outcome_fail {_} _.

Bind Scope outcome_scope with Outcome.

(* Definition outcome_fail {A : Type} : Outcome A := *)
(*   outcome_angelic (fun i : Empty_set => match i with end). *)
Definition outcome_block {A : Type} : Outcome A :=
  outcome_demonic (fun i : Empty_set => match i with end).

Fixpoint outcome_map {A B : Type} (f : A -> B) (o : Outcome A) : Outcome B :=
  match o with
  | outcome_pure a     => outcome_pure (f a)
  | outcome_demonic os => outcome_demonic (fun i => outcome_map f (os i))
  | outcome_angelic os => outcome_angelic (fun i => outcome_map f (os i))
  | outcome_fail s => outcome_fail s
  end.

Fixpoint outcome_bind {A B : Type} (o : Outcome A) (f : A -> Outcome B) : Outcome B :=
  match o with
  | outcome_pure a     => f a
  | outcome_demonic os => outcome_demonic (fun i => outcome_bind (os i) f)
  | outcome_angelic os => outcome_angelic (fun i => outcome_bind (os i) f)
  | outcome_fail s => outcome_fail s
  end.

Definition outcome_demonic_binary {A : Type} (o1 o2 : Outcome A) : Outcome A :=
  outcome_demonic (fun b : bool => if b then o1 else o2).
Definition outcome_angelic_binary {A : Type} (o1 o2 : Outcome A) : Outcome A :=
  outcome_angelic (fun b : bool => if b then o1 else o2).

Fixpoint outcome_satisfy {A : Type} (o : Outcome A) (P : A -> Prop) : Prop :=
  match o with
  | outcome_pure a     => P a
  | outcome_demonic os => forall i, outcome_satisfy (os i) P
  | outcome_angelic os => exists i, outcome_satisfy (os i) P
  | outcome_fail s => False
  end.

Definition outcome_safe {A : Type} (o : Outcome A) : Prop :=
  outcome_satisfy o (fun a => True).

Inductive outcome_satisfy_ind {A : Type} (P : A -> Prop) : Outcome A -> Prop :=
| outcome_satisfy_pure  a    :
    P a ->
    outcome_satisfy_ind P (outcome_pure a)
| outcome_satisfy_demonic {I os} :
    (forall i, outcome_satisfy_ind P (os i)) ->
    outcome_satisfy_ind P (@outcome_demonic _ I os)
| outcome_satisfy_angelic {I i os} :
    outcome_satisfy_ind P (os i) ->
    outcome_satisfy_ind P (@outcome_angelic _ I os).

Inductive outcome_in {A : Type} (a : A) : Outcome A -> Prop :=
| outcome_in_pure :
    outcome_in a (outcome_pure a)
| outcome_in_demonic {I os i} :
    outcome_in a (os i) ->
    outcome_in a (@outcome_demonic _ I os)
| outcome_in_angelic {I os i} :
    outcome_in a (os i) ->
    outcome_in a (@outcome_angelic _ I os).

Module OutcomeNotations.

  Notation "'⨂' i : I => F" := (outcome_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : outcome_scope.
  Notation "'⨁' i : I => F" := (outcome_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : outcome_scope.

  Infix "⊗" := outcome_demonic_binary (at level 40, left associativity) : outcome_scope.
  Infix "⊕" := outcome_angelic_binary (at level 50, left associativity) : outcome_scope.

  Notation "ma >>= f" := (outcome_bind ma f) (at level 50, left associativity) : outcome_scope.

End OutcomeNotations.
