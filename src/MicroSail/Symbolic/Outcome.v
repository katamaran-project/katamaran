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

From Coq Require Import
     Morphisms
     Program.Tactics
     List
     String.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Logic.

Set Implicit Arguments.

Delimit Scope outcome_scope with out.

Inductive Outcome (A: Type) : Type :=
| outcome_pure (a: A)
| outcome_angelic {I : Type} (os: I -> Outcome A)
| outcome_demonic {I : Type} (os: I -> Outcome A)
| outcome_angelic_binary (o1 o2 : Outcome A)
| outcome_demonic_binary (o1 o2 : Outcome A)
| outcome_fail (msg: string)
.
Arguments outcome_fail {_} _.

Section TransparentObligations.
  Local Set Transparent Obligations.
  Derive NoConfusion for Outcome.
End TransparentObligations.

Bind Scope outcome_scope with Outcome.

(* Definition outcome_fail {A : Type} : Outcome A := *)
(*   outcome_angelic (fun i : Empty_set => match i with end). *)
Definition outcome_block {A : Type} : Outcome A :=
  outcome_demonic (fun i : Empty_set => match i with end).

Definition outcome_angelic_list {A} (msg : string) : list A -> Outcome A :=
  fix outcome_angelic_list (xs : list A) :=
    match xs with
    | nil        => outcome_fail msg
    | cons x xs  => outcome_angelic_binary (outcome_pure x) (outcome_angelic_list xs)
    end.

(* Definition outcome_angelic_list {A} (msg : string) : list A -> Outcome A := *)
(*   fix outcome_angelic_list (xs : list A) := *)
(*     match xs with *)
(*     | nil        => outcome_fail msg *)
(*     | cons x nil => outcome_pure x *)
(*     | cons x xs  => outcome_angelic_binary (outcome_pure x) (outcome_angelic_list xs) *)
(*     end. *)

Fixpoint outcome_map {A B : Type} (f : A -> B) (o : Outcome A) : Outcome B :=
  match o with
  | outcome_pure a               => outcome_pure (f a)
  | outcome_angelic os           => outcome_angelic (fun i => outcome_map f (os i))
  | outcome_demonic os           => outcome_demonic (fun i => outcome_map f (os i))
  | outcome_angelic_binary o1 o2 => outcome_angelic_binary (outcome_map f o1) (outcome_map f o2)
  | outcome_demonic_binary o1 o2 => outcome_demonic_binary (outcome_map f o1) (outcome_map f o2)
  | outcome_fail s               => outcome_fail s
  end.

Fixpoint outcome_bind {A B : Type} (o : Outcome A) (f : A -> Outcome B) : Outcome B :=
  match o with
  | outcome_pure a               => f a
  | outcome_angelic os           => outcome_angelic (fun i => outcome_bind (os i) f)
  | outcome_demonic os           => outcome_demonic (fun i => outcome_bind (os i) f)
  | outcome_angelic_binary o1 o2 => outcome_angelic_binary (outcome_bind o1 f) (outcome_bind o2 f)
  | outcome_demonic_binary o1 o2 => outcome_demonic_binary (outcome_bind o1 f) (outcome_bind o2 f)
  | outcome_fail s               => outcome_fail s
  end.

Definition Error (s : string) : Prop := False.
Arguments Error s : simpl never.

Fixpoint outcome_satisfy {A : Type} (o : Outcome A) (P : A -> Prop) : Prop :=
  match o with
  | outcome_pure a               => P a
  | outcome_angelic os           => exists i, outcome_satisfy (os i) P
  | outcome_demonic os           => forall i, outcome_satisfy (os i) P
  | outcome_angelic_binary o1 o2 => outcome_satisfy o1 P \/ outcome_satisfy o2 P
  | outcome_demonic_binary o1 o2 => outcome_satisfy o1 P /\ outcome_satisfy o2 P
  | outcome_fail s               => Error s
  end.

Definition outcome_safe {A : Type} (o : Outcome A) : Prop :=
  outcome_satisfy o (fun a => True).

Lemma outcome_satisfy_map {A B : Type} (o : Outcome A) (f : A -> B) (P : B -> Prop) :
  outcome_satisfy (outcome_map f o) P <-> outcome_satisfy o (fun a => P (f a)).
Proof. induction o; firstorder. Qed.

Lemma outcome_satisfy_bind {A B : Type} (o : Outcome A) (f : A -> Outcome B) (P : B -> Prop) :
  outcome_satisfy (outcome_bind o f) P <-> outcome_satisfy o (fun a => outcome_satisfy (f a) P).
Proof. induction o; firstorder. Qed.

Lemma outcome_satisfy_monotonic {A : Type} {P Q : A -> Prop} (o : Outcome A) (hyp : forall a, P a -> Q a) :
  outcome_satisfy o P -> outcome_satisfy o Q.
Proof. induction o; firstorder. Qed.

Lemma outcome_satisfy_angelic_list {A msg xs} (P : A -> Prop) :
  outcome_satisfy (outcome_angelic_list msg xs) P <->
  exists x, In x xs /\ P x.
Proof.
  induction xs; cbn.
  - firstorder.
  - rewrite IHxs; firstorder; subst; auto.
Qed.

Lemma outcome_satisfy_map_angelic_list {A B msg xs} {f : A -> B} (P : B -> Prop) :
  outcome_satisfy (outcome_angelic_list msg (List.map f xs)) P <->
  outcome_satisfy (outcome_angelic_list msg xs) (fun x => P (f x)).
Proof.
  do 2 rewrite outcome_satisfy_angelic_list.
  split.
  - intros [b [H1 H2]].
    rewrite in_map_iff in H1.
    destruct H1 as [a [H0 H1]].
    subst b. now exists a.
  - intros [a [H1 H2]].
    exists (f a).
    auto using in_map.
Qed.

Lemma outcome_satisfy_filter_angelic_list {A msg xs} {f : A -> bool} (P : A -> Prop) :
  outcome_satisfy (outcome_angelic_list msg (List.filter f xs)) P <->
  outcome_satisfy (outcome_angelic_list msg xs) (fun x => P x /\ f x = true).
Proof.
  do 2 rewrite outcome_satisfy_angelic_list.
  split; intros [a [H1 H2]]; exists a.
  - rewrite filter_In in H1. intuition.
  - rewrite filter_In. intuition.
Qed.

Instance outcome_satisfy_iff_morphism {A} (o : Outcome A) :
  Proper (pointwise_relation A iff ==> iff) (@outcome_satisfy A o).
Proof. split; apply outcome_satisfy_monotonic; firstorder. Qed.

(* Inductive outcome_satisfy_ind {A : Type} (P : A -> Prop) : Outcome A -> Prop := *)
(* | outcome_satisfy_pure  a    : *)
(*     P a -> *)
(*     outcome_satisfy_ind P (outcome_pure a) *)
(* | outcome_satisfy_demonic {I os} : *)
(*     (forall i, outcome_satisfy_ind P (os i)) -> *)
(*     outcome_satisfy_ind P (@outcome_demonic _ I os) *)
(* | outcome_satisfy_angelic {I i os} : *)
(*     outcome_satisfy_ind P (os i) -> *)
(*     outcome_satisfy_ind P (@outcome_angelic _ I os). *)

(* Inductive outcome_in {A : Type} (a : A) : Outcome A -> Prop := *)
(* | outcome_in_pure : *)
(*     outcome_in a (outcome_pure a) *)
(* | outcome_in_demonic {I os i} : *)
(*     outcome_in a (os i) -> *)
(*     outcome_in a (@outcome_demonic _ I os) *)
(* | outcome_in_angelic {I os i} : *)
(*     outcome_in a (os i) -> *)
(*     outcome_in a (@outcome_angelic _ I os). *)

Module OutcomeNotations.

  Notation "'⨂' x .. y => F" :=
    (outcome_demonic (fun x => .. (outcome_demonic (fun y => F)) .. ))
    (at level 200, x binder, y binder, right associativity) : outcome_scope.
  Notation "'⨁' x .. y => F" :=
    (outcome_angelic (fun x => .. (outcome_angelic (fun y => F)) .. ))
    (at level 200, x binder, y binder, right associativity) : outcome_scope.

  Infix "⊗" := outcome_demonic_binary (at level 40, left associativity) : outcome_scope.
  Infix "⊕" := outcome_angelic_binary (at level 50, left associativity) : outcome_scope.

  Notation "ma >>= f" := (outcome_bind ma f) (at level 50, left associativity) : outcome_scope.

End OutcomeNotations.

Section Unused.

  Context `{SLL: ISepLogicLaws L}.

  Local Open Scope logic.

  Fixpoint outcome_satisfy_natded {A : Type} (o : Outcome A)
              (P : A -> L) {struct o} : L :=
    match o with
    | outcome_pure a => P a
    | @outcome_angelic _ I0 os =>
      ∃ i : I0, outcome_satisfy_natded (os i) P
    | @outcome_demonic _ IO os =>
      ∀ i : IO, outcome_satisfy_natded (os i) P
    | outcome_angelic_binary o1 o2 =>
      outcome_satisfy_natded o1 P ∨ outcome_satisfy_natded o2 P
    | outcome_demonic_binary o1 o2 =>
      outcome_satisfy_natded o1 P ∧ outcome_satisfy_natded o2 P
    | outcome_fail s => lfalse
  end.

  Axiom outcome_satisfy_natded_bind :
    forall {A B : Type} (o : Outcome A) (f : A -> Outcome B) (P : B -> L),
      outcome_satisfy_natded (outcome_bind o f) P ⊣⊢s
      outcome_satisfy_natded o (fun a => outcome_satisfy_natded (f a) P).

  Lemma outcome_satisfy_natded_monotonic {A : Type} {o : Outcome A} {P Q : A -> L}
    (hyp : forall a, P a ⊢ Q a) :
    outcome_satisfy_natded o P ⊢ outcome_satisfy_natded o Q.
  Proof.
    induction o; cbn.
    - apply hyp.
    - apply lex_left; intro i.
      apply lex_right with i.
      apply H.
    - apply lall_right; intro i.
      apply lall_left with i.
      apply H.
    - apply lor_left.
      + apply lor_right1.
        apply IHo1.
      + apply lor_right2.
        apply IHo2.
    - apply land_right.
      + apply land_left1.
        apply IHo1.
      + apply land_left2.
        apply IHo2.
    - apply entails_refl.
  Qed.

End Unused.
