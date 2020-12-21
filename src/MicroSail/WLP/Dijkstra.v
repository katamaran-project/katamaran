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
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith.
From MicroSail Require Import
     Context
     Environment
     Notation.

Set Implicit Arguments.

Definition Cont (R : Type) (A : Type) : Type := (A -> R) -> R.

(* Definition IStateT {I : Set} (S : I -> Set) (M : Type -> Type) (Γ1 Γ2 : I) (A : Type) : Type := *)
(*   S Γ1 -> M (A * S Γ2)%type. *)

(* Definition StateT (S : Set) (M : Type -> Type) := IStateT (fun _ : unit => S) M tt tt. *)

(* Definition DST (G : Set) {I : Set} (L : I -> Set) (Γ1 Γ2 : I) (A : Type) : Type := *)
(*   IStateT L (StateT G (Cont Prop)) Γ1 Γ2 A. *)

Definition DST (G : Type) {I : Type} (L : I -> Type) (Γ1 Γ2 : I) (A : Type) : Type :=
  (A -> L Γ2 -> G -> Prop) -> L Γ1 -> G -> Prop.


Section WithGIL.
  Context {G : Type}.
  Context {I : Type}.
  Context {L : I -> Type}.
  (* Local Set Maximal Implicit Insertion. *)

  Definition evalDST {A Γ1 Γ2} (m : DST G L Γ1 Γ2 A) :
    L Γ1 -> Cont (G -> Prop) A :=
    fun δ1 k => m (fun a δ2 => k a) δ1.

  Definition lift_cont {Γ A} (m : Cont Prop A) : DST G L Γ Γ A :=
    fun k δ γ => m (fun a => k a δ γ).
  Definition lift_cont_global {Γ A} (m : Cont (G -> Prop) A) : DST G L Γ Γ A :=
    fun k δ => m (fun a => k a δ).

  Definition pure {Γ A} (a : A) : DST G L Γ Γ A :=
    fun k => k a.
  Definition ap {Γ1 Γ2 Γ3 A B} (mf : DST G L Γ1 Γ2 (A -> B))
             (ma : DST G L Γ2 Γ3 A) : DST G L Γ1 Γ3 B :=
    fun k => mf (fun f => ma (fun a => k (f a))).
  Definition abort {Γ1 Γ2 A} : DST G L Γ1 Γ2 A :=
    fun k δ s => False.
  Definition assert {Γ} (b : bool) : DST G L Γ Γ bool :=
    fun k δ s => b = true /\ k b δ s.
  Definition bind {Γ1 Γ2 Γ3 A B} (ma : DST G L Γ1 Γ2 A) (f : A -> DST G L Γ2 Γ3 B) : DST G L Γ1 Γ3 B :=
    fun k => ma (fun a => f a k).
  Definition bindright {Γ1 Γ2 Γ3 A B} (ma : DST G L Γ1 Γ2 A) (mb : DST G L Γ2 Γ3 B) : DST G L Γ1 Γ3 B :=
    bind ma (fun _ => mb).
  Definition bindleft {Γ1 Γ2 Γ3 A B} (ma : DST G L Γ1 Γ2 A) (mb : DST G L Γ2 Γ3 B) : DST G L Γ1 Γ3 A :=
    bind ma (fun a => bind mb (fun _ => pure a)).
  Definition get_local {Γ} : DST G L Γ Γ (L Γ) :=
    fun k δ => k δ δ.
  Definition put_local {Γ Γ'} (δ' : L Γ') : DST G L Γ Γ' unit :=
    fun k _ => k tt δ'.
  Definition modify_local {Γ Γ'} (f : L Γ -> L Γ') : DST G L Γ Γ' unit :=
    bind get_local (fun δ => put_local (f δ)).
  Definition get_global {Γ} : DST G L Γ Γ G :=
    fun k δ γ => k γ δ γ.
  Definition put_global {Γ} (γ : G) : DST G L Γ Γ unit :=
    fun k δ _ => k tt δ γ.
  Definition modify_global {Γ} (f : G -> G) : DST G L Γ Γ unit :=
    bind get_global (fun γ => put_global (f γ)).
  Definition ifthenelse {Γ1 Γ2 A} (b : bool) (t e : DST G L Γ1 Γ2 A) : DST G L Γ1 Γ2 A :=
    fun k δ γ => (b = true -> t k δ γ) /\ (b = false -> e k δ γ).

  Global Arguments abort {_ _ _} / _ _ _.
  Global Arguments assert {_} _ / _ _ _.
  Global Arguments bind {_ _ _ _ _} _ _ / _ _ _.
  Global Arguments bindleft {_ _ _ _ _} _ _ / _ _ _.
  Global Arguments bindright {_ _ _ _ _} _ _ / _ _ _.
  Global Arguments evalDST {_ _ _} _ / _ _ _.
  Global Arguments get_global {_} / _ _ _.
  Global Arguments get_local {_} / _ _ _.
  Global Arguments lift_cont {_ _} _ / _ _ _.
  Global Arguments lift_cont_global {_ _} _ / _ _ _.
  Global Arguments modify_global {_} _ / _ _ _.
  Global Arguments modify_local {_ _} _ / _ _ _.
  Global Arguments pure {_ _} _ / _ _ _.
  Global Arguments put_global {_} _ / _ _ _.
  Global Arguments put_local {_ _} _ / _ _ _.
  Global Arguments ifthenelse {_ _ _} _ _ _ / _ _ _.

End WithGIL.

Section WithGBD.
  Context {G : Type}.
  Context {X T : Set}.
  Context {D : T -> Set}.

  Import CtxNotations.

  Definition pop {Γ x σ} : DST G (@NamedEnv X T D) (Γ ▻ (x :: σ)) Γ unit :=
    modify_local (fun δ => env_tail δ).
  Definition pops {Γ} Δ : DST G (@NamedEnv X T D) (Γ ▻▻ Δ) Γ unit :=
    modify_local (fun δΓΔ => env_drop Δ δΓΔ).
  Definition push {Γ x} σ (v : D σ) : DST G (@NamedEnv X T D) Γ (Γ ▻ (x :: σ)) unit :=
    modify_local (fun δ => env_snoc δ (x :: σ) v).
  Definition pushs {Γ Δ} (δΔ : @NamedEnv X T D Δ) : DST G (@NamedEnv X T D) Γ (Γ ▻▻ Δ) unit :=
    modify_local (fun δΓ => env_cat δΓ δΔ).

  Global Arguments pop {_ _ _} / _ _ _.
  Global Arguments pops {_} _ / _ _ _.
  Global Arguments push {_ _} _ _ / _ _ _.
  Global Arguments pushs {_ _} _ / _ _ _.

End WithGBD.

Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : monad_scope.
Notation "ma *> mb" := (bindright ma mb) (at level 50, left associativity) : monad_scope.
Notation "ma <* mb" := (bindleft ma mb) (at level 50, left associativity) : monad_scope.
Notation "s1 ;; s2" := (bind s1 (fun _ => s2)) : monad_scope.
