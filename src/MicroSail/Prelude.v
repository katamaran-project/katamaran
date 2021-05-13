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
     Bool.Bool
     Lists.List
     Logic.FinFun
     Strings.String
     ZArith.ZArith.

From Coq Require
     Vector
     ssr.ssrbool.

From Equations Require Import
     Equations.

(* stdpp changes a lot of flags and changes implicit arguments of standard
   library functions and constructors. Import the module here, so that the
   changes are consistently applied over our code base. *)
From stdpp Require
     base countable finite list option vector.

Import ListNotations.

Set Implicit Arguments.

Scheme Equality for list.
Scheme Equality for prod.
Scheme Equality for sum.
Scheme Equality for option.

Section WithA.
  Context {A : Type}.

  Definition all_list (P : A -> Prop) : list A -> Prop :=
    fix all_list (xs : list A) : Prop :=
      match xs with
      | nil       => True
      | cons x xs => P x /\ all_list xs
      end.

  Section WithEq.
    Variable eqbA : A -> A -> bool.
    Let eqbA_spec := fun x => forall y, reflect (x = y) (eqbA x y).

    Lemma list_beq_spec (hyp : forall x : A, eqbA_spec x) :
      forall xs ys : list A, reflect (xs = ys) (list_beq eqbA xs ys).
    Proof.
      induction xs as [|x xs]; intros [|y ys]; cbn; try (constructor; congruence).
      destruct (hyp x y).
      - apply (ssrbool.iffP (IHxs ys)); congruence.
      - constructor; congruence.
    Qed.

    Lemma option_beq_spec (hyp : forall x : A, eqbA_spec x) :
      forall xs ys : option A, reflect (xs = ys) (option_beq eqbA xs ys).
    Proof.
      intros [x|] [y|]; cbn in *; try constructor; try congruence.
      apply (ssrbool.iffP (hyp x y)); congruence.
    Qed.

  End WithEq.

End WithA.

Lemma all_list_map {A B} {P : B -> Prop} {xs : list A} (f : A -> B) :
  all_list P (map f xs) <-> all_list (fun a => P (f a)) xs.
Proof.
  induction xs; cbn; intuition.
Qed.

Lemma all_list_impl {A} {P1 P2 : A -> Prop} {xs : list A} :
  (forall x, P1 x -> P2 x) ->
  all_list P1 xs -> all_list P2 xs.
Proof.
  induction xs; cbn; intuition.
Qed.

Section Equality.

  Definition f_equal_dec {A B : Type} (f : A -> B) {x y : A} (inj : f x = f y -> x = y)
             (hyp : dec_eq x y) : dec_eq (f x) (f y) :=
    match hyp with
    | left p => left (f_equal f p)
    | right p => right (fun e : f x = f y => p (inj e))
    end.

  Definition f_equal2_dec {A1 A2 B : Type} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2}
             (inj : f x1 x2 = f y1 y2 -> @sigmaI _ _ x1 x2 = @sigmaI _ _ y1 y2)
             (hyp1 : dec_eq x1 y1) (hyp2 : dec_eq x2 y2) :
    dec_eq (f x1 x2) (f y1 y2) :=
    match hyp1 , hyp2 with
    | left  p , left q  => left (eq_trans
                                   (f_equal (f x1) q)
                                   (f_equal (fun x => f x y2) p))
    | left  p , right q =>
      right (fun e => q (f_equal (@pr2 _ (fun _ => _)) (inj e)))
    | right p , _       =>
      right (fun e => p (f_equal (@pr1 _ (fun _ => _)) (inj e)))
    end.

  Local Set Transparent Obligations.

  Global Instance Z_eqdec : EqDec Z := Z.eq_dec.
  Global Instance string_eqdec : EqDec string := string_dec.
  Derive NoConfusion EqDec for Empty_set.
  Derive Signature NoConfusion NoConfusionHom for Vector.t.

  Global Instance option_eqdec `{EqDec A} : EqDec (option A).
  Proof. eqdec_proof. Defined.
  Global Instance vector_eqdec `{EqDec A} {n} : EqDec (Vector.t A n).
  Proof. eqdec_proof. Defined.

  Definition eq_dec_het {I} {A : I -> Type} `{eqdec : EqDec (sigT A)}
    {i1 i2} (x1 : A i1) (x2 : A i2) : dec_eq (existT i1 x1) (existT i2 x2) :=
    eq_dec (existT i1 x1) (existT i2 x2).

  Import stdpp.base.

  Global Instance EqDecision_from_EqDec `{eqdec : EqDec A} :
    EqDecision A | 10 := eqdec.

End Equality.

Section Finite.

  Import stdpp.finite.

  Lemma nodup_fixed `{EqDec A} (l : list A) : nodup eq_dec l = l -> NoDup l.
  Proof.
    intros <-.
    apply NoDup_ListNoDup.
    apply NoDup_nodup.
  Qed.

End Finite.

Definition IsSome {A : Type} (m : option A) : Type :=
  match m with
  | Some _ => unit
  | None   => Empty_set
  end.

Definition fromSome {A : Type} (m : option A) : IsSome m -> A :=
  match m return IsSome m -> A with
  | Some a => fun _ => a
  | None   => fun p => match p with end
  end.

Section Countable.

  Import stdpp.countable.

  Global Program Instance Countable_sigT {A B} {EqDecA : EqDecision A} {CountA: Countable A}
    {EqDecB : forall (a:A), EqDecision (B a)} {CountB: forall a, Countable (B a)} :
    @Countable (sigT B) (sigma_eqdec EqDecA EqDecB)  :=
    {| encode x := prod_encode (encode (projT1 x)) (encode (projT2 x));
       decode p :=
         a ← (prod_decode_fst p ≫= decode);
         b ← (prod_decode_snd p ≫= decode);
         mret (existT a b)
    |}.
  Next Obligation.
    intros ? ? ? ? ? ? [a b].
    rewrite prod_decode_encode_fst; cbn.
    rewrite decode_encode; cbn.
    rewrite prod_decode_encode_snd; cbn.
    rewrite decode_encode; cbn.
    reflexivity.
  Defined.

End Countable.

Section Traverse.

  Local Set Universe Polymorphism.
  Import stdpp.base.

  Context `{MRet M, MBind M} {A B : Type} (f : A -> M B).

  Fixpoint traverse_list (xs : list A) : M (list B) :=
    match xs with
    | nil       => mret nil
    | cons x xs => b ← f x ; bs ← traverse_list xs ; mret (cons b bs)
    end.

  Fixpoint traverse_vector {n} (xs : Vector.t A n) : M (Vector.t B n) :=
    match xs with
    | Vector.nil => mret Vector.nil
    | Vector.cons x xs =>
      b ← f x ; bs ← traverse_vector xs ; mret (Vector.cons b bs)
    end.

End Traverse.

Inductive OptionSpec {A} (S : A -> Prop) (N : Prop) : option A -> Prop :=
| OptionSpecSome {a : A} : S a -> OptionSpec S N (Some a)
| OptionSpecNone  : N -> OptionSpec S N None.

Derive Signature for OptionSpec.

Definition option_ap {A B : Type} (f : option (A -> B)) (a : option A) : option B :=
  match f with
  | Some f => option_map f a
  | None => None
  end.

Definition option_bind {A B : Type} (f : A -> option B) (a : option A) : option B :=
  base.mbind f a.
Definition option_comp {A B C : Type} (f : A -> option B) (g : B -> option C) :=
  fun a => option_bind g (f a).

Lemma optionspec_map {A B : Type} (S : B -> Prop) (N : Prop)
      (f : A -> B) (o : option A) :
  OptionSpec S N (option_map f o) <->
  OptionSpec (fun a => S (f a)) N o.
Proof. split; intro H; destruct o; depelim H; now constructor. Qed.

Lemma optionspec_ap {A B : Type} (S : B -> Prop) (N : Prop)
      (f : option (A -> B)) (o : option A) :
  OptionSpec S N (option_ap f o) <->
  OptionSpec (fun f => OptionSpec (fun a => S (f a)) N o) N f.
Proof.
  split.
  - intro H. destruct f; cbn in *.
    + constructor. revert H. apply optionspec_map.
    + constructor. now depelim H.
  - intro H. destruct f; cbn in *.
    + depelim H. revert H. apply optionspec_map.
    + constructor. now depelim H.
Qed.

Lemma optionspec_monotonic {A : Type} (S1 S2 : A -> Prop) (N1 N2 : Prop)
      (fS : forall a, S1 a -> S2 a) (fN: N1 -> N2) :
  forall (o : option A),
    OptionSpec S1 N1 o -> OptionSpec S2 N2 o.
Proof. intros ? []; constructor; auto. Qed.

Fixpoint heap_extractions {C} (h : list C) : list (C * list C) :=
  match h with
  | nil      => []
  | cons c h => cons (pair c h) (map (fun '(pair c' h') => (pair c' (cons c h'))) (heap_extractions h))
  end.

Lemma heap_extractions_map {A B} (f : A -> B) (h : list A) :
  heap_extractions (List.map f h) = List.map (base.prod_map f (List.map f)) (heap_extractions h).
Proof.
  induction h; cbn.
  - reflexivity.
  - f_equal.
    rewrite IHh.
    rewrite ?List.map_map.
    apply List.map_ext.
    intros [x xs]. reflexivity.
Qed.
