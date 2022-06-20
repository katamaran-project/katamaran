(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese                      *)
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

From Coq Require Export
     Numbers.BinNums.
From Coq Require Import
     Bool.Bool
     Logic.StrictProp
     Lists.List
     NArith.NArith
     Strings.String
     ZArith.BinInt.

From Coq Require
     ssr.ssrbool.

From Equations Require Import
     Equations.

(* stdpp changes a lot of flags and changes implicit arguments of standard
   library functions and constructors. Import the module here, so that the
   changes are consistently applied over our code base. *)
From stdpp Require
     base countable finite list option vector.

Local Set Implicit Arguments.

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

  Definition EqbSpecPoint {A} (eqb : A -> A -> bool) (x : A) : Type :=
    forall y, reflect (x = y) (eqb x y).

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

Definition IsTrue (b : bool) : SProp :=
  if b then sUnit else sEmpty.

Module option.

  Definition isSome {A} (m : option A) : bool :=
    match m with Some _ => true | None => false end.
  Definition isNone {A} (m : option A) : bool :=
    match m with Some _ => false | None => true end.

  Definition IsSome {A} (m : option A) : SProp :=
    IsTrue (isSome m).

  Definition fromSome {A} (m : option A) : IsSome m -> A :=
    match m with Some a => fun _ => a | None => fun p => match p with end end.

  Definition map {A B} (f : A -> B) (o : option A) : option B :=
    match o with Some a => Some (f a) | None => None end.
  Definition bind {A B} (a : option A) (f : A -> option B) : option B :=
    match a with Some x => f x | None => None end.
  Definition comp {A B C : Type} (f : A -> option B) (g : B -> option C) :=
    fun a => bind (f a) g.

  Arguments map {A B} f !o.
  Arguments bind {A B} !a f.

  Module Import notations.

    Notation "' x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
          format "' x  <-  ma  ;;  mb").
    Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at next level, mb at level 200, right associativity).
    Notation "f <$> a" := (map f a) (at level 40, left associativity).
    Notation "f <*> a" :=
      (match f with Some g => map g a | None => None end)
        (at level 40, left associativity).

  End notations.

  (* Easy eq patterns *)
  Lemma map_eq_some {A B} (f : A -> B) (o : option A) (a : A) :
    o = Some a ->
    map f o = Some (f a).
  Proof. now intros ->. Qed.

  Lemma bind_eq_some {A B} (f : A -> option B) (o : option A) (b : B) :
    (exists a, o = Some a /\ f a = Some b) <->
    bind o f = Some b.
  Proof.
    split.
    - now intros (a & -> & <-).
    - destruct o as [a|]; [ now exists a | discriminate ].
  Qed.

  (* Variant of Bool.reflect and BoolSpec for options, i.e.
     a weakest pre without effect observation. *)
  Inductive spec {A} (S : A -> Prop) (N : Prop) : option A -> Prop :=
  | specSome {a : A} : S a -> spec S N (Some a)
  | specNone         : N -> spec S N None.

  (* Total correctness weakest pre for option. Arguments are inversed. *)
  Inductive wp {A} (S : A -> Prop) : option A -> Prop :=
  | wpSome {a : A} : S a -> wp S (Some a).

  (* Partial correctness weakest pre for option. Arguments are inversed. *)
  Inductive wlp {A} (S : A -> Prop) : option A -> Prop :=
  | wlpSome {a : A} : S a -> wlp S (Some a)
  | wlpNone         : wlp S None.

  (* We define equivalent formulations using pattern matches and
     logical connectives plus constructors. *)
  Lemma spec_match {A S N} (o : option A) :
    spec S N o <-> match o with
                   | Some a => S a
                   | None   => N
                   end.
  Proof.
    split.
    - intros []; auto.
    - destruct o; now constructor.
  Qed.

  Lemma wp_match {A S} (o : option A) :
    wp S o <-> match o with
               | Some a => S a
               | None   => False
               end.
  Proof.
    split.
    - intros []; auto.
    - destruct o; [apply wpSome|contradiction].
  Qed.

  Lemma wp_exists {A} (Q : A -> Prop) (o : option A) :
    wp Q o <-> exists a, o = Some a /\ Q a.
  Proof.
    rewrite wp_match. split.
    - destruct o; eauto; contradiction.
    - now intros [a [-> HQ]].
  Qed.

  Lemma wlp_match {A S} (o : option A) :
    wlp S o <-> match o with
               | Some a => S a
               | None   => True
               end.
  Proof.
    split.
    - intros []; auto.
    - destruct o; auto using wlpSome, wlpNone.
  Qed.

  Lemma wlp_forall {A} (Q : A -> Prop) (o : option A) :
    wlp Q o <-> forall a, o = Some a -> Q a.
  Proof.
    rewrite wlp_match. split.
    - intros; subst; auto.
    - destruct o; auto.
  Qed.

  Section Bind.

    Context {A B} {S : B -> Prop} {N : Prop} (f : A -> option B) (o : option A).

    Local Ltac proof :=
      destruct o; rewrite ?spec_match, ?wp_match, ?wlp_match; auto.

    Lemma spec_bind : spec S N (bind o f) <-> spec (fun a => spec S N (f a)) N o.
    Proof. proof. Qed.
    Definition spec_bind_elim := proj1 spec_bind.
    Definition spec_bind_intro := proj2 spec_bind.

    Lemma wp_bind : wp S (bind o f) <-> wp (fun a => wp S (f a)) o.
    Proof. proof. Qed.
    Definition wp_bind_elim := proj1 wp_bind.
    Definition wp_bind_intro := proj2 wp_bind.

    Lemma wlp_bind : wlp S (bind o f) <-> wlp (fun a => wlp S (f a)) o.
    Proof. proof. Qed.

    Definition wlp_bind_elim := proj1 wlp_bind.
    Definition wlp_bind_intro := proj2 wlp_bind.

  End Bind.

  Lemma spec_map {A B S N} (f : A -> B) (o : option A) :
    spec S N (map f o) <-> spec (fun a => S (f a)) N o.
  Proof. do 2 rewrite spec_match; now destruct o. Qed.

  Lemma spec_ap {A B S N} (f : option (A -> B)) (o : option A) :
    spec S N (f <*> o) <->
    spec (fun f => spec (fun a => S (f a)) N o) N f.
  Proof.
    do 2 rewrite spec_match. destruct f; auto.
    rewrite spec_match; now destruct o.
  Qed.

  Lemma spec_monotonic {A} (S1 S2 : A -> Prop) (N1 N2 : Prop)
    (fS : forall a, S1 a -> S2 a) (fN: N1 -> N2) :
    forall (o : option A),
      spec S1 N1 o -> spec S2 N2 o.
  Proof. intros ? []; constructor; auto. Qed.

  Lemma wp_map {A B S} (f : A -> B) (o : option A) :
    wp S (map f o) <-> wp (fun a => S (f a)) o.
  Proof. do 2 rewrite wp_match; now destruct o. Qed.

  Lemma wp_ap {A B S} (f : option (A -> B)) (o : option A) :
    wp S (f <*> o) <->
    wp (fun f => wp (fun a => S (f a)) o) f.
  Proof.
    do 2 rewrite wp_match. destruct f; auto.
    rewrite wp_match; now destruct o.
  Qed.

  Lemma wp_monotonic {A} (S1 S2 : A -> Prop) (fS : forall a, S1 a -> S2 a)  :
    forall (o : option A), wp S1 o -> wp S2 o.
  Proof. intros ? []; constructor; auto. Qed.

  Lemma wlp_map {A B S} (f : A -> B) (o : option A) :
    wlp S (map f o) <-> wlp (fun a => S (f a)) o.
  Proof. do 2 rewrite wlp_match; now destruct o. Qed.

  Lemma wlp_ap {A B S} (f : option (A -> B)) (o : option A) :
    wlp S (f <*> o) <->
    wlp (fun f => wlp (fun a => S (f a)) o) f.
  Proof.
    do 2 rewrite wlp_match. destruct f; auto.
    rewrite wlp_match; now destruct o.
  Qed.

  Lemma wlp_monotonic {A} (S1 S2 : A -> Prop) (fS : forall a, S1 a -> S2 a)  :
    forall (o : option A), wlp S1 o -> wlp S2 o.
  Proof. intros ? []; constructor; auto. Qed.

  Module tactics.

    Ltac mixin :=
      lazymatch goal with
      | |- wp _ (Some _) => constructor
      | |- wp _ (map _ _) => apply wp_map
      | |- wp _ (bind _ _) => apply wp_bind_intro
      | |- wp _ (_ <*> _) => apply wp_ap
      | |- wlp _ (Some _) => constructor
      | |- wlp _ (map _ _) => apply wlp_map
      | |- wlp _ (bind _ _) => apply wlp_bind_intro
      | |- wlp _ (_ <*> _) => apply wlp_ap
      | H: wp _ ?x |- wp _ ?x => revert H; apply wp_monotonic; intros
      | H: wlp _ ?x |- wlp _ ?x => revert H; apply wlp_monotonic; intros
      end.

  End tactics.

  Section Traverse.
    Context {A B} (f : A -> option B).

    Fixpoint traverse_list (xs : list A) : option (list B) :=
      match xs with
      | nil       => Some nil
      | cons x xs => b <- f x ;; bs <- traverse_list xs ;; Some (cons b bs)
      end.

    Fixpoint traverse_vector {n} (xs : Vector.t A n) : option (Vector.t B n) :=
      match xs with
      | Vector.nil       => Some Vector.nil
      | Vector.cons x xs => b <- f x ;; bs <- traverse_vector xs ;; Some (Vector.cons b bs)
      end.

  End Traverse.

End option.

Lemma and_iff_compat_r' (A B C : Prop) :
  (B /\ A <-> C /\ A) <-> (A -> B <-> C).
Proof. intuition. Qed.

Lemma and_iff_compat_l' (A B C : Prop) :
  (A /\ B <-> A /\ C) <-> (A -> B <-> C).
Proof. intuition. Qed.

Lemma imp_iff_compat_l' (A B C : Prop) :
  ((A -> B) <-> (A -> C)) <-> (A -> B <-> C).
Proof. intuition. Qed.

Lemma rightid_and_true (A : Prop) :
  A /\ True <-> A.
Proof. intuition. Qed.

Lemma leftid_true_and (A : Prop) :
  True /\ A <-> A.
Proof. intuition. Qed.

Lemma exists_or_compat {A} (P Q : A -> Prop):
  (exists a, P a \/ Q a) <-> (exists a, P a) \/ (exists a, Q a).
Proof. firstorder. Qed.

Lemma forall_and_compat {A} (P Q : A -> Prop):
  (forall a, P a /\ Q a) <-> (forall a, P a) /\ (forall a, Q a).
Proof. firstorder. Qed.

Declare Scope alt_scope.
Declare Scope asn_scope.
Declare Scope exp_scope.
Declare Scope modal_scope.
Declare Scope mut_scope.
Declare Scope pat_scope.
Delimit Scope alt_scope with alt.
Delimit Scope asn_scope with asn.
Delimit Scope exp_scope with exp.
Delimit Scope modal_scope with modal.
Delimit Scope mut_scope with mut.
Delimit Scope pat_scope with pat.

Definition findAD {A} {B : A -> Type} {eqA: EqDec A} (a : A) :
  list (sigT B) -> option (B a) :=
  fix find (xs : list (sigT B)) : option (B a) :=
    match xs with
    | nil                   => None
    | cons (existT a' b) xs =>
        match eq_dec a a' with
        | left e  => Some (eq_rect_r B b e)
        | right _ => find xs
        end
    end.

Record Stats : Set :=
  { branches : N
  ; pruned   : N
  }.

Definition plus_stats (x y : Stats) : Stats :=
  {| branches := branches x + branches y;
     pruned   := pruned x + pruned y
  |}.
Definition empty_stats : Stats :=
  {| branches := 0; pruned   := 0|}.
