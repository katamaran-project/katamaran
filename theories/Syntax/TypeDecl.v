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
     Bool.Bool
     Strings.String
     ZArith.BinInt.
Require Import stdpp.base.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Bitvector
     Context
     Prelude.
From Coq Require Import
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Module ty.

  Class TypeDeclKit : Type :=
    { (* Type constructor names. *)
      (* enumi    : Set;           (* Names of enum type constructors. *) *)
      unioni   : Set;           (* Names of union type constructors. *)
      (* recordi  : Set;           (* Names of record type constructors. *) *)
    }.

  Section WithTypeDecl.

    Local Unset Elimination Schemes.
    Local Set Transparent Obligations.

    Inductive Ty {TK : TypeDeclKit} : Set :=
    | int
    | bool
    | string
    (* | list (σ : Ty) *)
    | prod (σ τ : Ty)
    (* | sum  (σ τ : Ty) *)
    | unit
    (* | enum (E : enumi) *)
    | bvec (n : nat)
    (* | tuple (σs : Ctx Ty) *)
    | union (U : unioni)
    (* | record (R : recordi) *)
    .
    Derive NoConfusion for Ty.
    Context {TK : TypeDeclKit}.


    (* convenience definition. *)
    (* Definition option : Ty -> Ty := fun T => sum T unit. *)

    Section Ty_rect.
      Variable P : Ty -> Type.

      Hypothesis (P_int    : P int).
      Hypothesis (P_bool   : P bool).
      Hypothesis (P_string : P string).
      (* Hypothesis (P_list   : forall σ, P σ -> P (list σ)). *)
      Hypothesis (P_prod   : forall σ τ, P σ -> P τ -> P (prod σ τ)).
      (* Hypothesis (P_sum    : forall σ τ, P σ -> P τ -> P (sum σ τ)). *)
      Hypothesis (P_unit   : P unit).
      (* Hypothesis (P_enum   : forall E, P (enum E)). *)
      Hypothesis (P_bvec   : forall n, P (bvec n)).
      (* Hypothesis (P_tuple  : forall σs (IH : ctx.All P σs), P (tuple σs)). *)
      Hypothesis (P_union  : forall U, P (union U)).
      (* Hypothesis (P_record : forall R, P (record R)). *)

      Fixpoint Ty_rect (σ : Ty) : P σ :=
        match σ with
        | int      => ltac:(apply P_int)
        | bool     => ltac:(apply P_bool)
        | string   => ltac:(apply P_string)
        (* | list σ   => ltac:(apply P_list; auto) *)
        | prod σ τ => ltac:(apply P_prod; auto)
        (* | sum σ τ  => ltac:(apply P_sum; auto) *)
        | unit     => ltac:(apply P_unit; auto)
        (* | enum E   => ltac:(apply P_enum; auto) *)
        | bvec n   => ltac:(apply P_bvec; auto)
        (* | tuple σs => ltac:(apply P_tuple, ctx.all_intro, Ty_rect) *)
        | union U  => ltac:(apply P_union; auto)
        (* | record R => ltac:(apply P_record; auto) *)
        end.

    End Ty_rect.

    Definition Ty_rec (P : Ty -> Set) := Ty_rect P.
    Definition Ty_ind (P : Ty -> Prop) := Ty_rect P.

  End WithTypeDecl.

  Class TypeDenoteKit (TDC : TypeDeclKit) : Type :=
    { (* Mapping enum type constructor names to enum types *)
      (* enumt   : enumi -> Set; *)
      (* Mapping union type constructor names to union types *)
      uniont  : unioni -> Set;
      (* (* Mapping record type constructor names to record types *) *)
      (* recordt : recordi -> Set; *)
    }.

  Section WithTypeDenote.

    Fixpoint Val {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} (σ : Ty) : Set :=
      match σ with
      | int => Z
      | bool => Datatypes.bool
      | string => String.string
      (* | list σ' => Datatypes.list (Val σ') *)
      | prod σ1 σ2 => Val σ1 * Val σ2
      (* | sum σ1 σ2 => Val σ1 + Val σ2 *)
      | unit => Datatypes.unit
      (* | enum E => enumt E *)
      | bvec n => bv n
      (* | tuple σs => EnvRec Val σs *)
      | union U => uniont U
      (* | record R => recordt R *)
      end%type.

    #[universes(template)]
      (* Set Universe Polymorphism. *)
      Inductive RV (A : Type) : Type :=
    | SyncVal : A -> RV A
    | NonSyncVal : A -> A -> RV A
    .
    Global Arguments SyncVal {A}.
    Global Arguments NonSyncVal {A}.

    Section NoConfRV.
      Set Transparent Obligations.
      Derive NoConfusion for RV.
    End NoConfRV.

    Definition RVToOption {A} (rv : RV A) : option A :=
      match rv with
      | SyncVal v => Some v
      | NonSyncVal _ _ => None
      end.
    
    Definition projLeftRV {A} (rv : RV A) : A :=
      match rv with
      | SyncVal v => v
      | NonSyncVal vl _ => vl
      end.
    Global Arguments projLeftRV {A} !rv.

    Definition projRightRV {A} (rv : RV A) : A :=
      match rv with
      | SyncVal v => v
      | NonSyncVal _ vr => vr
      end.
    Global Arguments projRightRV {A} !rv.

    Definition RelVal {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} (τ : Ty) : Set :=
      RV (Val τ)
    .

    Ltac destructRVs :=
      repeat match goal with
          |- context[match ?b with
                     | SyncVal _ => _
                     | _ => _
                     end] => destruct b; cbn
        end.

    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.

    Definition projLeft {A} (rv : RelVal A) : Val A :=
      projLeftRV rv.
    Global Arguments projLeft {A} !rv.

    Definition projRight {A} (rv : RelVal A) : Val A :=
      projRightRV rv.
    Global Arguments projRight {A} !rv.

    Definition liftUnOpRV {A B} (f : A -> B) (rv : RV A) : RV B :=
      match rv with
      | (SyncVal v) => SyncVal (f v)
      | (NonSyncVal vl vr) => NonSyncVal (f vl) (f vr)
      end.
    Global Arguments liftUnOpRV {A B} f !rv.

    #[export] Instance proper_liftUnOpRV {A B : Type} : Proper ((pointwise_relation _ eq) ==> eq ==> eq) (@liftUnOpRV A B).
    Proof.
      intros f g Rfg rv rv' eq.
      destruct rv, rv'; cbn; inversion eq;
        rewrite Rfg; auto.
    Qed.

    Lemma comProjLeftRVLiftUnOpRV {A B} (f : A -> B) (rv : RV A) :
      projLeftRV (liftUnOpRV f rv) = f (projLeftRV rv).
    Proof.
      destruct rv; auto.
    Qed.

    Lemma comProjRightRVLiftUnOpRV {A B} (f : A -> B) (rv : RV A) :
      projRightRV (liftUnOpRV f rv) = f (projRightRV rv).
    Proof.
      destruct rv; auto.
    Qed.

    Lemma liftUnOpRV_inj {A B} (f : A -> B) rv1 rv2 (f_inj : ∀ a b, f a = f b -> a = b) :
      liftUnOpRV f rv1 = liftUnOpRV f rv2 ->
      rv1 = rv2.
    Proof.
      destruct rv1, rv2; cbn in *; intro H; try discriminate;
        inversion H.
      - apply f_inj in H1. now subst.
      - apply f_inj in H1, H2. now subst.
    Qed.

    
    Definition liftBinOpRV {A B C} (f : A -> B -> C) (rv1 : RV A) (rv2 : RV B) : RV C :=
      match (rv1 , rv2) with
      | (SyncVal v1 , SyncVal v2) => SyncVal (f v1 v2)
      | (_ , _) => NonSyncVal (f (projLeftRV rv1) (projLeftRV rv2)) (f (projRightRV rv1) (projRightRV rv2))
      end.
    Global Arguments liftBinOpRV {A B C} f !rv1 !rv2.

    Instance proper_liftBinOpRV {A B C : Type} : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@liftBinOpRV A B C).
    Proof.
      intros f g Rfg rv1 rv1' eq1 rv2 rv2' eq2.
      destruct rv1, rv2, rv1', rv2'; cbn; inversion eq1; inversion eq2;
        rewrite Rfg; auto.
    Qed.

    Lemma comProjLeftRVLiftBinOpRV {A B C} (f : A -> B -> C) (rv1 : RV A) (rv2 : RV B) :
      projLeftRV (liftBinOpRV f rv1 rv2) = f (projLeftRV rv1) (projLeftRV rv2).
    Proof.
      destruct rv1, rv2; auto.
    Qed.

    Lemma comProjRightRVLiftBinOpRV {A B C} (f : A -> B -> C) (rv1 : RV A) (rv2 : RV B) :
      projRightRV (liftBinOpRV f rv1 rv2) = f (projRightRV rv1) (projRightRV rv2).
    Proof.
      destruct rv1, rv2; auto.
    Qed.

    Definition rv_eq {A} (rv1 rv2 : RV A) : Prop :=
      let rvp := liftBinOpRV (fun x y => x = y) rv1 rv2 in
      projLeftRV rvp /\ projRightRV rvp.
    Global Arguments rv_eq {A} !rv1 !rv2.

    Lemma rv_eq_to_eq {A} (rv1 rv2 : RV A) :
      rv_eq rv1 rv2 <-> (projLeftRV rv1 = projLeftRV rv2 /\ projRightRV rv1 = projRightRV rv2).
    Proof.
      unfold rv_eq.
      now rewrite comProjLeftRVLiftBinOpRV, comProjRightRVLiftBinOpRV.
    Qed.

    Ltac remove_rv_eq :=
      repeat match goal with
        | |- context[rv_eq] => try rewrite rv_eq_to_eq
        | H : context[rv_eq] |- _ => try rewrite rv_eq_to_eq
        end.

    Tactic Notation "ty.remove_rv_eq" := remove_rv_eq.

    Definition liftUnOp {σ1 σ2} (f : Val σ1 -> Val σ2) (rv : RelVal σ1) : RelVal σ2 :=
      liftUnOpRV f rv.
    Global Arguments liftUnOp {σ1 σ2} f !rv.

    Instance proper_liftUnOp {σ1 σ2 : Ty} : Proper ((pointwise_relation _ eq) ==> eq ==> eq) (@liftUnOp σ1 σ2).
    Proof.
      intros f g Rfg rv rv' eq.
      destruct rv, rv'; cbn; inversion eq;
        rewrite Rfg; auto.
    Qed.

    Lemma comProjLeftLiftUnOp {σ1 σ2} (f : Val σ1 -> Val σ2) (rv : RelVal σ1) :
      projLeft (liftUnOp f rv) = f (projLeft rv).
    Proof.
      destruct rv; auto.
    Qed.

    Lemma comProjRightLiftUnOp {σ1 σ2} (f : Val σ1 -> Val σ2) (rv : RelVal σ1) :
      projRight (liftUnOp f rv) = f (projRight rv).
    Proof.
      destruct rv; auto.
    Qed.

    Lemma liftUnOp_inj {σ1 σ2} (f : Val σ1 -> Val σ2) (rv1 rv2 : RelVal σ1)  (f_inj : ∀ a b, f a = f b -> a = b) :
      liftUnOp f rv1 = liftUnOp f rv2 ->
      rv1 = rv2.
    Proof.
      destruct rv1, rv2; cbn in *; intro H; try discriminate;
        inversion H.
      - apply f_inj in H1. now subst.
      - apply f_inj in H1, H2. now subst.
    Qed.

    Definition liftBinOp {σ1 σ2 σ3} (f : Val σ1 -> Val σ2 -> Val σ3) (rv1 : RelVal σ1) (rv2 : RelVal σ2) : RelVal σ3 :=
      liftBinOpRV f rv1 rv2.
    Global Arguments liftBinOp {σ1 σ2 σ3} f !rv1 !rv2.

    Instance proper_liftBinOp {σ1 σ2 σ3 : Ty} : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@liftBinOp σ1 σ2 σ3).
    Proof.
      intros f g Rfg rv1 rv1' eq1 rv2 rv2' eq2.
      destruct rv1, rv2, rv1', rv2'; cbn; inversion eq1; inversion eq2;
      rewrite Rfg; auto.
    Qed.

    Lemma comProjLeftLiftBinOp {σ1 σ2 σ3} (f : Val σ1 -> Val σ2 -> Val σ3) (rv1 : RelVal σ1) (rv2 : RelVal σ2) :
      projLeft (liftBinOp f rv1 rv2) = f (projLeft rv1) (projLeft rv2).
    Proof.
      destruct rv1, rv2; auto.
    Qed.

    Lemma comProjRightLiftBinOp {σ1 σ2 σ3} (f : Val σ1 -> Val σ2 -> Val σ3) (rv1 : RelVal σ1) (rv2 : RelVal σ2) :
      projRight (liftBinOp f rv1 rv2) = f (projRight rv1) (projRight rv2).
    Proof.
      destruct rv1, rv2; auto.
    Qed.

    Lemma liftUnOpRVUnOpRVToUnOpRV {A C D} (f1 : C -> D) (f2 : A -> C) (rv : RV A) :
      liftUnOpRV f1 (liftUnOpRV f2 rv) = liftUnOpRV (fun a => f1 (f2 a)) rv.
    Proof.
      destruct rv; auto.
    Qed.

    Lemma liftUnOpRVUnOpToUnOp {σ1 σ2 C} (f1 : Val σ2 -> C) (f2 : Val σ1 -> Val σ2) (rv : RelVal σ1) :
      liftUnOpRV f1 (liftUnOp f2 rv) = liftUnOpRV (fun a => f1 (f2 a)) rv.
    Proof.
      destruct rv; auto.
    Qed.

    Lemma liftUnOpUnOpToUnOp {σ1 σ2 σ3} (f1 : Val σ2 -> Val σ3) (f2 : Val σ1 -> Val σ2) (rv : RelVal σ1) :
      liftUnOp f1 (liftUnOp f2 rv) = liftUnOp (fun a => f1 (f2 a)) rv.
    Proof.
      destruct rv; auto.
    Qed.

    Lemma liftUnOpRVBinOpRVToBinOpRV {A B C D} (fUn : C -> D) (fBin : A -> B -> C) (rv1 : RV A) (rv2 : RV B) :
      liftUnOpRV fUn (liftBinOpRV fBin rv1 rv2) = liftBinOpRV (fun a b => fUn (fBin a b)) rv1 rv2.
    Proof.
      destruct rv1, rv2; auto.
    Qed.

    Lemma liftUnOpBinOpToBinOp {σ1 σ2 σ3 σ4} (fUn : Val σ3 -> Val σ4) (fBin : Val σ1 -> Val σ2 -> Val σ3) (rv1 : RelVal σ1) (rv2 : RelVal σ2) :
    liftUnOp fUn (liftBinOp fBin rv1 rv2) = liftBinOp (fun a b => fUn (fBin a b)) rv1 rv2.
    Proof.
      destruct rv1, rv2; auto.
    Qed.

    Ltac removeLiftBinOp :=
    repeat match goal with
           | |- context[liftBinOp] =>
               repeat rewrite comProjLeftLiftBinOp, comProjRightLiftBinOp
           | H : context[liftBinOp] |- _ =>
               repeat rewrite comProjLeftLiftBinOp, comProjRightLiftBinOp in H
           | |- context[liftBinOpRV] =>
               repeat rewrite comProjLeftRVLiftBinOpRV, comProjRightRVLiftBinOpRV
           | H : context[liftBinOpRV] |- _ =>
               repeat rewrite comProjLeftRVLiftBinOpRV, comProjRightRVLiftBinOpRV in H
           | _ => idtac
           end.

    (* Tactic Notation "ty.removeLiftBinOp" := removeLiftBinOp. *)

    Definition valToRelVal {σ} : Val σ -> RelVal σ :=
      SyncVal.

    Lemma rv_eq_valToRelVal1 {σ} (v : Val σ) (rv : RelVal σ) :
      rv_eq (valToRelVal v) rv <-> v = projLeft rv /\ v = projRight rv.
    Proof.
      unfold rv_eq. unfold valToRelVal.
      removeLiftBinOp.
      auto.
    Qed.

    Lemma rv_eq_valToRelVal2 {σ} (rv : RelVal σ) (v : Val σ) :
      rv_eq rv (valToRelVal v) <-> projLeft rv = v /\ projRight rv = v.
    Proof.
      unfold rv_eq. unfold valToRelVal.
      removeLiftBinOp.
      auto.
    Qed.

    Lemma liftUnOpValToRelVal {σ1 σ2} (f : Val σ1 -> Val σ2) (v : Val σ1) :
      liftUnOp f (valToRelVal v) = valToRelVal (f v).
    Proof.
      cbn. auto.
    Qed.

    Lemma liftBinOpValToRelVal1 {σ1 σ2 σ3} (f : Val σ1 -> Val σ2 -> Val σ3) (v : Val σ1) (rv : RelVal σ2) :
      liftBinOp f (valToRelVal v) rv = liftUnOp (f v) rv.
    Proof.
      destruct rv; auto.
    Qed.

    Lemma liftBinOpValToRelVal2 {σ1 σ2 σ3} (f : Val σ1 -> Val σ2 -> Val σ3) (rv : RelVal σ1) (v : Val σ2) :
      liftBinOp f rv (valToRelVal v) = liftUnOp (fun v' => f v' v) rv.
    Proof.
      destruct rv; auto.
    Qed.

    Ltac removeValToRelVal :=
      repeat match goal with
        | |- context[valToRelVal] => try rewrite rv_eq_valToRelVal1, rv_eq_valToRelVal2, liftUnOpValToRelVal, liftBinOpValToRelVal1, liftBinOpValToRelVal2
        | H : context[valToRelVal] |- _ => try rewrite rv_eq_valToRelVal1, rv_eq_valToRelVal2, liftUnOpValToRelVal, liftBinOpValToRelVal1, liftBinOpValToRelVal2 in H
        end.

    Definition syncNamedEnv {N} {Γ : NCtx N Ty} : NamedEnv Val Γ -> NamedEnv RelVal Γ :=
      env.map (fun b => SyncVal).

    Definition nonsyncNamedEnv {N} {Γ : NCtx N Ty} : NamedEnv Val Γ -> NamedEnv Val Γ -> NamedEnv RelVal Γ :=
      env.zipWith (fun b => NonSyncVal).

    Fixpoint unliftNamedEnv {N} {Γ : NCtx N Ty} (vs : NamedEnv RelVal Γ) : RV (NamedEnv Val Γ) :=
      match vs with
      | []%env => SyncVal []%env
      | env.snoc vs k v =>
          match (v , unliftNamedEnv vs) with
          | (SyncVal v' , SyncVal vs') => SyncVal (vs' .[ k ↦ v'])
          | (_ , SyncVal vs') => NonSyncVal (vs' .[ k ↦ projLeft v ]) (vs' .[ k ↦ projRight v ])
          | (_ , NonSyncVal vs1' vs2') => NonSyncVal (vs1' .[ k ↦ projLeft v ]) (vs2' .[ k ↦ projRight v ])
          end
      end.

    Lemma unliftSyncNamedEnvIsSync {N} {Γ : NCtx N Ty} (nenv : NamedEnv Val Γ) :
      unliftNamedEnv (syncNamedEnv nenv) = SyncVal nenv.
    Proof.
      induction nenv.
      - auto.
      - cbn. change (env.map (λ b0 : N∷Ty, SyncVal) nenv) with (syncNamedEnv nenv).
        rewrite IHnenv. auto.
    Qed.

    Fixpoint listOfRVToRVOfList {A} (rv_list : (Datatypes.list (RV A))) : RV (Datatypes.list A) :=
      match rv_list with
      | nil => SyncVal nil
      | (x :: l)%list => liftBinOpRV cons x (listOfRVToRVOfList l)
      end.

    (* Definition listOfRelValToRelValOfList {A} (rv_list : (Datatypes.list (RelVal A))) : RelVal (list A) := *)
    (*   listOfRVToRVOfList rv_list. *)

    Definition RVOfPairToPairOfRV {σ1 σ2} (rv : RV (σ1 * σ2)) : RV σ1 * RV σ2 :=
      match rv with
      | SyncVal (a , b) => (SyncVal a, SyncVal b)
      | NonSyncVal (a1, b1) (a2, b2) => (NonSyncVal a1 a2, NonSyncVal b1 b2)
      end.

    Definition pairOfRVToRVOfPair {σ1 σ2} (rv_pair : RV σ1 * RV σ2) : RV (σ1 * σ2) :=
      match rv_pair with
      | (SyncVal v1 , SyncVal v2) => SyncVal (v1, v2)
      | (rv1, rv2) => NonSyncVal (projLeftRV rv1, projLeftRV rv2) (projRightRV rv1, projRightRV rv2)
      end.

    Definition RelValOfPairToPairOfRelVal {σ1 σ2} (rv : RelVal (prod σ1 σ2)) : RelVal σ1 * RelVal σ2 :=
      RVOfPairToPairOfRV rv.

    Definition pairOfRelValToRelValOfPair {σ1 σ2} (rv_pair : RelVal σ1 * RelVal σ2) : RelVal (prod σ1 σ2) :=
      pairOfRVToRVOfPair rv_pair.

    Definition isSyncValRV {σ} (rv : RV σ) : Datatypes.bool :=
      match rv with
      | SyncVal _ => true
      | NonSyncVal _ _ => false
      end.

    Definition isSyncVal {σ} : RelVal σ -> Datatypes.bool :=
      isSyncValRV.

    Definition isSyncValPropRV {σ} (v : RV σ) : Prop :=
      match v with
      | SyncVal _ => True
      | NonSyncVal _ _ => False
      end.

    Definition isSyncValProp {σ} : RelVal σ -> Prop :=
      isSyncValPropRV.
    

    Fixpoint vecOfRVToRVOfVec {n} (rv_vec : Vector.t (RV (Val bool)) n) : RV (Val (ty.bvec n)) :=
      match rv_vec with
      | Vector.nil => SyncVal bv.nil
      | Vector.cons x l => liftBinOpRV (A := Val bool) (B := Val (bvec _)) (C := Val (bvec _)) (bv.cons (n := _)) x (vecOfRVToRVOfVec l)
      end.

    Fixpoint vecOfRelValToRelValOfVec {n} (rv_vec : Vector.t (RelVal bool) n) : RelVal (ty.bvec n) :=
      vecOfRVToRVOfVec rv_vec
      .

  End WithTypeDenote.

  Class TypeDefKit {TDC : TypeDeclKit} (TDN : TypeDenoteKit TDC) : Type :=
    { (* enum_eqdec   : EqDec enumi; *)
      union_eqdec  : EqDec unioni;
      (* record_eqdec : EqDec recordi; *)

      (* enumt_eqdec E  : EqDec (enumt E); *)
      (* enumt_finite E : finite.Finite (enumt E); *)

      uniont_eqdec U  : EqDec (uniont U);
      (* Names of union data constructors. *)
      unionk          : unioni -> Set;
      unionk_eqdec U  : EqDec (unionk U);
      unionk_finite U : finite.Finite (unionk U);
      unionk_ty U     : unionk U -> Ty;

      (* recordt_eqdec R  : EqDec (recordt R); *)
      (* (* Record field names. *) *)
      (* recordf          : Set; *)
      (* (* Record field types. *) *)
      (* recordf_ty       : recordi -> NCtx recordf Ty; *)

      (* Union types. *)
      (* Union data constructor field type *)
      unionv_fold U   : { K : unionk U & Val (unionk_ty U K) } -> uniont U;
      unionv_unfold U : uniont U -> { K : unionk U & Val (unionk_ty U K) };

      (* (* Record types. *) *)
      (* recordv_fold R   : NamedEnv Val (recordf_ty R) -> recordt R; *)
      (* recordv_unfold R : recordt R -> NamedEnv Val (recordf_ty R); *)

      unionv_fold_unfold U K : unionv_fold U (unionv_unfold U K) = K;
      unionv_unfold_fold U K : unionv_unfold U (unionv_fold U K) = K;

      (* recordv_fold_unfold R v : recordv_fold R (recordv_unfold R v) = v; *)
      (* recordv_unfold_fold R v : recordv_unfold R (recordv_fold R v) = v; *)
    }.

  Definition unionv_fold_rel {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} {TDK : TypeDefKit TDN} U (existThingy : { K : unionk U & RelVal (unionk_ty U K) }) : RelVal (ty.union U) :=
    ty.liftUnOp (σ2 := ty.union _) (fun v => @unionv_fold TDC TDN _ U (existT (projT1 existThingy) v)) (projT2 existThingy).

  Definition unionv_unfold_rel {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} {TDK : TypeDefKit TDN} U (rv : RelVal (union U)) : RV { K : unionk U & Val (unionk_ty U K) } :=
    ty.liftUnOpRV (unionv_unfold U) rv.

  Definition unionv_unfold_fold_rel {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} {TDK : TypeDefKit TDN} U K a :
    unionv_unfold_rel U (unionv_fold_rel U (existT K a)) = ty.liftUnOpRV (λ a : Val (unionk_ty U K), existT K a) a.
  Proof.
    unfold ty.unionv_unfold_rel.
    unfold unionv_fold_rel.
    setoid_rewrite (ty.liftUnOpRVUnOpToUnOp (σ2 := ty.union _)).
    now setoid_rewrite unionv_unfold_fold.    
  Qed.


  (* Coq 8.16 will start generating coercions for [:>] in Class definitions. Not
     sure what the implications are and if we want that. For now, manually
     declare the necessary fields as superclass instances. *)
  (* #[export] Existing Instance enum_eqdec. *)
  #[export] Existing Instance union_eqdec.
  (* #[export] Existing Instance record_eqdec. *)
  (* #[export] Existing Instance enumt_eqdec. *)
  (* #[export] Existing Instance enumt_finite. *)
  #[export] Existing Instance uniont_eqdec.
  #[export] Existing Instance unionk_eqdec.
  #[export] Existing Instance unionk_finite.
  (* #[export] Existing Instance recordt_eqdec. *)

  Section WithTypeDef.

    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.
    Search Ty NoConfusionPackage.
    
    #[export] Instance Ty_eq_dec : EqDec Ty :=
      let nCinv := @noConfusion_inv _ (NoConfusionPackage_Ty _) in
      fix ty_eqdec (σ τ : Ty) {struct σ} : dec_eq σ τ :=
        match σ , τ with
        | int        , int        => left eq_refl
        | bool       , bool       => left eq_refl
        | string     , string     => left eq_refl
        (* | list σ     , list τ     => f_equal_dec list (nCinv _ _) (ty_eqdec σ τ) *)
        | prod σ1 σ2 , prod τ1 τ2 => f_equal2_dec prod (nCinv _ _) (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2)
        (* | sum σ1 σ2  , sum τ1 τ2  => f_equal2_dec sum (nCinv _ _) (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2) *)
        | unit       , unit       => left eq_refl
        (* | enum E1    , enum E2    => f_equal_dec enum (nCinv _ _) (eq_dec E1 E2) *)
        | bvec n1    , bvec n2    => f_equal_dec bvec (nCinv _ _) (eq_dec n1 n2)
        (* | tuple σs   , tuple τs   => f_equal_dec *)
        (*                                tuple (nCinv _ _) *)
        (*                                (eq_dec (EqDec := ctx.eq_dec_ctx ty_eqdec) σs τs) *)
        | union U1   , union U2   => f_equal_dec union (nCinv _ _) (eq_dec U1 U2)
        (* | record R1  , record R2  => f_equal_dec record (nCinv _ _) (eq_dec R1 R2) *)
        | _          , _          => right (nCinv _ _)
        end.

    #[export] Instance Val_eq_dec : forall σ, EqDec (Val σ) :=
      fix eqd σ :=
        match σ with
        | int      => eq_dec (A := Z)
        | bool     => eq_dec (A := Datatypes.bool)
        | string   => eq_dec (A := String.string)
        (* | list σ   => eq_dec (A := Datatypes.list (Val σ)) *)
        | prod σ τ => eq_dec (A := Datatypes.prod (Val σ) (Val τ))
        (* | sum σ τ  => eq_dec (A := Datatypes.sum (Val σ) (Val τ)) *)
        | unit     => eq_dec (A := Datatypes.unit)
        (* | enum E   => eq_dec (A := enumt E) *)
        | bvec n   => eq_dec (A := bv n)
        (* | tuple σs => ctx.Ctx_rect *)
        (*                 (fun τs => EqDec (EnvRec Val τs)) *)
        (*                 (eq_dec (A := Datatypes.unit)) *)
        (*                 (fun τs IHτs τ => *)
        (*                    @eq_dec *)
        (*                      (Datatypes.prod (EnvRec Val τs) (Val τ)) *)
        (*                      (prod_eqdec IHτs (eqd τ))) *)
        (*                 σs *)
        | union U  => eq_dec (A := uniont U)
        (* | record R => eq_dec (A := recordt R) *)
        end.

    #[export] Instance RV_eq_dec : forall A, EqDec A -> EqDec (RV A).
    Proof.
      intros.
      intros x y.
      destruct x; destruct y.
      - destruct (X a a0). left. subst. auto.
        right. intros F. inversion F. subst. contradiction.
      - right. intros. congruence.
      - right. intros. congruence.
      - destruct (X a a1); destruct (X a0 a2); try (now subst; left; auto);
        right; intros F; inversion F; subst; contradiction.
    Qed.

      #[export] Instance RelVal_eq_dec : forall σ, EqDec (RelVal σ) :=
      fun σ => RV_eq_dec _ (Val_eq_dec _).

    Lemma unionv_fold_inj {U} (v1 v2 : {K : unionk U & Val (unionk_ty U K)}) :
      unionv_fold U v1 = unionv_fold U v2 <-> v1 = v2.
    Proof.
      split; intro H; [|now f_equal].
      apply (f_equal (unionv_unfold U)) in H.
      now rewrite !unionv_unfold_fold in H.
    Qed.

    Set Equations With UIP.
    Lemma unionv_fold_rel_inj {U} {K : unionk U} (v1 v2 : RelVal (unionk_ty U K)) :
      unionv_fold_rel U (existT K v1) = unionv_fold_rel U (existT K v2) <-> v1 = v2.
    Proof.
      split; intro H; [|now subst].
      apply (f_equal (unionv_unfold_rel U)) in H.
      setoid_rewrite unionv_unfold_fold_rel in H.
      apply liftUnOpRV_inj in H; auto.
      intros a b eq. now dependent elimination eq.
    Qed.
    Unset Equations With UIP.

    Lemma unionv_unfold_inj {U} (v1 v2 : Val (union U)) :
      unionv_unfold U v1 = unionv_unfold U v2 <-> v1 = v2.
    Proof.
      split; intro H; [|now f_equal].
      apply (f_equal (unionv_fold U)) in H.
      now rewrite !unionv_fold_unfold in H.
    Qed.

    (* Lemma recordv_fold_inj {R} (v1 v2 : NamedEnv Val (recordf_ty R)) : *)
    (*   recordv_fold R v1 = recordv_fold R v2 <-> v1 = v2. *)
    (* Proof. *)
    (*   split; intro H; [|now f_equal]. *)
    (*   apply (f_equal (recordv_unfold R)) in H. *)
    (*   now rewrite !recordv_unfold_fold in H. *)
    (* Qed. *)

    (* Lemma recordv_unfold_inj {R} (v1 v2 : Val (ty.record R)) : *)
    (*   recordv_unfold R v1 = recordv_unfold R v2 <-> v1 = v2. *)
    (* Proof. *)
    (*   split; intro H; [|now f_equal]. *)
    (*   apply (f_equal (recordv_fold R)) in H. *)
    (*   now rewrite ?recordv_fold_unfold in H. *)
    (* Qed. *)

    Lemma K (σ : Ty) (p : σ = σ) : p = eq_refl.
    Proof. apply uip. Qed.

  End WithTypeDef.
  #[global] Arguments int {TK}.
  #[global] Arguments bool {TK}.
  #[global] Arguments string {TK}.
  (* #[global] Arguments list {TK} σ. *)
  #[global] Arguments prod {TK} σ τ.
  (* #[global] Arguments sum {TK} σ τ. *)
  #[global] Arguments unit {TK}.
  (* #[global] Arguments enum {TK} E. *)
  #[global] Arguments bvec {TK} n%_nat_scope.
  (* #[global] Arguments tuple {TK} σs%_ctx_scope. *)
  #[global] Arguments union {TK} U.
  (* #[global] Argumentsn record {TK} R. *)

End ty.
Export ty
  ( TypeDeclKit,
    (* enumt, *)
    uniont,
    (* recordt, *)

    TypeDenoteKit,
    Ty, Val, RelVal,

    RV, SyncVal, NonSyncVal,

    TypeDefKit, (* enum_eqdec, enumt_eqdec, enumt_finite, *)
    (* enumi, *)
    unioni,
    (* recordi, *)
    union_eqdec, uniont_eqdec, unionk, unionk_eqdec, unionk_finite, unionk_ty,
    unionv_fold, unionv_unfold,
    (* record_eqdec, recordt_eqdec, recordf, *)
    (* recordf_ty, recordv_fold, recordv_unfold, *)

    unionv_fold_unfold, unionv_unfold_fold,
    unionv_fold_inj, unionv_unfold_inj(* , *)
    (* recordv_fold_unfold, recordv_unfold_fold, *)
    (* recordv_fold_inj, recordv_unfold_inj *)
  ).
Export (hints) ty.

Module Type Types.

  #[export] Declare Instance typedeclkit   : TypeDeclKit.
  #[export] Declare Instance typedenotekit : TypeDenoteKit typedeclkit.
  #[export] Declare Instance typedefkit    : TypeDefKit typedenotekit.
  #[export] Declare Instance varkit        : VarKit.

End Types.

#[local] Instance DefaultTypeDeclKit : TypeDeclKit :=
  {| (* enumi := Empty_set; *)
     unioni := Empty_set;
     (* recordi := Empty_set; *)
  |}.

#[local] Instance DefaultTypeDenoteKit : TypeDenoteKit DefaultTypeDeclKit :=
  {| (* enumt _ := Empty_set; *)
     uniont _ := Empty_set;
     (* recordt _ := Empty_set; *)
  |}.

#[local,refine] Instance DefaultTypeDefKit : TypeDefKit DefaultTypeDenoteKit :=
  {| unionk _            := Empty_set;
     unionk_ty _ _       := ty.unit;
     unionv_fold         := Empty_set_rec _;
     unionv_unfold       := Empty_set_rec _;
     (* recordf             := Empty_set; *)
     (* recordf_ty          := Empty_set_rec _; *)
     (* recordv_fold        := Empty_set_rec _; *)
     (* recordv_unfold      := Empty_set_rec _; *)
  |}.
Proof. all: abstract (intros []). Defined.
