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
     ZArith.BinInt
     List
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     Program.Basics
.
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
      (* unioni   : Set;           (* Names of union type constructors. *) *)
      (* recordi  : Set;           (* Names of record type constructors. *) *)
    }.

  Section WithTypeDecl.

    Local Unset Elimination Schemes.
    Local Set Transparent Obligations.

    Inductive Ty {TK : TypeDeclKit} : Set :=
    | int
    | bool
    | string
    | list (σ : Ty)
    | prod (σ τ : Ty)
    (* | sum  (σ τ : Ty) *)
    | unit
(*    | enum (E : enumi) *)
    | bvec (n : nat)
(*    | tuple (σs : Ctx Ty)
    | union (U : unioni)
    | record (R : recordi) *)
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
      Hypothesis (P_list   : forall σ, P σ -> P (list σ)).
      Hypothesis (P_prod   : forall σ τ, P σ -> P τ -> P (prod σ τ)).
      (* Hypothesis (P_sum    : forall σ τ, P σ -> P τ -> P (sum σ τ)). *)
      Hypothesis (P_unit   : P unit).
(*      Hypothesis (P_enum   : forall E, P (enum E)). *)
      Hypothesis (P_bvec   : forall n, P (bvec n)).
(*      Hypothesis (P_tuple  : forall σs (IH : ctx.All P σs), P (tuple σs)).
      Hypothesis (P_union  : forall U, P (union U)).
      Hypothesis (P_record : forall R, P (record R)). *)

      Fixpoint Ty_rect (σ : Ty) : P σ :=
        match σ with
        | int      => ltac:(apply P_int)
        | bool     => ltac:(apply P_bool)
        | string   => ltac:(apply P_string)
        | list σ   => ltac:(apply P_list; auto)
        | prod σ τ => ltac:(apply P_prod; auto)
        (* | sum σ τ  => ltac:(apply P_sum; auto) *)
        | unit     => ltac:(apply P_unit; auto)
(*        | enum E   => ltac:(apply P_enum; auto) *)
        | bvec n   => ltac:(apply P_bvec; auto)
(*        | tuple σs => ltac:(apply P_tuple, ctx.all_intro, Ty_rect)
        | union U  => ltac:(apply P_union; auto)
        | record R => ltac:(apply P_record; auto) *)
        end.

    End Ty_rect.

    Definition Ty_rec (P : Ty -> Set) := Ty_rect P.
    Definition Ty_ind (P : Ty -> Prop) := Ty_rect P.

  End WithTypeDecl.

  Class TypeDenoteKit (TDC : TypeDeclKit) : Type :=
    { (* Mapping enum type constructor names to enum types *)
(*      enumt   : enumi -> Set;
      (* Mapping union type constructor names to union types *)
      uniont  : unioni -> Set;
      (* Mapping record type constructor names to record types *)
      recordt : recordi -> Set; *)
    }.

  Section WithTypeDenote.

    Fixpoint Val {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} (σ : Ty) : Set :=
      match σ with
      | int => Z
      | bool => Datatypes.bool
      | string => String.string
      | list σ' => Datatypes.list (Val σ')
      | prod σ1 σ2 => Val σ1 * Val σ2
      (* | sum σ1 σ2 => Val σ1 + Val σ2 *)
      | unit => Datatypes.unit
      | bvec n => bv n
      end%type.

    (* Inductive RelVal {TDC : TypeDeclKit} {TDN : TypeDenoteKit TDC} (τ : Ty) : Set := *)
    (* | SyncVal : Val τ -> RelVal τ *)
    (* | NonSyncVal : Val τ -> Val τ -> RelVal τ *)
    (* . *)

    Set Universe Polymorphism.
    Inductive RV (A : Type) : Type :=
    | SyncVal : A -> RV A
    | NonSyncVal : A -> A -> RV A
    .

    Global Arguments SyncVal {A}.
    Global Arguments NonSyncVal {A}.

    Definition projLeftRV {A} (rv : RV A) : A :=
      match rv with
      | SyncVal v => v
      | NonSyncVal vl _ => vl
      end.

    Definition projRightRV {A} (rv : RV A) : A :=
      match rv with
      | SyncVal v => v
      | NonSyncVal _ vr => vr
      end.

    Definition liftUnOpRV {A B} (f : A -> B) (rv : RV A) : RV B :=
      match rv with
      | (SyncVal v) => SyncVal (f v)
      | (NonSyncVal vl vr) => NonSyncVal (f vl) (f vr)
      end.

    Definition liftBinOpRV {A B C} (f : A -> B -> C) (rv1 : RV A) (rv2 : RV B) : RV C :=
      match (rv1 , rv2) with
      | (SyncVal v1 , SyncVal v2) => SyncVal (f v1 v2)
      | (_ , _) => NonSyncVal (f (projLeftRV rv1) (projLeftRV rv2)) (f (projRightRV rv1) (projRightRV rv2))
      end.
    
    Definition rv_equiv (rv1 : RV Prop) (rv2 : RV Prop) : RV Prop :=
      match rv1, rv2 with
      | SyncVal p, SyncVal q => SyncVal (p <-> q)
      | SyncVal p, NonSyncVal q1 q2 => NonSyncVal (p <-> q1) (p <-> q2)
      | NonSyncVal p1 p2, SyncVal q => NonSyncVal (p1 <-> q) (p2 <-> q)
      | NonSyncVal p1 p2, NonSyncVal q1 q2 => NonSyncVal (p1 <-> q1) (p2 <-> q2)
      end.

    Definition rv_impl (rv1 : RV Prop) (rv2 : RV Prop) : RV Prop :=
      match rv1, rv2 with
      | SyncVal p1, SyncVal p2 => SyncVal (p1 -> p2)
      | SyncVal p, NonSyncVal q1 q2 => NonSyncVal (p -> q1) (p -> q2)
      | NonSyncVal p1 p2, SyncVal q => NonSyncVal (p1 -> q) (p2 -> q)
      | NonSyncVal p1 p2, NonSyncVal q1 q2 => NonSyncVal (p1 -> q1) (p2 -> q2)
      end.

    Definition rv_bientails (rv1 : RV Prop) (rv2 : RV Prop) : Prop :=
      match rv1, rv2 with
      | SyncVal p, SyncVal q => p <-> q
      | SyncVal p, NonSyncVal q1 q2 => (p <-> q1) /\ (p <-> q2)
      | NonSyncVal p1 p2, SyncVal q => (p1 <-> q) /\ (p2 <-> q)
      | NonSyncVal p1 p2, NonSyncVal q1 q2 => (p1 <-> q1) /\ (p2 <-> q2)
      end.

    Definition rv_entails (rv1 : RV Prop) (rv2 : RV Prop) : Prop :=
      match rv1, rv2 with
      | SyncVal p, SyncVal q => p -> q
      | SyncVal p, NonSyncVal q1 q2 => (p -> q1) /\ (p -> q2)
      | NonSyncVal p1 p2, SyncVal q => (p1 -> q) /\ (p2 -> q)
      | NonSyncVal p1 p2, NonSyncVal q1 q2 => (p1 -> q1) /\ (p2 -> q2)
      end.

    (* Definition rv_equiv_is_iff (rv1 : RV Prop) (rv2 : RV Prop) : rv_equiv rv1 rv2 <-> (rv_impl rv1 rv2 /\ rv_impl rv2 rv1). *)
    (* Proof. *)
    (*   destruct rv1; destruct rv2; cbn; tauto. *)
    (* Qed. *)

    Definition rv_neg (rv : RV Prop) : RV Prop :=
      match rv with
      | SyncVal p1 => SyncVal (~ p1)
      | NonSyncVal p1 p2 => NonSyncVal (~ p1) (~ p2)
      end.

    Definition rv_entails_refl : Reflexive (rv_entails).
    Proof. unfold Reflexive, rv_entails. intros.
           destruct x; cbn; auto.
    Qed.

    Definition rv_entails_trans : Transitive (rv_entails).
    Proof.
      unfold Transitive, rv_entails.
      intros.
      destruct x; destruct y; destruct z; cbn in *; eauto; try contradiction; try tauto.
    Qed.

    #[export] Instance preorder_entails : PreOrder (rv_entails).
    Proof. split; auto using rv_entails_refl, rv_entails_trans. Qed.

    #[export] Instance equivalence_bientails : Equivalence (rv_bientails).
    Proof.
      unfold rv_bientails. constructor.
      - unfold Reflexive. intros. destruct x; cbn; auto.
      - unfold Symmetric. intros. destruct x; destruct y; cbn in *; tauto.
      - unfold Transitive. intros.
        destruct x; destruct y; destruct z; cbn in *; eauto; try contradiction; tauto.
    Qed.

    #[export] Instance subrelation_bientails_entails :
      subrelation (rv_bientails) (rv_entails).
    Proof. intros x y xy.
           destruct x; destruct y; cbn in *; try apply xy;
             tauto.
    Qed.

    #[export,program] Instance proper_rv_bientails (rv1 rv2 : RV Prop) :
      Proper (rv_bientails ==> rv_bientails ==> iff) (rv_bientails).
    Next Obligation.
      intros rv1 rv2.
      intros p1 p2 Rp q1 q2 Rq. 
      unfold rv_bientails in *.
      destruct p1; destruct p2; destruct q1; destruct q2; cbn; tauto.
    Qed.

    #[export,program] Instance proper_rv_equiv (rv1 rv2 : RV Prop) :
       Proper (rv_bientails ==> rv_bientails ==> rv_bientails) (rv_equiv).
    Next Obligation.
      intros rv1 rv2.
      intros p1 p2 Rp q1 q2 Rq. 
      unfold rv_bientails in *. unfold rv_equiv.
      destruct p1; destruct p2; destruct q1; destruct q2; cbn; tauto.
    Qed.

    #[export,program] Instance proper_rv_entails (rv1 rv2 : RV Prop) :
      Proper (rv_bientails ==> rv_bientails ==> iff) (rv_entails).
    Next Obligation.
      intros rv1 rv2.
      intros p1 p2 Rp q1 q2 Rq. 
      unfold rv_bientails in *.
      destruct p1; destruct p2; destruct q1; destruct q2; cbn; tauto.
    Qed.

    #[export,program] Instance proper_rv_impl (rv1 rv2 : RV Prop) :
      Proper (rv_bientails ==> rv_bientails ==> rv_bientails) (rv_impl).
    Next Obligation.
      intros rv1 rv2.
      intros p1 p2 Rp q1 q2 Rq. 
      unfold rv_bientails in *.
      destruct p1; destruct p2; destruct q1; destruct q2; cbn; tauto.
    Qed.

    #[export,program] Instance proper_rv_impl_mono' (rv1 rv2 : RV Prop) :
      Proper (rv_entails --> rv_entails ==> rv_entails) (rv_impl).
    Next Obligation.
      intros rv1 rv2.
      intros p1 p2 Rp q1 q2 Rq. 
      unfold rv_entails in *. cbn in *.
      destruct p1; destruct p2; destruct q1; destruct q2; cbn; tauto.
    Qed.

    #[export,program] Instance proper_rv_impl_flip_mono' (rv1 rv2 : RV Prop) :
      Proper (rv_entails ==> flip(rv_entails) ==> flip(rv_entails)) (rv_impl).
    Next Obligation.
      intros rv1 rv2.
      intros p1 p2 Rp q1 q2 Rq. 
      unfold rv_entails in *. cbn in *.
      destruct p1; destruct p2; destruct q1; destruct q2; cbn; tauto.
    Qed.


    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    
    Fixpoint RelVal (σ : Ty) : Set :=
      match σ with
      | int => RV (Val int)
      | bool => RV (Val bool)
      | string => RV (Val string)
      | list σ' => Datatypes.list (RelVal σ')
      | prod σ1 σ2 => RelVal σ1 * RelVal σ2
      (* | sum σ1 σ2 => RV (RelVal σ1 + RelVal σ2) *)
      | unit => Datatypes.unit
      | bvec n => RV (Val (bvec n))
      end%type.

    Fixpoint valToRelVal {σ} : Val σ -> RelVal σ :=
      match σ return Val σ -> RelVal σ with
      | int => fun v => SyncVal v
      | bool => fun v => SyncVal v
      | string => fun v => SyncVal v
      | list σ' => fun v => List.map valToRelVal v
      | prod σ1 σ2 => fun v => (valToRelVal (fst v), valToRelVal (snd v))
      (* | sum σ1 σ2 => fun v => match v with *)
      (*                         | inl v => SyncVal (inl (valToRelVal v)) *)
      (*                         | inr v => SyncVal (inr (valToRelVal v)) *)
      (*                         end *)
      | unit => fun v => tt
      | bvec n => fun v => SyncVal v
      end%type.

    Fixpoint map {σ} : (forall σ, RV (Val σ) -> Val σ) -> RelVal σ -> Val σ :=
      match σ return (forall σ, RV (Val σ) -> Val σ) -> RelVal σ -> Val σ with
      | int => fun f rv => f _ rv
      | bool => fun f rv => f _ rv
      | string => fun f rv => f _ rv
      | list σ' => fun f rv => List.map (map f) rv
      | prod σ1 σ2 => fun f rv => (map f (fst rv), map f (snd rv))
      (* | sum σ1 σ2 => fun f rv => f _ rv *)
      | unit => fun f rv => tt
      | bvec n => fun f rv => f _ rv
      end%type.

    Definition projLeft {σ} (rv : RelVal σ) : Val σ :=
      map (fun σ => @projLeftRV (Val σ)) rv.

    Definition projRight {σ} (rv : RelVal σ) : Val σ :=
      map (fun σ => @projRightRV (Val σ)) rv.

    Fixpoint listOfRVToRVOfList {A} (rv_list : (Datatypes.list (RV A))) : RV (Datatypes.list A) :=
      match rv_list with
      | nil => SyncVal nil
      | (x :: l)%list => liftBinOpRV cons x (listOfRVToRVOfList l)
      end.

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

    Fixpoint relValToRV {σ} : RelVal σ -> RV (Val σ) :=
      match σ return RelVal σ -> RV (Val σ) with
      | int => id
      | bool => id
      | string => id
      | list σ' => fun rv => listOfRVToRVOfList (List.map relValToRV rv)
      | prod σ1 σ2 => fun rv => pairOfRVToRVOfPair (relValToRV (fst rv), relValToRV (snd rv))
      (* | sum σ1 σ2 => id *)
      | unit => fun rv => SyncVal tt
      | bvec n => id
      end%type.

    Lemma valToRelValToRVIsSyncVal {σ} (v : Val σ) : relValToRV (valToRelVal v) = SyncVal v.
    Proof.
      induction σ; try reflexivity.
      - cbn. induction v.
        + auto.
        + cbn. rewrite IHv. rewrite IHσ. auto.
      - destruct v. cbn. rewrite IHσ1, IHσ2. auto.
      - destruct v. auto.
    Qed.

    (* This function "and"s the result in case of lists and pairs and unit is automatically true *)
    (*  TODO: I am not a 100% sure that this method isn't more misleading than helpful. *)
    Fixpoint liftBoolFuncRelValAnd {σ} (f : forall σ', RV σ' -> Datatypes.bool) :
      RelVal σ -> Datatypes.bool :=
      match σ return RelVal σ -> Datatypes.bool with
      | int => fun rv => f _ rv
      | bool => fun rv => f _ rv
      | string => fun rv => f _ rv
      | list σ' => fun rv => fold_right andb true (List.map (liftBoolFuncRelValAnd f) rv)
      | prod σ1 σ2 => fun rv => liftBoolFuncRelValAnd f (fst rv) && liftBoolFuncRelValAnd f (snd rv)
      (* | sum σ1 σ2 => fun rv => f _ rv *)
      | unit => fun rv => true
      | bvec n => fun rv => f _ rv
      end%type.

    Fixpoint liftPropFuncRelValAnd {σ} (f : forall σ', RV σ' -> Prop) :
      RelVal σ -> Prop :=
      match σ return RelVal σ -> Prop with
      | int => fun rv => f _ rv
      | bool => fun rv => f _ rv
      | string => fun rv => f _ rv
      | list σ' => fun rv => fold_right and True (List.map (liftPropFuncRelValAnd f) rv)
      | prod σ1 σ2 => fun rv => liftPropFuncRelValAnd f (fst rv) /\ liftPropFuncRelValAnd f (snd rv)
      (* | sum σ1 σ2 => fun rv => f _ rv *)
      | unit => fun rv => True
      | bvec n => fun rv => f _ rv
      end%type.

    Definition isSyncValRV {σ} (rv : RV σ) : Datatypes.bool :=
      match rv with
      | SyncVal _ => true
      | NonSyncVal _ _ => false
      end.

    Definition isSyncVal {σ} : RelVal σ -> Datatypes.bool :=
      liftBoolFuncRelValAnd (@isSyncValRV).

    Definition isSyncValPropRV {σ} (v : RV σ) : Prop :=
      match v with
      | SyncVal _ => True
      | NonSyncVal _ _ => False
      end.

    Definition isSyncValProp {σ} : RelVal σ -> Prop :=
      liftPropFuncRelValAnd (@isSyncValPropRV).
      

      Fixpoint vecOfRVToRVOfVec {n} (rv_vec : Vector.t (RV (Val bool)) n) : RV (Val (ty.bvec n)) :=
        match rv_vec with
        | Vector.nil => SyncVal bv.nil
        | Vector.cons x l => liftBinOpRV (A := Val bool) (B := Val (bvec _)) (C := Val (bvec _)) (bv.cons (n := _)) x (vecOfRVToRVOfVec l)
        end.

      (* Fixpoint sumRelValIsRelValSum {σ1 σ2} (rv_sum : RelVal σ1 + RelVal σ2) : RelVal (sum σ1 σ2) := *)
      (*   match rv_sum with *)
      (*   | inl rv => match rv with *)
      (*               | SyncVal _ v => SyncVal (sum _ _) (inl v) *)
      (*               | NonSyncVal _ v1 v2 => NonSyncVal (sum _ _) (inl v1) (inl v2) *)
      (*               end *)
      (*   | inr rv => match rv with *)
      (*               | SyncVal _ v => SyncVal (sum _ _) (inr v) *)
      (*               | NonSyncVal _ v1 v2 => NonSyncVal (sum _ _) (inr v1) (inr v2) *)
      (*               end *)
      (*   end. *)

      (* Fixpoint liftNamedEnv {varkit b} (a : @NamedEnv (@Variables.PVar varkit) Ty Val b) : @NamedEnv (@Variables.PVar varkit) Ty RelVal b := *)
      (*   match a with *)
      (*   | env.nil => env.nil *)
      (*   | env.snoc e x db => env.snoc (liftNamedEnv e) x (SyncVal _ db) *)
      (*   end. *)

      (* Fixpoint NamedEnvValToRelVal {N Γ} (nenv1 : @NamedEnv N Ty Val Γ) : NamedEnv Val Γ -> NamedEnv RelVal Γ := *)
      (*   match nenv1 with *)
      (*   | env.nil => fun nenv2 => env.nil *)
      (*   | env.snoc nenv1' b1 db1 => *)
      (*       fun nenv2 => *)
      (*         match env.view nenv2 with *)
      (*           env.isSnoc nenv2' db2 => env.snoc (NamedEnvValToRelVal nenv1' nenv2') b1 (NonSyncVal (type b1) db1 db2) *)
      (*         end *)
      (*   end. *)
      

      (* Fixpoint mapSyncValNamedEnv {X Σ} (ı : NamedEnv (X := X) Val Σ) : NamedEnv (X := X) RelVal Σ := *)
      (*   match ı with *)
      (*   | env.nil => env.nil *)
      (*   | env.snoc E db v => env.snoc (mapSyncValNamedEnv E) db (SyncVal (type db) v) *)
      (*   end. *)

      (* Fixpoint allSync {X Σ} (ı : NamedEnv (X := X) RelVal Σ) : Prop := *)
      (*   match ı with *)
      (*   | env.nil => True *)
      (*   | env.snoc E db v => match v with *)
      (*                        | SyncVal _ _ => allSync E *)
      (*                        | _ => False *)
      (*                        end *)
      (*   end. *)

      (* Fixpoint allNonSync {X Σ} (ı : NamedEnv (X := X) RelVal Σ) : Prop := *)
      (*   match ı with *)
      (*   | env.nil => True *)
      (*   | env.snoc E db v => match v with *)
      (*                        | NonSyncVal _ _ _ => allNonSync E *)
      (*                        | _ => False *)
      (*                        end *)
      (*   end. *)

      (* Fixpoint namedEnvRel_to_nonsyncval {X Σ} (nenv : NamedEnv (X := X) RelVal Σ) : NamedEnv (X := X) RelVal Σ := *)
      (*   match nenv with *)
      (*   | env.nil => env.nil *)
      (*   | env.snoc E db rv => *)
      (*       match rv with *)
      (*       | NonSyncVal _ _ _ => env.snoc (namedEnvRel_to_nonsyncval E) db rv *)
      (*       | SyncVal _ v => env.snoc (namedEnvRel_to_nonsyncval E) db (NonSyncVal _ v v) *)
      (*       end *)
      (*   end. *)

    Unset Universe Polymorphism.

  End WithTypeDenote.

  Class TypeDefKit {TDC : TypeDeclKit} (TDN : TypeDenoteKit TDC) : Type :=
    {
      (* enum_eqdec   : EqDec enumi;
      union_eqdec  : EqDec unioni;
      record_eqdec : EqDec recordi;

      enumt_eqdec E  : EqDec (enumt E);
      enumt_finite E : finite.Finite (enumt E);

      uniont_eqdec U  : EqDec (uniont U);
      (* Names of union data constructors. *)
      unionk          : unioni -> Set;
      unionk_eqdec U  : EqDec (unionk U);
      unionk_finite U : finite.Finite (unionk U);
      unionk_ty U     : unionk U -> Ty;

      recordt_eqdec R  : EqDec (recordt R);
      (* Record field names. *)
      recordf          : Set;
      (* Record field types. *)
      recordf_ty       : recordi -> NCtx recordf Ty;

      (* Union types. *)
      (* Union data constructor field type *)
      unionv_fold U   : { K : unionk U & Val (unionk_ty U K) } -> uniont U;
      unionv_unfold U : uniont U -> { K : unionk U & Val (unionk_ty U K) };

      (* Record types. *)
      recordv_fold R   : NamedEnv Val (recordf_ty R) -> recordt R;
      recordv_unfold R : recordt R -> NamedEnv Val (recordf_ty R);

      unionv_fold_unfold U K : unionv_fold U (unionv_unfold U K) = K;
      unionv_unfold_fold U K : unionv_unfold U (unionv_fold U K) = K;

      recordv_fold_unfold R v : recordv_fold R (recordv_unfold R v) = v;
      recordv_unfold_fold R v : recordv_unfold R (recordv_fold R v) = v; *)
    }.

  (* Coq 8.16 will start generating coercions for [:>] in Class definitions. Not
     sure what the implications are and if we want that. For now, manually
     declare the necessary fields as superclass instances. *)
 (* #[export] Existing Instance enum_eqdec.
  #[export] Existing Instance union_eqdec.
  #[export] Existing Instance record_eqdec.
  #[export] Existing Instance enumt_eqdec.
  #[export] Existing Instance enumt_finite.
  #[export] Existing Instance uniont_eqdec.
  #[export] Existing Instance unionk_eqdec.
  #[export] Existing Instance unionk_finite.
  #[export] Existing Instance recordt_eqdec. *)

  Section WithTypeDef.

    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.

    #[export] Instance Ty_eq_dec : EqDec Ty :=
      fix ty_eqdec (σ τ : Ty) {struct σ} : dec_eq σ τ :=
        match σ , τ with
        | int        , int        => left eq_refl
        | bool       , bool       => left eq_refl
        | string     , string     => left eq_refl
        | list σ     , list τ     => f_equal_dec list noConfusion_inv (ty_eqdec σ τ)
        | prod σ1 σ2 , prod τ1 τ2 => f_equal2_dec prod noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2)
        (* | sum σ1 σ2  , sum τ1 τ2  => f_equal2_dec sum noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2) *)
        | unit       , unit       => left eq_refl
(*        | enum E1    , enum E2    => f_equal_dec enum noConfusion_inv (eq_dec E1 E2) *)
        | bvec n1    , bvec n2    => f_equal_dec bvec noConfusion_inv (eq_dec n1 n2)
(*        | tuple σs   , tuple τs   => f_equal_dec
                                       tuple noConfusion_inv
                                       (eq_dec (EqDec := ctx.eq_dec_ctx ty_eqdec) σs τs)
        | union U1   , union U2   => f_equal_dec union noConfusion_inv (eq_dec U1 U2)
        | record R1  , record R2  => f_equal_dec record noConfusion_inv (eq_dec R1 R2) *)
        | _          , _          => right noConfusion_inv
        end.

    #[export] Instance Val_eq_dec : forall σ, EqDec (Val σ) :=
      fix eqd σ :=
        match σ with
        | int      => eq_dec (A := Z)
        | bool     => eq_dec (A := Datatypes.bool)
        | string   => eq_dec (A := String.string)
        | list σ   => eq_dec (A := Datatypes.list (Val σ))
        | prod σ τ => eq_dec (A := Datatypes.prod (Val σ) (Val τ))
        (* | sum σ τ  => eq_dec (A := Datatypes.sum (Val σ) (Val τ)) *)
        | unit     => eq_dec (A := Datatypes.unit)
 (*       | enum E   => eq_dec (A := enumt E) *)
        | bvec n   => eq_dec (A := bv n)
(*        | tuple σs => ctx.Ctx_rect
                        (fun τs => EqDec (EnvRec Val τs))
                        (eq_dec (A := Datatypes.unit))
                        (fun τs IHτs τ =>
                           @eq_dec
                             (Datatypes.prod (EnvRec Val τs) (Val τ))
                             (prod_eqdec IHτs (eqd τ)))
                        σs
        | union U  => eq_dec (A := uniont U)
        | record R => eq_dec (A := recordt R) *)
        end.

    Lemma helper {A} {x y1 y2 : A} : NonSyncVal y1 y2 = SyncVal x -> False.
    Proof.
      congruence.
      Show Proof.
    Qed.      


    #[export] Instance RV_eq_dec : forall σ, EqDec (RV (Val σ)) :=
      fun σ x y => match x , y with
                   | SyncVal x , SyncVal y => match eq_dec x y with
                                                  | left eq => left (f_equal SyncVal eq)
                                                  | right neq => right (fun p : SyncVal _ = SyncVal _ => neq (f_equal projLeftRV p))
                                                  end
                   | NonSyncVal x1 x2 , NonSyncVal y1 y2 =>
                       match eq_dec x1 y1 , eq_dec x2 y2 with
                       | left eq1 , left eq2 => left (f_equal2 NonSyncVal eq1 eq2)
                       | right neq1, _ => right (fun p : NonSyncVal _ _ = NonSyncVal _ _ => neq1 (f_equal projLeftRV p))
                       | _, right neq2 => right (fun p : NonSyncVal _ _ = NonSyncVal _ _ => neq2 (f_equal projRightRV p))
                       end
                   | SyncVal x , NonSyncVal y1 y2 =>
                       right (fun Heq =>
                       let H0 : False :=
                         eq_ind (SyncVal x)
                           (fun e : RV _ => match e with
                                                | SyncVal _ => True
                                                | NonSyncVal _ _ => False
                                                end) I (NonSyncVal y1 y2) Heq in
                       False_ind False H0)
                   | NonSyncVal x1 x2 , SyncVal y =>
                       right (fun Heq =>
                       let H0 : False :=
                         eq_ind (NonSyncVal x1 x2)
                           (fun e : RV _ =>
                              match e with
                              | SyncVal _ => False
                              | NonSyncVal _ _ => True
                              end) I (SyncVal y) Heq in
                       False_ind False H0)
                   end.

        #[export] Instance RelVal_eq_dec : forall σ, EqDec (RelVal σ) :=
      fix eqd σ :=
        match σ return EqDec (RelVal σ) with
        | int      => RV_eq_dec _
        | bool     => RV_eq_dec _
        | string   => RV_eq_dec _
        | list σ   => eq_dec (A := Datatypes.list (RelVal σ))
        | prod σ τ => eq_dec (A := Datatypes.prod (RelVal σ) (RelVal τ))
        (* | sum σ τ  => RV_eq_dec _ *)
        | unit     => eq_dec (A := Datatypes.unit)
        | bvec n   => RV_eq_dec _
        end.


 (*   Lemma unionv_fold_inj {U} (v1 v2 : {K : unionk U & Val (unionk_ty U K)}) :
      unionv_fold U v1 = unionv_fold U v2 <-> v1 = v2.
    Proof.
      split; intro H; [|now f_equal].
      apply (f_equal (unionv_unfold U)) in H.
      now rewrite !unionv_unfold_fold in H.
    Qed.

    Lemma unionv_unfold_inj {U} (v1 v2 : Val (union U)) :
      unionv_unfold U v1 = unionv_unfold U v2 <-> v1 = v2.
    Proof.
      split; intro H; [|now f_equal].
      apply (f_equal (unionv_fold U)) in H.
      now rewrite !unionv_fold_unfold in H.
    Qed.

    Lemma recordv_fold_inj {R} (v1 v2 : NamedEnv Val (recordf_ty R)) :
      recordv_fold R v1 = recordv_fold R v2 <-> v1 = v2.
    Proof.
      split; intro H; [|now f_equal].
      apply (f_equal (recordv_unfold R)) in H.
      now rewrite !recordv_unfold_fold in H.
    Qed.

    Lemma recordv_unfold_inj {R} (v1 v2 : Val (ty.record R)) :
      recordv_unfold R v1 = recordv_unfold R v2 <-> v1 = v2.
    Proof.
      split; intro H; [|now f_equal].
      apply (f_equal (recordv_fold R)) in H.
      now rewrite ?recordv_fold_unfold in H.
    Qed.

*)

    Lemma K (σ : Ty) (p : σ = σ) : p = eq_refl.
    Proof. apply uip. Qed.

  End WithTypeDef.
  #[global] Arguments int {TK}.
  #[global] Arguments bool {TK}.
  #[global] Arguments string {TK}.
  #[global] Arguments list {TK} σ.
  #[global] Arguments prod {TK} σ τ.
  (* #[global] Arguments sum {TK} σ τ. *)
  #[global] Arguments unit {TK}.
  (*  #[global] Arguments enum {TK} E. *)
  #[global] Arguments bvec {TK} n%_nat_scope.
(*  #[global] Arguments tuple σs%_ctx_scope.
  #[global] Arguments union U.
  #[global] Arguments record R. *)

End ty.
Export ty
  ( TypeDeclKit, (* enumt, uniont, recordt, *)

    TypeDenoteKit,
    Ty, Val, RelVal,

    TypeDefKit(* , enum_eqdec, enumt_eqdec, enumt_finite, *)
    (* enumi, *)
    (* unioni, *)
    (* recordi *)
    (* union_eqdec, uniont_eqdec, unionk, unionk_eqdec, unionk_finite, unionk_ty,
    unionv_fold, unionv_unfold, record_eqdec, recordt_eqdec, recordf,
    recordf_ty, recordv_fold, recordv_unfold,

    unionv_fold_unfold, unionv_unfold_fold,
    unionv_fold_inj, unionv_unfold_inj,
    recordv_fold_unfold, recordv_unfold_fold,
    recordv_fold_inj, recordv_unfold_inj *)
  ).
Export (hints) ty.

Module Type Types.

  #[export] Declare Instance typedeclkit   : TypeDeclKit.
  #[export] Declare Instance typedenotekit : TypeDenoteKit typedeclkit.
  #[export] Declare Instance typedefkit    : TypeDefKit typedenotekit.
  #[export] Declare Instance varkit        : VarKit.

End Types.

#[local] Instance DefaultTypeDeclKit : TypeDeclKit := ty.Build_TypeDeclKit.
  (* {| enumi := Empty_set; *)
  (*    unioni := Empty_set; *)
  (*    recordi := Empty_set; *)
  (* |}. *)

#[local] Instance DefaultTypeDenoteKit : TypeDenoteKit DefaultTypeDeclKit := ty.Build_TypeDenoteKit _.
  (* {| (* enumt _ := Empty_set; *)
  (*    uniont _ := Empty_set; *)
  (*    recordt _ := Empty_set; *) *)
  (* |}. *)

#[local,refine] Instance DefaultTypeDefKit : TypeDefKit DefaultTypeDenoteKit := ty.Build_TypeDefKit _ _.
(*   {| (* *)
(*     unionk _            := Empty_set; *)
(*      unionk_ty _ _       := ty.unit; *)
(*      unionv_fold         := Empty_set_rec _; *)
(*      unionv_unfold       := Empty_set_rec _; *)
(*      recordf             := Empty_set; *)
(*      recordf_ty          := Empty_set_rec _; *)
(*      recordv_fold        := Empty_set_rec _; *)
(*      recordv_unfold      := Empty_set_rec _; *)
(* *) *)
(*   |}. *)
Proof. all: abstract (intros []). Defined.
