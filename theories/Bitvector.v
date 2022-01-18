(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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
     Logic.StrictProp
     NArith.BinNat.

From Katamaran Require Import
     Prelude.
Local Set Implicit Arguments.
(* Local Set Primitive Projections. *)

Module bv.

  Fixpoint at_most (n : nat) {struct n} : positive -> SProp.
  Proof.
    destruct n; intros p.
    - apply sEmpty.
    - destruct p.
      + apply (at_most n p).
      + apply (at_most n p).
      + apply sUnit.
  Defined.

  Definition is_wf (n : nat) (bs : N) : SProp :=
    match bs with
    | N0     => sUnit
    | Npos p => at_most n p
    end.

  Record t (n : nat) : Set :=
    mk { bin : N; wf : is_wf n bin }.
  Arguments mk {n} _ &.

  Section Conversion.

    Fixpoint trunc (n : nat) (p : positive) : N :=
      match n with
      | 0   => N0
      | S n => match p with
                | xI p => N.succ_double (trunc n p)
                | xO p => N.double (trunc n p)
                | xH   => N0
                end
      end.

    Lemma wf_double (n : nat) (x : N) :
      is_wf n x -> is_wf (S n) (N.double x).
    Proof. destruct x; cbn; intros H; apply H. Qed.

    Lemma wf_succ_double (n : nat) (x : N) :
      is_wf n x -> is_wf (S n) (N.succ_double x).
    Proof. destruct x; cbn; intros H; apply H. Qed.

    Lemma wf_trunc n : forall p, is_wf n (trunc n p).
    Proof.
      induction n; cbn.
      - constructor.
      - intros p. destruct p; cbn.
        + apply wf_succ_double. apply IHn.
        + apply wf_double. apply IHn.
        + constructor.
    Qed.

    Definition of_N {n} (bs : N) : t n :=
      match bs with
      | N0     => mk N0 stt
      | Npos p => mk (trunc n p) (wf_trunc n p)
      end.

    (* Definition unsigned {n} (x : t n) : Z := *)
    (*   Z.of_N (bin x). *)
    (* Definition signed {n} (x : t n) : Z := *)
    (*   unsigned x - Zpower.two_power_nat (Nat.pred n). *)

    (* Definition of_Z {n} (x : Z) : t n := *)
    (*   of_N (Z.to_N (Z.modulo x (Zpower.two_power_nat n))). *)

  End Conversion.

  Section Constants.

    Definition zero n : t n := mk 0 stt.
    Definition one n : t n :=
      match n with
      | 0   => mk 0 stt
      | S _ => mk 1 stt
      end.

  End Constants.

  Section Equality.

    Definition eqb {n : nat} (x y : t n) : bool :=
      N.eqb (bin x) (bin y).

    Lemma eqb_spec {n : nat} : forall (x y : t n), reflect (x = y) (eqb x y).
    Proof.
      intros [x wfx] [y wfy]. unfold eqb. cbn.
      destruct (N.eqb_spec x y); constructor.
      - now destruct e.
      - now intros p%(f_equal (@bin _)).
    Qed.

  End Equality.

  Section Arithmetic.

    Definition add {n} (x y : t n) : t n :=
      of_N (N.add (bin x) (bin y)).

    Definition sub {n} (x y : t n) : t n :=
      of_N (N.sub (N.shiftl_nat 1 n + bin x) (bin y)).

    Definition mul {n} (x y : t n) : t n :=
      of_N (N.mul (bin x) (bin y)).

  End Arithmetic.

  Section Logical.

    Definition land {n} (x y : t n) : t n :=
      of_N (N.land (bin x) (bin y)).

    Definition lor {n} (x y : t n) : t n :=
      of_N (N.lor (bin x) (bin y)).

    Definition lxor {n} (x y : t n) : t n :=
      of_N (N.lxor (bin x) (bin y)).

  End Logical.

  Section ListLike.

    Definition nil : t 0 :=
      mk N0 stt.
    Definition cons [n] (b : bool) (xs : t n) : t (S n) :=
      match xs with
        mk bs wf =>
          if b
          then mk (N.succ_double bs) (wf_succ_double n bs wf)
          else mk (N.double bs) (wf_double n bs wf)
      end.

    Inductive NilView : t 0 -> Set :=
    | nvnil : NilView nil.
    Definition nilView (xs : t 0) : NilView xs :=
      match xs with
      | mk bs wf =>
          match bs return forall wf : is_wf 0 bs, NilView (mk bs wf) with
          | N0      => fun _ => nvnil
          | N.pos p => sEmpty_rect _
          end wf
      end.

    Inductive ConsView {n} : t (S n) -> Set :=
    | cvcons (b : bool) (xs : t n) : @ConsView n (cons b xs).
    Definition consView {n} (xs : t (S n)) : ConsView xs :=
      match xs with
      | mk bs wf =>
          match bs return forall wf : is_wf (S n) bs, ConsView (mk bs wf) with
          | N0      => fun _ => cvcons false (mk 0 stt)
          | N.pos p =>
              match p return forall wf : at_most (S n) p, ConsView (mk (N.pos p) wf) with
              | xI p => fun wf => cvcons true  (mk (N.pos p) wf)
              | xO p => fun wf => cvcons false (mk (N.pos p) wf)
              | xH   => fun _  => cvcons true  (mk 0 stt)
              end
          end wf
      end.

    Inductive View : forall n, t n -> Set :=
    | isnil  : @View 0 nil
    | iscons (b : bool) {n} (xs : t n) : @View (S n) (cons b xs).
    Definition view {n} : forall xs : t n, View xs :=
      match n return forall xs : t n, View xs with
      | 0   => fun xs => match nilView xs with nvnil => isnil end
      | S n => fun xs => match consView xs with cvcons b xs => iscons b xs end
      end.

    Definition t_rect (P : forall n : nat, t n -> Type)
      (PO : P O nil)
      (PS : forall n (b : bool) (x : t n), P n x -> P (S n) (cons b x)) :
      forall [n] (xs : t n), P n xs :=
      fix t_rect (n : nat) : forall xs : t n, P n xs :=
        match n with
        | 0   => fun xs => match nilView xs with
                           | nvnil => PO
                           end
        | S n => fun xs => match consView xs with
                           | cvcons b xs => PS n b xs (t_rect n xs)
                           end
        end.

    Definition fold_right (A : forall n : nat, Type)
      (c : forall n, bool -> A n -> A (S n)) (n : A O) :
      forall {m} (xs : t m), A m :=
      t_rect (fun m _ => A m) n (fun m b _ p => c m b p).

    Definition app {m n} (xs : t m) (ys : t n) : t (m + n) :=
      fold_right (fun m => t (m + n)) (fun m => @cons (m + n)) ys xs.
    Global Arguments app : simpl never.

    Lemma app_nil {m} (xs : t m) :
      app nil xs = xs.
    Proof. reflexivity. Defined.

    Lemma app_cons b {m n} (xs : t m) (ys : t n) :
      app (cons b xs) ys = cons b (app xs ys).
    Proof. destruct xs as [[] ?], b; reflexivity. Defined.

    Inductive AppView m n : t (m + n) -> Set :=
    | isapp (xs : t m) (ys : t n) : AppView _ _ (app xs ys).

    Definition avcons {m n} b {xs} (axs : AppView m n xs) : AppView (S m) n (cons b xs).
    Proof. destruct axs. rewrite <- app_cons. constructor. Defined.

    Fixpoint appView m n {struct m} : forall xs : t (m + n), AppView _ _ xs.
      destruct m; cbn [plus].
      - apply (@isapp 0 n nil).
      - intros xs. destruct (consView xs). apply avcons. apply appView.
    Defined.

  End ListLike.

  Module rec.

    Fixpoint t (n : nat) : Set :=
      match n with
      | O   => unit
      | S n => bool * t n
      end.

    Definition nil : t 0 := tt.
    Definition cons [n] (b : bool) (xs : t n) : t (S n) := (b , xs).

    Definition t_rect (P : forall n : nat, t n -> Type)
      (PO : P O nil)
      (PS : forall n (b : bool) (x : t n), P n x -> P (S n) (cons b x)) :
      forall [n] (x : t n), P n x :=
      fix t_rect (n : nat) : forall x : t n, P n x :=
        match n with
        | 0   => fun x => match x with tt    => PO end
        | S n => fun x => match x with (b,x) => PS n b x (t_rect n x) end
        end.

    Definition fold_right (A : forall n : nat, Type)
      (c : forall n, bool -> A n -> A (S n)) (n : A O) :
      forall {m} (xs : t m), A m :=
      t_rect (fun m _ => A m) n (fun m b _ p => c m b p).

  End rec.

  Definition to_rec {n} : t n -> rec.t n :=
    fold_right rec.t rec.cons rec.nil.

  Definition of_rec {n} : rec.t n -> t n :=
    rec.fold_right t cons nil.

End bv.
Notation bv n := (bv.t n).
