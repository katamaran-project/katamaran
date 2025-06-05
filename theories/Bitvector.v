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
     Arith.PeanoNat
     Bool.Bool
     NArith.BinNat
     PArith.BinPos
     ZArith.BinInt
     ZArith.Zdiv
     RelationClasses
     Ring
     micromega.Lia
     Morphisms.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations Prelude.
Require Import stdpp.base.
Local Set Implicit Arguments.

Declare Scope bv_scope.
Delimit Scope bv_scope with bv.
Declare Scope bv_bitstring_scope.
Delimit Scope bv_bitstring_scope with bits.

(* Yet another library for sized bitvectors. Under the hood it is reusing the
   binary natural numbers N from the Coq standard library to leverage the proof
   automation already defined for it (very soon I guess). This means that
   bitvectors are stored as strings of bits in little-endian! Bitvector sizes
   are statically checked through a type-level natural number. We also define
   a good amount of dependently-typed goodies for vector-like operations.

   Ultimately, it would be great to consolidate this with for example:
   https://github.com/jasmin-lang/coqword or
   https://github.com/mit-plv/coqutil/tree/master/src/coqutil/Word

   Other resources include:
   https://github.com/arthuraa/coq-utils/blob/master/theories/word.v
   https://github.com/mit-plv/bbv
*)

Module bv.

  Import transparent.

  (* The given [positive] consist of fewer than n bits. *)
  Fixpoint at_most (n : nat) {struct n} : positive -> bool :=
    match n with
    | O   => fun _ => false
    | S n => fun p =>
               match p with
               | xI p => at_most n p
               | xO p => at_most n p
               | xH => true
               end
    end.

  Definition is_wf (n : nat) (bs : N) : bool :=
    match bs with
    | N0     => true
    | Npos p => at_most n p
    end.

  Record bv (n : nat) : Set :=
    mk { bin : N; _ : Is_true (is_wf n bin) }.
  Arguments mk {n} _ &.
  Set Transparent Obligations.

  Definition bin_inj {n} (x y : bv n) : bin x = bin y -> x = y :=
    match x , y with
    | mk x p , mk y q =>
        fun e : x = y =>
          match e in _ = y return forall q, mk x p = mk y q with
          | eq_refl =>
              fun q =>
                match proof_irrelevance_is_true p q with
                | eq_refl => eq_refl
                end
          end q
    end.

  Lemma bin_inj_equiv {n} (x y : bv n) : bin x = bin y <-> x = y.
  Proof.
    split.
    - apply bin_inj.
    - now intros ->.
  Qed.

  Section Equality.

    Definition eqb {n : nat} (x y : bv n) : bool :=
      N.eqb (bin x) (bin y).

    Lemma eqb_spec {n : nat} : forall (x y : bv n), reflect (x = y) (eqb x y).
    Proof.
      intros [x wfx] [y wfy]. unfold eqb. cbn.
      destruct (N.eqb_spec x y); constructor.
      - destruct e. apply f_equal, proof_irrelevance_is_true.
      - now intros p%(f_equal (@bin _)).
    Qed.

    #[export] Instance eqdec_bv {n : nat} : EqDec (bv n) :=
      fun x y =>
        match N.eq_dec (bin x) (bin y) with
        | left a  => left (bin_inj x y a)
        | right n => right (fun e => n (f_equal (@bin _) e))
        end.

  End Equality.

  Section NoConfusion.

    Definition NoConfusion_bv {n} (x y : bv n) : Prop :=
      bin x = bin y.

    Definition noConfusion_bv {n} (x y : bv n) : NoConfusion_bv x y -> x = y :=
      bin_inj x y.

    Definition noConfusion_inv_bv {n} (x y : bv n) : x = y -> NoConfusion_bv x y :=
      fun e => match e with
               | eq_refl => eq_refl
               end.

    #[program]
    Instance NoConfusionPackage_bv {n} : NoConfusionPackage (bv n) :=
      {| NoConfusion := @NoConfusion_bv n;
         noConfusion := @noConfusion_bv n;
         noConfusion_inv := @noConfusion_inv_bv n;
      |}.
    Next Obligation.
      intros n x y. destruct x as [x p], y as [y q].
      intros e. change_no_check (x = y) in e.
      destruct e. cbn. now destruct proof_irrelevance_is_true.
    Qed.
    Next Obligation.
      intros n x y e. apply uip.
    Qed.

  End NoConfusion.
  Local Existing Instance NoConfusionPackage_bv.

  #[global] Notation exp2 n := (N.pow 2%N (N.of_nat n)).

  Section Conversion.

    Lemma exp2_S n : exp2 (S n) = (2 * exp2 n)%N.
    Proof. now rewrite Nnat.Nat2N.inj_succ, N.pow_succ_r'. Qed.

    Fixpoint trunc (n : nat) (p : positive) : N :=
      match n with
      | 0   => N0
      | S n => match p with
                | xI p => N.succ_double (trunc n p)
                | xO p => N.double (trunc n p)
                | xH   => 1%N
                end
      end.

    Definition wf_double (n : nat) (x : N) :
      Is_true (is_wf n x) -> Is_true (is_wf (S n) (N.double x)) :=
      match x with
      | N0     => fun wf => wf
      | Npos p => fun wf => wf
      end.

    Definition wf_succ_double (n : nat) (x : N) :
      Is_true (is_wf n x) -> Is_true (is_wf (S n) (N.succ_double x)) :=
       match x with
       | N0     => fun wf => wf
       | Npos p => fun wf => wf
       end.

    Fixpoint wf_trunc n : forall p, Is_true (is_wf n (trunc n p)) :=
      match n with
      | O   => fun _ => I
      | S n => fun p =>
                  match p with
                  | xI p => wf_succ_double n (trunc n p) (wf_trunc n p)
                  | xO p => wf_double n (trunc n p) (wf_trunc n p)
                  | xH   => I
                  end
      end.


    Definition truncn (n : nat) (x : N) : N :=
      match x with
      | N0 => N0
      | Npos p => trunc n p
      end.

    Lemma truncn_zero {x} : truncn 0 x = N0.
    Proof. now destruct x. Qed.

    Definition wf_truncn n x : Is_true (is_wf n (truncn n x)) :=
      match x with
      | N0     => I
      | Npos p => wf_trunc n p
      end.

    Definition of_N {n} (bs : N) : bv n :=
      mk (truncn n bs) (wf_truncn n bs).

    Definition of_nat {n} (k : nat) : bv n :=
      of_N (N.of_nat k).

    Definition of_bool (b : bool) : bv 1 := if b then mk 1 I else mk 0 I.
    Definition to_bool (b : bv 1) : bool := N.eqb 1 (bin b).
    Lemma to_bool_of_bool {b} : to_bool (of_bool b) = b.
    Proof. now destruct b. Qed.
    Lemma of_bool_to_bool {b} : of_bool (to_bool b) = b.
    Proof. destruct b as [[|[?|?|]] []]; now cbn. Qed.

    Fixpoint trunc_wf (n : nat) (p : positive) {struct n} :
      Is_true (at_most n p) -> trunc n p = N.pos p :=
      match n , p with
      | O   , _    => fun w => match w with end
      | S n , xI p => fun w => f_equal N.succ_double (trunc_wf n p w)
      | S n , xO p => fun w => f_equal N.double (trunc_wf n p w)
      | S n , xH   => fun _ => eq_refl
      end.
    Lemma trunc_illf (n : nat) (p : positive) :
      not (Is_true (at_most n p)) -> (trunc n p < N.pos p)%N.
    Proof. generalize dependent p. induction n as [| n]; cbn.
     - Lia.lia.
     - intros p Hp. destruct p.
       * specialize (IHn _ Hp).
         now apply (N.succ_double_lt_mono) in IHn.
       * specialize (IHn _ Hp).
         now apply (N.double_lt_mono) in IHn.
       * cbn in Hp. now exfalso.
    Qed.

    Definition truncn_succ_double (n : nat) (x : N) : truncn (S n) (N.succ_double x) = N.succ_double (truncn n x) :=
      match x with
      | 0%N => eq_refl
      | N.pos p => eq_refl
      end.
    Definition truncn_double (n : nat) (x : N) : truncn (S n) (N.double x) = N.double (truncn n x) :=
      match x with
      | 0%N => eq_refl
      | N.pos p => eq_refl
      end.
    Fixpoint truncn_trunc (n : nat) (p : positive) {struct n} :
      truncn n (trunc n p) = trunc n p.
    Proof.
      destruct n, p; cbn; intuition auto.
      - now rewrite truncn_succ_double, truncn_trunc.
      - now rewrite truncn_double, truncn_trunc.
    Defined.

    Definition truncn_idemp (n : nat) (x : N) :
      truncn n (truncn n x) = truncn n x :=
      match x with
      | 0%N => eq_refl
      | N.pos p => truncn_trunc n p
      end.

    Lemma truncn_wf (n : nat) (x : N) :
      Is_true (is_wf n x) -> truncn n x = x.
    Proof.
      destruct x; cbn; auto using trunc_wf.
    Qed.
    Lemma truncn_illf (n : nat) (x : N) :
      not (Is_true (is_wf n x)) -> (truncn n x < x)%N.
    Proof.
      destruct x; cbn; auto using trunc_illf. contradiction.
    Qed.
    Lemma truncn_le {n x} : (truncn n x <= x)%N.
    Proof. destruct (decide (Is_true (is_wf n x))) eqn:Wf.
    - rewrite truncn_wf; auto.
    - apply N.lt_le_incl. apply truncn_illf; auto.
    Qed.
    Lemma bin_of_N_decr {n} x : (@bin n (of_N x) <= x)%N.
    Proof. unfold bin, of_N. apply truncn_le. Qed.
    Lemma bin_of_nat_decr {n} x : (@bin n (of_nat x) <= N.of_nat x)%N.
    Proof. apply bin_of_N_decr. Qed.

    Definition of_N_wf [n] (bs : N) :
      forall w, of_N bs = @mk n bs w.
    Proof. intros w. now apply noConfusion, truncn_wf. Qed.

    Definition of_N_bin {n} (x : bv n) : of_N (bin x) = x :=
      match x with mk bs w => of_N_wf bs w end.

    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

    Lemma exp2_nzero n : exp2 n <> 0%N.
    Proof. cbn; lia. Qed.

    Lemma trunc_spec {n} : forall p, trunc n p = (Npos p mod exp2 n)%N.
    Proof.
      induction n; cbn.
      - symmetry. apply N.mod_1_r.
      - destruct p; cbn; try rewrite IHn; clear IHn;
          change (N.pos ?p~1)%N with (N.succ_double (Npos p));
          change (N.pos ?p~0)%N with (N.double (Npos p));
          try (remember (Npos p) as q; clear p Heqq);
          rewrite ?N.succ_double_spec, ?N.double_spec, ?exp2_S.
        + rewrite N.Div0.add_mod, N.Div0.mul_mod_distr_l, N.mod_1_l; [|lia].
          symmetry. apply N.mod_small. cbn.
          lia.
        + rewrite (N.double_spec q).
          now rewrite N.Div0.mul_mod_distr_l.
        + rewrite N.mod_1_l; lia.
    Qed.

    Lemma truncn_spec {n x} : truncn n x = (x mod exp2 n)%N.
    Proof.
      destruct x.
      - now rewrite N.Div0.mod_0_l.
      - apply trunc_spec.
    Qed.

    Lemma at_most_spec {n x} : Is_true (at_most n x) <-> (N.pos x < exp2 n)%N.
    Proof.
      revert x.
      induction n; rewrite ?exp2_S; cbn.
      - lia.
      - destruct x; rewrite ?IHn; intuition; lia.
    Qed.

    Lemma is_wf_spec {n x} : Is_true (is_wf n x) <-> (x < exp2 n)%N.
    Proof.
      destruct x; cbn.
      - lia.
      - eapply at_most_spec.
    Qed.

    Lemma bv_is_wf `(a : bv n): (bin a < exp2 n)%N.
    Proof. destruct a as [? Hwf]. cbn. now rewrite is_wf_spec in Hwf. Qed.

  End Conversion.

  Section ListLike.

    Definition nil : bv 0 :=
      mk N0 I.
    Definition cons [n] (b : bool) (xs : bv n) : bv (S n) :=
      match xs with
        mk bs wf =>
          if b
          then mk (N.succ_double bs) (wf_succ_double n bs wf)
          else mk (N.double bs) (wf_double n bs wf)
      end.

    Definition bv_case (P : forall n : nat, bv n -> Type) (PO : P O nil)
      (PS : forall n (b : bool) (x : bv n), P (S n) (cons b x)) :
      forall [n] (xs : bv n), P n xs :=
      fun n xs =>
        match xs with
        | mk bs wf =>
            match n , bs return forall wf, P n (mk bs wf) with
            | O   , N0      => fun wf =>
                                 match wf as t return (P 0 (mk 0 t)) with
                                 | I => PO
                                 end
            | O   , N.pos p => fun wf => False_rect _ wf
            | S m , N0      => fun wf => PS m false (mk 0 wf)
            | S m , N.pos p => match p with
                               | xI p => fun wf => PS m true (mk (N.pos p) wf)
                               | xO p => fun wf => PS m false (mk (N.pos p) wf)
                               | xH    => fun wf => PS m true (mk 0 wf)
                               end
            end wf
        end.

    Lemma bv_case_cons (P : forall n : nat, bv n -> Type) (PO : P O nil)
      (PS : forall n (b : bool) (x : bv n), P (S n) (cons b x)) n b (xs : bv n) :
      bv_case P PO PS (cons b xs) = PS n b xs.
    Proof. now destruct b, xs as [[] wf_xs]. Qed.

    Definition bv_rect (P : forall n : nat, bv n -> Type) (PO : P O nil)
      (PS : forall n (b : bool) (x : bv n), P n x -> P (S n) (cons b x)) :
      forall [n] (xs : bv n), P n xs :=
      fix rect [n] (xs : bv n) {struct n} : P n xs :=
        bv_case P PO (fun n b x => PS n b x (rect x)) xs.

    Fixpoint fold_right (A : forall n : nat, Type)
      (c : forall n, bool -> A n -> A (S n)) (n : A O) [m] (xs : bv m) : A m :=
      bv_case (fun k _ => A k) n
        (fun k b x => c k b (fold_right A c n x)) xs.

    Fixpoint fold_left {A : forall n : nat, Type}
      (c : forall n, A n -> bool -> A (S n)) (n : A O) [m] (xs : bv m) : A m :=
      bv_case (fun m _ => A m) n
        (fun k b xs => fold_left (fun m => c (S m)) (c 0 n b) xs) xs.

    Lemma fold_left_cons {A : forall n : nat, Type}
      (c : forall n, A n -> bool -> A (S n)) (n : A O) [m] (b : bool) (xs : bv m) :
      fold_left c n (cons b xs) =
      fold_left (fun n => c (S n)) (c 0 n b) xs.
    Proof. now cbn; rewrite bv_case_cons. Qed.

    Variant NilView : bv 0 -> Set :=
      nvnil : NilView nil.
    Variant ConsView {n} : bv (S n) -> Set :=
      cvcons (b : bool) (xs : bv n) : @ConsView n (cons b xs).
    #[global] Arguments cvcons [n] b xs.

    Definition view : forall {n} (xs : bv n),
      match n with O => NilView | S n => ConsView end xs :=
      bv_case _ nvnil cvcons.

    Definition app {m n} (xs : bv m) (ys : bv n) : bv (m + n) :=
      fold_right (fun m => bv (m + n)) (fun m => @cons (m + n)) ys xs.
    #[global] Arguments app : simpl never.

    Lemma app_nil {m} (xs : bv m) : app nil xs = xs.
    Proof. reflexivity. Defined.

    Definition app_cons b {m n} (xs : bv m) (ys : bv n) :
      app (cons b xs) ys = cons b (app xs ys).
    Proof. destruct xs as [[] ?], b; reflexivity. Defined.

    Variant AppView m n : bv (m + n) -> Set :=
      isapp (xs : bv m) (ys : bv n) : AppView _ _ (app xs ys).

    Import EqNotations.

    Definition cvapp {m n} {x : bv (S m)} (cv : ConsView x) (y : bv n) :
      ConsView (app x y) :=
      match cv with
      | cvcons b x => rew <- app_cons b x y in cvcons b (app x y)
      end.

    Definition avcons {m n} b {xs} (axs : AppView m n xs) :
      AppView (S m) n (cons b xs) :=
      match axs with
      | isapp xs ys => rew app_cons b xs ys in isapp (cons b xs) ys
      end.

    Fixpoint appView m n {struct m} : forall xs : bv (m + n), AppView _ _ xs :=
      match m with
      | O   => isapp nil
      | S m => fun xs =>
                 match view xs with
                 | cvcons b xs => avcons b (appView m n xs)
                 end
      end.

    Definition rev_append {m n} (x : bv m) (y : bv n) : bv (m + n) :=
      fold_left (A := fun k => bv (k + n)) (fun k (z : bv (k + n)) b => cons b z) y x.
    Definition rev {m} (x : bv m) : bv m :=
      fold_left (fun k (z : bv k) b => cons b z) nil x.

    Lemma cons_inj [n] (x y : bool) (xs ys : bv n) :
      cons x xs = cons y ys <-> x = y /\ xs = ys.
    Proof.
      split.
      - destruct xs as [xs wfxs], ys as [ys wfys], x, y; intros Heq.
        + split; auto. apply noConfusion_inv_bv, N.succ_double_inj in Heq.
          destruct Heq. apply f_equal, proof_irrelevance_is_true.
        + exfalso. apply noConfusion_inv_bv in Heq.
          destruct xs, ys; discriminate Heq.
        + exfalso. apply noConfusion_inv_bv in Heq.
          destruct xs, ys; discriminate Heq.
        + split; auto. apply noConfusion_inv_bv, N.double_inj in Heq.
          destruct Heq. apply f_equal, proof_irrelevance_is_true.
      - intros [e1 e2]; now f_equal.
    Qed.

    Lemma app_inj [m n] (x1 y1 : bv m) (x2 y2 : bv n) :
      app x1 x2 = app y1 y2 <-> x1 = y1 /\ x2 = y2.
    Proof.
      split.
      - induction x1 using bv_rect.
        + destruct (view y1). rewrite ?app_nil. intuition auto.
        + destruct (view y1) as [c y1]. rewrite ?app_cons.
          intros [H1 H2]%cons_inj. specialize (IHx1 y1 H2).
          intuition congruence.
      - intros [e1 e2]; now f_equal.
    Qed.

    Lemma view_cons {m} b (x : bv m)  :
      view (cons b x) = cvcons b x.
    Proof. now destruct x as [[|x0] p], b. Qed.

    Lemma view_app {m n} (x : bv (S m)) (y : bv n) :
      view (app x y) = cvapp (view x) y.
    Proof.
      destruct (view x).
      rewrite <- (f_equal_dep _ view (eq_sym (app_cons b xs y))).
      cbn. now rewrite view_cons.
    Qed.

    Lemma match_rew {m : nat} {x y : bv (S m)} {D : forall (x : bv (S m)), Set}
      (e : y = x) {f : forall b x, D (cons b x)} (v : ConsView x) :
      match rew <- e in v in ConsView b0 return D b0 with
      | cvcons b0 xs0 => f b0 xs0
      end =
        rew <- e in match v in ConsView b0 return D b0 with
        | cvcons b0 xs0 => f b0 xs0
        end.
    Proof. now subst. Qed.

    Lemma appView_app [m n] (x : bv m) (y : bv n) :
      appView m n (app x y) = isapp x y.
    Proof.
      induction x using bv_rect; cbn - [plus].
      - reflexivity.
      - rewrite view_app.
        rewrite view_cons.
        cbn.
        rewrite match_rew.
        rewrite IHx. cbn.
        now rewrite rew_opp_l.
    Qed.

    Lemma cons_eq_rect (m n : nat) (e : m = n) (b : bool) (v : bv m) :
      cons b (eq_rect m bv v n e) =
      eq_rect (S m) bv (cons b v) (S n) (f_equal S e).
    Proof. now destruct e. Qed.


    Lemma app_nil_r {n} (v : bv n) :
      app v nil = eq_rect n bv v (n + O) (eq_sym (nat_add_0_r n)).
    Proof.
      induction v using bv_rect; cbn; [easy|].
      now rewrite app_cons, IHv, cons_eq_rect, eq_sym_map_distr.
    Qed.

    Lemma app_app {m n o} (vm : bv m) (vn : bv n) (vo : bv o) :
      app (app vm vn) vo =
      eq_rect _ bv (app vm (app vn vo)) _ (nat_add_assoc m n o).
    Proof.
      induction vm using bv_rect; [easy|]; cbn.
      now rewrite !app_cons, IHvm, cons_eq_rect.
    Qed.

    Lemma fold_left_app {A : Type} (c : nat -> A -> bool -> A) (n : A)
      [k l] (xs : bv k) (ys : bv l) :
      fold_left c n (app xs ys) =
      fold_left (fun n' a b => c (k + n') a b) (fold_left c n xs) ys.
    Proof.
      revert c n.
      induction xs using bv_rect; cbn [plus]; intros;
        now rewrite ?app_nil, ?app_cons, ?fold_left_cons.
    Qed.

    Import SignatureNotations.

    #[export] Instance proper_fold_left A (RA : ∀ n, relation (A n))
      : Proper
          ((∀ n, RA n ==> bool ::> RA (S n)) ==> RA 0 ==> ∀ n, bv n ::> RA n)
          fold_left.
    Proof.
      intros c1 c2 cr n1 n2 nr m x. revert A RA c1 c2 cr n1 n2 nr.
      induction x using bv_rect; intros A RA c1 c2 cr n1 n2 nr; cbn - [plus].
      - apply nr.
      - rewrite !bv_case_cons.
        apply (IHx (fun m => A (S m)) (fun m => RA (S m))).
        + intros m a1 a2 ar ?b. now apply cr.
        + now apply cr.
    Qed.

    Lemma fold_left_app_dep {A : forall n : nat, Type}
      (c : forall n, A n -> bool -> A (S n)) (n : A O)
      [k l] (xs : bv k) (ys : bv l) :
      fold_left c n (app xs ys) =
      (fold_left
         (fun n' a b => rew <- [A] nat_add_succ_r k n' in c (k + n') a b)
         (rew <- [A] nat_add_0_r k in fold_left c n xs) ys).
    Proof.
      revert A c n.
      induction xs using bv_rect; cbn [plus]; intros;
        rewrite ?app_nil, ?app_cons, ?fold_left_cons.
      - reflexivity.
      - rewrite IHxs. cbn.
        simple apply (proper_fold_left (fun k => A (S (n + k))) (fun k => @eq _)).
        + clear. intros n' a a' <- b. now destruct (nat_add_succ_r n n'); cbn.
        + generalize (fold_left (fun m => c (S m)) (c 0 n0 b) xs). clear.
          intros a. unfold eq_rect_r. now rewrite eq_sym_map_distr, rew_map.
    Qed.

  End ListLike.

  Section Constants.

    Definition zero {n} : bv n := mk 0 I.
    Definition one {n} : bv n :=
      match n with
      | 0   => mk 0 I
      | S u => mk 1 I
      end.

    Fixpoint onesp (n : nat) : positive :=
      match n with
      | O   => 1
      | S n => (onesp n)~1
      end%positive.

    Fixpoint wf_onesp (n : nat) : at_most (S n) (onesp n) :=
      match n with
      | 0    => I
      | S n' => wf_onesp n'
      end.

    Definition onesn (n : nat) : N :=
      match n with
      | O   => N0
      | S m => Npos (onesp m)
      end.

    Definition wf_onesn (n : nat) : is_wf n (onesn n) :=
      match n with
      | 0    => I
      | S n' => wf_onesp n'
      end.

    Definition ones (n : nat) : bv n :=
      mk (onesn n) (wf_onesn n).

    Lemma zero_S n : @zero (S n) = cons false (@zero n).
    Proof. reflexivity. Qed.

    Lemma app_zero_zero {m n} :
      app (@zero m) (@zero n) = @zero (m + n).
    Proof. induction m; [easy|now rewrite zero_S, app_cons, IHm]. Qed.

    Lemma ones_O : ones 0 = nil.
    Proof. reflexivity. Qed.

    Lemma ones_S n : ones (S n) = cons true (ones n).
    Proof. destruct n; reflexivity. Qed.

    Lemma app_ones_ones {m n} :
      app (ones m) (ones n) = ones (m + n).
    Proof.
      induction m; cbn [plus]; [easy|].
      now rewrite !ones_S, app_cons, IHm.
    Qed.

    Lemma bin_one {n} : n > 0 -> bin (@one n) = 1%N.
    Proof.
      destruct n; cbn; now Lia.lia.
    Qed.

    #[export] Instance bv_inhabited n : Inhabited (bv n) := populate (zero).
  End Constants.

  Section Access.

    Import BinPos.

    Definition lsb {n} (v : bv n) : bool :=
      match v with
      | mk N0          u => false
      | mk (N.pos _~0) _ => false
      | mk (N.pos _~1) _ => true
      | mk (N.pos 1)   _ => true
      end.

    Definition msbwithcarry {n} (c : bool) (v : bv n) : bool :=
      fold_left (fun _ l m => m) c v.

    Lemma msbwithcarry_cons {n} (c b : bool) (x : bv n)  :
      msbwithcarry c (cons b x) = msbwithcarry b x.
    Proof. unfold msbwithcarry. now rewrite fold_left_cons. Qed.

    Lemma msbwithcarry_app {m n} (c : bool) (xs : bv m) (ys : bv n) :
      msbwithcarry c (app xs ys) = msbwithcarry (msbwithcarry c xs) ys.
    Proof. unfold msbwithcarry. apply fold_left_app. Qed.

    Lemma msbwithcarry_ones {k} :
      msbwithcarry true (ones k) = true.
    Proof. induction k; now rewrite ?ones_S, ?msbwithcarry_cons. Qed.

    Lemma msbwithcarry_zero {k} :
      msbwithcarry false (@zero k) = false.
    Proof. now induction k. Qed.

    Definition msb {n} (v : bv n) : bool :=
      msbwithcarry false v.

    Lemma msb_cons (n : nat) (b : bool) (x : bv n) :
      msb (cons b x) = msbwithcarry b x.
    Proof. apply msbwithcarry_cons. Qed.

    Lemma msb_ones n :
      msb (ones (S n)) = true.
    Proof.
      rewrite ones_S, msb_cons.
      apply msbwithcarry_ones.
    Qed.

    Lemma msb_zero n :
      msb (n := n) zero = false.
    Proof. apply msbwithcarry_zero. Qed.

  End Access.

  Section Extend.

    (* Sign extension. A bit awkward for little-endian vectors.  *)
    Definition sext' {m} (v : bv m) n : bv (m + n) :=
      app v (if msb v then ones n else zero).
    (* Zero extension. Equally as awkward. *)
    Definition zext' {m} (v : bv m) n : bv (m + n) :=
      app v zero.

    Variant LeView (m : nat) : nat -> Set :=
      is_le k : LeView m (m + k).

    Fixpoint leview (m n : nat) : IsTrue (m <=? n) -> LeView m n :=
      match m , n with
      | O    , n    => fun _ => is_le O n
      | S m' , O    => fun p => match IsTrue.from p with end
      | S m' , S n' => fun p => match leview m' n' p with
                                | is_le _ k => is_le (S m') k
                                end
      end.
    #[global] Arguments is_le [m] k.
    #[global] Arguments leview _ _ {p}.

    (* Less awkward to use, but some type-level trickery. *)
    Definition sext {m} (v : bv m) {n} {p : IsTrue (m <=? n)} : bv n :=
      match leview m n with is_le k => sext' v k end.
    Definition zext {m} (v : bv m) {n} {p : IsTrue (m <=? n)} : bv n :=
      match leview m n with is_le k => zext' v k end.

    Definition truncate {n} (m : nat) (xs : bv n) {p : IsTrue (m <=? n)} : bv m :=
      match leview m n in LeView _ sl return bv sl -> bv m with
      | is_le k => fun (bits : bv (m + k)) =>
                     let (result, _) := appView m k bits in
                     result
      end xs.
  End Extend.

  Section Integers.

    Open Scope Z_scope.

    Definition unsigned {n} (x : bv n) : Z :=
      Z.of_N (bin x).
    Definition signed {n} (x : bv n) : Z :=
      let u := unsigned x in
      if msb x then u - 2 ^ Z.of_nat n else u.
    Definition truncz (n : nat) := fun y => Z.modulo y (2 ^ Z.of_nat n).
    Definition of_Z {n} (x : Z) : bv n :=
      of_N (Z.to_N (truncz n x)).

    Lemma unsigned_inj {n} (x y : bv n) : unsigned x = unsigned y -> x = y.
    Proof.
      intros.
      now apply bin_inj, Znat.N2Z.inj.
    Qed.

    Lemma truncz_pos n x : 0 <= truncz n x.
    Proof. apply numbers.Z.mod_pos. lia. Qed.

    Definition truncz_idemp (n : nat) (x : Z) :
      truncz n (truncz n x) = truncz n x.
    Proof. unfold truncz. apply Zmod_mod. Qed.

    Lemma truncz_add {n x y} : truncz n (x + y) = truncz n (truncz n x + truncz n y).
    Proof. apply Zplus_mod. Qed.

    Lemma of_N_truncz {n x} : Z.of_N (truncn n x) = truncz n (Z.of_N x).
    Proof.
      unfold truncz. now rewrite truncn_spec, Znat.N2Z.inj_mod, Znat.N2Z.inj_pow, Znat.nat_N_Z.
    Qed.

    Lemma to_N_truncz {n x} : Z.to_N (truncz n (Z.of_N x)) = truncn n x.
    Proof.
      unfold truncz.
      rewrite truncn_spec.
      rewrite Znat.Z2N.inj_mod; try lia.
      rewrite Znat.N2Z.id.
      rewrite Znat.Z2N.inj_pow; try lia.
      repeat f_equal.
      now Lia.lia.
    Qed.

    Lemma to_N_truncz2 {n x} (Hx : 0 <= x) : Z.to_N (truncz n x) = truncn n (Z.to_N x).
    Proof.
      unfold truncz.
      rewrite truncn_spec, Znat.Z2N.inj_mod; f_equal; cbn; lia.
    Qed.

    Lemma unsigned_cons n b (x : bv n) :
      unsigned (cons b x) = Z.b2z b + 2 * unsigned x.
    Proof. destruct b, x; unfold unsigned; cbn; Lia.lia. Qed.

    Lemma unsigned_app m n (x : bv m) (y : bv n) :
      unsigned (app x y) = unsigned x + unsigned y * 2 ^ Z.of_nat m.
    Proof.
      induction x using bv_rect; cbn [plus].
      - rewrite app_nil. cbn. lia.
      - rewrite app_cons, !unsigned_cons, IHx,
                  Znat.Nat2Z.inj_succ, Z.pow_succ_r; lia.
    Qed.

    Lemma unsigned_zero {m} :
      unsigned (@zero m) = 0.
    Proof. reflexivity. Qed.

    Lemma unsigned_ones n :
      unsigned (ones n) = Z.ones (Z.of_nat n).
    Proof.
      induction n; cbn - [ones].
      - reflexivity.
      - rewrite ones_S, unsigned_cons, IHn, Znat.Nat2Z.inj_succ.
        cbn. rewrite !Z.ones_equiv, Z.pow_succ_r; Lia.lia.
    Qed.

    Lemma unsigned_bounds {n} (v : bv n) :
      (0 <= unsigned v < 2 ^ Z.of_nat n)%Z.
    Proof.
      destruct v as [v wf_v]. unfold unsigned. cbn.
      apply is_wf_spec in wf_v.
      lia.
    Qed.

    Lemma msbwithcarry_spec {n} c (x : bv n) :
      msbwithcarry c x =
      match n with
      | O => c
      | S _ => (2 ^ Z.of_nat n <=? 2 * unsigned x)%Z
      end.
    Proof.
      revert c. induction x using bv_rect.
      - reflexivity.
      - intros c. rewrite msbwithcarry_cons.
        rewrite Znat.Nat2Z.inj_succ, Z.pow_succ_r; [|lia].
        rewrite unsigned_cons, IHx. clear IHx.
        destruct n; cbn.
        + rewrite Nat2Z.inj_0, Z.pow_0_r.
          destruct (view x). destruct b; cbn; lia.
        + rewrite Znat.Nat2Z.inj_succ, Z.pow_succ_r; [|lia].
          destruct (view x). rewrite unsigned_cons.
          destruct b; cbn; lia.
    Qed.

    Corollary msb_spec {n} (x : bv n) :
      msb x = (2 ^ Z.of_nat n <=? 2 * unsigned x)%Z.
    Proof.
      unfold msb. rewrite msbwithcarry_spec.
      now induction x using bv_case.
    Qed.

    Lemma signed_zero {m} :
      signed (@zero m) = 0.
    Proof. unfold signed. now rewrite msb_zero. Qed.

    Lemma signed_ones n :
      signed (ones (S n)) = (-1)%Z.
    Proof.
      unfold signed. rewrite msb_ones.
      rewrite unsigned_ones, Z.ones_equiv.
      Lia.lia.
    Qed.

    Corollary signed_spec {n} (x : bv n) :
      signed x =
      (let u := unsigned x in
       if (2 ^ Z.of_nat n <=? 2 * u)
       then u - 2 ^ Z.of_nat n
       else u)%Z.
    Proof. unfold signed. now rewrite msb_spec. Qed.

    Lemma signed_inj {n} (x y : bv n) : signed x = signed y -> x = y.
    Proof.
      pose proof (unsigned_bounds x).
      pose proof (unsigned_bounds y).
      pose proof (unsigned_inj x y).
      rewrite !signed_spec. cbn.
      repeat
        match goal with
          |- context[Z.leb ?x ?y] => destruct (Z.leb_spec x y)
        end; intros; auto; try lia;
        try assert (unsigned x = unsigned y) by lia; auto.
    Qed.

    Lemma signed_bounds {n} (x : bv n) :
      (- 2 ^ (Z.of_nat n) <= 2 * signed x < 2 ^ (Z.of_nat n))%Z.
    Proof.
      pose proof (unsigned_bounds x). rewrite signed_spec. cbn.
      destruct (Z.leb_spec (2 ^ Z.of_nat n) (2 * unsigned x)); lia.
    Qed.

  End Integers.

  Section Extract.

    Definition drop m {n} (x : bv (m + n)) : bv n :=
      let (_,ys) := appView m n x in ys.

    Definition take m {n} (x : bv (m + n)) : bv m :=
      let (xs,_) := appView m n x in xs.

    Lemma drop_cons {m n} b (xs : bv (m + n)) :
      drop (S m) (cons b xs) = drop m xs.
    Proof.
      unfold drop. cbn.
      unfold view. rewrite bv_case_cons.
      destruct appView; cbn.
      now destruct app_cons.
    Qed.

    Lemma drop_app {m n} (x : bv m) (y : bv n) :
      drop m (app x y) = y.
    Proof.
      induction x using bv_rect.
      - now rewrite app_nil.
      - now rewrite app_cons, drop_cons.
    Qed.

    Lemma take_cons {m n} b (xs : bv (m + n)) :
      take (S m) (cons b xs) = cons b (take m xs).
    Proof.
      unfold take. cbn.
      unfold view. rewrite bv_case_cons.
      destruct appView; cbn.
      now destruct app_cons.
    Qed.

    Lemma take_app {m n} (x : bv m) (y : bv n) :
      take m (app x y) = x.
    Proof.
      induction x using bv_rect.
      - now rewrite app_nil.
      - now rewrite app_cons, take_cons; f_equal.
    Qed.

    Lemma take_full {m} (b : bv (m + 0)) :
      take m b = eq_rect (m + 0) bv b m (transparent.nat_add_0_r m).
    Proof.
      induction m; cbn in *.
      * now destruct (view b).
      * rewrite <- rew_map. destruct (view b). rewrite take_cons.
        rewrite IHm. generalize (transparent.nat_add_0_r m). clear.
        generalize dependent (m + 0). intros; now subst.
    Qed.

    Definition vector_subrange {n} (start len : nat)
      {p : IsTrue (start + len <=? n)} : bv n -> bv len :=
      match leview (start + len) n with
      | is_le k => fun bits : bv (start + len + k) =>
                    drop start (take (start + len) bits)
      end.
    #[global] Arguments vector_subrange {n} _ _ {_} _  : simpl never.

    Goal vector_subrange 0 1 (@of_nat 1 1)    = of_nat 1. reflexivity. Abort.
    Goal vector_subrange 0 8 (@of_nat 16 256) = zero.     reflexivity. Abort.
    Goal vector_subrange 8 8 (@of_nat 16 256) = one.      reflexivity. Abort.

    Lemma vector_subrange_S_cons {start len n} (p : IsTrue (start + len <=? n))
                                  (b : bool) (xs : bv n) :
      @vector_subrange (S n) (S start) len p (cons b xs) =
      @vector_subrange n start len p xs.
    Proof.
      unfold vector_subrange; cbn. destruct leview.
      now rewrite take_cons, drop_cons.
    Qed.

    Lemma vector_subrange_0_S_cons {len n} (p : IsTrue (len <=? n))
      (b : bool) (xs : bv n) :
      @vector_subrange (S n) 0 (S len) p (cons b xs) =
      cons b (@vector_subrange _ 0 len p xs).
    Proof.
      unfold vector_subrange; cbn. destruct leview.
      now rewrite take_cons.
    Qed.

  End Extract.

  Section Update.
    Definition update_vector_subrange {n} (start len : nat)
      (p : IsTrue (start + len <=? n)) : bv n -> bv len -> bv n :=
      match leview (start + len) n in LeView _ sl return bv sl -> bv len -> bv sl with
      | is_le k =>
          fun bits upd =>
            let (xs, rest1) := appView (start + len) k bits in
            let (rest2, _) := appView start len xs in
            app (app rest2 upd) rest1
      end.
    #[global] Arguments update_vector_subrange {n} _ _ {_} _ _ : simpl never.

    Goal update_vector_subrange 0 1 (@of_nat 2 0) (of_nat 1) = of_nat 1. reflexivity. Abort.
    Goal update_vector_subrange 0 4 (@of_nat 4 0) (of_nat 15) = of_nat 15. reflexivity. Abort.
    Goal update_vector_subrange 0 4 (@of_nat 8 15) (of_nat 0) = of_nat 0. reflexivity. Abort.
    Goal update_vector_subrange 0 4 (@of_nat 8 255) (of_nat 0) = of_nat 240. reflexivity. Abort.
    Goal update_vector_subrange 4 4 (@of_nat 8 255) (of_nat 0) = of_nat 15. reflexivity. Abort.

    Lemma subrange_same_update_vector_subrange
      {n start len} (p : IsTrue (start + len <=? n)) (xs : bv n) (ys : bv len) :
      vector_subrange start len (update_vector_subrange start len xs ys) = ys.
    Proof.
      unfold vector_subrange, update_vector_subrange.
      destruct leview as [k].
      destruct (appView (start + len) k xs).
      destruct (appView start len xs).
      unfold drop, take.
      now rewrite !appView_app.
    Qed.

    Lemma subrange_before_update_vector_subrange {n start len} (xs : bv n)
      (p : IsTrue (start + len <=? n))
      start_u len_u (p_u : IsTrue (start_u + len_u <=? n)) (ys : bv len_u)
      (q : IsTrue (start + len <=? start_u)) :
      vector_subrange start len (update_vector_subrange start_u len_u xs ys) =
      vector_subrange start len xs.
    Proof.
      destruct (leview (start + len) start_u) as [kpq]. clear q.
      unfold update_vector_subrange.
      destruct leview as [k_u]. clear p_u.
      repeat
        match goal with
        | |- context[appView ?m ?n ?v] =>
            is_var n; is_var v; destruct (appView m n v)
        end.
      rewrite !app_app. destruct nat_add_assoc; cbn.
      generalize (app ys ys0) (app ys1 ys0).
      generalize dependent (len_u + k_u).
      clear. intros k p zs1 zs2.
      destruct (appView _ _ xs).
      rewrite !app_app. destruct nat_add_assoc; cbn.
      generalize (app ys zs1) (app ys zs2).
      generalize dependent (kpq + k).
      clear. intros k p zs1 zs2.
      destruct (appView _ _ xs).
      rewrite !app_app. destruct nat_add_assoc; cbn.
      induction xs using bv_rect; cbn in *.
      - rewrite !app_nil.
        induction ys using bv_rect; cbn; [easy|].
        rewrite !app_cons, !vector_subrange_0_S_cons.
        now f_equal.
      - now rewrite !app_cons, !vector_subrange_S_cons, IHxs.
    Qed.

    Lemma subrange_after_update_vector_subrange {n start len} (xs : bv n)
      (p : IsTrue (start + len <=? n))
      start_u len_u (p_u : IsTrue (start_u + len_u <=? n)) (ys : bv len_u)
      (q : IsTrue (start_u + len_u <=? start)) :
      vector_subrange start len (update_vector_subrange start_u len_u xs ys) =
      vector_subrange start len xs.
    Proof.
      destruct (@leview _ _ q). clear q.
      unfold update_vector_subrange.
      destruct leview as [k_u]. clear p_u.
      repeat
        match goal with
        | |- context[appView ?m ?n ?v] =>
            is_var n; is_var v; destruct (appView m n v)
        end.
      induction xs using bv_rect; cbn in *.
      - rewrite !app_nil.
        induction len_u; cbn in *; destruct (view ys), (view ys1).
        + reflexivity.
        + rewrite !app_cons, !vector_subrange_S_cons. auto.
      - now rewrite !app_cons, !vector_subrange_S_cons, IHxs.
    Qed.

  End Update.

  Section Shift.
    Definition shiftr {m n} (x : bv m) (y : bv n) : bv m :=
      of_Z (Z.shiftr (unsigned x) (unsigned y)).

    Definition shiftl {m n} (x : bv m) (y : bv n) : bv m :=
      of_Z (Z.shiftl (unsigned x) (unsigned y)).
  End Shift.

  Section EqMod2N.
    Definition eq2np (n : nat) := fun x y => trunc n x = trunc n y.
    #[global] Arguments eq2np n x y : simpl never.
    Lemma eq2np_refl {n} : Reflexive (eq2np n).
    Proof. now intros x. Qed.
    Lemma eq2np_sym {n} : Symmetric (eq2np n).
    Proof. now intros x y. Qed.
    Lemma eq2np_trans {n} : Transitive (eq2np n).
    Proof. intros ? ? ?; unfold eq2np; apply transitivity. Qed.
    #[export] Instance eq2np_setoid {n} : Equivalence (eq2np n).
    Proof.
      constructor; auto using eq2np_refl, eq2np_sym, eq2np_trans.
    Qed.
    #[export] Instance eq2np_rewriterelation {n} : RewriteRelation (eq2np n). Defined.

    Definition eq2n (n : nat) := fun x y => truncn n x = truncn n y.
    #[global] Arguments eq2n n x y : simpl never.
    Lemma eq2n_refl {n} : Reflexive (eq2n n).
    Proof. now intros [|px]. Qed.
    Lemma eq2n_sym {n} : Symmetric (eq2n n).
    Proof. now intros [|px] [|py]. Qed.
    Lemma eq2n_trans {n} : Transitive (eq2n n).
    Proof. intros [|px] [|py] [|pz]; unfold eq2n; apply transitivity. Qed.
    #[export] Instance eq2n_setoid {n} : Equivalence (eq2n n).
    Proof.
      constructor; auto using eq2n_refl, eq2n_sym, eq2n_trans.
    Qed.

    Lemma eq2n_zero {x y} : eq2n 0 x y.
    Proof. unfold eq2n. now rewrite ?truncn_zero. Qed.

    #[export] Instance eq2n_rewriterelation {n} : RewriteRelation (eq2n n). Defined.

    Definition eq2nz (n : nat) := fun x y => truncz n x = truncz n y.
    #[global] Arguments eq2nz n x y : simpl never.
    Lemma eq2nz_refl {n} : Reflexive (eq2nz n).
    Proof. now intros. Qed.
    Lemma eq2nz_sym {n} : Symmetric (eq2nz n).
    Proof. now intros. Qed.
    Lemma eq2nz_trans {n} : Transitive (eq2nz n).
    Proof. intros ? ? ?. unfold eq2nz; apply transitivity. Qed.
    #[export] Instance eq2nz_setoid {n} : Equivalence (eq2nz n).
    Proof.
      constructor; auto using eq2nz_refl, eq2nz_sym, eq2nz_trans.
    Qed.

    Lemma truncz_zero {x} : truncz 0 x = 0%Z.
    Proof. unfold truncz. now rewrite Zdiv.Zmod_1_r. Qed.
    Lemma eq2nz_zero {x y} : eq2nz 0 x y.
    Proof. unfold eq2nz. now rewrite ?truncz_zero. Qed.

    #[export] Instance eq2nz_rewriterelation {n} : RewriteRelation (eq2nz n). Defined.

    #[export] Instance trunc_Proper {n} : Proper (eq2np n ==> eq2n n) (trunc n).
    Proof. now intros x y ->. Qed.

    Lemma trunc_eq2n {n p} : eq2n n (trunc n p) (N.pos p).
    Proof.
      unfold eq2n.
      now rewrite truncn_trunc.
    Qed.

    Lemma truncn_eq2n {n x} : eq2n n (truncn n x) x.
    Proof.
      unfold eq2n.
      now apply truncn_idemp.
    Qed.

    Lemma truncz_eq2nz {n x} : eq2nz n (truncz n x) x.
    Proof.
      unfold eq2nz.
      now apply truncz_idemp.
    Qed.

    #[export] Instance truncn_Proper {n : nat} : Proper (eq2n n ==> eq) (truncn n).
    Proof. now intros x y H. Qed.

    #[export] Instance truncz_Proper {n : nat} : Proper (eq2nz n ==> eq) (truncz n).
    Proof. now intros x y H. Qed.

    #[export] Instance of_N_Proper {n} : Proper (eq2n n ==> eq) (@of_N n).
    Proof. intros x y e. now apply noConfusion. Qed.

    #[export] Instance of_Z_Proper {n} : Proper (eq2nz n ==> eq) (@of_Z n).
    Proof. unfold of_Z. now intros x y <-. Qed.

    Lemma of_Z_unsigned n v : @of_Z n (unsigned v) = v.
    Proof.
      unfold unsigned, of_Z.
      rewrite to_N_truncz, truncn_eq2n.
      now rewrite bv.of_N_bin.
    Qed.

    Lemma unsigned_of_Z {n} (x : Z) : @unsigned n (of_Z x) = truncz n x.
    Proof.
      unfold of_Z, unsigned; cbn.
      pose proof (truncz_pos n x).
      now rewrite <-to_N_truncz2, truncz_idemp, Znat.Z2N.id.
    Qed.

    Lemma of_Z_signed n (v : bv n) :
      of_Z (signed v) = v.
    Proof.
      rewrite signed_spec. cbn.
      destruct (Z.leb_spec (2 ^ Z.of_nat n) (2 * unsigned v)).
      - unfold of_Z, truncz.
        rewrite Zdiv.Zminus_mod, Zdiv.Z_mod_same_full.
        rewrite Z.sub_0_r, Zmod_mod. apply of_Z_unsigned.
      - apply of_Z_unsigned.
    Qed.

    Lemma signed_eq_z {n} (x : bv n) z :
      signed x = z <-> ((- 2 ^ (Z.of_nat n) <= 2 * z < 2 ^ (Z.of_nat n))%Z
                        /\ x = of_Z z).
    Proof.
      split.
      - intros <-. split. apply signed_bounds. now rewrite of_Z_signed.
      - intros [[Hl Hu] ->]. rewrite signed_spec, unsigned_of_Z.
        unfold truncz.
        destruct (Z.ltb_spec z 0).
        + assert (z mod 2 ^ Z.of_nat n = (z + 2 ^ Z.of_nat n) mod 2 ^ Z.of_nat n)%Z as ->.
          rewrite Z.add_mod, Z_mod_same_full, Z.add_0_r, Zmod_mod; try lia.
          rewrite Zmod_small; try lia.
          destruct (Z.leb_spec (2 ^ Z.of_nat n) (2 * (z + 2 ^ Z.of_nat n))); lia.
        + rewrite Zmod_small; try lia.
          destruct (Z.leb_spec (2 ^ Z.of_nat n) (2 * z)); lia.
    Qed.

    Lemma of_Z_nat {n} i : @of_Z n (Z.of_nat i) = of_nat i.
    Proof.
      unfold of_nat, of_Z.
      now rewrite <-Znat.nat_N_Z, to_N_truncz, truncn_eq2n.
    Qed.

    #[export] Instance Z_of_N_Proper {n} : Proper (eq2n n ==> eq2nz n) Z.of_N.
    Proof.
      unfold eq2nz, eq2n.
      intros x y Hxy.
      unfold truncz.
      rewrite ?truncn_spec in Hxy.
      rewrite <- Znat.nat_N_Z.
      change 2%Z with (Z.of_N 2%N).
      rewrite <- Znat.N2Z.inj_pow.
      rewrite <-?Znat.N2Z.inj_mod.
      now rewrite Hxy.
    Qed.

    #[export] Instance double_proper {n} : Proper (eq2n n ==> eq2n (S n)) N.double.
    Proof.
      intros x x' Hx.
      unfold eq2n.
      now rewrite ?truncn_double, Hx.
    Qed.

    Lemma eq2n_exp2 {n} : eq2n n (exp2 n) 0.
    Proof.
      induction n; cbn.
      - apply eq2n_zero.
      - now rewrite ?exp2_S, IHn.
    Qed.

    #[export] Instance succ_double_proper {n} : Proper (eq2n n ==> eq2n (S n)) N.succ_double.
    Proof.
      intros x x' Hx.
      unfold eq2n.
      now rewrite ?truncn_succ_double, Hx.
    Qed.

    Lemma eq2n_to_eq_lt n {x y} : (x < exp2 n)%N -> (y < exp2 n)%N -> eq2n n x y -> x = y.
    Proof.
      unfold eq2n.
      rewrite ?truncn_spec.
      intros xle yle xmeqy.
      rewrite (N.div_mod x (exp2 n)); try apply exp2_nzero.
      rewrite (N.div_mod y (exp2 n)); try apply exp2_nzero.
      rewrite xmeqy.
      do 2 f_equal.
      now rewrite ?N.div_small.
    Qed.

    Lemma eq2nz_to_eq_lt n {x y} :
      (0 <= x < 2 ^ Z.of_nat n)%Z ->
      (0 <= y < 2 ^ Z.of_nat n)%Z ->
      eq2nz n x y -> eq x y.
    Proof.
      unfold eq2nz, truncz.
      intros xle yle xmeqy.
      rewrite (Z.div_mod x (2 ^ Z.of_nat n)); try Lia.lia.
      rewrite (Z.div_mod y (2 ^ Z.of_nat n)); try Lia.lia.
      rewrite xmeqy.
      do 2 f_equal.
      now rewrite ?Z.div_small.
    Qed.

    Lemma unsigned_inj_eq2nz {n x y} : eq2nz n (@unsigned n x) (unsigned y) -> x = y.
    Proof.
      intros Hbxy.
      now rewrite <-(of_Z_unsigned x), <-(of_Z_unsigned y), Hbxy.
    Qed.

    #[export] Instance unsigned_Proper {n} : Proper (eq ==> eq2nz n) (@unsigned n).
    Proof.
      now intros x y <-.
    Qed.
  End EqMod2N.
  Section Arithmetic.

    Definition add {n} (x y : bv n) : bv n :=
      of_N (N.add (bin x) (bin y)).

    Definition negate {n} (x : bv n) : bv n := of_N (exp2 n - bin x).

    Definition sub {n} (x y : bv n) : bv n := add x (negate y).

    Definition mul {n} (x y : bv n) : bv n :=
      of_N (N.mul (bin x) (bin y)).

    Lemma bin_of_N_eq2n {n x} : eq2n n (@bin n (@of_N n x)) x.
    Proof.
      destruct x; cbn;
        now auto using trunc_eq2n.
    Qed.

    Lemma truncn_add : forall {n x y}, eq2n n (x + y) (truncn n x + truncn n y).
    Proof.
      intros n x y. unfold eq2n.
      rewrite ?truncn_spec.
      now apply N.Div0.add_mod.
    Qed.

    #[export] Instance Nadd_Proper {n} : Proper (eq2n n ==> eq2n n ==> eq2n n) N.add.
    Proof.
      intros x x' eqx y y' eqy.
      unfold eq2n.
      rewrite (@truncn_add n x y).
      rewrite eqx, eqy.
      now rewrite <-(@truncn_add n x' y').
    Qed.

    #[export] Instance Zadd_Proper {n} : Proper (eq2nz n ==> eq2nz n ==> eq2nz n) Z.add.
    Proof.
      intros x x' eqx y y' eqy.
      unfold eq2nz.
      rewrite (@truncz_add n x y).
      rewrite eqx, eqy.
      now rewrite <-(@truncz_add n x' y').
    Qed.

    Lemma truncz_sub : forall {n x y}, eq2nz n (x - y) (truncz n x - truncz n y).
    Proof.
      intros n x y. unfold eq2nz, truncz.
      now rewrite <-Zdiv.Zminus_mod.
    Qed.

    Lemma truncz_mul : forall {n x y}, eq2nz n (x * y) (truncz n x * truncz n y).
    Proof.
      intros n x y. unfold eq2nz, truncz.
      now rewrite <-Zdiv.Zmult_mod.
    Qed.

    #[export] Instance Zsub_Proper_eq2nz {n} : Proper (eq2nz n ==> eq2nz n ==> eq2nz n) Z.sub.
    Proof.
      unfold eq2nz.
      intros x1 x2 Hx y1 y2 Hy.
      now rewrite truncz_sub, Hx, Hy, <-truncz_sub.
    Qed.

    #[export] Instance Zopp_Proper_eq2nz {n} : Proper (eq2nz n ==> eq2nz n) Z.opp.
    Proof.
      intros x1 x2 Hx.
      replace (- x1)%Z with (0 - x1)%Z by Lia.lia.
      replace (- x2)%Z with (0 - x2)%Z by Lia.lia.
      now rewrite Hx.
    Qed.

    #[export] Instance Zmul_Proper_eq2nz {n} : Proper (eq2nz n ==> eq2nz n ==> eq2nz n) Z.mul.
    Proof.
      unfold eq2nz.
      intros x1 x2 Hx y1 y2 Hy.
      now rewrite truncz_mul, Hx, Hy, <-truncz_mul.
    Qed.

    #[export] Instance bin_Proper {n} : Proper (eq ==> eq2n n) (@bin n).
    Proof.
      now intros x y <-.
    Qed.

    Lemma bin_inj_eq2n {n x y} : eq2n n (@bin n x) (bin y) -> x = y.
    Proof.
      intros Hbxy.
      now rewrite <-(of_N_bin x), <-(of_N_bin y), Hbxy.
    Qed.

    Lemma eq2R `{Reflexive A R} {x y} : x = y -> R x y.
    Proof. now induction 1. Qed.

    Local Ltac solve_eq2n := (apply bin_inj_eq2n; cbn; rewrite ?truncn_eq2n; apply eq2R; try Lia.lia).

    Lemma bin_add : forall {n} {x y : bv n}, bin (add x y) = ((bin x + bin y) mod exp2 n)%N.
    Proof. intros. now apply truncn_spec. Qed.

    Lemma add_comm {n} {x y}: @add n x y = @add n y x.
    Proof. solve_eq2n. Qed.

    Lemma add_assoc {n} {x y z}: @add n x (add y z) = @add n (add x y) z.
    Proof. solve_eq2n. Qed.

    Lemma add_zero_r {n} {x} : @add n x zero = x.
    Proof. solve_eq2n. Qed.

    Lemma add_zero_l {n} {x} : @add n zero x = x.
    Proof. solve_eq2n. Qed.

    Lemma add_negate {n} {y} : @add n (negate y) y = zero.
    Proof.
      apply bin_inj_eq2n; cbn.
      rewrite ?truncn_eq2n.
      rewrite N.sub_add.
      - now apply eq2n_exp2.
      - enough (bin y < exp2 n)%N by Lia.lia.
        apply is_wf_spec.
        now destruct y.
    Qed.

    Lemma add_negate2 {n} {y} : @add n y (negate y) = zero.
    Proof.
      now rewrite add_comm, add_negate.
    Qed.

    Lemma add_cancel_l {n} {x y z} : @add n x y = add x z -> y = z.
    Proof.
      intros eq.
      apply (f_equal (add (negate x))) in eq.
      now rewrite ?add_assoc, ?add_negate, ?add_zero_l in eq.
    Qed.

    Lemma add_cancel_r {n} {x y z} : @add n x z = add y z -> x = y.
    Proof.
      intros eq.
      apply (f_equal (fun y => add y (negate z))) in eq.
      now rewrite <-?add_assoc, ?add_negate2, ?add_zero_r in eq.
    Qed.

    Lemma of_N_add {n} x y : @add n (of_N x) (of_N y) = of_N (x + y).
    Proof.
      apply bin_inj. cbn. now rewrite <-truncn_add. Qed.

    Lemma of_Z_add {n} x y : @add n (of_Z x) (of_Z y) = of_Z (x + y).
    Proof.
      unfold of_Z. rewrite of_N_add.
      apply bin_inj. cbn.
      pose proof (truncz_pos n x).
      pose proof (truncz_pos n y).
      rewrite <-Znat.Z2N.inj_add; try easy.
      repeat (rewrite <-to_N_truncz, Znat.Z2N.id); try easy; try apply truncz_pos; try Lia.lia.
      now rewrite <-truncz_add, truncz_idemp.
    Qed.

    Lemma truncn_mul : forall {n x y}, eq2n n (x * y) (truncn n x * truncn n y).
    Proof.
      intros n x y. unfold eq2n.
      now rewrite ?truncn_spec, <-N.Div0.mul_mod.
    Qed.

    Lemma of_Z_mul {n} x y : @mul n (of_Z x) (of_Z y) = of_Z (x * y).
    Proof.
      apply unsigned_inj_eq2nz.
      rewrite unsigned_of_Z, truncz_eq2nz.
      unfold unsigned, mul; cbn.
      pose proof (truncz_pos n y).
      pose proof (truncz_pos n x).
      rewrite <-?to_N_truncz2, ?truncz_eq2nz; try easy.
      rewrite <-Znat.Z2N.inj_mul; try easy.
      rewrite <-to_N_truncz2; try Lia.lia.
      rewrite Znat.Z2N.id; [|apply truncz_pos].
      now rewrite ?truncz_eq2nz.
    Qed.


    #[export] Instance Nmul_Proper {n} : Proper (eq2n n ==> eq2n n ==> eq2n n) N.mul.
    Proof.
      intros x x' eqx y y' eqy.
      unfold eq2n.
      rewrite truncn_mul, eqx, eqy.
      now rewrite <-truncn_mul.
    Qed.

    Lemma mul_comm {n} {x y}: @mul n x y = @mul n y x.
    Proof. solve_eq2n. Qed.

    Lemma mul_assoc {n} {x y z}: @mul n x (mul y z) = @mul n (mul x y) z.
    Proof. solve_eq2n. Qed.

    Lemma mul_one_r {n} {x}: @mul n x one = x.
    Proof.
      apply bin_inj_eq2n; cbn.
      rewrite truncn_mul, !truncn_eq2n.
      destruct n; cbn; [apply eq2n_zero|].
      apply eq2R. Lia.lia.
    Qed.

    Lemma mul_one_l {n} {x}: @mul n one x = x.
    Proof.
      apply bin_inj_eq2n; cbn.
      rewrite truncn_mul, !truncn_eq2n.
      destruct n; cbn; [apply eq2n_zero|].
      apply eq2R. Lia.lia.
    Qed.

    Lemma mul_add_distrib_r {n} {x y z} : @mul n (add x y) z = add (mul x z) (mul y z).
    Proof. solve_eq2n. Qed.

    Lemma ring_theory n : ring_theory (R := bv n) zero one add mul sub negate eq.
    Proof.
      constructor;
        eauto using add_zero_l, add_comm, add_assoc, mul_one_l, mul_comm, mul_assoc, mul_add_distrib_r, add_negate2.
    Qed.
    (* Once you have a fixed n, you can Add Ring BitVector : (bv.ring_theory n).  and then use the ring tactic. *)

    (* Definition succ {n} : bv n -> bv n := add (one n). *)

    Lemma of_nat_S {n} (k : nat) :
      @of_nat n (S k) = add one (of_nat k).
    Proof.
      apply bin_inj.
      cbn -[truncn].
      replace (bin one) with (truncn n 1) by now destruct n.
      rewrite <-truncn_add.
      f_equal.
      Lia.lia.
    Qed.

    Lemma add_of_nat_0_l :
      forall {n} (v : bv n), v = add (of_nat 0) v.
    Proof.
      intros.
      unfold of_nat.
      simpl.
      symmetry.
      apply add_zero_l.
    Qed.

    Lemma add_of_nat_0_r :
      forall {n} (v : bv n), v = add v (bv.of_nat 0).
    Proof. intros; rewrite add_comm; apply add_of_nat_0_l. Qed.

    Lemma unsigned_add {n} x y : @unsigned n (add x y) = truncz n (unsigned x + unsigned y).
    Proof.
      unfold unsigned; cbn.
      rewrite truncn_add, truncz_add, truncn_add.
      now rewrite <-?of_N_truncz, <-Znat.N2Z.inj_add, <-?of_N_truncz, ?truncn_idemp.
    Qed.

    (* A view on the possible outcomes of an unsigned integer addition. *)
    Variant UnsignedAddView {n} (u v : bv n) : Z -> Prop :=
    | UnsignedAddNoOverflow (p : (unsigned u + unsigned v < 2 ^ Z.of_nat n)%Z) :
      UnsignedAddView u v (unsigned u + unsigned v)%Z
    | UnsignedAddOverflow (p : (2 ^ Z.of_nat n <= unsigned u + unsigned v)%Z) :
      UnsignedAddView u v (unsigned u + unsigned v - 2 ^ Z.of_nat n)%Z.

    Definition unsigned_add_view {n} (u v : bv n) :
      UnsignedAddView u v (unsigned (add u v)).
    Proof.
      destruct (Z.ltb_spec (unsigned u + unsigned v) (2 ^ Z.of_nat n)).
      - enough (unsigned (add u v) = unsigned u + unsigned v)%Z as ->.
        + now constructor.
        + destruct u as [u wf_u], v as [v wf_v].
          unfold unsigned, add, of_N in *; cbn in *.
          rewrite of_N_truncz. unfold truncz.
          rewrite Zmod_small; lia.
      - enough (unsigned (add u v) = unsigned u + unsigned v - 2 ^ Z.of_nat n)%Z as ->.
        + now constructor.
        + destruct u as [u wf_u], v as [v wf_v].
          unfold unsigned, add, of_N in *; cbn in *.
          rewrite of_N_truncz. unfold truncz.
          rewrite Znat.N2Z.inj_add.
          apply is_wf_spec in wf_u. apply is_wf_spec in wf_v.
          Zify.zify.
          remember (Z.of_nat n) as e.
          remember (Z.of_N u) as x.
          remember (Z.of_N v) as y.
          clear n u v Heqe Heqx Heqy.
          assert (0 <= x + y - 2 ^ e < 2 ^ e)%Z as <-%Zmod_small by lia.
          now rewrite Zminus_mod, Z_mod_same_full, Z.sub_0_r, Zmod_mod.
    Qed.

    Lemma unsigned_negate {n} x : @unsigned n (negate x) = truncz n (- (unsigned x)).
    Proof.
      unfold negate, unsigned, truncz; cbn.
      generalize (bv_is_wf x).
      rewrite ?truncn_spec.
      intros Hx.
      assert (2 ^ Z.of_nat n ≠ 0)%Z by Lia.lia.
      rewrite ?Znat.N2Z.inj_mod, ?Znat.N2Z.inj_pow.
      rewrite Znat.N2Z.inj_sub; [|Lia.lia].
      rewrite ?Znat.N2Z.inj_pow, ?Znat.nat_N_Z.
      cbn.
      rewrite Zdiv.Zminus_mod, Zdiv.Z_mod_same_full.
      change (0)%Z with (0 mod 2 ^ Z.of_nat n)%Z.
      now rewrite <-Zdiv.Zminus_mod.
    Qed.

    Lemma of_Z_negate {n} x : @negate n (of_Z x) = of_Z (- x).
    Proof.
      apply unsigned_inj_eq2nz.
      rewrite unsigned_of_Z.
      rewrite unsigned_negate.
      now rewrite unsigned_of_Z, ?truncz_eq2nz.
    Qed.

    Lemma unsigned_sub {n} x y : @unsigned n (sub x y) = truncz n (unsigned x - unsigned y).
    Proof.
      unfold sub.
      rewrite unsigned_add, unsigned_negate.
      now rewrite (truncz_eq2nz (x := - unsigned y)).
    Qed.

    Lemma of_Z_sub {n} x y : @sub n (of_Z x) (of_Z y) = of_Z (x - y).
    Proof.
      apply unsigned_inj_eq2nz.
      rewrite unsigned_of_Z, truncz_eq2nz.
      rewrite unsigned_sub, ?unsigned_of_Z.
      now rewrite <-truncz_sub, truncz_eq2nz.
    Qed.

    Lemma unsigned_mul {n} x y : @unsigned n (mul x y) = truncz n (unsigned x * unsigned y).
    Proof.
      now rewrite <-unsigned_of_Z, <-of_Z_mul, ?of_Z_unsigned.
    Qed.

    (* For the relational operators we default to the < and <= version and
       only allow the others for parsing. *)
    Definition uleb {n} (x y : bv n) : bool := N.leb (bin x) (bin y).
    Definition ultb {n} (x y : bv n) : bool := N.ltb (bin x) (bin y).
    Definition sleb {n} (x y : bv n) : bool := Z.leb (signed x) (signed y).
    Definition sltb {n} (x y : bv n) : bool := Z.ltb (signed x) (signed y).
    Definition ule {n} (x y : bv n) : Prop := N.le (bin x) (bin y).
    Definition ult {n} (x y : bv n) : Prop := N.lt (bin x) (bin y).
    Definition sle {n} (x y : bv n) : Prop := Z.le (signed x) (signed y).
    Definition slt {n} (x y : bv n) : Prop := Z.lt (signed x) (signed y).

    Definition sle_spec {n} (v1 v2 : bv n) : reflect (sle v1 v2) (sleb v1 v2) :=
      Z.leb_spec0 (signed v1) (signed v2).
    Definition slt_spec {n} (v1 v2 : bv n) : reflect (slt v1 v2) (sltb v1 v2) :=
      Z.ltb_spec0 (signed v1) (signed v2).
    Definition ule_spec {n} (v1 v2 : bv n) : reflect (ule v1 v2) (uleb v1 v2) :=
      N.leb_spec0 (bin v1) (bin v2).
    Definition ult_spec {n} (v1 v2 : bv n) : reflect (ult v1 v2) (ultb v1 v2) :=
      N.ltb_spec0 (bin v1) (bin v2).

    Definition ugeb {n} (x y : bv n) : bool := uleb y x.
    Definition ugtb {n} (x y : bv n) : bool := ultb y x.
    Definition sgeb {n} (x y : bv n) : bool := sleb y x.
    Definition sgtb {n} (x y : bv n) : bool := sltb y x.
    Definition uge {n} (x y : bv n) : Prop := ule y x.
    Definition ugt {n} (x y : bv n) : Prop := ult y x.
    Definition sge {n} (x y : bv n) : Prop := ule y x.
    Definition sgt {n} (x y : bv n) : Prop := ult y x.

    (* Unfold these automaticall when fully applied. *)
    #[global] Arguments ugeb {n} x y /.
    #[global] Arguments ugtb {n} x y /.
    #[global] Arguments sgeb {n} x y /.
    #[global] Arguments sgtb {n} x y /.
    #[global] Arguments uge {n} x y /.
    #[global] Arguments ugt {n} x y /.
    #[global] Arguments sge {n} x y /.
    #[global] Arguments sgt {n} x y /.

  End Arithmetic.

  Section Sequencing.
    Import stdpp.list_numbers.

    (* not sure why we don't use exp2 here? *)
    Definition bv_modulus (n : nat) : Z := 2 ^ (Z.of_nat n).

    Lemma exp2_bv_modulus {n} : bv_modulus n = Z.of_N (exp2 n).
    Proof. unfold bv_modulus. now lia. Qed.

    Definition bv_seq {n : nat} (start : bv n) (len : Z) : list (bv n) :=
      (fun i : Z => add start (bv.of_Z i)) <$> (seqZ 0 len).
  End Sequencing.

  Section Logical.

    Definition land {n} (x y : bv n) : bv n :=
      of_N (N.land (bin x) (bin y)).

    Definition lor {n} (x y : bv n) : bv n :=
      of_N (N.lor (bin x) (bin y)).

    Definition lxor {n} (x y : bv n) : bv n :=
      of_N (N.lxor (bin x) (bin y)).

    Fixpoint notp (n : nat) (p : positive) : N :=
      match n with
      | O   => N0
      | S n => match p with
               | 1   => N.double (onesn n)
               | p~0 => N.succ_double (notp n p)
               | p~1 => N.double (notp n p)
               end%positive
      end.

    Fixpoint wf_notp (n : nat) p0 : is_wf n (notp n p0) :=
      match n with
      | O => I
      | S n =>
          match p0
          with
          | 1   => wf_double n (onesn n) (wf_onesn n)
          | p~0 => wf_succ_double n (notp n p) (wf_notp n p)
          | p~1 => wf_double n (notp n p) (wf_notp n p)
          end%positive
      end.

    Definition notn (n : nat) (x : N) : N :=
      match x with
      | N0 => onesn n
      | Npos p => notp n p
      end.

    Definition wf_notn n x : is_wf n (notn n x) :=
      match x with
      | N0     => wf_onesn n
      | Npos p => wf_notp n p
      end.

    Definition not {n} (x : bv n) : bv n :=
      let x := bin x in mk (notn n x) (wf_notn n x).

    Lemma not_nil :
      not nil = nil.
    Proof. reflexivity. Qed.

    Lemma not_cons {n} (b : bool) (x : bv n) :
      not (cons b x) = cons (negb b) (not x).
    Proof. destruct x as [[] wfx], b; cbn; try easy. now destruct n. Qed.

    Lemma not_app {m n} (xs : bv m) (ys : bv n) :
      not (app xs ys) = app (not xs) (not ys).
    Proof.
      induction xs using bv_rect; cbn;
        repeat rewrite ?not_nil, ?app_nil, ?not_cons, ?app_cons; congruence.
    Qed.

    Lemma not_ones {n} :
      not (ones n) = zero.
    Proof.
      induction n; cbn; [easy|].
      now rewrite ones_S, not_cons, IHn.
    Qed.

  End Logical.

  Module finite.

    Fixpoint enumV {V : forall k : nat, Type} (c : forall k, bool -> V k -> V (S k))
      (n : V O) (m : nat) {struct m} : list (V m) :=
      match m with
      | O   => Datatypes.cons n Datatypes.nil
      | S m => Datatypes.app
                 (enumV (fun k => c (S k)) (c O false n) m)
                 (enumV (fun k => c (S k)) (c O true n) m)
      end.

    Lemma enumV_length {V : forall k : nat, Type} (c : forall k, bool -> V k -> V (S k)) (n : V O) (m : nat) :
      length (enumV c n m) = 2 ^ m.
    Proof.
      revert V c n. induction m; intros V c n.
      - reflexivity.
      - specialize (IHm (fun k => V (S k)) (fun k => c (S k))).
        cbn. now rewrite List.app_length, !IHm, Nat.add_0_r.
    Qed.

    Lemma enumV_inj {V : forall k : nat, Type} (c : forall k, bool -> V k -> V (S k))
      (c_inj : forall k b1 b2 v1 v2, c k b1 v1 = c k b2 v2 -> b1 = b2 /\ v1 = v2)
      (n1 n2 : V O) (m : nat) :
      enumV c n1 m = enumV c n2 m -> n1 = n2.
    Proof.
      revert V c c_inj n1 n2. induction m; intros V c c_inj n1 n2.
      - intros H%noConfusion_inv%(f_equal pr1). exact H.
      - cbn [enumV]. intros [H1 H2]%list.app_inj_1.
        apply (IHm (fun k => V (S k)) (fun k => c (S k))) in H1.
        + now apply c_inj in H1.
        + intros k. apply c_inj.
        + do 2 rewrite (@enumV_length (fun k => V (S k))).
          reflexivity.
    Qed.

    Lemma enumV_disjoint {V : forall k : nat, Type} (c : forall k, bool -> V k -> V (S k))
      (c_inj : forall k b1 b2 v1 v2, c k b1 v1 = c k b2 v2 -> b1 = b2 /\ v1 = v2)
      (n1 n2 : V O) (Heq : n1 <> n2) (m : nat) :
      forall (x : V m),
        elem_of_list x (enumV c n1 m) ->
        elem_of_list x (enumV c n2 m) -> False.
    Proof.
      revert V c c_inj n1 n2 Heq. induction m; intros V c c_inj n1 n2 Heq; cbn [enumV].
      - intros x xIn1%list.elem_of_list_singleton xIn2% list.elem_of_list_singleton.
        congruence.
      - specialize (IHm (fun k => V (S k)) (fun k => c (S k)) (fun k => c_inj (S k))).
        intros x [in1|in1]%list.elem_of_app [in2|in2]%list.elem_of_app;
          refine (IHm _ _ _ x in1 in2); intros []%c_inj; congruence.
    Qed.

    Lemma nodup_enumV {V : forall k : nat, Type} (c : forall k, bool -> V k -> V (S k))
      (c_inj : forall k b1 b2 v1 v2, c k b1 v1 = c k b2 v2 -> b1 = b2 /\ v1 = v2)
      (n : V O) (m : nat) : NoDup (enumV c n m).
    Proof.
      revert V c c_inj n. induction m; intros V c c_inj n; cbn [enumV].
      - apply list.NoDup_singleton.
      - specialize (IHm (fun k => V (S k)) (fun k => c (S k)) (fun k => c_inj (S k))).
        apply list.NoDup_app. repeat apply conj; auto.
        cbv - [enumV]. intros x.
        apply (@enumV_disjoint (fun k => V (S k)) (fun k => c (S k)) (fun k => c_inj (S k))).
        intros []%c_inj; congruence.
    Qed.

    Lemma elem_of_enumV {V : forall k : nat, Type} (c : forall k, bool -> V k -> V (S k)) (n : V O) (m : nat) :
      forall (b : bool) (x : V m),
        elem_of x (enumV c n m) ->
        elem_of (c m b x) (enumV c n (S m)).
    Proof.
      revert V c n. induction m; cbn; intros V c n b x xIn.
      - apply list.elem_of_list_singleton in xIn. subst x.
        destruct b; repeat constructor.
      - rewrite ?list.elem_of_app. rewrite list.elem_of_app in xIn.
        destruct xIn as [xIn|xIn];
          specialize (IHm (fun k => V (S k)) (fun k => c (S k)) _ b _ xIn);
          cbn in IHm; rewrite list.elem_of_app in IHm; intuition auto.
    Qed.

    Definition enum (n : nat) : list (bv n) :=
      enumV cons nil n.

    Lemma nodup_enum (n : nat) : base.NoDup (enum n).
    Proof. apply (nodup_enumV cons); intros *; apply cons_inj. Qed.

    Lemma elem_of_enum (m : nat) (x : bv m) : base.elem_of x (enum m).
    Proof.
      induction x using bv_rect.
      - now apply list.elem_of_list_singleton.
      - now apply elem_of_enumV.
    Qed.

    #[export] Instance finite_bv {n} : finite.Finite (bv n) :=
      {| stdpp.finite.enum         := enum n;
         stdpp.finite.NoDup_enum   := nodup_enum n;
         stdpp.finite.elem_of_enum := @elem_of_enum n;
      |}.

  End finite.

  Module countable.
    Import countable.
    #[export] Instance countable_bv {n} : Countable (bv n) :=
      {| encode x        := encode (bin x);
         decode p        := option.map of_N (decode p);
         decode_encode x := eq_trans
                              (f_equal (option.map of_N) (decode_encode (bin x)))
                              (f_equal Some (of_N_bin x));
      |}.
  End countable.

  (* Big-endian bit strings (radix 2 strings). This type is defined by recursion
     over the number of bits and is less efficient than the subtype
     representation. The intended use case is exhaustive pattern matching over
     small bit vectors, i.e. up to ~7-8 bits. It can also be used to define
     constants of medium sized bit vectors (256-bits or so), but should be
     avoided for large bit vectors. *)
  Module bitstring.

    Local Set Transparent Obligations.

    (* A raw representation of bit string intended for the definition of the
       number notation. *)
    Inductive raw : Set := rI (_:raw) | rO (_:raw) | rN.
    Variant null : Set := bN.
    Derive NoConfusion EqDec for null.

    Section Digit.
      Context {A : Set} {eqA : EqDec A}.
      Variant digit : Set :=
      | bO (_:A) | bI (_:A).
      Derive NoConfusion EqDec for digit.
    End Digit.
    Global Arguments digit : clear implicits.

    (* Parse a decimal number into a raw bit string, failing if any digit other
       than 0 or 1 is used. This doesn't check the length of the decimal. *)
    Definition of_uint (u : Number.uint) : option raw :=
      let fix f (u : Decimal.uint) : option raw :=
        match u with
        | Decimal.Nil  => Some rN
        | Decimal.D0 u => option_map rO (f u)
        | Decimal.D1 u => option_map rI (f u)
        | _ => None
        end
      in match u with
         | Number.UIntDecimal u => f u
         | Number.UIntHexadecimal _ => None
         end.

    (* Unparse the given raw bit string. *)
    Definition to_uint (r : raw) : Number.uint :=
      let fix f (r : raw) : Decimal.uint :=
        match r with
        | rI r => Decimal.D1 (f r)
        | rO r => Decimal.D0 (f r)
        | rN   => Decimal.Nil
        end
      in Number.UIntDecimal (f r).

  End bitstring.

  Fixpoint bitstring (n : nat) : Set :=
    match n with
    | O   => bitstring.null
    | S n => bitstring.digit (bitstring n)
    end.

  Fixpoint bitstring_zeroes (n : nat) : bitstring n :=
    match n with
    | O   => bitstring.bN
    | S n => bitstring.bO (bitstring_zeroes n)
    end.

  Fixpoint fold_left_nat [A : forall n : nat, Type]
    (s : forall n, A n -> A (S n)) (z : A O) (m : nat) {struct m} : A m :=
    match m as n return (A n) with
    | O   => z
    | S n => fold_left_nat (fun k => s (S k)) (s 0 z) n
    end.

  Fixpoint fold_left_positive [A : forall n : nat, Type]
    (cI : forall n, A n -> A (S n))
    (cO : forall n, A n -> A (S n))
    (n : A O) {m : nat} (p : positive) {struct m} : A m :=
    match m with
    | O => n
    | S m =>
        match p with
        | xI p => fold_left_positive (fun k => cI (S k)) (fun k => cO (S k)) (cI 0 n) p
        | xO p => fold_left_positive (fun k => cI (S k)) (fun k => cO (S k)) (cO 0 n) p
        | xH   => fold_left_nat (fun k => cO (S k)) (cI 0 n) m
        end
    end.

  (* The subtype representation is little-endian while bitstring are big-endian.
     So use a fold-left to reverse the order *)
  Definition to_bitstring {n} (x : bv n) : bitstring n :=
    match x with
    | mk N0 _        => bitstring_zeroes n
    | mk (N.pos p) _ => fold_left_positive
                          (fun k => @bitstring.bI (bitstring k))
                          (fun k => @bitstring.bO (bitstring k))
                          bitstring.bN p
    end.

  Fixpoint fold_bitstring_left {A : forall k : nat, Type}
    (c : forall k, A k -> bool -> A (S k)) (n : A O)
    [m] {struct m} : forall (xs : bitstring m), A m :=
    match m with
    | O   => fun _ => n
    | S m =>
        fun xs =>
          match match xs with
                | bitstring.bO a => (false,a)
                | bitstring.bI a => (true,a)
                end with
          | (b,a) =>
              fold_bitstring_left (fun k => c (S k)) (c 0 n b) a
          end
    end.

  Definition of_bitstring : forall n, bitstring n -> bv n :=
    fold_bitstring_left (A := bv) (fun _ x b => cons b x) nil.

  Arguments to_bitstring [n] & _%_bv.
  Arguments of_bitstring [n] & _%_bits.

  Module Import notations.
    Open Scope bv_scope.
    Open Scope bv_bitstring_scope.

    (* Coq doesn't like the fixpoint definition of bitstrings. Squelch the
       warnings. *)
    Local Set Warnings "-via-type-mismatch -via-type-remapping".

    (* Number notation for bitstrings. This is a combination of the "Number
       Notation for radix 3" and "Number Notation with implicit arguments"
       examples given in
       https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#number-notations
    *)
    Number Notation bitstring bitstring.of_uint bitstring.to_uint
           (via bitstring.raw mapping
                [[bitstring.bI] => bitstring.rI,
                 [bitstring.bO] => bitstring.rO,
                 [bitstring.bN] => bitstring.rN]) : bv_bitstring_scope.

    (* The number notation does not work for printing patterns in pattern
       matches, but curiously works for parsing. Possibly due to the via-type
       remappings whose warnings we silenced above. As a workaround we define
       printing only notations for the constructors that achieve the same result
       as printing the number notation. *)
    Notation "" := (bitstring.bN)
      (at level 0, right associativity, only printing) : bv_bitstring_scope.
    Notation "1 b" := (bitstring.bI b)
      (at level 0, right associativity, format "1 b", only printing) : bv_bitstring_scope.
    Notation "0 b" := (bitstring.bO b)
      (at level 0, right associativity, format "0 b", only printing) : bv_bitstring_scope.

    Notation "[ 'bits' x ]" := (of_bitstring x%bits)
      (format "[ 'bits'  x ]") : bv_scope.
    Notation "[ 'bits' ]" := (@of_bitstring 0 bitstring.bN)
      (format "[ 'bits' ]") : bv_scope.
    Notation "[ 'bits' [ n ] x ]" := (@of_bitstring n x%bits)
      (only parsing) : bv_scope.
    Notation "[ 'bits' [ 0 ] ]" := (@of_bitstring 0 bitstring.bN)
      (only parsing) : bv_scope.

    Notation "[ 'bv' x ]" := (mk x%xN I) (format "[ 'bv'  x ]") : bv_scope.
    Notation "[ 'bv' [ n ] x ]" := (@mk n x%xN I) (only parsing) : bv_scope.

    Infix "+" := (@add _) : bv_scope.
    Infix "-" := (@sub _) : bv_scope.
    Infix "*" := (@mul _) : bv_scope.

    (* Signed bitvector operations *)
    Infix ">=ˢ"  := (@sge _)  : bv_scope.
    Infix ">ˢ"   := (@sgt _)  : bv_scope.
    Infix "<=ˢ"  := (@sle _)  : bv_scope.
    Infix "<ˢ"   := (@slt _)  : bv_scope.
    Infix ">=ˢ?" := (@sgeb _) : bv_scope.
    Infix ">ˢ?"  := (@sgtb _) : bv_scope.
    Infix "<=ˢ?" := (@sleb _) : bv_scope.
    Infix "<ˢ?"  := (@sltb _) : bv_scope.

    (* Unsigned bitvector operations *)
    Infix ">=ᵘ"  := (@uge _)  : bv_scope.
    Infix ">ᵘ"   := (@ugt _)  : bv_scope.
    Infix "<=ᵘ"  := (@ule _)  : bv_scope.
    Infix "<ᵘ"   := (@ult _)  : bv_scope.
    Infix ">=ᵘ?" := (@ugeb _) : bv_scope.
    Infix ">ᵘ?"  := (@ugtb _) : bv_scope.
    Infix "<=ᵘ?" := (@uleb _) : bv_scope.
    Infix "<ᵘ?"  := (@ultb _) : bv_scope.

  End notations.

  Section DropTruncs.
    Lemma truncn_small {n x} : (x < exp2 n)%N -> truncn n x = x.
    Proof.
      intros.
      now apply truncn_wf, is_wf_spec.
    Qed.

    Lemma bin_add_small {n x y} : (@bin n x + bin y < exp2 n)%N ->
                            bin (x + y) = (bin x + bin y)%N.
    Proof.
      destruct x, y.
      now apply truncn_small.
    Qed.

    Lemma bin_sub_small {n x y} : (y <=ᵘ x) -> bv.bin (x - y)%bv = (bv.bin x - @bv.bin n y)%N.
    Proof.
      intro Hle.
      (* Some returning proof steps *)
      pose proof (bv.bv_is_wf x).
      pose proof (bv.bv_is_wf y).
      pose proof (bv.exp2_nzero n).
      destruct y as [yval ?]. (* Proof-irrelevant destruct needed; `y = bv.zero` does not work *)
      destruct (base.decide (yval = 0)%N) as [-> |]; cbn in *.
      - (* Exclude trivial case *)
        rewrite !bv.truncn_spec, !N.sub_0_r, N.Div0.mod_same.
        rewrite N.add_0_r, N.mod_small; easy.
      - setoid_rewrite -> truncn_small at 2.
        2: { apply N.sub_lt; Lia.lia. }
        rewrite bv.truncn_spec.
        rewrite N.add_sub_assoc; [..|Lia.lia].
        rewrite N.add_comm, <-N.add_sub_assoc; [..|easy].
        rewrite <-N.Div0.add_mod_idemp_l, N.Div0.mod_same.
        apply N.mod_small. Lia.lia.
    Qed.

    Lemma bin_of_N_small {n x} : (x < exp2 n)%N -> @bin n (of_N x) = x.
    Proof.
      now apply truncn_small.
    Qed.

    Lemma of_N_one {n} : of_N 1 = @one n.
    Proof. apply bin_inj_eq2n. now destruct n; easy. Qed.

    Lemma of_Z_one {n} : of_Z 1 = @one n.
    Proof.
      apply unsigned_inj. rewrite unsigned_of_Z. destruct n; [easy|].
      apply Z.mod_1_l. rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia.
    Qed.

    Lemma bin_of_nat_small {n x} : (N.of_nat x < exp2 n)%N ->
                                   @bin n (of_nat x) = N.of_nat x.
    Proof.
      now apply bin_of_N_small.
    Qed.

    Lemma unsigned_succ_small n m :
      (N.succ (bin m) < exp2 n)%N ->
      Z.succ (unsigned m) = @unsigned n (one + m).
    Proof.
      intro H. unfold unsigned.
      rewrite bin_add_small.
      - rewrite Znat.N2Z.inj_add.
        destruct n; cbn in *; Lia.lia.
      - induction m using bv_case; cbn in *; Lia.lia.
    Qed.
  End DropTruncs.

  Section NoDupBvSeq.
    Lemma NoDup_seq_bv n start len :
      (0 <= len <= bv_modulus n)%Z ->
      base.NoDup (@bv_seq n start len).
    Proof.
      rewrite exp2_bv_modulus.
      intros H. apply list.NoDup_alt. intros i j b'. unfold bv_seq. rewrite !list.list_lookup_fmap.
      intros [x [[-> ?]%list_numbers.lookup_seqZ ->]]%option.fmap_Some.
      intros.
      apply option.fmap_Some in H1.
      destruct H1 as (x & Hseq & Heq).
      apply list_numbers.lookup_seqZ in Hseq as (-> & Hj).
      apply add_cancel_l in Heq.
      change (0 + ?x)%Z with x in Heq.
      rewrite ?of_Z_nat in Heq.
      apply (f_equal (@bin _)) in Heq.
      rewrite ?bin_of_nat_small in Heq; Lia.lia.
    Qed.
  End NoDupBvSeq.

  Section Comparison.
    Lemma ule_nat_one_S : forall {w} (n : nat),
        (N.of_nat 1 < exp2 w)%N ->
        (N.of_nat (S n) < exp2 w)%N ->
        (@of_nat w 1) <=ᵘ (of_nat (S n)).
    Proof. intros; unfold ule. rewrite ?bin_of_nat_small; Lia.lia. Qed.

    Lemma ult_nat_S_zero : forall {w} (n : nat),
        (N.of_nat (S n) < exp2 w)%N ->
        @zero w <ᵘ of_nat (S n).
    Proof. intros; unfold ult; rewrite bin_of_nat_small; auto; now simpl. Qed.

    Lemma ule_trans : forall {n} (x y z : bv n),
        x <=ᵘ y ->
        y <=ᵘ z ->
        x <=ᵘ z.
    Proof. intros n x y z; unfold bv.ule; apply N.le_trans. Qed.

    Lemma ult_trans : forall {n} (x y z : bv n),
        x <ᵘ y ->
        y <ᵘ z ->
        x <ᵘ z.
    Proof. intros n x y z; unfold bv.ult; apply N.lt_trans. Qed.

    Lemma add_ule_mono : forall {x} (n m p : bv x),
        (bv.bin p + bv.bin n < bv.exp2 x)%N ->
        (bv.bin p + bv.bin m < bv.exp2 x)%N ->
        n <=ᵘ m <-> p + n <=ᵘ p + m.
    Proof. intros; unfold bv.ule; rewrite ?bv.bin_add_small; Lia.lia. Qed.

    Lemma ule_add_r : forall {x} (n m p : bv x),
        (bv.bin m + bv.bin p < bv.exp2 x)%N ->
        n <=ᵘ m -> n <=ᵘ m + p.
    Proof.
      intros.
      unfold bv.ule in *.
      rewrite bv.bin_add_small; auto.
      rewrite <- (N.add_0_r (bv.bin n)).
      apply N.add_le_mono; auto.
      apply N.le_0_l.
    Qed.

    Lemma add_ule_r : forall {x} (n m p : bv x),
        (bv.bin n + bv.bin p < bv.exp2 x)%N ->
        n + p <=ᵘ m -> n <=ᵘ m.
    Proof.
      intros.
      unfold bv.ule in *.
      rewrite bv.bin_add_small in H0; auto.
      rewrite <- N.add_0_r in H0.
      apply (N.le_le_add_le _ _ _ _ (N.le_0_l (bv.bin p)) H0).
    Qed.

    Lemma add_ule_S_ult : forall {x} (n m p : bv x),
        (bv.bin n + bv.bin p < bv.exp2 x)%N ->
        bv.zero <ᵘ p ->
        n + p <=ᵘ m -> n <ᵘ m.
    Proof.
      intros.
      unfold bv.ule, bv.ult in *.
      rewrite bv.bin_add_small in H1; auto.
      apply (N.lt_le_add_lt _ _ _ _ H0).
      now rewrite N.add_0_r.
    Qed.

    Lemma ultb_antisym : forall {n} (x y : bv n),
        y <ᵘ? x = negb (x <=ᵘ? y).
    Proof. intros; unfold bv.uleb, bv.ultb; apply N.ltb_antisym. Qed.

    Lemma ult_ule_incl : forall {n} (x y : bv n),
        x <ᵘ y -> x <=ᵘ y.
    Proof. intros; unfold bv.ule, bv.ult; apply N.lt_le_incl; auto. Qed.

    Lemma ule_cases : forall {n} (x y : bv n),
        x <=ᵘ y <-> x <ᵘ y \/ x = y.
    Proof.
      intros n x y.
      unfold bv.ule, bv.ult.
      rewrite N.lt_eq_cases; now rewrite bv.bin_inj_equiv.
    Qed.

    Lemma ule_refl : forall {n} (x : bv n),
        x <=ᵘ x.
    Proof. intros; unfold bv.ule; auto. Qed.

    Lemma uleb_ugt : forall {n} (x y : bv n),
        x <=ᵘ? y = false <-> y <ᵘ x.
    Proof. intros; unfold bv.uleb, bv.ule; now apply N.leb_gt. Qed.

    Lemma uleb_ule : forall {n} (x y : bv n),
        x <=ᵘ? y = true <-> x <=ᵘ y.
    Proof. intros; unfold bv.uleb; now apply N.leb_le. Qed.

    Lemma ultb_uge : forall {n} (x y : bv n),
        x <ᵘ? y = false <-> y <=ᵘ x.
    Proof. intros; unfold bv.ultb; now apply N.ltb_ge. Qed.

    Lemma ultb_ult : forall {n} (x y : bv n),
        x <ᵘ? y = true <-> x <ᵘ y.
    Proof. intros; unfold bv.ultb; now apply N.ltb_lt. Qed.

    Lemma ultb_uleb : forall {n} (x y : bv n),
        x <ᵘ? y = true -> x <=ᵘ? y = true.
    Proof.
      intros n x y.
      rewrite ultb_ult, uleb_ule.
      unfold bv.ule, bv.ult.
      Lia.lia.
    Qed.

    Lemma ult_antirefl : forall {n} (x : bv n), ~ (x <ᵘ x).
    Proof. unfold ult. Lia.lia. Qed.

    Lemma add_nonzero_neq : forall {n} (x y : bv n),
        bv.zero <ᵘ y ->
        x + y <> x.
    Proof.
      intros n x y ynz eq.
      replace x with (x + bv.zero) in eq  at 2 by apply bv.add_zero_r.
      apply bv.add_cancel_l in eq.
      subst. revert ynz.
      now apply ult_antirefl.
    Qed.

    Lemma ule_antisymm {n} {x y : bv n} : x <=ᵘ y -> y <=ᵘ x -> x = y.
    Proof.
      unfold bv.ule.
      intros ineq1 ineq2.
      apply bv.bin_inj.
      now Lia.lia.
    Qed.

    Lemma lt_S_add_one : forall {n} x,
        (N.of_nat (S x) < bv.exp2 n)%N ->
        (bv.bin (@bv.one n) + (@bv.bin n (bv.of_nat x)) < bv.exp2 n)%N.
    Proof.
      destruct n.
      simpl; Lia.lia.
      assert (bv.bin (@bv.one (S n)) = 1%N) by auto.
      rewrite H.
      intros.
      rewrite bv.bin_of_nat_small; Lia.lia.
    Qed.

    Lemma ult_iff_unsigned_lt {n} {x y : bv n} :
      x <ᵘ y <-> (bv.unsigned x < bv.unsigned y)%Z.
    Proof. apply N2Z.inj_lt. Qed.

    Lemma ugt_iff_unsigned_gt {n} {x y : bv n} :
      x >ᵘ y <-> (bv.unsigned x > bv.unsigned y)%Z.
    Proof. unfold ugt.
           now rewrite ult_iff_unsigned_lt, Z.gt_lt_iff.
    Qed.

    Lemma ule_iff_unsigned_le {n} {x y : bv n} :
      x <=ᵘ y <-> (bv.unsigned x <= bv.unsigned y)%Z.
    Proof. apply N2Z.inj_le. Qed.

    Lemma uge_iff_unsigned_ge {n} {x y : bv n} :
      x >=ᵘ y <-> (bv.unsigned x >= bv.unsigned y)%Z.
    Proof. unfold uge.
           now rewrite ule_iff_unsigned_le, Z.ge_le_iff.
    Qed.

  End Comparison.

  Load BitvectorSolve.

  Section Sequences.
    Import bv.notations.
    Import Lists.List.
    Import ListNotations.

    (* why do we have both bv_seq and seqBv? *)
    Definition seqBv {n} (min : bv n) (len : nat) := List.map (@bv.of_Z n) (list_numbers.seqZ (bv.unsigned min) (Z.of_nat len)).

    Lemma seqBv_zero {n} m : @seqBv n m 0 = nil.
    Proof. unfold seqBv. now cbv. Qed.
    Lemma seqBv_one {n} m : @seqBv n m 1 = cons m nil.
    Proof.
      unfold seqBv.
      rewrite list_numbers.seqZ_cons; [|lia]. cbn.
      f_equal. now rewrite of_Z_unsigned. Qed.

    Lemma seqBv_len n base width : length (@seqBv n base width) = width.
    Proof. unfold seqBv. rewrite map_length, list_numbers.length_seqZ. lia. Qed.

    Lemma seqBv_width_at_least {n width} base k y :
      base.lookup k (@seqBv n base width) = Some y -> exists p , width = (k + S p)%nat.
    Proof.
      intros Hlkup.
      apply list.lookup_lt_Some in Hlkup as Hw.
      apply Nat.le_exists_sub in Hw as (p & [Hweq _]).
      rewrite seqBv_len, <-Nat.add_succ_comm, Nat.add_comm in Hweq.
      eauto.
    Qed.

    Lemma seqBv_app {n} m n1 n2 :
      @seqBv n m (n1 + n2) = seqBv m n1 ++ seqBv (bv.add m (bv.of_nat n1)) n2.
    Proof.
      unfold seqBv.
      rewrite Znat.Nat2Z.inj_add, list_numbers.seqZ_app, map_app; try lia.
      f_equal. unfold list_numbers.seqZ. rewrite <- !list.list_fmap_compose.
      apply list.list_fmap_ext. intros _ x _. cbn.
      now rewrite <- !of_Z_add, !of_Z_unsigned, !of_Z_nat.
    Qed.

    Lemma seqBv_succ {n} m n1 :
      (@seqBv n m (S n1)) = cons m (seqBv (one + m) n1).
    Proof.
      rewrite <-Nat.add_1_l, seqBv_app, seqBv_one, add_comm. now destruct n.
    Qed.

    Lemma seqBv_succ_end {n} m n1 :
      (@seqBv n m (S n1)) = (seqBv m n1)%bv ++ (cons (m + of_nat n1) nil) .
    Proof.
      now rewrite <-Nat.add_1_r, seqBv_app, seqBv_one.
    Qed.

    Lemma seqBv_spec {n width} base k y:
      base.lookup k (@seqBv n base width) = Some y ->
      (base + bv.of_nat k) = y.
    Proof.
      intros Hlkup.
      pose proof (seqBv_width_at_least _ _ Hlkup) as [p ->].
      rewrite seqBv_app, list.lookup_app_r in Hlkup; [| now rewrite seqBv_len].
      rewrite seqBv_len, seqBv_succ, list.lookup_cons, Nat.sub_diag in Hlkup.
      now inversion Hlkup.
    Qed.

    (* More powerful version of `in_seqBv` where `len` and `min + len` need not be representable in `n` bits *)
    Lemma in_seqBv' n v min len :
      (min <=ᵘ v) -> (bv.bin v < bv.bin min + N.of_nat len)%N ->
        base.elem_of v (@seqBv n min len).
    Proof.
      unfold bv.ule, seqBv.
      intros mla alm.
      apply (list.elem_of_list_fmap_1_alt bv.of_Z _ (bv.unsigned v)).
      - apply list_numbers.elem_of_seqZ.
        unfold unsigned, Z.of_nat.
        destruct len; Lia.lia.
      - now rewrite bv.of_Z_unsigned.
    Qed.

    (* NOTE: this lemma does not work for the case where `min == 0` and `len == bv.exp2 n`, which is a valid case. We have hence proven the more general lemma above. *)
    Lemma in_seqBv n v min len :
      (min <=ᵘ v) -> (v <ᵘ bv.add min (bv.of_nat len)) ->
        base.elem_of v (@seqBv n min len).
    Proof.
      unfold bv.ule, bv.ult, seqBv.
      intros mla alm.
      enough (bv.bin v < bv.bin min + N.of_nat len)%N by (apply in_seqBv'; auto).
      eapply N.lt_le_trans; [exact alm |].
      unfold add.
      rewrite bin_of_N_decr. apply N.add_le_mono; auto.
      now rewrite bin_of_nat_decr.
    Qed.

    (* Only prove one direction *)
    Lemma seqBv_no_overlap {n} a a1 a2 b1 b2:
      (N.of_nat (b1 + b2) < (exp2 n))%N ->
      a1 + a2 <= b1 ->
      base.elem_of a (@seqBv n (bv.of_nat a1) a2) ->
      base.elem_of a (seqBv (bv.of_nat b1) b2) ->
      False.
    Proof.
      intros Hrep Hlt Hain Hbin.
      rewrite !list.elem_of_list_lookup in Hain, Hbin.
      destruct Hain as (ai & Hain).
      destruct Hbin as (bi & Hbin).
      apply list.lookup_lt_Some in Hain as Halen.
      apply list.lookup_lt_Some in Hbin as Hblen.
      rewrite !seqBv_len in Halen, Hblen.

      apply seqBv_spec, (f_equal (@bv.bin n)) in Hain, Hbin.
      rewrite !@bin_add_small, !@bin_of_nat_small in Hain, Hbin; try Lia.lia;
      rewrite ?@bin_of_nat_small ; try Lia.lia.
    Qed.

  Lemma seqBv_sub_list {n s s' e e'}:
    (bv.ule s s') ->
    (N.to_nat (bv.bin s') + e' <= N.to_nat (bv.bin s) + e) ->
    exists l1 l2, @seqBv n s e = l1 ++ (seqBv s' e' ++ l2).
  Proof. intros Hs He.
      unfold bv.ule in Hs.
      assert (e = (N.to_nat (bv.bin s') - N.to_nat (bv.bin s)) + (((N.to_nat (bv.bin s') + e') - N.to_nat (bv.bin s')) + ((N.to_nat (bv.bin s) + e) - (N.to_nat (bv.bin s') + e'))))%nat as -> by Lia.lia.
      rewrite 2!seqBv_app.
      do 2 eexists.
      repeat f_equal.
      - unfold bv.add.
        rewrite <-(bv.of_N_bin s') at -1. f_equal.
        rewrite bv.bin_of_nat_small; last bv_zify.
        rewrite <-Nnat.N2Nat.inj_sub, Nnat.N2Nat.id. Lia.lia.
      - Lia.lia.
  Qed.

  Lemma seqBv_sub_elem_of {n s s' e e'} a:
    (s <=ᵘ s') ->
    (N.to_nat (bv.bin s') + e' <= N.to_nat (bv.bin s) + e) ->
    (base.elem_of a (seqBv s' e')) -> (base.elem_of a (@seqBv n s e)).
  Proof.
    intros Hs He Hel.
    destruct (seqBv_sub_list Hs He) as (l1 & l2 & ->).
    rewrite !list.elem_of_app. auto.
  Qed.

  Lemma seqBv_in' {n v min len} :
    (bv.bin min + N.of_nat len <= bv.exp2 n)%N -> (* Required in this direction *)
    (base.elem_of v (@seqBv n min len)) ->
    and (min <=ᵘ v) (bv.bin v < bv.bin min + N.of_nat len)%N.
  Proof.
     unfold bv.ule, bv.ult, seqBv.
     intros Hflow [y [-> Hel%list_numbers.elem_of_seqZ]]%list.elem_of_list_fmap_2.
     unfold bv.of_Z.
     rewrite <-(Znat.Z2N.id y); last bv_zify.
     rewrite bv.to_N_truncz.
     rewrite bv.truncn_small; last bv_zify.
     rewrite bv.bin_of_N_small; last bv_zify.
     bv_zify.
  Qed.

  Lemma NoDup_seqbv {n min len}:
    (bv.bin min + N.of_nat len <= bv.exp2 n)%N ->
    base.NoDup (@seqBv n min len).
  Proof.
    intros Hof.
    apply list.NoDup_fmap_2_strong; last apply list_numbers.NoDup_seqZ.
    intros x y Hxin Hyin Heq.
    rewrite !list_numbers.elem_of_seqZ in Hxin, Hyin.
    rewrite <-(Znat.Z2N.id y) in Heq; last bv_zify.
    rewrite <-(Znat.Z2N.id x) in Heq; last bv_zify.
    unfold bv.unsigned, bv.of_Z in *.
    rewrite !bv.to_N_truncz, !bv.truncn_small in Heq; [|bv_zify..].
    apply (f_equal (@bv.bin _)) in Heq.
    rewrite !bv.bin_of_N_small in Heq; bv_zify.
  Qed.

  End Sequences.

  Section Tests.
    Goal lsb [bv[2] 0] = false. reflexivity. Abort.
    Goal lsb [bv[2] 1] = true.  reflexivity. Abort.
    Goal lsb [bv[2] 2] = false. reflexivity. Abort.
    Goal lsb [bv[2] 3] = true.  reflexivity. Abort.

    Goal msb [bv[2] 0] = false. reflexivity. Abort.
    Goal msb [bv[2] 1] = false. reflexivity. Abort.
    Goal msb [bv[2] 2] = true.  reflexivity. Abort.
    Goal msb [bv[2] 3] = true.  reflexivity. Abort.

    Goal sext' [bv[2] 0] 2 = [bv[4] 0].  reflexivity. Abort.
    Goal sext' [bv[2] 1] 2 = [bv[4] 1].  reflexivity. Abort.
    Goal sext' [bv[2] 2] 2 = [bv[4] 14]. reflexivity. Abort.
    Goal sext' [bv[2] 3] 2 = [bv[4] 15]. reflexivity. Abort.

    Goal zext' [bv[2] 0] 2 = [bv[4] 0]. reflexivity. Abort.
    Goal zext' [bv[2] 1] 2 = [bv[4] 1]. reflexivity. Abort.
    Goal zext' [bv[2] 2] 2 = [bv[4] 2]. reflexivity. Abort.
    Goal zext' [bv[2] 3] 2 = [bv[4] 3]. reflexivity. Abort.

    Goal sext [bv[2] 0] = [bv[4] 0].  reflexivity. Abort.
    Goal sext [bv[2] 1] = [bv[4] 1].  reflexivity. Abort.
    Goal sext [bv[2] 2] = [bv[4] 14]. reflexivity. Abort.
    Goal sext [bv[2] 3] = [bv[4] 15]. reflexivity. Abort.

    Goal zext [bv[2] 0] = [bv[4] 0]. reflexivity. Abort.
    Goal zext [bv[2] 1] = [bv[4] 1]. reflexivity. Abort.
    Goal zext [bv[2] 2] = [bv[4] 2]. reflexivity. Abort.
    Goal zext [bv[2] 3] = [bv[4] 3]. reflexivity. Abort.

    Goal signed [bv[0] 0] = 0%Z.    reflexivity. Abort.
    Goal signed [bv[1] 0] = 0%Z.    reflexivity. Abort.
    Goal signed [bv[1] 1] = (-1)%Z. reflexivity. Abort.
    Goal signed [bv[3] 0] = 0%Z.    reflexivity. Abort.
    Goal signed [bv[3] 1] = 1%Z.    reflexivity. Abort.
    Goal signed [bv[3] 2] = 2%Z.    reflexivity. Abort.
    Goal signed [bv[3] 3] = 3%Z.    reflexivity. Abort.
    Goal signed [bv[3] 4] = (-4)%Z. reflexivity. Abort.
    Goal signed [bv[3] 5] = (-3)%Z. reflexivity. Abort.
    Goal signed [bv[3] 6] = (-2)%Z. reflexivity. Abort.
    Goal signed [bv[3] 7] = (-1)%Z. reflexivity. Abort.

    Goal of_Z 0%Z    = [bv[0] 0]. reflexivity. Abort.
    Goal of_Z 0%Z    = [bv[1] 0]. reflexivity. Abort.
    Goal of_Z (-1)%Z = [bv[1] 1]. reflexivity. Abort.
    Goal of_Z 0%Z    = [bv[3] 0]. reflexivity. Abort.
    Goal of_Z 1%Z    = [bv[3] 1]. reflexivity. Abort.
    Goal of_Z 2%Z    = [bv[3] 2]. reflexivity. Abort.
    Goal of_Z 3%Z    = [bv[3] 3]. reflexivity. Abort.
    Goal of_Z (-4)%Z = [bv[3] 4]. reflexivity. Abort.
    Goal of_Z (-3)%Z = [bv[3] 5]. reflexivity. Abort.
    Goal of_Z (-2)%Z = [bv[3] 6]. reflexivity. Abort.
    Goal of_Z (-1)%Z = [bv[3] 7]. reflexivity. Abort.

    Goal shiftr [bv[8] 16] [bv[5] 4] = [bv[8] 1]. reflexivity. Abort.
    Goal shiftl [bv[8] 1] [bv[5] 4] = [bv[8] 16]. reflexivity. Abort.
  End Tests.

End bv.

Bind Scope bv_scope with bv.bv.
Bind Scope bv_bitstring_scope with bv.bitstring.
Bind Scope bv_bitstring_scope with bv.bitstring.null.
Bind Scope bv_bitstring_scope with bv.bitstring.digit.
Export bv (bv).
Export (hints) bv.
Export (hints) bv.countable.

Tactic Notation "solve_bv" := bv.bv_zify.
Tactic Notation "solve_bv" "-" hyp_list(Hs) := clear Hs; bv.bv_zify.
Tactic Notation "solve_bv" "+" hyp_list(Hs) := clear -Hs; bv.bv_zify.

Import bv.notations.

Module bv_solve_Ltac.
  Ltac solveBvManual :=
    intros;
    cbn;
    repeat
      (match goal with
       | |- context[ bv.ule ?x ?y ] => rewrite bv.ule_iff_unsigned_le
       | |- context[ bv.ult ?x ?y ] => rewrite bv.ult_iff_unsigned_lt
       | |- context[ bv.uge ?x ?y ] => rewrite bv.uge_iff_unsigned_ge
       | |- context[ bv.ugt ?x ?y ] => rewrite bv.ugt_iff_unsigned_gt
       | |- context[ bv.unsigned (?x + ?y) ] => destruct (bv.unsigned_add_view x y)
       | _ : context[ bv.unsigned (?x + ?y) ] |- _ => destruct (bv.unsigned_add_view x y)
       end; cbn);
    repeat
      match goal with
      | x : bv ?n |- _ => pose proof (bv.unsigned_bounds x); generalize dependent (bv.unsigned x); clear x
      end;
    cbn; intros; try lia.

  Goal forall v : bv 32, (76 + bv.unsigned v < 200)%Z -> (4 + bv.unsigned (v + [bv 0x4]) <= 200)%Z.
    solveBvManual.
  Qed.
End bv_solve_Ltac.
