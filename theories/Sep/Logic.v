(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov, Steven Keuchel     *)
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
     Classes.Morphisms
     Classes.RelationClasses
     Setoid.

From Katamaran Require Import
     Notations.

Local Set Implicit Arguments.

Declare Scope logic_scope.
Delimit Scope logic_scope with logic.
Delimit Scope logic_scope with L.

Module sep.

  Structure SepLogic :=
    { lcar        :> Type;
      lentails    : lcar -> lcar -> Prop where "P ⊢ Q" := (lentails P Q);
      land        : lcar -> lcar -> lcar where "P ∧ Q" := (land P Q);
      lor         : lcar -> lcar -> lcar where "P ∨ Q" := (lor P Q);
      limpl       : lcar -> lcar -> lcar where "P → Q" := (limpl P Q);
      lprop       : Prop -> lcar where "'!!' P" := (lprop P);
      lex         : forall T, (T -> lcar) -> lcar;
      lall        : forall T, (T -> lcar) -> lcar;
      lemp        : lcar;
      lsep        : lcar -> lcar -> lcar where "P ∗ Q" := (lsep P Q);
      lwand       : lcar -> lcar -> lcar where "P -∗ Q" := (lwand P Q);

      lequiv (P Q : lcar) : Prop := (P ⊢ Q) /\ (Q ⊢ P) where "P ⊣⊢ Q" := (lequiv P Q);

      #[canonical=no] lentails_preorder  : PreOrder lentails;

      #[canonical=no] land_right X P Q         : (X ⊢ P) -> (X ⊢ Q) -> (X ⊢ P ∧ Q);
      #[canonical=no] land_left1 P Q R         : (P ⊢ R) -> (P ∧ Q ⊢ R);
      #[canonical=no] land_left2 P Q R         : (Q ⊢ R) -> (P ∧ Q ⊢ R);
      #[canonical=no] lor_left P Q R           : (P ⊢ R) -> (Q ⊢ R) -> (P ∨ Q ⊢ R);
      #[canonical=no] lor_right1 P Q R         : (P ⊢ Q) -> (P ⊢ Q ∨ R);
      #[canonical=no] lor_right2 P Q R         : (P ⊢ R) -> (P ⊢ Q ∨ R);
      #[canonical=no] lex_right B x P Q        : (P ⊢ Q x) -> (P ⊢ @lex B Q);
      #[canonical=no] lex_left B P Q           : (forall x, P x ⊢ Q) -> (@lex B P ⊢ Q);
      #[canonical=no] lall_left B x P Q        : (P x ⊢ Q) -> (@lall B P ⊢ Q);
      #[canonical=no] lall_right B P Q         : (forall v, P ⊢ Q v) -> (P ⊢ @lall B Q);
      #[canonical=no] limpl_and_adjoint P Q R  : (P ∧ Q ⊢ R) <-> (P ⊢ Q → R);
      #[canonical=no] lprop_left (P : Prop) Q  : (P -> (!!True ⊢ Q)) -> (!!P ⊢ Q);
      #[canonical=no] lprop_right (P : Prop) Q : P -> (Q ⊢ !!P);

      #[canonical=no] lsep_assoc P Q R        : P ∗ (Q ∗ R) ⊣⊢ (P ∗ Q) ∗ R;
      #[canonical=no] lsep_comm P Q           : P ∗ Q ⊣⊢ Q ∗ P;
      #[canonical=no] lwand_sep_adjoint P Q R : (P ∗ Q ⊢ R) <-> (P ⊢ Q -∗ R);
      #[canonical=no] lsep_andp_prop P Q R    : P ∗ (!!Q ∧ R) ⊣⊢ !!Q ∧ (P ∗ R);
      #[canonical=no] lsep_entails P P' Q Q'  : (P ⊢ P') -> (Q ⊢ Q') -> (P ∗ Q ⊢ P' ∗ Q');
      #[canonical=no] lsep_emp P              : P ∗ lemp ⊣⊢ P;
      #[canonical=no] lsep_leak P             : P ⊢ lemp;
    }.

  Arguments lequiv {_} _ _.
  Arguments lentails {_} _ _.
  Arguments land {_} _ _.
  Arguments lor {_} _ _.
  Arguments limpl {_} _ _.
  Arguments lprop {_} _.
  Arguments lex {_} [_] _.
  Arguments lall {_} [_] _.
  Arguments lemp {_}.
  Arguments lsep {_} _ _.
  Arguments lwand {_} _ _.

  Module Import notations.
    Open Scope logic_scope.
    Notation "P ⊢ Q" := (lentails P%L Q%L) : type_scope.
    Notation "P '⊢@{' L } Q" := (@lentails L P%L Q%L) (only parsing) : type_scope.
    Notation "P ⊣⊢ Q" := (lequiv P%L Q%L) : type_scope.
    Notation "P '⊣⊢@{' L } Q" := (@lequiv L P%L Q%L) (only parsing) : type_scope.

    Infix "∨" := lor : logic_scope.
    Infix "∧" := land : logic_scope.
    Infix "→" := limpl : logic_scope.
    Notation "'∃' x .. y , P " :=
      (lex (fun x => .. (lex (fun y => P)) ..))
      (at level 200, x binder, y binder, right associativity,
      format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : logic_scope.
    Notation "'∀' x .. y , P " :=
      (lall (fun x => .. (lall (fun y => P)) ..))
      (at level 200, x binder, y binder, right associativity,
      format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : logic_scope.
    Notation "'!!' e" := (lprop e) : logic_scope.
    Notation "⊤" := (lprop True) : logic_scope.
    Notation "⊥" := (lprop False) : logic_scope.
    Infix "∗" := lsep : logic_scope.
    Infix "-∗" := lwand : logic_scope.
  End notations.

  Module Import instances.

    #[export] Existing Instance lentails_preorder.

    #[export] Instance lequiv_equivalence {L} : Equivalence (@lequiv L).
    Proof.
      constructor.
      - intros P. split; reflexivity.
      - intros P Q [pq qp]; split; assumption.
      - intros P Q R [pq qp] [qr rq].
        split; transitivity Q; auto.
    Qed.

    #[export] Instance proper_lentails {L} :
      Proper (lequiv ==> lequiv ==> iff) (@lentails L).
    Proof.
      intros P Q [pq qp] R S [rs sr]. split.
      - intros pr. transitivity P; auto. transitivity R; auto.
      - intros qs. transitivity Q; auto. transitivity S; auto.
    Qed.

    #[export] Instance proper_land {L} : Proper (lequiv ==> lequiv ==> lequiv) (@land L).
    Proof.
      intros P Q [pq qp] R S [rs sr].
      split; (apply land_right; [apply land_left1 | apply land_left2]); assumption.
    Qed.

    #[export] Instance proper_lor {L} : Proper (lequiv ==> lequiv ==> lequiv) (@lor L).
    Proof.
      intros P Q [pq qp] R S [rs sr].
      split; (apply lor_left; [ apply lor_right1 | apply lor_right2]); assumption.
    Qed.

    #[export] Instance proper_limpl {L} : Proper (lequiv ==> lequiv ==> lequiv) (@limpl L).
    Proof.
      intros P Q pq R S rs.
      split; apply limpl_and_adjoint;
        [ rewrite <- pq, <- rs
        | rewrite pq, rs
        ]; apply limpl_and_adjoint; reflexivity.
    Qed.

    #[export] Instance proper_lprop {L} : Proper (iff ==> lequiv) (@lprop L).
    Proof.
      intros P Q pq.
      split; apply lprop_left; intro; now apply lprop_right, pq.
    Qed.

    #[export] Instance proper_lex {L} T : Proper (pointwise_relation T lequiv ==> lequiv) (@lex L T).
    Proof.
      intros P Q pq.
      split; apply lex_left; intro x;
        apply (@lex_right _ _ x), (pq x).
    Qed.

    #[export] Instance proper_lall {L} T : Proper (pointwise_relation T lequiv ==> lequiv) (@lall L T).
    Proof.
      intros P Q pq.
      split; apply lall_right; intro x;
        apply (@lall_left _ _ x), (pq x).
    Qed.

    #[export] Instance proper_lsep {L} : Proper (lequiv ==> lequiv ==> lequiv) (@lsep L).
    Proof.
      intros P Q [pq qp] R S [rs sr].
      split; now apply lsep_entails.
    Qed.

    #[export] Instance proper_lwand {L} : Proper (lequiv ==> lequiv ==> lequiv) (@lwand L).
    Proof.
      intros P Q pq R S rs.
      split.
      - apply lwand_sep_adjoint.
        rewrite <- pq, <- rs.
        now apply lwand_sep_adjoint.
      - apply lwand_sep_adjoint.
        rewrite pq, rs.
        now apply lwand_sep_adjoint.
    Qed.

  End instances.

  Section Facts.

    Context {L : SepLogic}.

    Lemma ltrue_right {P : L} : P ⊢ ⊤.
    Proof. now apply lprop_right. Qed.

    Lemma lfalse_left {P : L} : ⊥ ⊢ P.
    Proof. now apply lprop_left. Qed.

    Lemma land_assoc {P Q R : L} :
      (P ∧ Q) ∧ R ⊣⊢ P ∧ (Q ∧ R).
    Proof.
      split; repeat apply land_right.
      - now apply land_left1, land_left1.
      - now apply land_left1, land_left2.
      - now apply land_left2.
      - now apply land_left1.
      - now apply land_left2, land_left1.
      - now apply land_left2, land_left2.
    Qed.

    Lemma land_false {P : L} : P ∧ ⊥ ⊣⊢ ⊥.
    Proof.
      split.
      - apply land_left2, lfalse_left.
      - apply lfalse_left.
    Qed.

    Lemma lfalse_and {P : L} : ⊥ ∧ P ⊣⊢ ⊥.
    Proof.
      split.
      - apply land_left1, lfalse_left.
      - apply lfalse_left.
    Qed.

    Lemma lex_false {T} : (∃ _ : T, ⊥) ⊣⊢@{L} ⊥.
    Proof.
      split.
      - apply lex_left. intros _. apply lfalse_left.
      - apply lfalse_left.
    Qed.

    Lemma land_comm {P Q : L} :
      P ∧ Q ⊣⊢ Q ∧ P.
    Proof.
      split; (apply land_right; [ now apply land_left2 | now apply land_left1 ]).
    Qed.

    Lemma land_idem {P : L} :
      P ∧ P ⊣⊢ P.
    Proof.
      split.
      - now apply land_left1.
      - now apply land_right.
    Qed.

    Lemma land_true {P : L} :
      P ∧ ⊤ ⊣⊢ P.
    Proof.
      split.
      - now apply land_left1.
      - apply land_right.
        + reflexivity.
        + apply ltrue_right.
    Qed.

    Lemma land_intro2 {P Q R S : L} :
      (P ⊢ Q) -> (R ⊢ S) -> (P ∧ R ⊢ Q ∧ S).
    Proof.
      intros pq rs.
      apply land_right.
      apply land_left1, pq.
      apply land_left2, rs.
    Qed.

    Lemma lor_assoc {P Q R : L} :
      ((P ∨ Q) ∨ R) ⊣⊢ (P ∨ (Q ∨ R)).
    Proof.
      split; repeat apply lor_left.
      - now apply lor_right1.
      - now apply lor_right2, lor_right1.
      - now apply lor_right2, lor_right2.
      - now apply lor_right1, lor_right1.
      - now apply lor_right1, lor_right2.
      - now apply lor_right2.
    Qed.

    Lemma lor_comm {P Q : L} :
      (P ∨ Q) ⊣⊢ (Q ∨ P).
    Proof.

      split; (apply lor_left; [ apply lor_right2 | apply lor_right1 ]); reflexivity.
    Qed.

    Lemma lor_idem {P : L} :
      (P ∨ P) ⊣⊢ P.
    Proof.
      split.
      - now apply lor_left.
      - now apply lor_right1.
    Qed.

    Lemma lprop_and_distr {P Q : Prop} :
      (!! P) ∧ (!! Q) ⊣⊢@{L} !! (P /\ Q).
    Proof.
      split.
      - apply limpl_and_adjoint.
        apply lprop_left; intros.
        apply limpl_and_adjoint.
        apply land_left2.
        apply lprop_left; intros.
        apply lprop_right.
        split; assumption.
      - apply lprop_left; intros [].
        apply land_right; apply lprop_right; assumption.
    Qed.

    Lemma lprop_float {P : L} {Q : Prop} :
      (P ∧ !! Q) ⊣⊢ (!! Q ∧ P).
    Proof. apply land_comm. Qed.

    Lemma lemp_true :
      lemp ⊣⊢@{L} ⊤.
    Proof.
      split.
      apply ltrue_right.
      apply lsep_leak.
    Qed.

    Lemma lsep_true {P : L} : ⊤ ∗ P ⊣⊢ P.
    Proof.
      rewrite <- lemp_true.
      rewrite lsep_comm.
      rewrite lsep_emp.
      reflexivity.
    Qed.

    Lemma lprop_sep_distr Q P :
      !! P ∗ !! Q ⊣⊢@{L} !! (P /\ Q).
    Proof.
      split.
      - apply lwand_sep_adjoint.
        apply lprop_left. intros HP.
        apply lwand_sep_adjoint.
        rewrite lsep_true.
        apply lprop_left. intros HQ.
        apply lprop_right; auto.
      - apply lprop_left. intros [HP HQ].
        rewrite <- lsep_true at 1.
        apply lsep_entails; now apply lprop_right.
    Qed.

    Lemma lprop_or_distr {P Q : Prop} :
      (!! P) ∨ (!! Q) ⊣⊢@{L} !! (P \/ Q).
    Proof.
      split.
      - apply lor_left; apply lprop_left;
          intros H; apply lprop_right; auto.
      - apply lprop_left; intros [HP|HQ];
          [apply lor_right1 | apply lor_right2];
          now apply lprop_right.
    Qed.

    Lemma lprop_exists_comm {T} (P : T -> Prop) :
      !! (exists t : T, P t) ⊣⊢@{L} (∃ t : T, !! P t).
    Proof.
      split.
      - apply lprop_left; intros [x HP].
        apply lex_right with x.
        now apply lprop_right.
      - apply lex_left. intros x.
        apply lprop_left; intros HP.
        apply lprop_right. now exists x.
    Qed.

    Lemma lsep_disj_distr {P Q R : L} :
      ((P ∨ Q) ∗ R) ⊣⊢ ((P ∗ R) ∨ (Q ∗ R)).
    Proof.
      split.
      - apply lwand_sep_adjoint, lor_left;
          apply lwand_sep_adjoint.
        + now apply lor_right1.
        + now apply lor_right2.
      - apply lor_left; apply lsep_entails; try reflexivity.
        + now apply lor_right1.
        + now apply lor_right2.
    Qed.

  End Facts.

End sep.
Export sep.
