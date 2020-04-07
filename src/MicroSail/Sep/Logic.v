Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

(* Adopted from VST: https://github.com/PrincetonUniversity/VST/blob/master/msl/seplog.v *)
Class NatDed (A: Type) := mkNatDed {
  andp : A -> A -> A;
  orp : A -> A -> A;
  (* existential quantification *)
  exp : forall {T : Set}, (T -> A) -> A;
  (* universal quantification *)
  allp : forall {T : Set}, (T -> A) -> A;
  imp : A -> A -> A;

  (* Prop embedding *)
  prop : Prop -> A;
  (* P ⊢ Q *)
  derives : A -> A -> Prop;

  TT := prop True;
  FF := prop False;
}.

Delimit Scope logic with logic.
Local Open Scope logic.
Notation "P '⊢' Q" := (derives P Q) (at level 80, no associativity) : logic_derives.
Open Scope logic_derives.
Notation "'∃' x .. y , P " :=
  (exp (fun x => .. (exp (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Notation "'∀' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Infix "∨" := orp (at level 50, left associativity) : logic.
Infix "∧" := andp (at level 40, left associativity) : logic.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : logic.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : logic.
Notation "'!!' e" := (prop e) (at level 25) : logic.

Class NatDedAxioms (A : Type) {ND : NatDed A} := {
  (* pred_ext : forall P Q, P ⊢ Q -> Q ⊢ P -> *)
  (*                   P = Q; *)
  derives_refl : forall P, P ⊢ P;
  derives_trans : forall P Q R, P ⊢ Q -> Q ⊢ R ->
                           P ⊢ R;

  andp_right :  forall X P Q, X ⊢ P -> X ⊢ Q ->
                         X ⊢ P ∧ Q;
  andp_left1 :  forall P Q R, P ⊢ R ->
                         P ∧ Q ⊢ R;
  andp_left2 :  forall P Q R, Q ⊢ R ->
                         P ∧ Q ⊢ R;
  orp_left : forall P Q R, P ⊢ R -> Q ⊢ R ->
                      P ∨ Q ⊢ R;
  orp_right1 : forall P Q R, P ⊢ Q ->
                        P ⊢ Q ∨ R;
  orp_right2 : forall P Q R, P ⊢ R ->
                        P ⊢ Q ∨ R;
  exp_right : forall {B : Set} (x : B) (P: A) (Q: B -> A), P ⊢ (Q x) ->
                                                     P ⊢ (exp Q);
  exp_left : forall {B : Set} (P : B -> A) (Q : A),
       (forall x, (P x) ⊢ Q) -> (exp P) ⊢ Q;
  allp_left : forall {B : Set} (P: B -> A) x Q, (P x) ⊢ Q -> (allp P) ⊢ Q;
  allp_right : forall {B : Set} (P: A) (Q: B -> A),  (forall v, P ⊢ (Q v)) -> P ⊢ (allp Q);
  imp_andp_adjoint : forall P Q R, P ∧ Q ⊢ R <-> P ⊢ (Q --> R);
  (* prop_left: forall (P: Prop) Q, (P -> TT ⊢ Q) -> (prop P) ⊢ Q; *)
  (* prop_right: forall (P: Prop) Q, P -> ⊢ Q (prop P); *)
  (* prop_imp_prop_left: forall (P Q: Prop), derives (imp (prop P) (prop Q)) (prop (P -> Q)); *)
  (* allp_prop_left: forall {B: Set} (P: B -> Prop), derives (allp (fun b => prop (P b))) (prop (forall b, P b)) *)
(* not_prop_right: forall (P: A) (Q: Prop), (Q -> derives P FF) -> derives P (prop (not Q)) *)
}.

Class SepLog (A : Type) := mkSepLog {
  is_NatDed :> NatDed A;
  emp : A;
  sepcon : A -> A -> A;
  wand : A -> A -> A;
  (* (* Existential magic wand *) *)
  (* ewand : A -> A -> A; *)
}.

Notation "P '✱' Q" := (sepcon P Q) (at level 45, left associativity) : logic.
Notation "P '-✱' Q" := (wand P Q) (at level 60, right associativity) : logic.
(* Notation "P '-◯' Q" := (ewand P Q) (* Typeset with -\ci5 *) *)
  (* (at level 60, right associativity) : logic. *)

Class SepLogAxioms (A : Type) {SL : SepLog A} := {
  is_NatDedAxioms :> NatDedAxioms A;
  sepcon_assoc: forall (P Q R : A), (P ✱ Q) ✱ R = P ✱ (Q ✱ R);
  sepcon_comm:  forall (P Q : A), P ✱ Q = Q ✱ P;
  wand_sepcon_adjoint: forall (P Q R : A), (P ✱ Q ⊢ R) <-> (P ⊢ Q -✱ R);
  sepcon_andp_prop: forall (P R : A) (Q : Prop), P ✱ (!!Q ∧ R) = !!Q ∧ (P ✱ R);
  sepcon_derives: forall P P' Q Q' : A, P ⊢ P' -> Q ⊢ Q' -> P ✱ Q ⊢ P' ✱ Q';
  (* ewand_sepcon: forall (P Q R : A),  (P ✱ Q) -◯ R = P -◯ (Q ✱ R); *)
  (* ewand_TT_sepcon: forall (P Q R: A), (P ✱ Q) ∧ (R -◯ TT) ⊢ (P ∧ (R -◯ TT)) ✱ (Q ∧ (R -◯ TT)); *)
  (* exclude_elsewhere: forall (P Q : A), P ✱ Q ⊢ (P ∧ (Q -◯ TT)) ✱ Q; *)
  (* ewand_conflict: forall (P Q R : A), P ✱ Q ⊢ FF -> P ∧ (Q -◯ R) ⊢ FF *)
}.
