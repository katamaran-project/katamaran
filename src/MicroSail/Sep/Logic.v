Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Sep.Spec.

(* Abstract logic interface, implemented as a Coq typeclasses

   Partially adopted from Gregory Malecha's PhD thesis (Chapter 7.1) and
   VST https://github.com/PrincetonUniversity/VST/blob/master/msl/seplog.v
*)

Class ILogic (L : Type) :=
{ lentails : L -> L -> Prop;
  ltrue : L;
  lfalse : L;
  land : L -> L -> L;
  lor : L -> L -> L;
  limpl : L -> L -> L;
  lprop: Prop -> L;
  lex : forall {T : Type}, (T -> L) -> L;
  lall : forall {T : Type}, (T -> L) -> L
 }.


Delimit Scope logic with logic.
Local Open Scope logic.
Notation "P '⊢' Q" := (lentails P Q) (at level 80, no associativity) : logic_entails.
Open Scope logic_entails.
Notation "'∃' x .. y , P " :=
  (lex (fun x => .. (lex (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Notation "'∀' x .. y , P " :=
  (lall (fun x => .. (lall (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Infix "∨" := lor (at level 50, left associativity) : logic.
Infix "∧" := land (at level 40, left associativity) : logic.
Notation "P '-->' Q" := (limpl P Q) (at level 55, right associativity) : logic.
Notation "P '<-->' Q" := (land (limpl P Q) (limpl Q P))
  (at level 57, no associativity) : logic.
Notation "P ⊣⊢ Q" := ((P ⊢ Q) /\ (Q ⊢ P)) (at level 50, no associativity) : logic.
Notation "'!!' e" := (lprop e) (at level 25) : logic.

Class ILogicLaws (L : Type) (LL : ILogic L) :=
{ entails_refl  : forall P, P ⊢ P;
  entails_trans : forall P Q R, P ⊢ Q -> Q ⊢ R -> P ⊢ R;
  land_right :  forall X P Q, X ⊢ P -> X ⊢ Q -> X ⊢ P ∧ Q;
  land_left1 :  forall P Q R, P ⊢ R -> P ∧ Q ⊢ R;
  land_left2 :  forall P Q R, Q ⊢ R -> P ∧ Q ⊢ R;
  lor_left : forall P Q R, P ⊢ R -> Q ⊢ R -> P ∨ Q ⊢ R;
  lor_right1 : forall P Q R, P ⊢ Q -> P ⊢ Q ∨ R;
  lor_right2 : forall P Q R, P ⊢ R -> P ⊢ Q ∨ R;
  lex_right  : forall {B : Type} (x : B) (P: L) (Q: B -> L), P ⊢ (Q x) -> P ⊢ (lex Q);
  lex_left   : forall {B : Type} (P : B -> L) (Q : L), (forall x, (P x) ⊢ Q) -> (lex P) ⊢ Q;
  lall_left  : forall {B : Type} (P: B -> L) x Q, (P x) ⊢ Q -> (lall P) ⊢ Q;
  lall_right : forall {B : Type} (P: L) (Q: B -> L),  (forall v, P ⊢ (Q v)) -> P ⊢ (lall Q);
  limpl_and_adjoint : forall P Q R, P ∧ Q ⊢ R <-> P ⊢ (Q --> R);
}.

Class ISepLogic (L : Type) := {
  is_ILogic :> ILogic L;
  emp : L;
  sepcon : L -> L -> L;
  wand : L -> L -> L;
}.

Notation "P '✱' Q" := (sepcon P Q) (at level 45, left associativity) : logic.
Notation "P '-✱' Q" := (wand P Q) (at level 60, right associativity) : logic.

Class ISepLogicLaws (L : Type) (SL : ISepLogic L) := {
  is_ILogicLaws :> ILogicLaws L is_ILogic;
  sepcon_assoc: forall (P Q R : L), ((P ✱ Q) ✱ R) ⊣⊢ (P ✱ (Q ✱ R));
  sepcon_comm:  forall (P Q : L), P ✱ Q ⊣⊢ Q ✱ P;
  wand_sepcon_adjoint: forall (P Q R : L), (P ✱ Q ⊢ R) <-> (P ⊢ Q -✱ R);
  sepcon_andp_prop: forall (P R : L) (Q : Prop), P ✱ (!!Q ∧ R) ⊣⊢ !!Q ∧ (P ✱ R);
  sepcon_entails: forall P P' Q Q' : L, P ⊢ P' -> Q ⊢ Q' -> P ✱ Q ⊢ P' ✱ Q';
}.

Module Type HeapKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit).

  Class IHeaplet (L : Type) := {
    is_ISepLogic :> ISepLogic L;
    pred (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) : L;
    ptsreg  {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Lit σ) : L
  }.

Notation "r '↦' t" := (ptsreg r t) (at level 30).

End HeapKit.
