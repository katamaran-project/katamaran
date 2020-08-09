Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.
Require Import Relations.
Require Import Classes.Equivalence.

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
Notation "'!!' e" := (lprop e) (at level 25) : logic.
Notation "⊥" := lfalse.
Notation "⊤" := ltrue.

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
  lprop_left: forall (P: Prop) Q, (P -> ltrue ⊢ Q) -> lprop P ⊢ Q;
  lprop_right: forall (P: Prop) Q, P -> Q ⊢ lprop P;
}.

Section Equivalence.

  Context {L : Type} {LL : ILogic L} {LLL : ILogicLaws L LL}.

  Definition bientails : relation L :=
    fun P Q => (P ⊢ Q) /\ (Q ⊢ P).

  Global Instance bientails_equiv : Equivalence bientails.
  Proof.
    split.
    - intros P.
      split; apply entails_refl.
    - intros P Q [pq qp].
      split; assumption.
    - intros P Q R [pq qp] [qr rq].
      split; eapply entails_trans; eauto.
  Qed.

End Equivalence.

Notation "P ⊣⊢ Q" := (bientails P Q) (at level 50, no associativity) : logic.

Class ISepLogic (L : Type) := {
  is_ILogic :> ILogic L;
  emp : L;
  sepcon : L -> L -> L;
  wand : L -> L -> L;
}.

Notation "P '✱' Q" := (sepcon P Q) (at level 45, left associativity) : logic.
Notation "P '-✱' Q" := (wand P Q) (at level 60, right associativity) : logic.

Class ISepLogicLaws (L : Type) {SL : ISepLogic L} := {
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
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit).

  (* Definition CEnv : SepContractEnv. *)
  (* Definition CEnvEx : SepContractEnvEx. *)

  Import CtxNotations.
  Import EnvNotations.

  Class IHeaplet (L : Type) := {
    is_ISepLogic :> ISepLogic L;
    pred (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) : L;
    ptsreg  {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Lit σ) : L
  }.

  Section Contracts.
    Context `{Logic : IHeaplet L}.

    Definition inst_chunk {Σ} (ι : SymInstance Σ) (c : Chunk Σ) : L :=
      match c with
      | chunk_pred p ts => pred p (env_map (fun _ => inst_term ι) ts)
      | chunk_ptsreg r t => ptsreg r (inst_term ι t)
      end.

    Fixpoint inst_assertion {Σ} (ι : SymInstance Σ) (a : Assertion Σ) : L :=
      match a with
      | asn_bool b => if inst_term ι b then ltrue else lfalse
      | asn_prop p => !!(uncurry_named p ι) ∧ emp
      | asn_chunk c => inst_chunk ι c
      | asn_if b a1 a2 => if inst_term ι b then inst_assertion ι a1 else inst_assertion ι a2
      | asn_match_enum E k alts => inst_assertion ι (alts (inst_term ι k))
      | asn_sep a1 a2 => inst_assertion ι a1 ✱ inst_assertion ι a2
      | asn_exist ς τ a => ∃ v, @inst_assertion (Σ ▻ (ς , τ)) (ι ► (ς , τ) ↦ v) a
    end.

    (* Definition ValidContract {Γ τ} (c : SepContract Γ τ) : L := *)
    (*   match c with *)
    (*   | sep_contract_unit δ0 req ens => *)
    (*     ∀ δ δΣ, !!(δ = env_map (fun _ t => eval_term t δΣ) δ0) --> *)
    (*               interpret δΣ req ∧ interpret δΣ ens *)
    (*   | sep_contract_result_pure δ0 result req ens => *)
    (*     ∀ δ δΣ, !!(δ = env_map (fun _ t => eval_term t δΣ) δ0) --> *)
    (*               interpret δΣ req ∧ interpret δΣ ens *)
    (*   | @sep_contract_result _ Σ σ δ0 result req ens => *)
    (*     ∀ δ δΣ, !!(δ = env_map (fun _ t => eval_term t δΣ) δ0) --> *)
    (*               interpret δΣ req *)
    (*             ∧ (∀ v, @interpret (Σ ▻ (result , σ)) (δΣ ► (result , σ) ↦ v) ens) *)
    (*   | sep_contract_none _ => ⊤ *)
    (*   end. *)

  End Contracts.

  Arguments inst_assertion {_ _ _} _ _.
  (* Arguments ValidContract {_ _ _ _} _. *)

  Notation "r '↦' t" := (ptsreg r t) (at level 30).

End HeapKit.
