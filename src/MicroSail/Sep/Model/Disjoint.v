Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.
(* Require Import MicroSail.Sep.Hoare. *)

(* Simple model (aka Logic Instance) using disjoint register-heaps *)

(* VST heavily relies of predicate extensionality to establish equality of
   heap propositions. To the contrary, Mirror Shard does not assume pred ext, but
   proves implications (even not <->) instead of qualities.

   The logic typelcasses we adopted from VST are tailored towards pred ext; thus, perhaps,
   we will need to look into other interfaces or adopt pred ext. *)


Module Disjoint
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit)
       (Import heapkit : HeapKit typekit termkit progkit assertkit contractkit).

  Open Scope logic.

  Definition Heap : Type := forall σ, 𝑹𝑬𝑮 σ -> option (Lit σ).

  Definition emp : Heap := fun _ _ => None.

  Definition HProp : Type := Heap -> Prop.

  Instance HProp_ILogic : ILogic HProp :=
  { land := (fun P Q => (fun γ => P γ /\ Q γ));
    lor  := (fun P Q => (fun γ => P γ \/ Q γ));
    (* existential quantification *)
    lex := (fun {T : Type} (P : T -> HProp) => (fun γ => exists x, P x γ));
    (* universal quantification *)
    lall := (fun {T : Type} (P : T -> HProp) => (fun γ => forall x, P x γ));
    limpl := (fun P Q => (fun γ => P γ -> Q γ));

    (* Prop embedding *)
    lprop := (fun (p : Prop) => (fun _ => p));
    (* P ⊢ Q *)
    lentails := (fun P Q => forall γ, P γ -> Q γ);

    ltrue := fun _ => True;
    lfalse := fun _ => False
  }.

  Program Instance HProp_ILogicLaws : @ILogicLaws HProp HProp_ILogic.
  Solve Obligations with firstorder.

  (* Check if two heaps are disjoint,
     Peter O'Hearn's Marktoberdorf notes call this '#'. *)
  Definition split (γ γl γr : Heap) : Prop :=
    forall (σ : Ty) (r : 𝑹𝑬𝑮 σ), (γl σ r = None \/ γr σ r = None) /\
                             γ σ r = match γl σ r with
                                     | None => γr σ r
                                     | Some x => Some x
                                     end.

  Definition disjoint (γl γr : Heap) : Prop :=
    forall σ (r : 𝑹𝑬𝑮 σ), γl σ r <> None -> γr σ r <> None -> False.

  Definition join (γl γr : Heap) (_ : disjoint γl γr) : Heap :=
    fun σ r => match γl σ r with
            | None => γr σ r
            | Some v => Some v
            end.

  Program Instance HProp_ISepLogic : ISepLogic HProp :=
  { emp := fun γ => forall σ r, γ σ r = None;
    sepcon P Q := fun γ => exists γl γr, split γ γl γr /\ P γl /\ Q γr;
    wand P Q := fun γl => forall γ γr, split γ γl γr -> P γr -> Q γ
  }.

  (* Solve a heap partitioning goal of form 'split γ γl γr' *)
  Ltac heap_solve_split :=
      repeat match goal with
      | [ |- split _ _ _ ] => unfold split in *
      | [ H : split _ _ _ |- _ ] => unfold split in *
      | [ |- forall x, _] => intro
      | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H')
      | [ γ : Heap , σ : Ty , r : 𝑹𝑬𝑮 _ |- _ ] => destruct (γ σ r); clear γ
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : Some ?l1 = Some ?l2 |- _ ] => rewrite H
      | [ |- _ /\ _ ] => split
      | [ |- _ \/ _ ] => auto
      end; cbn in *; try congruence; try eauto with seplogic.

  Create HintDb seplogic.

  Lemma split_eq : forall γ1 γ2 γl γr, split γ1 γl γr -> split γ2 γl γr -> γ1 = γ2.
  Proof.
    intros γ1 γ2 γl γr H1 H2.
    extensionality σ.
    extensionality r.
    heap_solve_split.
  Qed.

  Lemma split_comm : forall γ γ1 γ2, split γ γ1 γ2 -> split γ γ2 γ1.
  Proof. heap_solve_split. Qed.
  Hint Resolve split_comm : seplogic.

  Lemma split_emp : forall γ γ1, split γ emp γ1 <-> γ = γ1.
  Proof.
    intros γ γ1.
    split.
    - intros H.
      extensionality σ. extensionality r.
      heap_solve_split.
    - heap_solve_split.
  Qed.
  Hint Resolve split_emp : seplogic.

  Lemma split_assoc_l : forall γ γl γr γll γlr,
    split γ γl γr -> split γl γll γlr ->
    exists f, split γ γll f /\ split f γlr γr.
  Proof.
    intros γ γl γr γll γlr H_split_1 H_split_2.
    exists (fun σ r => match γr σ r with
               | None => γlr σ r
               | Some x => Some x
               end).
    split; heap_solve_split.
  Qed.
  Hint Resolve split_assoc_l : seplogic.

  Lemma split_assoc_r : forall γ γl γr γrl γrr,
    split γ γl γr -> split γr γrl γrr ->
    exists f, split γ f γrr /\ split f γl γrl.
  Proof.
    intros γ γl γr γrl γrr H_split_1 H_split_2.
    exists (fun σ r => match γl σ r with
               | None => γrl σ r
               | Some x => Some x
               end).
    split; heap_solve_split.
  Qed.
  Hint Resolve split_assoc_r : seplogic.

  Lemma sepcon_comm : forall (P Q : HProp), P ✱ Q ⊢ Q ✱ P.
  Proof.
    intros P Q γ H.
    destruct H as [γl [γr H]].
    exists γr. exists γl.
    destruct H as [H1 [H2 H3]].
    split.
    + apply (@split_comm _ _ _ H1).
    + firstorder.
  Qed.
  Hint Resolve sepcon_comm : seplogic.

  Lemma sepcon_assoc_forward : forall (P Q R : HProp), P ✱ Q ✱ R ⊢ P ✱ (Q ✱ R).
  Proof.
    cbn.
    intros P Q R γ H.
    destruct H as [γl [γr [H_split_1 [H HR]]]].
    destruct H as [γl' [γr' [H_split_2 [HP HQ]]]].
    specialize (split_assoc_l γ γl γr γl' γr' H_split_1 H_split_2) as H_split_3.
    inversion H_split_3 as [γcomp H_split_comp].
    exists γl'. exists γcomp.
    split.
    * apply H_split_comp.
    * split.
    + apply HP.
    + exists γr'. exists γr.
      intuition.
  Qed.
  Hint Resolve sepcon_assoc_forward : seplogic.

  Lemma sepcon_assoc_backward : forall (P Q R : HProp), P ✱ (Q ✱ R) ⊢ P ✱ Q ✱ R.
  Proof.
    intros P Q R γ H.
    cbn in *.
    destruct H as [γl [γr [H_split_1 [HP H]]]].
    destruct H as [γrl [γrr [H_split_2 [HQ HR]]]].
    specialize (split_comm _ _ _ H_split_1) as H_split_1'.
    specialize (split_comm _ _ _ H_split_2) as H_split_2'.
    specialize (split_assoc_l γ γr γl γrr γrl H_split_1' H_split_2') as H_split_3.
    destruct H_split_3 as [γcomp H_split_comp].
    exists γcomp, γrr.
    split.
    - intuition.
    - split.
      + exists γl, γrl.
        intuition.
      + intuition.
  Qed.
  Hint Resolve sepcon_assoc_backward : seplogic.

  Lemma wand_sepcon_adjoint : forall (P Q R : HProp),
      (P ✱ Q ⊢ R) <-> (P ⊢ Q -✱ R).
  Proof.
    intros P Q R.
    split.
    - intros H.
      cbn in *.
      intros γl HP γ γr H_split HQ.
      specialize (H γ).
      apply H.
      exists γl. exists γr.
      intuition.
    - intros H.
      cbn in *.
      intros γl H1.
      destruct H1 as [γll [γlr [H_split [HP HQ]]]].
      exact (H γll HP γl γlr H_split HQ).
  Qed.
  Hint Resolve wand_sepcon_adjoint : seplogic.

  Lemma sepcon_andp_prop_forward : forall (P R : HProp) (Q : Prop),
      (P ✱ (!!Q ∧ R)) ⊢ (!!Q ∧ (P ✱ R)).
  Proof.
    intros P R Q γ H.
    destruct H as [γl [γr [H_split [HP [HQ HR]]]]].
    split.
    - intuition.
    - cbn.
      exists γl. exists γr.
      intuition.
  Qed.
  Hint Resolve sepcon_andp_prop_forward : seplogic.

  Lemma sepcon_andp_prop_backward : forall (P R : HProp) (Q : Prop),
      (!!Q ∧ (P ✱ R)) ⊢ (P ✱ (!!Q ∧ R)).
  Proof.
    intros P R Q γ H.
    cbn in *.
    destruct H as [HQ [γl [γr [H_split [HP HR]]]]].
    exists γl, γr.
    split; intuition.
  Qed.
  Hint Resolve sepcon_andp_prop_backward : seplogic.

  Lemma sepcon_entails: forall (P P' Q Q' : HProp),
      P ⊢ P' -> Q ⊢ Q' -> P ✱ Q ⊢ P' ✱ Q'.
  Proof.
    intros P P' Q Q' H1 H2 γ H3.
    cbn in *.
    destruct H3 as [γl [γr [H_split [HP HQ]]]].
    exists γl, γr.
    intuition.
  Qed.
  Hint Resolve sepcon_entails : seplogic.

  Program Instance HProp_ISepLogicLaws : ISepLogicLaws HProp (HProp_ISepLogic).
  Solve Obligations with eauto with seplogic.

  Instance HProp_Heaplet : IHeaplet HProp :=
  { (* We don't have any predicates in this model yet;
       thus we map the predicate to False *)
    pred (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) := fun γ => False;
    ptsreg (σ : Ty) (r : 𝑹𝑬𝑮 σ) (t : Lit σ) := fun γ => γ σ r = Some t
  }.

End Disjoint.
