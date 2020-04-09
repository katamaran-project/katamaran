Require Import FunctionalExtensionality.

Require Import MicroSail.Syntax.
Require Import MicroSail.Environment.
Require Import MicroSail.Sep.Logic.
Require Import MicroSail.Sep.Spec.
Require Import MicroSail.Sep.Hoare.

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
       (Import heapkit : HeapKit typekit termkit progkit assertkit).

  Open Scope logic.

  Definition Heap : Type := forall σ, 𝑹𝑬𝑮 σ -> option (Lit σ).

  Definition emp : Heap := fun _ _ => None.

  Definition HProp (Γ : Ctx (𝑿 * Ty)) := LocalStore Γ -> Heap -> Prop.

  Program Instance HProp_NatDed (Γ : Ctx (𝑿 * Ty)) : NatDed (HProp Γ) :=
  { andp := (fun P Q => (fun δ γ => P δ γ /\ Q δ γ));
    orp  := (fun P Q => (fun δ γ => P δ γ \/ Q δ γ));
    (* existential quantification *)
    exp := (fun {T : Type} (P : T -> HProp Γ) => (fun δ γ => exists x, P x δ γ));
    (* universal quantification *)
    allp := (fun {T : Type} (P : T -> HProp Γ) => (fun δ γ => forall x, P x δ γ));
    imp := (fun P Q => (fun δ γ => P δ γ -> Q δ γ));

    (* Prop embedding *)
    prop := (fun (p : Prop) => (fun δ γ => p));
    (* P ⊢ Q *)
    derives := (fun P Q => forall δ γ, P δ γ -> Q δ γ)
  }.

  Program Instance HProp_NatDedAxioms (Γ : Ctx (𝑿 * Ty)) : @NatDedAxioms _ (HProp_NatDed Γ).
  Solve Obligations with firstorder.

  (* Check if two heaps are disjoint,
     Peter O'Hearn's Marktoberdorf notes call this '#'. *)
  Definition split (γ γl γr : Heap) : Prop :=
    forall (σ : Ty) (r : 𝑹𝑬𝑮 σ), (γl σ r = None \/ γr σ r = None) /\
                             γ σ r = match γl σ r with
                                     | None => γr σ r
                                     | Some x => Some x
                                     end.

  Program Instance HProp_SepLog (Γ : Ctx (𝑿 * Ty)) : SepLog (HProp Γ) :=
  { emp := fun δ γ => forall σ r, γ σ r = None;
    sepcon P Q := fun δ γ => exists γl γr, split γ γl γr /\ P δ γl /\ Q δ γr;
    wand P Q := fun δ γl => forall γ γr, split γ γl γr -> P δ γr -> Q δ γ
  }.

  (* Solve a heap partitioning goal of form 'split γ γl γr' *)
  Local Ltac heap_solve_split :=
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
      end; cbn in *; try congruence.

  Lemma split_comm {Γ : Ctx (𝑿 * Ty)} : forall γ γ1 γ2, split γ γ1 γ2 -> split γ γ2 γ1.
  Proof. heap_solve_split. Qed.

  Lemma split_emp {Γ : Ctx (𝑿 * Ty)} : forall γ γ1, split γ emp γ1 <-> γ = γ1.
  Proof.
    intros γ γ1.
    split.
    - intros H.
      extensionality σ. extensionality r.
      heap_solve_split.
    - heap_solve_split.
  Qed.

  Lemma split_assoc : forall γ γl γr γll γlr,
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

  Lemma sepcon_comm_forward (Γ : Ctx (𝑿 * Ty)) : forall (P Q : HProp Γ),
      forall δ γ, (P ✱ Q --> Q ✱ P) δ γ.
  Proof.
    intros P Q δ γ.
    cbn.
    intros.
    destruct H as [γl [γr H]].
    exists γr. exists γl.
    destruct H as [H1 [H2 H3]].
    split.
    - apply (@split_comm Γ _ _ _ H1).
    - firstorder.
  Qed.

  Lemma sepcon_assoc_forward {Γ : Ctx (𝑿 * Ty)} : forall (P Q R : HProp Γ),
    forall δ γ, ((P ✱ Q ✱ R) --> (P ✱ (Q ✱ R))) δ γ.
  Proof.
    intros P Q R δ γ.
    cbn.
    intros H.
    destruct H as [γl [γr [H_split_1 [H HR]]]].
    destruct H as [γl' [γr' [H_split_2 [HP HQ]]]].
    specialize (split_assoc γ γl γr γl' γr' H_split_1 H_split_2) as H_split_3.
    inversion H_split_3 as [γcomp H_split_comp].
    exists γl'. exists γcomp.
    split.
    - apply H_split_comp.
    - split.
      + apply HP.
      + exists γr'. exists γr.
        intuition.
  Qed.

  Lemma wand_sepcon_adjoint {Γ : Ctx (𝑿 * Ty)} : forall (P Q R : HProp Γ),
      (P ✱ Q ⊢ R) <-> (P ⊢ Q -✱ R).
  Proof.
    intros P Q R.
    split.
    - intros H.
      cbn in *.
      intros δ γl HP γ γr H_split HQ.
      specialize (H δ γ).
      apply H.
      exists γl. exists γr.
      intuition.
    - intros H.
      cbn in *.
      intros δ γl H1.
      (* specialize (H δ γl). *)
      destruct H1 as [γll [γlr [H_split [HP HQ]]]].
      exact (H δ γll HP γl γlr H_split HQ).
  Qed.

Lemma sepcon_andp_prop {Γ : Ctx (𝑿 * Ty)} : forall (P R : HProp Γ) (Q : Prop),
      (P ✱ (!!Q ∧ R)) <-> (!!Q ∧ (P ✱ R)).


  sepcon_entails: forall P P' Q Q' : A, P ⊢ P' -> Q ⊢ Q' -> P ✱ Q ⊢ P' ✱ Q';
