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
    wand P Q := fun δ γ => forall γl γr, split γ γl γr -> P δ γl -> Q δ γr
  }.

  Lemma split_comm {Γ : Ctx (𝑿 * Ty)} : forall γ γ1 γ2, split γ γ1 γ2 -> split γ γ2 γ1.
  Proof.
    intros γ γ1 γ2.
    intros H.
    unfold split.
    intros σ r.
    destruct (H σ r) as [H1 H2].
    split.
    + rewrite or_comm.
      apply H1.
    + rewrite H2.
      destruct (γ1 σ r); destruct (γ2 σ r);
        destruct H1; congruence.
  Qed.

  (* This lemma is wrong, but I want something like this. Am I trying to reinvent the
     frame rule?.. *)
  Lemma split_weaken {Γ : Ctx (𝑿 * Ty)} : forall γ γl γr γll γlr,
      split γ γl γr -> split γl γll γlr -> split γ γll γlr.
  Abort.

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
    forall δ γ, ((P ✱ Q ✱ R) --> P ✱ (Q ✱ R)) δ γ.
  Proof.
    intros P Q R δ γ.
    cbn.
    intros H.
    destruct H as [γl [γr [H_split_1 [H HR]]]].
    inversion H as [γl' [γr' [H_split_2 [HP HQ]]]].
    exists γl'. exists γr'.
    split.
    - unfold split.
      (* unfold split in H_split_2. *)
      intros σ r.
      specialize (H_split_2 σ r).
      destruct (γl' σ r); destruct (γr' σ r); destruct (γ σ r); destruct (γl σ r);
      repeat match goal with
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : Some _ = None |- _ ] => discriminate
      end.
  Abort.
