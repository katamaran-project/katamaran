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

Require Import FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

From Equations Require Import Equations.
Require Import Equations.Prop.EqDec.

From Katamaran Require Import
     Environment Sep.Logic Sep.Spec Syntax.
(* Require Import MicroSail.Sep.Hoare. *)

(* Simple model (aka Logic Instance) using disjoint register-heaps *)

(* VST heavily relies of predicate extensionality to establish equality of
   heap propositions. To the contrary, Mirror Shard does not assume pred ext, but
   proves implications (even not <->) instead of qualities.

   The logic typelcasses we adopted from VST are tailored towards pred ext; thus, perhaps,
   we will need to look into other interfaces or adopt pred ext. *)


Module Disjoint
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).

  Import LogicNotations.
  Open Scope logic.

  Definition Heap : Type := forall σ, 𝑹𝑬𝑮 σ -> option (Lit σ).

  (* convert a register store into a heap *)
  Definition heap (rs : RegStore) : Heap :=
    fun _ r => Some (read_register rs r).

  Definition emp : Heap := fun _ _ => None.

  (* A heap is total if every register points to a Some *)
  Definition Total (h : Heap) : Prop :=
    forall σ r, exists v, h σ r = Some v.

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
  Hint Unfold bientails : seplogic.

  Lemma split_eq {γ1 γ2 γl γr} :
    split γ1 γl γr -> split γ2 γl γr -> γ1 = γ2.
  Proof.
    intros.
    extensionality σ.
    extensionality r.
    heap_solve_split.
  Qed.

  Lemma split_eq_right {γ γl γr1 γr2} :
    split γ γl γr1 -> split γ γl γr2 -> γr1 = γr2.
  Proof.
    intros.
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

  Lemma sepcon_emp (P : HProp) : P ✱ Logic.emp ⊣⊢s P.
  Proof.
    split.
    - intros γ (γl & γr & H1 & H2 & H3).
      assert (γr = emp).
      { extensionality σ.
        extensionality r.
        apply H3.
      }
      subst γr.
      apply split_comm, split_emp in H1.
      now subst γl.
    - intros γ H1. cbn.
      exists γ, emp.
      split.
      apply split_comm, split_emp; reflexivity.
      split.
      assumption.
      reflexivity.
  Qed.
  Hint Resolve sepcon_emp : seplogic.

  Program Instance HProp_ISepLogicLaws : ISepLogicLaws HProp.
  Solve Obligations with eauto with seplogic.
  Admit Obligations of HProp_ISepLogicLaws.

  Program Instance HProp_Heaplet : IHeaplet HProp :=
  { (* We don't have any predicates in this model yet;
       thus we map the predicate to False *)
    luser (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) := fun γ => False;
    lptsreg (σ : Ty) (r : 𝑹𝑬𝑮 σ) (t : Lit σ) := fun γ => γ σ r = Some t;
  }.
  Next Obligation.
    intros p ts hdup h hyp.
    contradict hyp.
  Qed.

  Definition write_heap (γ : Heap) {σ} (r : 𝑹𝑬𝑮 σ)
    (v : Lit σ) : Heap :=
    fun τ r' =>
      match eq_dec_het r r' with
      | left e => Some (eq_rect σ Lit v τ (f_equal projT1 e))
      | right _ => γ τ r'
      end.

  (* writing into a heap creates a ptsreg heap chunk *)
  Lemma write_heap_ptsreg (γ : Heap) {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
    (write_heap γ r v) σ r = Some v.
  Proof.
    unfold write_heap, eq_dec_het.
    now rewrite eq_dec_refl.
  Qed.

  (* writing into a heap preserves the unaffected chunks *)
  Lemma write_heap_distinct (γfocus : Heap) {σ τ}
        (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ) (prf : existT _ r <> existT _ k)
        (v0 : option (Lit τ)) (v : Lit σ) :
    γfocus τ k = v0 -> (write_heap γfocus r v) τ k = v0.
  Proof.
    intros H.
    rewrite <- H.
    unfold write_heap.
    destruct (eq_dec_het r k).
    + contradiction.
    + reflexivity.
  Qed.

  (* writing into a heap preserves totality *)
  Lemma write_heap_preservers_total {σ} :
    forall (γ : Heap), Total γ -> forall (r : 𝑹𝑬𝑮 σ) (v : Lit σ), Total (write_heap γ r v).
  Proof.
    intros γ Htotal_γ r v τ k.
    specialize (Htotal_γ τ k); destruct Htotal_γ as [v0 Hpre].
    unfold write_heap.
    destruct (eq_dec_het r k).
    + eexists. reflexivity.
    + exists v0. apply Hpre.
  Qed.

  (* If a value is present in one of the two disjoint subheaps, then
     it must be absent in the other *)
  Lemma split_in_r_then_not_in_l {σ}
        (γ γl γr : Heap) (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
        split γ γl γr -> γr σ r = Some v -> γl σ r = None.
  Proof.
    intros Hsplit_γ H.
    unfold split in Hsplit_γ.
    specialize (Hsplit_γ σ r) as [[Heq1|Heq1] Heq2].
    - rewrite Heq1 in Heq2.
      congruence.
    - congruence.
  Qed.

  (* If a value is the heap is total and a value is absent in
     one if the disjoint subheaps then in must be present in the other *)
  Lemma split_not_in_r_then_in_l {σ}
        (γ γl γr : Heap) (r : 𝑹𝑬𝑮 σ) :
        Total γ -> split γ γl γr -> γr σ r = None -> (exists v, γl σ r = Some v).
  Proof.
    intros Htotal_γ Hsplit_γ H.
    unfold split in Hsplit_γ.
    unfold Total in *.
    specialize (Hsplit_γ σ r).
    destruct_conjs.
    destruct H0.
    + rewrite H0 in H1.
      specialize (Htotal_γ σ r).
      destruct_conjs. congruence.
    + rewrite H0 in H1.
      destruct (γl σ r).
      ++ now exists l.
      ++ specialize (Htotal_γ σ r).
         destruct_conjs.
         congruence.
  Qed.

  Lemma write_register_write_heap (rs : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
    heap (write_register rs r v) = write_heap (heap rs) r v.
  Proof.
    extensionality τ.
    extensionality k.
    unfold heap, write_heap; cbn.
    destruct (eq_dec_het r k).
    - f_equal.
      dependent elimination e; cbn.
      now rewrite read_write.
    - now rewrite read_write_distinct.
  Qed.

End Disjoint.
