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
     Classes.RelationClasses
     FunctionalExtensionality
     Program.Tactics.

From Equations Require Import Equations.
Require Import Equations.Prop.EqDec.

From Katamaran Require Import
     Prelude
     Environment
     Sep.Logic
     Specification
     Syntax.ContractDecl
     Program.
(* Require Import MicroSail.Sep.Hoare. *)

(* Simple model (aka Logic Instance) using disjoint register-heaps *)

(* VST heavily relies of predicate extensionality to establish equality of
   heap propositions. To the contrary, Mirror Shard does not assume pred ext, but
   proves implications (even not <->) instead of qualities.

   The logic typelcasses we adopted from VST are tailored towards pred ext; thus, perhaps,
   we will need to look into other interfaces or adopt pred ext. *)

Module Type DisjointModel
  (Import B : Base)
  (Import SIG : ProgramLogicSignature B)
  (Import SPEC : Specification B SIG).

  Definition Heap : Type := forall σ, 𝑹𝑬𝑮 σ -> option (Val σ).
  (* Check if two heaps are disjoint,
     Peter O'Hearn's Marktoberdorf notes call this '#'. *)
  Definition split (γ γl γr : Heap) : Prop :=
    forall (σ : Ty) (r : 𝑹𝑬𝑮 σ), (γl σ r = None \/ γr σ r = None) /\
                             γ σ r = match γl σ r with
                                     | None => γr σ r
                                     | Some x => Some x
                                     end.

  (* convert a register store into a heap *)
  Definition heap (rs : RegStore) : Heap :=
    fun _ r => Some (read_register rs r).

  Definition empty : Heap := fun _ _ => None.

  (* A heap is total if every register points to a Some *)
  Definition Total (h : Heap) : Prop :=
    forall σ r, exists v, h σ r = Some v.

  Definition disjoint (γl γr : Heap) : Prop :=
    forall σ (r : 𝑹𝑬𝑮 σ), γl σ r <> None -> γr σ r <> None -> False.

  Definition join (γl γr : Heap) (_ : disjoint γl γr) : Heap :=
    fun σ r => match γl σ r with
            | None => γr σ r
            | Some v => Some v
            end.

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
      | [ |- @eq Heap _ _ ] =>
          let σ := fresh "σ" in
          let r := fresh "r" in
          extensionality σ; extensionality r
      end; cbn in *; try congruence; try eauto with seplogic.

  Lemma split_eq {γ1 γ2 γl γr} :
    split γ1 γl γr -> split γ2 γl γr -> γ1 = γ2.
  Proof. heap_solve_split. Qed.

  Lemma split_eq_right {γ γl γr1 γr2} :
    split γ γl γr1 -> split γ γl γr2 -> γr1 = γr2.
  Proof. heap_solve_split. Qed.

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
  Local Hint Resolve split_assoc_l : seplogic.

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
  Local Hint Resolve split_assoc_r : seplogic.

  Lemma split_comm : forall γ γ1 γ2, split γ γ1 γ2 -> split γ γ2 γ1.
  Proof. heap_solve_split. Qed.
  Local Hint Resolve split_comm : seplogic.

  Lemma split_empty : forall γ γ1, split γ empty γ1 <-> γ = γ1.
  Proof. split; heap_solve_split. Qed.
  Local Hint Resolve split_empty : seplogic.

  Lemma lsep_assoc' (P Q R : Heap -> Prop) :
    (forall γ : Heap,
     (exists γl γr : Heap, split γ γl γr /\ P γl /\ (exists γl0 γr0 : Heap, split γr γl0 γr0 /\ Q γl0 /\ R γr0)) ->
     exists γl γr : Heap, split γ γl γr /\ (exists γl0 γr0 : Heap, split γl γl0 γr0 /\ P γl0 /\ Q γr0) /\ R γr) /\
    (forall γ : Heap,
     (exists γl γr : Heap, split γ γl γr /\ (exists γl0 γr0 : Heap, split γl γl0 γr0 /\ P γl0 /\ Q γr0) /\ R γr) ->
     exists γl γr : Heap, split γ γl γr /\ P γl /\ (exists γl0 γr0 : Heap, split γr γl0 γr0 /\ Q γl0 /\ R γr0)).
  Proof.
    split.
    - intros γ H.
      cbn in *.
      destruct H as [γl [γr [H_split_1 [HP H]]]].
      destruct H as [γrl [γrr [H_split_2 [HQ HR]]]].
      specialize (split_comm _ _ _ H_split_1) as H_split_1'.
      specialize (split_comm _ _ _ H_split_2) as H_split_2'.
      specialize (split_assoc_l γ γr γl γrr γrl H_split_1' H_split_2') as H_split_3.
      destruct H_split_3 as [γcomp H_split_comp].
      exists γcomp, γrr.
      split.
      + intuition.
      + split.
        * exists γl, γrl.
          intuition.
        * intuition.
    - intros γ H.
      destruct H as [γl [γr [H_split_1 [H HR]]]].
      destruct H as [γl' [γr' [H_split_2 [HP HQ]]]].
      specialize (split_assoc_l γ γl γr γl' γr' H_split_1 H_split_2) as H_split_3.
      inversion H_split_3 as [γcomp H_split_comp].
      exists γl'. exists γcomp.
      split.
      + apply H_split_comp.
      + split.
        * apply HP.
        * exists γr'. exists γr.
          intuition.
  Qed.

  Lemma lsep_comm' (P Q : Heap -> Prop) (γ : Heap) :
    (exists γl γr : Heap, split γ γl γr /\ P γl /\ Q γr) ->
    (exists γl γr : Heap, split γ γl γr /\ Q γl /\ P γr).
  Proof.
    intros (γl & γr & HS & HP & HQ).
    exists γr, γl. auto using split_comm.
  Qed.

  Lemma lsep_emp' (P : Heap -> Prop) :
    (forall γ : Heap, (exists γl γr : Heap, split γ γl γr /\ P γl /\ (forall (σ : Ty) (r : 𝑹𝑬𝑮 σ), γr σ r = None)) -> P γ) /\
    (forall γ : Heap, P γ -> exists γl γr : Heap, split γ γl γr /\ P γl /\ (forall (σ : Ty) (r : 𝑹𝑬𝑮 σ), γr σ r = None)).
  Proof.
    split.
    - intros γ (γl & γr & H1 & H2 & H3).
      assert (γr = empty).
      { extensionality σ.
        extensionality r.
        apply H3.
      }
      subst γr.
      apply split_comm, split_empty in H1.
      now subst γl.
    - intros γ H1. cbn.
      exists γ, empty.
      split.
      apply split_comm, split_empty; reflexivity.
      split.
      assumption.
      now intro.
  Qed.

  Import sep.notations.

  Local Obligation Tactic :=
    first
      [ apply lsep_assoc'
      | split; apply lsep_comm'
      | apply lsep_emp'
      | firstorder; fail
      | cbn
      ].

  Program Definition HProp : SepLogic :=
    {| lcar         := Heap -> Prop;
       lentails P Q := forall γ, P γ -> Q γ;
       land P Q     := fun γ => P γ /\ Q γ;
       lor P Q      := fun γ => P γ \/ Q γ;
       limpl P Q    := fun γ => P γ -> Q γ;
       lprop P      := fun _ => P;
       lex T P      := fun γ => exists x, P x γ;
       lall T P     := fun γ => forall x, P x γ;
       lemp         := fun γ => forall σ r, γ σ r = None;
       lsep P Q     := fun γ => exists γl γr, split γ γl γr /\ P γl /\ Q γr;
       lwand P Q    := fun γl => forall γ γr, split γ γl γr -> P γr -> Q γ;
    |}.
  Next Obligation.
    (* lsep_leak *)
  Admitted.

  (* This should be constructed from a parameter of the model. *)
  Program Instance pi_hprop : PredicateDef HProp :=
    {| lptsreg σ r t := fun γ => γ σ r = Some t;
       (* We don't have any predicates in this model yet;
          thus we map the predicate to False *)
       luser p ts    := fun _ => False;
    |}.

  Definition write_heap (γ : Heap) {σ} (r : 𝑹𝑬𝑮 σ)
    (v : Val σ) : Heap :=
    fun τ r' =>
      match eq_dec_het r r' with
      | left e => Some (eq_rect σ Val v τ (f_equal projT1 e))
      | right _ => γ τ r'
      end.

  (* writing into a heap creates a ptsreg heap chunk *)
  Lemma write_heap_ptsreg (γ : Heap) {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
    (write_heap γ r v) σ r = Some v.
  Proof.
    unfold write_heap, eq_dec_het.
    now rewrite eq_dec_refl.
  Qed.

  (* writing into a heap preserves the unaffected chunks *)
  Lemma write_heap_distinct (γfocus : Heap) {σ τ}
        (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ) (prf : existT _ r <> existT _ k)
        (v0 : option (Val τ)) (v : Val σ) :
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
    forall (γ : Heap), Total γ -> forall (r : 𝑹𝑬𝑮 σ) (v : Val σ), Total (write_heap γ r v).
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
        (γ γl γr : Heap) (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
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
      ++ now exists v.
      ++ specialize (Htotal_γ σ r).
         destruct_conjs.
         congruence.
  Qed.

  Lemma write_register_write_heap (rs : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
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

End DisjointModel.
