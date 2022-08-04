(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     Bool.Bool
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     (* Program.Basics *)
     (* Program.Tactics *)
     ZArith.

From Katamaran Require Import
     Prelude
     Tactics
     Sep.Logic
     Syntax.Predicates
     Syntax.Registers
     Base.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Fixpoint heap_extractions `{IsDuplicable C} (h : list C) : list (C * list C) :=
  match h with
  | nil      => nil
  | cons c h => let h' := if is_duplicable c then cons c h else h in
                let ec := pair c h' in
                cons ec (map (base.prod_map id (cons c)) (heap_extractions h))
  end.

Lemma heap_extractions_map `{IsDuplicable A} `{IsDuplicable B} (f : A -> B) (h : list A)
      (is_dup_map : (forall c, is_duplicable (f c) = is_duplicable c)) :
  heap_extractions (List.map f h) = List.map (base.prod_map f (List.map f)) (heap_extractions h).
Proof.
  induction h; cbn.
  - reflexivity.
  - f_equal.
    + unfold base.prod_map; cbn. f_equal.
      rewrite is_dup_map.
      now destruct is_duplicable.
    + rewrite IHh.
      rewrite ?List.map_map.
      apply List.map_ext.
      intros [x xs]; reflexivity.
Qed.

Module Type ChunksOn
  (Import B : Base)
  (Import P : PredicateKit B).

  (* Semi-concrete chunks *)
  Inductive SCChunk : Type :=
  | scchunk_user   (p : 𝑯) (vs : Env Val (𝑯_Ty p))
  | scchunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ)
  | scchunk_conj   (c1 c2 : SCChunk)
  | scchunk_wand   (c1 c2 : SCChunk).
  Global Arguments scchunk_user _ _ : clear implicits.

  (* Symbolic chunks *)
  Inductive Chunk (Σ : LCtx) : Type :=
  | chunk_user   (p : 𝑯) (ts : Env (Term Σ) (𝑯_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ)
  | chunk_conj   (c1 c2 : Chunk Σ)
  | chunk_wand   (c1 c2 : Chunk Σ).
  Global Arguments chunk_user [_] _ _.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for SCChunk.
    Derive NoConfusion for Chunk.
  End TransparentObligations.

  #[export] Instance scchunk_isdup : IsDuplicable SCChunk := {
    is_duplicable := fun c => match c with
                           | scchunk_user p _ => is_duplicable p
                           | scchunk_ptsreg _ _ => false
                           | scchunk_conj _ _ => false
                           | scchunk_wand _ _ => false
                           end
    }.

  #[export] Instance chunk_isdup {Σ} : IsDuplicable (Chunk Σ) := {
    is_duplicable := fun c => match c with
                           | chunk_user p _ => is_duplicable p
                           | chunk_ptsreg _ _ => false
                           | chunk_conj _ _ => false
                           | chunk_wand _ _ => false
                           end
    }.

  Open Scope lazy_bool_scope.

  Fixpoint chunk_eqb {Σ} (c1 c2 : Chunk Σ) : bool :=
    match c1 , c2 with
    | chunk_user p1 ts1, chunk_user p2 ts2 =>
      match eq_dec p1 p2 with
      | left e => env.eqb_hom
                    (@Term_eqb _)
                    (eq_rect _ (fun p => Env _ (𝑯_Ty p)) ts1 _ e)
                    ts2
      | right _ => false
      end
    | chunk_ptsreg r1 t1 , chunk_ptsreg r2 t2 =>
      match eq_dec_het r1 r2 with
      | left e  => Term_eqb
                     (eq_rect _ (Term Σ) t1 _ (f_equal projT1 e))
                     t2
      | right _ => false
      end
    | chunk_conj c11 c12 , chunk_conj c21 c22 =>
      chunk_eqb c11 c21 &&& chunk_eqb c12 c22
    | chunk_wand c11 c12 , chunk_wand c21 c22 =>
      chunk_eqb c11 c21 &&& chunk_eqb c12 c22
    | _ , _ => false
    end.

  Local Set Equations With UIP.

  Lemma chunk_eqb_spec {Σ} :
    forall (c1 c2 : Chunk Σ),
      reflect (c1 = c2) (chunk_eqb c1 c2).
  Proof.
    induction c1; intros [];
      solve_eqb_spec with
      try match goal with
          | |- reflect _ (env.eqb_hom (@Term_eqb ?Σ) ?x ?y) =>
              destruct (env.eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) x y)
          | |- reflect _ (Term_eqb ?x ?y) =>
              destruct (Term_eqb_spec x y)
          end.
  Qed.

  #[export] Instance SubstChunk : Subst Chunk :=
    fix sub_chunk {Σ1} (c : Chunk Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct c} : Chunk Σ2 :=
      match c with
      | chunk_user p ts => chunk_user p (subst ts ζ)
      | chunk_ptsreg r t => chunk_ptsreg r (subst t ζ)
      | chunk_conj c1 c2 =>
        chunk_conj (sub_chunk c1 ζ) (sub_chunk c2 ζ)
      | chunk_wand c1 c2 =>
        chunk_wand (sub_chunk c1 ζ) (sub_chunk c2 ζ)
      end.

  #[export] Instance substlaws_chunk : SubstLaws Chunk.
  Proof.
    constructor.
    { intros ? c. induction c; cbn; f_equal; auto; apply subst_sub_id. }
    { intros ? ? ? ? ? c. induction c; cbn; f_equal; auto; apply subst_sub_comp. }
  Qed.

  #[export] Instance inst_chunk : Inst Chunk SCChunk :=
    fix inst_chunk {Σ} (c : Chunk Σ) (ι : Valuation Σ) {struct c} : SCChunk :=
    match c with
    | chunk_user p ts => scchunk_user p (inst ts ι)
    | chunk_ptsreg r t => scchunk_ptsreg r (inst t ι)
    | chunk_conj c1 c2 => scchunk_conj (inst_chunk c1 ι) (inst_chunk c2 ι)
    | chunk_wand c1 c2 => scchunk_wand (inst_chunk c1 ι) (inst_chunk c2 ι)
    end.

  #[export] Instance inst_subst_chunk : InstSubst Chunk SCChunk.
  Proof.
    intros ? ? ζ ι c; induction c; cbn; f_equal; auto; apply inst_subst.
  Qed.

  Import option.notations.
  #[export] Instance OccursCheckChunk :
    OccursCheck Chunk :=
    fun Σ b bIn =>
      fix occurs_check_chunk (c : Chunk Σ) : option (Chunk (Σ - b)) :=
      match c with
      | chunk_user p ts => option.map (chunk_user p) (occurs_check bIn ts)
      | chunk_ptsreg r t => option.map (chunk_ptsreg r) (occurs_check bIn t)
      | chunk_conj c1 c2 =>
          c1' <- occurs_check_chunk c1 ;;
          c2' <- occurs_check_chunk c2 ;;
          Some (chunk_conj c1' c2')
      | chunk_wand c1 c2 =>
          c1' <- occurs_check_chunk c1 ;;
          c2' <- occurs_check_chunk c2 ;;
          Some (chunk_wand c1' c2')
      end.

  Definition SCHeap : Type := list SCChunk.
  Definition SHeap : LCtx -> Type := fun Σ => list (Chunk Σ).

  #[export] Instance inst_heap : Inst SHeap SCHeap :=
    inst_list.
  #[export] Instance inst_subst_heap : InstSubst SHeap SCHeap.
  Proof. apply inst_subst_list. Qed.

  Fixpoint peval_chunk {Σ} (c : Chunk Σ) : Chunk Σ :=
    match c with
    | chunk_user p ts => chunk_user p (env.map peval ts)
    | chunk_ptsreg r t => chunk_ptsreg r (peval t)
    | chunk_conj c1 c2 => chunk_conj (peval_chunk c1) (peval_chunk c2)
    | chunk_wand c1 c2 => chunk_wand (peval_chunk c1) (peval_chunk c2)
    end.

  Lemma peval_chunk_sound {Σ} (c : Chunk Σ) :
    forall (ι : Valuation Σ),
      inst (peval_chunk c) ι = inst c ι.
  Proof.
    induction c; cbn; intros ι; f_equal; auto using peval_sound.
    unfold inst, inst_env. rewrite env.map_map.
    apply env.map_ext. auto using peval_sound.
  Qed.

  Section Interpretation.
    Import sep.notations.
    Context {HProp} `{PI : PredicateDef HProp}.

    Fixpoint interpret_chunk {Σ} (c : Chunk Σ) (ι : Valuation Σ) {struct c} : HProp :=
      match c with
      | chunk_user p ts => luser p (inst ts ι)
      | chunk_ptsreg r t => lptsreg r (inst t ι)
      | chunk_conj c1 c2 => interpret_chunk c1 ι ∗ interpret_chunk c2 ι
      | chunk_wand c1 c2 => interpret_chunk c1 ι -∗ interpret_chunk c2 ι
      end.

    Fixpoint interpret_scchunk (c : SCChunk) : HProp :=
      match c with
      | scchunk_user p vs => luser p vs
      | scchunk_ptsreg r v => lptsreg r v
      | scchunk_conj c1 c2 => interpret_scchunk c1 ∗ interpret_scchunk c2
      | scchunk_wand c1 c2 => interpret_scchunk c1 -∗ interpret_scchunk c2
      end.

    Definition interpret_scheap : SCHeap -> HProp :=
      List.fold_right (fun c h => interpret_scchunk c ∗ h) lemp.
    Arguments interpret_scheap !h.
  End Interpretation.

End ChunksOn.
