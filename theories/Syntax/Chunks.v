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
     Syntax.Formulas
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
  (Import P : PredicateKit B)
  (Import F : FormulasOn B P).

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
    apply pevals_sound. apply peval_sound.
  Qed.

  Lemma inst_is_duplicable {Σ} (c : Chunk Σ) (ι : Valuation Σ) :
    is_duplicable (inst c ι) = is_duplicable c.
  Proof.
    destruct c; now cbn.
  Qed.

  Section Consume.
    Import EqNotations.

    Fixpoint try_consume_chunk_exact {Σ} (h : SHeap Σ) (c : Chunk Σ) : option (SHeap Σ) :=
      match h with
      | nil       => None
      | cons c' h =>
          if chunk_eqb c c'
          then Some (if is_duplicable c then (cons c h) else h)
          else option_map (cons c') (try_consume_chunk_exact h c)
      end.

    Lemma try_consume_chunk_exact_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option.wlp
        (fun h' => List.In (c , h') (heap_extractions h))
        (try_consume_chunk_exact h c).
    Proof.
      induction h as [|c' h].
      - now constructor.
      - cbn -[is_duplicable].
        destruct (chunk_eqb_spec c c').
        + constructor. left. subst.
          remember (is_duplicable c') as dup.
          destruct dup; reflexivity.
        + apply option.wlp_map. revert IHh.
          apply option.wlp_monotonic; auto.
          intros h' HIn. right.
          rewrite List.in_map_iff.
          exists (c,h'). auto.
    Qed.

    Section PreciseUser.

      Context {Σ} (p : 𝑯) {ΔI ΔO : Ctx Ty} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO)
        (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO).

      Equations(noeqns) match_chunk_user_precise (c : Chunk Σ) : option (PathCondition Σ) :=
        match_chunk_user_precise (chunk_user p' ts')
          with eq_dec p p' => {
            match_chunk_user_precise (chunk_user ?(p) ts') (left eq_refl) :=
              match env.catView (rew prec in ts') with
              | env.isCat tsI' tsO' =>
                  if env.eqb_hom Term_eqb tsI tsI'
                  then Some (formula_eqs_ctx tsO tsO')
                  else None
              end;
            match_chunk_user_precise (chunk_user p' ts') (right _) := None
          };
        match_chunk_user_precise _ := None.

      Fixpoint find_chunk_user_precise (h : SHeap Σ) : option (SHeap Σ * PathCondition Σ) :=
        match h with
        | nil => None
        | cons c h' =>
            match match_chunk_user_precise c with
            | Some eqs => Some (if is_duplicable p then cons c h' else h', eqs)
            | None => option_map (base.prod_map (cons c) id) (find_chunk_user_precise h')
            end
        end.

      Lemma find_chunk_user_precise_spec (h : SHeap Σ) :
        option.wlp
          (fun '(h', eqs) =>
             forall ι : Valuation Σ,
             instprop eqs ι ->
             List.In
               (inst (chunk_user p (eq_rect_r (fun c : Ctx Ty => Env (Term Σ) c) (tsI ►► tsO) prec)) ι, inst h' ι)
               (heap_extractions (inst h ι)))
          (find_chunk_user_precise h).
      Proof.
        induction h as [|c h]; [now constructor|]. cbn [find_chunk_user_precise].
        destruct match_chunk_user_precise as [eqs|] eqn:?.
        - clear IHh. constructor. intros ι Heqs. left.
          destruct c; try discriminate Heqo. cbn in *.
          destruct (eq_dec p p0); cbn in Heqo; try discriminate Heqo. destruct e.
          remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
          destruct (env.catView ts') as [tsI' tsO'].
          destruct (env.eqb_hom_spec Term_eqb (@Term_eqb_spec Σ) tsI tsI'); try discriminate.
          apply noConfusion_inv in Heqo. cbn in Heqo. subst.
          apply instprop_formula_eqs_ctx in Heqs.
          rewrite (@inst_eq_rect_indexed_r (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
          rewrite inst_env_cat. rewrite Heqs. rewrite <- inst_env_cat.
          change (env.cat ?A ?B) with (env.cat A B). rewrite Heqts'.
          rewrite (@inst_eq_rect_indexed (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
          rewrite rew_opp_l. now destruct is_duplicable.
        - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
          intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
          remember (inst (chunk_user p (eq_rect_r (fun c0 : Ctx Ty => Env (Term Σ) c0) (tsI ►► tsO) prec)) ι) as c'.
          change (inst (cons c h) ι) with (cons (inst c ι) (inst h ι)).
          cbn [fst heap_extractions]. right. apply List.in_map_iff.
          eexists (c', inst h' ι); auto.
      Qed.

    End PreciseUser.

    Section PrecisePtsreg.

      Context {Σ σ} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).

      Equations(noeqns) match_chunk_ptsreg_precise (c : Chunk Σ) : option (Formula Σ) :=
        match_chunk_ptsreg_precise (chunk_ptsreg r' t')
          with eq_dec_het r r' => {
            match_chunk_ptsreg_precise (chunk_ptsreg ?(r) t') (left eq_refl) :=
              Some (formula_relop bop.eq t t');
            match_chunk_ptsreg_precise (chunk_ptsreg r' t') (right _) := None
          };
        match_chunk_ptsreg_precise _ := None.

      Fixpoint find_chunk_ptsreg_precise (h : SHeap Σ) : option (SHeap Σ * PathCondition Σ) :=
        match h with
        | nil => None
        | cons c h' =>
            match match_chunk_ptsreg_precise c with
            | Some fml => Some (h', ctx.nil ▻ fml)
            | None => option_map (base.prod_map (cons c) id) (find_chunk_ptsreg_precise h')
            end
        end.

      Lemma find_chunk_ptsreg_precise_spec (h : SHeap Σ) :
        option.wlp
          (fun '(h', eqs) =>
             forall ι : Valuation Σ,
             instprop eqs ι ->
             List.In
               (inst (chunk_ptsreg r t) ι, inst h' ι)
               (heap_extractions (inst h ι)))
          (find_chunk_ptsreg_precise h).
      Proof.
        induction h; cbn [find_chunk_ptsreg_precise]; [now constructor|].
        destruct match_chunk_ptsreg_precise eqn:?.
        - constructor. intros ι [Hpc Hf]. clear IHh.
          destruct a; cbn in Heqo; try discriminate Heqo.
          destruct (eq_dec_het r r0); try discriminate Heqo.
          dependent elimination e. cbn in Heqo. dependent elimination Heqo.
          change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
          cbn. left. f_equal. f_equal. symmetry. exact Hf.
        - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
          intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
          remember (inst (chunk_ptsreg r t) ι) as c'.
          change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
          cbn [fst heap_extractions]. right. apply List.in_map_iff.
          eexists (c', inst h' ι); auto.
      Qed.

    End PrecisePtsreg.

    Definition try_consume_chunk_precise {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option (SHeap Σ * PathCondition Σ) :=
      match c with
      | chunk_user p ts =>
          match 𝑯_precise p with
          | Some (MkPrecise ΔI ΔO Δeq) =>
              match env.catView (rew Δeq in ts) with
              | env.isCat tsI tsO => find_chunk_user_precise Δeq tsI tsO h
              end
          | None => None
          end
      | chunk_ptsreg r t => find_chunk_ptsreg_precise r t h
      | _ => None
      end.

    Lemma try_consume_chunk_precise_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option.wlp
        (fun '(h', eqs) =>
           forall ι : Valuation Σ,
           instprop eqs ι ->
           List.In (inst c ι, inst h' ι)
             (heap_extractions (inst h ι)))
        (try_consume_chunk_precise h c).
    Proof.
      destruct c; [| |constructor|constructor];
        cbn [try_consume_chunk_precise].
      - destruct (𝑯_precise p) as [[ΔI ΔO prec]|]; [|constructor].
        remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
        destruct (env.catView ts') as [tsI tsO].
        generalize (find_chunk_user_precise_spec prec tsI tsO h).
        apply option.wlp_monotonic. intros [h' eqs].
        intros HIn ι Heqs. specialize (HIn ι Heqs).
        now rewrite Heqts', rew_opp_l in HIn.
      - apply find_chunk_ptsreg_precise_spec.
    Qed.

  End Consume.

  Section Interpretation.
    Import iris.bi.interface.

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
      List.fold_right (fun c h => interpret_scchunk c ∗ h)%I emp%I.
    #[global] Arguments interpret_scheap !h.

    Lemma interpret_scchunk_inst {Σ} (c : Chunk Σ) (ι : Valuation Σ) :
      interpret_scchunk (inst c ι) = interpret_chunk c ι.
    Proof.
      induction c; cbn [interpret_chunk];
        try rewrite <- IHc1, <- IHc2; reflexivity.
    Qed.

  End Interpretation.

End ChunksOn.
