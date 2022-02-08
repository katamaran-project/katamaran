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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Relations.Relation_Definitions
     Lists.List
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Coq Require
     Classes.CRelationClasses.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Symbolic.Propositions
     Symbolic.Worlds
     Syntax.ContractDecl
     Specification
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Set Implicit Arguments.

Module Type MutatorsOn
  (Import B : Base)
  (Import SPEC : Specification B)
  (Import SOLV : SolverKit B SPEC).

  Import Entailment.
  Import ModalNotations.
  Local Open Scope modal.

  Section DebugInfo.

    Record DebugCall (Σ : LCtx) : Type :=
      MkDebugCall
        { debug_call_function_parameters    : PCtx;
          debug_call_function_result_type   : Ty;
          debug_call_function_name          : 𝑭 debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_contract      : SepContract debug_call_function_parameters debug_call_function_result_type;
          debug_call_function_arguments     : SStore debug_call_function_parameters Σ;
          debug_call_program_context        : PCtx;
          debug_call_pathcondition          : PathCondition Σ;
          debug_call_localstore             : SStore debug_call_program_context Σ;
          debug_call_heap                   : SHeap Σ;
        }.

    Record DebugStm (Σ : LCtx) : Type :=
      MkDebugStm
        { debug_stm_program_context        : PCtx;
          debug_stm_statement_type         : Ty;
          debug_stm_statement              : Stm debug_stm_program_context debug_stm_statement_type;
          debug_stm_pathcondition          : PathCondition Σ;
          debug_stm_localstore             : SStore debug_stm_program_context Σ;
          debug_stm_heap                   : SHeap Σ;
        }.

    Record DebugAsn (Σ : LCtx) : Type :=
      MkDebugAsn
        { debug_asn_program_context        : PCtx;
          debug_asn_pathcondition          : PathCondition Σ;
          debug_asn_localstore             : SStore debug_asn_program_context Σ;
          debug_asn_heap                   : SHeap Σ;
        }.

    Record DebugConsumeChunk (Σ : LCtx) : Type :=
      MkDebugConsumeChunk
        { debug_consume_chunk_program_context        : PCtx;
          debug_consume_chunk_pathcondition          : PathCondition Σ;
          debug_consume_chunk_localstore             : SStore debug_consume_chunk_program_context Σ;
          debug_consume_chunk_heap                   : SHeap Σ;
          debug_consume_chunk_chunk                  : Chunk Σ;
        }.

    Global Instance SubstDebugCall : Subst DebugCall :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugCall f c ts pc δ h =>
          MkDebugCall f c (subst ts ζ01) (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Import option.notations.
    Global Instance OccursCheckDebugCall : OccursCheck DebugCall :=
      fun Σ x xIn d =>
        match d with
        | MkDebugCall f c ts pc δ h =>
            ts' <- occurs_check xIn ts ;;
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugCall f c ts' pc' δ' h')
        end.

    Global Instance SubstDebugStm : Subst DebugStm :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugStm s pc δ h =>
          MkDebugStm s (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance OccursCheckDebugStm : OccursCheck DebugStm :=
      fun Σ x xIn d =>
        match d with
        | MkDebugStm s pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugStm s pc' δ' h')
        end.

    Global Instance SubstDebugAsn : Subst DebugAsn :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugAsn pc δ h =>
          MkDebugAsn (subst pc ζ01) (subst δ ζ01) (subst h ζ01)
        end.

    Global Instance OccursCheckDebugAsn : OccursCheck DebugAsn :=
      fun Σ x xIn d =>
        match d with
        | MkDebugAsn pc δ h =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugAsn pc' δ' h')
        end.

    Global Instance SubstDebugConsumeChunk : Subst DebugConsumeChunk :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugConsumeChunk pc δ h c =>
          MkDebugConsumeChunk (subst pc ζ01) (subst δ ζ01) (subst h ζ01) (subst c ζ01)
        end.

    Global Instance OccursCheckDebugConsumeChunk : OccursCheck DebugConsumeChunk :=
      fun Σ x xIn d =>
        match d with
        | MkDebugConsumeChunk pc δ h c =>
            pc' <- occurs_check xIn pc ;;
            δ'  <- occurs_check xIn δ ;;
            h'  <- occurs_check xIn h ;;
            c'  <- occurs_check xIn c ;;
            Some (MkDebugConsumeChunk pc' δ' h'  c')
        end.

  End DebugInfo.

  Module WorldInstance.

    Record WInstance (w : World) : Set :=
      MkWInstance
        { ιassign :> Valuation w;
          ιvalid  : instpc (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : inst (A := Prop) fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof.
      intros. cbn.
      apply inst_pathcondition_cons. split; auto.
      apply ιvalid.
    Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : 𝑺 ∷ Ty} (v : Val (type b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env.snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite inst_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    (* Fixpoint winstance_cat {Σ} (ι : WInstance Σ) {Δ} (ιΔ : Valuation Δ) : *)
    (*   WInstance (wcat Σ Δ). *)
    (* Proof. *)
    (*   destruct ιΔ; cbn. *)
    (*   - apply ι. *)
    (*   - apply winstance_snoc. *)
    (*     apply winstance_cat. *)
    (*     apply ι. *)
    (*     apply ιΔ. *)
    (*     apply db. *)
    (* Defined. *)

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x∷σ ∈ w}
      (t : Term (w - x∷σ) σ) (p : inst t (env.remove (x∷σ) (ιassign ι) xIn) = env.lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env.remove _ (ιassign ι) xIn) _.
    Next Obligation.
      intros * p. cbn. rewrite inst_subst, <- inst_sub_shift in *.
      rewrite inst_sub_single_shift; auto using ιvalid.
    Qed.

    Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) : WInstance w1 -> WInstance w0 :=
      match ω01 in (_ ⊒ w) return (WInstance w -> WInstance w0) with
      | acc_refl            => fun ι => ι
      | @acc_sub _ w1 ζ ent => fun ι1 => {| ιassign := inst ζ ι1; |}
      end.
    Next Obligation.
    Proof.
      intros. specialize (ent ι1).
      rewrite <- inst_subst.
      apply ent.
      apply ιvalid.
    Qed.

  End WorldInstance.

  Definition PROP : TYPE :=
    fun _ => Prop.

  Import SymProp.
  Import Postprocessing.

  Section VerificationConditions.

    Inductive VerificationCondition (p : 𝕊 ctx.nil) : Prop :=
    | vc (P : safe p env.nil).

    Global Instance proper_vc : Proper (sequiv ctx.nil ==> iff) VerificationCondition.
    Proof. intros p q pq. split; intros []; constructor; now apply pq. Qed.

  End VerificationConditions.

  Definition SDijkstra (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> 𝕊.

  Module SDijk.

    Definition pure {A : TYPE} :
      ⊢ A -> SDijkstra A :=
      fun w0 a POST => T POST a.

    Definition map {A B} :
      ⊢ □(A -> B) -> SDijkstra A -> SDijkstra B :=
      fun w0 f m POST => m (comp <$> POST <*> f).

    Definition bind {A B} :
      ⊢ SDijkstra A -> □(A -> SDijkstra B) -> SDijkstra B :=
      fun w0 m f POST => m (fun w1 ω01 a1 => f w1 ω01 a1 (four POST ω01)).

    Definition angelic (x : option 𝑺) σ :
      ⊢ SDijkstra (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments angelic x σ [w] k.

    Definition angelic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SDijkstra (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
        | []      => fun k => T k env.nil
        | Δ ▻ x∷σ =>
          fun k =>
            angelic (Some (n x)) σ (fun w1 ω01 t =>
              rec Δ (fun w2 ω12 EΔ =>
                k w2 (acc_trans ω01 ω12) (EΔ ► (x∷σ ↦ persist__term t ω12))))
        end%ctx.
    Global Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic (x : option 𝑺) σ :
      ⊢ SDijkstra (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        demonicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ ctx.in_zero)).
    Global Arguments demonic x σ [w] k.

    Definition demonic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SDijkstra (fun w => NamedEnv (Term w) Δ) :=
      fix demonic_ctx {w} Δ {struct Δ} :=
        match Δ with
        | []      => fun k => T k env.nil
        | Δ ▻ x∷σ =>
          fun k =>
            demonic (Some (n x)) σ (fun w1 ω01 t =>
              demonic_ctx Δ (fun w2 ω12 EΔ =>
                k w2 (acc_trans ω01 ω12) (EΔ ► (x∷σ ↦ persist__term t ω12))))
        end%ctx.
    Global Arguments demonic_ctx {_} n [w] Δ : rename.

    Definition assume_formulas :
      ⊢ List Formula -> SDijkstra Unit :=
      fun w0 fmls0 POST =>
        match solver fmls0 with
        | Some (existT w1 (ν , fmls1)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_triangular ν
            (assume_formulas_without_solver fmls1
               (* Run POST in the world with the variable and residual
                  formulas included. This is a critical piece of code since
                  this is the place where we really meaningfully change the
                  world. We changed the type of assume_formulas_without_solver
                  just to not forget adding the formulas to the path constraints.
               *)
               (four POST (acc_triangular ν) (acc_formulas_right w1 fmls1) tt))
        | None =>
          (* The formulas are inconsistent with the path constraints. *)
          block
        end.

    Definition assume_formula :
      ⊢ Formula -> SDijkstra Unit :=
      fun w0 fml0 =>
        assume_formulas (cons fml0 nil).

    Definition assert_formulas :
      ⊢ Message -> List Formula -> SDijkstra Unit :=
      fun w0 msg fmls0 POST =>
        match solver fmls0 with
        | Some (existT w1 (ν , fmls1)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_triangular msg ν
            (fun msg' =>
               assert_formulas_without_solver msg' fmls1
                 (* Critical code. Like for assume_formulas. *)
                 (four POST (acc_triangular ν) (acc_formulas_right w1 fmls1) tt))
        | None =>
          (* The formulas are inconsistent with the path constraints. *)
          error (EMsgHere msg)
        end.

    Definition assert_formula :
      ⊢ Message -> Formula -> SDijkstra Unit :=
      fun w0 msg fml0 =>
        assert_formulas msg (cons fml0 nil).

    Definition angelic_binary {A} :
      ⊢ SDijkstra A -> SDijkstra A -> SDijkstra A :=
      fun w m1 m2 POST =>
        angelic_binary (m1 POST) (m2 POST).
    Definition demonic_binary {A} :
      ⊢ SDijkstra A -> SDijkstra A -> SDijkstra A :=
      fun w m1 m2 POST =>
        demonic_binary (m1 POST) (m2 POST).

    Definition angelic_list {M} {subM : Subst M} {occM : OccursCheck M} {A} :
      ⊢ M -> List A -> SDijkstra A :=
      fun w msg =>
        fix rec xs :=
        match xs with
        | nil        => fun POST => error (EMsgHere msg)
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition demonic_list {A} :
      ⊢ List A -> SDijkstra A :=
      fun w =>
        fix rec xs :=
        match xs with
        | nil        => fun POST => block
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition angelic_finite F `{finite.Finite F} :
      ⊢ Message -> SDijkstra ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SDijkstra ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).

    Definition angelic_match_bool' :
      ⊢ Message -> STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun _ msg t =>
        angelic_binary
          (fun POST => assert_formula msg (formula_bool t) (fun w1 ω01 _ => POST w1 ω01 true))
          (fun POST => assert_formula msg (formula_bool (term_not t)) (fun w1 ω01 _ => POST w1 ω01 false)).

    Definition angelic_match_bool :
      ⊢ Message -> STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun w msg t =>
        let t' := peval t in
        match term_get_val t' with
        | Some l => pure  l
        | None   => angelic_match_bool' msg t'
        end.

    Definition demonic_match_bool' :
      ⊢ STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun _ t =>
        demonic_binary
          (fun POST => assume_formula (formula_bool t) (fun w1 ω01 _ => POST w1 ω01 true))
          (fun POST => assume_formula (formula_bool (term_not t)) (fun w1 ω01 _ => POST w1 ω01 false)).

    Definition demonic_match_bool :
      ⊢ STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun w t =>
        let t' := peval t in
        match term_get_val t' with
        | Some l => pure  l
        | None   => demonic_match_bool' t'
        end.


    (* Definition angelic_match_enum {AT E} : *)
    (*   ⊢ Message -> STerm (ty_enum E) -> (⌜Val (ty_enum E)⌝ -> □(𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w msg t k => *)
    (*     match term_get_val t with *)
    (*     | Some v => T (k v) *)
    (*     | None => angelic_finite *)
    (*                 msg (fun v => assert_formulak msg (formula_eq t (term_enum E v)) (k v)) *)
    (*     end. *)

    (* Definition demonic_match_enum {AT E} : *)
    (*   ⊢ STerm (ty_enum E) -> (⌜Val (ty_enum E)⌝ -> □(𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w t k => *)
    (*     match term_get_val t with *)
    (*     | Some v => T (k v) *)
    (*     | None => demonic_finite *)
    (*                 (fun v => assume_formulak (formula_eq t (term_enum E v)) (k v)) *)
    (*     end. *)

    (* Definition angelic_match_list {AT} (x y : 𝑺) (σ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_list σ) -> □(𝕊 AT) -> □(STerm σ -> STerm (ty_list σ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 msg t knil kcons => *)
    (*     angelic_binary (assert_formulak msg (formula_eq (term_val (ty_list σ) []) t) knil) *)
    (*       (angelic x σ *)
    (*          (fun w1 ω01 (th : Term w1 σ) => *)
    (*           angelic y (ty_list σ) *)
    (*             (fun w2 ω12 (tt : Term w2 (ty_list σ)) => *)
    (*              assert_formulak (subst msg (wtrans ω01 ω12)) *)
    (*                (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12))) *)
    (*                (fun w3 ω23 => *)
    (*                 four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))). *)

    (* Definition demonic_match_list {AT} (x y : 𝑺) (σ : Ty) : *)
    (*   ⊢ STerm (ty_list σ) -> □(𝕊 AT) -> □(STerm σ -> STerm (ty_list σ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 t knil kcons => *)
    (*     demonic_binary (assume_formulak (formula_eq (term_val (ty_list σ) []) t) knil) *)
    (*       (demonic x σ *)
    (*          (fun w1 ω01 (th : Term w1 σ) => *)
    (*           demonic y (ty_list σ) *)
    (*             (fun w2 ω12 (tt : Term w2 (ty_list σ)) => *)
    (*              assume_formulak *)
    (*                (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12))) *)
    (*                (fun w3 ω23 => *)
    (*                 four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))). *)

    Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 msg t kinl kinr.
      apply angelic_binary.
      - eapply bind.
        apply (angelic (Some x) σ).
        intros w1 ω01 t1.
        eapply bind.
        apply assert_formula. apply (persist (A := Message) msg ω01).
        apply (formula_eq (term_inl t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinl ω01). auto.
        apply (persist__term t1 ω12).
      - eapply bind.
        apply (angelic (Some y) τ).
        intros w1 ω01 t1.
        eapply bind.
        apply assert_formula. apply (persist (A := Message) msg ω01).
        apply (formula_eq (term_inr t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinr ω01). auto.
        apply (persist__term t1 ω12).
    Defined.

    (* Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A. *)
    (* Proof. *)
    (*   intros w0. *)
    (*   fun w0 msg t kinl kinr => *)
    (*     match term_get_sum t with *)
    (*     | Some (inl tσ) => T kinl tσ *)
    (*     | Some (inr tτ) => T kinr tτ *)
    (*     | None => angelic_match_sum' x y msg t kinl kinr *)
    (*     end. *)

    Definition demonic_match_sum' {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 t kinl kinr.
      apply demonic_binary.
      - eapply bind.
        apply (demonic (Some x) σ).
        intros w1 ω01 t1.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_inl t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinl ω01). auto.
        apply (persist__term t1 ω12).
      - eapply bind.
        apply (demonic (Some y) τ).
        intros w1 ω01 t1.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_inr t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinr ω01). auto.
        apply (persist__term t1 ω12).
    Defined.

    Definition demonic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A :=
      fun w0 t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => demonic_match_sum' x y t kinl kinr
        end.

    Definition angelic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 msg t k.
      eapply bind.
      apply (angelic (Some x) σ).
      intros w1 ω01 t1.
      eapply bind.
      apply (angelic (Some y) τ).
      intros w2 ω12 t2.
      eapply bind.
      apply assert_formula. apply (persist (A := Message) msg (acc_trans ω01 ω12)).
      refine (formula_eq _ (persist__term t (acc_trans ω01 ω12))).
      eapply (term_binop binop_pair).
      apply (persist__term t1 ω12).
      apply t2.
      intros w3 ω23 _.
      apply (four k (acc_trans ω01 ω12)).
      auto.
      apply (persist__term t1 (acc_trans ω12 ω23)).
      apply (persist__term t2 ω23).
    Defined.

    (* Definition angelic_match_prod {AT} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     match term_get_pair t with *)
    (*     | Some (tσ,tτ) => T k tσ tτ *)
    (*     | None => angelic_match_prod' x y msg t k *)
    (*     end. *)

    Definition demonic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 t k.
      eapply bind.
      apply (demonic (Some x) σ).
      intros w1 ω01 t1.
      eapply bind.
      apply (demonic (Some y) τ).
      intros w2 ω12 t2.
      eapply bind.
      apply assume_formula.
      refine (formula_eq _ (persist__term t (acc_trans ω01 ω12))).
      eapply (term_binop binop_pair).
      apply (persist__term t1 ω12).
      apply t2.
      intros w3 ω23 _.
      apply (four k (acc_trans ω01 ω12)).
      auto.
      apply (persist__term t1 (acc_trans ω12 ω23)).
      apply (persist__term t2 ω23).
    Defined.

    (* Definition demonic_match_prod {AT} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     match term_get_pair t with *)
    (*     | Some (tσ,tτ) => T k tσ tτ *)
    (*     | None => demonic_match_prod' x y t k *)
    (*     end. *)

    (* Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   apply (angelic_freshen_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assert_formulak. *)
    (*   apply (subst msg ω01). *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_record R (record_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   destruct (term_get_record t). *)
    (*   - apply (T k). *)
    (*     apply (record_pattern_match_env p n0). *)
    (*   - apply (angelic_match_record' n p msg t k). *)
    (* Defined. *)

    (* Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   apply (demonic_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assume_formulak. *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_record R (record_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   destruct (term_get_record t). *)
    (*   - apply (T k). *)
    (*     apply (record_pattern_match_env p n0). *)
    (*   - apply (demonic_match_record' n p t k). *)
    (* Defined. *)

    (* Definition angelic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   apply (angelic_freshen_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assert_formulak. *)
    (*   apply (subst msg ω01). *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_tuple (tuple_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   destruct (term_get_tuple t). *)
    (*   - apply (T k). *)
    (*     apply (tuple_pattern_match_env p e). *)
    (*   - apply (angelic_match_tuple' n p msg t k). *)
    (* Defined. *)

    (* Definition demonic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   apply (demonic_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assume_formulak. *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_tuple (tuple_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   destruct (term_get_tuple t). *)
    (*   - apply (T k). *)
    (*     apply (tuple_pattern_match_env p e). *)
    (*   - apply (demonic_match_tuple' n p t k). *)
    (* Defined. *)

    (* (* TODO: move to Syntax *) *)
    (* Definition pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   NamedEnv (Term Σ) Δ -> Term Σ σ := *)
    (*   match p with *)
    (*   | pat_var x    => fun Ex => match snocView Ex with isSnoc _ t => t end *)
    (*   | pat_unit     => fun _ => term_val ty_unit tt *)
    (*   | pat_pair x y => fun Exy => match snocView Exy with *)
    (*                                  isSnoc Ex ty => *)
    (*                                  match snocView Ex with *)
    (*                                    isSnoc _ tx => term_binop binop_pair tx ty *)
    (*                                  end *)
    (*                                end *)
    (*   | pat_tuple p  => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ) *)
    (*   | pat_record p => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ) *)
    (*   end. *)

    (* Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   ⊢ Message -> STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     angelic_freshen_ctx n Δ *)
    (*       (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) => *)
    (*        assert_formulak (subst msg ω01) (formula_eq (subst t ω01) (pattern_match_env_reverse p ts)) *)
    (*          (fun w2 ω12 => k w2 (acc_trans ω01 ω12) (subst ts ω12))). *)

    (* Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   ⊢ STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     demonic_ctx n Δ *)
    (*       (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) => *)
    (*        assume_formulak (formula_eq (subst t ω01) (pattern_match_env_reverse p ts)) *)
    (*          (fun w2 ω12 => k w2 (acc_trans ω01 ω12) (subst ts ω12))). *)

    (* Definition angelic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     angelic_finite msg *)
    (*       (fun K : 𝑼𝑲 U => *)
    (*        angelic None (𝑼𝑲_Ty K) *)
    (*          (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) => *)
    (*           assert_formulak (subst msg ω01) (formula_eq (term_union U K t__field) (subst t ω01)) *)
    (*             (fun w2 ω12 => *)
    (*              let ω02 := wtrans ω01 ω12 in *)
    (*              angelic_match_pattern n (p K) (subst msg ω02) (subst t__field ω12) (four (k K) ω02)))). *)

    (* Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     match term_get_union t with *)
    (*     | Some (existT K t__field) => angelic_match_pattern n (p K) msg t__field (k K) *)
    (*     | None => angelic_match_union' n p msg t k *)
    (*     end. *)

    (* Definition demonic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     demonic_finite *)
    (*       (fun K : 𝑼𝑲 U => *)
    (*        demonic None (𝑼𝑲_Ty K) *)
    (*          (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) => *)
    (*           assume_formulak (formula_eq (term_union U K t__field) (subst t ω01)) *)
    (*             (fun w2 ω12 => *)
    (*              demonic_match_pattern n (p K) (subst t__field ω12) (four (k K) (acc_trans ω01 ω12))))). *)

    (* Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     match term_get_union t with *)
    (*     | Some (existT K t__field) => demonic_match_pattern n (p K) t__field (k K) *)
    (*     | None => demonic_match_union' n p t k *)
    (*     end. *)

    Global Instance proper_debug {B Σ b} : Proper (iff ==> iff) (@Debug B Σ b).
    Proof.
      intros P Q PQ.
      split; intros []; constructor; intuition.
    Qed.

    (* Ltac wsimpl := *)
    (*   repeat *)
    (*     (try change (wctx (wsnoc ?w ?b)) with (ctx_snoc (wctx w) b); *)
    (*      try change (sub_acc (@wred_sup ?w ?b ?t)) with (sub_snoc (sub_id (wctx w)) b t); *)
    (*      try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b))); *)
    (*      try change (sub_acc (@wrefl ?w)) with (sub_id (wctx w)); *)
    (*      try change (sub_acc (@wsnoc_sup ?w ?b)) with (@sub_wk1 (wctx w) b); *)
    (*      try change (wctx (wformula ?w ?fml)) with (wctx w); *)
    (*      try change (sub_acc (acc_trans ?ω1 ?ω2)) with (subst (sub_acc ω1) (sub_acc ω2)); *)
    (*      try change (sub_acc (@wformula_sup ?w ?fml)) with (sub_id (wctx w)); *)
    (*      try change (wco (wformula ?w ?fml)) with (cons fml (wco w)); *)
    (*      try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t)); *)
    (*      try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx_remove xIn); *)
    (*      try change (sub_acc (@acc_subst_right ?w _ _ ?xIn ?t)) with (sub_single xIn t); *)
    (*      rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id, *)
    (*        ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc, *)
    (*        ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons; *)
    (*      repeat *)
    (*        match goal with *)
    (*        | |- Debug _ _ <-> Debug _ _ => apply proper_debug *)
    (*        | |- (?A /\ ?B) <-> (?A /\ ?C) => apply and_iff_compat_l'; intro *)
    (*        | |- (?A -> ?B) <-> (?A -> ?C) => apply imp_iff_compat_l'; intro *)
    (*        | |- (exists x : ?X, _) <-> (exists y : ?X, _) => apply base.exist_proper; intro *)
    (*        | |- (forall x : ?X, _) <-> (forall y : ?X, _) => apply base.forall_proper; intro *)
    (*        | |- wp ?m _ ?ι -> wp ?m _ ?ι => apply wp_monotonic; intro *)
    (*        | |- wp ?m _ ?ι <-> wp ?m _ ?ι => apply wp_equiv; intro *)
    (*        | |- ?w ⊒ ?w => apply wrefl *)
    (*        | |- ?POST (@inst _ _ _ ?Σ1 ?x1 ?ι1) <-> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) => *)
    (*          assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto *)
    (*        | |- ?POST (?inst _ _ _ ?Σ1 ?x1 ?ι1) -> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) => *)
    (*          assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w ?ω _) _ = inst (?f ?w ?ω _) _ => *)
    (*          apply (Hdcl w ω w ω wrefl) *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w0 wrefl _) _ = inst (?f ?w1 ?ω01 _) _ => *)
    (*          apply (Hdcl w0 wrefl w1 ω01 ω01) *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w1 ?ω01 _) _ = inst (?f ?w0 wrefl _) _ => *)
    (*          symmetry; apply (Hdcl w0 wrefl w1 ω01 ω01) *)
    (*        | Hdcl : arrow_dcl ?f |- *)
    (*          wp (?f ?w ?ω _) _ _ -> wp (?f ?w ?ω _) _ _  => *)
    (*          apply (Hdcl w ω w ω wrefl) *)
    (*        end). *)

  End SDijk.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Definition SMut (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
    □(A -> SStore Γ2 -> SHeap -> 𝕊) -> SStore Γ1 -> SHeap -> 𝕊.
  Bind Scope mut_scope with SMut.

  Module SMut.

    Section Basic.

      Definition dijkstra {Γ} {A : TYPE} :
        ⊢ SDijkstra A -> SMut Γ Γ A.
      Proof.
        intros w0 m POST δ0 h0.
        apply m.
        intros w1 ω01 a1.
        apply POST; auto.
        apply (persist (A := SStore Γ) δ0 ω01).
        apply (persist (A := SHeap) h0 ω01).
      Defined.

      Definition pure {Γ} {A : TYPE} :
        ⊢ A -> SMut Γ Γ A.
      Proof.
        intros w0 a k.
        apply k; auto. apply acc_refl.
      Defined.

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SMut Γ1 Γ2 A -> □(A -> SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B.
      Proof.
        intros w0 ma f k.
        unfold SMut, Impl, Box in *.
        apply ma; auto.
        intros w1 ω01 a1.
        apply f; auto.
        apply (four k ω01).
      Defined.

      Definition bind_box {Γ1 Γ2 Γ3 A B} :
        ⊢ □(SMut Γ1 Γ2 A) -> □(A -> SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 B) :=
        fun w0 m f => bind <$> m <*> four f.

      (* Definition strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : SMut Γ1 Γ2 A Σ) (b : B Σ) : *)
      (*   SMut Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ := *)
      (*   bind ma (fun _ ζ a => pure (a, subst b ζ)). *)

      Definition bind_right {Γ1 Γ2 Γ3 A B} :
        ⊢ SMut Γ1 Γ2 A -> □(SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B.
      Proof.
        intros w0 m k POST.
        apply m.
        intros w1 ω01 a1.
        apply k. auto.
        intros w2 ω12 b2.
        apply (four POST ω01); auto.
      Defined.

      (* Definition bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} : *)
      (*   ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 A). *)
      (* Proof. *)
      (*   intros w0 ma mb. *)
      (*   apply (bbind ma). *)
      (*   intros w1 ω01 a1 δ1 h1. *)
      (*   apply (bind (mb w1 ω01 δ1 h1)). *)
      (*   intros w2 ω12 [_ δ2 h2]. *)
      (*   apply (pure). *)
      (*   apply (subst a1 ω12). *)
      (*   auto. *)
      (*   auto. *)
      (* Defined. *)

      (* Definition map {Γ1 Γ2 A B} `{Subst A, Subst B} : *)
      (*   ⊢ □(SMut Γ1 Γ2 A) -> □(A -> B) -> □(SMut Γ1 Γ2 B) := *)
      (*   fun w0 ma f Σ1 ζ01 pc1 δ1 h1 => *)
      (*     map pc1 *)
      (*       (fun Σ2 ζ12 pc2 '(MkSMutResult a2 δ2 h2) => *)
      (*          MkSMutResult (f Σ2 (subst ζ01 ζ12) pc2 a2) δ2 h2) *)
      (*        (ma Σ1 ζ01 pc1 δ1 h1). *)

      Definition error {Γ1 Γ2 A D} (func : string) (msg : string) (data:D) :
        ⊢ SMut Γ1 Γ2 A :=
        fun w _ δ h =>
          error
            (EMsgHere
               {| msg_function := func;
                  msg_message := msg;
                  msg_program_context := Γ1;
                  msg_localstore := δ;
                  msg_heap := h;
                  msg_pathcondition := wco w
               |}).
      Global Arguments error {_ _ _ _} func msg data {w} _ _.

      Definition block {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A.
      Proof.
        intros w0 POST δ h.
        apply block.
      Defined.

      Definition angelic_binary {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          angelic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).
      Definition demonic_binary {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          demonic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).

      Definition angelic_list {M} {subM : Subst M} {occM : OccursCheck M} {A Γ} :
        ⊢ (SStore Γ -> SHeap -> M) -> List A -> SMut Γ Γ A :=
        fun w msg xs POST δ h => dijkstra (SDijk.angelic_list (msg δ h) xs) POST δ h.

      Definition angelic_finite {Γ} F `{finite.Finite F} :
        ⊢ (SStore Γ -> SHeap -> Message) -> SMut Γ Γ ⌜F⌝ :=
        fun w msg POST δ h => dijkstra (SDijk.angelic_finite (msg δ h)) POST δ h.

      Definition demonic_finite {Γ} F `{finite.Finite F} :
        ⊢ SMut Γ Γ ⌜F⌝ :=
        fun w => dijkstra (SDijk.demonic_finite (w:=w)).
      Global Arguments demonic_finite {Γ} [_] {_ _} {w}.

      Definition angelic {Γ} (x : option 𝑺) σ :
        ⊢ SMut Γ Γ (STerm σ) :=
        fun w => dijkstra (SDijk.angelic x σ (w:=w)).
      Global Arguments angelic {Γ} x σ {w}.

      Definition demonic {Γ} (x : option 𝑺) σ :
        ⊢ SMut Γ Γ (STerm σ) :=
        fun w => dijkstra (SDijk.demonic x σ (w:=w)).
      Global Arguments demonic {Γ} x σ {w}.

      Definition debug {AT DT} `{Subst DT, OccursCheck DT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> DT) -> (SMut Γ1 Γ2 AT) -> (SMut Γ1 Γ2 AT).
      Proof.
        intros w0 d m POST δ h.
        eapply debug. eauto.
        eauto. eauto.
        apply d. auto. auto.
        apply m; auto.
      Defined.

      Definition angelic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 Δ. apply dijkstra.
        apply (SDijk.angelic_ctx n Δ).
      Defined.
      Global Arguments angelic_ctx {N} n {Γ} [w] Δ : rename.

      Definition demonic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 Δ. apply dijkstra.
        apply (SDijk.demonic_ctx n Δ).
      Defined.
      Global Arguments demonic_ctx {N} n {Γ} [w] Δ : rename.

    End Basic.

    Module SMutNotations.

      (* Notation "'⨂' x .. y => F" := *)
      (*   (smut_demonic (fun x => .. (smut_demonic (fun y => F)) .. )) : mut_scope. *)

      (* Notation "'⨁' x .. y => F" := *)
      (*   (smut_angelic (fun x => .. (smut_angelic (fun y => F)) .. )) : mut_scope. *)

      (* Infix "⊗" := smut_demonic_binary (at level 40, left associativity) : mut_scope. *)
      (* Infix "⊕" := smut_angelic_binary (at level 50, left associativity) : mut_scope. *)

      Notation "x <- ma ;; mb" := (bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
      Notation "ma >>= f" := (bind ma f) (at level 50, left associativity, only parsing) : mut_scope.
      Notation "ma >> mb" := (bind_right ma mb) (at level 50, left associativity, only parsing) : mut_scope.
      (* Notation "m1 ;; m2" := (smut_bind_right m1 m2) : mut_scope. *)

      Notation "⟨ ω ⟩ x <- ma ;; mb" :=
        (bind ma (fun _ ω x => mb))
          (at level 80, x at next level,
            ma at next level, mb at level 200,
            right associativity) : mut_scope.

    End SMutNotations.
    Import SMutNotations.
    Local Open Scope mut_scope.

    Section AssumeAssert.

      (* Add the provided formula to the path condition. *)
      Definition assume_formula {Γ} :
        ⊢ Formula -> SMut Γ Γ Unit.
      Proof.
        intros w0 fml. apply dijkstra.
        apply (SDijk.assume_formula fml).
      Defined.

      Definition box_assume_formula {Γ} :
        ⊢ Formula -> □(SMut Γ Γ Unit) :=
        fun w0 fml => assume_formula <$> persist fml.

      Definition assert_formula {Γ} :
        ⊢ Formula -> SMut Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          dijkstra
            (SDijk.assert_formula
               {| msg_function := "smut_assert_formula";
                  msg_message := "Proof obligation";
                  msg_program_context := Γ;
                  msg_localstore := δ0;
                  msg_heap := h0;
                  msg_pathcondition := wco w0
               |} fml)
            POST δ0 h0.

      Definition box_assert_formula {Γ} :
        ⊢ Formula -> □(SMut Γ Γ Unit) :=
        fun w0 fml => assert_formula <$> persist fml.

      Definition assert_formulas {Γ} :
        ⊢ List Formula -> SMut Γ Γ Unit.
      Proof.
        intros w0 fmls POST δ0 h0.
        eapply dijkstra.
        apply SDijk.assert_formulas.
        apply
          {| msg_function := "smut_assert_formula";
             msg_message := "Proof obligation";
             msg_program_context := Γ;
             msg_localstore := δ0;
             msg_heap := h0;
             msg_pathcondition := wco w0
          |}.
        apply fmls.
        apply POST.
        apply δ0.
        apply h0.
      Defined.

    End AssumeAssert.

    Section PatternMatching.

      (* Definition angelic_match_bool {Γ} : *)
      (*   ⊢ STerm ty_bool -> SMut Γ Γ ⌜bool⌝ := *)
      (*   fun w t POST δ h => *)
      (*     dijkstra *)
      (*       (SDijk.angelic_match_bool *)
      (*          {| msg_function := "SMut.angelic_match_bool"; *)
      (*             msg_message := "pattern match assertion"; *)
      (*             msg_program_context := Γ; *)
      (*             msg_localstore := δ; *)
      (*             msg_heap := h; *)
      (*             msg_pathcondition := wco w *)
      (*          |} t) *)
      (*       POST δ h. *)

      (* Definition demonic_match_bool {Γ} : *)
      (*   ⊢ STerm ty_bool -> SMut Γ Γ ⌜bool⌝ := *)
      (*   fun w t => dijkstra (SDijk.demonic_match_bool t). *)

      Definition angelic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kt kf.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "smut_angelic_match_bool"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_bool t).
          apply kt.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "smut_angelic_match_bool"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_bool (term_not t)).
          apply kf.
      Defined.

      Definition angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_val t with
          | Some true => T kt
          | Some false => T kf
          | None => angelic_match_bool' t kt kf
          end.

      Definition box_angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          angelic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition demonic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kt kf.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_bool t).
          apply kt.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_bool (term_not t)).
          apply kf.
      Defined.

      Definition demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_val t with
          | Some true => T kt
          | Some false => T kf
          | None => demonic_match_bool' t kt kf
          end.

      Definition box_demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          demonic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition angelic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := 𝑬𝑲 E)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_enum";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 EK.
        eapply bind_right.
        apply (assert_formula (formula_eq (persist__term t ω01) (term_enum E EK))).
        apply (four (cont EK)). auto.
      Defined.

      Definition demonic_match_enum {A E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 A)) -> SMut Γ1 Γ2 A.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := 𝑬𝑲 E)).
        intros w1 ω01 EK.
        eapply bind_right.
        apply (assume_formula (formula_eq (persist__term t ω01) (term_enum E EK))).
        apply (four (cont EK)). auto.
      Defined.

      Definition box_demonic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k =>
          demonic_match_enum
            <$> persist__term t
            <*> (fun (w1 : World) (ω01 : w0 ⊒ w1) (EK : 𝑬𝑲 E) => four (k EK) ω01).

      Definition angelic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr.
        apply angelic_binary.
        - eapply bind.
          apply (angelic (Some x) σ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assert_formula.
          apply (formula_eq (term_inl t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinl ω01). auto.
          apply (persist__term t1 ω12).
        - eapply bind.
          apply (angelic (Some y) τ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assert_formula.
          apply (formula_eq (term_inr t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinr ω01). auto.
          apply (persist__term t1 ω12).
      Defined.

      Definition demonic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr.
        apply demonic_binary.
        - eapply bind.
          apply (demonic (Some x) σ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_inl t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinl ω01). auto.
          apply (persist__term t1 ω12).
        - eapply bind.
          apply (demonic (Some y) τ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_inr t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinr ω01). auto.
          apply (persist__term t1 ω12).
      Defined.

      Definition demonic_match_sum_lifted {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr POST δ0 h0.
        eapply (SDijk.demonic_match_sum (A := fun w => SStore Γ2 w * SHeap w * AT w)%type x _ y _ _ t).
        - intros w1 ω01 t' POSTl.
          apply kinl. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTl. auto. auto.
          apply (persist (A := SStore _) δ0 ω01).
          apply (persist (A := SHeap) h0 ω01).
        - intros w1 ω01 t' POSTr.
          apply kinr. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTr. auto. auto.
          apply (persist (A := SStore _) δ0 ω01).
          apply (persist (A := SHeap) h0 ω01).
        - intros w1 ω01 [ [δ1 h1] a1]. apply POST. auto. auto. auto. auto.
      Defined.

      Definition angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "SMut.angelic_match_list"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_eq (term_val (ty_list σ) []%list) t).
          intros w1 ω01.
          apply knil. auto.
        - eapply bind.
          apply (angelic (Some x) σ).
          intros w1 ω01 thead.
          eapply bind.
          apply (angelic (Some y) (ty_list σ)).
          intros w2 ω12 ttail.
          eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "SMut.angelic_match_list"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*      msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*      msg_pathcondition   := wco w2; *)
          (*   |}. *)
          apply (formula_eq (term_binop binop_cons (persist__term thead ω12) ttail) (persist__term t (acc_trans ω01 ω12))).
          intros w3 ω23.
          apply (four kcons (acc_trans ω01 ω12)). auto.
          apply (persist__term thead (acc_trans ω12 ω23)).
          apply (persist__term ttail ω23).
      Defined.

      Definition box_angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t knil kcons => angelic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_val (ty_list σ) []%list) t).
          intros w1 ω01.
          apply knil. auto.
        - eapply bind.
          apply (demonic (Some x) σ).
          intros w1 ω01 thead.
          eapply bind.
          apply (demonic (Some y) (ty_list σ)).
          intros w2 ω12 ttail.
          eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_binop binop_cons (persist__term thead ω12) ttail) (persist__term t (acc_trans ω01 ω12))).
          intros w3 ω23.
          apply (four kcons (acc_trans ω01 ω12)). auto.
          apply (persist__term thead (acc_trans ω12 ω23)).
          apply (persist__term ttail ω23).
      Defined.

      Definition box_demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t knil kcons => demonic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (angelic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (angelic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_prod"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_binop binop_pair (persist__term tσ ω12) tτ) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        apply (four k (acc_trans ω01 ω12)). auto.
        apply (persist__term tσ (acc_trans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition box_angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_prod x y <$> persist__term t <*> four k.

      Definition demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (demonic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (demonic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_binop binop_pair (persist__term tσ ω12) tτ) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        apply (four k (acc_trans ω01 ω12)). auto.
        apply (persist__term tσ (acc_trans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition box_demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_prod x y <$> persist__term t <*> four k.

      Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_record"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (angelic_match_record' n p t k).
      Defined.

      Definition box_angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_record n p <$> persist__term t <*> four k.

      Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (demonic_match_record' n p t k).
      Defined.

      Definition box_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_record n p <$> persist__term t <*> four k.

      Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_tuple"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
        (* |}. *)
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition box_angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_tuple n p <$> persist__term t <*> four k.

      Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition box_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_tuple n p <$> persist__term t <*> four k.

      Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ (SStore Γ -> SHeap -> Message) -> STerm σ -> SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 msg t.
        eapply (bind).
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply (bind_right).
        apply assert_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (persist__term t ω01)).
        intros w2 ω12.
        apply pure.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ STerm σ -> SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 t.
        eapply (bind).
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply (bind_right).
        apply assume_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (persist__term t ω01)).
        intros w2 ω12.
        apply pure.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := 𝑼𝑲 U)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 UK.
        eapply bind.
        apply (angelic None (𝑼𝑲_Ty UK)).
        intros w2 ω12 t__field.
        eapply bind_right.
        apply assert_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        eapply bind.
        apply (angelic_match_pattern n (p UK)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w3;
            |}.
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (acc_trans ω01 (acc_trans ω12 ω23)).
      Defined.

      Definition box_angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => angelic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

      Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := 𝑼𝑲 U)).
        intros w1 ω01 UK.
        eapply bind.
        apply (demonic None (𝑼𝑲_Ty UK)).
        intros w2 ω12 t__field.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        eapply bind.
        apply (demonic_match_pattern n (p UK)).
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (acc_trans ω01 (acc_trans ω12 ω23)).
      Defined.

      Definition box_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => demonic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

      Definition angelic_match_bvec' {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty_bvec n) -> (⌜bv n⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ b <- angelic_finite
                        (fun (δ : SStore Γ1 w0) (h : SHeap w0) =>
                           {| msg_function := "SMut.angelic_match_bvec";
                              msg_message := "pattern match assertion";
                              msg_program_context := Γ1;
                              msg_localstore := δ;
                              msg_heap := h;
                              msg_pathcondition := wco w0
                           |}) ;;
          let t1 := persist__term t ω1 in
          ⟨ ω2 ⟩ _ <- assert_formula (formula_eq t1 (term_val (ty_bvec n) b)) ;;
          four (k b) ω1 ω2.

      Definition angelic_match_bvec {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty_bvec n) -> (⌜bv n⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT :=
        fun w0 t k =>
          match term_get_val t with
          | Some b => T (k b)
          | None   => angelic_match_bvec' t k
          end.

      Definition demonic_match_bvec' {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty_bvec n) -> (⌜bv n⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT :=
        fun w0 t k =>
          ⟨ ω1 ⟩ b <- demonic_finite (F := bv n) ;;
          let s1 := term_val (ty_bvec n) b in
          let t1 := persist__term t ω1 in
          ⟨ ω2 ⟩ _ <- assume_formula (formula_eq s1 t1) ;;
          four (k b) ω1 ω2.

      Definition demonic_match_bvec {AT n} {Γ1 Γ2} :
        ⊢ STerm (ty_bvec n) -> (⌜bv n⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT :=
        fun w0 t k =>
          match term_get_val t with
          | Some b => T (k b)
          | None   => demonic_match_bvec' t k
          end.

    End PatternMatching.

    Section State.

      Definition pushpop {AT Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SMut (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) AT -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t m POST δ h.
        apply m.
        intros w1 ω01 a1 δ1 h1.
        apply POST. auto. auto. apply (env.tail δ1). apply h1.
        apply env.snoc.
        apply δ.
        apply t.
        apply h.
      Defined.

      Definition pushspops {AT Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 δΔ m POST δ h.
        apply m.
        intros w1 ω01 a1 δ1 h1.
        apply POST. auto. auto. apply (env.drop Δ δ1). apply h1.
        apply env.cat.
        apply δ.
        apply δΔ.
        apply h.
      Defined.

      Definition get_local {Γ} : ⊢ SMut Γ Γ (SStore Γ) :=
        fun w0 POST δ => T POST δ δ.
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SMut Γ1 Γ2 Unit :=
        fun w0 δ POST _ => T POST tt δ.
      Definition get_heap {Γ} : ⊢ SMut Γ Γ SHeap :=
        fun w0 POST δ h => T POST h δ h.
      Definition put_heap {Γ} : ⊢ SHeap -> SMut Γ Γ Unit :=
        fun w0 h POST δ _ => T POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SMut Γ Γ (STerm σ).
        intros w POST δ h.
        apply (T POST).
        apply peval.
        apply (seval_exp δ e).
        auto.
        auto.
      Defined.

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SMut Γ Γ (SStore σs).
        intros w POST δ h.
        apply (T POST).
        refine (env.map _ es).
        intros b e. apply peval. apply (seval_exp δ e).
        auto.
        auto.
      Defined.

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SMut Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn w} v.

    End State.

    Section ProduceConsume.
      Import EqNotations.

      Definition produce_chunk {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit :=
        fun w0 c k δ h => T k tt δ (cons (peval_chunk c) h).

      Fixpoint try_consume_chunk_exact {Σ} (h : SHeap Σ) (c : Chunk Σ) {struct h} : option (SHeap Σ) :=
        match h with
        | nil       => None
        | cons c' h =>
          if chunk_eqb c c'
          then Some (if is_duplicable c then (cons c h) else h)
          else option_map (cons c') (try_consume_chunk_exact h c)
        end.

      Equations(noeqns) match_chunk {Σ : LCtx} (c1 c2 : Chunk Σ) : List Formula Σ :=
        match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2)
        with eq_dec p1 p2 => {
          match_chunk (chunk_user p1 vs1) (chunk_user ?(p1) vs2) (left eq_refl) := formula_eqs_ctx vs1 vs2;
          match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2) (right _) :=
            cons (formula_bool (term_val ty_bool false)) nil
        };
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
        with eq_dec_het r1 r2 => {
          match_chunk (chunk_ptsreg r1 v1) (chunk_ptsreg ?(r1) v2) (left eq_refl) := cons (formula_eq v1 v2) nil;
          match_chunk (chunk_ptsreg r1 v1) (chunk_ptsreg r2 v2) (right _)      :=
            cons (formula_bool (term_val ty_bool false)) nil
        };
        match_chunk (chunk_conj c11 c12) (chunk_conj c21 c22) :=
          app (match_chunk c11 c21) (match_chunk c12 c22);
        match_chunk (chunk_wand c11 c12) (chunk_wand c21 c22) :=
          app (match_chunk c11 c21) (match_chunk c12 c22);
        match_chunk _ _  := cons (formula_bool (term_val ty_bool false)) nil.

      Lemma inst_match_chunk {Σ : LCtx} (c1 c2 : Chunk Σ) (ι : Valuation Σ) :
        instpc (match_chunk c1 c2) ι <-> inst c1 ι = inst c2 ι.
      Proof.
        revert c2.
        induction c1 as [p1 ts1|σ1 r1 t1|c11 IHc11 c12 IHc12|c11 IHc11 c12 IHc12];
          intros [p2 ts2|σ2 r2 t2|c21 c22|c21 c22]; cbn; rewrite ?inst_pathcondition_cons;
            try (split; intros Heq; cbn in Heq; destruct_conjs; discriminate);
            change (inst_chunk ?c ?ι) with (inst c ι).
        - split.
          + destruct (eq_dec p1 p2) as [Heqp|Hneqp].
            * destruct Heqp; cbn. rewrite inst_formula_eqs_ctx. intuition.
            * cbn. intros []. discriminate.
          + remember (inst ts1 ι) as vs1.
            remember (inst ts2 ι) as vs2.
            intros Heq. dependent elimination Heq.
            rewrite EqDec.eq_dec_refl. cbn.
            rewrite inst_formula_eqs_ctx.
            subst. auto.
        - split.
          + destruct (eq_dec_het r1 r2).
            * dependent elimination e; cbn.
              now intros [-> _].
            * cbn. intros []. discriminate.
          + remember (inst t1 ι) as v1.
            remember (inst t2 ι) as v2.
            intros Heq. dependent elimination Heq.
            unfold eq_dec_het.
            rewrite EqDec.eq_dec_refl. cbn.
            subst. split; auto.
        - rewrite inst_pathcondition_app, IHc11, IHc12.
          split; [intuition|].
          generalize (inst c11 ι), (inst c12 ι), (inst c21 ι), (inst c22 ι).
          clear. intros * Heq. dependent elimination Heq; auto.
        - rewrite inst_pathcondition_app, IHc11, IHc12.
          split; [intuition|].
          generalize (inst c11 ι), (inst c12 ι), (inst c21 ι), (inst c22 ι).
          clear. intros * Heq. dependent elimination Heq; auto.
      Qed.

      Section ConsumePreciseUser.

        Context {Σ} (p : 𝑯) {ΔI ΔO : Ctx Ty} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO) (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO).

        Equations(noeqns) match_chunk_user_precise (c : Chunk Σ) : option (List Formula Σ) :=
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

        Fixpoint find_chunk_user_precise (h : SHeap Σ) : option (SHeap Σ * List Formula Σ) :=
          match h with
          | nil => None
          | cons c h' =>
              match match_chunk_user_precise c with
              | Some eqs => Some (if is_duplicable p then cons c h' else h', eqs)
              | None => option_map (base.prod_map (cons c) id) (find_chunk_user_precise h')
              end
          end.

      End ConsumePreciseUser.

      Section ConsumePrecisePtsreg.

        Context {Σ σ} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).

        Equations(noeqns) match_chunk_ptsreg_precise (c : Chunk Σ) : option (Formula Σ) :=
        match_chunk_ptsreg_precise (chunk_ptsreg r' t')
        with eq_dec_het r r' => {
          match_chunk_ptsreg_precise (chunk_ptsreg ?(r) t') (left eq_refl) := Some (formula_eq t t');
          match_chunk_ptsreg_precise (chunk_ptsreg r' t') (right _) := None
        };
        match_chunk_ptsreg_precise _ := None.

        Fixpoint find_chunk_ptsreg_precise (h : SHeap Σ) : option (SHeap Σ * List Formula Σ) :=
          match h with
          | nil => None
          | cons c h' =>
              match match_chunk_ptsreg_precise c with
              | Some fml => Some (h', cons fml nil)
              | None => option_map (base.prod_map (cons c) id) (find_chunk_ptsreg_precise h')
              end
          end.

      End ConsumePrecisePtsreg.

      Definition try_consume_chunk_precise {Σ} (h : SHeap Σ) (c : Chunk Σ) : option (SHeap Σ * List Formula Σ) :=
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

      Definition consume_chunk {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit.
      Proof.
        intros w0 c.
        eapply bind.
        apply get_heap.
        intros w1 ω01 h.
        pose proof (peval_chunk (persist c ω01)) as c1. clear c.
        destruct (try_consume_chunk_exact h c1) as [h'|].
        { apply put_heap. apply h'. }
        destruct (try_consume_chunk_precise h c1) as [[h' eqs]|].
        { eapply bind_right.
          apply put_heap. apply h'.
          intros w2 ω12.
          apply assert_formulas.
          apply (persist (A := List Formula) eqs ω12).
        }
        { intros _ δ1 h1.
          apply
            (SymProp.error
               (EMsgHere
                  {| debug_consume_chunk_program_context := Γ;
                     debug_consume_chunk_pathcondition := wco w1;
                     debug_consume_chunk_localstore := δ1;
                     debug_consume_chunk_heap := h1;
                     debug_consume_chunk_chunk := c1
                  |})).
        }
      Defined.

      Definition consume_chunk_angelic {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit.
      Proof.
        intros w0 c.
        eapply bind.
        apply get_heap.
        intros w1 ω01 h.
        pose proof (peval_chunk (persist c ω01)) as c1. clear c.
        destruct (try_consume_chunk_exact h c1) as [h'|].
        { apply put_heap. apply h'. }
        destruct (try_consume_chunk_precise h c1) as [[h' eqs]|].
        { eapply bind_right.
          apply put_heap. apply h'.
          intros w2 ω12.
          apply assert_formulas.
          apply (persist (A := List Formula) eqs ω12).
        }
        { eapply bind.
          refine (angelic_list
                    (A := Pair Chunk SHeap)
                    (fun δ h =>
                       {| debug_consume_chunk_program_context := Γ;
                          debug_consume_chunk_pathcondition := wco w1;
                          debug_consume_chunk_localstore := δ;
                          debug_consume_chunk_heap := h;
                          debug_consume_chunk_chunk := c1
                        |})
                    (heap_extractions h)).
          intros w2 ω12 [c' h'].
          eapply bind_right.
          apply assert_formulas.
          apply (match_chunk (persist c1 ω12) c').
          intros w3 ω23.
          apply put_heap.
          apply (persist (A := SHeap) h' ω23).
        }
      Defined.

      (* Definition smut_leakcheck {Γ Σ} : SMut Γ Γ Unit Σ := *)
      (*   smut_get_heap >>= fun _ _ h => *)
      (*   match h with *)
      (*   | nil => smut_pure tt *)
      (*   | _   => smut_error "SMut.leakcheck" "Heap leak" h *)
      (*   end. *)

      Definition produce {Γ} :
        ⊢ Assertion -> □(SMut Γ Γ Unit).
      Proof.
        refine (fix produce w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assume_formula fml).
        - apply (produce_chunk <$> persist c).
        - apply (produce_chunk <$> persist c).
        - apply (demonic_match_bool <$> persist__term b <*> four (produce _ asn1) <*> four (produce _ asn2)).
        - intros w1 ω01.
          apply (demonic_match_enum
                    (persist__term k ω01)
                    (fun EK : 𝑬𝑲 E => four (produce w0 (alts EK)) ω01)).
        - refine (demonic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr <$> persist__term s <*> four _ <*> four _).
          intros w1 ω01 t1.
          apply (produce (wsnoc w0 (xl∷σ)) asn1).
          apply (acc_snoc_left ω01 (xl∷σ) t1).
          intros w1 ω01 t1.
          apply (produce (wsnoc w0 (xr∷τ)) asn2).
          apply (acc_snoc_left ω01 (xr∷τ) t1).
        - apply (box_demonic_match_list xh xt s).
          + apply (produce _ asn1).
          + intros w1 ω01 thead ttail.
            apply (produce (wsnoc (wsnoc w0 (xh∷_)) (xt∷_)) asn2 w1).
            apply (acc_snoc_left (acc_snoc_left ω01 (xh∷_) thead) (xt∷_) ttail).
        - apply (box_demonic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (produce (wsnoc (wsnoc w0 (xl∷σ1)) (xr∷σ2)) asn w1).
          apply (acc_snoc_left (acc_snoc_left ω01 (xl∷σ1) t1) (xr∷σ2) t2).
        - apply (box_demonic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (produce (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_demonic_match_record id p s).
          intros w1 ω01 ts.
          apply (produce (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_demonic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (produce (wcat w0 (alt__ctx UK)) (alt__rhs UK) w1).
          apply acc_cat_left; auto.
        - apply (bind_right <$> produce _ asn1 <*> four (produce _ asn2)).
        - apply (demonic_binary <$> produce _ asn1 <*> produce _ asn2).
        - intros w1 ω01.
          eapply bind.
          apply (@demonic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (produce (wsnoc w0 (ς∷τ)) asn w2).
          apply (acc_snoc_left (acc_trans ω01 ω12) (ς∷τ) t2).
        - intros w1 ω01.
          apply (debug (DT := DebugAsn)).
          intros δ h.
          apply (MkDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

      Definition consume {Γ} :
        ⊢ Assertion -> □(SMut Γ Γ Unit).
      Proof.
        refine (fix consume w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assert_formula fml).
        - apply (consume_chunk <$> persist c).
        - apply (consume_chunk_angelic <$> persist c).
        - apply (angelic_match_bool <$> persist__term b <*> four (consume _ asn1) <*> four (consume _ asn2)).
        - intros w1 ω01.
          apply (angelic_match_enum
                    (persist__term k ω01)
                    (fun EK : 𝑬𝑲 E => four (consume w0 (alts EK)) ω01)).
        - refine (angelic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr <$> persist__term s <*> four _ <*> four _).
          intros w1 ω01 t1.
          apply (consume (wsnoc w0 (xl∷σ)) asn1).
          apply (acc_snoc_left ω01 (xl∷σ) t1).
          intros w1 ω01 t1.
          apply (consume (wsnoc w0 (xr∷τ)) asn2).
          apply (acc_snoc_left ω01 (xr∷τ) t1).
        - apply (box_angelic_match_list xh xt s).
          + apply (consume _ asn1).
          + intros w1 ω01 thead ttail.
            apply (consume (wsnoc (wsnoc w0 (xh∷_)) (xt∷_)) asn2 w1).
            apply (acc_snoc_left (acc_snoc_left ω01 (xh∷_) thead) (xt∷_) ttail).
        - apply (box_angelic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (consume (wsnoc (wsnoc w0 (xl∷σ1)) (xr∷σ2)) asn w1).
          apply (acc_snoc_left (acc_snoc_left ω01 (xl∷σ1) t1) (xr∷σ2) t2).
        - apply (box_angelic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (consume (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_angelic_match_record id p s).
          intros w1 ω01 ts.
          apply (consume (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_angelic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (consume (wcat w0 (alt__ctx UK)) (alt__rhs UK) w1).
          apply acc_cat_left; auto.
        - apply (bind_right <$> consume _ asn1 <*> four (consume _ asn2)).
        - apply (angelic_binary <$> consume _ asn1 <*> consume _ asn2).
        - intros w1 ω01.
          eapply bind.
          apply (@angelic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (consume (wsnoc w0 (ς∷τ)) asn w2).
          apply (acc_snoc_left (acc_trans ω01 ω12) (ς∷τ) t2).
        - intros w1 ω01.
          apply (debug (DT := DebugAsn)).
          intros δ h.
          apply (MkDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

    End ProduceConsume.

    Section Exec.

      Variable cfg : Config.

      Definition call_contract {Γ Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SMut Γ Γ (STerm τ).
      Proof.
        destruct c as [Σe δe req result ens].
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind_right.
        apply (assert_formulas
                 (* {| *)
                 (*   msg_function := "SMut.call"; *)
                 (*   msg_message := "argument pattern match"; *)
                 (*   msg_program_context := Γ; *)
                 (*   msg_localstore := subst δ0 ω01; *)
                 (*   msg_heap := subst h0 ω01; *)
                 (*   msg_pathcondition := wco w1; *)
                 (* |} *) (formula_eqs_nctx (subst δe evars) (persist args ω01))).
        intros w2 ω12.
        eapply bind_right.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (acc_trans _ ω12).
        constructor 2 with evars. cbn. constructor.
        intros w3 ω23.
        eapply bind.
        apply (demonic (Some result)).
        intros w4 ω34 res.
        eapply bind_right.
        apply (produce
                 (w := @MkWorld (Σe ▻ result∷τ) nil)
                 ens).
        constructor 2 with (sub_snoc (persist (A := Sub _) evars (acc_trans ω12 (acc_trans ω23 ω34))) (result∷τ) res).
        cbn. constructor.
        intros w5 ω45. clear - res ω45.
        apply pure.
        apply (persist__term res ω45).
      Defined.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) :
        ⊢ SStore Δ -> SMut Γ Γ Unit.
      Proof.
        destruct lem as [Σe δe req ens].
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind_right.
        apply (assert_formulas
                 (* {| *)
                 (*   msg_function := "SMut.call"; *)
                 (*   msg_message := "argument pattern match"; *)
                 (*   msg_program_context := Γ; *)
                 (*   msg_localstore := subst δ0 ω01; *)
                 (*   msg_heap := subst h0 ω01; *)
                 (*   msg_pathcondition := wco w1; *)
                 (* |} *) (formula_eqs_nctx (subst δe evars) (persist args ω01))).
        intros w2 ω12.
        eapply bind_right.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (acc_trans _ ω12).
        constructor 2 with evars. cbn. constructor.
        intros w3 ω23.
        apply (produce
                 (w := @MkWorld Σe nil)
                 ens).
        constructor 2 with (persist (A := Sub _) evars (acc_trans ω12 ω23)).
        cbn. constructor.
      Defined.

      Definition call_contract_debug {Γ Δ τ} (f : 𝑭 Δ τ) (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SMut Γ Γ (STerm τ) :=
        fun w0 δΔ =>
          let o := call_contract c δΔ in
          if config_debug_function cfg f
          then
            debug
              (fun δ h => {| debug_call_function_parameters := Δ;
                             debug_call_function_result_type := τ;
                             debug_call_function_name := f;
                             debug_call_function_contract := c;
                             debug_call_function_arguments := δΔ;
                             debug_call_program_context := Γ;
                             debug_call_pathcondition := wco w0;
                             debug_call_localstore := δ;
                             debug_call_heap := h|})
              o
          else o.

      Definition Exec := forall Γ τ (s : Stm Γ τ), ⊢ SMut Γ Γ (STerm τ).

      Section ExecAux.

        Variable rec : Exec.

        Fixpoint exec_aux {Γ τ} (s : Stm Γ τ) {struct s} :
          ⊢ SMut Γ Γ (STerm τ).
        Proof.
          intros w0; destruct s.
          - apply pure. apply (term_val τ v).
          - apply (eval_exp e).
          - eapply bind. apply (exec_aux _ _ s1).
            intros w1 ω01 t1.
            eapply (pushpop t1).
            apply (exec_aux _ _ s2).
          - eapply (pushspops (lift δ)).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (exec_aux _ _ s).
            intros w1 ω01 t.
            eapply bind_right.
            apply (assign x t).
            intros w2 ω12.
            apply pure.
            apply (subst (T := STerm τ) t (sub_acc ω12)).
          - eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            destruct (CEnv f) as [c|].
            + apply (call_contract_debug f c args).
            + intros POST δΓ. refine (rec (FunDef f) _ args).
              intros w2 ω12 res _. apply POST. apply ω12.
              apply res. refine (persist δΓ ω12).
          - rename δ into δΔ.
            eapply bind.
            apply get_local.
            intros w1 ω01 δ1.
            eapply bind_right.
            apply (put_local (lift δΔ)).
            intros w2 ω12.
            eapply bind.
            apply (exec_aux _ _ s).
            intros w3 ω23 t.
            eapply bind_right.
            apply put_local.
            apply (persist (A := SStore _) δ1 (acc_trans ω12 ω23)).
            intros w4 ω34.
            apply pure.
            apply (persist__term t ω34).
          - eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            apply (call_contract (CEnvEx f) args).
          - eapply bind_right.
            eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            apply (call_lemma (LEnv l) args).
            intros w2 ω12.
            apply (exec_aux _ _ s).
          - eapply bind. apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_bool t).
            + intros w2 ω12.
              apply (exec_aux _ _ s1).
            + intros w2 ω12.
              apply (exec_aux _ _ s2).
          - eapply bind_right.
            apply (exec_aux _ _ s1).
            intros w1 ω01.
            apply (exec_aux _ _ s2).
          - eapply bind. apply (eval_exp e1).
            intros w1 ω01 t.
            eapply bind_right.
            apply (assume_formula (formula_bool t)).
            intros w2 ω12.
            apply (exec_aux _ _ s).
          - apply block.
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_list (𝑿to𝑺 xh) (𝑿to𝑺 xt) t).
            + intros w2 ω12.
              apply (exec_aux _ _ s1).
            + intros w2 ω12 thead ttail.
              eapply (pushspops (env.snoc (env.snoc env.nil (xh∷_) thead) (xt∷_) ttail)).
              apply (exec_aux _ _ s2).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_sum (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t).
            + intros w2 ω12 tl.
              eapply (pushpop tl).
              apply (exec_aux _ _ s1).
            + intros w2 ω12 tr.
              eapply (pushpop tr).
              apply (exec_aux _ _ s2).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_prod (𝑿to𝑺 xl) (𝑿to𝑺 xr) t).
            intros w2 ω12 t1 t2.
            eapply (pushspops (env.snoc (env.snoc env.nil (_∷_) t1) (_∷_) t2)).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_enum t).
            intros EK.
            intros w2 ω12.
            apply (exec_aux _ _ (alts EK)).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_tuple 𝑿to𝑺 p t).
            intros w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_union 𝑿to𝑺 alt__pat t).
            intros UK w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_aux _ _ (alt__rhs UK)).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_record 𝑿to𝑺 p t).
            intros w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_bvec t).
            intros bs w2 ω12.
            apply (exec_aux _ _ (rhs bs)).
          - eapply bind.
            apply (angelic None τ).
            intros w1 ω01 t.
            eapply bind_right.
            apply (T (consume (asn_chunk (chunk_ptsreg reg t)))).
            intros w2 ω12.
            eapply bind_right.
            apply (T (produce (asn_chunk (chunk_ptsreg reg (persist__term t ω12))))).
            intros w3 ω23.
            apply pure.
            apply (persist__term t (acc_trans ω12 ω23)).
          - eapply bind.
            eapply (angelic None τ).
            intros w1 ω01 told.
            eapply bind_right.
            apply (T (consume (asn_chunk (chunk_ptsreg reg told)))).
            intros w2 ω12.
            eapply bind.
            apply (eval_exp e).
            intros w3 ω23 tnew.
            eapply bind_right.
            apply (T (produce (asn_chunk (chunk_ptsreg reg tnew)))).
            intros w4 ω34.
            apply pure.
            apply (persist__term tnew ω34).
          - apply (error "SMut.exec" "stm_bind not supported" tt).
          - apply (debug (DT := DebugStm)).
            intros δ0 h0.
            econstructor.
            apply s.
            apply (wco w0).
            apply δ0.
            apply h0.
            apply (exec_aux _ _ s).
        Defined.

      End ExecAux.

      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ _ => error "SMut.exec" "out of fuel for inlining" tt
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} _ {w} _ _ _.

      Import Notations.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        SMut Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := [] |} :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          produce (w:=@MkWorld _ _) req acc_refl >> fun w1 ω01 =>
          exec inline_fuel s >>= fun w2 ω12 res =>
          consume
            (w:=wsnoc (@MkWorld _ []) (result∷τ)%ctx)
            ens
            (acc_snoc_left (acc_trans ω01 ω12) (result∷τ)%ctx res)
        end.

      Definition exec_contract_path {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) : 𝕊 wnil :=
        demonic_close (exec_contract c s (fun w1 ω01 _ δ1 h1 => SymProp.block) (sep_contract_localstore c) nil).

      Definition ValidContractWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        VerificationCondition (prune (solve_uvars (prune (solve_evars (prune (exec_contract_path c body)))))).

    End Exec.

    Definition ok {Σ} (p : 𝕊 Σ) : bool :=
      match prune p with
      | SymProp.block => true
      | _           => false
      end.

    Lemma ok_sound {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      is_true (ok p) -> safe p ι.
    Proof.
      rewrite <- prune_sound. unfold ok.
      generalize (prune p) as q. clear. intros q.
      destruct q; try discriminate; cbn; auto.
    Qed.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (prune (solve_uvars (prune (solve_evars (prune (exec_contract_path default_config 1 c body)))))).

    Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      is_true (ok (prune (solve_uvars (prune (solve_evars (prune (exec_contract_path default_config 1 c body))))))).

    Lemma validcontract_reflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflect c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractReflect, ValidContract. intros Hok.
      apply (ok_sound _ env.nil) in Hok. now constructor.
    Qed.

  End SMut.

End MutatorsOn.

Module MakeExecutor
  (Import B    : Base)
  (Import SPEC : Specification B)
  (Import SOLV : SolverKit B SPEC).

  Include MutatorsOn B SPEC SOLV.

End MakeExecutor.
