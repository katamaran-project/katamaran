(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From Coq Require Export
     Numbers.BinNums.
From Coq Require Import
     Program.Tactics.
From Katamaran Require Export
     Context
     Environment
     Prelude
     Syntax.BinOps
     Syntax.Registers
     Syntax.TypeDecl
     Syntax.Variables
     Tactics.
From Katamaran Require Import
     Syntax.Expressions
     Syntax.Patterns
     Syntax.Terms
     Symbolic.Instantiation
     Symbolic.OccursCheck
     Symbolic.PartialEvaluation.

Module Type BaseMixin (Import TY : Types).
  Include
    ExpressionsOn TY <+
    TermsOn TY <+ PatternsOn TY <+
    OccursCheckOn TY <+ InstantiationOn TY <+
    PartialEvaluationOn TY.

  Notation PCtx := (NCtx PVar Ty).
  Notation LCtx := (NCtx LVar Ty).
  Notation Valuation Σ := (@Env (Binding LVar Ty) (fun xt : Binding LVar Ty => Val (@type LVar Ty xt)) Σ).
  Notation CStore := (@NamedEnv PVar Ty Val).

  Section PatternMatching.
    Context {N : Set}.

    Definition pattern_match_env_reverse {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      NamedEnv (Term Σ) Δ -> Term Σ σ :=
      match p with
      | pat_var x          => fun Ex => match env.snocView Ex with env.isSnoc _ t => t end
      | pat_unit           => fun _ => term_val ty.unit tt
      | pat_pair x y       => fun Exy =>
                                let (Ex,ty) := env.snocView Exy in
                                let (E,tx)  := env.snocView Ex in
                                term_binop bop.pair tx ty
      | pat_tuple p        => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ)
      | pat_record p       => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ)
      | pat_bvec_split x y => fun Exy =>
                                let (Ex,ty) := env.snocView Exy in
                                let (E,tx)  := env.snocView Ex in
                                term_binop bop.bvapp tx ty
      end.

    Lemma inst_tuple_pattern_match {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : Env (Term Σ) σs) :
      inst (tuple_pattern_match_env p ts) ι =
      tuple_pattern_match_env p (inst (T := fun Σ => Env (Term Σ) σs) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_tuple_pattern_match_reverse {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : NamedEnv (Term Σ) Δ) :
      inst (tuple_pattern_match_env_reverse p ts) ι =
      tuple_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_record_pattern_match {Δ__R : NCtx recordf Ty} {Σ : LCtx} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ__R) :
      inst (T := fun Σ => NamedEnv (Term Σ) Δ) (record_pattern_match_env p ts) ι =
      record_pattern_match_env p (inst ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_record_pattern_match_reverse {Δ__R : NCtx recordf Ty} {Σ : LCtx} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ) :
      inst (record_pattern_match_env_reverse p ts) ι =
      record_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_pattern_match_env_reverse {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty}
          (ι : Valuation Σ) (p : Pattern Δ σ) (ts : NamedEnv (Term Σ) Δ) :
      inst (Inst := inst_term) (pattern_match_env_reverse p ts) ι =
      pattern_match_env_val_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      induction p.
      - now destruct (env.snocView ts).
      - reflexivity.
      - destruct (env.snocView ts).
        now destruct (env.snocView E); cbn.
      - cbn - [Val].
        now rewrite inst_term_tuple, inst_tuple_pattern_match_reverse.
      - cbn.
        f_equal.
        apply inst_record_pattern_match_reverse.
      - cbn. now destruct env.snocView, env.snocView.
    Qed.

    Definition newpattern_match_term_reverse {Σ σ} (pat : @PatternShape N σ) :
      forall (pc : PatternCase pat), NamedEnv (Term Σ) (PatternCaseCtx pc) -> Term Σ σ :=
      match pat with
      | pat_shape_var σ x =>
          fun _ ts => env.head ts
      | pat_shape_bool =>
          fun b _ => term_val ty.bool b
      | pat_shape_list σ x y =>
          fun b =>
            match b with
            | true => fun _ => term_val (ty.list σ) nil
            | false => fun Eht =>
                         let (Eh,t) := env.snocView Eht in
                         let (E,h)  := env.snocView Eh in
                         term_binop bop.cons h t
            end
      | pat_shape_prod σ τ x y =>
          fun _ Exy =>
            let (Ex,vτ) := env.snocView Exy in
            let (E,vσ)  := env.snocView Ex in
            term_binop bop.pair vσ vτ
      | pat_shape_sum σ0 τ x y =>
          fun b =>
            match b with
            | true => fun ts => term_inl (env.head ts)
            | false => fun ts => term_inr (env.head ts)
            end
      | pat_shape_unit =>
          fun pc _ => term_val ty.unit pc
      | pat_shape_enum E =>
          fun v _ => term_val (ty.enum E) v
      | pat_shape_bvec_split m n x y =>
          fun _ Exy =>
            let (Ex,vr) := env.snocView Exy in
            let (E,vl)  := env.snocView Ex in
            term_binop bop.bvapp vl vr
      | pat_shape_bvec_exhaustive m =>
          fun v _ => term_val (ty.bvec m) v
      | pat_shape_tuple σs Δ p =>
          fun _ ts => term_tuple (tuple_pattern_match_env_reverse p ts)
      | pat_shape_union U x =>
          fun K ts => term_union U K (env.head ts)
      | pat_shape_record R Δ p =>
          fun _ ts => term_record R (record_pattern_match_env_reverse p ts)
      end.

    Lemma inst_newpattern_match_term_reverse {Σ σ} (ι : Valuation Σ) (pat : @PatternShape N σ) :
      forall (pc : PatternCase pat) (ts : NamedEnv (Term Σ) (PatternCaseCtx pc)),
        inst (newpattern_match_term_reverse pat pc ts) ι =
        newpattern_match_val_reverse pat pc (inst (T := fun Σ => NamedEnv (Term Σ) _) ts ι).
    Proof.
      destruct pat; cbn.
      - intros _ ts. now env.destroy ts.
      - reflexivity.
      - intros [] ts.
        + reflexivity.
        + now env.destroy ts.
      - intros _ ts. now env.destroy ts.
      - intros [] ts; now env.destroy ts.
      - intros [] ts. reflexivity.
      - reflexivity.
      - intros _ ts. now env.destroy ts.
      - reflexivity.
      - intros _ ts.
        rewrite <- inst_tuple_pattern_match_reverse.
        generalize (tuple_pattern_match_env_reverse p ts).
        clear.
        intros e. induction e; cbn.
        + reflexivity.
        + f_equal. apply IHe.
      - intros K ts. now env.destroy ts.
      - intros _ ts. f_equal.
        apply inst_record_pattern_match_reverse.
    Qed.

  End PatternMatching.

  Import env.notations.

  Definition seval_exp {Γ Σ} (δ : SStore Γ Σ) :
    forall {σ} (e : Exp Γ σ), Term Σ σ :=
    fix seval_exp {σ} (e : Exp Γ σ) : Term Σ σ :=
      match e with
      | exp_var ς                => δ.[??ς]
      | exp_val σ v              => term_val σ v
      | exp_binop op e1 e2       => term_binop op (seval_exp e1) (seval_exp e2)
      | exp_neg e                => term_neg (seval_exp e)
      | exp_not e                => term_not (seval_exp e)
      | exp_inl e                => term_inl (seval_exp e)
      | exp_inr e                => term_inr (seval_exp e)
      | exp_list es              => term_list (List.map seval_exp es)
      | exp_bvec es              => term_bvec (Vector.map seval_exp es)
      | exp_tuple es             => term_tuple (env.map (@seval_exp) es)
      | exp_union E K e          => term_union E K (seval_exp e)
      | exp_record R es          => term_record R (env.map (fun _ => seval_exp) es)
      end%exp.

  Lemma eval_exp_inst {Γ Σ τ} (ι : Valuation Σ) (δΓΣ : SStore Γ Σ) (e : Exp Γ τ) :
    eval e (inst δΓΣ ι) = inst (seval_exp δΓΣ e) ι.
  Proof.
    induction e; cbn; repeat f_equal; auto.
    { unfold inst, inst_store, inst_env at 1; cbn.
      now rewrite env.lookup_map.
    }
    2: {
      induction es as [|eb n es IHes]; cbn in *.
      { reflexivity. }
      { destruct X as [-> Heqs].
        change (inst_term ?ι ?t) with (inst ι t).
        destruct (inst (seval_exp δΓΣ eb) ι);
          cbn; f_equal; auto.
      }
    }
    all: induction es; cbn in *; destruct_conjs; f_equal; auto.
  Qed.

  Lemma subst_seval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
    subst (T := fun Σ => Term Σ _) (seval_exp δ e) ζ = seval_exp (subst δ ζ) e.
  Proof.
    induction e; cbn; f_equal; auto.
    { now rewrite (subst_lookup xInΓ). }
    all: induction es; cbn in *; destruct_conjs; f_equal; auto.
  Qed.

  (* Preciseness for spatial predicates *)
  Record Precise {P : Set} (F : P -> Ctx Ty) (p : P) : Set :=
    MkPrecise
      { prec_input  : Ctx Ty;
        prec_output : Ctx Ty;
        prec_inout  : F p = ctx.cat prec_input prec_output;
      }.
  Arguments MkPrecise {_ _ _} & _ _ _.

End BaseMixin.

Module Type Base := Types <+ RegDeclKit <+ BaseMixin.

Module DefaultBase <: Base.

  #[export] Instance typedeclkit : TypeDeclKit := DefaultTypeDeclKit.
  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit := DefaultTypeDenoteKit.
  #[export] Instance typedefkit : TypeDefKit typedenotekit := DefaultTypeDefKit.
  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include DefaultRegDeclKit.
  Include BaseMixin.

End DefaultBase.
