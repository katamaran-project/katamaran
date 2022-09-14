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

From Katamaran Require Import
     Prelude
     Context
     Environment
     Syntax.TypeDecl.

Import ctx.notations.
Import env.notations.

Module Type PatternsOn (Import TY : Types).

  Section Patterns.

    (* These patterns are used in program and logic contexts for pattern
       matching in statements and in assertions. We abstract over the type of
       variables here. *)
    Context {N : Set}.

    Inductive TuplePat : Ctx Ty -> NCtx N Ty -> Set :=
    | tuplepat_nil  : TuplePat [] []
    | tuplepat_snoc
        {σs : Ctx Ty} {Δ : NCtx N Ty}
        (pat : TuplePat σs Δ) {σ : Ty} (x : N) :
        TuplePat (σs ▻ σ) (Δ ▻ x∷σ).

    Inductive RecordPat : NCtx recordf Ty -> NCtx N Ty -> Set :=
    | recordpat_nil  : RecordPat [] []
    | recordpat_snoc
        {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
        (pat : RecordPat rfs Δ) (rf : recordf) {τ : Ty} (x : N) :
        RecordPat (rfs ▻ rf∷τ) (Δ ▻ x∷τ).

    Inductive Pattern : NCtx N Ty -> Ty -> Set :=
    | pat_var (x : N) {σ : Ty} : Pattern [ x∷σ ] σ
    | pat_unit : Pattern [] ty.unit
    | pat_pair (x y : N) {σ τ : Ty} : Pattern [ x∷σ; y∷τ ] (ty.prod σ τ)
    | pat_tuple {σs Δ} (p : TuplePat σs Δ) : Pattern Δ (ty.tuple σs)
    | pat_record {R Δ} (p : RecordPat (recordf_ty R) Δ) : Pattern Δ (ty.record R)
    | pat_bvec_split (xl xr : N) {m n} : Pattern [ xl∷ty.bvec m; xr∷ty.bvec n] (ty.bvec (m + n)).

    Definition tuple_pattern_match_env {T : Ty -> Set} :
      forall {σs : Ctx Ty} {Δ : NCtx N Ty},
        TuplePat σs Δ -> Env T σs -> NamedEnv T Δ :=
      fix pattern_match {σs} {Δ} p {struct p} :=
        match p with
        | tuplepat_nil => fun _ => []
        | tuplepat_snoc p x =>
          fun EΔ =>
            match env.snocView EΔ with
            | env.isSnoc E v => pattern_match p E ► (_ ↦ v)
            end
        end.

    Definition tuple_pattern_match_env_reverse {T : Ty -> Set} :
      forall {σs : Ctx Ty} {Δ : NCtx N Ty},
        TuplePat σs Δ -> NamedEnv T Δ -> Env T σs :=
      fix pattern_match {σs} {Δ} p {struct p} :=
        match p with
        | tuplepat_nil => fun _ => []
        | tuplepat_snoc p x =>
          fun EΔ =>
            match env.snocView EΔ with
            | env.isSnoc E v => pattern_match p E ► (_ ↦ v)
            end
        end.

    Definition tuple_pattern_match_val {σs : Ctx Ty} {Δ : NCtx N Ty}
             (p : TuplePat σs Δ) : Val (ty.tuple σs) -> NamedEnv Val Δ :=
      fun lit => tuple_pattern_match_env p (@envrec.to_env Ty Val σs lit).

    Fixpoint record_pattern_match_env {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} : NamedEnv V rfs -> NamedEnv V Δ :=
      match p with
      | recordpat_nil => fun _ => []
      | recordpat_snoc p rf x =>
        fun E =>
          env.snoc
            (record_pattern_match_env p (env.tail E)) (x∷_)
            (env.lookup E ctx.in_zero)
      end.

    Fixpoint record_pattern_match_env_reverse {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} :  NamedEnv V Δ -> NamedEnv V rfs :=
      match p with
      | recordpat_nil => fun _ => env.nil
      | recordpat_snoc p rf x =>
        fun E =>
          env.snoc
            (record_pattern_match_env_reverse p (env.tail E)) (rf∷_)
            (env.lookup E ctx.in_zero)
      end.

    Lemma record_pattern_match_env_inverse_right {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
          (p : RecordPat rfs Δ) (vs : NamedEnv V Δ) :
      record_pattern_match_env p (record_pattern_match_env_reverse p vs) = vs.
    Proof.
      induction p.
      - now destruct (env.nilView vs).
      - destruct (env.snocView vs) as [vs v].
        cbn. f_equal. now apply IHp.
    Qed.

    Lemma record_pattern_match_env_inverse_left {V : Ty -> Set} {rfs : NCtx recordf Ty} {Δ : NCtx N Ty}
          (p : RecordPat rfs Δ) (vs : NamedEnv V rfs) :
      record_pattern_match_env_reverse p (record_pattern_match_env p vs) = vs.
    Proof.
      induction p.
      - now destruct (env.nilView vs).
      - destruct (env.snocView vs) as [vs v].
        cbn. f_equal. now apply IHp.
    Qed.

    Lemma tuple_pattern_match_env_inverse_right {T : Ty -> Set}
      {σs : Ctx Ty} {Δ : NCtx N Ty} (p : TuplePat σs Δ) (ts : NamedEnv T Δ) :
      tuple_pattern_match_env p (tuple_pattern_match_env_reverse p ts) = ts.
    Proof.
      induction p; cbn.
      - now destruct (env.nilView ts).
      - destruct (env.snocView ts); cbn.
        now rewrite (IHp E).
    Qed.

    Lemma tuple_pattern_match_env_inverse_left {T : Ty -> Set}
          {σs : Ctx Ty} {Δ : NCtx N Ty} (p : TuplePat σs Δ) (ts : Env T σs) :
      tuple_pattern_match_env_reverse p (tuple_pattern_match_env p ts) = ts.
    Proof.
      induction p.
      - now destruct (env.nilView ts).
      - destruct (env.snocView ts); cbn.
        now rewrite (IHp E).
    Qed.

    Definition record_pattern_match_val {R} {Δ : NCtx N Ty}
      (p : RecordPat (recordf_ty R) Δ) : Val (ty.record R) -> NamedEnv Val Δ :=
      fun v => record_pattern_match_env p (recordv_unfold R v).

    Definition pattern_match_val {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      Val σ -> NamedEnv Val Δ :=
      match p with
      | pat_var x => fun v => [v]
      | pat_unit => fun _ => []
      | pat_pair x y => fun '(u , v) => [nenv u;v]
      | pat_tuple p => tuple_pattern_match_val p
      | pat_record p => record_pattern_match_val p
      | pat_bvec_split x y => fun v => let (vx,vy) := bv.appView _ _ v in
                                       [env].[x∷ty.bvec _ ↦ vx].[y∷ty.bvec _ ↦ vy]
      end.

    Definition pattern_match_env_val_reverse {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      NamedEnv Val Δ -> Val σ :=
      match p with
      | pat_var x          => fun Ex => match env.snocView Ex with env.isSnoc _ t => t end
      | pat_unit           => fun _  => tt
      | pat_pair x y       => fun Exy =>
                                      let (Ex,vy) := env.snocView Exy in
                                      let (E,vx)  := env.snocView Ex in
                                      (vx, vy)
      | pat_tuple p        => fun EΔ  => envrec.of_env (tuple_pattern_match_env_reverse p EΔ)
      | pat_record p       => fun EΔ  => recordv_fold _ (record_pattern_match_env_reverse p EΔ)
      | pat_bvec_split x y => fun Exy =>
                                let (Ex,vy) := env.snocView Exy in
                                let (E,vx)  := env.snocView Ex in
                                bv.app vx vy
      end.

    Lemma pattern_match_val_inverse_left {σ : Ty} {Δ : NCtx N Ty} {p : Pattern Δ σ}
          (v : Val σ) :
      pattern_match_env_val_reverse p (pattern_match_val p v) = v.
    Proof.
      induction p; cbn; eauto.
      - now destruct v.
      - now destruct v.
      - unfold tuple_pattern_match_val.
        now rewrite tuple_pattern_match_env_inverse_left, envrec.of_to_env.
      - unfold record_pattern_match_val.
        now rewrite record_pattern_match_env_inverse_left, recordv_fold_unfold.
      - now destruct bv.appView.
    Qed.

    Lemma pattern_match_val_inverse_right {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ)
      (vs : NamedEnv Val Δ) :
      pattern_match_val p (pattern_match_env_val_reverse p vs) = vs.
    Proof.
      induction p; cbn; eauto.
      - destruct (env.snocView vs).
        now destruct (env.nilView E).
      - now destruct (env.nilView vs).
      - destruct (env.snocView vs).
        destruct (env.snocView E).
        now destruct (env.nilView E).
      - unfold tuple_pattern_match_val.
        now rewrite envrec.to_of_env, tuple_pattern_match_env_inverse_right.
      - unfold record_pattern_match_val.
        now rewrite recordv_unfold_fold, record_pattern_match_env_inverse_right.
      - destruct env.snocView, env.snocView.
        destruct (env.nilView E).
        now rewrite bv.appView_app.
    Qed.

  End Patterns.

  Bind Scope pat_scope with TuplePat.
  Bind Scope pat_scope with RecordPat.
  Bind Scope pat_scope with Pattern.

End PatternsOn.
