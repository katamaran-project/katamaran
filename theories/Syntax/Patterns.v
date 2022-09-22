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
Import SigTNotations.

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

    (* A [PatternShape] describes the different pattern matching possibilities.
       Not every type can be matched on, and some types can be matched on in
       different ways, e.g. bitvectors. The [PatternShape], as opposed to the
       [PatternCase] below, is a value that is provided by the user in the
       program and therefore includes all the names ((program or logic
       variables) for all alternatives of that match. For example
       [pat_shape_sum] contains the names [x] and [y] for the [inl] and [inr]
       cases. *)
    Inductive PatternShape : Ty -> Set :=
    | pat_shape_var (x : N) {σ}                             : PatternShape σ
    | pat_shape_bool                                        : PatternShape ty.bool
    | pat_shape_list σ (x y : N)                            : PatternShape (ty.list σ)
    | pat_shape_prod (x y : N) {σ τ}                        : PatternShape (ty.prod σ τ)
    | pat_shape_sum σ τ (x y : N)                           : PatternShape (ty.sum σ τ)
    | pat_shape_unit                                        : PatternShape ty.unit
    | pat_shape_enum E                                      : PatternShape (ty.enum E)
    | pat_shape_bvec_split m n (x y : N)                    : PatternShape (ty.bvec (m+n))
    | pat_shape_bvec_exhaustive m                           : PatternShape (ty.bvec m)
    | pat_shape_tuple {σs Δ} (p : TuplePat σs Δ)             : PatternShape (ty.tuple σs)
    | pat_shape_record R Δ (p : RecordPat (recordf_ty R) Δ) : PatternShape (ty.record R)
    | pat_shape_union U
        (p : forall K, PatternShape (unionk_ty U K))        : PatternShape (ty.union U).

    (* This describes the different cases/alternatives for a single pattern
       match of a particular shape. It can be seen as a representation of the
       arity of a match. *)
    Fixpoint PatternCase {σ} (pat : PatternShape σ) : Set :=
      match pat with
      | pat_shape_var x              => unit
      | pat_shape_bool               => bool
      | pat_shape_list σ x y         => bool
      | pat_shape_prod x y           => unit
      | pat_shape_sum σ τ x y        => bool
      | pat_shape_unit               => unit
      | pat_shape_enum E             => enumt E
      | pat_shape_bvec_split m n x y => unit
      | pat_shape_bvec_exhaustive m  => bv m
      | pat_shape_tuple p            => unit
      | pat_shape_record R Δ p       => unit
      | pat_shape_union U p          => { K : unionk U & PatternCase (p K) }
      end.

    #[export] Instance EqDec_PatternCase :
      forall {σ} (pat : PatternShape σ),
        Classes.EqDec (PatternCase pat) :=
      fix eqd {σ} pat :=
        match pat return Classes.EqDec (PatternCase pat) with
        | pat_shape_var _              => EqDecInstances.unit_EqDec
        | pat_shape_bool               => EqDecInstances.bool_EqDec
        | pat_shape_list _ _ _         => EqDecInstances.bool_EqDec
        | pat_shape_prod _ _           => EqDecInstances.unit_EqDec
        | pat_shape_sum _ _ _ _        => EqDecInstances.bool_EqDec
        | pat_shape_unit               => EqDecInstances.unit_EqDec
        | pat_shape_enum E             => enumt_eqdec E
        | pat_shape_bvec_split _ _ _ _ => EqDecInstances.unit_EqDec
        | pat_shape_bvec_exhaustive m  => bv.eqdec_bv
        | pat_shape_tuple _            => EqDecInstances.unit_EqDec
        | pat_shape_record _ _ _       => EqDecInstances.unit_EqDec
        | pat_shape_union U p          => EqDecInstances.sigma_eqdec
                                            (unionk_eqdec U)
                                            (fun K => eqd (p K))
        end.

    #[export] Instance Finite_PatternCase :
      forall {σ} (pat : PatternShape σ),
        finite.Finite (PatternCase pat) :=
      fix fin {σ} pat :=
        match pat with
        | pat_shape_var _              => finite.unit_finite
        | pat_shape_bool               => Finite_bool
        | pat_shape_list _ _ _         => Finite_bool
        | pat_shape_prod _ _           => finite.unit_finite
        | pat_shape_sum _ _ _ _        => Finite_bool
        | pat_shape_unit               => finite.unit_finite
        | pat_shape_enum E             => enumt_finite E
        | pat_shape_bvec_split _ _ _ _ => finite.unit_finite
        | pat_shape_bvec_exhaustive m  => bv.finite_bv
        | pat_shape_tuple _            => finite.unit_finite
        | pat_shape_record _ _ _       => finite.unit_finite
        | pat_shape_union U p          =>
            @Finite_sigT (unionk U) _ _
              (fun K => PatternCase (p K))
              (fun K => EqDec_PatternCase (p K))
              (fun K => fin (p K))
        end.

    (* For each [PatternShape] and each [PatternCase] for that shape, calculate
       the context that represents the variables bound in that case. *)
    Fixpoint PatternCaseCtx {σ} {p : PatternShape σ} : PatternCase p -> NCtx N Ty :=
      match p with
      | @pat_shape_var x σ           => fun _ => [x∷σ]
      | pat_shape_bool               => fun _ => [ctx]
      | pat_shape_list σ x y         => fun b => if b then [ctx] else [x∷σ; y∷ty.list σ]
      | @pat_shape_prod x y σ τ      => fun _ => [x∷σ; y∷τ]
      | pat_shape_sum σ τ x y        => fun b => if b then [x∷σ] else [y∷τ]
      | pat_shape_unit               => fun _ => [ctx]
      | pat_shape_enum _             => fun _ => [ctx]
      | pat_shape_bvec_split m n x y => fun _ => [x∷ty.bvec m; y∷ty.bvec n]
      | pat_shape_bvec_exhaustive m  => fun _ => [ctx]
      | @pat_shape_tuple _ Δ _       => fun _ => Δ
      | pat_shape_record _ Δ _       => fun _ => Δ
      | pat_shape_union U p          => fun '(K; pc) =>
                                          @PatternCaseCtx (unionk_ty U K) (p K) pc
      end%ctx.

    (* Pattern match on a value. The result is a [PatternCase] that represents
       the alternative corresponding to the value, together with an environment
       that maps the variables of the pattern to values. *)
    Fixpoint newpattern_match_val {σ} (pat : PatternShape σ) :
      Val σ -> { c : PatternCase pat & NamedEnv Val (PatternCaseCtx c) } :=
      match pat with
      | pat_shape_var x =>
          fun v => (tt; [env].[x∷_ ↦ v])
      | pat_shape_bool       =>
          fun b => (b; [env])
      | pat_shape_list σ x y =>
          fun v : Val (ty.list σ) =>
            match v with
            | nil       => (true; [env])
            | cons v vs => (false; [env].[x∷σ ↦ v].[y∷ty.list σ ↦ vs])
            end
      | pat_shape_prod x y =>
          fun '(a, b) => (tt; [env].[x∷_ ↦ a].[y∷_ ↦ b])
      | pat_shape_sum σ τ x y =>
          fun v =>
            match v with
            | inl a => (true; [env].[x∷σ ↦ a])
            | inr b => (false; [env].[y∷τ ↦ b])
            end
      | pat_shape_unit =>
          fun _ => (tt; [env])
      | pat_shape_enum E =>
          fun v : enumt E => (v; [env])
      | pat_shape_bvec_split m n x y =>
          fun v =>
            match bv.appView m n v with
            | bv.isapp xs ys =>
                (tt; [env].[x∷ty.bvec m ↦ xs].[y∷ty.bvec n ↦ ys])
            end
      | pat_shape_bvec_exhaustive m =>
          fun v => (v; [env])
      | pat_shape_tuple p =>
          fun v => (tt; tuple_pattern_match_val p v)
      | pat_shape_record R Δ p =>
          fun v => (tt; record_pattern_match_val p v)
      | pat_shape_union U p =>
          fun v =>
            let (K, u)    := unionv_unfold U v in
            let (pc, δpc) := newpattern_match_val (p K) u in
            ((K; pc); δpc)
      end.

    (* Reverse a pattern match. Given a [PatternCase] and an environment with
       values for all variables in the pattern, reconstruct a value. *)
    Fixpoint newpattern_match_val_reverse {σ} (pat : PatternShape σ) :
      forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> Val σ :=
      match pat with
      | pat_shape_var x      => fun _ vs => env.head vs
      | pat_shape_bool       => fun b _ => b
      | pat_shape_list σ x y =>
          fun b =>
            match b with
            | true  => fun _ => nil
            | false => fun Eht =>
                         let (Eh,t) := env.snocView Eht in
                         let (E,h)  := env.snocView Eh in
                         cons h t
            end
      | pat_shape_prod x y =>
          fun _ Exy =>
            let (Ex,vy) := env.snocView Exy in
            let (E,vx)  := env.snocView Ex in
            (vx,vy)
      | pat_shape_sum σ τ x y =>
          fun b =>
            match b with
            | true  => fun vs => inl (env.head vs)
            | false => fun vs => inr (env.head vs)
            end
      | pat_shape_unit =>
          fun _ _ => tt
      | pat_shape_enum E =>
          fun v _ => v
      | pat_shape_bvec_split m n x y =>
          fun _ Exy =>
            let (Ex,vy) := env.snocView Exy in
            let (E,vx)  := env.snocView Ex in
            bv.app vx vy
      | pat_shape_bvec_exhaustive m =>
          fun v _ => v
      | pat_shape_tuple p =>
          fun _ vs => envrec.of_env (tuple_pattern_match_env_reverse p vs)
      | pat_shape_record R Δ p =>
          fun _ vs => recordv_fold R (record_pattern_match_env_reverse p vs)
      | pat_shape_union U p =>
          fun '(K; pc) δpc =>
            unionv_fold U (K; newpattern_match_val_reverse (p K) pc δpc)
      end.

    Definition newpattern_match_val_reverse' {σ} (pat : PatternShape σ) :
      { c : PatternCase pat & NamedEnv Val (PatternCaseCtx c) } -> Val σ :=
        fun c => newpattern_match_val_reverse pat (projT1 c) (projT2 c).

    Lemma newpattern_match_val_inverse_right' {σ} (pat : PatternShape σ) :
      forall (c : { pc : PatternCase pat & NamedEnv Val (PatternCaseCtx pc)}),
        newpattern_match_val pat (newpattern_match_val_reverse' pat c) = c.
    Proof.
      induction pat; cbn; intros [pc vs]; try progress cbn.
      - destruct pc; now env.destroy vs.
      - env.destroy vs. reflexivity.
      - destruct pc; now env.destroy vs.
      - destruct pc; now env.destroy vs.
      - destruct pc; now env.destroy vs.
      - destruct pc; now env.destroy vs.
      - now env.destroy vs.
      - destruct pc; env.destroy vs.
        now rewrite bv.appView_app.
      - now env.destroy vs.
      - destruct pc.
        unfold tuple_pattern_match_val.
        rewrite envrec.to_of_env.
        now rewrite tuple_pattern_match_env_inverse_right.
      - destruct pc.
        unfold record_pattern_match_val.
        rewrite recordv_unfold_fold.
        now rewrite record_pattern_match_env_inverse_right.
      - destruct pc as [K pc].
        rewrite unionv_unfold_fold.
        change (newpattern_match_val_reverse _ ?pc ?vs) with
          (newpattern_match_val_reverse' _ (pc;vs)).
        now rewrite H.
    Qed.

    Lemma newpattern_match_val_inverse_right {σ} (pat : PatternShape σ)
      (pc : PatternCase pat) (δpc : NamedEnv Val (PatternCaseCtx pc)) :
      newpattern_match_val pat (newpattern_match_val_reverse pat pc δpc) = (pc; δpc).
    Proof. apply (newpattern_match_val_inverse_right' pat (pc;δpc)). Qed.

    Lemma newpattern_match_val_inverse_left {σ} (pat : PatternShape σ) :
      forall v : Val σ,
        newpattern_match_val_reverse' pat (newpattern_match_val pat v) = v.
    Proof.
      induction pat; cbn; intros v; try progress cbn.
      - reflexivity.
      - reflexivity.
      - destruct v; reflexivity.
      - destruct v; reflexivity.
      - destruct v; reflexivity.
      - destruct v; reflexivity.
      - reflexivity.
      - destruct bv.appView; reflexivity.
      - reflexivity.
      - unfold tuple_pattern_match_val.
        rewrite tuple_pattern_match_env_inverse_left.
        now rewrite envrec.of_to_env.
      - unfold record_pattern_match_val.
        rewrite record_pattern_match_env_inverse_left.
        now rewrite recordv_fold_unfold.
      - destruct unionv_unfold as [K v'] eqn:Heq.
        apply (f_equal (unionv_fold U)) in Heq.
        rewrite unionv_fold_unfold in Heq. subst.
        destruct newpattern_match_val eqn:Heq; cbn.
        change (newpattern_match_val_reverse _ ?pc ?vs) with
          (newpattern_match_val_reverse' _ (pc;vs)).
        now rewrite <- Heq, H.
    Qed.

    Section NewAlternative.
      Context {R : NCtx N Ty -> Type} {Γ : NCtx N Ty}.

      Fixpoint PatternCaseCurried {σ} (pat : PatternShape σ) : Type :=
        match pat with
        | @pat_shape_var x σ => R (Γ ▻ x∷σ)
        | pat_shape_bool => bool -> R Γ
        | pat_shape_list σ0 x y => (R Γ * R (Γ ▻ x∷σ0 ▻ y∷ty.list σ0))%type
        | @pat_shape_prod x y σl σr => R (Γ ▻ x∷σl ▻ y∷σr)
        | pat_shape_sum σ0 τ0 x y => (R (Γ ▻ x∷σ0) * R (Γ ▻ y∷τ0))%type
        | pat_shape_unit => R Γ
        | pat_shape_enum E => enumt E -> R Γ
        | pat_shape_bvec_split m n x y => R (Γ ▻ x∷ty.bvec m ▻ y∷ty.bvec n)
        | pat_shape_bvec_exhaustive m => bv m -> R Γ
        | @pat_shape_tuple _ Δ _ => R (Γ ▻▻ Δ)
        | pat_shape_record _ Δ _ => R (Γ ▻▻ Δ)
        | pat_shape_union U p => forall K : unionk U, PatternCaseCurried (p K)
        end.

      Fixpoint of_pattern_case_curried {σ} (pat : PatternShape σ) {struct pat} :
        PatternCaseCurried pat -> forall pc : PatternCase pat, R (Γ ▻▻ PatternCaseCtx pc) :=
        match pat with
        | pat_shape_var x => fun rhs _ => rhs
        | pat_shape_bool => fun rhs => rhs
        | pat_shape_list σ0 x y => fun '(a,b) pc =>
                                     match pc with true => a | false => b end
        | pat_shape_prod x y => fun rhs _ => rhs
        | pat_shape_sum _ _ x y => fun '(a,b) pc =>
                                     match pc with | true => a | false => b end
        | pat_shape_unit => fun rhs _ => rhs
        | pat_shape_enum E => fun rhs => rhs
        | pat_shape_bvec_split m n x y => fun rhs _ => rhs
        | pat_shape_bvec_exhaustive m => fun rhs => rhs
        | @pat_shape_tuple _ Δ _ => fun rhs _ => rhs
        | pat_shape_record _ Δ _ => fun rhs _ => rhs
        | pat_shape_union U p0 => fun rhs '(existT K pc) =>
                                    of_pattern_case_curried (p0 K) (rhs K) pc
        end.

      Record NewAlternative (σ : Ty) : Type :=
        MkNewAlt
          { newalt_pat : PatternShape σ;
            newalt_rhs : PatternCaseCurried newalt_pat;
          }.

    End NewAlternative.
    #[global] Arguments NewAlternative : clear implicits.
    #[global] Arguments MkNewAlt {R Γ σ} _ & _.
    #[global] Arguments newalt_pat {R Γ σ} _.
    #[global] Arguments newalt_rhs {R Γ σ} _.

  End Patterns.

  Bind Scope pat_scope with TuplePat.
  Bind Scope pat_scope with RecordPat.
  Bind Scope pat_scope with Pattern.

End PatternsOn.
