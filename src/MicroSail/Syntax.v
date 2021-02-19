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

From Coq Require Import
     Bool.Bool
     Classes.Equivalence
     Program.Tactics
     Relations
     Strings.String
     ZArith.ZArith
     micromega.Lia.
From Coq Require
     Vector.

From bbv Require
     Word.

From stdpp Require
     finite.
From Equations Require Import
     Equations Signature.
Require Equations.Prop.DepElim.
Require Import Equations.Prop.EqDec.

From MicroSail Require Export
     Context
     Notation
     Syntax.Types
     Syntax.Values.

Import CtxNotations.
Import EnvNotations.

Local Set Implicit Arguments.
Local Unset Transparent Obligations.
Obligation Tactic := idtac.

Module Type TermKit.

  Declare Module valuekit : ValueKit.
  Module Export VAL := Values valuekit.

  (* Names of expression variables. These represent mutable variables appearing
     in programs. *)
  Parameter Inline 𝑿 : Set. (* input: \MIX *)
  (* For name resolution we rely on decidable equality of expression
     variables. The functions in this module resolve to the closest binding
     of an equal name and fill in the de Bruijn index automatically from
     a successful resolution.
  *)
  Declare Instance 𝑿_eq_dec : EqDec 𝑿.

  (* Names of logical variables. These represent immutable variables
     standing for concrete literals in assertions. *)
  Parameter Inline 𝑺 : Set. (* input: \MIS *)
  Declare Instance 𝑺_eq_dec : EqDec 𝑺.
  (* Punning of program variables with logical variables. *)
  Parameter Inline 𝑿to𝑺 : 𝑿 -> 𝑺.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  (* Names of functions. *)
  Parameter Inline 𝑭 : PCtx -> Ty -> Set.
  Parameter Inline 𝑭𝑿 : PCtx -> Ty -> Set.

  (* Names of registers. *)
  Parameter Inline 𝑹𝑬𝑮 : Ty -> Set.
  Declare Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮).

End TermKit.

Module Terms (Export termkit : TermKit).

  Definition LocalStore (Γ : PCtx) : Set := NamedEnv Lit Γ.
  Bind Scope env_scope with LocalStore.

  Section BinaryOperations.

    Inductive BinOp : Ty -> Ty -> Ty -> Set :=
    | binop_plus              : BinOp ty_int ty_int ty_int
    | binop_times             : BinOp ty_int ty_int ty_int
    | binop_minus             : BinOp ty_int ty_int ty_int
    | binop_eq                : BinOp ty_int ty_int ty_bool
    | binop_le                : BinOp ty_int ty_int ty_bool
    | binop_lt                : BinOp ty_int ty_int ty_bool
    | binop_gt                : BinOp ty_int ty_int ty_bool
    | binop_and               : BinOp ty_bool ty_bool ty_bool
    | binop_or                : BinOp ty_bool ty_bool ty_bool
    | binop_pair {σ1 σ2 : Ty} : BinOp σ1 σ2 (ty_prod σ1 σ2)
    | binop_cons {σ : Ty}     : BinOp σ (ty_list σ) (ty_list σ)
    | binop_bvplus {n}        : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
    | binop_bvmult {n}        : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
    | binop_bvcombine {m n}   : BinOp (ty_bvec m) (ty_bvec n) (ty_bvec (m + n))
    .

    Local Set Transparent Obligations.
    Derive Signature NoConfusion for BinOp.
    Local Unset Transparent Obligations.

    Import Sigma_Notations.

    Definition BinOpTel : Set :=
      Σ i : (Σ σ1 σ2 : Ty, Ty), BinOp i.1 (i.2).1 (i.2).2.

    Definition binoptel_pair (σ1 σ2 : Ty) : BinOpTel :=
      ((σ1, σ2, ty_prod σ1 σ2), binop_pair).
    Definition binoptel_cons (σ : Ty) : BinOpTel :=
      ((σ, ty_list σ, ty_list σ), binop_cons).

    Definition binoptel_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3}
      (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      dec_eq (A := BinOpTel) ((σ1,σ2,σ3),op1) ((τ1,τ2,τ3),op2) :=
      match op1 , op2 with
      | binop_plus  , binop_plus   => left eq_refl
      | binop_times , binop_times  => left eq_refl
      | binop_minus , binop_minus  => left eq_refl
      | binop_eq    , binop_eq     => left eq_refl
      | binop_le    , binop_le     => left eq_refl
      | binop_lt    , binop_lt     => left eq_refl
      | binop_gt    , binop_gt     => left eq_refl
      | binop_and   , binop_and    => left eq_refl
      | binop_or    , binop_or     => left eq_refl
      | @binop_pair σ1 σ2 , @binop_pair τ1 τ2   =>
        f_equal2_dec binoptel_pair noConfusion_inv (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | @binop_cons σ  , @binop_cons τ   =>
        f_equal_dec binoptel_cons noConfusion_inv (eq_dec σ τ)
      | @binop_bvplus m , @binop_bvplus n =>
        f_equal_dec
          (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvplus))
          noConfusion_inv (eq_dec m n)
      | @binop_bvmult m , @binop_bvmult n =>
        f_equal_dec
          (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvmult))
          noConfusion_inv (eq_dec m n)
      | @binop_bvcombine m1 m2 , @binop_bvcombine n1 n2 =>
        f_equal2_dec
          (fun m n => ((ty_bvec m, ty_bvec n, ty_bvec (m+n)), binop_bvcombine))
          noConfusion_inv (eq_dec m1 n1) (eq_dec m2 n2)
      | _           , _            => right noConfusion_inv
      end.

    Inductive OpEq {σ1 σ2 σ3} (op1 : BinOp σ1 σ2 σ3) : forall τ1 τ2 τ3, BinOp τ1 τ2 τ3 -> Prop :=
    | opeq_refl : OpEq op1 op1.
    Derive Signature for OpEq.
    Global Arguments opeq_refl {_ _ _ _}.

    Lemma binop_eqdep_dec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      {OpEq op1 op2} + {~ OpEq op1 op2}.
    Proof.
      destruct (binoptel_eq_dec op1 op2).
      - left. dependent elimination e. constructor.
      - right. intro e. apply n. dependent elimination e. reflexivity.
    Defined.

    Local Set Equations With UIP.
    Global Instance binop_eq_dec {σ1 σ2 σ3} : EqDec (BinOp σ1 σ2 σ3).
    Proof.
      intros x y.
      destruct (binoptel_eq_dec x y) as [p|p].
      - left. dependent elimination p. reflexivity.
      - right. congruence.
    Defined.

  End BinaryOperations.

  Section Expressions.

    Local Unset Elimination Schemes.

    (* Intrinsically well-typed expressions. The context Γ of mutable variables
       contains names 𝑿 and types Ty, but the names are not computationally
       relevant. The underlying representation is still a de Bruijn index based
       one. The names are meant for human consumption and we also provide name
       resolution infrastructure in the NameResolution module to fill in de
       Bruijn indices automatically.

       The de Bruijn indices are wrapped together with a resolution proof in the
       InCtx type class, which currently does not have any global instances. We
       do have local implicit instances like for example in the exp_var
       constructor below and use the type class mechanism to copy these
       locally. *)
    Inductive Exp (Γ : PCtx) : Ty -> Set :=
    | exp_var     (x : 𝑿) (σ : Ty) {xInΓ : x∶σ ∈ Γ} : Exp Γ σ
    | exp_lit     (σ : Ty) : Lit σ -> Exp Γ σ
    | exp_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1) (e2 : Exp Γ σ2) : Exp Γ σ3
    | exp_neg     (e : Exp Γ ty_int) : Exp Γ ty_int
    | exp_not     (e : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_inl     {σ1 σ2 : Ty} : Exp Γ σ1 -> Exp Γ (ty_sum σ1 σ2)
    | exp_inr     {σ1 σ2 : Ty} : Exp Γ σ2 -> Exp Γ (ty_sum σ1 σ2)
    | exp_list    {σ : Ty} (es : list (Exp Γ σ)) : Exp Γ (ty_list σ)
    (* Experimental features *)
    | exp_bvec    {n} (es : Vector.t (Exp Γ ty_bit) n) : Exp Γ (ty_bvec n)
    | exp_tuple   {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Exp Γ (ty_tuple σs)
    | exp_projtup {σs : Ctx Ty} (e : Exp Γ (ty_tuple σs)) (n : nat) {σ : Ty}
                  {p : ctx_nth_is σs n σ} : Exp Γ σ
    | exp_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)) : Exp Γ (ty_union U)
    | exp_record  (R : 𝑹) (es : NamedEnv (Exp Γ) (𝑹𝑭_Ty R)) : Exp Γ (ty_record R).
    (* | exp_projrec {R : 𝑹} (e : Exp Γ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty} *)
    (*               {rfInR : rf∶σ ∈ 𝑹𝑭_Ty R} : Exp Γ σ. *)
    Bind Scope exp_scope with Exp.

    Global Arguments exp_var {_} _ {_ _}.
    Global Arguments exp_lit {_} _ _.
    Global Arguments exp_tuple {_ _} _.
    Global Arguments exp_union {_} _ _.
    Global Arguments exp_record {_} _ _.
    (* Global Arguments exp_projrec {_ _} _ _ {_ _}. *)

    Section ExpElimination.

      Variable (Γ : PCtx).
      Variable (P : forall t, Exp Γ t -> Type).
      Arguments P _ _ : clear implicits.

      Let PL (σ : Ty) : list (Exp Γ σ) -> Type :=
        List.fold_right (fun e es => P _ e * es)%type unit.
      Let PV (n : nat) (es : Vector.t (Exp Γ ty_bit) n) : Type :=
        Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
      Let PE : forall σs, Env (Exp Γ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.
      Let PNE : forall (σs : NCtx 𝑹𝑭 Ty), NamedEnv (Exp Γ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.

      Hypothesis (P_var     : forall (x : 𝑿) (σ : Ty) (xInΓ : x∶σ ∈ Γ), P σ (exp_var x)).
      Hypothesis (P_lit     : forall (σ : Ty) (l : Lit σ), P σ (exp_lit σ l)).
      Hypothesis (P_binop   : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1), P σ1 e1 -> forall e2 : Exp Γ σ2, P σ2 e2 -> P σ3 (exp_binop op e1 e2)).
      Hypothesis (P_neg     : forall e : Exp Γ ty_int, P ty_int e -> P ty_int (exp_neg e)).
      Hypothesis (P_not     : forall e : Exp Γ ty_bool, P ty_bool e -> P ty_bool (exp_not e)).
      Hypothesis (P_inl     : forall (σ1 σ2 : Ty) (e : Exp Γ σ1), P σ1 e -> P (ty_sum σ1 σ2) (exp_inl e)).
      Hypothesis (P_inr     : forall (σ1 σ2 : Ty) (e : Exp Γ σ2), P σ2 e -> P (ty_sum σ1 σ2) (exp_inr e)).
      Hypothesis (P_list    : forall (σ : Ty) (es : list (Exp Γ σ)), PL es -> P (ty_list σ) (exp_list es)).
      Hypothesis (P_bvec    : forall (n : nat) (es : Vector.t (Exp Γ ty_bit) n), PV es -> P (ty_bvec n) (exp_bvec es)).
      Hypothesis (P_tuple   : forall (σs : Ctx Ty) (es : Env (Exp Γ) σs), PE es -> P (ty_tuple σs) (exp_tuple es)).
      Hypothesis (P_projtup : forall (σs : Ctx Ty) (e : Exp Γ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx_nth_is σs n σ), P σ (@exp_projtup _ _ e n _ p)).
      Hypothesis (P_union   : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (exp_union U K e)).
      Hypothesis (P_record  : forall (R : 𝑹) (es : NamedEnv (Exp Γ) (𝑹𝑭_Ty R)), PNE es -> P (ty_record R) (exp_record R es)).
      (* Hypothesis (P_projrec : forall (R : 𝑹) (e : Exp Γ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (exp_projrec e rf)). *)

      Fixpoint Exp_rect {τ : Ty} (e : Exp Γ τ) {struct e} : P τ e :=
        match e with
        | exp_var x                 => ltac:(apply P_var; auto)
        | exp_lit _ l               => ltac:(apply P_lit; auto)
        | exp_binop op e1 e2        => ltac:(apply P_binop; auto)
        | exp_neg e                 => ltac:(apply P_neg; auto)
        | exp_not e                 => ltac:(apply P_not; auto)
        | exp_inl e                 => ltac:(apply P_inl; auto)
        | exp_inr e                 => ltac:(apply P_inr; auto)
        | exp_list es               => ltac:(apply P_list; induction es; cbn; auto using unit)
        | exp_bvec es               => ltac:(apply P_bvec; induction es; cbn; auto using unit)
        | exp_tuple es              => ltac:(apply P_tuple; induction es; cbn; auto using unit)
        | @exp_projtup _ σs e n σ p => ltac:(apply P_projtup; auto)
        | exp_union U K e           => ltac:(apply P_union; auto)
        | exp_record R es           => ltac:(apply P_record; induction es; cbn; auto using unit)
        (* | exp_projrec e rf          => ltac:(apply P_projrec; auto) *)
        end.

    End ExpElimination.

    Definition Exp_rec {Γ} (P : forall σ, Exp Γ σ -> Set) := Exp_rect P.
    Definition Exp_ind {Γ} (P : forall σ, Exp Γ σ -> Prop) := Exp_rect P.

    Import EnvNotations.

    Fixpoint tuple_proj (σs : Ctx Ty) (n : nat) (σ : Ty) :
      Lit (ty_tuple σs) -> ctx_nth_is σs n σ -> Lit σ :=
      match σs with
      | ctx_nil       => fun l (p : ctx_nth_is ctx_nil _ _) =>
                           match p with end
      | ctx_snoc τs τ => match n with
                         | 0   => fun (l : Lit (ty_tuple (ctx_snoc _ _)))
                                      (p : ctx_nth_is _ 0 _) =>
                                    @eq_rect Ty τ Lit (snd l) σ p
                         | S m => fun l p => tuple_proj τs m σ (fst l) p
                         end
      end.

    Definition eval_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Lit σ1 -> Lit σ2 -> Lit σ3 :=
      match op with
      | binop_plus      => Z.add
      | binop_times     => Z.mul
      | binop_minus     => Z.sub
      | binop_eq        => Z.eqb
      | binop_le        => Z.leb
      | binop_lt        => Z.ltb
      | binop_gt        => Z.gtb
      | binop_and       => andb
      | binop_or        => fun v1 v2 => orb v1 v2
      | binop_pair      => pair
      | binop_cons      => cons
      | binop_bvplus    => fun v1 v2 => Word.wplus v1 v2
      | binop_bvmult    => fun v1 v2 => Word.wmult v1 v2
      | binop_bvcombine => fun v1 v2 => Word.combine v1 v2
      end.

    Fixpoint eval {Γ : PCtx} {σ : Ty} (e : Exp Γ σ) (δ : LocalStore Γ) {struct e} : Lit σ :=
      match e in (Exp _ t) return (Lit t) with
      | exp_var x           => δ ‼ x
      | exp_lit _ l         => l
      | exp_binop op e1 e2  => eval_binop op (eval e1 δ) (eval e2 δ)
      | exp_neg e           => Z.opp (eval e δ)
      | exp_not e           => negb (eval e δ)
      | exp_inl e           => inl (eval e δ)
      | exp_inr e           => inr (eval e δ)
      | exp_list es         => List.map (fun e => eval e δ) es
      | exp_bvec es         => Vector.t_rect
                                 _ (fun m (_ : Vector.t (Exp Γ ty_bit) m) => Word.word m)
                                 Word.WO (fun eb m _ (vs : Word.word m) =>
                                            match eval eb δ with
                                            | bitzero => Word.WS false vs
                                            | bitone => Word.WS true vs
                                            end)
                                 _ es
      | exp_tuple es        => Env_rect
                                 (fun σs _ => Lit (ty_tuple σs))
                                 tt
                                 (fun σs _ (vs : Lit (ty_tuple σs)) σ e => (vs, eval e δ))
                                 es
      | @exp_projtup _ σs e n σ p => tuple_proj σs n σ (eval e δ) p
      | exp_union U K e     => 𝑼_fold (existT K (eval e δ))
      | exp_record R es     => 𝑹_fold (Env_rect
                                         (fun σs _ => NamedEnv Lit σs)
                                         env_nil
                                         (fun σs _ vs _ e => env_snoc vs _ (eval e δ)) es)
      (* | exp_projrec e rf    => 𝑹_unfold (eval e δ) ‼ rf *)
      end.

    Definition evals {Γ Δ} (es : NamedEnv (Exp Γ) Δ) (δ : LocalStore Γ) : LocalStore Δ :=
      env_map (fun xτ e => eval e δ) es.

  End Expressions.
  Bind Scope exp_scope with Exp.

  Section Statements.

    Inductive TuplePat {N : Set} : Ctx Ty -> (NCtx N Ty) -> Set :=
    | tuplepat_nil  : TuplePat ctx_nil ctx_nil
    | tuplepat_snoc
        {σs : Ctx Ty} {Δ : NCtx N Ty}
        (pat : TuplePat σs Δ) {σ : Ty} (x : N) :
        TuplePat (ctx_snoc σs σ) (ctx_snoc Δ (x∶σ)).
    Bind Scope pat_scope with TuplePat.

    Inductive RecordPat {N : Set} : NCtx 𝑹𝑭 Ty -> NCtx N Ty -> Set :=
    | recordpat_nil  : RecordPat ctx_nil ctx_nil
    | recordpat_snoc
        {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
        (pat : RecordPat rfs Δ) (rf : 𝑹𝑭) {τ : Ty} (x : N) :
        RecordPat (ctx_snoc rfs (rf∶τ)) (ctx_snoc Δ (x∶τ)).
    Bind Scope pat_scope with RecordPat.

    Inductive Pattern {N : Set} : NCtx N Ty -> Ty -> Set :=
    | pat_var (x : N) {σ : Ty} : Pattern [ x ∶ σ ]%ctx σ
    | pat_unit : Pattern ctx_nil ty_unit
    | pat_pair (x y : N) {σ τ : Ty} : Pattern [ x ∶ σ , y ∶ τ ]%ctx (ty_prod σ τ)
    | pat_tuple {σs Δ} (p : TuplePat σs Δ) : Pattern Δ (ty_tuple σs)
    | pat_record {R Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) : Pattern Δ (ty_record R).

    (* Local Unset Elimination Schemes. *)

    Inductive Stm (Γ : PCtx) (τ : Ty) : Type :=
    | stm_lit           (l : Lit τ)
    | stm_exp           (e : Exp Γ τ)
    | stm_let           (x : 𝑿) (σ : Ty) (s__σ : Stm Γ σ) (s__τ : Stm (Γ ▻ x∶σ) τ)
    | stm_block         (Δ : PCtx) (δ : LocalStore Δ) (s : Stm (Γ ▻▻ Δ) τ)
    | stm_assign        (x : 𝑿) {xInΓ : x∶τ ∈ Γ} (s : Stm Γ τ)
    | stm_call          {Δ : PCtx} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    | stm_call_frame    (Δ : PCtx) (δ : LocalStore Δ) (s : Stm Δ τ)
    | stm_call_external {Δ : PCtx} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    | stm_if            (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
    | stm_seq           {σ : Ty} (s : Stm Γ σ) (k : Stm Γ τ)
    | stm_assertk       (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ)
    | stm_fail          (s : Lit ty_string)
    | stm_match_list
        {σ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ) (xh xt : 𝑿)
        (alt_cons : Stm (Γ ▻ xh∶σ ▻ xt∶ty_list σ) τ)
    | stm_match_sum
        {σinl σinr : Ty} (e : Exp Γ (ty_sum σinl σinr))
        (xinl : 𝑿) (alt_inl : Stm (Γ ▻ xinl∶σinl) τ)
        (xinr : 𝑿) (alt_inr : Stm (Γ ▻ xinr∶σinr) τ)
    | stm_match_pair
        {σ1 σ2 : Ty} (e : Exp Γ (ty_prod σ1 σ2))
        (xl xr : 𝑿) (rhs : Stm (Γ ▻ xl∶σ1 ▻ xr∶σ2) τ)
    | stm_match_enum
        {E : 𝑬} (e : Exp Γ (ty_enum E))
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
    | stm_match_tuple
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) (rhs : Stm (Γ ▻▻ Δ) τ)
    | stm_match_union
        {U : 𝑼} (e : Exp Γ (ty_union U))
        (alt__ctx : forall (K : 𝑼𝑲 U), PCtx)
        (alt__pat : forall (K : 𝑼𝑲 U), Pattern (alt__ctx K) (𝑼𝑲_Ty K))
        (alt__rhs : forall (K : 𝑼𝑲 U), Stm (Γ ▻▻ alt__ctx K) τ)
    | stm_match_record
        {R : 𝑹} {Δ : PCtx} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) (rhs : Stm (Γ ▻▻ Δ) τ)
    | stm_read_register (reg : 𝑹𝑬𝑮 τ)
    | stm_write_register (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ)
    (* EXPERIMENTAL *)
    (* | stm_while  (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) : Stm Γ ty_unit *)
    | stm_bind   {σ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ).

    Section TransparentObligations.

      Local Set Transparent Obligations.
      Derive Signature for Stm.
      Derive NoConfusionHom for Stm.

    End TransparentObligations.

    (* Section StmElimination. *)

    (*   Variable (P : forall (Γ : PCtx) (t : Ty), Stm Γ t -> Type). *)

    (*   Hypothesis (P_lit   : forall (Γ : PCtx) (τ : Ty) (l : Lit τ), P (stm_lit Γ l)). *)
    (*   Hypothesis (P_exp  : forall (Γ : PCtx) (τ : Ty) (e : Exp Γ τ), P (stm_exp e)). *)
    (*   Hypothesis (P_let  : forall (Γ : PCtx) (x : 𝑿) (τ : Ty) (s : Stm Γ τ) (σ : Ty) (k : Stm (Γ ▻ (x ∶ τ)%ctx) σ), P s -> P k -> P (stm_let s k)). *)
    (*   Hypothesis (P_block : forall (Γ Δ : PCtx) (δ : LocalStore Δ) (σ : Ty) (k : Stm (Γ ▻▻ Δ) σ), P k -> P (stm_block Γ δ k)). *)
    (*   Hypothesis (P_assign : forall (Γ : PCtx) (x : 𝑿) (τ : Ty) (xInΓ : (x ∶ τ)%ctx ∈ Γ) (e : Stm Γ τ), P e -> P (stm_assign e)). *)
    (*   Hypothesis (P_call  : forall (Γ Δ : PCtx) (σ : Ty) (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ), P (stm_call f es)). *)
    (*   Hypothesis (P_call_frame  : forall (Γ Δ : PCtx) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ), P s -> P (stm_call_frame Γ δ s)). *)
    (*   Hypothesis (P_call_external  : forall (Γ Δ : PCtx) (σ : Ty) (f : 𝑭𝑿 Δ σ) (es : NamedEnv (Exp Γ) Δ), P (stm_call_external f es)). *)
    (*   Hypothesis (P_if  : forall (Γ : PCtx) (τ : Ty) (e : Exp Γ ty_bool) (s1 : Stm Γ τ) (s2 : Stm Γ τ), P s1 -> P s2 -> P (stm_if e s1 s2)). *)
    (*   Hypothesis (P_seq  : forall (Γ : PCtx) (τ : Ty) (e : Stm Γ τ) (σ : Ty) (k : Stm Γ σ), P e -> P k -> P (stm_seq e k)). *)
    (*   Hypothesis (P_assert  : forall (Γ : PCtx) (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string), P (stm_assert e1 e2)). *)
    (*   Hypothesis (P_fail  : forall (Γ : PCtx) (τ : Ty) (s : Lit ty_string), P (stm_fail Γ τ s)). *)
    (*   Hypothesis (P_match_list : forall (Γ : PCtx) (σ τ : Ty) (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ) (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh ∶ σ)%ctx ▻ (xt ∶ ty_list σ)%ctx) τ), *)
    (*         P alt_nil -> P alt_cons -> P (stm_match_list e alt_nil alt_cons)). *)
    (*   Hypothesis (P_match_sum : forall (Γ : PCtx) (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr)) (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl ∶ σinl)%ctx) τ) (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr ∶ σinr)%ctx) τ), *)
    (*         P alt_inl -> P alt_inr -> P (stm_match_sum e alt_inl alt_inr)). *)
    (*   Hypothesis (P_match_pair : forall (Γ : PCtx) (σ1 σ2 τ : Ty) (e : Exp Γ (ty_prod σ1 σ2)) (xl xr : 𝑿) (rhs : Stm (Γ ▻ (xl ∶ σ1)%ctx ▻ (xr ∶ σ2)%ctx) τ), *)
    (*         P rhs -> P (stm_match_pair e rhs)). *)
    (*   Hypothesis (P_match_enum : forall (Γ : PCtx) (E : 𝑬) (e : Exp Γ (ty_enum E)) (τ : Ty) (alts : 𝑬𝑲 E -> Stm Γ τ), *)
    (*         (forall K : 𝑬𝑲 E, P (alts K)) -> P (stm_match_enum e alts)). *)
    (*   Hypothesis (P_match_tuple : forall (Γ : PCtx) (σs : Ctx Ty) (Δ : PCtx) (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ) (τ : Ty) (rhs : Stm (Γ ▻▻ Δ) τ), *)
    (*         P rhs -> P (stm_match_tuple e p rhs)). *)
    (*   Hypothesis (P_match_union : forall (Γ : PCtx) (U : 𝑼) (e : Exp Γ (ty_union U)) (τ : Ty) (alt__ctx : 𝑼𝑲 U -> PCtx) *)
    (*         (alt__pat : forall K : 𝑼𝑲 U, Pattern (alt__ctx K) (𝑼𝑲_Ty K)) (alt__rhs : forall K : 𝑼𝑲 U, Stm (Γ ▻▻ alt__ctx K) τ), *)
    (*         (forall K : 𝑼𝑲 U, P (alt__rhs K)) -> P (stm_match_union e alt__ctx alt__pat alt__rhs)). *)
    (*   Hypothesis (P_match_record : forall (Γ : PCtx) (R : 𝑹) (Δ : PCtx) (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ) (τ : Ty) (rhs : Stm (Γ ▻▻ Δ) τ), *)
    (*         P rhs -> P (stm_match_record e p rhs)). *)
    (*   Hypothesis (P_read_register : forall (Γ : PCtx) (τ : Ty) (reg : 𝑹𝑬𝑮 τ), *)
    (*         P (stm_read_register Γ reg)). *)
    (*   Hypothesis (P_write_register : forall (Γ : PCtx) (τ : Ty) (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ), *)
    (*         P (stm_write_register reg e)). *)
    (*   Hypothesis (P_bind : forall (Γ : PCtx) (σ τ : Ty) (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ), *)
    (*         P s -> (forall l : Lit σ, P (k l)) -> P (stm_bind s k)). *)

    (*   Fixpoint Stm_rect {Γ : PCtx} {τ : Ty} (s : Stm Γ τ) {struct s} : P s := *)
    (*     match s with *)
    (*     | stm_lit _ _             => ltac:(apply P_lit; auto) *)
    (*     | stm_exp _               => ltac:(apply P_exp; auto) *)
    (*     | stm_let _ _             => ltac:(apply P_let; auto) *)
    (*     | stm_block _ _ _         => ltac:(apply P_block; auto) *)
    (*     | stm_assign _            => ltac:(apply P_assign; auto) *)
    (*     | stm_call _ _            => ltac:(apply P_call; auto) *)
    (*     | stm_call_frame _ _ _    => ltac:(apply P_call_frame; auto) *)
    (*     | stm_call_external _ _   => ltac:(apply P_call_external; auto) *)
    (*     | stm_if _ _ _            => ltac:(apply P_if; auto) *)
    (*     | stm_seq _ _             => ltac:(apply P_seq; auto) *)
    (*     | stm_assert _ _          => ltac:(apply P_assert; auto) *)
    (*     | stm_fail _ _ _          => ltac:(apply P_fail; auto) *)
    (*     | stm_match_list _ _ _    => ltac:(apply P_match_list; auto) *)
    (*     | stm_match_sum _ _ _     => ltac:(apply P_match_sum; auto) *)
    (*     | stm_match_pair _ _      => ltac:(apply P_match_pair; auto) *)
    (*     | stm_match_enum _ _      => ltac:(apply P_match_enum; auto) *)
    (*     | stm_match_tuple _ _ _   => ltac:(apply P_match_tuple; auto) *)
    (*     | stm_match_union _ _ _ _ => ltac:(apply P_match_union; auto) *)
    (*     | stm_match_record _ _ _  => ltac:(apply P_match_record; auto) *)
    (*     | stm_read_register _ _   => ltac:(apply P_read_register; auto) *)
    (*     | stm_write_register _ _  => ltac:(apply P_write_register; auto) *)
    (*     | stm_bind _ _            => ltac:(apply P_bind; auto) *)
    (*     end. *)

    (* End StmElimination. *)

    (* Definition Stm_rec (P : forall Γ σ, Stm Γ σ -> Set) := Stm_rect P. *)
    (* Definition Stm_ind (P : forall Γ σ, Stm Γ σ -> Prop) := Stm_rect P. *)

    Global Arguments stm_lit {Γ} τ l.
    Global Arguments stm_exp {Γ τ} e%exp.
    Global Arguments stm_let {Γ τ} x σ s__σ%exp s__τ%exp.
    Global Arguments stm_block {Γ τ Δ} δ s%exp.
    Global Arguments stm_assign {Γ τ} x {xInΓ} s%exp.
    Global Arguments stm_call {Γ τ Δ} f _%arg.
    Global Arguments stm_call_frame {Γ τ Δ} δ s%exp.
    Global Arguments stm_call_external {Γ τ Δ} f _%arg.
    Global Arguments stm_if {Γ τ} e%exp s1%exp s2%exp.
    Global Arguments stm_seq {Γ τ σ} s%exp k%exp.
    Global Arguments stm_assertk {Γ τ} e1%exp e2%exp k%exp.
    Global Arguments stm_fail {Γ} τ s%string.
    Global Arguments stm_match_list {Γ τ _} _ _ _ _ _.
    Global Arguments stm_match_sum {Γ τ _ _} _ _ _ _ _.
    Global Arguments stm_match_pair {Γ τ _ _} _ _ _ _.
    Global Arguments stm_match_enum {Γ τ} E e%exp alts%exp.
    Global Arguments stm_match_tuple {Γ τ σs Δ} e%exp p%pat rhs%exp.
    Global Arguments stm_match_union {Γ τ} U e {alt__ctx} alt__pat alt__rhs.
    Global Arguments stm_match_record {Γ τ} R {Δ} e%exp p%pat rhs%exp.
    Global Arguments stm_read_register {Γ τ} reg.
    Global Arguments stm_write_register {Γ τ} reg e%exp.

    Record Alternative (Γ : PCtx) (σ τ : Ty) : Set :=
      MkAlt
        { alt_ctx : PCtx;
          alt_pat : Pattern alt_ctx σ;
          alt_rhs : Stm (Γ ▻▻ alt_ctx) τ;
        }.

    Definition stm_match_union_alt {Γ τ} U (e : Exp Γ (ty_union U))
      (alts : forall (K : 𝑼𝑲 U), Alternative Γ (𝑼𝑲_Ty K) τ) : Stm Γ τ :=
      stm_match_union U e
        (fun K => alt_pat (alts K))
        (fun K => alt_rhs (alts K)).

    Definition stm_assert {Γ} (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) : Stm Γ ty_unit :=
      stm_assertk e1 e2 (stm_lit ty_unit tt).

    Global Arguments MkAlt {_ _ _ _} _ _.
    Global Arguments stm_match_union_alt {_ _} _ _ _.
    Global Arguments stm_assert {Γ} e1%exp e2%exp.

  End Statements.

  Bind Scope exp_scope with Stm.
  Bind Scope pat_scope with Pattern.
  Bind Scope pat_scope with TuplePat.
  Bind Scope pat_scope with RecordPat.

  Section PatternMatching.

    Fixpoint tuple_pattern_match {N : Set} {σs : Ctx Ty} {Δ : NCtx N Ty}
             (p : TuplePat σs Δ) {struct p} : Lit (ty_tuple σs) -> NamedEnv Lit Δ :=
      match p with
      | tuplepat_nil => fun _ => env_nil
      | tuplepat_snoc p x =>
        fun lit =>
          env_snoc
            (tuple_pattern_match p (fst lit)) (x∶_)%ctx
            (snd lit)
      end.

    Fixpoint record_pattern_match {N : Set} {V : Ty -> Set} {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} : NamedEnv V rfs -> NamedEnv V Δ :=
      match p with
      | recordpat_nil => fun _ => env_nil
      | recordpat_snoc p rf x =>
        fun E =>
          env_snoc
            (record_pattern_match p (env_tail E)) (x∶_)
            (env_lookup E inctx_zero)
      end.

    Definition pattern_match {N : Set} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      Lit σ -> NamedEnv Lit Δ :=
      match p with
      | pat_var x => fun v => env_snoc env_nil (x∶_) v
      | pat_unit => fun _ => env_nil
      | pat_pair x y => fun '(u , v) => env_snoc (env_snoc env_nil (x∶_) u) (y∶_) v
      | pat_tuple p => tuple_pattern_match p
      | pat_record p => fun r => record_pattern_match p (𝑹_unfold r)
      end.

  End PatternMatching.

  (* Record FunDef (Δ : PCtx) (τ : Ty) : Set := *)
  (*   { fun_body : Stm Δ τ }. *)

  Section NameResolution.

    (* Ideally the following smart constructors would perform name resolution
       and fill in the de Bruijn index and the type of a variable. Unfortunately,
       they critically rely on the order that type-checking is performed. For
       instance in context Γ := (ε ▻ ("x", ty_int)) the expression
       (@exp_smart_var Γ "x" tt) type-checks while the (@exp_smart_var _ "x" tt)
       fails to type-check with error message

         The term "tt" has type "unit" while it is expected
         to have type "IsSome (ctx_resolve ?Γ0 "x")".

       So the variable ?Γ0 has not been unified and blocks the evaluation of
       ctx_resolve. Unfortunately, Coq decides to fail immediately.
     *)
    Definition exp_smart_var {Γ : PCtx} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Exp Γ (fromSome (ctx_resolve Γ x) p) :=
      @exp_var Γ x (fromSome (ctx_resolve Γ x) p) (mk_inctx Γ x p).

    Definition stm_smart_assign {Γ : PCtx} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Stm Γ (fromSome (ctx_resolve Γ x) p) -> Stm Γ (fromSome (ctx_resolve Γ x) p) :=
      @stm_assign Γ (fromSome _ p) x (mk_inctx Γ x p).

    (* Instead we hook mk_inctx directly into the typeclass resolution mechanism.
       Apparently, the unification of Γ is performed before the resolution so
       evaluation of ctx_resolve and mk_inctx is not blocked. This hook is more
       generally defined in MicroSail.Context.
     *)

  End NameResolution.

  Definition SymInstance (Σ : LCtx) : Set := NamedEnv Lit Σ.
  Bind Scope env_scope with SymInstance.

  Section SymbolicTerms.

    Local Unset Elimination Schemes.

    Inductive Term (Σ : LCtx) : Ty -> Set :=
    | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς ∶ σ) Σ} : Term Σ σ
    | term_lit     (σ : Ty) : Lit σ -> Term Σ σ
    | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
    | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
    | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
    | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
    | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
    | term_list    {σ : Ty} (es : list (Term Σ σ)) : Term Σ (ty_list σ)
    (* Experimental features *)
    | term_bvec    {n} (es : Vector.t (Term Σ ty_bit) n) : Term Σ (ty_bvec n)
    | term_tuple   {σs : Ctx Ty} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs)
    | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                   {p : ctx_nth_is σs n σ} : Term Σ σ
    | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
    | term_record  (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R).
    (* | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty} *)
    (*                {rfInR : InCtx (rf ∶ σ) (𝑹𝑭_Ty R)} : Term Σ σ. *)
    Local Set Transparent Obligations.
    Derive NoConfusion Signature for Term.

    Global Arguments term_var {_} _ {_ _}.
    Global Arguments term_lit {_} _ _.
    Global Arguments term_neg {_} _.
    Global Arguments term_not {_} _.
    Global Arguments term_inl {_ _ _} _.
    Global Arguments term_inr {_ _ _} _.
    Global Arguments term_list {_ _} _.
    Global Arguments term_bvec {_ _} _%exp.
    Global Arguments term_tuple {_ _} _%exp.
    Global Arguments term_projtup {_ _} _%exp _ {_ _}.
    Global Arguments term_union {_} _ _.
    Global Arguments term_record {_} _ _.
    (* Global Arguments term_projrec {_ _} _ _ {_ _}. *)

    Definition term_enum {Σ} (E : 𝑬) (k : 𝑬𝑲 E) : Term Σ (ty_enum E) :=
      term_lit (ty_enum E) k.
    Global Arguments term_enum {_} _ _.

    Section Term_rect.

      Variable (Σ : LCtx).
      Variable (P  : forall t : Ty, Term Σ t -> Type).
      Arguments P _ _ : clear implicits.

      Let PL (σ : Ty) : list (Term Σ σ) -> Type :=
        List.fold_right (fun t ts => P _ t * ts)%type unit.
      Let PV (n : nat) (es : Vector.t (Term Σ ty_bit) n) : Type :=
        Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
      Let PE : forall σs, Env (Term Σ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ ts IHts _ t => IHts * P _ t)%type.
      Let PNE : forall (σs : NCtx 𝑹𝑭 Ty), NamedEnv (Term Σ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ ts IHts _ t => IHts * P _ t)%type.

      Hypothesis (P_var        : forall (ς : 𝑺) (σ : Ty) (ςInΣ : (ς∶σ) ∈ Σ), P σ (term_var ς)).
      Hypothesis (P_lit        : forall (σ : Ty) (l : Lit σ), P σ (term_lit σ l)).
      Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
      Hypothesis (P_neg        : forall e : Term Σ ty_int, P ty_int e -> P ty_int (term_neg e)).
      Hypothesis (P_not        : forall e : Term Σ ty_bool, P ty_bool e -> P ty_bool (term_not e)).
      Hypothesis (P_inl        : forall (σ1 σ2 : Ty) (t : Term Σ σ1), P σ1 t -> P (ty_sum σ1 σ2) (term_inl t)).
      Hypothesis (P_inr        : forall (σ1 σ2 : Ty) (t : Term Σ σ2), P σ2 t -> P (ty_sum σ1 σ2) (term_inr t)).
      Hypothesis (P_list       : forall (σ : Ty) (es : list (Term Σ σ)), PL es -> P (ty_list σ) (term_list es)).
      Hypothesis (P_bvec       : forall (n : nat) (es : Vector.t (Term Σ ty_bit) n), PV es -> P (ty_bvec n) (term_bvec es)).
      Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs), PE es -> P (ty_tuple σs) (term_tuple es)).
      Hypothesis (P_projtup    : forall (σs : Ctx Ty) (e : Term Σ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx_nth_is σs n σ), P σ (@term_projtup _ _ e n _ p)).
      Hypothesis (P_union      : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (term_union U K e)).
      Hypothesis (P_record     : forall (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)), PNE es -> P (ty_record R) (term_record R es)).
      (* Hypothesis (P_projrec    : forall (R : 𝑹) (e : Term Σ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (term_projrec e rf)). *)

      Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) : P σ t :=
        match t with
        | @term_var _ ς σ ςInΣ           => ltac:(eapply P_var; eauto)
        | @term_lit _ σ x                => ltac:(eapply P_lit; eauto)
        | term_binop op e1 e2            => ltac:(eapply P_binop; eauto)
        | @term_neg _ e                  => ltac:(eapply P_neg; eauto)
        | @term_not _ e                  => ltac:(eapply P_not; eauto)
        | @term_inl _ σ1 σ2 x            => ltac:(eapply P_inl; eauto)
        | @term_inr _ σ1 σ2 x            => ltac:(eapply P_inr; eauto)
        | @term_bvec _ _ es              => ltac:(apply P_bvec; induction es; cbn; auto using unit)
        | @term_list _ σ es              => ltac:(eapply P_list; induction es; cbn; eauto using unit)
        | @term_tuple _ σs es            => ltac:(eapply P_tuple; induction es; cbn; eauto using unit)
        | @term_projtup _ σs e n σ p     => ltac:(eapply P_projtup; eauto)
        | @term_union _ U K e            => ltac:(eapply P_union; eauto)
        | @term_record _ R es            => ltac:(eapply P_record; induction es; cbn; eauto using unit)
        (* | @term_projrec _ R e rf σ rfInR => ltac:(eapply P_projrec; eauto) *)
        end.

    End Term_rect.

    Definition Term_rec Σ (P : forall σ, Term Σ σ -> Set) := Term_rect P.
    Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := Term_rect P.

    Section Utils.

      Definition term_get_lit {Σ σ} (t : Term Σ σ) : option (Lit σ) :=
        match t with
        | term_lit _ l => Some l
        | _            => None
        end.

      Equations(noeqns) term_get_pair {Σ σ1 σ2} (t : Term Σ (ty_prod σ1 σ2)) :
        option (Term Σ σ1 * Term Σ σ2) :=
        term_get_pair (term_lit _ (t1,t2))          := Some (term_lit _ t1, term_lit _ t2);
        term_get_pair (term_binop binop_pair t1 t2) := Some (t1, t2);
        term_get_pair _ := None.

      Equations(noeqns) term_get_sum {Σ σ1 σ2} (t : Term Σ (ty_sum σ1 σ2)) :
        option (Term Σ σ1 + Term Σ σ2) :=
        term_get_sum (term_lit _ (inl l)) := Some (inl (term_lit _ l));
        term_get_sum (term_lit _ (inr l)) := Some (inr (term_lit _ l));
        term_get_sum (term_inl t)         := Some (inl t);
        term_get_sum (term_inr t)         := Some (inr t);
        term_get_sum _ := None.

      Equations(noeqns) term_get_union {Σ U} (t : Term Σ (ty_union U)) :
        option { K : 𝑼𝑲 U & Term Σ (𝑼𝑲_Ty K) } :=
        term_get_union (term_lit _ l)   :=
          Some (let (K, p) := 𝑼_unfold l in existT K (term_lit _ p));
        term_get_union (term_union K t) := Some (existT K t);
        term_get_union _ := None.

      Equations(noeqns) term_get_record {R Σ} (t : Term Σ (ty_record R)) :
        option (NamedEnv (Term Σ) (𝑹𝑭_Ty R)) :=
        term_get_record (term_lit _ v)        := Some (env_map (fun _ => term_lit _) (𝑹_unfold v));
        term_get_record (@term_record _ R ts) := Some ts;
        term_get_record _ := None.

      (* Equations(noeqns) term_get_tuple {σs Σ} (t : Term Σ (ty_tuple σs)) : *)
      (*   option (Env (Term Σ) σs) := *)
      (*   term_get_tuple (term_lit _ v)       := Some _; *)
      (*   term_get_tuple (@term_tuple _ _ ts) := Some ts; *)
      (*   term_get_tuple _ := None. *)

    End Utils.

    Fixpoint inst_term {Σ : LCtx} (ι : SymInstance Σ) {σ : Ty} (t : Term Σ σ) {struct t} : Lit σ :=
      match t in Term _ σ return Lit σ with
      | @term_var _ x _      => ι ‼ x
      | term_lit _ l         => l
      | term_binop op e1 e2  => eval_binop op (inst_term ι e1) (inst_term ι e2)
      | term_neg e           => Z.opp (inst_term ι e)
      | term_not e           => negb (inst_term ι e)
      | term_inl e           => inl (inst_term ι e)
      | term_inr e           => inr (inst_term ι e)
      | term_list es         => List.map (fun e => inst_term ι e) es
      | term_bvec es         => Vector.t_rect
                                 _ (fun m (_ : Vector.t (Term Σ ty_bit) m) => Word.word m)
                                 Word.WO (fun eb m _ (vs : Word.word m) =>
                                            Word.WS
                                              (match inst_term ι eb with
                                               | bitzero => false
                                               | bitone => true
                                               end) vs)
                                 _ es
      | term_tuple es        => Env_rect
                                  (fun σs _ => Lit (ty_tuple σs))
                                  tt
                                  (fun σs _ (vs : Lit (ty_tuple σs)) σ e => (vs, inst_term ι e))
                                  es
      | @term_projtup _ σs e n σ p => tuple_proj σs n σ (inst_term ι e) p
      | @term_union _ U K e     => 𝑼_fold (existT K (inst_term ι e))
      | @term_record _ R es     => 𝑹_fold (Env_rect
                                             (fun σs _ => NamedEnv Lit σs)
                                             env_nil
                                             (fun σs _ vs _ e => env_snoc vs _ (inst_term ι e)) es)
      (* | @term_projrec _ _ e rf    => 𝑹_unfold (inst_term ι e) ‼ rf *)
      end.

    Section TermEquivalence.

      Context {Σ : LCtx} {σ : Ty}.

      Definition TermEqv (ι : SymInstance Σ) : relation (Term Σ σ) :=
        fun t1 t2 => inst_term ι t1 = inst_term ι t2.

      Global Instance TermEqv_Equiv {ι} : Equivalence (TermEqv ι).
      Proof. split; congruence. Qed.

    End TermEquivalence.

    Section TermEqvB.

      Context {Σ : LCtx}.

      Fixpoint Term_eqvb {σ τ} (t1 : Term Σ σ) (t2 : Term Σ τ) {struct t1} : option bool :=
        match t1 , t2 with
        | @term_var _ _ _ ς1inΣ , @term_var _ _ _ ς2inΣ =>
          if InCtx_eqb ς1inΣ ς2inΣ
          then Some true
          else None
        | term_lit σ l1 , term_lit τ l2 =>
          match eq_dec σ τ with
          | left  p => Some (Lit_eqb τ (eq_rect σ Lit l1 τ p) l2)
          | right _ => Some false
          end
        | term_neg x   , term_neg y   => Term_eqvb x y
        | term_not x   , term_not y   => Term_eqvb x y
        | term_inl x   , term_inl y   => Term_eqvb x y
        | term_inl _   , term_inr _   => Some false
        | term_inr _   , term_inl _   => Some false
        | term_inr x   , term_inr y   => Term_eqvb x y
        | _            , _            => None
        end.

      Local Set Equations With UIP.
      Lemma Term_eqvb_spec {ι σ} (t1 t2 : Term Σ σ) :
        OptionSpec
          (fun b : bool => TermEqv ι t1 t2 <-> is_true b)
          True
          (Term_eqvb t1 t2).
      Proof.
        induction t1; dependent elimination t2; cbn; intros; try (solve [ constructor; auto ]).
        - destruct (InCtx_eqb_spec ςInΣ ςInΣ0); constructor; auto.
          dependent elimination e. apply reflect_iff. constructor. reflexivity.
        - rewrite eq_dec_refl. cbn. constructor. apply reflect_iff, Lit_eqb_spec.
        - specialize (IHt1 e). revert IHt1.
          apply optionspec_monotonic; [ intros ? <- | auto ].
          unfold TermEqv; cbn; lia.
        - specialize (IHt1 e0). revert IHt1.
          apply optionspec_monotonic; [ intros ? <- | auto ].
          unfold TermEqv; cbn. split.
          + now intros ?%ssrbool.negb_inj.
          + congruence.
        - specialize (IHt1 t). revert IHt1.
          apply optionspec_monotonic; [ intros ? <- | auto ].
          unfold TermEqv; cbn. split; congruence.
        - constructor. apply reflect_iff. constructor. discriminate.
        - constructor. apply reflect_iff. constructor. discriminate.
        - specialize (IHt1 t0). revert IHt1.
          apply optionspec_monotonic; [ intros ? <- | auto ].
          unfold TermEqv; cbn. split; congruence.
      Qed.

    End TermEqvB.

    Equations(noind) Term_eqb {Σ} {σ : Ty} (t1 t2 : Term Σ σ) : bool :=
      Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
        InCtx_eqb ς1inΣ ς2inΣ;
      Term_eqb (term_lit _ l1) (term_lit _ l2) := Lit_eqb _ l1 l2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
        with binop_eqdep_dec op1 op2 => {
        Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (left opeq_refl) :=
          Term_eqb x1 x2 && Term_eqb y1 y2;
        Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
      };
      Term_eqb (term_neg x) (term_neg y) := Term_eqb x y;
      Term_eqb (term_not x) (term_not y) := Term_eqb x y;
      Term_eqb (term_inl x) (term_inl y) := Term_eqb x y;
      Term_eqb (term_inr x) (term_inr y) := Term_eqb x y;
      Term_eqb (term_list xs) (term_list ys) := list_beq Term_eqb xs ys;
      Term_eqb (term_bvec xs) (term_bvec ys) := Vector.eqb _ Term_eqb xs ys;
      Term_eqb (term_tuple x) (term_tuple y) :=
         @env_eqb_hom _ (Term Σ) (@Term_eqb _) _ x y;
      Term_eqb (@term_projtup σs x n _ p) (@term_projtup τs y m _ q)
        with eq_dec σs τs => {
        Term_eqb (@term_projtup σs x n _ p) (@term_projtup ?(σs) y m _ q) (left eq_refl) :=
          (n =? m) && Term_eqb x y;
        Term_eqb (@term_projtup _ x n _ p) (@term_projtup _ y m _ q) (right _) := false
        };
      Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
        with 𝑼𝑲_eq_dec k1 k2 => {
        Term_eqb (term_union k1 e1) (term_union k2 e2) (left eq_refl) :=
          Term_eqb e1 e2;
        Term_eqb _ _ (right _) := false
      };
      Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
         @env_eqb_hom _ (fun b => Term Σ (snd b)) (fun b => @Term_eqb _ (snd b)) _ xs ys;
      (* Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2) *)
      (*          with (𝑹_eq_dec r1 r2) => { *)
      (* Term_eqb (@term_projrec r e1 _ _ prf1) (@term_projrec ?(r) e2 _ _ prf2) *)
      (*   (left eq_refl) := InCtx_eqb prf1 prf2 && Term_eqb e1 e2; *)
      (* Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2) *)
      (*   (right _) := false }; *)

      Term_eqb _ _ := false.

    Local Transparent Term_eqb.
    Local Set Equations With UIP.
    Lemma Term_eqb_spec Σ (σ : Ty) (t1 t2 : Term Σ σ) :
      reflect (t1 = t2) (Term_eqb t1 t2).
    Proof.
      induction t1 using Term_rect; cbn [Term_eqb]; dependent elimination t2;
        microsail_solve_eqb_spec.
      - destruct (InCtx_eqb_spec ςInΣ ςInΣ0); constructor.
        + dependent elimination e. reflexivity.
        + intros e. apply n.
          dependent elimination e. reflexivity.
      - match goal with
        | |- context[Lit_eqb _ ?l1 ?l2] => destruct (Lit_eqb_spec _ l1 l2); cbn
        end; microsail_solve_eqb_spec.
      - destruct (binop_eqdep_dec op op0) as [e|ne]; cbn.
        + dependent elimination e; cbn.
          microsail_solve_eqb_spec.
        + constructor; intro e.
          dependent elimination e.
          apply ne; constructor.
      - apply (@ssrbool.iffP (es = es0)).
        + revert es0.
          induction es as [|x xs]; intros [|y ys]; cbn in *; try (constructor; congruence).
          destruct X as [x1 x2].
          specialize (IHxs x2 ys).
          specialize (x1 y).
          microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
      - apply (@ssrbool.iffP (es = es1)).
        + revert es1.
          induction es; intros es1; dependent elimination es1; microsail_solve_eqb_spec.
          destruct X as [x1 x2].
          specialize (IHes x2 t).
          specialize (x1 h0).
          microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
      - apply (@ssrbool.iffP (es = es2)).
        + revert es2.
          induction es; intros es2; dependent elimination es2; microsail_solve_eqb_spec.
          destruct X as [x1 x2].
          specialize (IHes x1 E).
          specialize (x2 db0).
          microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
      - destruct e.
        destruct (Nat.eqb_spec n n1); cbn.
        + subst n1.
          microsail_solve_eqb_spec.
          f_equal; auto.
          apply ctx_nth_is_proof_irrelevance.
        + microsail_solve_eqb_spec.
      - destruct (𝑼𝑲_eq_dec K K0); cbn.
        + destruct e. specialize (IHt1 e4). microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
      - apply (@ssrbool.iffP (es = es3)).
        + revert es3.
          induction es; intros es3; dependent elimination es3; microsail_solve_eqb_spec.
          destruct X as [x1 x2].
          specialize (IHes x1 E).
          specialize (x2 db0).
          microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
      (* - destruct (𝑹_eq_dec R R1); cbn. *)
      (*   + destruct e. specialize (IHt1 e5). apply reflect_iff in IHt1. *)
      (*     assert (EqDec_𝑹𝑭 : EqDec 𝑹𝑭) by admit. *)
      (*     destruct (InCtx_eqb_spec rfInR rfInR0); cbn. *)
      (*     * apply iff_reflect. rewrite <- IHt1. *)
      (*       split. *)
      (*       intros e2. now dependent elimination e2. *)
      (*       intros e2. subst. now dependent elimination e. *)
      (*     * constructor. intros e. apply n. *)
      (*       now dependent elimination e. *)
          (*   + constructor. congruence. *)
    Qed.

  End SymbolicTerms.
  Bind Scope exp_scope with Term.

  Section SymbolicSubstitutions.

    Definition Sub (Σ1 Σ2 : LCtx) : Set :=
      Env (fun b => Term Σ2 (snd b)) Σ1.
    (* Hint Unfold Sub. *)

    Fixpoint sub_term {σ} {Σ1 Σ2 : LCtx} (ζ : Sub Σ1 Σ2) (t : Term Σ1 σ) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                => ζ ‼ ς
      | term_lit σ l              => term_lit σ l
      | term_binop op t1 t2       => term_binop op (sub_term ζ t1) (sub_term ζ t2)
      | term_neg t0               => term_neg (sub_term ζ t0)
      | term_not t0               => term_not (sub_term ζ t0)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term ζ t0)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term ζ t0)
      | @term_list _ σ es         => term_list (List.map (sub_term ζ) es)
      | term_bvec es              => term_bvec (Vector.map (sub_term ζ) es)
      | term_tuple es             => term_tuple (env_map (fun σ => @sub_term σ _ _ ζ) es)
      | @term_projtup _ _ t n σ p => term_projtup (sub_term ζ t) n (p := p)
      | term_union U K t0         => term_union U K (sub_term ζ t0)
      | term_record R es          => term_record R (env_map (fun _ => sub_term ζ) es)
      (* | term_projrec t rf         => term_projrec (sub_term ζ t) rf *)
      end.

    Class Subst (T : LCtx -> Type) : Type :=
      subst : forall {Σ1 Σ2 : LCtx}, Sub Σ1 Σ2 -> T Σ1 -> T Σ2.
    Global Arguments subst {T _ _ _} _ _.

    Global Instance SubstTerm {σ} : Subst (fun Σ => Term Σ σ) :=
      fun Σ1 Σ2 ζ => sub_term ζ.
    Global Instance SubstPair {A B} `{Subst A, Subst B} : Subst (fun Σ => A Σ * B Σ)%type :=
      fun Σ1 Σ2 ζ '(a,b) => (subst ζ a, subst ζ b).
    Global Instance SubstList {A} `{Subst A} : Subst (fun Σ => list (A Σ))%type :=
      fun Σ1 Σ2 ζ => List.map (subst ζ).
    Global Instance SubstEnv {B : Set} {A : Ctx _ -> B -> Set} `{forall b, Subst (fun Σ => A Σ b)} {Δ : Ctx B} :
      Subst (fun Σ => Env (A Σ) Δ) :=
      fun Σ1 Σ2 ζ => env_map (fun b a => subst ζ a).

    Definition sub_id Σ : Sub Σ Σ :=
      @env_tabulate _ (fun b => Term _ (snd b)) _
                    (fun '(ς :: σ) ςIn => @term_var Σ ς σ ςIn).
    Global Arguments sub_id : clear implicits.

    Definition sub_snoc {Σ1 Σ2 : LCtx} (ζ : Sub Σ1 Σ2) b (t : Term Σ2 (snd b)) :
      Sub (Σ1 ▻ b) Σ2 := env_snoc ζ b t.
    Global Arguments sub_snoc {_ _} _ _ _.

    Definition sub_shift {Σ b} (bIn : b ∈ Σ) : Sub (Σ - b) Σ :=
      env_tabulate
        (D := fun b => Term Σ (snd b))
        (fun '(x :: τ) xIn => @term_var Σ x τ (shift_var bIn xIn)).

    Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=
      env_tabulate
        (D := fun b => Term _ (snd b))
        (fun '(ς :: σ) ςIn => @term_var _ ς σ (inctx_succ ςIn)).

    Definition sub_comp {Σ1 Σ2 Σ3} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) : Sub Σ1 Σ3 :=
      subst ζ2 ζ1.

    Definition wk1 {Σ b} `{Subst T} (t : T Σ) : T (Σ ▻ b) :=
      subst sub_wk1 t.

    Definition sub_up1 {Σ1 Σ2} (ζ : Sub Σ1 Σ2) {b} : Sub (Σ1 ▻ b) (Σ2 ▻ b) :=
      let '(ς :: σ) := b in
      env_snoc (sub_comp ζ sub_wk1) (ς :: σ) (@term_var _ ς σ inctx_zero).

    Definition sub_single {Σ x σ} (xIn : (x :: σ) ∈ Σ) (t : Term (Σ - (x :: σ)) σ) : Sub Σ (Σ - (x :: σ)) :=
      @env_tabulate
        _ (fun b => Term _ (snd b)) _
        (fun '(y :: τ) =>
           fun yIn =>
             match occurs_check_var xIn yIn with
             | inl e => eq_rect σ (Term (Σ - (x :: σ))) t τ (f_equal snd e)
             | inr i => term_var y
             end).

    Class SubstLaws (T : LCtx -> Type) `{Subst T} : Type :=
      { subst_sub_id Σ (t : T Σ) :
          subst (sub_id _) t = t;
        subst_sub_comp Σ0 Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) t :
          subst (sub_comp ζ1 ζ2) t = subst ζ2 (subst ζ1 t);
      }.

    Global Arguments SubstLaws T {_}.

    Global Instance SubstLawsTerm {σ} : SubstLaws (fun Σ => Term Σ σ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold sub_id.
          now rewrite env_lookup_tabulate.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply X.
            * apply IHes, X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply X.
            * apply IHes, X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold sub_comp, subst at 1, SubstEnv.
          now rewrite env_lookup_map.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply X.
            * apply IHes, X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply X.
            * apply IHes, X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
      }
    Qed.

    Global Instance SubstLawsPair {A B} `{SubstLaws A, SubstLaws B} : SubstLaws (fun Σ => A Σ * B Σ)%type.
    Proof.
      constructor.
      { intros ? [t1 t2]; cbn.
        f_equal; apply subst_sub_id.
      }
      { intros ? ? ? ? ? [t1 t2]; cbn.
        f_equal; apply subst_sub_comp.
      }
    Qed.

    Global Instance SubstLawsList {A} `{SubstLaws A} : SubstLaws (fun Σ => list (A Σ))%type.
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; auto using subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; auto using subst_sub_comp.
      }
    Qed.

    Global Instance SubstLawsEnv {B : Set} {A : Ctx _ -> B -> Set}
      `{forall b, Subst (fun Σ => A Σ b), forall b, SubstLaws (fun Σ => A Σ b)}
      {Δ : Ctx B} :
      SubstLaws (fun Σ => Env (A Σ) Δ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn.
        - reflexivity.
        - f_equal.
          + apply IHt.
          + apply subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn.
        - reflexivity.
        - f_equal.
          + apply IHt.
          + apply subst_sub_comp.
      }
    Qed.

    Lemma sub_comp_id_left {Σ0 Σ1} (ζ : Sub Σ0 Σ1) :
      sub_comp (sub_id Σ0) ζ = ζ.
    Proof.
      unfold sub_comp, subst, SubstEnv, sub_id.
      apply env_lookup_extensional; cbn.
      intros [] ?.
      now rewrite env_lookup_map, env_lookup_tabulate.
    Qed.

    Lemma sub_comp_id_right {Σ0 Σ1} (ζ : Sub Σ0 Σ1) :
      sub_comp ζ (sub_id Σ1) = ζ.
    Proof.
      apply subst_sub_id.
    Qed.

    Lemma sub_comp_assoc {Σ0 Σ1 Σ2 Σ3} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (ζ3 : Sub Σ2 Σ3) :
      sub_comp (sub_comp ζ1 ζ2) ζ3 = sub_comp ζ1 (sub_comp ζ2 ζ3).
    Proof.
      unfold sub_comp at 1, sub_comp at 2.
      rewrite subst_sub_comp. reflexivity.
    Qed.

    Lemma sub_comp_wk1_tail {Σ0 Σ1 x τ} (ζ : Sub (Σ0 ▻ (x :: τ)) Σ1) :
      sub_comp sub_wk1 ζ = env_tail ζ.
    Proof.
      apply env_lookup_extensional.
      intros [] ?.
      unfold sub_comp, subst, SubstEnv, sub_wk1.
      rewrite env_map_tabulate.
      rewrite env_lookup_tabulate.
      dependent elimination ζ.
      now cbn.
    Qed.

    Lemma sub_comp_wk1_comm {Σ0 Σ1 x τ} (ζ : Sub Σ0 Σ1) :
      sub_comp sub_wk1 (sub_up1 ζ) = sub_comp ζ (sub_wk1 (b:=(x::τ))).
    Proof. now rewrite sub_comp_wk1_tail. Qed.

    Lemma sub_snoc_comp {Σ1 Σ2 Σ3 x τ v} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) :
      sub_comp ζ1 ζ2 ► (x∶τ ↦ v) =
      sub_comp (sub_up1 ζ1) (ζ2 ► (x∶τ ↦ v)).
    Proof.
      unfold sub_up1, sub_comp, subst, SubstEnv; cbn.
      rewrite env_map_map. f_equal.
      apply env_map_ext. intros.
      now rewrite <- subst_sub_comp, sub_comp_wk1_tail.
    Qed.

    Lemma sub_up_comp {Σ0 Σ1 Σ2} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) b :
      sub_up1 (b:=b) (sub_comp ζ1 ζ2) = sub_comp (sub_up1 ζ1) (sub_up1 ζ2).
    Proof.
      destruct b. DepElim.hnf_eq. f_equal.
      now rewrite ?sub_comp_assoc, sub_comp_wk1_comm.
    Qed.

    Lemma sub_comp_shift_single {Σ x σ} (xInΣ : (x :: σ) ∈ Σ) (t : Term (Σ - (x :: σ)) σ) :
          sub_comp (sub_shift xInΣ) (sub_single xInΣ t) = sub_id (Σ - (x :: σ)).
    Proof.
      apply env_lookup_extensional.
      intros [] ?.
      unfold sub_comp, subst, SubstEnv, sub_single, sub_shift, sub_id.
      rewrite env_map_tabulate, ?env_lookup_tabulate.
      cbn.
      rewrite env_lookup_tabulate.
      now rewrite occurs_check_shift_var.
    Qed.


  End SymbolicSubstitutions.

  Section MultiSubs.

    Inductive MultiSub : forall (Σ1 Σ2 : LCtx), Set :=
    | multisub_id {Σ}       : MultiSub Σ Σ
    | multisub_cons {Σ Σ' x σ} (xIn : (x::σ) ∈ Σ) (t : Term (Σ - (x::σ)) σ)
                    (ζ : MultiSub (Σ - (x::σ)) Σ')
                    : MultiSub Σ Σ'.

    Global Arguments multisub_cons {_ _} x {_ _} t ζ.

    Fixpoint sub_multi {Σ1 Σ2} (ζ : MultiSub Σ1 Σ2) : Sub Σ1 Σ2 :=
      match ζ in (MultiSub Σ3 Σ4) return (Sub Σ3 Σ4) with
      | multisub_id         => sub_id _
      | multisub_cons x t ζ => sub_comp (sub_single _ t) (sub_multi ζ)
      end.

  End MultiSubs.

  Section OccursCheck.

    Class OccursCheck (T : LCtx -> Type) : Type :=
      occurs_check : forall {Σ x} (xIn : x ∈ Σ) (t : T Σ), option (T (Σ - x)%ctx).

    Import stdpp.base.

    Fixpoint occurs_check_term {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | @term_var _ ς σ0 ςInΣ =>
        match occurs_check_var xIn ςInΣ with
        | inl e     => None
        | inr ςInΣ' => Some (@term_var _ _ _ ςInΣ')
        end
      | term_lit σ0 l => Some (term_lit σ0 l)
      | term_binop op t1 t2 =>
        t1' ← occurs_check_term xIn t1; t2' ← occurs_check_term xIn t2; Some (term_binop op t1' t2')
      | term_neg t => option_map term_neg (occurs_check_term xIn t)
      | term_not t => option_map term_not (occurs_check_term xIn t)
      | term_inl t => option_map term_inl (occurs_check_term xIn t)
      | term_inr t => option_map term_inr (occurs_check_term xIn t)
      | term_list es => option_map term_list (traverse_list (occurs_check_term xIn) es)
      | term_bvec es => option_map term_bvec (traverse_vector (occurs_check_term xIn) es)
      | term_tuple es => option_map term_tuple (traverse_env (@occurs_check_term _ _ xIn) es)
      | @term_projtup _ σs t n σ p =>
        option_map (fun t' => @term_projtup _ _ t' n _ p) (occurs_check_term xIn t)
      | term_union U K t => option_map (term_union U K) (occurs_check_term xIn t)
      | term_record R es => option_map (term_record R) (traverse_env (fun _ => occurs_check_term xIn) es)
      (* | term_projrec t rf => option_map (fun t' => term_projrec t' rf) (occurs_check_term xIn t) *)
      end.

    Global Instance OccursCheckTerm {σ} : OccursCheck (fun Σ => Term Σ σ) :=
      fun _ _ xIn => occurs_check_term xIn.

    Global Instance OccursCheckList {T : LCtx -> Type} `{OccursCheck T} :
      OccursCheck (fun Σ => list (T Σ)) :=
      fun _ _ xIn => traverse_list (occurs_check xIn).

    Global Instance OccursCheckEnv {I : Set} {T : LCtx -> I -> Set}
           {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
           {Γ : Ctx I} :
      OccursCheck (fun Σ => Env (T Σ) Γ) :=
      fun _ _ xIn => traverse_env (fun i => occurs_check (T := fun Σ => T Σ i) xIn).

    Global Instance OccursCheckSub {Σ} : OccursCheck (Sub Σ) :=
      OccursCheckEnv.

  End OccursCheck.

  Section OccursCheckLaws.

    Class OccursCheckLaws (T : LCtx -> Type) `{Subst T, OccursCheck T} : Prop :=
      { occurs_check_shift {Σ x σ} (xIn : (x::σ) ∈ Σ) (t : T (Σ - (x::σ))%ctx) :
          occurs_check xIn (subst (sub_shift xIn) t) = Some t;
        occurs_check_sound {Σ x} (xIn : x ∈ Σ) (t : T Σ) (t' : T (Σ - x)) :
          occurs_check xIn t = Some t' -> t = subst (sub_shift xIn) t'
      }.

    Global Arguments OccursCheckLaws T {_ _}.

    Lemma option_map_eq_some {A B} (f : A -> B) (o : option A) (a : A) :
      o = Some a ->
      option_map f o = Some (f a).
    Proof. now intros ->. Qed.

    Lemma option_map_eq_some' {A B} (f : A -> B) (o : option A) (b : B) :
      option_map f o = Some b <->
      exists a, o = Some a /\ f a = b.
    Proof.
      split.
      - destruct o as [a|].
        + intros H. apply noConfusion_inv in H. cbn in H.
          exists a. split; congruence.
        + discriminate.
      - now intros (a & -> & <-).
    Qed.

    Lemma option_bind_eq_some {A B} (f : A -> option B) (o : option A) (b : B) :
      (exists a, o = Some a /\ f a = Some b) <->
      option.option_bind A B f o = Some b.
    Proof.
      split.
      - now intros (a & -> & <-).
      - destruct o as [a|]; [ now exists a | discriminate ].
    Qed.

    Local Ltac solve :=
      repeat
        match goal with
        | H: Some _ = Some _ |- _ =>
          apply noConfusion_inv in H; cbn in H; subst
        | H: base.mbind _ _ = Some _ |- _ =>
          apply option_bind_eq_some in H; cbn in H; destruct_conjs; subst
        | H: option_map _ _ = Some _ |- _ =>
          apply option_map_eq_some' in H; cbn in H; destruct_conjs; subst

        | |- match occurs_check_term ?xIn ?t with _ => _ end = _ =>
          destruct (occurs_check_term xIn t); try discriminate
        | |- match occurs_check ?xIn ?t with _ => _ end = _ =>
          destruct (occurs_check xIn t); try discriminate
        | |- base.mbind _ _ = Some _ =>
          apply option_bind_eq_some; eexists; split; [ eassumption; fail | idtac ]
        | |- option_map ?f _ = Some (?f _) =>
          apply option_map_eq_some
        | |- option_map _ _ = Some _ =>
          apply option_map_eq_some'; eexists; split; [ eassumption; fail | idtac ]
        | |- _ =>
          unfold base.mret, option.option_ret in *; cbn in *; try congruence
        end.

    Global Instance OccursCheckLawsTerm {τ} : OccursCheckLaws (fun Σ => Term Σ τ).
    Proof.
      constructor.
      - intros; unfold occurs_check, OccursCheckTerm, subst, SubstTerm.
        induction t; cbn.
        + unfold sub_shift. rewrite env_lookup_tabulate.
          cbv [occurs_check_term base.mbind option.option_bind].
          now rewrite occurs_check_shift_var.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
          induction es; destruct X; cbn.
          * reflexivity.
          * now rewrite e, IHes.
        + solve.
          induction es; destruct X; cbn.
          * reflexivity.
          * now rewrite e, IHes.
        + solve.
          induction es; destruct X; cbn.
          * reflexivity.
          * now rewrite IHes, e0.
        + solve.
        + solve.
        + solve.
          induction es; destruct X; cbn.
          * reflexivity.
          * now rewrite IHes, e0.
        (* + solve. *)
      - unfold occurs_check, OccursCheckTerm, subst, SubstTerm.
        intros ? ? ? t t' H1.
        induction t; cbn in H1.
        + pose proof (occurs_check_var_spec xIn ςInΣ) as H2.
          destruct (occurs_check_var xIn ςInΣ); apply noConfusion_inv in H1;
            cbn in H1; try contradiction; subst; cbn.
          destruct H2 as [H2 H3]. subst. unfold sub_shift.
          now rewrite env_lookup_tabulate.
        + solve.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal. admit.
        + solve. f_equal. admit.
        + solve. f_equal. admit.
        + solve. f_equal. auto.
        + solve. f_equal. auto.
        + solve. f_equal. admit.
        (* + solve. f_equal. auto. *)
    Admitted.

    Global Instance OccursCheckLawsList {T : LCtx -> Type} `{OccursCheckLaws T} :
      OccursCheckLaws (fun Σ => list (T Σ)).
    Proof.
      constructor.
      - intros. induction t; cbn.
        + reflexivity.
        + cbv [base.mbind option.option_bind].
          now rewrite occurs_check_shift, IHt.
      - intros ? ? ? t. induction t; cbn; intros t' Heq.
        + solve.
        + solve. apply occurs_check_sound in H2.
          f_equal; auto.
    Qed.

    Global Instance OccursCheckLawsEnv {I : Set} {T : LCtx -> I -> Set}
           {_ : forall i : I, Subst (fun Σ => T Σ i)}
           {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
           {_ : forall i : I, OccursCheckLaws (fun Σ => T Σ i)}
           {Γ : Ctx I} :
      OccursCheckLaws (fun Σ => Env (T Σ) Γ).
    Proof.
      constructor.
      - intros. induction t.
        + reflexivity.
        + unfold occurs_check, OccursCheckEnv, subst, SubstEnv in IHt.
          cbn. cbv [base.mbind option.option_ret option.option_bind] in *.
          now rewrite IHt, occurs_check_shift.
      - intros ? ? ? E. induction E; cbn; intros E' Heq.
        + solve. reflexivity.
        + solve. apply (occurs_check_sound (T := fun Σ => T Σ _)) in H2.
          f_equal.
          * now apply IHE.
          * auto.
    Qed.

    Global Instance OccursCheckLawsSub {Σ} : OccursCheckLaws (Sub Σ) :=
      OccursCheckLawsEnv.

  End OccursCheckLaws.

  Section Instantiation.

    (* This type class connects a symbolic representation of a type with its
       concrete / semi-concrete counterpart. The method 'inst' will instantiate
       all logic variables in a symbolic value to obtain the concrete value and
       'lift' injects the concrete type into the symbolic one. *)
    Class Inst (T : LCtx -> Type) (A : Type) : Type :=
      { inst {Σ} (ι : SymInstance Σ) (t : T Σ) : A;
        lift {Σ} (a : A) : T Σ;
      }.

    Global Instance instantiate_term {σ} : Inst (fun Σ => Term Σ σ) (Lit σ) :=
      {| inst Σ ι t := inst_term ι t;
         lift Σ l   := term_lit σ l;
      |}.

    Global Instance instantiate_list {T : LCtx -> Set} {A : Set} `{Inst T A} :
      Inst (fun Σ => list (T Σ)) (list A) :=
      {| inst Σ ι := List.map (inst ι);
         lift Σ   := List.map lift;
      |}.

    Global Instance instantiate_env {T : Set} {S : LCtx -> T -> Set}
           {A : T -> Set} {_ : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
           {Γ : Ctx T} :
      Inst (fun Σ => Env (S Σ) Γ) (Env A Γ) :=
      {| inst Σ ι := env_map (fun (b : T) (s : S Σ b) => inst ι s);
         lift Σ   := env_map (fun (b : T) (a : A b) => lift a)
      |}.

    Global Instance instantiate_sub {Σ} : Inst (Sub Σ) (SymInstance Σ) :=
      instantiate_env.

    Class InstLaws (T : LCtx -> Type) (A : Type) `{SubstLaws T, Inst T A} : Prop :=
      { inst_lift {Σ} (ι : SymInstance Σ) (a : A) :
          inst ι (lift a) = a;
        inst_subst {Σ Σ'} (ζ : Sub Σ Σ') (ι : SymInstance Σ') (t : T Σ) :
          inst ι (subst ζ t) = inst (inst ι ζ) t
      }.

    Global Arguments InstLaws T A {_ _ _}.

    Global Instance instantiatelaws_term {σ} : InstLaws (fun Σ => Term Σ σ) (Lit σ).
    Proof.
      constructor.
      { reflexivity. }
      { induction t; cbn; try (f_equal; auto; fail).
        - now rewrite env_lookup_map.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply X.
            * apply IHes, X.
        - induction es; cbn in *.
          + reflexivity.
          + change (sub_term ζ h) with (subst ζ h).
            f_equal.
            * now destruct X as [->].
            * apply IHes, X.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
        - f_equal.
          f_equal.
          apply IHt.
        - f_equal.
          induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
        (* - f_equal. *)
        (*   f_equal. *)
        (*   apply IHt. *)
      }
    Qed.

    Global Instance instantiatelaws_list {T : LCtx -> Set} {A : Set} `{InstLaws T A} :
      InstLaws (fun Σ => list (T Σ)) (list A).
    Proof.
      constructor.
      { intros; cbn.
        rewrite List.map_map, <- List.map_id.
        apply List.map_ext, inst_lift.
      }
      { intros ? ? ζ ι xs; cbn.
        unfold subst, SubstList.
        rewrite List.map_map.
        apply List.map_ext, inst_subst.
      }
    Qed.

    Global Instance instantiatelaws_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
           {_ : forall τ : T, Subst (fun Σ => S Σ τ)}
           {_ : forall τ : T, SubstLaws (fun Σ => S Σ τ)}
           {_ : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
           {_ : forall τ : T, InstLaws (fun Σ => S Σ τ) (A τ)}
           {Γ : Ctx T} :
      InstLaws (fun Σ => Env (S Σ) Γ) (Env A Γ).
    Proof.
      constructor.
      { intros; cbn.
        rewrite env_map_map.
        apply env_map_id_eq.
        intros; apply inst_lift.
      }
      { intros ? ? ζ ι E; cbn.
        unfold subst, SubstEnv.
        rewrite env_map_map.
        apply env_map_ext.
        intros b s.
        now rewrite inst_subst.
      }
    Qed.

    Global Instance instantiatelaws_sub {Σ} : InstLaws (Sub Σ) (SymInstance Σ).
    Proof. apply instantiatelaws_env. Qed.

    Lemma inst_sub_wk1 {Σ ς τ v} (ι : SymInstance Σ) :
      inst (ι ► (ς∶τ ↦ v)) sub_wk1 = ι.
    Proof.
      apply env_lookup_extensional.
      intros [x σ] ?; unfold sub_wk1; cbn.
      now rewrite env_map_tabulate, env_lookup_tabulate.
    Qed.
    
    Lemma inst_sub_id {Σ} (ι : SymInstance Σ) :
      inst ι (sub_id Σ) = ι.
    Proof.
      apply env_lookup_extensional.
      intros [x τ] ?; unfold sub_id; cbn.
      now rewrite env_map_tabulate, env_lookup_tabulate.
    Qed.

  End Instantiation.

  Section SymbolicLocalStore.

    Definition SymbolicLocalStore (Γ : PCtx) (Σ : LCtx) : Type :=
      NamedEnv (Term Σ) Γ.

    Global Program Instance inst_localstore {Γ} : Inst (SymbolicLocalStore Γ) (LocalStore Γ) :=
      instantiate_env.

    Global Instance instlaws_localstore {Γ} : InstLaws (SymbolicLocalStore Γ) (LocalStore Γ).
    Proof. apply instantiatelaws_env. Qed.

  End SymbolicLocalStore.
  Bind Scope env_scope with SymbolicLocalStore.

  Section Contracts.

    Definition Pred (A : Type) : Type := A -> Prop.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _   => True
      | stm_fail _ _ => True
      | _ => False
      end.

    Definition ResultOrFail {Γ σ} (s : Stm Γ σ) :
      forall (POST : Lit σ -> Prop), Prop :=
      match s with
      | stm_lit _ v => fun POST => POST v
      | stm_fail _ _ => fun _ => True
      | _ => fun _ => False
      end.

    Lemma result_or_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> Prop) :
      ResultOrFail s POST -> (exists msg, s = stm_fail _ msg)
                          \/ (exists v, s = stm_lit _ v /\ POST v).
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

    (* This predicate encodes that the statement s is a finished computation and
       that the result is not a failure. This is a computational version that is
       better suited for the goal and the inversion below is better suited for
       a hypothesis. *)
    Definition ResultNoFail {Γ σ} (s : Stm Γ σ) :
      forall (POST : Lit σ -> Prop), Prop :=
      match s with
      | stm_lit _ v => fun POST => POST v
      | _ => fun _ => False
      end.

    Lemma result_no_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> Prop) :
      ResultNoFail s POST -> exists v, s = stm_lit _ v /\ POST v.
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

  End Contracts.

  Section GenericRegStore.

    Definition GenericRegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Lit σ.

    Definition generic_write_register (γ : GenericRegStore) {σ} (r : 𝑹𝑬𝑮 σ)
      (v : Lit σ) : GenericRegStore :=
      fun τ r' =>
        match eq_dec_het r r' with
        | left eqt => eq_rect σ Lit v τ (f_equal projT1 eqt)
        | right _ => γ τ r'
        end.

    Definition generic_read_register (γ : GenericRegStore) {σ} (r : 𝑹𝑬𝑮 σ) :
      Lit σ := γ _ r.

    Lemma generic_read_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
      generic_read_register (generic_write_register γ r v) r = v.
    Proof.
      unfold generic_read_register, generic_write_register.
      unfold eq_dec_het. now rewrite eq_dec_refl.
    Qed.

    Lemma generic_read_write_distinct γ {σ τ} (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ) (v : Lit σ):
      existT _ r <> existT _ k ->
      generic_read_register (generic_write_register γ r v) k = generic_read_register γ k.
    Proof.
      intros ?; unfold generic_read_register, generic_write_register.
      destruct (eq_dec_het r k).
      - congruence.
      - reflexivity.
    Qed.

    Lemma generic_write_read γ {σ} (r : 𝑹𝑬𝑮 σ) :
      forall τ (r' : 𝑹𝑬𝑮 τ),
        generic_write_register γ r (generic_read_register γ r) r' = γ τ r'.
    Proof.
      intros ? ?.
      unfold generic_write_register, generic_read_register.
      destruct (eq_dec_het r r') as [e|].
      - now dependent elimination e.
      - reflexivity.
    Qed.

    Lemma generic_write_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ) :
      forall τ (r' : 𝑹𝑬𝑮 τ),
        generic_write_register (generic_write_register γ r v1) r v2 r' =
        generic_write_register γ r v2 r'.
    Proof.
      intros ? ?.
      unfold generic_write_register, generic_read_register.
      destruct (eq_dec_het r r'); reflexivity.
    Qed.

  End GenericRegStore.

  Notation lit_int l := (@exp_lit _ ty_int l%Z).
  Notation lit_bool l := (@exp_lit _ ty_bool l).
  Notation lit_true   := (@exp_lit _ ty_bool true).
  Notation lit_false  := (@exp_lit _ ty_bool false).
  Notation lit_string s := (@exp_lit _ ty_string s%string).
  Notation "e1 && e2" := (exp_binop binop_and e1 e2) : exp_scope.
  Notation "e1 || e2" := (exp_binop binop_or e1 e2) : exp_scope.
  Notation "e1 + e2" := (exp_binop binop_plus e1 e2) : exp_scope.
  Notation "e1 * e2" := (exp_binop binop_times e1 e2) : exp_scope.
  Notation "e1 - e2" := (exp_binop binop_minus e1 e2) : exp_scope.
  Notation "e1 < e2" := (exp_binop binop_lt e1 e2) : exp_scope.
  Notation "e1 > e2" := (exp_binop binop_gt e1 e2) : exp_scope.
  Notation "e1 <= e2" := (exp_binop binop_le e1 e2) : exp_scope.
  Notation "e1 = e2" := (exp_binop binop_eq e1 e2) : exp_scope.
  Notation "- e" := (exp_neg e) : exp_scope.
  (* Notation "e ․ f" := (* Using Unicode Character “․” (U+2024) *) *)
  (*     (@exp_projrec _ _ e f%string _ _) *)
  (*       (at level 9, no associativity, format *)
  (*        "e ․ f") : exp_scope. *)

  Notation "[ x , .. , z ]" :=
    (tuplepat_snoc .. (tuplepat_snoc tuplepat_nil x) .. z) (at level 0) : pat_scope.
  Notation "[ x , .. , z ]" :=
    (env_snoc .. (env_snoc env_nil (_ :: _) x) .. (_ :: _) z) (at level 0, only parsing) : arg_scope.

  Notation "'if:' e 'then' s1 'else' s2" := (stm_if e%exp s1%exp s2%exp)
    (at level 99, right associativity, format
     "'[hv' 'if:'  e  '/' '[' 'then'  s1  ']' '/' '[' 'else'  s2 ']' ']'"
    ) : exp_scope.

  Notation "'let:' x := s1 'in' s2" := (stm_let x _ s1%exp s2%exp)
    (at level 100, right associativity, x at level 30, s1 at next level, format
     "'let:'  x  :=  s1  'in'  '/' s2"
    ) : exp_scope.
  Notation "'let:' x ∶ τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 100, right associativity, x at level 30, τ at next level, s1 at next level, format
     "'let:'  x  ∶  τ  :=  s1  'in'  '/' s2"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  | alt2%exp => rhs2%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  | alt6 => rhs6%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' 'end' ']'"
    ) : exp_scope.

  (* Notation "'match:' e 'in' U 'with' | alt1 x1 => rhs1 | alt2 x2 => rhs2 'end'" := *)
  (*   (@stm_match_union _ U e _ *)
  (*     (fun K => match K with *)
  (*               | alt1%exp => x1 *)
  (*               | alt2%exp => x2 *)
  (*               end) *)
  (*     (fun K => match K return Stm _ _ with *)
  (*               | alt1%exp => rhs1%exp *)
  (*               | alt2%exp => rhs2%exp *)
  (*               end) *)
  (*   ) *)
  (*   (at level 100, alt1 pattern, alt2 pattern, format *)
  (*    "'[hv' 'match:'  e  'in'  U  'with'  '/' |  alt1  x1  =>  rhs1  '/' |  alt2  x2  =>  rhs2  '/' 'end' ']'" *)
  (*     ) : exp_scope. *)

  Notation "'match:' e 'with' | 'inl' p1 => rhs1 | 'inr' p2 => rhs2 'end'" :=
    (stm_match_sum e p1%string rhs1 p2%string rhs2) (at level 100, only parsing) : exp_scope.

  Notation "'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' | '(' fst ',' snd ')' => rhs 'end'" :=
    (@stm_match_pair _ σ1 σ2 _ e fst%string snd%string rhs)
    (at level 100, fst pattern, snd pattern, format
     "'[hv' 'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' '/' | '(' fst ',' snd ')' => rhs '/' 'end' ']'"
    ) : exp_scope.

  Notation "'call' f a1 .. an" :=
    (stm_call f (env_snoc .. (env_snoc env_nil (_ :: _) a1%exp) .. (_ :: _) an%exp))
    (at level 10, f global, a1, an at level 9) : exp_scope.
  Notation "'callex' f a1 .. an" :=
    (stm_call_external f (env_snoc .. (env_snoc env_nil (_ :: _) a1%exp) .. (_ :: _) an%exp))
    (at level 10, f global, a1, an at level 9) : exp_scope.

  Notation "'call' f" :=
    (stm_call f env_nil)
    (at level 10, f global) : exp_scope.
  Notation "'callex' f" :=
    (stm_call_external f env_nil)
    (at level 10, f global) : exp_scope.

  Notation "s1 ;; s2" := (stm_seq s1 s2) : exp_scope.
  Notation "x <- s" := (stm_assign x s)
    (at level 80, s at next level) : exp_scope.
  Notation "'fail' s" := (stm_fail _ s)
    (at level 10, no associativity) : exp_scope.

End Terms.

(******************************************************************************)

Module Type ProgramKit (termkit : TermKit).

  Module Export TM := Terms termkit.

  (* We choose to make [RegStore] a parameter so the users of the module would be able to
     instantiate it with their own data structure and [read_regsiter]/[write_register]
     functions *)
  Parameter RegStore : Type.
  (* Definition RegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Lit σ. *)
  Parameter read_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ), Lit σ.
  Parameter write_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ), RegStore.

  Parameter read_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Lit σ),
            read_register (write_register γ r v) r = v.

  Parameter read_write_distinct :
    forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ) (v__σ : Lit σ),
      existT _ r__σ <> existT _ r__τ ->
      read_register (write_register γ r__σ v__σ) r__τ = read_register γ r__τ.

  (* Parameter write_read : *)
  (*   forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ), *)
  (*     read_register (write_register γ r (read_register γ r)) r__τ = *)
  (*     read_register γ r__τ. *)

  (* Parameter write_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ), *)
  (*     write_register (write_register γ r v1) r v2 = write_register γ r v2. *)

  (* Memory model *)
  Parameter Memory : Type.
  (* Step relation for calling an external function. The complete function call
     is done in one step. The result of an external call is either a failure
     with an error message msg (res = inl msg) or a successful computation with
     a result value v (res = inr v).
   *)
  Parameter ExternalCall :
    forall
      {Δ σ} (f : 𝑭𝑿 Δ σ)
      (args : LocalStore Δ)
      (res  : string + Lit σ)
      (γ γ' : RegStore)
      (μ μ' : Memory), Prop.
  Parameter ExternalProgress :
    forall {Δ σ} (f : 𝑭𝑿 Δ σ) (args : LocalStore Δ) γ μ,
    exists γ' μ' res, ExternalCall f args res γ γ' μ μ'.

  (* Bind Scope env_scope with Memory. *)
  (* Parameter read_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹), Lit ty_int. *)
  (* Parameter write_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Lit ty_int), Memory. *)

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), Stm Δ τ.

End ProgramKit.
