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
     Lists.List
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     Arith.PeanoNat
     ZArith.ZArith.

From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Outcome
     Syntax.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.

Module Type SymbolicTermKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit).
  Module TM := Terms typekit termkit.
  Export TM.
       (* (Import progkit : ProgramKit typekit termkit). *)

  Parameter Inline 𝑺 : Set. (* input: \MIS *)
  Parameter Inline 𝑺_eq_dec : forall (s1 s2 : 𝑺), {s1=s2}+{~s1=s2}.
  Parameter Inline 𝑿to𝑺 : 𝑿 -> 𝑺.

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Parameter Inline 𝑷_eq_dec : forall (p : 𝑷) (q : 𝑷), {p = q}+{~ p = q}.
End SymbolicTermKit.

Module SymbolicTerms
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (symtermkit : SymbolicTermKit typekit termkit).

  Export symtermkit.

  Import CtxNotations.
  Import EnvNotations.
  Import ListNotations.

  Local Unset Elimination Schemes.
  Inductive Term (Σ : Ctx (𝑺 * Ty)) : Ty -> Type :=
  | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς , σ) Σ} : Term Σ σ
  | term_lit     (σ : Ty) : Lit σ -> Term Σ σ
  | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
  | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
  | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
  | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
  | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
  | term_list    {σ : Ty} (es : list (Term Σ σ)) : Term Σ (ty_list σ)
  | term_nil     {σ : Ty} : Term Σ (ty_list σ)
  (* Experimental features *)
  | term_tuple   {σs : Ctx Ty} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs)
  | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                 {p : ctx_nth_is σs n σ} : Term Σ σ
  | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
  | term_record  (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R)
  | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Term Σ σ.
  (* | term_builtin {σ τ : Ty} (f : Lit σ -> Lit τ) (e : Term Σ σ) : Term Σ τ. *)
  Bind Scope exp_scope with Term.
  Derive Signature for Term.
  Local Set Elimination Schemes.

  Arguments term_var {_} _ _ {_}.

  Section Term_rect.

    Variable (Σ : Ctx (𝑺 * Ty)).
    Variable (P  : forall t : Ty, Term Σ t -> Type).
    Arguments P _ _ : clear implicits.

    Fixpoint PL (σ : Ty) (ts : list (Term Σ σ)) : Type :=
      match ts with
      | [] => unit
      | t :: ts => P σ t * PL ts
      end.
    Fixpoint PE (σs : Ctx Ty) (ts : Env (Term Σ) σs) : Type :=
      match ts with
      | env_nil => unit
      | env_snoc ts _ t => PE ts * P _ t
      end.
    Fixpoint PE' (σs : Ctx (𝑹𝑭 * Ty)) (ts : NamedEnv (Term Σ) σs) : Type :=
      match ts with
      | env_nil => unit
      | env_snoc ts b t => PE' ts * P (snd b) t
      end.

    Hypothesis (P_var        : forall (ς : 𝑺) (σ : Ty) (ςInΣ : (ς ∶ σ)%ctx ∈ Σ), P σ (term_var ς σ)).
    Hypothesis (P_lit        : forall (σ : Ty) (l : Lit σ), P σ (term_lit Σ σ l)).
    Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
    Hypothesis (P_neg        : forall e : Term Σ ty_int, P ty_int e -> P ty_int (term_neg e)).
    Hypothesis (P_not        : forall e : Term Σ ty_bool, P ty_bool e -> P ty_bool (term_not e)).
    Hypothesis (P_inl        : forall (σ1 σ2 : Ty) (t : Term Σ σ1), P σ1 t -> P (ty_sum σ1 σ2) (term_inl t)).
    Hypothesis (P_inr        : forall (σ1 σ2 : Ty) (t : Term Σ σ2), P σ2 t -> P (ty_sum σ1 σ2) (term_inr t)).
    Hypothesis (P_list       : forall (σ : Ty) (es : list (Term Σ σ)), PL es -> P (ty_list σ) (term_list es)).
    Hypothesis (P_nil        : forall σ : Ty, P (ty_list σ) (term_nil Σ)).
    Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs), PE es -> P (ty_tuple σs) (term_tuple es)).
    Hypothesis (P_projtup    : forall (σs : Ctx Ty) (e : Term Σ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx_nth_is σs n σ), P σ (@term_projtup _ _ e n _ p)).
    Hypothesis (P_union      : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (term_union e)).
    Hypothesis (P_record     : forall (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)), PE' es -> P (ty_record R) (term_record es)).
    Hypothesis (P_projrec    : forall (R : 𝑹) (e : Term Σ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (term_projrec e)).

    Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) : P σ t :=
      match t with
      | @term_var _ ς σ ςInΣ           => ltac:(eapply P_var; eauto)
      | @term_lit _ σ x                => ltac:(eapply P_lit; eauto)
      | term_binop op e1 e2            => ltac:(eapply P_binop; eauto)
      | @term_neg _ e                  => ltac:(eapply P_neg; eauto)
      | @term_not _ e                  => ltac:(eapply P_not; eauto)
      | @term_inl _ σ1 σ2 x            => ltac:(eapply P_inl; eauto)
      | @term_inr _ σ1 σ2 x            => ltac:(eapply P_inr; eauto)
      | @term_list _ σ es              => ltac:(eapply P_list; induction es; cbn; eauto using unit)
      | @term_nil _ σ                  => ltac:(eapply P_nil; eauto)
      | @term_tuple _ σs es            => ltac:(eapply P_tuple; induction es; cbn; eauto using unit)
      | @term_projtup _ σs e n σ p     => ltac:(eapply P_projtup; eauto)
      | @term_union _ U K e            => ltac:(eapply P_union; eauto)
      | @term_record _ R es            => ltac:(eapply P_record; induction es; cbn; eauto using unit)
      | @term_projrec _ R e rf σ rfInR => ltac:(eapply P_projrec; eauto)
      end.

  End Term_rect.

  Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := Term_rect P.

  (* Two proofs of context containment are equal of the deBruijn indices are equal *)
  Definition InCtx_eqb {Σ} {ς1 ς2 : 𝑺} {σ : Ty}
             (ς1inΣ : InCtx (ς1, σ) Σ)
             (ς2inΣ : InCtx (ς2, σ) Σ) : bool :=
    Nat.eqb (@inctx_at _ _ _ ς1inΣ) (@inctx_at _ _ _ ς2inΣ).

  Definition binop_eqb {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) : bool :=
    match op1 , op2 with
    | binop_plus  , binop_plus   => true
    | binop_times , binop_times  => true
    | binop_minus , binop_minus  => true
    | binop_eq    , binop_eq     => true
    | binop_le    , binop_le     => true
    | binop_lt    , binop_lt     => true
    | binop_gt    , binop_gt     => true
    | binop_and   , binop_and    => true
    | binop_or    , binop_or     => true
    | binop_pair  , binop_pair   => if Ty_eq_dec σ3 τ3 then true else false
    | binop_cons  , binop_cons   => if Ty_eq_dec σ3 τ3 then true else false
    | _           , _            => false
    end.

  Inductive OpEq {σ1 σ2 σ3} (op1 : BinOp σ1 σ2 σ3) : forall τ1 τ2 τ3, BinOp τ1 τ2 τ3 -> Prop :=
  | opeq_refl : OpEq op1 op1.
  Derive Signature for OpEq.

  Arguments opeq_refl {_ _ _ _}.

  Lemma binop_eqb_spec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
    reflect (OpEq op1 op2) (binop_eqb op1 op2).
  Proof.
    destruct op1, op2; cbn;
      try (destruct Ty_eq_dec);
      try match goal with
          | H: ty_prod _ _ = ty_prod _ _ |- _ => inversion H; subst; clear H
          | H: ty_list _   = ty_list _   |- _ => inversion H; subst; clear H
          end;
      first
        [ constructor; constructor
        | constructor;
          let H := fresh in
          intro H;
          dependent destruction H;
          congruence
        ].
  Defined.

  Lemma binop_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
    {OpEq op1 op2} + {~ OpEq op1 op2}.
  Proof.
    destruct (binop_eqb_spec op1 op2).
    - left; auto.
    - right; auto.
  Defined.

  Equations(noeqns) Term_eqb {Σ} {σ : Ty} (t1 t2 : Term Σ σ) : bool :=
    Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
      InCtx_eqb ς1inΣ ς2inΣ;
    Term_eqb (term_lit _ l1) (term_lit _ l2) := Lit_eqb _ l1 l2;
    Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
      with binop_eq_dec op1 op2 => {
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (left opeq_refl) :=
        Term_eqb x1 x2 && Term_eqb y1 y2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
    };
    Term_eqb (term_neg x) (term_neg y) := Term_eqb x y;
    Term_eqb (term_not x) (term_not y) := Term_eqb x y;
    Term_eqb (term_inl x) (term_inl y) := Term_eqb x y;
    Term_eqb (term_inr x) (term_inr y) := Term_eqb x y;
    Term_eqb (term_list xs) (term_list ys) := list_beq Term_eqb xs ys;
    Term_eqb (@term_nil _) (@term_nil _) := true;
    Term_eqb (term_tuple x) (term_tuple y) :=
       @env_beq _ (Term Σ) (@Term_eqb _) _ x y;
    Term_eqb (@term_projtup σs x n _ p) (@term_projtup τs y m _ q)
      with Ctx_eq_dec Ty_eq_dec σs τs => {
      Term_eqb (@term_projtup σs x n _ p) (@term_projtup ?(σs) y m _ q) (left eq_refl) :=
        (n =? m) && Term_eqb x y;
      Term_eqb (@term_projtup _ x n _ p) (@term_projtup _ y m _ q) (right _) := false
      };
    Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
      with 𝑼𝑲_eq_dec k1 k2 => {
      Term_eqb (term_union e1) (term_union e2) (left eq_refl) :=
        Term_eqb e1 e2;
      Term_eqb _ _ (right _) := false
    };
    Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
       @env_beq _ (fun b => Term Σ (snd b)) (fun b => @Term_eqb _ (snd b)) _ xs ys;
    Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2)
             with (𝑹_eq_dec r1 r2) => {
    Term_eqb (@term_projrec r e1 _ _ prf1) (@term_projrec ?(r) e2 _ _ prf2)
      (left eq_refl) := (@inctx_at _ _ _ prf1 =? @inctx_at _ _ _ prf2) && Term_eqb e1 e2;
    Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2)
      (right _) := false };

    Term_eqb _ _ := false.

  Global Arguments term_var {_} _ {_ _}.
  Global Arguments term_tuple {_ _} _%exp.
  Global Arguments term_union {_} _ _.
  Global Arguments term_record {_} _ _.
  Global Arguments term_projrec {_ _} _ _ {_ _}.

  Definition Sub (Σ1 Σ2 : Ctx (𝑺 * Ty)) : Type :=
    forall b, InCtx b Σ1 -> Term Σ2 (snd b).
  (* Hint Unfold Sub. *)

  Section WithSub.
    Context {Σ1 Σ2 : Ctx (𝑺 * Ty)}.
    Variable (ζ : Sub Σ1 Σ2).

    Fixpoint sub_term {σ} (t : Term Σ1 σ) {struct t} : Term Σ2 σ :=
      match t in (Term _ t0) return (Term Σ2 t0) with
      | @term_var _ ς σ0 ςInΣ     => ζ ςInΣ
      | term_lit _ σ0 l           => term_lit Σ2 σ0 l
      | term_binop op t1 t2       => term_binop op (sub_term t1) (sub_term t2)
      | term_neg t0               => term_neg (sub_term t0)
      | term_not t0               => term_not (sub_term t0)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term t0)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term t0)
      | @term_list _ σ es         => term_list
                                      ((fix sub_terms (ts : list (Term Σ1 σ)) : list (Term Σ2 σ) :=
                                          match ts with
                                          | nil       => nil
                                          | cons t ts => cons (sub_term t) (sub_terms ts)
                                          end) es)
      | term_nil _                => term_nil Σ2
      | term_tuple es             => term_tuple
                                      ((fix sub_terms {σs} (ts : Env (Term Σ1) σs) : Env (Term Σ2) σs :=
                                          match ts with
                                          | env_nil           => env_nil
                                          | env_snoc ts' _ t' => env_snoc (sub_terms ts') _ (sub_term t')
                                          end
                                       ) _ es)
      | @term_projtup _ _ t _ n p => @term_projtup _ _ (sub_term t) _ n p
      | term_union U K t0         => term_union U K (sub_term t0)
      | term_record R es          => term_record R
                                                ((fix sub_terms {σs} (ts : NamedEnv (Term Σ1) σs) : NamedEnv (Term Σ2) σs :=
                                                    match ts with
                                                    | env_nil           => env_nil
                                                    | env_snoc ts' _ t' => env_snoc (sub_terms ts') _ (sub_term t')
                                                    end
                                                 ) _ es)
      | term_projrec t rf         => term_projrec (sub_term t) rf
                                                 (* | term_builtin f t          => term_builtin f (sub_term t) *)
      end.

  End WithSub.

  Definition sub_id Σ : Sub Σ Σ :=
    fun '(ς, τ) ςIn => term_var ς.
  Arguments sub_id : clear implicits.

  Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=
    (fun '(ς, τ) ςIn => @term_var (Σ ▻ b) ς τ (inctx_succ ςIn)).

  Definition sub_comp {Σ1 Σ2 Σ3} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) : Sub Σ1 Σ3 :=
    fun b bIn => sub_term ζ2 (ζ1 b bIn).

  Definition wk1_term {Σ σ b} (t : Term Σ σ) : Term (Σ ▻ b) σ :=
    sub_term sub_wk1 t.

  Definition sub_up1 {Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
    forall {b : 𝑺 * Ty}, Sub (Σ1 ▻ b) (Σ2 ▻ b) :=
    fun '(ς, τ) =>
      @inctx_case_snoc
        (𝑺 * Ty) (fun b' => Term (Σ2 ▻ (ς , τ)) (snd b')) Σ1 (ς , τ)
        (@term_var (Σ2 ▻ (ς , τ)) ς τ inctx_zero)
        (fun b' b'In => wk1_term (ζ b' b'In)).

End SymbolicTerms.

Module SymbolicPrograms
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import symtermkit : SymbolicTermKit typekit termkit).

  Module STs := SymbolicTerms typekit termkit symtermkit.
  Export STs.

  Import CtxNotations.
  Import EnvNotations.
  Import OutcomeNotations.
  Import ListNotations.

  Definition SymbolicLocalStore (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type := NamedEnv (Term Σ) Γ.
  Bind Scope env_scope with SymbolicLocalStore.
  Definition SymbolicRegStore (Σ : Ctx (𝑺 * Ty))  : Type := forall σ, 𝑹𝑬𝑮 σ -> Term Σ σ.


  Fixpoint symbolic_eval_exp {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : SymbolicLocalStore Σ Γ) : Term Σ σ :=
    match e in (Exp _ t) return (Term Σ t) with
    | exp_var ς                       => (δ ‼ ς)%lit
    | exp_lit _ σ0 l                  => term_lit _ σ0 l
    | exp_binop op e1 e2              => term_binop op (symbolic_eval_exp e1 δ) (symbolic_eval_exp e2 δ)
    | exp_neg e0                      => term_neg (symbolic_eval_exp e0 δ)
    | exp_not e0                      => term_not (symbolic_eval_exp e0 δ)
    | @exp_inl _ σ1 σ2 e0             => @term_inl _ σ1 σ2 (symbolic_eval_exp e0 δ)
    | @exp_inr _ σ1 σ2 e0             => @term_inr _ σ1 σ2 (symbolic_eval_exp e0 δ)
    | @exp_list _ σ0 es               => term_list (List.map (fun e : Exp Γ σ0 => symbolic_eval_exp e δ) es)
    | @exp_nil _ σ0                   => term_nil _
    | @exp_tuple _ σs es              =>
      let symbolic_eval_exps := fix symbolic_eval_exps {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Env (Term Σ) σs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (symbolic_eval_exps es) σ (symbolic_eval_exp e δ)
                      end
      in @term_tuple _ σs (symbolic_eval_exps es)
    | @exp_projtup _ σs e0 n σ0 p     => @term_projtup _ σs (symbolic_eval_exp e0 δ) n σ0 p
    | @exp_union _ T K e0             => @term_union _ T K (symbolic_eval_exp e0 δ)
    | exp_record R es                 =>
      let symbolic_eval_exps := fix symbolic_eval_exps {rfs : Ctx (𝑹𝑭 * Ty)} (es : NamedEnv (Exp Γ) rfs) : NamedEnv (Term Σ) rfs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (symbolic_eval_exps es) σ (symbolic_eval_exp e δ)
                      end
      in term_record R (symbolic_eval_exps es)
    | @exp_projrec _ R e0 rf σ0 rfInR => @term_projrec _ R (symbolic_eval_exp e0 δ) rf σ0 rfInR
    (* | @exp_builtin _ σ0 τ f e0        => @term_builtin _ σ0 τ f (symbolic_eval_exp e0 δ) *)
    end.

  Inductive Chunk (Σ : Ctx (𝑺 * Ty)) : Type :=
  | chunk_pred   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).

  Inductive Formula (Σ : Ctx (𝑺 * Ty)) : Type :=
  | formula_bool (t : Term Σ ty_bool)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).

  Inductive Assertion (Σ : Ctx (𝑺 * Ty)) : Type :=
  | asn_bool (b : Term Σ ty_bool)
  | asn_chunk (c : Chunk Σ)
  | asn_if   (b : Term Σ ty_bool) (a1 a2 : Assertion Σ)
  | asn_sep  (a1 a2 : Assertion Σ)
  | asn_exist (ς : 𝑺) (τ : Ty) (a : Assertion (Σ ▻ (ς , τ))).

  Arguments asn_exist [_] _ _ _.

  Inductive SepContract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
  | sep_contract_unit   {Σ} (δ : SymbolicLocalStore Σ Δ) (req : Assertion Σ) (ens : Assertion Σ) (e : τ = ty_unit)
  | sep_contract_result {Σ} (δ : SymbolicLocalStore Σ Δ) (result : 𝑺) (req : Assertion Σ) (ens : Assertion (Σ ▻ (result , τ))).

  Definition SepContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), SepContract Δ τ.
  Parameter Inline CEnv : SepContractEnv.

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Formula Σ).
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Chunk Σ).

  Arguments chunk_pred [_] _ _.

  Definition sub_chunk {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (c : Chunk Σ1) : Chunk Σ2 :=
    match c with
    | chunk_pred p ts => chunk_pred p (env_map (fun _ => sub_term ζ) ts)
    | chunk_ptsreg r t => chunk_ptsreg r (sub_term ζ t)
    end.

  Definition sub_formula {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (fml : Formula Σ1) : Formula Σ2 :=
    match fml with
    | formula_bool t    => formula_bool (sub_term ζ t)
    | formula_eq t1 t2  => formula_eq (sub_term ζ t1) (sub_term ζ t2)
    | formula_neq t1 t2 => formula_neq (sub_term ζ t1) (sub_term ζ t2)
    end.

  Fixpoint sub_assertion {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (a : Assertion Σ1) {struct a} : Assertion Σ2 :=
    match a with
    | asn_bool b => asn_bool (sub_term ζ b)
    | asn_chunk c => asn_chunk (sub_chunk ζ c)
    | asn_if b a1 a2 => asn_if (sub_term ζ b) (sub_assertion ζ a1) (sub_assertion ζ a2)
    | asn_sep a1 a2 => asn_sep (sub_assertion ζ a1) (sub_assertion ζ a2)
    | asn_exist ς τ a => asn_exist ς τ (sub_assertion (sub_up1 ζ) a)
    end.

  Definition sub_pathcondition {Σ1 Σ2} (ζ : Sub Σ1 Σ2) : PathCondition Σ1 -> PathCondition Σ2 :=
    map (sub_formula ζ).
  Definition sub_localstore {Σ1 Σ2 Γ} (ζ : Sub Σ1 Σ2) : SymbolicLocalStore Σ1 Γ -> SymbolicLocalStore Σ2 Γ :=
    env_map (fun _ => sub_term ζ).
  Definition sub_heap {Σ1 Σ2} (ζ : Sub Σ1 Σ2) : SymbolicHeap Σ1 -> SymbolicHeap Σ2 :=
    map (sub_chunk ζ).

  Section SymbolicState.

    Record SymbolicState (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type :=
      MkSymbolicState
        { symbolicstate_pathcondition : PathCondition Σ;
          symbolicstate_localstore    : SymbolicLocalStore Σ Γ;
          symbolicstate_heap          : SymbolicHeap Σ
        }.
    Global Arguments symbolicstate_pathcondition {_ _} _.
    Global Arguments symbolicstate_localstore {_ _} _.
    Global Arguments symbolicstate_heap {_ _} _.

    Definition symbolic_assume_formula {Σ Γ} (fml : Formula Σ) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (fml :: Φ) ŝ ĥ.
    Definition symbolic_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (formula_bool (symbolic_eval_exp e ŝ) :: Φ) ŝ ĥ.
    Definition symbolic_push_local {Σ Γ x} σ (v : Term Σ σ) : SymbolicState Σ Γ -> SymbolicState Σ (Γ ▻ (x , σ)) :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_snoc ŝ (x , σ) v) ĥ.
    Definition symbolic_pop_local {Σ Γ x σ} : SymbolicState Σ (Γ ▻ (x , σ)) -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_tail ŝ) ĥ.

    Program Definition sub_symbolicstate {Σ1 Σ2 Γ} (ζ : Sub Σ1 Σ2) : SymbolicState Σ1 Γ -> SymbolicState Σ2 Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (sub_pathcondition ζ Φ) (sub_localstore ζ ŝ) (sub_heap ζ ĥ).
    Definition wk1_symbolicstate {Σ Γ b} : SymbolicState Σ Γ -> SymbolicState (Σ ▻ b) Γ :=
      sub_symbolicstate sub_wk1.

  End SymbolicState.
End SymbolicPrograms.

Module SymbolicSemantics_Mutator
    (typekit : TypeKit)
    (termkit : TermKit typekit)
    (symtermkit : SymbolicTermKit typekit termkit).
  Import typekit.
  Import termkit.

  Module SP := SymbolicPrograms typekit termkit symtermkit.
  Export SP.

  Import CtxNotations.
  Import EnvNotations.
  Import OutcomeNotations.

  Section Mutator.

    Definition Obligation : Type := { Σ & Formula Σ }.
    Definition Mutator (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Σ Γ1 -> Outcome (A * SymbolicState Σ Γ2 * list Obligation).
    Bind Scope mutator_scope with Mutator.

    Definition mutator_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨂ i : I => ms i s)%out.
    Definition mutator_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨁ i : I => ms i s)%out.
    Definition mutator_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_demonic (fun b : bool => if b then m1 else m2).
    Definition mutator_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_angelic (fun b : bool => if b then m1 else m2).

    Definition mutator_pure {Σ Γ A} (a : A) : Mutator Σ Γ Γ A :=
      fun s => outcome_pure (a, s, nil).
    Definition mutator_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      fun s0 => outcome_bind (ma s0) (fun '(a , s1 , w1) => outcome_bind (f a s1) (fun '(b , s2 , w2) => outcome_pure (b , s2 , w1 ++ w2))).
    Definition mutator_bind_right {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      mutator_bind ma (fun _ => mb).
    Definition mutator_bind_left {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 A :=
      mutator_bind ma (fun a => mutator_bind mb (fun _ => mutator_pure a)).
    Definition mutator_map {Σ Γ1 Γ2 A B} (f : A -> B) (ma : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 B :=
      mutator_bind ma (fun a => mutator_pure (f a)).

  End Mutator.
  Bind Scope mutator_scope with Mutator.

  Module MutatorNotations.

    Notation "'⨂' i : I => F" := (mutator_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : mutator_scope.
    Notation "'⨁' i : I => F" := (mutator_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : mutator_scope.

    Infix "⊗" := mutator_demonic_binary (at level 40, left associativity) : mutator_scope.
    Infix "⊕" := mutator_angelic_binary (at level 50, left associativity) : mutator_scope.

    Notation "x <- ma ;; mb" := (mutator_bind ma (fun x => mb)) (at level 100, right associativity, ma at next level) : mutator_scope.
    Notation "ma >>= f" := (mutator_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (mutator_bind m1 (fun _ => m2)) : mutator_scope.
    Notation "ma *> mb" := (mutator_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (mutator_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.
  Import MutatorNotations.

  Section MutatorOperations.

    Local Open Scope mutator_scope.

    Definition mutator_fail {Σ Γ} {A : Type} : Mutator Σ Γ Γ A :=
      fun s => outcome_fail.
    Definition mutator_get {Σ Γ} : Mutator Σ Γ Γ (SymbolicState Σ Γ) :=
      fun s => outcome_pure (s , s , nil).
    Definition mutator_put {Σ Γ Γ'} (s : SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun _ => outcome_pure (tt , s, nil).
    Definition mutator_modify {Σ Γ Γ'} (f : SymbolicState Σ Γ -> SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_get >>= fun δ => mutator_put (f δ).
    Definition mutator_get_local {Σ Γ} : Mutator Σ Γ Γ (SymbolicLocalStore Σ Γ) :=
      fun s => outcome_pure (symbolicstate_localstore s , s , nil).
    Definition mutator_put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun '(MkSymbolicState Φ _ ĥ) => outcome_pure (tt , MkSymbolicState Φ δ' ĥ , nil).
    Definition mutator_modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_get_local >>= fun δ => mutator_put_local (f δ).
    Definition mutator_pop_local {Σ Γ x σ} : Mutator Σ (Γ ▻ (x , σ)) Γ unit :=
      mutator_modify_local (fun δ => env_tail δ).
    Definition mutator_pops_local {Σ Γ} Δ : Mutator Σ (Γ ▻▻ Δ) Γ unit :=
      mutator_modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition mutator_push_local {Σ Γ x} σ (v : Term Σ σ) : Mutator Σ Γ (Γ ▻ (x , σ)) unit :=
      mutator_modify_local (fun δ => env_snoc δ (x , σ) v).
    Definition mutator_pushs_local {Σ Γ Δ} (δΔ : NamedEnv (Term Σ) Δ) : Mutator Σ Γ (Γ ▻▻ Δ) unit :=
      mutator_modify_local (fun δΓ => env_cat δΓ δΔ).

    Definition mutator_get_heap {Σ Γ} : Mutator Σ Γ Γ (SymbolicHeap Σ) :=
      mutator_map symbolicstate_heap mutator_get.
    Definition mutator_put_heap {Σ Γ} (h : SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      fun '(MkSymbolicState Φ δ _) => outcome_pure (tt , MkSymbolicState Φ δ h , nil).
    Definition mutator_modify_heap {Σ Γ} (f : SymbolicHeap Σ -> SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify (fun '(MkSymbolicState Φ δ h) => MkSymbolicState Φ δ (f h)).

    Definition mutator_eval_exp {Σ Γ σ} (e : Exp Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      mutator_get_local >>= fun δ => mutator_pure (symbolic_eval_exp e δ).

    Definition mutator_assume_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify (symbolic_assume_formula fml).
    Definition mutator_assume_term {Σ Γ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assume_formula (formula_bool t).
    Definition mutator_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assume_term.

    Definition mutator_assert_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      fun δ => outcome_pure (tt , δ , existT Formula Σ fml :: nil).
    Definition mutator_assert_term {Σ Γ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assume_formula (formula_bool t).
    Definition mutator_assert_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assert_term.

    Definition mutator_produce_chunk {Σ Γ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify_heap (fun h => c :: h).

    Equations chunk_eqb {Σ} {ctx : Ctx Ty}
             (c1 : Env (Term Σ) ctx) (c2 : Env (Term Σ) ctx) : bool :=
        chunk_eqb env_nil env_nil  := true;
        chunk_eqb (env_snoc xs ?(σ) x) (env_snoc ys σ y) :=
          Term_eqb x y && chunk_eqb xs ys.

    Program Fixpoint outcome_consume_chunk {Σ} (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
        (h : SymbolicHeap Σ) : Outcome (SymbolicHeap Σ) :=
      let fix go h unconsumed {struct h} : Outcome (SymbolicHeap Σ) :=
          match h return Outcome (SymbolicHeap Σ) with
          | nil => outcome_pure unconsumed
          | cons x xs =>
            match x with
            | chunk_pred p' ts' =>
              match (𝑷_eq_dec p p') with
              | left e => let c := ltac:(rewrite e in *; exact (chunk_eqb ts ts'))
                         in if c then go xs unconsumed else go xs (x :: unconsumed)
              | right _ => go xs (x :: unconsumed)
              end
            | chunk_ptsreg r t =>
              go xs (x :: unconsumed)
            end
          end
      in go h nil.
    Arguments outcome_consume_chunk {_} _ _ _.

    Definition mutator_consume_chunk {Σ Γ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      match c with
      | chunk_pred p ts => fun '(MkSymbolicState Φ δ h) =>
                             outcome_bind
                               (outcome_consume_chunk p ts h)
                               (fun h' => outcome_pure (tt , MkSymbolicState Φ δ h' , nil))
      | chunk_ptsreg r t => mutator_fail
      end.

    Fixpoint mutator_produce {Σ Γ} (asn : Assertion Σ) : Mutator Σ Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assume_term b
      | asn_chunk c     => mutator_produce_chunk c
      | asn_if b a1 a2  => (mutator_assume_term b ;; mutator_produce a1) ⊗
                           (mutator_assume_term (term_not b) ;; mutator_produce a2)
      | asn_sep a1 a2   => mutator_produce a1 *> mutator_produce a2
      | asn_exist ς τ a => mutator_fail
      end.

    Fixpoint mutator_consume {Σ Γ} (asn : Assertion Σ) : Mutator Σ Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assert_term b
      | asn_chunk c     => mutator_consume_chunk c
      | asn_if b a1 a2  => (mutator_assume_term b ;; mutator_consume a1) ⊗
                           (mutator_assume_term (term_not b) ;; mutator_consume a2)
      | asn_sep a1 a2   => mutator_consume a1 *> mutator_consume a2
      | asn_exist ς τ a => mutator_fail
      end.

    Program Fixpoint mutator_exec {Σ Γ σ} (s : Stm Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      match s with
      | stm_lit τ l => mutator_pure (term_lit _ τ l)
      | stm_exp e => mutator_eval_exp e
      | stm_let x τ s k =>
        mutator_exec s >>= fun v =>
        mutator_push_local v *>
        mutator_exec k              <*
        mutator_pop_local
      | stm_let' δ k =>
        mutator_pushs_local (env_map (fun _ => term_lit Σ _) δ) *>
        mutator_exec k <*
        mutator_pops_local _
      | stm_assign x e => mutator_exec e >>= fun v =>
        mutator_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *>
        mutator_pure v
      | stm_call f es =>
        match CEnv f with
        | @sep_contract_unit _ _ Σ' _ req ens e =>
          ⨁ ζ : Sub Σ' Σ =>
            mutator_consume (sub_assertion ζ req) *>
            mutator_produce (sub_assertion ζ ens) *>
            mutator_pure (term_lit Σ _ (@eq_rect_r Ty ty_unit Lit tt _ e))
        | @sep_contract_result _ _ Σ' δ result req ens => _
        end
      | stm_call' Δ δ' τ s =>
        mutator_get_local                                      >>= fun δ =>
        mutator_put_local (env_map (fun _ => term_lit _ _) δ') >>= fun _ =>
        mutator_exec s                                                >>= fun t =>
        mutator_put_local δ                                    >>= fun _ =>
        mutator_pure t
      | stm_if e s1 s2 =>
        (mutator_assume_exp e ;; mutator_exec s1) ⊗
        (mutator_assume_exp (exp_not e) ;; mutator_exec s2)
      | stm_seq e k => mutator_exec e ;; mutator_exec k
      | stm_assert e1 _ => mutator_eval_exp e1 >>= fun t =>
                           mutator_assert_term t ;;
                           mutator_pure t
      | stm_fail τ s =>    mutator_fail
      | stm_match_list e alt_nil xh xt alt_cons =>
        mutator_eval_exp e >>= fun t =>
                                 (* (formula_term_eq t nil) *)
        (mutator_assume_formula _ ;; mutator_exec alt_nil) ⊗ _
        (* mutator_exists (fun ςh ςt => *)
        (*                   mutator_assume_formula (weaken t (ςh , ςt) = cons ςh ςt) ;; *)
        (*                   xh  ↦ ςh ;; *)
        (*                   xt  ↦ ςt ;; *)
        (*                   mutator_exec alt_cons ;; *)
        (*                   pop ;; *)
        (*                   pop) *)
      | stm_match_sum e xinl alt_inl xinr alt_inr => _
      | stm_match_pair e xl xr rhs => _
      | stm_match_enum E e alts => _
      | stm_match_tuple e p rhs => _
      | stm_match_union U e altx alts => _
      | stm_match_record R e p rhs => _
      | @stm_read_register _ τ reg => ⨁ t : Term Σ τ =>
        mutator_consume (asn_chunk (chunk_ptsreg reg t)) *>
        mutator_produce (asn_chunk (chunk_ptsreg reg t))  *>
        mutator_pure t
      | @stm_write_register _ τ reg e => mutator_eval_exp e >>=
        fun v => ⨁ t : Term Σ τ =>
        mutator_consume (asn_chunk (chunk_ptsreg reg t)) *>
        mutator_produce (asn_chunk (chunk_ptsreg reg v)) *>
        mutator_pure v
      | stm_bind s k => _
      | stm_read_memory _ => _
      | stm_write_memory _ _ => _
      end.
    Admit Obligations of mutator_exec.

  End MutatorOperations.
End SymbolicSemantics_Mutator.
