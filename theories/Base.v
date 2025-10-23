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
     Syntax.UnOps
     Syntax.Variables
     Tactics.
From Katamaran Require Import
     Syntax.Expressions
     Syntax.Messages
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
    MessagesOn TY <+ PartialEvaluationOn TY.

  Notation Ty := (@ty.Ty typedeclkit).
  Notation LVar := (@Variables.LVar varkit).
  Notation PVar := (@Variables.PVar varkit).
  Notation PCtx := (NCtx PVar Ty).
  Notation LCtx := (NCtx LVar Ty).
  Notation Val := (@ty.Val typedeclkit typedenotekit).
  Notation RelVal := (@ty.RelVal typedeclkit typedenotekit).

  Notation Valuation Σ :=
    (@Env (Binding LVar Ty)
       (fun xt : Binding LVar Ty =>
          RelVal (@type _ _ xt)) Σ).

  Notation CStore := (@NamedEnv PVar Ty RelVal).
  Notation CStoreVal := (@NamedEnv PVar Ty Val).

  Definition projLeftCStore {Γ} (δ : CStore Γ) : CStoreVal Γ :=
    env.map (fun _ => ty.projLeft) δ.

  Definition projRightCStore {Γ} (δ : CStore Γ) : CStoreVal Γ :=
    env.map (fun _ => ty.projRight) δ.

  Definition zipCStoreVal {Γ : PCtx} (δ1 δ2 : CStoreVal Γ) : CStore Γ.
  Proof.
    induction Γ.
    - exact env.nil.
    - apply env.snoc.
      + apply IHΓ.
        * env.destroy δ1. exact δ1.
        * env.destroy δ2. exact δ2.
      + apply NonSyncVal.
        * env.destroy δ1. exact v.
        * env.destroy δ2. exact v.
          Show Proof.
  Defined.

  (* TODO: Replace proof mode definition by declaritive definition *)
  (* Fixpoint zipCStoreVal {Γ : PCtx} (δ1 δ2 : CStoreVal Γ) : CStore Γ := *)
  (* match Γ , δ1 , δ2 with *)
  (* | ctx.nil , _ , _ => env.nil *)
  (* | ctx.snoc Γ b , env.snoc δ1 b1 db1 , env.snoc δ2 b2 db2 => *)
  (*     env.snoc (zipCStoreVal δ1 δ2) (NonSyncVal db1 db2) *)
  (* end. *)

  Lemma projLeftZipCStoreVal {Γ} (δ1 δ2 : CStoreVal Γ) :
    projLeftCStore (zipCStoreVal δ1 δ2) = δ1.
  Proof.
    induction Γ.
    - env.destroy δ1. reflexivity.
    - env.destroy δ1. env.destroy δ2. cbn.
      rewrite IHΓ. reflexivity.
  Qed.

  Lemma projRightZipCStoreVal {Γ} (δ1 δ2 : CStoreVal Γ) :
    projRightCStore (zipCStoreVal δ1 δ2) = δ2.
  Proof.
    induction Γ.
    - env.destroy δ2. reflexivity.
    - env.destroy δ1. env.destroy δ2. cbn.
      rewrite IHΓ. reflexivity.
  Qed.

  Lemma projLeftCStoreCatIsCatOfProjLeftCStore {Γ1 Γ2} (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    projLeftCStore (env.cat δ1 δ2) = env.cat (projLeftCStore δ1) (projLeftCStore δ2).
  Proof.
    induction Γ2.
    - env.destroy δ2. reflexivity.
    - env.destroy δ2. cbn. rewrite IHΓ2. reflexivity.
  Qed.

  Lemma projRightCStoreCatIsCatOfProjRightCStore {Γ1 Γ2} (δ1 : CStore Γ1) (δ2 : CStore Γ2) :
    projRightCStore (env.cat δ1 δ2) = env.cat (projRightCStore δ1) (projRightCStore δ2).
  Proof.
    induction Γ2.
    - env.destroy δ2. reflexivity.
    - env.destroy δ2. cbn. rewrite IHΓ2. reflexivity.
  Qed.

  Lemma projLeftCStoreEnvMapValToRelValIsId {Γ} (δ : CStoreVal Γ) :
    projLeftCStore (env.map (fun _ => ty.valToRelVal) δ) = δ.
  Proof.
    induction Γ.
    - env.destroy δ. reflexivity.
    - env.destroy δ. cbn. rewrite IHΓ. reflexivity.
  Qed.

  Lemma projRightCStoreEnvMapValToRelValIsId {Γ} (δ : CStoreVal Γ) :
    projRightCStore (env.map (fun _ => ty.valToRelVal) δ) = δ.
  Proof.
    induction Γ.
    - env.destroy δ. reflexivity.
    - env.destroy δ. cbn. rewrite IHΓ. reflexivity.
  Qed.

  Lemma projLeftCStoreEnvTailIsEnvTailProjLeftCStore {Γ b} (δ : CStore (ctx.snoc Γ b)) :
    projLeftCStore (env.tail δ) = env.tail (projLeftCStore δ).
  Proof.
    env.destroy δ.
    reflexivity.
  Qed.

  Lemma projRightCStoreEnvTailIsEnvTailProjRightCStore {Γ b} (δ : CStore (ctx.snoc Γ b)) :
    projRightCStore (env.tail δ) = env.tail (projRightCStore δ).
  Proof.
    env.destroy δ.
    reflexivity.
  Qed.

  Lemma projLeftCStoreEnvDropIsEnvDropProjLeftCStore {Γ Δ} (δ : CStore (ctx.cat Γ Δ)) :
  projLeftCStore (env.drop Δ δ) = env.drop Δ (projLeftCStore δ).
  Proof.
    induction Δ.
    - reflexivity.
    - cbn. rewrite IHΔ, projLeftCStoreEnvTailIsEnvTailProjLeftCStore. reflexivity.
  Qed.

  Lemma projRightCStoreEnvDropIsEnvDropProjRightCStore {Γ Δ} (δ : CStore (ctx.cat Γ Δ)) :
    projRightCStore (env.drop Δ δ) = env.drop Δ (projRightCStore δ).
  Proof.
    induction Δ.
    - reflexivity.
    - cbn. rewrite IHΔ, projRightCStoreEnvTailIsEnvTailProjRightCStore. reflexivity.
  Qed.

  Lemma projLeftCStoreEnvUpdateIsEnvUpdateProjLeftCStore {Γ} (δ : CStore Γ)
    (x : PVar) (σ : Ty) (xIn : ctx.In {| name := x; type := σ |} Γ) (rv : RelVal σ) :
    projLeftCStore (env.update δ xIn rv) = env.update (projLeftCStore δ) xIn (ty.projLeft rv).
  Proof.
    unfold projLeftCStore.
    now rewrite env.map_update.
  Qed.

  Lemma projRightCStoreEnvUpdateIsEnvUpdateProjRightCStore {Γ} (δ : CStore Γ)
    (x : PVar) (σ : Ty) (xIn : ctx.In {| name := x; type := σ |} Γ) (rv : RelVal σ) :
    projRightCStore (env.update δ xIn rv) = env.update (projRightCStore δ) xIn (ty.projRight rv).
  Proof.
    unfold projRightCStore.
    now rewrite env.map_update.
  Qed.

  Definition SMatchResult {N σ} (pat : Pattern (N:=N) σ) (Σ : LCtx) : Type :=
    { pc : PatternCase pat & NamedEnv (Term Σ) (PatternCaseCtx pc) }.
  

  Section PatternMatching.
    Context {N : Set}.

    (* Lemma inst_tuple_pattern_match {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty} *)
    (*   (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : Env (Term Σ) σs) : *)
    (*   inst (tuple_pattern_match_env p ts) ι = *)
    (*   tuple_pattern_match_env p (inst (T := fun Σ => Env (Term Σ) σs) ts ι). *)
    (* Proof. *)
    (*   unfold inst at 1; cbn. *)
    (*   induction p; cbn. *)
    (*   - reflexivity. *)
    (*   - destruct (env.view ts); cbn. *)
    (*     f_equal. apply IHp. *)
    (* Qed. *)

    (* Lemma inst_tuple_pattern_match_reverse {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty} *)
    (*   (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : NamedEnv (Term Σ) Δ) : *)
    (*   inst (tuple_pattern_match_env_reverse p ts) ι = *)
    (*   tuple_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι). *)
    (* Proof. *)
    (*   unfold inst at 1; cbn. *)
    (*   induction p; cbn. *)
    (*   - reflexivity. *)
    (*   - destruct (env.view ts); cbn. *)
    (*     f_equal. apply IHp. *)
    (* Qed. *)

    (* Lemma inst_record_pattern_match {Δ__R : NCtx recordf Ty} {Σ : LCtx} {Δ : NCtx N Ty} *)
    (*   (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ__R) : *)
    (*   inst (T := fun Σ => NamedEnv (Term Σ) Δ) (record_pattern_match_env p ts) ι = *)
    (*   record_pattern_match_env p (inst ts ι). *)
    (* Proof. *)
    (*   unfold inst at 1; cbn. *)
    (*   induction p; cbn. *)
    (*   - reflexivity. *)
    (*   - destruct (env.view ts); cbn. *)
    (*     f_equal. apply IHp. *)
    (* Qed. *)

    (* Lemma inst_record_pattern_match_reverse {Δ__R : NCtx recordf Ty} {Σ : LCtx} {Δ : NCtx N Ty} *)
    (*   (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ) : *)
    (*   inst (record_pattern_match_env_reverse p ts) ι = *)
    (*   record_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι). *)
    (* Proof. *)
    (*   unfold inst at 1; cbn. *)
    (*   induction p; cbn. *)
    (*   - reflexivity. *)
    (*   - destruct (env.view ts); cbn. *)
    (*     f_equal. apply IHp. *)
    (* Qed. *)

    Definition pattern_match_term_reverse {Σ σ} (pat : Pattern (N:=N) σ) :
      forall (pc : PatternCase pat), NamedEnv (Term Σ) (PatternCaseCtx pc) -> Term Σ σ :=
      match pat with
      | pat_var x =>
          fun _ ts => env.head ts
      | pat_bool =>
          fun b _ => term_val ty.bool b
      (* | pat_list σ x y => *)
      (*     fun b => *)
      (*       match b with *)
      (*       | true => fun _ => term_val (ty.list σ) nil *)
      (*       | false => fun Eht => *)
      (*                    let (Eh,t) := env.view Eht in *)
      (*                    let (E,h)  := env.view Eh in *)
      (*                    term_binop bop.cons h t *)
      (*       end *)
      | pat_pair x y =>
          fun _ Exy =>
            let (Ex,vτ) := env.view Exy in
            let (E,vσ)  := env.view Ex in
            term_binop bop.pair vσ vτ
      (* | pat_sum σ0 τ x y => *)
      (*     fun b => *)
      (*       match b with *)
      (*       | true => fun ts => term_unop uop.inl (env.head ts) *)
      (*       | false => fun ts => term_unop uop.inr (env.head ts) *)
      (*       end *)
      | pat_unit =>
          fun pc _ => term_val ty.unit pc
      (* | pat_enum E => *)
      (*     fun v _ => term_val (ty.enum E) v *)
      | pat_bvec_split m n x y =>
          fun _ Exy =>
            let (Ex,vr) := env.view Exy in
            let (E,vl)  := env.view Ex in
            term_binop bop.bvapp vl vr
      (* | pat_bvec_exhaustive m => *)
      (*     fun v _ => term_val (ty.bvec m) v *)
      (* | pat_tuple p => *)
      (*     fun _ ts => term_tuple (tuple_pattern_match_env_reverse p ts) *)
      (* | pat_record R Δ p => *)
      (*     fun _ ts => term_record R (record_pattern_match_env_reverse p ts) *)
      (* | pat_union U x => *)
      (*     fun '(existT K pc) ts => term_union U K (pattern_match_term_reverse (x K) pc ts) *)
      end.

    Lemma inst_pattern_match_term_reverse {Σ σ} (ι : Valuation Σ) (pat : Pattern (N:=N) σ) :
      forall (pc : PatternCase pat) (ts : NamedEnv (Term Σ) (PatternCaseCtx pc)),
        inst (A := RelVal _) (pattern_match_term_reverse pat pc ts) ι =
          pattern_match_relval_reverse pat pc (inst (T := fun Σ => NamedEnv (Term Σ) _) ts ι).
    Proof.
      induction pat; cbn.
      - intros _y ts. env.destroy ts. cbn in *.
        now destructInsts.
      - intros __y ts. env.destroy ts. auto.
      (* - intros [] ts. *)
      (*   + reflexivity. *)
      (*   + now env.destroy ts. *)
      - intros __y ts. env.destroy ts. cbn in *. now destructInsts.
      - intros [] ts; now env.destroy ts.
      (* - intros [] ts. reflexivity. *)
      (* - reflexivity. *)
      - intros __y ts. env.destroy ts. cbn in *. now destructInsts.
      (* - reflexivity. *)
      (* - intros _ ts. *)
      (*   now rewrite <- inst_tuple_pattern_match_reverse. *)
      (* - intros _ ts. f_equal. *)
      (*   apply inst_record_pattern_match_reverse. *)
      (* - intros [] ts. cbn. f_equal. f_equal. apply H. *)
    Qed.

    Lemma inst_unfreshen_namedenv (n : N -> LVar) {Σ Σ' Δ}
      (ζ : Sub (freshen_ctx n Σ Δ) Σ') (ι : Valuation Σ') :
      inst (unfreshen_namedenv n ζ) ι = unfreshen_namedenv n (inst ζ ι).
    Proof. induction Δ; cbn in ζ; env.destroy ζ; cbn; f_equal; apply IHΔ. Qed.

    Lemma inst_unfreshen_patterncaseenv (n : N -> LVar) {Σ Σ' σ} (pat : Pattern (N:=N) σ)
      (pc : PatternCase (freshen_pattern n Σ pat))
      (ζ : Sub (PatternCaseCtx pc) Σ')
      (ι : Valuation Σ') :
      inst (unfreshen_patterncaseenv n pat pc ζ) ι =
      unfreshen_patterncaseenv n pat pc (inst ζ ι).
    Proof.
      induction pat; cbn in pc; try destruct pc; cbn in ζ, ι; env.destroy ζ;
        env.destroy ι; cbn; auto using inst_unfreshen_namedenv.
    Qed.

  End PatternMatching.

  Import env.notations.

  Definition seval_exp {Γ Σ} (δ : SStore Γ Σ) :
    forall {σ} (e : Exp Γ σ), Term Σ σ :=
    fix seval_exp {σ} (e : Exp Γ σ) : Term Σ σ :=
      match e with
      | exp_var ς          => δ.[??ς]
      | exp_val σ v        => term_val σ v
      | exp_binop op e1 e2 => term_binop op (seval_exp e1) (seval_exp e2)
      | exp_unop op e      => term_unop op (seval_exp e)
      (* | exp_list es        => term_list (List.map seval_exp es) *)
      | exp_bvec es        => term_bvec (Vector.map seval_exp es)
      (* | exp_tuple es       => term_tuple (env.map (@seval_exp) es) *)
      (* | exp_union E K e    => term_union E K (seval_exp e) *)
      (* | exp_record R es    => term_record R (env.map (fun _ => seval_exp) es) *)
      end%exp.

  Definition seval_exps {Γ Σ N} (δ : SStore Γ Σ) {Δ} :
    NamedEnv (X := N) (Exp Γ) Δ -> NamedEnv (Term Σ) Δ
      := env.map (fun b (e : Exp Γ (type b)) => peval (seval_exp δ e)).

  Ltac destructRVs :=
    repeat match goal with
        |- context[match ?b with
                   | SyncVal _ => _
                   | _ => _
                   end] => destruct b; cbn
      end.

  (* Lemma eval_exp_inst {Γ Σ τ} (ι : Valuation Σ) (δΓΣ : SStore Γ Σ) (e : Exp Γ τ) : *)
  (*   eval e (inst δΓΣ ι) = inst (seval_exp δΓΣ e) ι. *)
  (* Proof. *)
  (*   induction e; cbn; repeat f_equal; auto. *)
  (*   { unfold inst, inst_store, inst_env at 1; cbn. *)
  (*     now rewrite env.lookup_map. *)
  (*   } *)
  (*   (* 2: { *) *)
  (*   (*   induction es as [|eb n es IHes]; cbn in *. *) *)
  (*   (*   { reflexivity. } *) *)
  (*   (*   { destruct X as [-> Heqs]. *) *)
  (*   (*     change (inst_term ?ι ?t) with (inst ι t). *) *)
  (*   (*     destruct (inst (seval_exp δΓΣ eb) ι); *) *)
  (*   (*       cbn; f_equal; auto. *) *)
  (*   (*   } *) *)
  (*   (* } *) *)
  (*   { rewrite IHe1. rewrite IHe2. *)
  (*   now destructInsts. } *)
  (*   { admit. } *)
  (* Qed. *)

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

Module Type OperationalModel.

  (* Memory model *)
  Parameter Memory : Type.
  
End OperationalModel.


Module Type Base := Types <+ RegDeclKit <+ OperationalModel <+ BaseMixin.

Module DefaultBase <: Base.

  Definition Memory : Set := unit.

  #[export] Instance typedeclkit : TypeDeclKit := DefaultTypeDeclKit.
  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit := DefaultTypeDenoteKit.
  #[export] Instance typedefkit : TypeDefKit typedenotekit := DefaultTypeDefKit.
  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include DefaultRegDeclKit.
  Include BaseMixin.

End DefaultBase.
