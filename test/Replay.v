(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     Lists.List
     Logic.FinFun
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Signature
     Semantics.Registers
     Symbolic.Executor
     Shallow.Executor
     Symbolic.Solver
     Specification
     Program.

From stdpp Require decidable finite.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)

(** Enums **)
Inductive Enums : Set :=.

(** Unions **)
Inductive Unions : Set :=.
  
(** Records **)
Inductive Records : Set :=.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Enums.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Records.

End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for Unions.
Derive EqDec for Records.

Module Import ReplayBase <: Base.
  Import stdpp.finite.

  #[export] Instance typedeclkit : TypeDeclKit :=
    {| enumi := Enums;
       unioni := Unions;
       recordi := Records;
    |}.

  Definition enum_denote (E : Enums) : Set :=
    match E with end.

  Definition union_denote (U : Unions) : Set :=
    match U with end.

  Definition record_denote (R : Records) : Set :=
    match R with end.

  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {| enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.

  Definition union_constructors (U : Unions) : Set :=
    match U with end.

  Definition union_constructor_type (U : Unions) : union_constructors U -> Ty :=
    match U with end.

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with end.

  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
    match U with end.

  Definition record_field_type (R : recordi) : NCtx Empty_set Ty :=
    match R with end.

  Definition record_fold (R : recordi) : NamedEnv Val (record_field_type R) -> recordt R :=
    match R with end.
  Definition record_unfold (R : recordi) : recordt R -> NamedEnv Val (record_field_type R) :=
    match R with end.

  #[export] Instance eqdec_enum_denote E : EqDec (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance finite_enum_denote E : finite.Finite (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance eqdec_union_denote U : EqDec (union_denote U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_union_constructors U : EqDec (union_constructors U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance finite_union_constructors U : finite.Finite (union_constructors U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_record_denote R : EqDec (record_denote R) :=
    ltac:(destruct R; auto with typeclass_instances).

  #[export,refine] Instance typedefkit : TypeDefKit typedenotekit :=
    {| unionk         := union_constructors;
       unionk_ty      := union_constructor_type;
       unionv_fold    := union_fold;
       unionv_unfold  := union_unfold;
       recordf        := Empty_set;
       recordf_ty     := record_field_type;
       recordv_fold   := record_fold;
       recordv_unfold := record_unfold;
    |}.
  Proof.
    - abstract (now intros [] []).
    - abstract (now intros [] [[]]).
    - abstract (intros []).
    - abstract (intros []).
  Defined.

  Definition ty_X := ty.list ty.int.

  #[export] Instance varkit : VarKit := DefaultVarKit.

  Section RegDeclKit.
    Inductive Reg : Ty -> Set :=.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion EqDec for Reg.
    End TransparentObligations.

    Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
    #[export] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg) :=
      sigma_eqdec _ _.

    Local Obligation Tactic :=
      finite_from_eqdec.

    #[export,program] Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) :=
      {| enum := [] |}.
  End RegDeclKit.
  Include BaseMixin.
End ReplayBase.

(*** PROGRAM ***)

Module Import ReplayProgram <: Program ReplayBase.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | main : Fun ["xs" :: ty_X] ty.unit.

    Inductive Lem : PCtx -> Set :=
    | open_list : Lem ε.

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳 : PCtx -> Set := Lem.

  End FunDeclKit.

  Include FunDeclMixin ReplayBase.

  Section FunDefKit.
    Import ctx.resolution.

    Local Coercion stm_exp : Exp >-> Stm.

    Definition fun_main : Stm ["xs" :: ty_X] ty.unit :=
      stm_lemma open_list [] ;;
      stm_val ty.unit tt.

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | main => fun_main
      end.
  End FunDefKit.

  Include DefaultRegStoreKit ReplayBase.

  Section ForeignKit.
    Definition Memory : Set := unit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. destruct f. Qed.
  End ForeignKit.

  Include ProgramMixin ReplayBase.

End ReplayProgram.

Module Import ReplayPredicates.
  Import ListNotations.

  Inductive PurePredicate : Set :=
  | Q.

  Fixpoint Q_aux (xs : Val ty_X) : bool :=
    match xs with
    | 0 :: xs => (1 =? 7)
    | _       => true
    end%list.

  Definition interp_Q (xs : Val ty_X) : Prop :=
    Q_aux xs = true.

  Inductive Predicate : Set :=
  | P.

  Section TransparentObligations.
    Local Set Transparent Obligations.

    Derive NoConfusion for PurePredicate.
    Derive NoConfusion for Predicate.

  End TransparentObligations.

  Derive EqDec for PurePredicate.
  Derive EqDec for Predicate.
End ReplayPredicates.

Module Import ReplaySig <: Signature ReplayBase.
  Section PredicateKit.
    Definition 𝑷 := PurePredicate.
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | Q => [ty_X]
      end.
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | Q => interp_Q
      end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | P => [ty_X]
      end.
    Global Instance 𝑯_is_dup : IsDuplicable 𝑯 := {
        is_duplicable p := false
      }.
    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    Local Arguments Some {_} &.
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | P => Some (MkPrecise ε [ty_X] eq_refl)
      end.
  End PredicateKit.

  Include PredicateMixin ReplayBase.
  Include SignatureMixin ReplayBase.
End ReplaySig.

Module Import ReplaySpecification <: Specification ReplayBase ReplayProgram ReplaySig.
  Include SpecificationMixin ReplayBase ReplayProgram ReplaySig.
  Import ctx.resolution.
  Import List.ListNotations.

  Section ContractDefKit.

    Import asn.notations.
    Notation asn_prop Σ P := (asn.formula (@formula_prop Σ Σ (sub_id Σ) P)).
    Notation asn_P xs := (asn.chunk (chunk_user P [xs])).
    Notation asn_Q xs := (asn.formula (formula_user Q [xs])).

    Definition sep_contract_main : SepContract ["xs" :: ty_X] ty.unit :=
      {| sep_contract_logic_variables := ["xs" :: ty_X];
         sep_contract_localstore      := [term_var "xs"];
         sep_contract_precondition    := asn_Q (term_var "xs") ∗ asn_P (term_var "xs");
         sep_contract_result          := "_";
         sep_contract_postcondition   := term_val ty.int 1%Z = term_val ty.int 7%Z;
      |}.

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | main => Some sep_contract_main
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with end.

    Definition SepLemma {Δ} (f : Lem Δ) : Type :=
      Lemma Δ.

    Definition lemma_open_list : SepLemma open_list :=
      {| lemma_logic_variables := ["l" :: ty_X];
         lemma_patterns        := env.nil;
         lemma_precondition    := asn_P (term_var "l");
         lemma_postcondition   := term_var "l" = term_list [term_val ty.int 0%Z];
      |}.

    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with
        | open_list => lemma_open_list
        end.

  End ContractDefKit.

End ReplaySpecification.

Module ReplaySolverKit <: SolverKit ReplayBase ReplaySig.
  Import List.ListNotations.
  Import Entailment.

  Definition simplify_Q {Σ} (xs : Term Σ ty_X) : option (PathCondition Σ) :=
    let no_simplification := Some [formula_user Q [xs]] in
    match term_get_val xs with
    | Some ls => match ls with
                 | 0 :: _ => Some [formula_relop bop.eq (term_val ty.int 1%Z) (term_val ty.int 7%Z)]%ctx
                 | _      => no_simplification
                 end%list
    | _       => no_simplification
    end.

  Equations(noeqns) simplify_user [Σ] (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (PathCondition Σ) :=
  | Q | [env xs ] => simplify_Q xs.

  Local Ltac lsolve :=
    repeat
      lazymatch goal with
      | |- Some _             ⊣⊢ Some _             => apply @proper_some
      | |- ctx.snoc ctx.nil _ ⊣⊢ ctx.snoc ctx.nil _ => apply proper_snoc; [easy|]
      | |- None               ⊣⊢ Some _             => apply @unsatisfiable_none_some
      | |- [ctx]              ⊣⊢ _                  => apply nil_l_valid
      | |- Unsatisfiable (ctx.snoc ctx.nil _)       => apply unsatisfiable_snoc_r
      | |- match @term_get_val ?Σ ?σ ?v with _ => _ end ⊣⊢ _ =>
          destruct (@term_get_val_spec Σ σ v); subst; try progress cbn
      | |- match @term_get_list ?Σ ?σ ?v with _ =>_ end ⊣⊢ _ =>
          destruct (@term_get_list_spec Σ σ v) as [[] ?|]; subst; try progress cbn
      | |- match @term_get_pair ?Σ ?σ₁ ?σ₂ ?v with _ =>_ end ⊣⊢ _ =>
          destruct (@term_get_pair_spec Σ σ₁ σ₂ v); subst; try progress cbn
      | |- match @term_get_record ?r ?Σ ?v with _ =>_ end ⊣⊢ _ =>
          destruct (@term_get_record_spec Σ r v); subst; try progress cbn
      | H: ?fst * ?snd |- _ =>
          destruct H; subst; try progress cbn
      end; try easy; auto.

  Lemma simplify_user_spec : SolverUserOnlySpec simplify_user.
  Proof.
    intros Σ p ts.
    destruct p; cbv in ts; env.destroy ts.
    cbn.
    unfold simplify_Q; lsolve.
    destruct a; lsolve.
    destruct v; lsolve.
  Qed.

  Definition solver : Solver :=
    solveruseronly_to_solver simplify_user.

  Lemma solver_spec : SolverSpec solver.
  Proof.
    apply solveruseronly_to_solver_spec, simplify_user_spec.
  Qed.
End ReplaySolverKit.

Module ReplaySolver := MakeSolver ReplayBase ReplaySig ReplaySolverKit.

Module Import ReplayExecutor :=
  MakeExecutor ReplayBase ReplayProgram ReplaySig ReplaySpecification ReplaySolver.
Module Import ReplayShallowExecutor :=
  MakeShallowExecutor ReplayBase ReplayProgram ReplaySig ReplaySpecification.

Lemma shallow_valid_contract_main : Shallow.ValidContract sep_contract_main (FunDef main).
Proof.
  cbn.
  intros.
  intros HQ.
  compute.
  exists v.
  split; auto.
  intros ->.
  unfold interp_Q in HQ.
  now cbn in HQ.
Qed.

Lemma symbolic_no_replay_valid_contract_main :
  VerificationCondition
    (postprocess
       (postprocess (SHeapSpecM.vcgen default_config 1 sep_contract_main (FunDef main)))).
Proof.
  compute. (* Output: replay would solve more than what we see here! Once we now the shape of the list, the Q predicate can be simplified in a way that makes the goal trivial to solve. *)
  constructor.
  compute.
  firstorder.
Qed.

Lemma symbolic_replay_valid_contract_main :
  VerificationCondition
    (postprocess
       (ReplayExecutor.Replay.replay (postprocess (SHeapSpecM.vcgen default_config 1 sep_contract_main (FunDef main))))).
Proof.
  compute. (* Output: with the replay functionality the residu VC is trivial. *)
  firstorder.
Qed.
