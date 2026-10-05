(******************************************************************************)
(* Copyright (c) 2026 Dominique Devriese                                      *)
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

(* This file tests the linear programming solver from Staging.LinearProgramming.
   It contains a function [cycle] with a branch whose condition
   x <= y && y <= z && z < x is unsatisfiable. The unreachable branch returns a
   result that violates the contract, so the contract can only be verified
   fully automatically if the solver prunes that branch. The generic solver
   cannot do so, because the contradiction requires combining the three
   inequalities.

   The function [cycle_sep] is similar, but the inequalities x <= y and y <= z
   come from the precondition, and only z < x is assumed by the branch. The
   solver is only passed the newly assumed formulas, so it currently does not
   find the contradiction and this test fails. *)

From Stdlib Require Import
     Strings.String
     ZArith.ZArith.

From Katamaran Require Import
     Program
     Semantics.Registers
     Sep.Hoare
     Signature
     Staging.LinearProgramming
     Staging.Quote
     Symbolic.Solver
     Symbolic.Worlds
     Syntax.Predicates
     MicroSail.SymbolicExecutor.

From stdpp Require Import base.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Import DefaultBase.

Module Import ExampleProgram <: Program DefaultBase.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | cycle : Fun [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ] ty.int
    | cycle_sep : Fun [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ] ty.int.

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳 : PCtx -> Set := fun _ => Empty_set.
  End FunDeclKit.

  Include FunDeclMixin DefaultBase.

  Section FunDefKit.
    Import ctx.resolution.

    Local Coercion stm_exp : Exp >-> Stm.
    Local Notation "'x'" := (@exp_var _ "x" _ _) : exp_scope.
    Local Notation "'y'" := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'z'" := (@exp_var _ "z" _ _) : exp_scope.

    (* The then-branch is unreachable, and returns a result that violates the
       postcondition. *)
    Definition fun_cycle : Stm [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ] ty.int :=
      if: (x <= y) && (y <= z) && (z < x)
      then stm_val ty.int 0
      else stm_val ty.int 1.

    (* The then-branch is unreachable given the precondition x <= y and
       y <= z. *)
    Definition fun_cycle_sep : Stm [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ] ty.int :=
      if: z < x
      then stm_val ty.int 0
      else stm_val ty.int 1.

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | cycle => fun_cycle
      | cycle_sep => fun_cycle_sep
      end.
  End FunDefKit.

  Include DefaultRegStoreKit DefaultBase.

  Section ForeignKit.
    Definition Memory : Set := unit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. destruct f. Qed.
  End ForeignKit.

  Include ProgramMixin DefaultBase.

  Import callgraph.

  Lemma fundef_bindfree (Δ : PCtx) (τ : Ty) (f : Fun Δ τ) :
    stm_bindfree (FunDef f).
  Proof. destruct f; now vm_compute. Qed.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (Accessible 𝑭_call_graph f) :=
    match f with
    | cycle => None
    | cycle_sep => None
    end.

End ExampleProgram.

Module Import ExampleQuote.
  Include QuoteOn DefaultBase DefaultBase DefaultBase DefaultBase.
End ExampleQuote.

(* The predicates and worlds are defined separately, so that the solver module
   can be instantiated before the signature. *)
Module ExamplePreds.
  Include DefaultPredicateKit DefaultBase.
  Include PredicateMixin DefaultBase.
  Include WorldsMixin DefaultBase.
End ExamplePreds.

Module ExampleLP.
  Include LPSolverOn DefaultBase ExamplePreds ExamplePreds ExampleQuote.
End ExampleLP.

(* The signature uses the linear programming solver as the user-defined
   solver. *)
Module Import ExampleSig <: Signature DefaultBase.
  Include ExamplePreds.

  Definition solver : Solver := ExampleLP.solver_lp.
  Definition solver_spec : SolverSpec solver := ExampleLP.solver_lp_spec.

  Include SignatureMixin DefaultBase.
End ExampleSig.

Module Import ExampleProgramLogic :=
  MakeProgramLogic DefaultBase ExampleSig ExampleProgram.

(* The specification is parametrized over the signature, so that we can
   instantiate it both with the linear programming solver and with the default
   solver. *)
Module CycleSpecificationOn
  (Import SIG : Signature DefaultBase)
  (Import PL : ProgramLogic DefaultBase SIG ExampleProgram).

  Import ctx.resolution.
  Import asn.notations.

  Definition sep_contract_cycle : SepContract [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ] ty.int :=
    {| sep_contract_logic_variables := [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ];
       sep_contract_localstore      := [term_var "x"; term_var "y"; term_var "z"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   := term_var "result" = term_val ty.int 1;
    |}.

  Definition sep_contract_cycle_sep : SepContract [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ] ty.int :=
    {| sep_contract_logic_variables := [ "x" ∷ ty.int; "y" ∷ ty.int; "z" ∷ ty.int ];
       sep_contract_localstore      := [term_var "x"; term_var "y"; term_var "z"];
       sep_contract_precondition    :=
         term_var "x" <= term_var "y" ∗ term_var "y" <= term_var "z";
       sep_contract_result          := "result";
       sep_contract_postcondition   := term_var "result" = term_val ty.int 1;
    |}.

  Definition contract_environment : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | cycle => Some sep_contract_cycle
      | cycle_sep => Some sep_contract_cycle_sep
      end.

  Definition contract_environment_foreign : SepContractEnvEx :=
    fun Δ τ f => match f with end.

  Definition lemma_environment : LemmaEnv :=
    fun Δ l => match l with end.

  #[export] Instance example_specification : Specification :=
    {| CEnv   := contract_environment;
       CEnvEx := contract_environment_foreign;
       LEnv   := lemma_environment;
       fail_rule_pre := true;
    |}.

End CycleSpecificationOn.

Module Import ExampleSpecification :=
  CycleSpecificationOn ExampleSig ExampleProgramLogic.

Module Import ExampleExecutor :=
  MakeExecutor DefaultBase ExampleSig ExampleProgram ExampleProgramLogic.

(* The contract is verified by computation alone, which only succeeds because
   the solver prunes the unreachable branch. *)
Lemma valid_contract_cycle : Symbolic.ValidContractReflect sep_contract_cycle fun_cycle.
Proof. reflexivity. Qed.

(* TODO: this currently fails, because the solver does not take the formulas
   x <= y and y <= z from the path condition into account when assuming z < x.
   Replace by [Proof. reflexivity. Qed.] once it does. *)
Lemma valid_contract_cycle_sep : Symbolic.ValidContractReflect sep_contract_cycle_sep fun_cycle_sep.
Proof. Fail reflexivity. Abort.

(* As a sanity check, the same contract does not verify by computation alone
   with the default solver. *)
Module DefaultSolverCheck.
  Module Import DefaultSig <: Signature DefaultBase.
    Include DefaultPredicateKit DefaultBase.
    Include PredicateMixin DefaultBase.
    Include WorldsMixin DefaultBase.
    Include DefaultSolverKit DefaultBase.
    Include SignatureMixin DefaultBase.
  End DefaultSig.

  Module Import DefaultProgramLogic :=
    MakeProgramLogic DefaultBase DefaultSig ExampleProgram.

  Module Import DefaultSpecification :=
    CycleSpecificationOn DefaultSig DefaultProgramLogic.

  Module Import DefaultExecutor :=
    MakeExecutor DefaultBase DefaultSig ExampleProgram DefaultProgramLogic.

  Goal ~ Symbolic.ValidContractReflect sep_contract_cycle fun_cycle.
  Proof. vm_compute. discriminate. Qed.

  Goal ~ Symbolic.ValidContractReflect sep_contract_cycle_sep fun_cycle_sep.
  Proof. vm_compute. discriminate. Qed.
End DefaultSolverCheck.
