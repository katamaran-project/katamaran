(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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

(* This file contains the verification of the single summaxlen function. It is
   a function with a pure contract, and we can thus show a simple pure adequacy
   result for it. Unfortunately, this file has a lot of overhead instantiating
   the Iris model for a function that does not use separation logic. *)

From Coq Require Import
     Bool.Bool
     Lists.List
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Semantics.Registers
     Sep.Hoare
     Signature
     Specification
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Worlds
     Syntax.Predicates
     Syntax.Terms
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(* We use the default base because this example does not use any types other
   than the standard ones already available. We also don't make any use of
   registers (global variables). *)
Import DefaultBase.

(* The [Program] module defines the program consisting of only the [summaxlen]
   function. *)
Module Import ExampleProgram <: Program DefaultBase.

  Section FunDeclKit.

    Inductive Fun : PCtx -> Ty -> Set :=
    | summaxlen : Fun [ "xs" ∷ ty.list ty.int ] (ty.prod (ty.prod ty.int ty.int) ty.int)
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    (* We do not have any foreign functions. *)
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    (* We do not make use of explicit ghost lemmas in the program. *)
    Definition 𝑳 : PCtx -> Set := fun _ => Empty_set.

  End FunDeclKit.

  (* Include the definition of statements etc to define the body of [summaxlen]. *)
  Include FunDeclMixin DefaultBase.

  Section FunDefKit.
    Import ctx.resolution.

    Local Coercion stm_exp : Exp >-> Stm.
    Local Notation "'l'"   := (@exp_var _ "l" _ _) : exp_scope.
    Local Notation "'m'"   := (@exp_var _ "m" _ _) : exp_scope.
    Local Notation "'s'"   := (@exp_var _ "s" _ _) : exp_scope.
    Local Notation "'sm'"   := (@exp_var _ "sm" _ _) : exp_scope.
    Local Notation "'sml'"   := (@exp_var _ "sml" _ _) : exp_scope.
    Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'xs'"   := (@exp_var _ "xs" _ _) : exp_scope.
    Local Notation "'ys'"   := (@exp_var _ "ys" _ _) : exp_scope.

    (* The implementation of the [summaxlen] function as a μSail statement. *)
    Definition fun_summaxlen : Stm ["xs" ∷ ty.list ty.int] (ty.prod (ty.prod ty.int ty.int) ty.int) :=
      stm_match_list xs (stm_val (ty.prod (ty.prod ty.int ty.int) ty.int) (0,0,0))
        "y" "ys"
        (let: "sml" := call summaxlen ys in
         match: sml in (ty.prod ty.int ty.int , ty.int) with
         | ("sm","l") =>
           match: sm in (ty.int,ty.int) with
           | ("s","m") =>
             let: "m'" := if: m < y then y else m in
             exp_binop bop.pair (exp_binop bop.pair (s + y) (exp_var "m'")) (l + exp_int 1)
           end
         end).

    (* A variant of the [summaxlen] function to demonstrate the explicit debug ghost statement. *)
    Definition fun_summaxlen_with_debug : Stm ["xs" ∷ ty.list ty.int] (ty.prod (ty.prod ty.int ty.int) ty.int) :=
      stm_match_list xs (stm_val (ty.prod (ty.prod ty.int ty.int) ty.int) (0,0,0))
        "y" "ys"
        (let: "sml" := call summaxlen ys in
         match: sml in (ty.prod ty.int ty.int , ty.int) with
         | ("sm","l") =>
             match: sm in (ty.int,ty.int) with
             | ("s","m") =>
                 let: "m'" := if: m < y then y else m in
                 stm_debugk (exp_binop bop.pair (exp_binop bop.pair (s + y) (exp_var "m'")) (l + exp_int 1))
             end
         end).

    (* The library expects a map [FunDef] from function names to function bodies. *)
    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | summaxlen => fun_summaxlen
      end.

  End FunDefKit.

  (* We pull in the default implementation of a store for registers. *)
  Include DefaultRegStoreKit DefaultBase.

  (* We do not have any foreign functions in this example and therefore
     instantiate the library with some dummy definitions. *)
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
    Is_true (stm_bindfree (FunDef f)).
  Proof. destruct f; now vm_compute. Qed.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (Accessible 𝑭_call_graph f) :=
    match f with
    | summaxlen => None
    end.

End ExampleProgram.

(* The program logic signature contains all the necessary definitions
   pertaining to user-defined pure and spatial predicates. We do not have
   any in this example, so use default definitions provided by the library. *)
Module Import ExampleSig <: Signature DefaultBase.
  Include DefaultPredicateKit DefaultBase.
  Include PredicateMixin DefaultBase.
  Include WorldsMixin DefaultBase.
  (* We do not provide any user-defined simplifier/solver. Just rely on the
     generic one defined by the framework. *)
  Include DefaultSolverKit DefaultBase.
  Include SignatureMixin DefaultBase.
End ExampleSig.

(* The specification module defines the contract for the [summaxlen] function. *)
Module Import ExampleSpecification <: Specification DefaultBase ExampleSig ExampleProgram.
  Include SpecificationMixin DefaultBase ExampleSig ExampleProgram.

  Import ctx.resolution.
  Import asn.notations.

  Definition sep_contract_summaxlen : SepContract [ "xs" ∷ ty.list ty.int ] (ty.prod (ty.prod ty.int ty.int) ty.int) :=
    {| sep_contract_logic_variables := ["xs" ∷ ty.list ty.int ];
       sep_contract_localstore      := [term_var "xs"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn.match_prod
           (term_var "result") "sm" "l"
           (asn.match_prod
              (term_var "sm") "s" "m"
              (term_var "s" <= term_binop bop.times (term_var "m") (term_var "l") ∗
               term_val ty.int 0 <= term_var "l"));
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | summaxlen => Some sep_contract_summaxlen
      end.

  (* No foreign functions. *)
  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with end.

  (* No ghost lemmas. *)
  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with end.

End ExampleSpecification.

(* Use the specification and the solver module to compose the symbolic executor
   and symbolic verification condition generator. *)
Module Import ExampleExecutor :=
  MakeExecutor DefaultBase ExampleSig ExampleProgram ExampleSpecification.

(* Some simple Ltac tactic to solve the shallow and symbolic VCs. *)
Local Ltac solve :=
  repeat
    (repeat
       match goal with
       | H: _ /\ _ |- _ => destruct H
       | H: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
       | H: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
       | H: pair _ _ = pair _ _ |- _ => inversion H; subst; clear H
       | H: ?x = ?x |- _ => clear H
       | |- forall _, _ => intro
       | |- exists _, _ => eexists
       | |- _ /\ _ => constructor
       | |- _ = _  => reflexivity
       end;
     try progress subst);
  auto.

(* Also instantiate the shallow verification condition generator. *)
Module Import ExampleShalExec :=
  MakeShallowExecutor DefaultBase ExampleSig ExampleProgram ExampleSpecification.

(* This computes and proves the shallow VC. Make sure to not unfold the
   definition of the binary operators and Coq predicates used in the example. *)
Goal True. idtac "Timing before: summaxlen/shallow". Abort.
Lemma valid_contract_summaxlen_shallow : Shallow.ValidContract sep_contract_summaxlen fun_summaxlen.
Proof.
  compute - [negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge].
  solve; nia.
Qed.
Goal True. idtac "Timing after: summaxlen/shallow". Abort.

(* This computes and proves the symbolic VC. Note that this VC is not solved
   completely automatically. The VCG returns a residual VC that we still need to
   proof manually in Coq. This VC however is simpler than the shallow one
   generated above. *)
Goal True. idtac "Timing before: summaxlen/symbolic". Abort.
Lemma valid_contract_summaxlen : Symbolic.ValidContract sep_contract_summaxlen fun_summaxlen.
Proof.
  (* Interactive handling of the instrinsically-typed term representation used
     throughout the Katamaran codebase is unfortunately very slow. Therefore, we
     calculate a symbolic proposition with some of the typing information
     removed. Specifically, we remove the context containment proofs from the
     variable case of symbolic terms and all variable context indexing. When
     transforming the symbolic propositions to shallow ones, we simply
     re-typecheck the variable case. *)
  apply Symbolic.validcontract_with_erasure_sound.
  compute. constructor.
  compute - [Z.mul Z.add Z.le Z.ge Z.lt].
  (* We solve the remaining obligations using nia. *)
  solve; nia.
Qed.
Goal True. idtac "Timing after: summaxlen/symbolic". Abort.

Section Debug.

  (* A simple goal to print the shallow verification condition. *)
  Goal Shallow.ValidContract sep_contract_summaxlen fun_summaxlen.
    compute - [negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge].
    (* We change the goal here to give more descriptive names to the quantified variables. Coq's
       type checker makes sure that this is definitionally equal to the computed goal. *)
    change
      (forall xs : list Z, true = true ->
         (nil = xs -> exists (sm : Z * Z) (l : Z), (sm,l) = (0, 0, 0) /\
            (exists s m : Z, (s, m) = sm /\ s <= m * l /\ 0 <= l /\ True)) /\
      (forall (y : Z) (ys : list Z), y :: ys = xs -> exists ys' : list Z, ys' = ys /\ true = true /\
         (forall (sml : Z * Z * Z) (sm : Z * Z) (l : Z), (sm, l) = sml ->
          forall s m : Z, (s, m) = sm -> s <= m * l -> 0 <= l ->
          forall (sm' : Z * Z) (l' : Z), (sm', l') = sml -> forall s' m' : Z, (s',m') = sm' ->
          (true = (m' <? y) -> exists (sm'' : Z * Z) (l'' : Z), (sm'', l'') = (s' + y, y, l' + 1) /\
             (exists s'' m'' : Z, (s'', m'') = sm'' /\ s'' <= m'' * l'' /\ 0 <= l'' /\ True)) /\
          (false = (m' <? y) -> exists (sm'' : Z * Z) (l'' : Z), (sm'', l'') = (s' + y, m', l' + 1) /\
             (exists s'' m'' : Z, (s'', m'') = sm'' /\ s'' <= m'' * l'' /\ 0 <= l'' /\ True)))))%list.
    idtac "Shallow verification condition:".
    match goal with |- ?x => idtac x end.
  Abort.

  Import ty.
  Import SymProp.
  Import SymProp.notations.

  (* Simple goal to print the produced symbolic VC. This is essentially like
     [Lemma valid_contract_summaxlen], but without the erasure step. *)
  Goal Symbolic.ValidContract sep_contract_summaxlen fun_summaxlen.
    compute.
    idtac "Symbolic verification condition:".
    match goal with |- VerificationCondition ?x => idtac x end.
  Abort.

  (* Print the VC for the variant of the [summaxlen] function that contains the
     explicit debug ghost statement. *)
  Goal Symbolic.ValidContract sep_contract_summaxlen fun_summaxlen_with_debug.
    compute.
    idtac "Symbolic verification condition with debug nodes:".
    match goal with |- VerificationCondition ?x => idtac x end.
    idtac "Second debug node:".
    match goal with
    | |- context[SymProp.assumek
                   (formula_relop bop.le _ _)
                   (SymProp.debug (amsg.mk ?x) _)] =>
        idtac x
    end.
  Abort.

End Debug.

(* Instantiate the operational semantics. *)
Module ExampleSemantics <: Semantics DefaultBase ExampleProgram :=
  MakeSemantics DefaultBase ExampleProgram.

(* This module contains the instantiation of the Iris model with trivial
   definitions for this example. *)
Module Import ExampleModel.

  Import ExampleProgram.
  Import ExampleSpecification.
  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.base_logic.lib.gen_heap.
  Import iris.proofmode.tactics.

  (* There is no memory, so use trivial definitions to instantiate the ghost
     state and its requirements. *)
  Module Import ExampleIrisBase <: IrisBase DefaultBase ExampleProgram ExampleSemantics.

    Include IrisPrelims DefaultBase ExampleProgram ExampleSemantics.

    Definition memGS : gFunctors -> Set := fun Σ => True.
    Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ := fun Σ mG μ => True%I.

    (* Combine the memory and register ghost states. *)
    Include IrisResources DefaultBase ExampleProgram ExampleSemantics.
    Include IrisWeakestPre DefaultBase ExampleProgram ExampleSemantics.
    Include IrisTotalWeakestPre DefaultBase ExampleProgram ExampleSemantics.
    Include IrisTotalPartialWeakestPre DefaultBase ExampleProgram ExampleSemantics.

  End ExampleIrisBase.

  Module ExampleIrisAdeqParams <: IrisAdeqParameters DefaultBase ExampleIrisBase.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.tactics.

    Definition memGpreS : gFunctors -> Set := fun Σ => True.
    Definition memΣ : gFunctors := gFunctors.nil.
    Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ := fun _ _ => I.
    Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ := fun Σ mG μ => True%I.
    Lemma mem_inv_init `{gHP : memGpreS Σ} (μ : Memory) :
      ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
    Proof. now iStartProof. Qed.
  End ExampleIrisAdeqParams.


  (* Finally, include the constructed operational model, the axiomatic program
     logic, and the Iris implementation of the axioms. *)
  Module Import ExampleIrisInstance <:
    IrisInstance DefaultBase ExampleSig ExampleProgram ExampleSemantics
      ExampleIrisBase ExampleIrisAdeqParams.

    (* There are no user-defined spatial predicates, also use trivial definitions
       here. *)
    Section ExampleIrisPredicates.
      Import iris.base_logic.lib.iprop.
      Definition luser_inst : forall `{sRG : sailRegGS Σ} `{fancy_updates.invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ :=
        fun Σ sRG iG mG p ts => match p with end.
      Definition lduplicate_inst : forall `{sRG : sailRegGS Σ} `{fancy_updates.invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
          is_duplicable p = true -> bi_entails (luser_inst (sRG := sRG) mG _ ts) (luser_inst (sRG := sRG) mG _ ts ∗ luser_inst (sRG := sRG) mG _ ts) :=
        fun Σ sRG iG mG p ts dup => match p with end.
    End ExampleIrisPredicates.

    Include IrisSignatureRules DefaultBase ExampleSig ExampleProgram
      ExampleSemantics ExampleIrisBase.
    Include IrisAdequacy DefaultBase ExampleSig ExampleProgram ExampleSemantics
      ExampleIrisBase ExampleIrisAdeqParams.
    Include ProgramLogicOn DefaultBase ExampleSig ExampleProgram ExampleSpecification.
    Include IrisInstanceWithContracts DefaultBase ExampleSig ExampleProgram
      ExampleSemantics ExampleSpecification ExampleIrisBase ExampleIrisAdeqParams.

    (* Verification of the absent foreign functions. *)
    Lemma foreignSem `{sailGS Σ} : ForeignSem.
    Proof. intros Δ τ f; destruct f. Qed.

    (* Verification of the absent ghost lemmas. *)
    Lemma lemSem `{sailGS Σ} : LemmaSem.
    Proof. intros Γ l. destruct l. Qed.

    (* Import the soundness proofs for the shallow and symbolic executors. *)
    Include MicroSail.ShallowSoundness.Soundness DefaultBase ExampleSig ExampleProgram
      ExampleSpecification ExampleShalExec.
    Include MicroSail.RefineExecutor.RefineExecOn DefaultBase ExampleSig
      ExampleProgram ExampleSpecification ExampleShalExec ExampleExecutor.

    (* Show that all the contracts are sound in the Iris model. *)
    Lemma contracts_sound `{sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
    Proof.
      apply (sound foreignSem lemSem).
      intros Γ τ f c.
      destruct f; inversion 1; subst.
      apply shallow_vcgen_soundness.
      apply symbolic_vcgen_soundness.
      apply valid_contract_summaxlen.
    Qed.

    Import ExampleSemantics.SmallStepNotations.

    (* This is an adequacy proposition that holds for functions with a pure
       contract, i.e. a contract that does not use any spatial predicates. For
       such function an contracts we can state adequacy just in terms of the
       operational semantics without exposing other parts of the Iris model. *)
    Definition adequacy_pure_prop (Δ : PCtx) (σ : Ty) (f : Fun Δ σ) : Prop :=
      match CEnv f with
      | Some (MkSepContract _ _ Σ args pre result post) =>
          asn.is_pure pre -> asn.is_pure post ->
          (* The Γ is the caller's program context and δ, δ' the caller's
             local variable stores. *)
          forall Γ (δ δ' : CStore Γ)
            (γ γ' : RegStore) (μ μ' : Memory) (ι : Valuation Σ),
            asn.interpret_pure pre ι ->
            forall v,
              (* We could make it more general and allow arbitrary expressions
              as the arguments instead of values. But this is just form
              demonstration purposes. *)
              ⟨ γ, μ, δ, stm_call f (env.map (fun _ => exp_val _) (inst args ι)) ⟩
                --->*
              ⟨ γ', μ', δ', stm_val σ v ⟩  ->
              asn.interpret_pure post ι.[result∷σ ↦ v]
                (* removed the following: annoying to express in a contract... *)
                (* /\ δ = δ' *)
      | None => True
      end.

    Lemma interpret_assertion_pure_or_not `{sailGS Σ} {Γ} A (Hasn : asn.is_pure A) (ι : Valuation Γ) :
      asn.interpret A ι ⊣⊢ (⌜ asn.interpret_pure A ι ⌝)%I.
    Proof. now apply asn.interpret_pure_equiv, Is_true_eq_true. Qed.

    (* Derive the pure adequacy lemma from the more general lemma
       ExampleModel.adequacy defined in the library. *)
    Lemma adequacy_pure {Δ σ} (f : Fun Δ σ) : adequacy_pure_prop f.
    Proof.
      unfold adequacy_pure_prop.
      destruct (CEnv f) as [[Σ args pre result post]|] eqn:Heqc; [|easy].
      intros preP postP Γ δ δ' γ γ' μ μ' ι PRE v evals.
      refine (adequacy
                (Q := fun v => asn.interpret_pure post ι.[result∷σ ↦ v]) evals I _).
      iIntros (Σ' sG).
      iApply (iris_rule_stm_call _ _ _ _ Heqc).
      - cbn.
        iIntros "_".
        iExists ι.
        unfold DefaultBase.evals.
        rewrite env.map_map env.map_id.
        rewrite interpret_assertion_pure_or_not; auto.
        iSplit; [trivial|].
        iSplitL; [trivial|].
        iIntros (v0) "post".
        rewrite interpret_assertion_pure_or_not; auto.
      - iApply contracts_sound.
    Qed.

    (* Finally, instantitate the pure adequacy lemma for the summaxlen example. *)
    Corollary summaxlen_adequacy {Γ} (δ : CStore Γ) (γ γ' : RegStore) (μ μ' : Memory) :
      forall (xs : list Z) (s m l : Z),
        ⟨ γ, μ, δ, call summaxlen (exp_val (ty.list ty.int) xs) ⟩ --->*
       ⟨ γ', μ', δ, stm_val (ty.prod (ty.prod ty.int ty.int) ty.int) (s, m, l) ⟩ ->
        (s ≤ m * l)%Z /\ (0 ≤ l)%Z.
    Proof.
      intros xs s m l Hsteps.
      generalize (adequacy_pure summaxlen I I Γ δ δ γ γ' μ μ' (env.snoc env.nil _ xs) eq_refl _ Hsteps).
      cbn. intuition.
    Qed.

  End ExampleIrisInstance.

  Goal True.
    idtac "Assumptions for symbolic_vcgen_soundness:". Print Assumptions symbolic_vcgen_soundness.
    idtac "Assumptions for shallow_vcgen_soundness:". Print Assumptions shallow_vcgen_soundness.
    idtac "Assumptions for summaxlen_adequacy:". Print Assumptions summaxlen_adequacy.
  Abort.

End ExampleModel.

(* This tactic calculates the number of different execution branches explored by
   the shallow and symbolic executor for the body of the function [fn]. *)
Ltac calcstats fn :=
  let smb := eval compute in (Symbolic.Statistics.calc fn) in
  let shl := Shallow.Statistics.calc fn in
  let row := constr:(pair fn (pair shl smb)) in
  idtac row.

(* We print the statistics for every μSail function defined in the program, i.e.
   just the [summaxlen] function in this case. *)
Goal forall {Δ τ} (f : Fun Δ τ), f = f.
  idtac "Branching statistics:".
  destruct f;
    match goal with
    |- ?g = _ => calcstats g
    end.
Abort.
