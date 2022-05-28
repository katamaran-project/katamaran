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
     Semantics.Registers
     Shallow.Executor
     Symbolic.Mutator
     Symbolic.Solver
     Symbolic.Worlds
     Symbolic.Propositions
     Specification
     Program
     Syntax.Predicates
     Syntax.ContractDecl.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** PROGRAM ***)

Import DefaultBase.

Module Import ExampleProgram <: Program DefaultBase.

  Section FunDeclKit.

    Inductive Fun : PCtx -> Ty -> Set :=
    | summaxlen : Fun [ "xs" ∷ ty.list ty.int ] (ty.prod (ty.prod ty.int ty.int) ty.int)
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳 : PCtx -> Set := fun _ => Empty_set.

  End FunDeclKit.

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

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | summaxlen => fun_summaxlen
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

End ExampleProgram.

Module Import ExampleSig <: ProgramLogicSignature DefaultBase.
  Module PROG := ExampleProgram.
  Import ctx.resolution.

  Include DefaultPredicateKit DefaultBase.
  Include ContractDeclMixin DefaultBase ExampleProgram.
  Include SpecificationMixin DefaultBase ExampleProgram.
End ExampleSig.

Module Import ExampleSpecification <: Specification DefaultBase ExampleSig.

  Import ctx.resolution.

  Definition sep_contract_summaxlen : SepContract [ "xs" ∷ ty.list ty.int ] (ty.prod (ty.prod ty.int ty.int) ty.int) :=
    {| sep_contract_logic_variables := ["xs" ∷ ty.list ty.int ];
       sep_contract_localstore      := [term_var "xs"];
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_match_prod
           (term_var "result") "sm" "l"
           (asn_match_prod
              (term_var "sm") "s" "m"
              (asn_sep
                 (asn_formula (formula_le (term_var "s") (term_binop bop.times (term_var "m") (term_var "l"))))
                 (asn_formula (formula_le (term_val ty.int 0) (term_var "l")))));
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | summaxlen => Some sep_contract_summaxlen
      end.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with end.

End ExampleSpecification.

Module ExampleSolverKit := DefaultSolverKit DefaultBase ExampleSig ExampleSpecification.
Module ExampleSolver := MakeSolver DefaultBase ExampleSig ExampleSpecification ExampleSolverKit.

Module Import ExampleExecutor :=
  MakeExecutor DefaultBase ExampleSig ExampleSpecification ExampleSolver.

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

Module Import ExampleShalExec := MakeShallowExecutor DefaultBase ExampleSig ExampleSpecification.
Import CMut.

Goal True. idtac "Timing before: summaxlen/shallow". Abort.
Lemma valid_contract_summaxlen_shallow : CMut.ValidContract 1 sep_contract_summaxlen fun_summaxlen.
Proof.
  compute - [negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge].
  solve; nia.
Qed.
Goal True. idtac "Timing after: summaxlen/shallow". Abort.

(* Goal True. idtac "Timing before: summaxlen/slow". Abort. *)
(* Lemma valid_contract_summaxlen_slow : SMut.ValidContract sep_contract_summaxlen fun_summaxlen. *)
(* Proof. *)
(*   compute. constructor. *)
(*   compute - [Z.mul Z.add Z.le Z.ge Z.lt]. *)
(*   solve; nia. *)
(* Time Qed. *)
(* Goal True. idtac "Timing after: summaxlen/slow". Abort. *)

Goal True. idtac "Timing before: summaxlen/symbolic". Abort.
Lemma valid_contract_summaxlen : SMut.ValidContract sep_contract_summaxlen fun_summaxlen.
Proof.
  apply SMut.validcontract_with_erasure_sound.
  hnf.
  compute. constructor.
  compute - [Z.mul Z.add Z.le Z.ge Z.lt].
  solve; nia.
Qed.
Goal True. idtac "Timing after: summaxlen/symbolic". Abort.

Section Debug.

  Goal CMut.ValidContract 1 sep_contract_summaxlen fun_summaxlen.
    compute - [negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge].
    change
      (forall xs : list Z, true = true ->
         (nil = xs -> exists (sm : Z * Z) (l : Z), (sm,l) = (0, 0, 0) /\
            (exists s m : Z, (s, m) = sm /\ s <= m * l /\ 0 <= l /\ True)) /\
      (forall (y : Z) (ys : list Z), y :: ys = xs -> exists ys' : list Z, ys' = ys /\ true = true /\
         (forall (sml : Z * Z * Z) (sm : Z * Z) (l : Z), (sm, l) = sml ->
          forall s m : Z, (s, m) = sm -> s <= m * l -> 0 <= l ->
          forall (sm' : Z * Z) (l' : Z), (sm', l') = sml -> forall s' m' : Z, (s',m') = sm' ->
          ((m' <? y) = true -> exists (sm'' : Z * Z) (l'' : Z), (sm'', l'') = (s' + y, y, l' + 1) /\
             (exists s'' m'' : Z, (s'', m'') = sm'' /\ s'' <= m'' * l'' /\ 0 <= l'' /\ True)) /\
          ((m' <? y) = false -> exists (sm'' : Z * Z) (l'' : Z), (sm'', l'') = (s' + y, m', l' + 1) /\
             (exists s'' m'' : Z, (s'', m'') = sm'' /\ s'' <= m'' * l'' /\ 0 <= l'' /\ True)))))%list.
    idtac "Shallow verification condition:".
    match goal with |- ?x => idtac x end.
  Abort.

  Import ty.
  Import SymProp.
  Import SymProp.notations.

  Goal SMut.ValidContract sep_contract_summaxlen fun_summaxlen.
    compute.
    idtac "Symbolic verification condition:".
    match goal with |- VerificationCondition ?x => idtac x end.
  Abort.

  Goal SMut.ValidContract sep_contract_summaxlen fun_summaxlen_with_debug.
    compute.
    idtac "Symbolic verification condition with debug nodes:".
    match goal with |- VerificationCondition ?x => idtac x end.
    idtac "Second debug node:".
    match goal with
    | |- context[SymProp.assumek
                   (formula_ge _ _)
                   (SymProp.debug (MkAMessage _ ?x) _)] =>
        idtac x
    end.
  Abort.

End Debug.
