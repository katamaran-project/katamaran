(******************************************************************************)
(* Copyright (c) 2021 Steven Keuchel                                          *)
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
     Notations
     Semantics.Registers
     Shallow.Executor
     Shallow.Soundness
     Symbolic.Executor
     Symbolic.Solver
     Symbolic.Worlds
     Symbolic.Propositions
     Symbolic.Soundness
     Program
     Specification
     Sep.Hoare
     Sep.Logic
     Semantics
     Iris.Model.

From stdpp Require decidable finite list fin_maps infinite.
From iris.proofmode Require string_ident tactics.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Local Open Scope string_scope.

(*** TERMS ***)

Import DefaultBase.
Notation ptr   := ty.int.
Notation llist := (ty.option ptr).

Module Import ExampleProgram <: Program DefaultBase.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | append      : Fun [ "p" ∷ llist; "q" ∷ llist ] llist
    | appendloop  : Fun [ "p" ∷ ptr; "q" ∷ llist ] ty.unit
    | length      : Fun [ "p" ∷ llist ] ty.int
    | copy        : Fun [ "p" ∷ llist ] llist
    | reverse     : Fun [ "p" ∷ llist ] llist
    | reverseloop : Fun [ "p" ∷ llist; "q" ∷ llist ] llist
    .

    Inductive FunX : PCtx -> Ty -> Set :=
    | mkcons : FunX [ "x" ∷ ty.int; "xs" ∷ llist ] ptr
    | fst    : FunX [ "p" ∷ ptr ] ty.int
    | snd    : FunX [ "p" ∷ ptr ] llist
    (* | setfst : FunX [ "p" ∷ ptr, "x" ∷ ty.int ] ty.unit *)
    | setsnd : FunX [ "p" ∷ ptr; "xs" ∷ llist ] ty.unit
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := FunX.

    Inductive Lem : NCtx 𝑿 Ty -> Set :=
    | open_nil      : Lem [ ]
    | open_cons     : Lem [ "p" ∷ ptr ]
    | close_nil     : Lem [ "p" ∷ ty.unit ]
    | close_cons    : Lem [ "p" ∷ ptr ].

    Definition 𝑳 : NCtx 𝑿 Ty -> Set := Lem.

  End FunDeclKit.

  Include FunDeclMixin DefaultBase.

  Section FunDefKit.

    Local Coercion stm_exp : Exp >-> Stm.

    Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
    Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

    Notation "'lemma' f args" := (stm_lemma f args%env) (at level 10, f at next level) : exp_scope.

    Definition fun_append : Stm [ "p" ∷ llist; "q" ∷ llist ] llist :=
      match: exp_var "p" with
      | inl "x" =>
        call appendloop (exp_var "x") (exp_var "q") ;;
        exp_var "p"
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        exp_var "q"
      end.

    Definition fun_appendloop : Stm [ "p" ∷ ptr; "q" ∷ llist ] ty.unit :=
      lemma open_cons [exp_var "p"] ;;
      let: "mbn" := foreign snd (exp_var "p") in
      match: (exp_var "mbn") with
      | inl "x" => call appendloop (exp_var "x") (exp_var "q")
      | inr "tt" =>
          lemma close_nil [exp_var "tt"] ;;
          foreign setsnd (exp_var "p") (exp_var "q")
      end;;
      lemma close_cons [exp_var "p"].

    Definition fun_appendloop_broken : Stm [ "p" ∷ ptr; "q" ∷ llist ] ty.unit :=
      (* lemma open_cons [exp_var "p"] ;; *)
      let: "mbn" := foreign snd (exp_var "p") in
      match: (exp_var "mbn") with
      | inl "x" => call appendloop (exp_var "x") (exp_var "q")
      | inr "tt" =>
          lemma close_nil [exp_var "tt"] ;;
          foreign setsnd (exp_var "p") (exp_var "q")
      end;;
      lemma close_cons [exp_var "p"].

    Definition fun_length : Stm [ "p" ∷ llist ] ty.int :=
      match: exp_var "p" with
      | inl "x" =>
        lemma open_cons [exp_var "x"] ;;
        let: "t" := foreign snd (exp_var "x") in
        let: "r" := call length (exp_var "t") in
        lemma close_cons [exp_var "x"] ;;
        exp_binop bop.plus (exp_val ty.int 1%Z) (exp_var "r")
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        lemma open_nil [] ;;
        stm_val ty.int 0%Z
      end.

    Definition fun_copy : Stm [ "p" ∷ llist ] llist :=
      match: exp_var "p" with
      | inl "x" =>
        lemma open_cons [exp_var "x"] ;;
        let: "h"  := foreign fst (exp_var "x") in
        let: "t"  := foreign snd (exp_var "x") in
        let: "t'" := call copy (exp_var "t") in
        let: "x'" := foreign mkcons (exp_var "h") (exp_var "t'") in
        lemma close_cons [exp_var "x"] ;;
        lemma close_cons [exp_var "x'"] ;;
        exp_inl (exp_var "x'")
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        lemma open_nil [] ;;
        lemma open_nil [] ;;
        exp_val llist (inr tt)
      end.

    Definition fun_reverse : Stm [ "p" ∷ llist ] llist :=
      lemma open_nil [] ;;
      call reverseloop (exp_var "p") (exp_val llist (inr tt)).

    Definition fun_reverseloop : Stm [ "p" ∷ llist; "q" ∷ llist ] llist :=
      match: exp_var "p" with
      | inl "x" =>
        lemma open_cons [exp_var "x"] ;;
        let: "n"  := foreign snd (exp_var "x") in
        foreign setsnd (exp_var "x") (exp_var "q");;
        lemma close_cons [exp_var "x"] ;;
        call reverseloop (exp_var "n") (exp_inl (exp_var "x"))
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        exp_var "q"
      end.

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | append     => fun_append
      | appendloop => fun_appendloop
      | length     => fun_length
      | copy       => fun_copy
      | reverse     => fun_reverse
      | reverseloop => fun_reverseloop
      end.

  End FunDefKit.

  Include DefaultRegStoreKit DefaultBase.

  Section ForeignKit.

    Import iris.proofmode.tactics.
    Definition Memory : Set := gmap Z (Z * (Z + unit)).

    Equations(noeqns) ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop :=
      ForeignCall mkcons (env.snoc (env.snoc env.nil _ x) _ xs) res γ γ' μ μ' :=
        let next := infinite_fresh (elements (dom (gset Z) μ)) in
        γ' = γ /\
        μ' = (<[next := (x, xs)]> μ) /\
        res = inr next;
      ForeignCall fst (env.snoc env.nil _ z) res γ γ' μ μ' :=
        match μ !! z with
        | None          => res = inl "Invalid pointer"
        | Some (head,_) => γ' = γ /\ μ' = μ /\ res = inr head
        end;
      ForeignCall snd (env.snoc env.nil _ z) res γ γ' μ μ' :=
        match μ !! z with
        | None          => res = inl "Invalid pointer"
        | Some (_,next) => γ' = γ /\ μ' = μ /\ res = inr next
        end;
      ForeignCall setsnd (env.snoc (env.snoc env.nil _ z) _ xs) res γ γ' μ μ' :=
        match (μ !! z) with
        | None => res = inl "Invalid pointer"
        | Some (elem, _) => γ' = γ /\  μ' = <[z := (elem, xs)]> μ /\ res = inr tt
        end.

    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof.
      destruct f; env.destroy args; cbn;
        try match goal with
            | |- context[match ?disc with _ => _ end] =>
                lazymatch disc with
                (* Destruct the lookup first before creating the evars using eexists. *)
                | lookup _ _ => destruct disc as [[elem next]|] eqn:?
                end
            end;
        repeat
          lazymatch goal with
          | |- _ = _ => reflexivity
          | |- _ /\ _ => split
          | |- exists _, _ => eexists
          end; auto.
    Qed.

  End ForeignKit.

  Include ProgramMixin DefaultBase.

End ExampleProgram.

Inductive PurePredicate : Set :=
| plength
| preverse
| preverseappend
.

Inductive Predicate : Set :=
| ptstocons
| ptstolist
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Import ExampleSignature <: ProgramLogicSignature DefaultBase.
  Module PROG := ExampleProgram.
  Import DefaultBase.

  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | plength => [ty.list ty.int; ty.int]
    | preverse => [ty.list ty.int; ty.list ty.int]
    | preverseappend => [ty.list ty.int; ty.list ty.int; ty.list ty.int]
    end.
  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
    match p with
    | plength => fun xs l => Z.of_nat (Datatypes.length xs) = l
    | preverse => fun xs ys => ys = rev xs
    | preverseappend => fun xs ys zs => zs = rev_append xs ys
    end.

  Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Section HeapPredicateDeclKit.

    Definition 𝑯 := Predicate.
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstocons => [ptr; ty.int; llist]
      | ptstolist => [llist; ty.list ty.int]
      end.
    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.
    Global Instance 𝑯_is_dup : IsDuplicable 𝑯 :=
      {| is_duplicable p := false |}.

    Local Arguments Some {_} &.
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptstocons => Some (MkPrecise [ptr] [ptr; llist] eq_refl)
      | ptstolist => Some (MkPrecise [llist] [ty.list ptr] eq_refl)
      end.

  End HeapPredicateDeclKit.

  Include ContractDeclMixin DefaultBase ExampleProgram.
  Include SpecificationMixin DefaultBase ExampleProgram.
End ExampleSignature.

Module Import ExampleSpecification <: Specification DefaultBase ExampleSignature.
  Section ContractDefKit.

    Import ctx.resolution.

    Local Notation "p '↦l' xs" := (asn_chunk (chunk_user ptstolist (env.nil ► (llist ↦ p) ► (ty.list ty.int ↦ xs)))) (at level 70).
    Local Notation "p '∗' q" := (asn_sep p q).
    Local Notation "p '↦p' ( x , xs )" := (asn_chunk (chunk_user ptstocons (env.nil ► (ptr ↦ p) ► (ty.int ↦ x) ► (llist ↦ xs)))) (at level 70).

    Arguments formula_prop [Σ] Σ' ζ _.

    Definition asn_append {Σ : LCtx} (xs ys zs : Term Σ (ty.list ty.int)) : Assertion Σ :=
      asn_formula (formula_eq (term_binop bop.append xs ys) zs).

    Definition sep_contract_append : SepContract [ "p" ∷ llist; "q" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "q" ∷ llist; "xs" ∷ ty.list ty.int; "ys" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"; term_var "q"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_exist "zs" (ty.list ty.int)
             (term_var "result" ↦l term_var "zs" ∗
              asn_append (term_var "xs") (term_var "ys") (term_var "zs"));
      |}.

    Definition sep_contract_appendloop : SepContract [ "p" ∷ ptr; "q" ∷ llist ] ty.unit :=
      {| sep_contract_logic_variables := ["p" ∷ ptr; "q" ∷ llist; "xs" ∷ ty.list ty.int; "ys" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"; term_var "q"];
         sep_contract_precondition    := term_inl (term_var "p") ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_val ty.unit tt)) ∗
           asn_exist "zs" (ty.list ty.int)
             (term_inl (term_var "p") ↦l term_var "zs" ∗
              asn_append (term_var "xs") (term_var "ys") (term_var "zs"));
      |}.

    Definition sep_contract_length : SepContract [ "p" ∷ llist ] ty.int :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "xs" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_user plength [term_var "xs"; term_var "result"]) ∗
           term_var "p" ↦l term_var "xs"
      |}.

    Definition sep_contract_copy : SepContract [ "p" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "xs" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           term_var "p" ↦l term_var "xs" ∗
           term_var "result" ↦l term_var "xs"
      |}.

    Definition sep_contract_reverse : SepContract [ "p" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "xs" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs";
         sep_contract_result          := "r";
         sep_contract_postcondition   :=
           asn_exist "zs" (ty.list ty.int)
             (term_var "r" ↦l term_var "zs" ∗
              asn_formula (formula_user preverse [term_var "xs"; term_var "zs"]));
      |}.

    Definition sep_contract_reverseloop : SepContract [ "p" ∷ llist; "q" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "q" ∷ llist; "xs" ∷ ty.list ty.int; "ys" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"; term_var "q"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "r";
         sep_contract_postcondition   :=
           asn_exist "zs" (ty.list ty.int)
             (term_var "r" ↦l term_var "zs" ∗
              asn_formula (formula_user preverseappend [term_var "xs"; term_var "ys"; term_var "zs"]));
      |}.

    Definition sep_contract_mkcons : SepContract [ "x" ∷ ty.int; "xs" ∷ llist ] ptr :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "x"; term_var "xs"];
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "p";
         sep_contract_postcondition   := term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_fst : SepContract [ "p" ∷ ptr ] ty.int :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "xs" );
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_var "x")) ∗
           term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_snd : SepContract [ "p" ∷ ptr ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "xs" );
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_var "xs")) ∗
           term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_setsnd : SepContract [ "p" ∷ ptr; "xs" ∷ llist ] ty.unit :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"; term_var "xs"];
         sep_contract_precondition    := asn_exist "ys" llist (term_var "p" ↦p ( term_var "x" , term_var "ys"));
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
         asn_formula (formula_eq (term_var "result") (term_val ty.unit tt)) ∗
         term_var "p" ↦p ( term_var "x" , term_var "xs");
      |}.

    Definition sep_lemma_open_nil : Lemma [ ] :=
      {| lemma_logic_variables := [];
         lemma_patterns        := [];
         lemma_precondition    := asn_true;
         lemma_postcondition   := term_val llist (inr tt) ↦l term_val (ty.list ty.int) nil;
      |}.

    Definition sep_lemma_open_cons : Lemma [ "p" ∷ ptr ] :=
      {| lemma_logic_variables := ["p" ∷ ty.int; "xs" ∷ ty.list ty.int];
         lemma_patterns        := [term_var "p"];
         lemma_precondition    := term_inl (term_var "p") ↦l term_var "xs";
         lemma_postcondition   :=
           asn_match_list (term_var "xs")
             asn_false
             "y" "ys"
             (asn_exist "n" llist
                (term_var "p" ↦p (term_var "y", term_var "n") ∗
                term_var "n" ↦l term_var "ys"))
      |}.

    Definition sep_lemma_close_cons : Lemma [ "p" ∷ ptr ] :=
      {| lemma_logic_variables := ["p" ∷ ptr; "x" ∷ ty.int; "xs" ∷ ty.list ty.int; "n" ∷ llist ];
         lemma_patterns        := [term_var "p"];
         lemma_precondition    := term_var "p" ↦p (term_var "x" , term_var "n") ∗
                                  term_var "n" ↦l term_var "xs";
         lemma_postcondition   := term_inl (term_var "p") ↦l term_binop bop.cons (term_var "x") (term_var "xs")
      |}.

    Definition sep_lemma_close_nil : Lemma [ "p" ∷ ty.unit ] :=
      {| lemma_logic_variables := ["p" ∷ ty.unit; "xs" ∷ ty.list ty.int ];
         lemma_patterns        := [term_var "p"];
         lemma_precondition    := term_inr (term_var "p") ↦l term_var "xs";
         lemma_postcondition   :=
           asn_formula (formula_eq (term_var "p") (term_val ty.unit tt)) ∗
           asn_formula (formula_eq (term_var "xs") (term_val (ty.list ty.int) nil))
      |}.

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | append     => Some (sep_contract_append)
        | appendloop => Some (sep_contract_appendloop)
        | length     => Some (sep_contract_length)
        | copy       => Some (sep_contract_copy)
        | reverse    => Some (sep_contract_reverse)
        | reverseloop => Some (sep_contract_reverseloop)
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | mkcons => sep_contract_mkcons
        | fst => sep_contract_fst
        | snd => sep_contract_snd
        | setsnd => sep_contract_setsnd
        end.

    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with
        | open_nil => sep_lemma_open_nil
        | open_cons => sep_lemma_open_cons
        | close_cons => sep_lemma_close_cons
        | close_nil => sep_lemma_close_nil
        end.

  End ContractDefKit.

End ExampleSpecification.

Module ExampleSolverKit <: SolverKit DefaultBase ExampleSignature ExampleSpecification.

  Local Unset Implicit Arguments.
  Set Equations Transparent.
  Import ListNotations.

  Equations simplify_plength {Σ} (xs : Term Σ (ty.list ty.int)) (n : Term Σ ty.int) : option (List Formula Σ) :=
  | term_binop bop.cons x xs | term_binop bop.plus (term_val ?(ty.int) 1%Z) n :=
    Some [formula_user plength (env.nil ► (_ ↦ xs) ► (ty.int ↦ n))]%list;
  | term_val ?(ty.list ty.int) nil | term_val ?(ty.int) 0%Z := Some nil;
  | xs          | n          :=
    Some [formula_user plength (env.nil ► (_ ↦ xs) ► (ty.int ↦ n))]%list.

  Goal True. idtac "Timing before: llist/simplify_plength_spec". Abort.
  Lemma simplify_plength_spec {Σ} (xs : Term Σ (ty.list ty.int)) (n : Term Σ ty.int) :
    let f := formula_user plength (env.nil ► (_ ↦ xs) ► (ty.int ↦ n)) in
    option.spec
      (fun r : List Formula Σ =>
         forall ι : Valuation Σ,
           inst f ι <-> instpc r ι)
      (forall ι : Valuation Σ, ~ inst f ι)
      (simplify_plength xs n).
  Proof.
    pattern (simplify_plength xs n).
    apply_funelim (simplify_plength xs n);
      try (constructor; intros; cbn; now rewrite rightid_and_true);
      intros; constructor; intros ι; cbn.
    - split; auto.
    - now rewrite rightid_and_true, Nat2Z.inj_succ, Z.add_1_l, Z.succ_inj_wd.
  Qed.
  Goal True. idtac "Timing after: llist/simplify_plength_spec". Abort.

  Equations simplify_preverseappend {Σ} (xs ys zs: Term Σ (ty.list ty.int)) : option (List Formula Σ) :=
  (* | term_binop binop_cons x xs | term_binop binop_plus (term_val ?(ty.int) 1%Z) n := *)
  (*   Some [formula_user plength (env.nil ► (_ ↦ xs) ► (ty.int ↦ n))]%list; *)
  | term_val ?(ty.list ty.int) nil | ys | zs := Some [formula_eq ys zs]%list;
  | xs | term_val ?(ty.list ty.int) nil | zs := Some [formula_user preverse (env.nil ► (_ ↦ xs) ► (_ ↦ zs))]%list;
  | term_binop bop.cons x xs | ys | zs := Some [formula_user preverseappend (env.nil ► (_ ↦ xs) ► (_  ↦ term_binop bop.cons x ys) ► (_  ↦ zs))]%list;
  | xs | ys | zs          :=
    Some [formula_user preverseappend (env.nil ► (_ ↦ xs) ► (_  ↦ ys) ► (_  ↦ zs))]%list.

  Goal True. idtac "Timing before: llist/simplify_preverseappend_spec". Abort.
  Lemma simplify_preverseappend_spec {Σ} (xs ys zs : Term Σ (ty.list ty.int)) :
    let f := formula_user preverseappend (env.nil ► (_ ↦ xs) ► (_ ↦ ys) ► (_ ↦ zs)) in
    option.spec
      (fun r : List Formula Σ =>
         forall ι : Valuation Σ,
           inst f ι <-> instpc r ι)
      (forall ι : Valuation Σ, ~ inst f ι)
      (simplify_preverseappend xs ys zs).
  Proof.
    pattern (simplify_preverseappend xs ys zs).
    apply_funelim (simplify_preverseappend xs ys zs);
      try (constructor; intros; cbn; now rewrite rightid_and_true);
      intros; constructor; intros ι; cbn; rewrite ?rightid_and_true.
    - now rewrite rev_alt.
    - now rewrite rev_append_rev.
    - now rewrite rev_alt.
  Qed.
  Goal True. idtac "Timing after: llist/simplify_preverseappend_spec". Abort.

  Definition solve_user : SolverUserOnly :=
    fun Σ p =>
      match p with
      | plength => fun ts =>
                     let (ts,n)  := env.snocView ts in
                     let (ts,xs) := env.snocView ts in
                     simplify_plength xs n
      | preverse => fun ts => Some (cons (formula_user preverse ts) nil)
      | preverseappend =>
          fun ts =>
            let (ts,zs) := env.snocView ts in
            let (ts,ys) := env.snocView ts in
            let (ts,xs) := env.snocView ts in
            simplify_preverseappend xs ys zs
      end.

  Lemma solve_user_spec : SolverUserOnlySpec solve_user.
  Proof.
    intros Σ p ts.
    destruct p; cbv in ts; env.destroy ts.
    - apply simplify_plength_spec.
    - constructor; intros ?; cbn.
      now rewrite rightid_and_true.
    - apply simplify_preverseappend_spec.
  Qed.

  Definition solver : Solver :=
    solveruseronly_to_solver solve_user.
  Lemma solver_spec : SolverSpec solver.
  Proof.
    apply solveruseronly_to_solver_spec, solve_user_spec.
  Qed.

End ExampleSolverKit.
Module ExampleSolver := MakeSolver DefaultBase ExampleSignature ExampleSpecification ExampleSolverKit.

Module Import ExampleExecutor :=
  MakeExecutor DefaultBase ExampleSignature ExampleSpecification ExampleSolver.

Section DebugExample.
  Import SymProp.notations.
  Notation "x '∷' σ . P" := (@SymProp.EMsgThere _ (x ∷ σ) P) (at level 200, right associativity, only printing, format "x '∷' σ .  '/' P").
  Notation "'error' x" := (SymProp.error x) (at level 200, only printing, format "'error'  x").
  Notation "P" := (SymProp.EMsgHere P) (only printing).
  Import ListNotations.

  Lemma debug_appendloop_broken : Symbolic.ValidContract sep_contract_appendloop fun_appendloop_broken.
  Proof.
    compute.
    idtac "Verification condition with failure:".
    match goal with |- VerificationCondition ?x => idtac x end.
  Abort.

End DebugExample.

Goal True. idtac "Timing before: llist/valid_contract_append". Abort.
Lemma valid_contract_append : Symbolic.ValidContractReflect sep_contract_append fun_append.
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: llist/valid_contract_append". Abort.

Goal True. idtac "Timing before: llist/valid_contract_appendloop". Abort.
Lemma valid_contract_appendloop : Symbolic.ValidContractReflect sep_contract_appendloop fun_appendloop.
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: llist/valid_contract_appendloop". Abort.

Goal True. idtac "Timing before: llist/valid_contract_length". Abort.
Lemma valid_contract_length : Symbolic.ValidContractReflect sep_contract_length fun_length.
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: llist/valid_contract_length". Abort.

Goal True. idtac "Timing before: llist/valid_contract_copy". Abort.
Lemma valid_contract_copy : Symbolic.ValidContractReflect sep_contract_copy fun_copy.
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: llist/valid_contract_copy". Abort.

Goal True. idtac "Timing before: llist/valid_contract_reverse". Abort.
Lemma valid_contract_reverse : Symbolic.ValidContractReflect sep_contract_reverse fun_reverse.
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: llist/valid_contract_reverse". Abort.

Goal True. idtac "Timing before: llist/valid_contract_reverseloop". Abort.
Lemma valid_contract_reverseloop : Symbolic.ValidContractReflect sep_contract_reverseloop fun_reverseloop.
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: llist/valid_contract_reverseloop". Abort.

Module Import ExampleShalExec :=
  MakeShallowExecutor DefaultBase ExampleSignature ExampleSpecification.
Module ExampleSemantics <: Semantics DefaultBase ExampleProgram :=
  MakeSemantics DefaultBase ExampleProgram.

Module ExampleModel.
  Import ExampleProgram.
  Import ExampleSpecification.

  Module ExampleIrisPrelims <: IrisPrelims DefaultBase ExampleProgram ExampleSignature ExampleSemantics.
    Include IrisPrelims DefaultBase ExampleProgram ExampleSignature ExampleSemantics.
  End ExampleIrisPrelims.

  Module ExampleIrisParameters <: IrisParameters DefaultBase ExampleProgram ExampleSignature ExampleSemantics ExampleIrisPrelims.
    Import ExampleIrisPrelims.
    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.tactics.

    Class mcMemGS Σ :=
      McMemGS {
          (* ghost variable for tracking state of registers *)
          mc_ghGS :> gen_heapGS Z (Z * (Z + unit)) Σ;
          mc_invNs : namespace
        }.

    Definition memGpreS : gFunctors -> Set := fun Σ => gen_heapGpreS Z (Z * (Z + unit)) Σ.
    Definition memGS : gFunctors -> Set := mcMemGS.
    Definition memΣ : gFunctors := gen_heapΣ Z (Z * (Z + unit)).

    Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
      fun {Σ} => subG_gen_heapGpreS (Σ := Σ) (L := Z) (V := (Z * (Z + unit))).

    Lemma fst_pair_id2 : forall {A} {B},
        (λ (x : A) (y : B), (Datatypes.fst ∘ pair x) y) = (λ (x : A) (y : B), x).
    Proof.
      intros; reflexivity.
    Qed.

    Lemma imap_pair_fst_seq {A} (l : list A) :
      (imap pair l).*1 = seq 0 (length l).
    Proof.
      rewrite fmap_imap.
      rewrite fst_pair_id2.
      rewrite imap_seq_0.
      rewrite list_fmap_id; reflexivity.
    Qed.

    Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ => (gen_heap_interp (hG := mc_ghGS (mcMemGS := hG)) μ)%I.

    Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ => ([∗ map] l↦v ∈ μ, mapsto (hG := mc_ghGS (mcMemGS := hG)) l (DfracOwn 1) v)%I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
                                                ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
    Proof.
      iIntros (Σ μ gHP).
      iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Z) (V := (Z * (Z + unit))) empty) as (gH) "[inv _]".

      iMod (gen_heap_alloc_big empty μ (map_disjoint_empty_r μ) with "inv") as "(inv & res & _)".
      iModIntro.
      rewrite (right_id empty union μ).

      iExists (McMemGS gH (nroot .@ "mem_inv")).
      iFrame.
    Qed.
  End ExampleIrisParameters.

  Module ExampleIrisResources <: IrisResources DefaultBase ExampleSignature ExampleSemantics ExampleIrisPrelims ExampleIrisParameters.
    Include IrisResources DefaultBase ExampleSignature ExampleSemantics ExampleIrisPrelims ExampleIrisParameters.
  End ExampleIrisResources.

  Section Predicates.
    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.tactics.
    Import ExampleIrisParameters.

    Definition ptstocons_interp `{mG : memGS Σ} (p : Z) (v : Z) (n : Z + unit) : iProp Σ :=
      (mapsto (hG := mc_ghGS (mcMemGS := mG)) p (DfracOwn 1) (pair v n))%I.

    Fixpoint ptstolist_interp `{mG : memGS Σ} (p : Z + unit) (vs : list Z) : iProp Σ :=
      match vs with
      | nil => ⌜p = inr tt⌝
      | v :: vs => (∃ p' pn, ⌜p = inl p'⌝ ∗ ptstocons_interp (mG := mG) p' v pn ∗ ptstolist_interp (mG := mG) pn vs)%I
      end.
  End Predicates.

  Module ExampleIrisPredicates <: IrisPredicates DefaultBase ExampleSignature ExampleSemantics ExampleIrisPrelims ExampleIrisParameters ExampleIrisResources.
    Import ExampleIrisPrelims.
    Import ExampleIrisParameters.
    Import iris.base_logic.lib.iprop.

    Definition luser_inst `{sRG : sailRegGS Σ} `{wsat.invGS.invGS Σ} (mG : memGS Σ) (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
      (match p return Env Val (𝑯_Ty p) -> iProp Σ with
      | ptstocons => fun ts => ptstocons_interp (mG := mG) (env.head (env.tail (env.tail ts))) (env.head (env.tail ts)) (env.head ts)
      | ptstolist => fun ts => ptstolist_interp (mG := mG) (env.head (env.tail ts)) (env.head ts)
       end) ts.

    Definition lduplicate_inst `{sRG : sailRegGS Σ} `{wsat.invGS.invGS Σ} (mG : memGS Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true -> luser_inst mG p ts -∗ luser_inst mG p ts ∗ luser_inst mG p ts.
    Proof.
      destruct p; now cbn.
    Qed.
  End ExampleIrisPredicates.

  Import ExampleIrisParameters.
  Import ExampleIrisResources.

  Include IrisInstance DefaultBase ExampleSignature ExampleSemantics ExampleIrisPrelims ExampleIrisParameters ExampleIrisResources ExampleIrisPredicates.
  Include ProgramLogicOn DefaultBase ExampleSignature ExampleSpecification.
  Include IrisInstanceWithContracts DefaultBase ExampleSignature ExampleSpecification ExampleSemantics ExampleIrisPrelims ExampleIrisParameters ExampleIrisResources ExampleIrisPredicates.

  Section WithIrisNotations.
    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.program_logic.weakestpre.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.string_ident.
    Import iris.proofmode.tactics.

    (* Import PROG to reset the access path of notations. *)
    Import PROG.

    Ltac destruct_syminstance ι :=
      repeat
        match type of ι with
        | Env _ (ctx.snoc _ (MkB ?s _)) =>
            let id := string_to_ident s in
            let fr := fresh id in
            destruct (env.snocView ι) as [ι fr];
            destruct_syminstance ι
        | Env _ ctx.nil => destruct (env.nilView ι)
        | _ => idtac
        end.

    Lemma mkcons_sound `{sailGS Σ} {Γ δ} :
      forall (x : Exp Γ ptr) (xs : Exp Γ llist),
        ⊢ semTriple δ (⌜true = true⌝ ∧ emp) (foreign mkcons x xs)
          (λ (v : Val ptr) (δ' : CStore Γ),
            ptstocons_interp (mG := sailGS_memGS) v (eval x δ) (eval xs δ) ∗ ⌜δ' = δ⌝).
    Proof.
      iIntros (x xs) "_".
      rewrite wp_unfold. cbn.
      iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
      unfold mem_inv.
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      dependent elimination H0.
      dependent elimination s.
      cbn in f1.
      destruct_conjs; subst.
      do 3 iModIntro.
      cbn.
      iMod "Hclose2" as "_".
      iMod (gen_heap_alloc μ1 (infinite_fresh (A := Z) (elements (dom (gset Z) μ1))) (eval x δ1, eval xs δ1) with "Hmem") as "[Hmem [Hres _]]".
      { rewrite <-not_elem_of_dom, <-elem_of_elements.
        now eapply infinite_is_fresh.
      }
      iModIntro.
      iFrame.
      iSplitL; last done.
      iApply wp_value.
      now iFrame.
    Qed.

    Lemma fst_sound `{sailGS Σ} {Γ δ} :
      forall (ep : Exp Γ ptr) (vx : Val ty.int) (vxs : Val llist),
        let vp := eval ep δ in
        ⊢ semTriple δ
          (ptstocons_interp (mG := sailGS_memGS) vp vx vxs)
          (foreign fst ep)
          (λ (v : Z) (δ' : CStore Γ),
            ((⌜v = vx⌝ ∧ emp) ∗ ptstocons_interp (mG := sailGS_memGS) vp vx vxs) ∗ ⌜ δ' = δ⌝).
    Proof.
      iIntros (ep vx vxs vp) "Hres".
      rewrite wp_unfold.
      iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first done.
      iIntros (e2 σ'' efs) "%".
      dependent elimination H0.
      dependent elimination s.
      cbn in f1.
      unfold mem_inv.
      do 3 iModIntro.
      iMod "Hclose2" as "_".
      iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx,vxs) with "Hmem Hres") as "%".
      rewrite H0 in f1.
      destruct_conjs; subst.
      iModIntro.
      iFrame.
      iSplitL; last done.
      iApply wp_value.
      now iFrame.
    Qed.

    Lemma snd_sound `{sailGS Σ} {Γ δ} :
      forall (ep : Exp Γ ptr) (vx : Val ptr) (vxs : Val llist),
        let vp := eval ep δ in
        ⊢ semTriple δ
          (ptstocons_interp (mG := sailGS_memGS) vp vx vxs)
          (foreign snd ep)
          (λ (v : Z + ()) (δ' : CStore Γ),
            ((⌜v = vxs⌝ ∧ emp) ∗ ptstocons_interp (mG := sailGS_memGS) vp vx vxs) ∗ ⌜ δ' = δ⌝).
    Proof.
      iIntros (ep vx vxs vp) "Hres".
      rewrite wp_unfold.
      iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first done.
      iIntros (e2 σ'' efs) "%".
      dependent elimination H0.
      dependent elimination s.
      cbn in f1.
      unfold mem_inv.
      do 3 iModIntro.
      iMod "Hclose2" as "_".
      iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx,vxs) with "Hmem Hres") as "%".
      rewrite H0 in f1.
      destruct_conjs; subst.
      iModIntro.
      iFrame.
      iSplitL; last done.
      iApply wp_value.
      now iFrame.
    Qed.

    Lemma setsnd_sound`{sailGS Σ}  {Γ δ} :
      forall (ep : Exp Γ ptr) (exs : Exp Γ llist) (vx : Val ptr),
        let vp := eval ep δ in let vxs := eval exs δ in
        ⊢ semTriple δ
        (∃ v : Z + (), ptstocons_interp (mG := sailGS_memGS) vp vx v)
        (foreign setsnd ep exs)
        (λ (v : ()) (δ' : CStore Γ),
           ((⌜v = tt⌝ ∧ emp) ∗ ptstocons_interp (mG := sailGS_memGS) vp vx vxs) ∗ ⌜δ' = δ⌝).
    Proof.
      iIntros (ep exs vx vp vxs) "Hres".
      iDestruct "Hres" as (vxs__old) "Hres".
      rewrite wp_unfold.
      iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      dependent elimination H0. cbn.
      dependent elimination s.
      cbn in f1.
      unfold mem_inv.
      do 3 iModIntro.
      iMod "Hclose2" as "_".
      iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx,vxs__old) with "Hmem Hres") as "%".
      rewrite H0 in f1.
      destruct_conjs; subst.
      iMod (gen_heap_update μ1 vp (vx,vxs__old) (vx,vxs) with "Hmem Hres") as "[Hmem Hres]".
      iModIntro.
      iFrame.
      iApply wp_value.
      now iFrame.
    Qed.

    Lemma foreignSem `{sailGS Σ} : ForeignSem.
    Proof.
      intros Γ τ Δ f es δ; destruct f; env.destroy es;
        intros ι; env.destroy ι; cbn; intros Heq; env.destroy Heq; subst;
        eauto using mkcons_sound, fst_sound, snd_sound, setsnd_sound.
    Qed.

    Goal True. idtac "Timing before: llist/lemmas". Abort.
    Lemma lemSem `{sailGS Σ} : LemmaSem.
    Proof.
      intros Γ l.
      destruct l; cbn; intros ι; destruct_syminstance ι; cbn.
      - auto.
      - iIntros "Hres".
        destruct xs; cbn.
        { iDestruct "Hres" as "%". inversion H0. }
        iDestruct "Hres" as (p' pn) "[% [Hp' Hpn]]".
        inversion H0; subst.
        iExists pn.
        iFrame.
      - iIntros "Hres".
        destruct xs; cbn.
        + now destruct p.
        + iDestruct "Hres" as (p' pn) "[% _]".
          inversion H0.
      - iIntros "[Hp Hn]".
        iExists p.
        iExists n.
        now iFrame.
    Qed.
    Goal True. idtac "Timing after: llist/lemmas". Abort.

  End WithIrisNotations.

  Include Shallow.Soundness.Soundness DefaultBase ExampleSignature ExampleSpecification ExampleShalExec.
  Include Soundness DefaultBase ExampleSignature ExampleSpecification ExampleSolver ExampleShalExec ExampleExecutor.

  Section WithIrisNotations.
    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.program_logic.weakestpre.
    Import iris.base_logic.lib.gen_heap.

  Lemma linked_list_sound `{sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
  Proof.
    apply (sound foreignSem lemSem).
    intros Γ τ f c.
    destruct f; inversion 1; subst;
    apply shallow_vcgen_soundness;
    apply symbolic_vcgen_soundness;
    apply Symbolic.validcontract_reflect_sound.
    apply valid_contract_append.
    apply valid_contract_appendloop.
    apply valid_contract_length.
    apply valid_contract_copy.
    apply valid_contract_reverse.
    apply valid_contract_reverseloop.
  Qed.

  Goal True. idtac "Assumptions linked_list_sound:". Abort.
  Print Assumptions linked_list_sound.

  End WithIrisNotations.
End ExampleModel.

Ltac calcstats fn :=
  let smb := eval compute in (Symbolic.Statistics.calc fn) in
  let shl := Shallow.Statistics.calc fn in
  let row := constr:(pair fn (pair shl smb)) in
  idtac row.

Goal forall {Δ τ} (f : Fun Δ τ), f = f.
  idtac "Branching statistics:".
  destruct f;
    match goal with
    |- ?g = _ => calcstats g
    end.
Abort.
