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
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Symbolic.Mutator
     Sep.Spec
     Syntax.

From stdpp Require decidable finite.
From iris_string_ident Require Import ltac2_string_ident.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)
Inductive Enums : Set :=.
Inductive Unions : Set :=.
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

Module ExampleTypeKit <: TypeKit.

  Import stdpp.finite.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (E : 𝑬) : Set :=
    match E with
    end.
  Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).
  Instance 𝑬𝑲_finite (E : 𝑬) : Finite (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).

  (** UNIONS **)
  Definition 𝑼        := Unions.
  Definition 𝑼_eq_dec := Unions_eqdec.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    end.
  Instance 𝑼𝑲_eq_dec U : EqDec (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).
  Instance 𝑼𝑲_finite U : Finite (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).

  (** RECORDS **)
  Definition 𝑹        := Records.
  Definition 𝑹_eq_dec := Records_eqdec.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    end.
  Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
    ltac:(destruct R; auto with typeclass_instances).

End ExampleTypeKit.

(*** VALUES ***)

Module ExampleValueKit <: ValueKit.
  Module typekit := ExampleTypeKit.
  Module Export TY := Types typekit.

  (** UNIONS **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    end.
  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    end.
  Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold U (𝑼_unfold U Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) }),
      𝑼_unfold U (𝑼_fold U Kv) = Kv.
  Proof. now intros [] [[]]. Qed.

  (** RECORDS **)
  Definition 𝑹𝑭  : Set := Empty_set.
  Definition 𝑹𝑭_Ty (R : 𝑹) : Ctx (𝑹𝑭 * Ty) := match R with end.
  Definition 𝑹_fold (R : 𝑹) : NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R := match R with end.
  Definition 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Lit (𝑹𝑭_Ty R) := match R with end.
  Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold R (𝑹_unfold R Kv) = Kv.
  Proof. intros []. Qed.
  Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold R (𝑹_fold R Kv) = Kv.
  Proof. intros []. Qed.

End ExampleValueKit.

(*** TERMS ***)

Module ExampleTermKit <: TermKit.
  Module valuekit := ExampleValueKit.
  Module Export VAL := Values valuekit.

  (* VARIABLES *)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.
  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.
  Definition fresh := Context.fresh (T := Ty).

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  Notation ptr   := ty_int.
  Notation llist := (ty_option ptr).

  (** FUNCTIONS **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | append   : Fun [ "p" :: ptr, "q" :: llist ] ty_unit
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  | cons    : FunX [ "x" :: ty_int, "xs" :: llist ] ptr
  (* | head    : FunX [ "p" :: ptr ] ty_int *)
  | tail    : FunX [ "p" :: ptr ] llist
  (* | sethead : FunX [ "p" :: ptr, "x" :: ty_int ] ty_unit *)
  | settail : FunX [ "p" :: ptr, "xs" :: llist ] ty_unit
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿 : Ctx (𝑿 * Ty) -> Ty -> Set := FunX.

  Definition 𝑹𝑬𝑮 : Ty -> Set := fun _ => Empty_set.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮) :=
    fun '(existT _ x) => match x with end.

  Inductive Lem : NCtx 𝑿 Ty -> Set :=
  | open_cons     : Lem [ "p" :: ptr ]
  | close_nil     : Lem [ "p" :: ty_unit ]
  | close_cons    : Lem [ "p" :: ptr ].

  Definition 𝑳 : NCtx 𝑿 Ty -> Set := Lem.

  Instance 𝑹𝑬𝑮_eq_decision : base.RelDecision (@eq (sigT 𝑹𝑬𝑮)).
  Proof.
    intros xy; eapply 𝑹𝑬𝑮_eq_dec.
  Defined.

  Program Instance 𝑹𝑬𝑮_finite : finite.Finite (sigT 𝑹𝑬𝑮) := {| finite.enum := nil |}.
  Next Obligation.
    now eapply (nodup_fixed (H := 𝑹𝑬𝑮_eq_dec)).
  Defined.
  Next Obligation.
    intros x.
    refine (@decidable.bool_decide_unpack _ (list.elem_of_list_dec _ _) _).
    destruct x as [σ r]; now destruct r.
  Qed.

End ExampleTermKit.

(*** PROGRAM ***)

Module ExampleProgramKit <: (ProgramKit ExampleTermKit).
  Module Export TM := Terms ExampleTermKit.

  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
  Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

  Notation "'lemma' f args" := (stm_lemma f args%arg) (at level 10, f at next level) : exp_scope.

  Definition fun_append : Stm [ "p" :: ptr, "q" :: llist ] ty_unit :=
    lemma open_cons [exp_var "p"] ;;
    let: "mbn" := foreign tail (exp_var "p") in
    match: (exp_var "mbn") with
    | inl "x" => call append (exp_var "x") (exp_var "q")
    | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        foreign settail (exp_var "p") (exp_var "q")
    end;;
    lemma close_cons [exp_var "p"].

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    Eval compute in
    match f in Fun Δ τ return Stm Δ τ with
    | append => fun_append
    end.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  Definition Memory : Set := unit.
  Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs)
    (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Admitted.

End ExampleProgramKit.
Import ExampleProgramKit.

(* ⇑ GENERATED                                                                *)
(******************************************************************************)
(* ⇓ NOT GENERATED                                                            *)

Inductive Predicate : Set :=
| ptstocons
| ptstolist
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module SepContracts.

  Module ExampleAssertionKit <:
    (AssertionKit ExampleTermKit ExampleProgramKit).
    Export ExampleProgramKit.

    Definition 𝑷 := Predicate.
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | ptstocons => [ptr, ty_int, llist]
      | ptstolist => [llist, ty_list ty_int]
      end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.
    Instance 𝑷_is_dup : IsDuplicable 𝑷 :=
      {| is_duplicable p :=
        match p with
        | ptstocons => false
        | ptstolist => false
        end
      |}.

  End ExampleAssertionKit.

  Module ExampleSymbolicContractKit <:
    SymbolicContractKit ExampleTermKit ExampleProgramKit ExampleAssertionKit.
    Module Export ASS := Assertions ExampleTermKit ExampleProgramKit ExampleAssertionKit.

    Local Notation "p '↦' xs" := (asn_chunk (chunk_user ptstolist (env_nil ► (llist ↦ p) ► (ty_list ty_int ↦ xs)))) (at level 100).
    Local Notation "p '∗' q" := (asn_sep p q) (at level 150).
    Local Notation "p '↦p' ( x , xs )" := (asn_chunk (chunk_user ptstocons (env_nil ► (ptr ↦ p) ► (ty_int ↦ x) ► (llist ↦ xs)))) (at level 100).

    Arguments formula_prop [Σ] Σ' ζ _.

    Definition asn_append {Σ : LCtx} (xs ys zs : Term Σ (ty_list ty_int)) : Assertion Σ :=
      asn_formula (formula_eq (term_binop binop_append xs ys) zs).

    Definition sep_contract_append : SepContract [ "p" :: ptr, "q" :: llist ] ty_unit :=
      {| sep_contract_logic_variables := ["p" :: ptr, "q" :: llist, "xs" :: ty_list ty_int, "ys" :: ty_list ty_int];
         sep_contract_localstore      := [term_var "p", term_var "q"]%arg;
         sep_contract_precondition    := term_inl (term_var "p") ↦ term_var "xs" ∗ term_var "q" ↦ term_var "ys";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_lit ty_unit tt)) ∗
           asn_exist "zs" (ty_list ty_int)
             (term_inl (term_var "p") ↦ term_var "zs" ∗
              asn_append (term_var "xs") (term_var "ys") (term_var "zs"));
      |}.

    Definition sep_contract_cons : SepContract [ "x" :: ty_int, "xs" :: llist ] ptr :=
      {| sep_contract_logic_variables := ["x" :: ty_int, "xs" :: llist];
         sep_contract_localstore      := [term_var "x", term_var "xs"]%arg;
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "p";
         sep_contract_postcondition   := term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_tail : SepContract [ "p" :: ptr ] llist :=
      {| sep_contract_logic_variables := ["p" :: ty_int, "x" :: ty_int, "xs" :: llist];
         sep_contract_localstore      := [term_var "p"]%arg;
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "xs" );
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_var "xs")) ∗
           term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_settail : SepContract [ "p" :: ptr, "xs" :: llist ] ty_unit :=
      {| sep_contract_logic_variables := ["p" :: ty_int, "x" :: ty_int, "xs" :: llist, "ys" :: llist];
         sep_contract_localstore      := [term_var "p", term_var "xs"]%arg;
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "ys");
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
         asn_formula (formula_eq (term_var "result") (term_lit ty_unit tt)) ∗
         term_var "p" ↦p ( term_var "x" , term_var "xs");
      |}.

    Definition sep_lemma_open_cons : Lemma [ "p" :: ptr ] :=
      {| lemma_logic_variables := ["p" :: ty_int, "xs" :: ty_list ty_int];
         lemma_patterns        := [term_var "p"]%arg;
         lemma_precondition    := term_inl (term_var "p") ↦ term_var "xs";
         lemma_postcondition   :=
           asn_match_list (term_var "xs")
             asn_false
             "y" "ys"
             (asn_exist "n" llist
                (term_var "p" ↦p (term_var "y", term_var "n") ∗
                term_var "n" ↦ term_var "ys"))
      |}.

    Definition sep_lemma_close_cons : Lemma [ "p" :: ptr ] :=
      {| lemma_logic_variables := ["p" :: ptr, "x" :: ty_int, "xs" :: ty_list ty_int, "n" :: llist ];
         lemma_patterns        := [term_var "p"]%arg;
         lemma_precondition    := term_var "p" ↦p (term_var "x" , term_var "n") ∗
                                  term_var "n" ↦ term_var "xs";
         lemma_postcondition   := term_inl (term_var "p") ↦ term_binop binop_cons (term_var "x") (term_var "xs")
      |}.

   Definition sep_lemma_close_nil : Lemma [ "p" :: ty_unit ] :=
      {| lemma_logic_variables := ["p" :: ty_unit, "xs" :: ty_list ty_int ];
         lemma_patterns        := [term_var "p"]%arg;
         lemma_precondition    := term_inr (term_var "p") ↦ term_var "xs";
         lemma_postcondition   :=
           asn_formula (formula_eq (term_var "p") (term_lit ty_unit tt)) ∗
           asn_formula (formula_eq (term_var "xs") (term_lit (ty_list ty_int) nil))
      |}.

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | append => Some (sep_contract_append)
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | cons => sep_contract_cons
        | tail => sep_contract_tail
        | settail => sep_contract_settail
        end.

    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with
        | open_cons => sep_lemma_open_cons
        | close_cons => sep_lemma_close_cons
        | close_nil => sep_lemma_close_nil
        end.

  End ExampleSymbolicContractKit.
  Import ExampleSymbolicContractKit.

  Module ExampleSMutators :=
    Mutators
      ExampleTermKit
      ExampleProgramKit
      ExampleAssertionKit
      ExampleSymbolicContractKit.
  Import ExampleSMutators.

  Lemma valid_contract_append : SMut.ValidContractReflect sep_contract_append fun_append.
  Proof. Time reflexivity. Qed.

End SepContracts.
