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
     Lists.List
     Logic.FinFun
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Symbolic.Mutator
     Sep.Spec
     Syntax.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)

(** Enums **)
Inductive Enums : Set :=
| ordering.

Inductive Ordering : Set :=
| LT
| EQ
| GT.

(** Unions **)
Inductive Unions : Set :=
| either.

Inductive EitherConstructor : Set :=
| Left
| Right.

(** Records **)
Inductive Records : Set :=.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Enums.
  Derive NoConfusion for Ordering.
  Derive NoConfusion for Unions.
  Derive NoConfusion for EitherConstructor.
  Derive NoConfusion for Records.

End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for Ordering.
Derive EqDec for Unions.
Derive EqDec for EitherConstructor.
Derive EqDec for Records.

Section Finite.

  Import stdpp.finite.
  Import ListNotations.

  Global Program Instance Ordering_finite : Finite Ordering :=
    {| enum := [LT;EQ;GT] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance EitherConstructor_finite : Finite EitherConstructor :=
    {| enum := [Left;Right] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

End Finite.

Module ExampleTypeKit <: TypeKit.

  Import stdpp.finite.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (E : 𝑬) : Set :=
    match E with
    | ordering => Ordering
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
    | either => (string + Z)%type
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | either => EitherConstructor
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
    | either => fun K => match K with
                         | Left => ty_string
                         | Right => ty_int
                         end
    end.
  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | either => fun Kv =>
                  match Kv with
                  | existT Left v  => inl v
                  | existT Right v => inr v
                  end
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    | either => fun Kv =>
                  match Kv with
                  | inl v => existT Left v
                  | inr v => existT Right v
                  end
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

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | abs :        Fun [ "x" :: ty_int               ] ty_int
  | cmp :        Fun [ "x" :: ty_int, "y" :: ty_int ] (ty_enum ordering)
  | gcd :        Fun [ "x" :: ty_int, "y" :: ty_int ] ty_int
  | gcdloop :    Fun [ "x" :: ty_int, "y" :: ty_int ] ty_int
  | msum :       Fun [ "x" :: ty_union either, "y" :: ty_union either] (ty_union either)
  | length {σ} : Fun [ "xs" :: ty_list σ           ] ty_int
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿 : Ctx (𝑿 * Ty) -> Ty -> Set := fun _ _ => Empty_set.

  Definition 𝑹𝑬𝑮 : Ty -> Set := fun _ => Empty_set.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮) :=
    fun '(existT _ x) => match x with end.

End ExampleTermKit.

(*** PROGRAM ***)

Module ExampleProgramKit <: (ProgramKit ExampleTermKit).
  Module Export TM := Terms ExampleTermKit.

  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'`LT'" := (@exp_lit _ (ty_enum ordering) LT).
  Local Notation "'`GT'" := (@exp_lit _ (ty_enum ordering) GT).
  Local Notation "'`EQ'" := (@exp_lit _ (ty_enum ordering) EQ).
  Local Notation "'`Left' e" := (exp_union either Left e) (at level 10, e at level 9).
  Local Notation "'`Right' e" := (exp_union either Right e) (at level 10, e at level 9).
  Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
  Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

  Definition fun_msum : Stm ["x" :: ty_union either, "y" :: ty_union either] (ty_union either) :=
    stm_match_union_alt either x
     (fun K =>
        match K with
        | Left  => MkAlt (pat_var "z") (`Left z)
        | Right => MkAlt (pat_var "z") y
        end).

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    Eval compute in
    match f in Fun Δ τ return Stm Δ τ with
    | abs => if: lit_int 0 <= x then x else - x
    | cmp => if: x < y then `LT else
             if: x = y then `EQ else
             if: x > y then `GT else
             fail "cmp failed"
    | gcd => "x" <- call abs x ;;
             "y" <- call abs y ;;
             call gcdloop x y
    | gcdloop =>
             let: "z" := call cmp x y in
             match: z in ordering with
             | LT => call gcdloop x (y - x)
             | EQ => x
             | GT => call gcdloop (x - y) y
             end
    | msum => fun_msum
    | length => stm_match_list
                  (exp_var "xs")
                  (stm_lit ty_int 0)
                  "y" "ys" (let: "n" := call length (exp_var "ys") in lit_int 1 + exp_var "n")
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
  Proof. destruct f. Qed.

End ExampleProgramKit.

(* ⇑ GENERATED                                                                *)
(******************************************************************************)
(* ⇓ NOT GENERATED                                                            *)

Module SepContracts.

  Module ExampleAssertionKit <:
    (AssertionKit ExampleTermKit ExampleProgramKit).
    Export ExampleProgramKit.

    Definition 𝑷 := Empty_set.
    Definition 𝑷_Ty : 𝑷 -> Ctx Ty := fun p => match p with end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := fun p => match p with end.
  End ExampleAssertionKit.

  Module ExampleSymbolicContractKit <:
    SymbolicContractKit ExampleTermKit ExampleProgramKit ExampleAssertionKit.
    Module Export ASS := Assertions ExampleTermKit ExampleProgramKit ExampleAssertionKit.

    Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
    Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

    (* Arguments asn_prop [_] & _. *)
    (* Arguments MkSepContractPun [_ _] & _ _ _ _. *)

    Definition sep_contract_abs : SepContract [ "x" :: ty_int ] ty_int :=
      {| sep_contract_logic_variables := ["x" :: ty_int];
         sep_contract_localstore      := [term_var "x"]%arg;
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_prop
             ["x" :: ty_int, "result" :: ty_int]
             (fun x result => result = Z.abs x)
           (* asn_if *)
           (*   (term_binop binop_lt (term_var "x") (term_lit ty_int 0)) *)
           (*   (asn_bool (term_binop binop_eq (term_var "result") (term_neg (term_var "x")))) *)
           (*   (asn_bool (term_binop binop_eq (term_var "result") (term_var "x"))) *)
      |}.

    Definition sep_contract_cmp : SepContract ["x" :: ty_int, "y" :: ty_int] (ty_enum ordering)  :=
       {| sep_contract_logic_variables := ["x" :: ty_int, "y" :: ty_int];
          sep_contract_localstore      := [term_var "x", term_var "y"]%arg;
          sep_contract_precondition    := asn_true;
          sep_contract_result          := "result";
          sep_contract_postcondition   :=
            asn_match_enum
              ordering (term_var "result")
              (fun result =>
                 match result with
                 | LT => asn_bool (term_binop binop_lt (term_var "x") (term_var "y"))
                 | EQ => asn_bool (term_binop binop_eq (term_var "x") (term_var "y"))
                 | GT => asn_bool (term_binop binop_gt (term_var "x") (term_var "y"))
                 end)
       |}.

    Definition sep_contract_gcd : SepContract [ "x" :: ty_int, "y" :: ty_int ] ty_int :=
      {| sep_contract_logic_variables := ["x" :: ty_int, "y" :: ty_int];
         sep_contract_localstore      := [term_var "x", term_var "y"]%arg;
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           @asn_prop
             ["x" :: ty_int, "y" :: ty_int, "result" :: ty_int]
             (fun x y result => result = Z.gcd x y)
      |}.

    Definition sep_contract_gcdloop : SepContract [ "x" :: ty_int, "y" :: ty_int ] ty_int :=
      {| sep_contract_logic_variables := ["x" :: ty_int, "y" :: ty_int];
         sep_contract_localstore      := [term_var "x", term_var "y"]%arg;
         sep_contract_precondition    :=
           asn_bool (term_binop binop_le (term_lit ty_int 0) (term_var "x")) ✱
                    asn_bool (term_binop binop_le (term_lit ty_int 0) (term_var "y"));
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           @asn_prop
             ["x" :: ty_int, "y" :: ty_int, "result" :: ty_int]
             (fun x y result => result = Z.gcd x y)
      |}.

    Definition sep_contract_length {σ} : SepContract [ "xs" :: ty_list σ ] ty_int :=
      {| sep_contract_logic_variables := ["xs" :: ty_list σ ];
         sep_contract_localstore      := [term_var "xs"]%arg;
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           @asn_prop
             ["xs" :: ty_list σ, "result" :: ty_int]
             (fun xs result => result = Z.of_nat (Datatypes.length xs))
      |}.

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | abs     => Some sep_contract_abs
        | cmp     => Some sep_contract_cmp
        | gcd     => Some sep_contract_gcd
        | gcdloop => Some sep_contract_gcdloop
        | msum    => None
        | length  => Some sep_contract_length
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with end.

  End ExampleSymbolicContractKit.

  Module ExampleMutators :=
    Mutators
      ExampleTermKit
      ExampleProgramKit
      ExampleAssertionKit
      ExampleSymbolicContractKit.
  Import ExampleMutators.
  Import SMut.

  Local Ltac solve :=
    repeat
      (repeat intro;
       repeat
         match goal with
         | H: NamedEnv _ _ |- _ => unfold NamedEnv in H
         | H: Env _ ctx_nil |- _ => dependent destruction H
         | H: Env _ (ctx_snoc _ _) |- _ => dependent destruction H
         | H: _ /\ _ |- _ => destruct H
         | |- Debug _ _ => constructor
         | |- _ /\ _ => constructor
         | |- VerificationCondition _ => constructor; cbn
         | |- Obligation _ _ _ => constructor; cbn
         | |- _ \/ False => left
         | |- False \/ _ => right
         end;
       compute
       - [Pos.of_succ_nat List.length Pos.succ Z.pos_sub Z.succ Z.of_nat Z.add
          Z.gtb Z.eqb Z.ltb Lit
         ] in *;
       cbn [List.length];
       subst; try congruence;
       auto
      ).

  Lemma valid_contract_length {σ} : ValidContractEvarEnv (@sep_contract_length σ) (Pi length).
  Proof. solve; lia. Qed.
  Hint Resolve valid_contract_length : contracts.

  Lemma valid_contract_cmp : ValidContractEvarEnv sep_contract_cmp (Pi cmp).
  Proof. solve. Qed.
  Hint Resolve valid_contract_cmp : contracts.

End SepContracts.
