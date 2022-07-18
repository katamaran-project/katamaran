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

  Local Obligation Tactic :=
    finite_from_eqdec.

  Global Program Instance Ordering_finite : Finite Ordering :=
    {| enum := [LT;EQ;GT] |}.
  Global Program Instance EitherConstructor_finite : Finite EitherConstructor :=
    {| enum := [Left;Right] |}.

End Finite.

Module Import ExampleBase <: Base.
  Import stdpp.finite.

  #[export] Instance typedeclkit : TypeDeclKit :=
    {| enumi := Enums;
       unioni := Unions;
       recordi := Records;
    |}.

  Definition enum_denote (E : Enums) : Set :=
    match E with
    | ordering => Ordering
    end.

  Definition union_denote (U : Unions) : Set :=
    match U with
    | either => (string + Z)%type
    end.

  Definition record_denote (R : Records) : Set :=
    match R with end.

  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {| enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.

  Definition union_constructors (U : Unions) : Set :=
    match U with
    | either => EitherConstructor
    end.

  Definition union_constructor_type (U : Unions) : union_constructors U -> Ty :=
    match U with
    | either => fun K => match K with
                         | Left => ty.string
                         | Right => ty.int
                         end
    end.

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | either => fun Kv =>
                  match Kv with
                  | inl v => existT Left v
                  | inr v => existT Right v
                  end
    end.

  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
    match U with
    | either => fun Kv =>
                  match Kv with
                  | existT Left v  => inl v
                  | existT Right v => inr v
                  end
    end.

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

  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include DefaultRegDeclKit.
  Include BaseMixin.

End ExampleBase.

(*** PROGRAM ***)

Module Import ExampleProgram <: Program ExampleBase.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | abs :        Fun [ "x" ∷ ty.int               ] ty.int
    | cmp :        Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] (ty.enum ordering)
    | gcd :        Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int
    | gcdloop :    Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int
    | msum :       Fun [ "x" ∷ ty.union either; "y" ∷ ty.union either] (ty.union either)
    | length {σ} : Fun [ "xs" ∷ ty.list σ           ] ty.int
    | fpthree16 :  Fun [ "sign" ∷ ty.bvec 1 ] (ty.bvec 16)
    | fpthree32 :  Fun [ "sign" ∷ ty.bvec 1 ] (ty.bvec 32)
    | fpthree64 :  Fun [ "sign" ∷ ty.bvec 1 ] (ty.bvec 64)
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳 : PCtx -> Set := fun _ => Empty_set.

  End FunDeclKit.

  Include FunDeclMixin ExampleBase.

  Section FunDefKit.
    Import ctx.resolution.

    Local Coercion stm_exp : Exp >-> Stm.

    Local Notation "'`LT'" := (@exp_val _ (ty.enum ordering) LT).
    Local Notation "'`GT'" := (@exp_val _ (ty.enum ordering) GT).
    Local Notation "'`EQ'" := (@exp_val _ (ty.enum ordering) EQ).
    Local Notation "'`Left' e" := (exp_union either Left e) (at level 10, e at level 9).
    Local Notation "'`Right' e" := (exp_union either Right e) (at level 10, e at level 9).
    Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
    Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

    Definition fun_msum : Stm ["x" ∷ ty.union either; "y" ∷ ty.union either] (ty.union either) :=
      stm_match_union_alt either x
       (fun K =>
          match K with
          | Left  => MkAlt (pat_var "z") (`Left z)
          | Right => MkAlt (pat_var "z") y
          end).

    Definition fun_fpthree' (e f : nat) : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec (1 + e + f)) :=
      let: "exp" ∷ ty.bvec e := stm_val (ty.bvec e) (bv.one e) in
      let: "frac" ∷ ty.bvec f := stm_val (ty.bvec f) (bv.one f) in
      exp_binop
        (@bop.bvapp _ 1 (e + f))
        (exp_var "sign")
        (exp_binop
           (@bop.bvapp _ e f)
           (exp_var "exp")
           (exp_var "frac")).

    Definition fun_fpthree16 : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec 16) :=
      (let n := 16 in
       let e := 5 in
       let f := (n - (e + 1)) in
       fun_fpthree' e f)%nat.

    Definition fun_fpthree32 : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec 32) :=
      (let n := 32 in
       let e := 8 in
       let f := (n - (e + 1)) in
       fun_fpthree' e f)%nat.

    Definition fun_fpthree64 : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec 64) :=
      (let n := 64 in
       let e := 11 in
       let f := (n - (e + 1)) in
       fun_fpthree' e f)%nat.

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      Eval compute in
      match f in Fun Δ τ return Stm Δ τ with
      | abs => if: exp_int 0 <= x then x else - x
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
                    (stm_val ty.int 0)
                    "y" "ys" (let: "n" := call length (exp_var "ys") in exp_int 1 + exp_var "n")
      | fpthree16 => fun_fpthree16
      | fpthree32 => fun_fpthree32
      | fpthree64 => fun_fpthree64
      end.
  End FunDefKit.

  Include DefaultRegStoreKit ExampleBase.

  Section ForeignKit.
    Definition Memory : Set := unit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. destruct f. Qed.
  End ForeignKit.

  Include ProgramMixin ExampleBase.

End ExampleProgram.

Module Import ExampleSig <: Signature ExampleBase.
  Include DefaultPredicateKit ExampleBase.
  Include PredicateMixin ExampleBase.
End ExampleSig.

Module Import ExampleSpecification <: Specification ExampleBase ExampleProgram ExampleSig.
  Include SpecificationMixin ExampleBase ExampleProgram ExampleSig.
  Import ctx.resolution.

  Section ContractDefKit.

    Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
    Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

    Definition sep_contract_abs : SepContract [ "x" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int];
         sep_contract_localstore      := [term_var "x"];
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_prop
             ["x" ∷ ty.int; "result" ∷ ty.int]
             (fun x result => result = Z.abs x)
      |}.

    Definition sep_contract_cmp : SepContract ["x" ∷ ty.int; "y" ∷ ty.int] (ty.enum ordering)  :=
       {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
          sep_contract_localstore      := [term_var "x"; term_var "y"];
          sep_contract_precondition    := asn_true;
          sep_contract_result          := "result";
          sep_contract_postcondition   :=
            asn_match_enum
              ordering (term_var "result")
              (fun result =>
                 match result with
                 | LT => asn_bool (term_binop bop.lt (term_var "x") (term_var "y"))
                 | EQ => asn_bool (term_binop bop.eq (term_var "x") (term_var "y"))
                 | GT => asn_bool (term_binop bop.gt (term_var "x") (term_var "y"))
                 end)
       |}.

    Definition sep_contract_gcd : SepContract [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
         sep_contract_localstore      := [term_var "x"; term_var "y"];
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           @asn_prop
             ["x" ∷ ty.int; "y" ∷ ty.int; "result" ∷ ty.int]
             (fun x y result => result = Z.gcd x y)
      |}.

    Definition sep_contract_gcdloop : SepContract [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
         sep_contract_localstore      := [term_var "x"; term_var "y"];
         sep_contract_precondition    :=
           asn_bool (term_binop bop.le (term_val ty.int 0) (term_var "x")) ✱
                    asn_bool (term_binop bop.le (term_val ty.int 0) (term_var "y"));
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           @asn_prop
             ["x" ∷ ty.int; "y" ∷ ty.int; "result" ∷ ty.int]
             (fun x y result => result = Z.gcd x y)
      |}.

    Definition length_post {σ} (xs : list (Val σ)) (result : Val ty.int) :=
      result = Z.of_nat (@Datatypes.length (Val σ) xs).
    Definition sep_contract_length {σ} : SepContract [ "xs" ∷ ty.list σ ] ty.int :=
      {| sep_contract_logic_variables := ["xs" ∷ ty.list σ ];
         sep_contract_localstore      := [term_var "xs"];
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "result";
         sep_contract_postcondition   := asn_prop ["xs"∷ty.list σ; "result"∷ty.int] length_post
      |}.

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | abs       => Some sep_contract_abs
        | cmp       => Some sep_contract_cmp
        | gcd       => Some sep_contract_gcd
        | gcdloop   => Some sep_contract_gcdloop
        | msum      => None
        | length    => Some sep_contract_length
        | fpthree16 => None
        | fpthree32 => None
        | fpthree64 => None
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with end.

    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with end.

  End ContractDefKit.

End ExampleSpecification.

Module ExampleSolverKit := DefaultSolverKit ExampleBase ExampleSig.
Module ExampleSolver := MakeSolver ExampleBase ExampleSig ExampleSolverKit.

Module Import ExampleExecutor :=
  MakeExecutor ExampleBase ExampleProgram ExampleSig ExampleSpecification ExampleSolver.

Local Ltac solve :=
  repeat
    (compute
     - [Pos.of_succ_nat List.length Pos.succ Val
        Z.add Z.compare Z.eqb Z.ge Z.geb Z.gt Z.gtb Z.le Z.leb Z.lt
        Z.ltb Z.mul Z.of_nat Z.opp Z.pos_sub Z.succ is_true negb
       ] in *;
      repeat
       match goal with
       | H: NamedEnv _ _ |- _ => unfold NamedEnv in H
       | H: _ /\ _ |- _ => destruct H
       | H: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
       | H: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
       | H : pair _ _ = pair _ _ |- _ => inversion H; subst; clear H
       | |- forall _, _ => intro
       | |- exists _, _ => eexists
       | |- Debug _ _ => constructor
       | |- _ /\ _ => constructor
       | |- VerificationCondition _ => constructor; cbn
       | |- Obligation _ _ _ => constructor; cbn
       | |- _ \/ False => left
       | |- False \/ _ => right
       end;
     cbn [List.length];
     subst; try congruence;
     auto
    ).

Goal True. idtac "Timing before: example/length". Abort.
Lemma valid_contract_length {σ} : Symbolic.ValidContract (@sep_contract_length σ) (FunDef length).
Proof. constructor. compute - [length_post Val Z.add]. solve; lia. Qed.
Goal True. idtac "Timing after: example/length". Abort.

Goal True. idtac "Timing before: example/cmp". Abort.
Lemma valid_contract_cmp : Symbolic.ValidContractReflect sep_contract_cmp (FunDef cmp).
Proof. reflexivity. Qed.
Goal True. idtac "Timing after: example/cmp". Abort.
