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
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From MicroSail Require Import
     WLP.Spec
     Syntax.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)

Inductive Enums : Set :=
| ordering.

Inductive Ordering : Set :=
| LT
| EQ
| GT.

Module ExampleTypeKit <: TypeKit.

  Definition 𝑬 : Set := Enums.
  Definition 𝑻 : Set := Empty_set.
  Definition 𝑹 : Set := Empty_set.
  Definition 𝑿 : Set := string.
  Definition 𝑿_eq_dec := string_dec.

End ExampleTypeKit.
Module ExampleTypes := Types ExampleTypeKit.
Import ExampleTypes.

(*** TERMS ***)

Module ExampleTermKit <: (TermKit ExampleTypeKit).
  Module TY := ExampleTypes.

  (** ENUMS **)
  Definition 𝑬𝑲 (E : 𝑬) : Set :=
    match E with
    | ordering => Ordering
    end.
  Program Instance Blastable_𝑬𝑲 E : Blastable (𝑬𝑲 E) :=
    match E with
    | ordering => {| blast ord k :=
                       (ord = LT -> k LT) /\
                       (ord = EQ -> k EQ) /\
                       (ord = GT -> k GT)
                  |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  (** UNIONS **)
  Definition 𝑲 (T : 𝑻) : Set := match T with end.
  Definition 𝑲_Ty (T : 𝑻) : 𝑲 T -> Ty := match T with end.
  Program Instance Blastable_𝑲 T : Blastable (𝑲 T) :=
    match T with
    end.
  Solve All Obligations with destruct a; intuition congruence.

  (** RECORDS **)
  Definition 𝑹𝑭  : Set := Empty_set.
  Definition 𝑹𝑭_Ty (R : 𝑹) : Ctx (𝑹𝑭 * Ty) := match R with end.

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | abs :     Fun [ "x" ∶ ty_int               ] ty_int
  | cmp :     Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] (ty_enum ordering)
  | gcd :     Fun [ "p" ∶ ty_int, "q" ∶ ty_int ] ty_int
  | gcdloop : Fun [ "p" ∶ ty_int, "q" ∶ ty_int ] ty_int
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.

End ExampleTermKit.
Module ExampleTerms := Terms ExampleTypeKit ExampleTermKit.
Import ExampleTerms.
Import NameResolution.

(*** PROGRAM ***)

Module ExampleProgramKit <: (ProgramKit ExampleTypeKit ExampleTermKit).
  Module TM := ExampleTerms.

  Local Coercion stm_exp : Exp >-> Stm.
  Local Open Scope exp_scope.
  Local Open Scope stm_scope.

  Local Notation "'`LT'" := (exp_lit _ (ty_enum ordering) LT).
  Local Notation "'`GT'" := (exp_lit _ (ty_enum ordering) GT).
  Local Notation "'`EQ'" := (exp_lit _ (ty_enum ordering) EQ).
  Local Notation "'p'"   := (@exp_var _ "p" _ _).
  Local Notation "'q'"   := (@exp_var _ "q" _ _).
  Local Notation "'x'"   := (@exp_var _ "x" _ _).
  Local Notation "'y'"   := (@exp_var _ "y" _ _).

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f in Fun Δ τ return Stm Δ τ with
    | abs => if: lit_int 0 <= x then x else - x
    | cmp => if: x < y then `LT else
             if: x = y then `EQ else
             if: x > y then `GT else
             fail "cmp failed"
    | gcd => "p" <- stm_call abs [p] ;;
             "q" <- stm_call abs [q] ;;
             stm_call gcdloop [p, q]
    | gcdloop =>
             let: "ord" := stm_call cmp [p, q] in
             match: exp_var "ord" in ordering with
             | LT => stm_call gcdloop [p, q - p]
             | EQ => p
             | GT => stm_call gcdloop [p - q, q]
             end
    end.

End ExampleProgramKit.
Import ExampleProgramKit.

(* ⇑ GENERATED                                                                *)
(******************************************************************************)
(* ⇓ NOT GENERATED                                                            *)

Module ExampleContractKit <: (ContractKit ExampleTypeKit ExampleTermKit ExampleProgramKit).

  Definition CEnv : ContractEnv :=
    fun σs τ f =>
      match f with
      | abs        => ContractNoFail
                        ["x" ∶ ty_int] ty_int
                        (fun x => True)
                        (fun x r => r = Z.abs x)
      | cmp        => ContractNoFail
                        ["x" ∶ ty_int, "y" ∶ ty_int] (ty_enum ordering)
                        (fun x y => True)
                        (fun x y r =>
                           match r with
                           | LT => x < y
                           | EQ => x = y
                           | GT => x > y
                           end
                           (* (x < y <-> r = LT) /\ *)
                           (* (x = y <-> r = EQ) /\ *)
                           (* (x > y <-> r = GT) *)
                        )
      | gcd        => ContractNoFail
                        ["p" ∶ ty_int, "q" ∶ ty_int] ty_int
                        (fun p q => True)
                        (fun p q r => r = Z.gcd p q)
      | gcdloop    => ContractNoFail
                        ["p" ∶ ty_int, "q" ∶ ty_int] ty_int
                        (fun p q => p >= 0 /\ q >= 0)
                        (fun p q r => r = Z.gcd p q)
      end.

End ExampleContractKit.
Import ExampleContractKit.

Module ExampleWLP := WLP ExampleTypeKit ExampleTermKit ExampleProgramKit ExampleContractKit.
Import ExampleWLP.

Lemma gcd_sub_diag_l (n m : Z) : Z.gcd (n - m) m = Z.gcd n m.
Proof. now rewrite Z.gcd_comm, Z.gcd_sub_diag_r, Z.gcd_comm. Qed.

Ltac validate_destr :=
  match goal with
  | [ |- _ -> _ ]  => intro
  | [ |- True ]  => constructor
  | [ H: True |- _ ] => clear H
  | [ H: False |- _ ] => destruct H
  | [ H: Env _ (ctx_snoc _ _) |- _ ] => dependent destruction H
  | [ H: Env _ ctx_nil |- _ ] => dependent destruction H
  | [ H: Env' _ (ctx_snoc _ _) |- _ ] => dependent destruction H
  | [ H: Env' _ ctx_nil |- _ ] => dependent destruction H
  end.

Ltac validate_simpl :=
  repeat
    (cbn in *; repeat validate_destr; destruct_conjs; subst;
     rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_gt, ?Z.ltb_ge, ?Z.ltb_lt, ?Z.leb_le, ?Z.gtb_ltb,
       ?Z.gcd_diag, ?Z.gcd_abs_l, ?Z.gcd_abs_r, ?Z.gcd_sub_diag_r, ?gcd_sub_diag_l in *).

Ltac validate_case :=
  match goal with
  | [ |- match ?e with _ => _ end _ _ ] =>
    case_eq e
  | [ |- WLP match ?e with _ => _ end _ _ ] =>
    case_eq e
  end.

Ltac validate_solve :=
  repeat
    (validate_simpl; intuition;
     try lia;
     try validate_case).

Lemma validCEnv : ValidContractEnv CEnv.
Proof. intros σs τ [] δ; validate_solve. Qed.

(* Print Assumptions validCEnv. *)
