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

Notation "x ∶ τ" := (pair x τ) (at level 90, no associativity) : ctx_scope.
Notation "[ x ]" := (ctx_snoc ctx_nil x) : ctx_scope.
Notation "[ x , .. , z ]" := (ctx_snoc .. (ctx_snoc ctx_nil x) .. z) : ctx_scope.

Module ExampleTermKit <: (TermKit ExampleTypeKit).
  Module TY := ExampleTypes.

  (* Names of union data constructors. *)
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

  Definition 𝑲 (T : 𝑻) : Set := match T with end.
  Definition 𝑲_Ty (T : 𝑻) : 𝑲 T -> Ty := match T with end.
  Program Instance Blastable_𝑲 T : Blastable (𝑲 T) :=
    match T with
    end.
  Solve All Obligations with destruct a; intuition congruence.

  Definition 𝑹𝑭  : Set := Empty_set.
  Definition 𝑹𝑭_Ty (R : 𝑹) : Ctx (𝑹𝑭 * Ty) := match R with end.

  (* Names of functions. *)
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

Notation "[ x , .. , z ]" :=
  (tuplepat_snoc .. (tuplepat_snoc tuplepat_nil x) .. z) : pat_scope.
Notation "[ x , .. , z ]" :=
  (env_snoc .. (env_snoc env_nil _ x) .. _ z) : exp_scope.

Notation "e1 * e2" := (exp_times e1 e2) : exp_scope.
Notation "e1 - e2" := (exp_minus e1 e2) : exp_scope.
Notation "e1 < e2" := (exp_lt e1 e2) : exp_scope.
Notation "e1 > e2" := (exp_gt e1 e2) : exp_scope.
Notation "e1 <= e2" := (exp_le e1 e2) : exp_scope.
Notation "e1 = e2" := (exp_eq e1 e2) : exp_scope.
Notation "'lit_int' l" := (exp_lit _ ty_int l) (at level 1, no associativity) : exp_scope.
Notation "'lit_unit'" := (exp_lit _ ty_unit tt) (at level 1, no associativity) : exp_scope.

Local Coercion stmexp := @stm_exp.

Module ExampleProgramKit <: (ProgramKit ExampleTypeKit ExampleTermKit).
  Module TM := ExampleTerms.

  Local Open Scope exp_scope.

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f in Fun Δ τ return Stm Δ τ with
    | abs =>
      stm_if
        (lit_int (0%Z) <= exp_var "x")
        (exp_var "x")
        (exp_neg (exp_var "x"))
    | cmp =>
      stm_if (exp_var "x" < exp_var "y")
        (stm_lit (ty_enum ordering) LT)
      (stm_if (exp_var "x" = exp_var "y")
        (stm_lit (ty_enum ordering) EQ)
      (stm_if (exp_var "x" > exp_var "y")
        (stm_lit (ty_enum ordering) GT)
        (stm_fail (ty_enum ordering) "compare")))
    | gcd =>
      stm_let "p'" ty_int (stm_call abs [exp_var "p"])
      (stm_let "q'" ty_int (stm_call abs [exp_var "q"])
        (stm_call gcdloop [exp_var "p'", exp_var "q'"]))
    | gcdloop =>
      stm_let "ord" (ty_enum ordering)
        (stm_call cmp [exp_var "p", exp_var "q"])
        (stm_match_enum ordering (exp_var "ord")
           (fun K =>
              match K with
              | LT => stm_call gcdloop (env_snoc (env_snoc env_nil ("p" , ty_int) (exp_var "p")) ("q" , ty_int) (exp_var "q" - exp_var "p"))
              | EQ => stm_exp (exp_var "p")
              | GT => stm_call gcdloop (env_snoc (env_snoc env_nil ("p" , ty_int) (exp_var "p" - exp_var "q")) ("q" , ty_int) (exp_var "q"))
              end))
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
