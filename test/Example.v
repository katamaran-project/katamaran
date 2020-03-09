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
     Logic.FinFun
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     WLP.Spec
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

Instance Enums_eq_dec : EqDec Enums.
  unfold EqDec; decide equality.
Defined.

Inductive Ordering : Set :=
| LT
| EQ
| GT.

(** Unions **)
Inductive Unions : Set :=
| either
.


Inductive EitherConstructor : Set :=
| Left
| Right.

Instance Unions_eq_dec : EqDec Unions.
  unfold EqDec; decide equality.
Defined.

(** Records **)
Inductive Records : Set :=
.

Instance Records_eq_dec : EqDec Records.
  unfold EqDec; decide equality.
Defined.

Module ExampleTypeKit <: TypeKit.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬𝑲 (E : 𝑬) : Set :=
    match E with
    | ordering => Ordering
    end.
  Program Instance Blastable_𝑬𝑲 E : Blastable (𝑬𝑲 E) :=
    match E with
    | ordering => {| blast ord POST :=
                       (ord = LT -> POST LT) /\
                       (ord = EQ -> POST EQ) /\
                       (ord = GT -> POST GT)
                  |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  Definition 𝑼        := Unions.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    | either => (string + Z)%type
    end.
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | either => EitherConstructor
    end.
  Program Instance Blastable_𝑼𝑲 U : Blastable (𝑼𝑲 U) :=
    match U with
    | either => {| blast v POST :=
                     (v = Left  -> POST Left) /\
                     (v = Right -> POST Right)
                |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  Definition 𝑹        := Records.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    end.

  Definition 𝑿        := string.

  Definition 𝑬_eq_dec := Enums_eq_dec.
  Definition 𝑬𝑲_eq_dec : forall (e : 𝑬) (x y : 𝑬𝑲 e), {x=y}+{~x=y}.
  Proof. unfold 𝑬𝑲 in *. intros. destruct e. decide equality. Qed.
  Definition 𝑼_eq_dec := Unions_eq_dec.
  Definition 𝑼𝑻_eq_dec : forall (u : 𝑼) (x y : 𝑼𝑻 u), {x=y}+{~x=y}.
  Proof.
    unfold 𝑼𝑻 in *.
    intros. destruct u.
    pose string_dec.
    pose Z.eq_dec.
    decide equality.
  Qed.
  Definition 𝑼𝑲_eq_dec : forall (u : 𝑼) (x y : 𝑼𝑲 u), {x=y}+{~x=y}.
  Proof. intros. destruct u. decide equality. Qed.
  Definition 𝑹_eq_dec := Records_eq_dec.
  Definition 𝑹𝑻_eq_dec : forall (r : 𝑹) (x y : 𝑹𝑻 r), {x=y}+{~x=y}.
  Proof. intros. destruct r. Qed.
  Definition 𝑿_eq_dec := string_dec.

  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.
  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.

End ExampleTypeKit.
Module ExampleTypes := Types ExampleTypeKit.
Import ExampleTypes.

(*** TERMS ***)

Module ExampleTermKit <: (TermKit ExampleTypeKit).
  Module TY := ExampleTypes.

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
                  | existT _ Left v  => inl v
                  | existT _ Right v => inr v
                  end
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    | either => fun Kv =>
                  match Kv with
                  | inl v => existT _ Left v
                  | inr v => existT _ Right v
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

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | abs :     Fun [ "x" ∶ ty_int               ] ty_int
  | cmp :     Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] (ty_enum ordering)
  | gcd :     Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] ty_int
  | gcdloop : Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] ty_int
  | msum :    Fun [ "x" ∶ ty_union either, "y" ∶ ty_union either] (ty_union either)
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.

  Definition 𝑹𝑬𝑮 : Ty -> Set := fun _ => Empty_set.
  Definition 𝑹𝑬𝑮_eq_dec {σ τ} (x : 𝑹𝑬𝑮 σ) (y : 𝑹𝑬𝑮 τ) : {x ≡ y}+{~ x ≡ y}.
  Proof.
    destruct x; destruct y; cbn;
      first
        [ left; now apply tyeq_refl with eq_refl
        | right; intros [eqt eqr];
          rewrite <- (Eqdep_dec.eq_rect_eq_dec Ty_eq_dec) in eqr; discriminate
        ].
  Defined.

  Definition 𝑨𝑫𝑫𝑹 : Set := Empty_set.

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
  Local Notation "'`Left' e" := (exp_union either Left e) (at level 10, e at level 9).
  Local Notation "'`Right' e" := (exp_union either Right e) (at level 10, e at level 9).
  Local Notation "'x'"   := (@exp_var _ "x" _ _).
  Local Notation "'y'"   := (@exp_var _ "y" _ _).
  Local Notation "'z'"   := (@exp_var _ "z" _ _).

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ.
    let pi := eval compute in
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
    | msum =>
             match: x in either with
             | Left  "z" => `Left z
             | Right "z" => y
             end
    end in exact pi.
  Defined.

Definition RegStore : Set := Empty_set.

Definition read_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) : Lit σ :=
  match r with end.

Definition write_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) : RegStore :=
  match r with end.

Definition read_write (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
    read_register (write_register γ r v) r = v := match r with end.

Definition write_read (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) :
    (write_register γ r (read_register γ r)) = γ := match r with end.

Definition write_write (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ) :
    write_register (write_register γ r v1) r v2 = write_register γ r v2 :=
  match r with end.

Definition Memory : Set := Empty_set.

Definition read_memory (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) : Lit ty_int :=
  match addr with end.

Definition write_memory (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Lit ty_int) : Memory :=
  match addr with end.

  (* Definition RegStore := GenericRegStore. *)
  (* Definition read_register := generic_read_register. *)
  (* Definition write_register := generic_write_register. *)
  (* Definition read_write := generic_read_write. *)
  (* Definition write_read := generic_write_read. *)
  (* Definition write_write := generic_write_write. *)

End ExampleProgramKit.

Module ExamplePrograms :=
  Programs ExampleTypeKit ExampleTermKit ExampleProgramKit.
Import ExamplePrograms.
Import ExampleProgramKit.

(* ⇑ GENERATED                                                                *)
(******************************************************************************)
(* ⇓ NOT GENERATED                                                            *)

Module SepContracts.

  Module ExampleAssertionKit <:
    (AssertionKit ExampleTypeKit ExampleTermKit ExampleProgramKit).
    Module PM := Programs ExampleTypeKit ExampleTermKit ExampleProgramKit.

    Definition 𝑷 := Empty_set.
    Definition 𝑷_Ty : 𝑷 -> Ctx Ty := fun p => match p with end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := fun p => match p with end.
  End ExampleAssertionKit.

  Module ExampleAssertions :=
    Assertions ExampleTypeKit ExampleTermKit ExampleProgramKit ExampleAssertionKit.
  Import ExampleAssertions.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

  Module ExampleSymbolicContractKit <:
    SymbolicContractKit ExampleTypeKit ExampleTermKit ExampleProgramKit ExampleAssertionKit.
    Module ASS := ExampleAssertions.

    Open Scope env_scope.

    (* Arguments asn_prop [_] & _. *)

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | abs =>
          @sep_contract_result
            ["x" ∶ ty_int]
            ["x" ∶ ty_int]
            ty_int
            [term_var "x"]%arg
            "result"
            asn_true
            (@asn_prop
               ["x" ∶ ty_int, "result" ∶ ty_int]
               (fun x result => result = Z.abs x))
            (* (asn_if *)
            (*    (term_binop binop_lt (term_var "x") (term_lit ty_int 0)) *)
            (*    (asn_bool (term_binop binop_eq (term_var "result") (term_neg (term_var "x")))) *)
            (*    (asn_bool (term_binop binop_eq (term_var "result") (term_var "x")))) *)
        | cmp =>
          @sep_contract_result
            ["x" ∶ ty_int, "y" ∶ ty_int]
            ["x" ∶ ty_int, "y" ∶ ty_int]
            (ty_enum ordering)
            [term_var "x", term_var "x"]%arg
            "result"
            asn_true
            (asn_match_enum
               ordering (term_var "result")
               (fun result =>
                  match result with
                  | LT => asn_bool (term_binop binop_lt (term_var "x") (term_var "y"))
                  | EQ => asn_bool (term_binop binop_eq (term_var "x") (term_var "y"))
                  | GT => asn_bool (term_binop binop_gt (term_var "x") (term_var "y"))
                  end))
        | gcd =>
          @sep_contract_result
            ["x" ∶ ty_int, "y" ∶ ty_int]
            ["x" ∶ ty_int, "y" ∶ ty_int]
            ty_int
            [term_var "x", term_var "x"]%arg
            "result"
            asn_true
            (@asn_prop
               ["x" ∶ ty_int, "y" ∶ ty_int, "result" ∶ ty_int]
               (fun x y result => result = Z.gcd x y))
        | gcdloop =>
          @sep_contract_result
            ["x" ∶ ty_int, "y" ∶ ty_int]
            ["x" ∶ ty_int, "y" ∶ ty_int]
            ty_int
            [term_var "x", term_var "x"]%arg
            "result"
            (asn_bool (term_binop binop_le (term_lit ty_int 0) (term_var "x")) ✱
             asn_bool (term_binop binop_le (term_lit ty_int 0) (term_var "y")))
            (@asn_prop
               ["x" ∶ ty_int, "y" ∶ ty_int, "result" ∶ ty_int]
               (fun x y result => result = Z.gcd x y))
        | msum => sep_contract_none _
        end.

  End ExampleSymbolicContractKit.

  Module ExampleSymbolicContracts :=
    SymbolicContracts
      ExampleTypeKit
      ExampleTermKit
      ExampleProgramKit
      ExampleAssertionKit
      ExampleSymbolicContractKit.
  Import ExampleSymbolicContracts.

End SepContracts.

Module WLPContracts.

  Module ExampleContractKit <: (ContractKit ExampleTypeKit ExampleTermKit ExampleProgramKit).
    Module PM := ExamplePrograms.

    Definition CEnv : ContractEnv :=
      fun σs τ f =>
        match f with
        | abs        => ContractNoFail
                          ["x" ∶ ty_int] ty_int
                          (fun x γ => True)
                          (fun x r γ => r = Z.abs x)
        | cmp        => ContractNoFail
                          ["x" ∶ ty_int, "y" ∶ ty_int] (ty_enum ordering)
                          (fun x y γ => True)
                          (fun x y r γ =>
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
                          ["x" ∶ ty_int, "y" ∶ ty_int] ty_int
                          (fun x y γ => True)
                          (fun x y r γ => r = Z.gcd x y)
        | gcdloop    => ContractNoFail
                          ["x" ∶ ty_int, "y" ∶ ty_int] ty_int
                          (fun x y γ => x >= 0 /\ y >= 0)
                          (fun x y r γ => r = Z.gcd x y)
        | msum       => ContractNone
                          [ "x" ∶ ty_union either, "y" ∶ ty_union either] (ty_union either)
        end.

  End ExampleContractKit.
  Import ExampleContractKit.

  Module ExampleWLP := WLP ExampleTypeKit ExampleTermKit ExampleProgramKit ExampleContractKit.
  Import ExampleWLP.

  Lemma gcd_sub_diag_l (n m : Z) : Z.gcd (n - m) m = Z.gcd n m.
  Proof. now rewrite Z.gcd_comm, Z.gcd_sub_diag_r, Z.gcd_comm. Qed.

  Ltac wlp_cbv :=
    cbv [Blastable_𝑬𝑲 CEnv Forall Lit ValidContract WLP abstract blast
                      blastable_lit env_lookup env_map env_update eval evals inctx_case_snoc
                      snd uncurry eval_prop_true eval_prop_false eval_binop
        ].

  Ltac validate_solve :=
    repeat
      (intros; subst;
       rewrite ?Z.gcd_diag, ?Z.gcd_abs_l, ?Z.gcd_abs_r, ?Z.gcd_sub_diag_r,
       ?gcd_sub_diag_l;
       intuition (try lia)
      ).

  Lemma validCEnv : ValidContractEnv CEnv.
  Proof. intros σs τ []; wlp_cbv; validate_solve. Qed.

End WLPContracts.
