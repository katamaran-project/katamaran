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
     WLP.Spec
     Syntax.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Inductive Unions := instruction.

Lemma Unions_eq_dec : EqDec Unions.
  unfold EqDec.
  intros x y.
  destruct x. destruct y.
  decide equality.
Qed.

Inductive Instruction :=
    Halt
  | Load
  | Add
  | Jump
  .

(** Describe a part of REDFIN ISA
    Property to verify:
      Every instruction is memory safe, i.e. it checks memory
      access and sets the 'OutOfMemory' flag if out of memory
      access has been attempted. *)
Module ExampleTypeKit <: TypeKit.

  Definition 𝑬        := Empty_set.
  Definition 𝑼        := Unions.
  Definition 𝑹        := Empty_set.
  Definition 𝑿        := string.

  Definition 𝑬_eq_dec : EqDec 𝑬 := ltac:(unfold EqDec; decide equality).
  Definition 𝑼_eq_dec : EqDec 𝑼 := Unions_eq_dec.
  Definition 𝑹_eq_dec : EqDec 𝑹 := ltac:(unfold EqDec; decide equality).
  Definition 𝑿_eq_dec : EqDec 𝑿 := string_dec.

End ExampleTypeKit.
Module ExampleTypes := Types ExampleTypeKit.
Import ExampleTypes.

Module ExampleTermKit <: (TermKit ExampleTypeKit).
  Module TY := ExampleTypes.
  Open Scope lit_scope.
  (** ENUMS **)

  Definition 𝑬𝑲 (E : 𝑬) : Set := Empty_set.
  Program Instance Blastable_𝑬𝑲 E : Blastable (𝑬𝑲 E) :=
    match E with end.

  (** UNIONS **)
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | instruction => Instruction
    end.
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | instruction => fun K => match K with
                          | Halt => ty_unit
                          (* Load has two fields: register label and memory address *)
                          (* represented as ints *)
                          | Load => ty_prod ty_int ty_int
                          | Add => ty_prod ty_int ty_int
                          | Jump => ty_int
                          end
    end.
  Program Instance Blastable_𝑼𝑲 U : Blastable (𝑼𝑲 U) :=
    match U with
    | instruction => {| blast v POST :=
                     (v = Halt  -> POST Halt) /\
                     (v = Load -> POST Load)  /\
                     (v = Add -> POST Add)    /\
                     (v = Jump -> POST Jump)
                |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  (** RECORDS **)
  Definition 𝑹𝑭  : Set := Empty_set.
  Definition 𝑹𝑭_Ty (R : 𝑹) : Ctx (𝑹𝑭 * Ty) := match R with end.

  (** FUNCTIONS **)
  (* Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set := *)
  (* | abs :     Fun [ "x" ∶ ty_int               ] ty_int *)
  (* | cmp :     Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] ty_int *)
  (* | gcd :     Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] ty_int *)
  (* | gcdloop : Fun [ "x" ∶ ty_int, "y" ∶ ty_int ] ty_int *)
  (* | msum :    Fun [ "x" ∶ ty_int , "y" ∶ ty_int ] ty_int *)
  (* . *)

  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | semantics : Fun [ "x" ∶ ty_union instruction] ty_unit
  | ihalt : Fun ε ty_unit
  | iload : Fun [ "dest_reg" ∶ ty_int , "src_addr" ∶ ty_int ] ty_unit
  | iadd  : Fun [ "dest_reg" ∶ ty_int , "src_addr" ∶ ty_int ] ty_unit
  | ijump : Fun [ "offset" ∶ ty_int ] ty_unit
  .

  Definition 𝑭 := Fun.

  Inductive Reg : Ty -> Set :=
      Halted      : Reg ty_bool
    | Overflow    : Reg ty_bool
    | OutOfMemory : Reg ty_bool

    | R0 : Reg ty_int
    | R1 : Reg ty_int
    | R2 : Reg ty_int
    | R3 : Reg ty_int
    .
  Definition 𝑹𝑬𝑮 := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : forall σ, EqDec (𝑹𝑬𝑮 σ).
  Proof.
    unfold EqDec.
    dependent destruction x;
    dependent destruction y;
    (now right) || (now left).
  Defined.
End ExampleTermKit.
Module ExampleTerms := Terms ExampleTypeKit ExampleTermKit.
Import ExampleTerms.
Import NameResolution.

Module ExampleProgramKit <: (ProgramKit ExampleTypeKit ExampleTermKit).
  Module TM := ExampleTerms.

  Definition RegStore := forall σ, 𝑹𝑬𝑮 σ -> Lit σ.

  Definition read_register (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) : Lit σ :=
    γ σ r.

  Equations write_register (γ : RegStore) {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) : RegStore :=
    write_register γ Halted      v Halted      := v;
    write_register γ OutOfMemory v OutOfMemory := v;
    write_register γ Overflow    v Overflow    := v;
    write_register γ R0 v R0 := v;
    write_register γ R1 v R1 := v;
    write_register γ R2 v R2 := v;
    write_register γ R3 v R3 := v;
    write_register γ r1 v r2 := γ _ r2.

  Local Coercion stm_exp : Exp >-> Stm.
  Local Open Scope exp_scope.
  Local Open Scope stm_scope.

  Local Notation "'x'"   := (@exp_var _ "x" _ _).
  Local Notation "'y'"   := (@exp_var _ "y" _ _).
  Local Notation "'z'"   := (@exp_var _ "z" _ _).

  Local Notation "'load_args'"   := (exp_pair _ _).
  Local Notation "'y'"   := (@exp_var _ "y" _ _).
  Local Notation "'z'"   := (@exp_var _ "z" _ _).

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ.
    let pi := eval compute in
    match f in Fun Δ τ return Stm Δ τ with
    | semantics => (@stm_match_union _ instruction x _
        (fun K => match K with
               | Halt => ""
               | Load => "load_args"
               | Add => "add_args"
               | Jump => "jump_args"
               end)
        (fun K => match K return Stm _ _ with
               | Halt => stm_fail _ "not implemented"
               | Load => stm_match_pair (exp_var "load_args") "dest" "source"
                                       (stm_fail _ "not implemented")
               | Add => stm_fail _ "not implemented"
               | Jump => stm_fail _ "not implemented"
               (* | alt2%exp => rhs2%stm *)
               end))
    | ihalt => stm_fail _ "not implemented"
    | iload => stm_fail _ "not implemented"
    | iadd => stm_fail _ "not implemented"
    | ijump => stm_fail _ "not implemented"
    end in exact pi.
  Defined.

End ExampleProgramKit.
Import ExampleProgramKit.
