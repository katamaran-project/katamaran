From Coq Require Import
     Logic.FinFun
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia
     Logic.FunctionalExtensionality.

From Equations Require Import
     Equations.

From MicroSail Require Import
     (* WLP.Spec *)
     Notation
     SmallStep.Step
     Syntax.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Inductive Unions : Set := instruction.

Lemma Unions_eq_dec : EqDec Unions.
  unfold EqDec.
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
  (* Names are inspired by sail-riscv naming convention *)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read registers *)
  | rX  : Fun ["reg_code" ∶ ty_int] ty_int
  (* write register *)
  | wX : Fun ["reg_code" ∶ ty_int, "reg_value" ∶ ty_int] ty_int
  (* read flag *)
  | rF      : Fun ["flag_code" ∶ ty_int] ty_bool
  (* write flag *)
  | wF     : Fun ["flag_code" ∶ ty_int, "flag_value" ∶ ty_bool] ty_bool
  (* read memory *)
  | rM    : Fun ["address" ∶ ty_int] ty_int
  (* write memory *)
  | wM   : Fun ["address" ∶ ty_int, "mem_value" ∶ ty_int] ty_int
  (* check memory bounds *)
  | in_bounds : Fun ["address" ∶ ty_int] ty_bool
  (* semantics of a single instruction *)
  | semantics : Fun [ "x" ∶ ty_union instruction] ty_unit
  .

  Definition 𝑭 : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.

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

  Inductive Address : Set :=
    A0 | A1 | A2 | A3.

  Definition Address_eq_dec : EqDec Address.
  Proof.
    unfold EqDec.
    decide equality.
  Defined.

  Definition 𝑨𝑫𝑫𝑹 : Set := Address.

End ExampleTermKit.
Module ExampleTerms := Terms ExampleTypeKit ExampleTermKit.
Import ExampleTerms.
Import NameResolution.

Module ExampleProgramKit <: (ProgramKit ExampleTypeKit ExampleTermKit).
  Module TM := ExampleTerms.

  Local Definition lit_true {Γ}  : Exp Γ ty_bool := exp_lit _ _ (untag (taglit_bool true)).
  Local Definition lit_false {Γ} : Exp Γ ty_bool := exp_lit _ _ (untag (taglit_bool false)).
  Local Definition int_lit {Γ} (literal : Z) : Exp Γ ty_int :=
    exp_lit _ _ (untag (taglit_int literal)).

  (* REGISTER STORE *)
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

  Lemma read_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Lit σ),
      read_register (write_register γ r v) r = v.
  Proof.
    intros γ σ r v. now destruct r.
  Qed.

  Lemma write_read : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ),
      (write_register γ r (read_register γ r)) = γ.
  Proof.
    intros γ σ r.
    unfold read_register.
    extensionality σ'.
    extensionality r'.
    destruct r';
    destruct r;
    now simp write_register.
  Qed.

  Lemma write_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ),
            write_register (write_register γ r v1) r v2 = write_register γ r v2.
  Proof.
    intros γ σ r v1 v2.
    now destruct r.
  Qed.

  (* MEMORY *)
  Definition Memory := 𝑨𝑫𝑫𝑹 -> Lit ty_int.

  (* Address space bounds *)
  Definition Memory_lb {Γ} : Exp Γ ty_int := int_lit 0.
  Definition Memory_hb {Γ} : Exp Γ ty_int := int_lit 3.

  Definition read_memory (μ : Memory) (addr : 𝑨𝑫𝑫𝑹 ) : Lit ty_int :=
    μ addr.

  Definition write_memory (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Lit ty_int) : Memory :=
    fun addr' => match (Address_eq_dec addr addr') with
              | left eq_refl => v
              | right _ => μ addr'
              end.

  Local Coercion stm_exp : Exp >-> Stm.
  Local Open Scope exp_scope.
  Local Open Scope stm_scope.

  Local Notation "'x'"   := (@exp_var _ "x" _ _).
  Local Notation "'y'"   := (@exp_var _ "y" _ _).
  Local Notation "'z'"   := (@exp_var _ "z" _ _).
  Local Notation "'reg_code'" := (@exp_var _ "reg_code" ty_int _).
  Local Notation "'reg_value'" := (@exp_var _ "reg_value" ty_int _).
  Local Notation "'flag_code'" := (@exp_var _ "flag_code" ty_int _).
  Local Notation "'flag_value'" := (@exp_var _ "flag_value" ty_bool _).
  Local Notation "'address'" := (@exp_var _ "address" ty_int _).
  Local Notation "'mem_value'" := (@exp_var _ "mem_value" ty_int _).
  Local Definition nop {Γ} : Stm Γ ty_unit := stm_lit _ (untag taglit_unit).

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ.
    let pi := eval compute in
    match f in Fun Δ τ return Stm Δ τ with
    | rX =>
      if:      reg_code = int_lit 0 then stm_read_register R0
      else if: reg_code = int_lit 1 then stm_read_register R1
      else if: reg_code = int_lit 2 then stm_read_register R2
      else if: reg_code = int_lit 3 then stm_read_register R3
      else     stm_fail _ "read_register: invalid register"
    | wX =>
      if:      reg_code = int_lit 0 then stm_write_register R0 reg_value
      else if: reg_code = int_lit 1 then stm_write_register R1 reg_value
      else if: reg_code = int_lit 2 then stm_write_register R2 reg_value
      else if: reg_code = int_lit 3 then stm_write_register R3 reg_value
      else     stm_fail _ "write_register: invalid register"
    | rF =>
      if:      flag_code = int_lit 5 then stm_read_register Halted
      else if: flag_code = int_lit 6 then stm_read_register Overflow
      else if: flag_code = int_lit 7 then stm_read_register OutOfMemory
      else     stm_fail _ "read_register: invalid register"
    | wF =>
      if:      flag_code = int_lit 5 then stm_write_register Halted flag_value
      else if: flag_code = int_lit 6 then stm_write_register Overflow flag_value
      else if: flag_code = int_lit 7 then stm_write_register OutOfMemory flag_value
      else     stm_fail _ "write_register: invalid register"
    | rM =>
      stm_fail _ "read_memory: not implemented"
    | wM =>
      stm_fail _ "write_memory: invalid register"
    | in_bounds => exp_and (exp_or (address = Memory_lb) (address > Memory_lb))
                          (address < Memory_hb)
    | semantics => (@stm_match_union _ instruction x _
        (fun K => match K with
               | Halt => ""
               | Load => "load_args"
               | Add => "add_args"
               | Jump => "jump_args"
               end)
        (fun K => match K return Stm _ _ with
               | Halt =>
                 stm_write_register Halted lit_true ;; nop
               | Load =>
                 match: (exp_var "load_args") in (ty_int , ty_int) with
                 | ("dest", "source") =>
                      let: "x" := call rM (exp_var "source")
                   in let: "safe" := call in_bounds (exp_var "source")
                   in if: (exp_var "safe")
                      then (call wX (exp_var "dest") (exp_var "x");;nop)
                      else (stm_write_register OutOfMemory lit_true;; nop)
                  end
               | Add => stm_fail _ "not implemented"
               | Jump => stm_fail _ "not implemented"
               end))
    end in exact pi.
  Defined.

End ExampleProgramKit.
Import ExampleProgramKit.

Module ISASmappStep := SmallStep ExampleTypeKit ExampleTermKit ExampleProgramKit.
Import ISASmappStep.
Import CtxNotations.
Lemma t :
  forall
    (* (x : ty_union instruction) *)
    (* (Γ : ["x" ∶ ty_union instruction]) *)
    (γ : RegStore) (μ : Memory) (δ : LocalStore _),
    ⟨ γ , μ , δ , @Pi ["x" ∶ ty_union instruction] ty_unit semantics ⟩ --->
    ⟨ γ , μ , δ , stm_fail _ "not implemented" ⟩.
Proof.
  intros.
  destruct (Pi semantics);
  (* Focus 19. *)
  match goal with
  | [ γ : RegStore |- ⟨ ?γ , ?μ , ?δ , (stm_read_register _ ) ⟩ ---> ⟨ ?γ , ?μ , ?δ , _ ⟩ ] => idtac
  end.
  match goal with
  | [ |- ⟨ γ , μ , δ , (stm_match_union _ _ _ _) ⟩ ---> ⟨ γ , μ , δ , _ ⟩ ] => idtac
  end.

Check (Pi semantics).
