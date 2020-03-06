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
     Notation
     SmallStep.Step
     SmallStep.Progress
     Syntax
     Sep.Outcome
     Sep.Spec.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Inductive Enums : Set := register_tag.

Definition Enums_eq_dec : EqDec Enums := ltac:(unfold EqDec; decide equality).

Inductive RegisterTag :=
  RegTag0 | RegTag1 | RegTag2 | RegTag3.

Inductive Unions : Set := instruction.

Lemma Unions_eq_dec : EqDec Unions.
  unfold EqDec.
  decide equality.
Qed.

Inductive Instruction :=
| Halt
| Load (dst src : Z)
| Add  (dst src : Z)
| Jump (dst : Z)
.

Inductive InstructionConstructor :=
| KHalt
| KLoad
| KAdd
| KJump
.

(** Describe a part of REDFIN ISA
    Property to verify:
      Every instruction is memory safe, i.e. it checks memory
      access and sets the 'OutOfMemory' flag if out of memory
      access has been attempted. *)
Module ISATypeKit <: TypeKit.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬𝑲 (E : 𝑬) : Set :=
    match E with
    | register_tag => RegisterTag
    end.
  Program Instance Blastable_𝑬𝑲 E : Blastable (𝑬𝑲 E) :=
    match E with
    | register_tag => {| blast v POST :=
                     (v = RegTag0  -> POST RegTag0) /\
                     (v = RegTag1 -> POST RegTag1)  /\
                     (v = RegTag2 -> POST RegTag2)    /\
                     (v = RegTag3 -> POST RegTag3)
                |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  (** UNIONS **)
  Definition 𝑼        := Unions.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    | instruction => Instruction
    end.
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.
  Program Instance Blastable_𝑼𝑲 U : Blastable (𝑼𝑲 U) :=
    match U with
    | instruction => {| blast v POST :=
                     (v = KHalt  -> POST KHalt) /\
                     (v = KLoad -> POST KLoad)  /\
                     (v = KAdd -> POST KAdd)    /\
                     (v = KJump -> POST KJump)
                |}
    end.
  Solve All Obligations with destruct a; intuition congruence.

  Definition 𝑹        := Empty_set.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    end.

  Definition 𝑿        := string.

  Definition 𝑬_eq_dec : EqDec 𝑬 := ltac:(unfold EqDec; decide equality).
  Definition 𝑬𝑲_eq_dec : forall (e : 𝑬), EqDec (𝑬𝑲 e).
  Proof.
    intros. unfold EqDec.
    intros x y. destruct e. decide equality.
  Qed.
  Definition 𝑼_eq_dec : EqDec 𝑼 := Unions_eq_dec.
  Definition 𝑼𝑻_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑻 u).
  Proof.
    unfold EqDec. intros.
    destruct u. unfold 𝑼𝑻. pose string_dec. pose Z.eq_dec. decide equality.
  Qed.
  Definition 𝑼𝑲_eq_dec : forall (u : 𝑼), EqDec(𝑼𝑲 u).
  Proof. unfold EqDec. destruct u. decide equality. Qed.
  Definition 𝑹_eq_dec : EqDec 𝑹 := ltac:(unfold EqDec; decide equality).
  Definition 𝑹𝑻_eq_dec : forall (r : 𝑹), EqDec (𝑹𝑻 r).
  Proof. unfold EqDec. destruct r. Qed.
  Definition 𝑿_eq_dec : EqDec 𝑿 := string_dec.

  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.
  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.

End ISATypeKit.
Module ISATypes := Types ISATypeKit.
Import ISATypes.

Module ISATermKit <: (TermKit ISATypeKit).
  Module TY := ISATypes.

  Open Scope lit_scope.

  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | instruction => fun K => match K with
                          | KHalt => ty_unit
                          (* Load has two fields: a register label and a memory address, *)
                          (* represented as ints *)
                          | KLoad => ty_prod ty_int ty_int
                          | KAdd => ty_prod ty_int ty_int
                          | KJump => ty_int
                          end
    end.
  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | instruction => fun Kv =>
                       match Kv with
                       | existT _ KHalt tt        => Halt
                       | existT _ KLoad (dst,src) => Load dst src
                       | existT _ KAdd (dst,src)  => Add dst src
                       | existT _ KJump dst       => Jump dst
                       end
    end.

  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U with
    | instruction => fun Kv =>
                       match Kv with
                       | Halt         => existT _ KHalt tt
                       | Load dst src => existT _ KLoad (dst,src)
                       | Add dst src  => existT _ KAdd (dst,src)
                       | Jump dst     => existT _ KJump dst
                       end
    end.
  Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold U (𝑼_unfold U Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) }),
      𝑼_unfold U (𝑼_fold U Kv) = Kv.
  Proof. intros [] [[] l]; cbn in *; destruct_conjs;
         repeat match goal with
                | [l : unit |- _] => destruct l
                end; reflexivity.
  Qed.

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
  (* Names are inspired by sail-riscv naming convention *)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read registers *)
  | rX  : Fun ["reg_tag" ∶ ty_enum register_tag ] ty_int
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
  | semantics : Fun [ "instr" ∶ ty_union instruction] ty_unit
  | swapreg : Fun ["r1" ∶ ty_int, "r2" ∶ ty_int] ty_unit
  | swapreg12 : Fun ctx_nil ty_unit
  | add : Fun [ "x" ∶ ty_int , "y" ∶ ty_int ] ty_int
  | double : Fun [ "z" ∶ ty_int ] ty_int
  | add3 : Fun [ "x" ∶ ty_int , "y" ∶ ty_int , "z" ∶ ty_int ] ty_int
  .

  Definition 𝑭 : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.

  (* Flags are represented as boolean-valued registers;
     additionally, there are four general-purpose int-value registers
   *)
  Inductive Reg : Ty -> Set :=
      Halted      : Reg ty_bool
    | Overflow    : Reg ty_bool
    | OutOfMemory : Reg ty_bool

    | R0 : Reg ty_int
    | R1 : Reg ty_int
    | R2 : Reg ty_int
    | R3 : Reg ty_int
    .

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec {σ τ} (x : 𝑹𝑬𝑮 σ) (y : 𝑹𝑬𝑮 τ) : {x ≡ y}+{ ~ x ≡ y}.
  Proof.
    destruct x; destruct y; cbn;
      first
        [ left; now apply teq_refl with eq_refl
        | right; intros [eqt eqr];
          try rewrite <- (Eqdep_dec.eq_rect_eq_dec Ty_eq_dec) in eqr; discriminate
        ].
  Defined.

  (* A silly address space of four addresses *)
  Inductive Address : Set :=
    A0 | A1 | A2 | A3.

  Definition Address_eq_dec : EqDec Address.
  Proof.
    unfold EqDec.
    decide equality.
  Defined.

  Definition 𝑨𝑫𝑫𝑹 : Set := Address.

End ISATermKit.
Module ISATerms := Terms ISATypeKit ISATermKit.
Import ISATerms.
Import NameResolution.

Module ISAProgramKit <: (ProgramKit ISATypeKit ISATermKit).
  Module TM := ISATerms.

  Definition lit_true {Γ}  : Exp Γ ty_bool := exp_lit _ ty_bool true.
  Definition lit_false {Γ} : Exp Γ ty_bool := exp_lit _ ty_bool false.
  Definition int_lit {Γ} (literal : Z) : Exp Γ ty_int :=
    exp_lit _ ty_int literal.

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
  Local Notation "'instr'" := (@exp_var _ "instr" _ _).
  Local Notation "'reg_code'" := (@exp_var _ "reg_code" ty_int _).
  Local Notation "'reg_tag'" := (@exp_var _ "reg_tag" (ty_enum register_tag) _).
  Local Notation "'reg_value'" := (@exp_var _ "reg_value" ty_int _).
  Local Notation "'flag_code'" := (@exp_var _ "flag_code" ty_int _).
  Local Notation "'flag_value'" := (@exp_var _ "flag_value" ty_bool _).
  Local Notation "'address'" := (@exp_var _ "address" ty_int _).
  Local Notation "'mem_value'" := (@exp_var _ "mem_value" ty_int _).
  Local Definition nop {Γ} : Stm Γ ty_unit := stm_lit ty_unit tt.

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ.
    let pi := eval compute in
    match f in Fun Δ τ return Stm Δ τ with
    | rX =>
      stm_match_enum register_tag reg_tag
      (fun tag =>
         match tag with
         | RegTag0 => stm_read_register R0
         | RegTag1 => stm_read_register R1
         | RegTag2 => stm_read_register R2
         | RegTag3 => stm_read_register R3
         end)
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
      if:      address = int_lit 0 then stm_read_memory A0
      else if: address = int_lit 1 then stm_read_memory A1
      else if: address = int_lit 2 then stm_read_memory A2
      else if: address = int_lit 3 then stm_read_memory A3
      else     stm_fail _ "read_register: invalid register"
    | wM =>
      if:      address = int_lit 0 then stm_write_memory A0 mem_value
      else if: address = int_lit 1 then stm_write_memory A1 mem_value
      else if: address = int_lit 2 then stm_write_memory A2 mem_value
      else if: address = int_lit 3 then stm_write_memory A3 mem_value
      else     stm_fail _ "read_register: invalid register"
    (* an [int] represents a valid address if it is >= [Memory_lb] and < [Memory_hb] *)
    | in_bounds => ((address = Memory_lb) || (address > Memory_lb)) && (address < Memory_hb)
    | semantics => (@stm_match_union _ instruction instr _
        (fun K => match K with
               | KHalt => ""
               | KLoad => "load_args"
               | KAdd => "add_args"
               | KJump => "jump_args"
               end)
        (fun K => match K return Stm _ _ with
               | KHalt =>
                 stm_write_register Halted lit_true ;; nop
               | KLoad =>
                 match: (exp_var "load_args") in (ty_int , ty_int) with
                 | ("dest", "source") =>
                      let: "x" := call rM (exp_var "source")
                   in let: "safe" := call in_bounds (exp_var "source")
                   in if: (exp_var "safe")
                      then (call wX (exp_var "dest") (exp_var "x");;nop)
                      else (stm_write_register OutOfMemory lit_true;; nop)
                  end
               | KAdd => stm_fail _ "not implemented"
               | KJump => stm_fail _ "not implemented"
               end))
    | swapreg => stm_fail _ "not_implemented"
      (* let: "v1" := call rX (exp_var "r1") in *)
      (* let: "v2" := call rX (exp_var "r2") in *)
      (* call wX (exp_var "r1") (exp_var "v2") ;; *)
      (* call wX (exp_var "r2") (exp_var "v1") ;; *)
      (* nop *)
    | swapreg12 =>
      let: "x" := stm_read_register R1 in
      let: "y" := stm_read_register R2 in
      stm_write_register R1 y ;;
      stm_write_register R2 x ;;
      nop
    | double => call add z z
    | add => x + y
    | add3 => let: "xy" := call add x y in
              call add (exp_var "xy") z
    end in exact pi.
  Defined.

End ISAProgramKit.
Import ISAProgramKit.

Module ExampleStepping.

  Module ISASmappStep := SmallStep ISATypeKit ISATermKit ISAProgramKit.
  Import ISASmappStep.

  Module ISAProgress := Progress ISATypeKit ISATermKit ISAProgramKit.
  Import ISAProgress.
  Import CtxNotations.

  Lemma example_halt :
    forall (Γ : Ctx (𝑿 * Ty))
           (γ : RegStore) (μ : Memory),
      ⟨ γ , μ
        , env_nil ► ("instr" ∶ ty_union instruction) ↦ Halt
        , Pi semantics ⟩
        --->*
        ⟨ write_register γ Halted true , μ
          , env_nil ► ("instr" ∶ ty_union instruction) ↦ Halt
          , stm_lit ty_unit tt ⟩.
  Proof.
    intros; cbn [Pi].
    (* Step 1 *)
    econstructor 2.
    { constructor. }
    cbn.
    (* Step 2 *)
    econstructor 2.
    { constructor. constructor. constructor. }
    cbn.
    (* Step 3 *)
    econstructor 2.
    { constructor. apply step_stm_seq_value. }
    (* Step 4 *)
    econstructor 2.
    { constructor. }
    (* End *)
    constructor 1.
  Qed.

End ExampleStepping.

Module ISASymbolicTermKit <: (SymbolicTermKit ISATypeKit ISATermKit ISAProgramKit).
  Module PM := Programs ISATypeKit ISATermKit ISAProgramKit.

  Definition 𝑷 := Empty_set.
  Definition 𝑷_Ty : 𝑷 -> Ctx Ty := fun p => match p with end.
  Definition 𝑷_eq_dec :  forall (p : 𝑷) (q : 𝑷), {p = q}+{~ p = q} := fun p => match p with end.
End ISASymbolicTermKit.

Module ISASymbolicTerms := SymbolicTerms
                             ISATypeKit
                             ISATermKit
                             ISAProgramKit
                             ISASymbolicTermKit.
Import ISASymbolicTerms.

Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

Module ISASymbolicContractKit <:
  (SymbolicContractKit
     ISATypeKit
     ISATermKit
     ISAProgramKit
     ISASymbolicTermKit
  ).
  Module STs := ISASymbolicTerms.

  Open Scope env_scope.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX =>
        let Σ' := ["reg_tag" ∶ ty_enum register_tag,  "v" ∶ ty_int] in
        let δ' := (@env_snoc (string * Ty)
                             (fun xt => Term Σ' (snd xt)) _ env_nil
                    ("reg_tag" ∶ ty_enum register_tag)
                    (* (@term_enum _ register_tag RegTag0) *)
                    (term_var "reg_tag")
                  ) in
        sep_contract_result_pure
          δ'
          (@term_var Σ' "v" _ _)
        (@asn_match_enum _ register_tag (term_var "reg_tag")
                        (fun k => match k with
                               | RegTag0 => R0 ↦ term_var "v"
                               | RegTag1 => R1 ↦ term_var "v"
                               | RegTag2 => R2 ↦ term_var "v"
                               | RegTag3 => R3 ↦ term_var "v"
                               end))
        (@asn_match_enum _ register_tag (term_var "reg_tag")
                        (fun k => match k with
                               | RegTag0 => R0 ↦ term_var "v"
                               | RegTag1 => R1 ↦ term_var "v"
                               | RegTag2 => R2 ↦ term_var "v"
                               | RegTag3 => R3 ↦ term_var "v"
                               end))
      | wX => sep_contract_none _
      | rF => sep_contract_none _
      | wF => sep_contract_none _
      | rM => sep_contract_none _
      | wM => sep_contract_none _
      | in_bounds => sep_contract_none _
      | semantics => sep_contract_none _
      | swapreg => sep_contract_none _
      | swapreg12 =>
        @sep_contract_unit
          ε
          ["u" ∶ ty_int, "v" ∶ ty_int]
          env_nil
          (R1 ↦ term_var "u" ✱ R2 ↦ term_var "v")
          (R1 ↦ term_var "v" ✱ R2 ↦ term_var "u")
      | add =>
        @sep_contract_result_pure
          ["x" ∶ ty_int, "y" ∶ ty_int]
          ["x" ∶ ty_int, "y" ∶ ty_int]
          ty_int
          [term_var "x", term_var "y"]%arg
          (term_binop binop_plus (term_var "x") (term_var "y"))
          asn_true
          asn_true
      | double =>
        @sep_contract_result_pure
          ["z" ∶ ty_int]
          ["z" ∶ ty_int]
          ty_int
          [term_var "z"]%arg
          (term_binop binop_plus (term_var "z") (term_var "z"))
          asn_true
          asn_true
      | add3 =>
        @sep_contract_result_pure
          ["x" ∶ ty_int, "y" ∶ ty_int, "z" ∶ ty_int]
          ["x" ∶ ty_int, "y" ∶ ty_int, "z" ∶ ty_int]
          ty_int
          [term_var "x", term_var "y", term_var "z"]%arg
          (term_binop binop_plus (term_binop binop_plus (term_var "x") (term_var "y")) (term_var "z"))
          asn_true
          asn_true
      end.

End ISASymbolicContractKit.
Module ISASymbolicContracts :=
  SymbolicContracts
    ISATypeKit
    ISATermKit
    ISAProgramKit
    ISASymbolicTermKit
    ISASymbolicContractKit.
Import ISASymbolicContracts.

Local Transparent chunk_eqb.
Local Transparent Term_eqb.

Import List.

Lemma Forall_singleton {A : Type} :
  forall (x : A) (P : A -> Prop) (prf : P x), Forall P (x :: nil).
  Proof.
    intros.
    apply Forall_forall.
    intros y yInX.
    destruct yInX.
    - rewrite <- H. exact prf .
    - destruct H.
  Qed.

  Lemma Forall_nil {A : Type} :
  forall (P : A -> Prop), Forall P nil.
Proof. trivial. Qed.

Local Ltac solve :=
  unfold valid_obligations, valid_obligation;
  repeat
    (cbn in *; intros;
     try
       match goal with
       | |- Forall _ _ => constructor
       | H: Forall _ _ |- _ => dependent destruction H
       end;
     try congruence; auto).

Lemma valid_contracts : ValidContractEnv CEnv.
Proof.
  intros Δ τ []; hnf; try match goal with |- True => auto end.
  - intros i; destruct i; cbn.
    + intros j; destruct j; solve.
      * exists (term_var "v"); solve.
        exists RegTag0; solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
    + intros j; destruct j; solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
        exists RegTag1; solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
    + intros j; destruct j; solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
        exists RegTag2; solve.
      * exists (term_var "v"); solve.
    + intros j; destruct j; solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
      * exists (term_var "v"); solve.
        exists RegTag3; solve.
  - exists (term_var "u").
    exists (term_var "v").
    exists (term_var "u").
    exists (term_var "v").
    repeat constructor.
  - repeat constructor.
  - exists [term_var "z", term_var "z"]%arg; cbn.
    repeat constructor.
  - exists [term_var "x", term_var "y"]%arg; cbn; auto.
    exists [term_binop binop_plus (term_var "x") (term_var "y"), term_var "z"]%arg; cbn.
    repeat constructor.
Qed.
