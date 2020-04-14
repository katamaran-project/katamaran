From Coq Require Import
     Logic.FinFun
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia
     Logic.FunctionalExtensionality.

From Equations Require Import
     EqDecInstances
     Equations.

From MicroSail Require Import
     Notation
     SmallStep.Step
     Syntax
     Sep.Spec
     Symbolic.Mutator
     Symbolic.Outcome.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Instance Z_eqdec : EqDec Z := Z.eq_dec.
Derive EqDec for Empty_set.

Inductive Enums : Set := register_tag.
Inductive RegisterTag : Set :=
  RegTag0 | RegTag1 | RegTag2 | RegTag3.
Inductive Unions : Set := instruction.

Inductive Instruction :=
| Halt
| Load (dst src : RegisterTag)
| Add  (dst src : RegisterTag)
| Jump (dst : Z).

Inductive InstructionConstructor :=
| KHalt
| KLoad
| KAdd
| KJump.

(* A silly address space of four addresses *)
Inductive Address : Set :=
  A0 | A1 | A2 | A3.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Enums.
  Derive NoConfusion for RegisterTag.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Instruction.
  Derive NoConfusion for InstructionConstructor.
  Derive NoConfusion for Address.

End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for RegisterTag.
Derive EqDec for Unions.
Derive EqDec for Instruction.
Derive EqDec for InstructionConstructor.
Derive EqDec for Address.

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

  Definition 𝑬_eq_dec : EqDec 𝑬 := Enums_eqdec.
  Definition 𝑬𝑲_eq_dec : forall (e : 𝑬), EqDec (𝑬𝑲 e).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑼_eq_dec : EqDec 𝑼 := Unions_eqdec.
  Definition 𝑼𝑻_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑻 u).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑼𝑲_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑲 u).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
  Definition 𝑹_eq_dec : EqDec 𝑹 := Empty_set_eqdec.
  Definition 𝑹𝑻_eq_dec : forall (r : 𝑹), EqDec (𝑹𝑻 r).
  Proof. intros []; cbn; auto with typeclass_instances. Defined.
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
    | instruction =>
      fun K =>
        match K with
        | KHalt => ty_unit
        (* Load has two fields: a register label and a memory address, *)
        (* represented as ints *)
        | KLoad => ty_prod (ty_enum register_tag) (ty_enum register_tag)
        | KAdd => ty_prod (ty_enum register_tag) (ty_enum register_tag)
        | KJump => ty_int
        end
    end.
  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | instruction =>
      fun Kv =>
        match Kv with
        | existT KHalt tt        => Halt
        | existT KLoad (dst,src) => Load dst src
        | existT KAdd (dst,src)  => Add dst src
        | existT KJump dst       => Jump dst
        end
    end.

  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U with
    | instruction =>
      fun Kv =>
        match Kv with
        | Halt         => existT KHalt tt
        | Load dst src => existT KLoad (dst,src)
        | Add dst src  => existT KAdd (dst,src)
        | Jump dst     => existT KJump dst
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
  | wX : Fun ["reg_tag" ∶ ty_enum register_tag, "reg_value" ∶ ty_int] ty_unit
  (* read flag *)
  | rF      : Fun ["flag_code" ∶ ty_int] ty_bool
  (* write flag *)
  | wF     : Fun ["flag_code" ∶ ty_int, "flag_value" ∶ ty_bool] ty_bool
  (* check memory bounds *)
  | in_bounds : Fun ["address" ∶ ty_int] ty_bool
  (* semantics of a single instruction *)
  | semantics : Fun [ "instr" ∶ ty_union instruction] ty_unit
  | execute_load : Fun [ "dst" ∶ ty_enum register_tag, "src" ∶ ty_enum register_tag ] ty_unit
  | swapreg : Fun ["r1" ∶ ty_enum register_tag, "r2" ∶ ty_enum register_tag] ty_unit
  | swapreg12 : Fun ctx_nil ty_unit
  | add : Fun [ "x" ∶ ty_int , "y" ∶ ty_int ] ty_int
  | double : Fun [ "z" ∶ ty_int ] ty_int
  | add3 : Fun [ "x" ∶ ty_int , "y" ∶ ty_int , "z" ∶ ty_int ] ty_int
  .

  Inductive FunGhost : Set :=
  | open_ptstoreg
  | close_ptstoreg0
  | close_ptstoreg1
  | close_ptstoreg2
  | close_ptstoreg3
  .

  Inductive FunX : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_int
  (* write memory *)
  | wM                   : FunX ["address" ∶ ty_int, "mem_value" ∶ ty_int] ty_unit
  | ghost (f : FunGhost) : FunX ctx_nil ty_unit
  .

  Definition 𝑭 : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿 : Ctx (𝑿 * Ty) -> Ty -> Set := FunX.

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

  Local Coercion stm_exp : Exp >-> Stm.
  Local Open Scope exp_scope.
  Local Open Scope stm_scope.

  Notation "'callghost' f" :=
    (stm_callex (ghost f) env_nil)
    (at level 10, f global) : stm_scope.

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

  (* Address space bounds *)
  Definition Memory_lb {Γ} : Exp Γ ty_int := int_lit 0.
  Definition Memory_hb {Γ} : Exp Γ ty_int := int_lit 3.

  Definition fun_rX : Stm ["reg_tag" ∶ ty_enum register_tag] ty_int :=
    callghost open_ptstoreg ;;
    match: reg_tag in register_tag with
    | RegTag0 => let: "x" := stm_read_register R0 in callghost close_ptstoreg0 ;; stm_exp x
    | RegTag1 => let: "x" := stm_read_register R1 in callghost close_ptstoreg1 ;; stm_exp x
    | RegTag2 => let: "x" := stm_read_register R2 in callghost close_ptstoreg2 ;; stm_exp x
    | RegTag3 => let: "x" := stm_read_register R3 in callghost close_ptstoreg3 ;; stm_exp x
    end.

  Definition fun_wX : Stm ["reg_tag" ∶ ty_enum register_tag, "reg_value" ∶ ty_int] ty_unit :=
    callghost open_ptstoreg ;;
    match: reg_tag in register_tag with
    | RegTag0 => stm_write_register R0 reg_value ;; callghost close_ptstoreg0
    | RegTag1 => stm_write_register R1 reg_value ;; callghost close_ptstoreg1
    | RegTag2 => stm_write_register R2 reg_value ;; callghost close_ptstoreg2
    | RegTag3 => stm_write_register R3 reg_value ;; callghost close_ptstoreg3
    end.

  Definition fun_semantics : Stm ["instr" ∶ ty_union instruction] ty_unit :=
    stm_match_union instruction instr
      (fun K => match K with
                | KHalt => alt _ (pat_unit)                 (stm_write_register Halted lit_true ;; nop)
                | KLoad => alt _ (pat_pair "dest" "source") (call execute_load (exp_var "dest") (exp_var "source"))
                | KAdd  => alt _ (pat_var "jump_args")      (stm_fail _ "not implemented")
                | KJump => alt _ (pat_var "add_args")       (stm_fail _ "not implemented")
                end).

  Definition fun_execute_load : Stm ["dst" ∶ ty_enum register_tag, "src" ∶ ty_enum register_tag] ty_unit :=
    (* TODO: Update PC *)
    let: "addr" := call rX (exp_var "src") in
    let: "safe" := call in_bounds (exp_var "addr") in
    if: exp_var "safe"
    then (let: "v" := callex rM (exp_var "addr") in
          call wX (exp_var "dst") (exp_var "v") ;;
          nop)
    else (stm_write_register OutOfMemory lit_true ;; nop).

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    Eval compute in
    match f in Fun Δ τ return Stm Δ τ with
    | rX => fun_rX
    | wX => fun_wX
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
    (* an [int] represents a valid address if it is >= [Memory_lb] and < [Memory_hb] *)
    | in_bounds => ((address = Memory_lb) || (address > Memory_lb)) && (address < Memory_hb)
    | semantics => fun_semantics
    | execute_load => fun_execute_load
    | swapreg =>
      let: "v1" := call rX (exp_var "r1") in
      let: "v2" := call rX (exp_var "r2") in
      call wX (exp_var "r1") (exp_var "v2") ;;
      call wX (exp_var "r2") (exp_var "v1") ;;
      nop
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
    end.

  (* MEMORY *)
  Definition Memory := Z -> option Z.

  Definition fun_rM (μ : Memory) (addr : Lit ty_int) : string + Lit ty_int :=
    match μ addr with
    | Some v => inr v
    | None   => inl "Err [fun_rM]: invalid address"
    end.

  Definition fun_wM (μ : Memory) (addr val : Lit ty_int) : Memory :=
    fun addr' => if Z.eqb addr addr' then Some val else μ addr'.

  Inductive CallEx : forall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
  | callex_rM {addr : Z} {γ : RegStore} {μ : Memory} :
      CallEx rM (env_snoc env_nil (_ , ty_int) addr)
             (fun_rM μ addr)
             γ γ μ μ
  | callex_wM {addr val : Z} {γ : RegStore} {μ : Memory} :
      CallEx wM (env_snoc (env_snoc env_nil (_ , ty_int) addr) (_ , ty_int) val)
             (inr tt)
             γ γ μ (fun_wM μ addr val)
  | callex_ghost {f γ μ} : CallEx (ghost f) env_nil (inr tt) γ γ μ μ
  .

  Definition ExternalCall := @CallEx.

  Lemma ExternalProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ExternalCall f args res γ γ' μ μ'.
  Proof. destruct f; cbn; repeat depelim args; repeat eexists; constructor. Qed.

End ISAProgramKit.
Import ISAProgramKit.

Module ExampleStepping.

  Module ISASmappStep := SmallStep ISATypeKit ISATermKit ISAProgramKit.
  Import ISASmappStep.

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

Inductive Predicate : Set := ptstoreg.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module ISAAssertionKit <: (AssertionKit ISATypeKit ISATermKit ISAProgramKit).
  Module PM := Programs ISATypeKit ISATermKit ISAProgramKit.

  Definition 𝑷 := Predicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | ptstoreg => [ty_enum register_tag, ty_int]
    end.
  Definition 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.

End ISAAssertionKit.

Module ISAAssertions :=
  Assertions ISATypeKit ISATermKit ISAProgramKit ISAAssertionKit.
Import ISAAssertions.

Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

Module ISASymbolicContractKit <:
  SymbolicContractKit ISATypeKit ISATermKit ISAProgramKit ISAAssertionKit.
  Module ASS := ISAAssertions.

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
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_var "reg_tag" ► ty_int ↦ term_var "v")))
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_var "reg_tag" ► ty_int ↦ term_var "v")))
      | wX => 
        @sep_contract_unit
          [ "reg_tag" ∶ ty_enum register_tag,
            "reg_value" ∶ ty_int ]
          [ "r" ∶ ty_enum register_tag,
            "v_old" ∶ ty_int,
            "v_new" ∶ ty_int ]
          [term_var "r", term_var "v_new"]%arg
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_var "r" ► ty_int ↦ term_var "v_old")))
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_var "r" ► ty_int ↦ term_var "v_new")))
      | rF => sep_contract_none _
      | wF => sep_contract_none _
      | in_bounds => sep_contract_none _
      | semantics => sep_contract_none _
      | execute_load =>
        @sep_contract_unit
          [ "dst" ∶ ty_enum register_tag,
            "src" ∶ ty_enum register_tag ]
          [ "dst" ∶ ty_enum register_tag,
            "src" ∶ ty_enum register_tag,
            "a"   ∶ ty_int,
            "v"   ∶ ty_int
          ]
          [term_var "dst", term_var "src"]%arg
          asn_true
          asn_true
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

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | rM => sep_contract_none _
      | wM => sep_contract_none _
      | ghost open_ptstoreg =>
        @sep_contract_unit
          ctx_nil
          [ "r" ∶ ty_enum register_tag,
            "v" ∶ ty_int
          ]
          env_nil
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_var "r" ► ty_int ↦ term_var "v")))
          (asn_match_enum register_tag (term_var "r")
                          (fun k => match k with
                                    | RegTag0 => R0 ↦ term_var "v"
                                    | RegTag1 => R1 ↦ term_var "v"
                                    | RegTag2 => R2 ↦ term_var "v"
                                    | RegTag3 => R3 ↦ term_var "v"
                                    end))
      | ghost close_ptstoreg0 =>
        @sep_contract_unit
          ctx_nil
          [ "v" ∶ ty_int ]
          env_nil
          (R0 ↦ term_var "v")
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_enum register_tag RegTag0 ► ty_int ↦ term_var "v")))
      | ghost close_ptstoreg1 =>
        @sep_contract_unit
          ctx_nil
          [ "v" ∶ ty_int ]
          env_nil
          (R1 ↦ term_var "v")
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_enum register_tag RegTag1 ► ty_int ↦ term_var "v")))
      | ghost close_ptstoreg2 =>
        @sep_contract_unit
          ctx_nil
          [ "v" ∶ ty_int ]
          env_nil
          (R2 ↦ term_var "v")
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_enum register_tag RegTag2 ► ty_int ↦ term_var "v")))
      | ghost close_ptstoreg3 =>
        @sep_contract_unit
          ctx_nil
          [ "v" ∶ ty_int ]
          env_nil
          (R3 ↦ term_var "v")
          (asn_chunk
             (chunk_pred
                ptstoreg
                (env_nil ► ty_enum register_tag ↦ term_enum register_tag RegTag3 ► ty_int ↦ term_var "v")))
      end.

End ISASymbolicContractKit.
Module ISAMutators :=
  Mutators
    ISATypeKit
    ISATermKit
    ISAProgramKit
    ISAAssertionKit
    ISASymbolicContractKit.
Import ISAMutators.

Local Transparent Term_eqb env_beq.

Import List.

Arguments inctx_zero {_ _ _} /.
Arguments inctx_succ {_ _ _ _} !_ /.

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

Lemma valid_contract_rX : ValidContract (CEnv rX) fun_rX.
Proof. intros [] []; solve. Qed.
Hint Resolve valid_contract_rX : contracts.

(* Lemma valid_contract_rX : ValidContractDynMut (CEnv rX) fun_rX. *)
(* Proof. *)
(*   exists [term_var "reg_tag", term_var "v"]%arg. *)
(*   intros [] []; exists (term_var "v"). *)
(*   - exists (env_snoc env_nil (_,_) (term_var "v")). *)
(*     repeat constructor. *)
(*   - solve. *)
(*   - solve. *)
(*   - solve. *)
(*   - solve. *)
(*   - exists (env_snoc env_nil (_,_) (term_var "v")). *)
(*     repeat constructor. *)
(*   - solve. *)
(*   - solve. *)
(*   - solve. *)
(*   - solve. *)
(*   - exists (env_snoc env_nil (_,_) (term_var "v")). *)
(*     repeat constructor. *)
(*   - solve. *)
(*   - solve. *)
(*   - solve. *)
(*   - solve. *)
(*   - exists (env_snoc env_nil (_,_) (term_var "v")). *)
(*     repeat constructor. *)
(* Qed. *)

Lemma valid_contract_wX : ValidContract (CEnv wX) fun_wX.
Proof. intros [] []; solve. Qed.
Hint Resolve valid_contract_wX : contracts.

(* Arguments asn_true {_} /. *)

Lemma valid_contract_execute_load : ValidContract (CEnv execute_load) fun_execute_load.
Proof.
Admitted.
Hint Resolve valid_contract_execute_load : contracts.

Lemma valid_contracts : ValidContractEnv CEnv.
Proof.
  intros Δ τ []; auto with contracts.
  - intros [].
  - intros [].
  - intros [].
  - intros [].
  - intros [].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.
