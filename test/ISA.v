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
     Sep.Spec
     SmallStep.Step
     Symbolic.Mutator
     Symbolic.Sound
     Syntax.

From stdpp Require
     finite.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

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

Section Finite.

  Import stdpp.finite.
  Import ListNotations.

  Global Program Instance RegisterTag_finite : Finite RegisterTag :=
    {| enum := [RegTag0;RegTag1;RegTag2;RegTag3] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance InstructionConstructor_finite : Finite InstructionConstructor :=
    {| enum := [KHalt;KLoad;KAdd;KJump] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

End Finite.

(** Describe a part of REDFIN ISA
    Property to verify:
      Every instruction is memory safe, i.e. it checks memory
      access and sets the 'OutOfMemory' flag if out of memory
      access has been attempted. *)
Module ISATypeKit <: TypeKit.

  Import stdpp.finite.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (E : 𝑬) : Set :=
    match E with
    | register_tag => RegisterTag
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
    | instruction => Instruction
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; auto with typeclass_instances).
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.
  Instance 𝑼𝑲_eq_dec U : EqDec (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).
  Instance 𝑼𝑲_finite U : Finite (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).

  (** RECORDS **)
  Definition 𝑹        := Empty_set.
  Definition 𝑹_eq_dec := Empty_set_eqdec.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    end.
  Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
    ltac:(destruct R; auto with typeclass_instances).

End ISATypeKit.

Module ISAValueKit <: ValueKit.
  Module typekit := ISATypeKit.
  Module Export TY := Types typekit.

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

End ISAValueKit.

Module ISATermKit <: TermKit.
  Module valuekit := ISAValueKit.
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

  (** FUNCTIONS **)
  (* Names are inspired by sail-riscv naming convention *)
  Inductive Fun : PCtx -> Ty -> Set :=
  (* read registers *)
  | rX  : Fun ["reg_tag" :: ty_enum register_tag ] ty_int
  (* write register *)
  | wX : Fun ["reg_tag" :: ty_enum register_tag, "reg_value" :: ty_int] ty_unit
  (* read flag *)
  | rF      : Fun ["flag_code" :: ty_int] ty_bool
  (* write flag *)
  | wF     : Fun ["flag_code" :: ty_int, "flag_value" :: ty_bool] ty_bool
  (* check memory bounds *)
  | in_bounds : Fun ["address" :: ty_int] ty_bool
  (* semantics of a single instruction *)
  | semantics : Fun [ "instr" :: ty_union instruction] ty_unit
  | execute_load : Fun [ "dst" :: ty_enum register_tag, "src" :: ty_enum register_tag ] ty_unit
  | swapreg : Fun ["r1" :: ty_enum register_tag, "r2" :: ty_enum register_tag] ty_unit
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" :: ty_int] ty_int
  (* write memory *)
  | wM                   : FunX ["address" :: ty_int, "mem_value" :: ty_int] ty_unit
  .

  Inductive Lem : PCtx -> Set :=
  | open_ptstoreg                    : Lem ctx_nil
  | close_ptstoreg (R : RegisterTag) : Lem ctx_nil
  .

  Definition 𝑭 : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿 : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

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

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive Signature NoConfusion for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮).
  Proof.
    intros [? []] [? []]; cbn;
      first
        [ left; now apply eq_refl
        | right; intros e; dependent elimination e
        ].
  Defined.

End ISATermKit.

Module ISAProgramKit <: (ProgramKit ISATermKit).
  Module Export TM := Terms ISATermKit.

  (* REGISTER STORE *)
  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  Local Coercion stm_exp : Exp >-> Stm.

  Notation "'lemma' f" :=
    (stm_lemma f env_nil)
    (at level 10, f at next level) : exp_scope.

  Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
  Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.
  Local Notation "'instr'" := (@exp_var _ "instr" _ _) : exp_scope.
  Local Notation "'reg_code'" := (@exp_var _ "reg_code" ty_int _) : exp_scope.
  Local Notation "'reg_tag'" := (@exp_var _ "reg_tag" (ty_enum register_tag) _) : exp_scope.
  Local Notation "'reg_value'" := (@exp_var _ "reg_value" ty_int _) : exp_scope.
  Local Notation "'flag_code'" := (@exp_var _ "flag_code" ty_int _) : exp_scope.
  Local Notation "'flag_value'" := (@exp_var _ "flag_value" ty_bool _) : exp_scope.
  Local Notation "'address'" := (@exp_var _ "address" ty_int _) : exp_scope.
  Local Notation "'mem_value'" := (@exp_var _ "mem_value" ty_int _) : exp_scope.
  Local Definition nop {Γ} : Stm Γ ty_unit := stm_lit ty_unit tt.

  (* Address space bounds *)
  Definition Memory_lb {Γ} : Exp Γ ty_int := lit_int 0.
  Definition Memory_hb {Γ} : Exp Γ ty_int := lit_int 3.

  Definition fun_rX : Stm ["reg_tag" :: ty_enum register_tag] ty_int :=
    lemma open_ptstoreg ;;
    match: reg_tag in register_tag with
    | RegTag0 => let: "x" := stm_read_register R0 in lemma (close_ptstoreg RegTag0) ;; stm_exp x
    | RegTag1 => let: "x" := stm_read_register R1 in lemma (close_ptstoreg RegTag1) ;; stm_exp x
    | RegTag2 => let: "x" := stm_read_register R2 in lemma (close_ptstoreg RegTag2) ;; stm_exp x
    | RegTag3 => let: "x" := stm_read_register R3 in lemma (close_ptstoreg RegTag3) ;; stm_exp x
    end.

  Definition fun_wX : Stm ["reg_tag" :: ty_enum register_tag, "reg_value" :: ty_int] ty_unit :=
    lemma open_ptstoreg ;;
    match: reg_tag in register_tag with
    | RegTag0 => stm_write_register R0 reg_value ;; lemma (close_ptstoreg RegTag0)
    | RegTag1 => stm_write_register R1 reg_value ;; lemma (close_ptstoreg RegTag1)
    | RegTag2 => stm_write_register R2 reg_value ;; lemma (close_ptstoreg RegTag2)
    | RegTag3 => stm_write_register R3 reg_value ;; lemma (close_ptstoreg RegTag3)
    end.

  Definition fun_semantics : Stm ["instr" :: ty_union instruction] ty_unit :=
    stm_match_union_alt instruction instr
      (fun K => match K with
                | KHalt => MkAlt (pat_unit)                 (stm_write_register Halted lit_true ;; nop)
                | KLoad => MkAlt (pat_pair "dest" "source") (call execute_load (exp_var "dest") (exp_var "source"))
                | KAdd  => MkAlt (pat_var "jump_args")      (stm_fail _ "not implemented")
                | KJump => MkAlt (pat_var "add_args")       (stm_fail _ "not implemented")
                end).

  Definition fun_execute_load : Stm ["dst" :: ty_enum register_tag, "src" :: ty_enum register_tag] ty_unit :=
    (* TODO: Update PC *)
    let: "addr" := call rX (exp_var "src") in
    let: "safe" := call in_bounds (exp_var "addr") in
    if: exp_var "safe"
    then (let: "v" := foreign rM (exp_var "addr") in
          call wX (exp_var "dst") (exp_var "v") ;;
          nop)
    else (stm_write_register OutOfMemory lit_true ;; nop).

  Definition fun_swapreg : Stm ["r1" :: ty_enum register_tag, "r2" :: ty_enum register_tag] ty_unit :=
    let: "v1" := call rX (exp_var "r1") in
    let: "v2" := call rX (exp_var "r2") in
    call wX (exp_var "r1") (exp_var "v2") ;;
    call wX (exp_var "r2") (exp_var "v1") ;;
    nop.

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f in Fun Δ τ return Stm Δ τ with
    | rX => fun_rX
    | wX => fun_wX
    | rF =>
      if:      flag_code = lit_int 5 then stm_read_register Halted
      else if: flag_code = lit_int 6 then stm_read_register Overflow
      else if: flag_code = lit_int 7 then stm_read_register OutOfMemory
      else     stm_fail _ "read_register: invalid register"
    | wF =>
      if:      flag_code = lit_int 5 then stm_write_register Halted flag_value
      else if: flag_code = lit_int 6 then stm_write_register Overflow flag_value
      else if: flag_code = lit_int 7 then stm_write_register OutOfMemory flag_value
      else     stm_fail _ "write_register: invalid register"
    (* an [int] represents a valid address if it is >= [Memory_lb] and < [Memory_hb] *)
    | in_bounds => ((address = Memory_lb) || (address > Memory_lb)) && (address < Memory_hb)
    | semantics => fun_semantics
    | execute_load => fun_execute_load
    | swapreg => fun_swapreg
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
  .

  Definition ForeignCall := @CallEx.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof. destruct f; cbn; repeat depelim args; repeat eexists; constructor. Qed.

End ISAProgramKit.

Module ExampleStepping.

  Module ISASmappStep := SmallStep ISATermKit ISAProgramKit.
  Import ISAProgramKit.
  Import ISASmappStep.

  Lemma example_halt :
    forall (Γ : PCtx)
           (γ : RegStore) (μ : Memory),
      ⟨ γ , μ
        , env_nil ► ("instr" :: ty_union instruction ↦ Halt)
        , Pi semantics ⟩
        --->*
        ⟨ write_register γ Halted true , μ
          , env_nil ► ("instr" :: ty_union instruction ↦ Halt)
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

Module ISAAssertionKit <: (AssertionKit ISATermKit ISAProgramKit).
  Export ISAProgramKit.

  Definition 𝑷 := Predicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | ptstoreg => [ty_enum register_tag, ty_int]
    end.
  Definition 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.

End ISAAssertionKit.

Module ISASymbolicContractKit <:
  SymbolicContractKit ISATermKit ISAProgramKit ISAAssertionKit.
  Module Export ASS := Assertions ISATermKit ISAProgramKit ISAAssertionKit.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '✱' q" := (asn_sep p q) (at level 150).
  Local Notation "[ x , .. , z ]" :=
    (env_snoc .. (env_snoc env_nil _ x) .. _ z) (at level 0) : env_scope.

  Definition sep_contract_rX : SepContract ["reg_tag" :: ty_enum register_tag ] ty_int :=
    {| sep_contract_logic_variables := ["reg_tag" :: ty_enum register_tag,  "v" :: ty_int];
       sep_contract_localstore      := [term_var "reg_tag"]%arg;
       sep_contract_precondition    :=
         asn_chunk (chunk_user ptstoreg [ term_var "reg_tag", term_var "v" ]%env);
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_rX") (term_var "v") ✱
         asn_chunk (chunk_user ptstoreg [ term_var "reg_tag", term_var "v" ]%env) ;
    |}.

  Definition sep_contract_wX : SepContract ["reg_tag" :: ty_enum register_tag, "reg_value" :: ty_int] ty_unit :=
    {| sep_contract_logic_variables := ["r" :: ty_enum register_tag, "v_old" :: ty_int, "v_new" :: ty_int];
       sep_contract_localstore      := [term_var "r", term_var "v_new"]%arg;
       sep_contract_precondition    :=
         asn_chunk (chunk_user ptstoreg [ term_var "r", term_var "v_old" ]%env);
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_wX") (term_lit ty_unit tt) ✱
         asn_chunk (chunk_user ptstoreg [ term_var "r", term_var "v_new" ]%env)
    |}.

  Definition sep_contract_swapreg : SepContract ["r1" :: ty_enum register_tag, "r2" :: ty_enum register_tag] ty_unit :=
    {| sep_contract_pun_logic_variables := ["u" :: ty_int, "v" :: ty_int];
       sep_contract_pun_precondition :=
         asn_chunk (chunk_user ptstoreg [term_var "r1", term_var "u"]) ✱
         asn_chunk (chunk_user ptstoreg [term_var "r2", term_var "v"]);
       sep_contract_pun_result := "result_swapreg";
       sep_contract_pun_postcondition :=
         asn_eq (term_var "result_swapreg") (term_lit ty_unit tt) ✱
         asn_chunk (chunk_user ptstoreg [term_var "r1", term_var "v"]) ✱
         asn_chunk (chunk_user ptstoreg [term_var "r2", term_var "u"])
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX => Some sep_contract_rX
      | wX => Some sep_contract_wX
      | swapreg => Some sep_contract_swapreg
      | _ => None
      end.

  Program Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | rM => _
      | wM => _
      end.
  Admit Obligations of CEnvEx.

  Definition lemma_open_ptstoreg : Lemma ctx_nil :=
    {| lemma_logic_variables := ["r" :: ty_enum register_tag, "v" :: ty_int];
       lemma_patterns        := env_nil;
       lemma_precondition    :=
         asn_chunk (chunk_user ptstoreg [term_var "r", term_var "v"]%env);
       lemma_postcondition   :=
         asn_match_enum
           register_tag (term_var "r")
           (fun k => match k with
                     | RegTag0 => R0 ↦ term_var "v"
                     | RegTag1 => R1 ↦ term_var "v"
                     | RegTag2 => R2 ↦ term_var "v"
                     | RegTag3 => R3 ↦ term_var "v"
                     end)
    |}.

  Definition regtag_to_reg (R : RegisterTag) : Reg ty_int :=
    match R with
    | RegTag0 => R0
    | RegTag1 => R1
    | RegTag2 => R2
    | RegTag3 => R3
    end.

  Definition lemma_close_ptstoreg (R : RegisterTag) : Lemma ctx_nil :=
    {| lemma_logic_variables := ["v" :: ty_int];
       lemma_patterns        := env_nil;
       lemma_precondition    := (regtag_to_reg R ↦ term_var "v");
       lemma_postcondition   :=
         asn_chunk
            (chunk_user
               ptstoreg
               [term_enum register_tag R, term_var "v"]%env)
    |}.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      | open_ptstoreg    => lemma_open_ptstoreg
      | close_ptstoreg R => lemma_close_ptstoreg R
      end.

End ISASymbolicContractKit.
Module ISAMutators :=
  Mutators
    ISATermKit
    ISAProgramKit
    ISAAssertionKit
    ISASymbolicContractKit.
Import ISAMutators.
Import SMut.

Lemma valid_contract_rX : ValidContractReflect sep_contract_rX fun_rX.
Proof. reflexivity. Qed.
Hint Resolve valid_contract_rX : contracts.

Lemma valid_contract_wX : ValidContractReflect sep_contract_wX fun_wX.
Proof. reflexivity. Qed.
Hint Resolve valid_contract_wX : contracts.

Lemma valid_contract_swapreg : ValidContractReflect sep_contract_swapreg fun_swapreg.
Proof. reflexivity. Qed.
Hint Resolve valid_contract_swapreg : contracts.

(* Arguments asn_true {_} /. *)

(* Lemma valid_contracts : ValidContractEnv CEnv. *)
(* Proof. *)
(*   unfold ValidContractEnv. *)
(*   intros Δ τ [] c; inversion 1; subst c. *)
(*   - apply dmut_contract_sound; auto with contracts. *)
(*   - apply dmut_contract_sound; auto with contracts. *)
(*   - apply dmut_contract_sound; auto with contracts. *)
(*   - cbn; intuition. *)
(*   - cbn; intuition. *)
(*   - cbn; intuition. *)
(*   - intro c; inversion 1. subst c. intros []. *)
(*   - intros []. *)
(*   - intros []. *)
(*   - intros []. *)
(*   - intros []. *)
(*   - constructor. *)
(*   - constructor. *)
(*   - constructor. *)
(*   - constructor. *)
(* Qed. *)
