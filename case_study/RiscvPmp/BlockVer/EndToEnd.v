From Coq Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Bitvector
     Notations
     Specification
     SmallStep.Step
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.Contracts
     (* RiscvPmp.LoopVerification *)
     RiscvPmp.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Module inv := invariants.

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.tactics.

  Import MicroSail.ShallowExecutor.

  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.


  Section EndToEnd.
