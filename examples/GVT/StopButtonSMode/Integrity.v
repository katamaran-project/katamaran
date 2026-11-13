(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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

From Stdlib Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Base
     Bitvector
     SmallStep.Step
     RiscvPmp.GVT.PmpCheck
     RiscvPmp.GVT.Spec
     RiscvPmp.GVT.TotalVerifier
     RiscvPmp.GVT.IrisModel
     RiscvPmp.GVT.IrisInstance
     RiscvPmp.GVT.Machine
     RiscvPmp.GVT.Logic
     RiscvPmp.GVT.trace
     RiscvPmp.iostate
     RiscvPmp.GVT.Sig
     RiscvPmp.GVT.StopButtonSMode.Kernel
     RiscvPmp.GVT.StopButtonSMode.BlockVerification.
From Katamaran Require
     RiscvPmp.GVT.Contracts
     RiscvPmp.GVT.LoopVerification
     RiscvPmp.GVT.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Module inv := invariants.

Import iris.program_logic.weakestpre.
Import iris.proofmode.proofmode.

Import MicroSail.ShallowExecutor.

Import RiscvPmp.GVT.Contracts.
Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
Import RiscvPmpIrisInstancePredicates.
Import RiscvPmpIrisInstance.
Import RiscvPmpBlockVerifSpec.
Import RiscvPmpIrisInstanceWithContracts.
Import RiscvPmpShallowExec.

(* Safety and end-to-end theorem for the S-mode StopButton femtokernel.

   To be ported from examples/GVT/StopButtonUMode.v, after Section FemtoKernel:
   - advAddrs / liveAddrs and the PMP lemmas (adv_in_pmp, pmp_in_adv,
     memAdv_pmpPolicy),
   - femtokernel_handler_safe*, femtokernel_init_safe (loop verification),
   - memory splitting (intro_ptsto*, femtokernel_splitMemory) and
     femtokernel_endToEnd. *)
