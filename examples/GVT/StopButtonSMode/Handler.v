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
     RiscvPmp.GVT.Target
     RiscvPmp.GVT.StopButtonSMode.Layout
     RiscvPmp.GVT.StopButtonSMode.Kernel
     RiscvPmp.GVT.StopButtonSMode.InitChain.
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

(* Block verification for the handler blocks of the S-mode StopButton
   femtokernel. The init chain lives in InitChain.v; the assertions and
   Ltac defined there are available here, with the exception of its
   section-local notations, which are repeated below.

   Nothing is ported yet. To be taken from examples/GVT/StopButtonUMode.v:
   the handler blocks from handler_block0 onwards, which save the context to
   the M-mode stack, dispatch on mcause, and -- unlike anything in the init
   chain -- read the interrupt word at mmio_interrupt_addr. That read is the
   one place where the IO protocol changes state, so it takes the IOR__intr
   case rather than IOdev, and solve_dev_chain will not close it.

   Sigma__csrs and CSRVals in InitChain.v were written for these blocks:
   the handler owns every CSR it saves and restores, so its assertions are
   parameterised over a valuation rather than naming values one by one. *)

Section Handler.
  Import bv.notations.
  Import ListNotations.
  Import TermNotations.
  Import asn.notations.
  Import RiscvPmp.GVT.Sig.

  Open Scope hex_Z_scope.

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

  (* Repeated from InitChain.v: Local Notation does not survive the end of a
     section, let alone the end of a file. If these grow, or the handler ends
     up needing more of InitChain's definitions than expected, hoist both
     into a StopButtonSMode/Assertions.v that the two files share. *)
  Local Notation asn_mmio_trace_state_inv := (asn.chunk (chunk_user (mmio_state_trace bytes_per_word) [env])).
  Local Notation asn_mmio_state_pred s := (asn.chunk (chunk_user (mmio_state bytes_per_word) [s])).
  Local Notation asn_mmio_read_valid a s := (asn.formula (formula_user (mmio_read_valid bytes_per_word) [a; s])).
  Local Notation asn_mmio_event a v t s s' := (asn.formula (formula_user (mmio_event bytes_per_word) [a; v; t; s; s'])).

  Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
  Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

End Handler.
