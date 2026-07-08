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

From Katamaran Require Import
  Iris.Instance
  Iris.Base
  Notations
  Bitvector
  Sep.Hoare
  Specification
  MicroSail.ShallowExecutor
  MicroSail.ShallowSoundness
  MicroSail.SymbolicExecutor
  MicroSail.RefineExecutor
  MicroSail.Soundness
  RiscvPmp.PmpCheck
  RiscvPmp.IrisModel
  RiscvPmp.IrisModelBinary
  RiscvPmp.IrisInstance
  RiscvPmp.IrisInstanceBinary
  RiscvPmp.Machine
  RiscvPmp.Sig
  RiscvPmp.Contracts
  RiscvPmp.BlockVer.Spec
  RiscvPmp.BlockVer.TotalVerifier
  RiscvPmp.BlockVer.BinaryVerifier
  RiscvPmp.ModelBinary.

(* Combine all the modules without duplication. *)

Module RVPCOM : RiscvPmpIrisBaseCommon.
  Include RiscvPmpIrisBaseCommon.
End RVPCOM.
Module RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM.
  Include RiscvPmpIrisBase LeftOrRightLeft RVPCOM.
End RVPBASEl.
Module RVPPREDl : RiscvPmpIrisInstancePredicates LeftOrRightLeft RVPCOM RVPBASEl.
  Include RiscvPmpIrisInstancePredicates LeftOrRightLeft RVPCOM RVPBASEl.
End RVPPREDl.
Module RVPINSTl : RiscvPmpIrisInstance LeftOrRightLeft RiscvPmpBlockVerifFailLogic RVPCOM RVPBASEl RVPPREDl.
  Include RiscvPmpIrisInstance LeftOrRightLeft RiscvPmpBlockVerifFailLogic RVPCOM RVPBASEl RVPPREDl.
End RVPINSTl.
Module RVPCONTRl : RiscvPmpIrisInstanceWithContracts LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl RVPINSTl.
  Include RiscvPmpIrisInstanceWithContracts LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl RVPINSTl.
End RVPCONTRl.
Module RVPTVl : RiscvPmpBlockVerifTotalVerifier LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl RVPINSTl RVPCONTRl.
  Include RiscvPmpBlockVerifTotalVerifier LeftOrRightLeft RVPCOM RVPBASEl RVPPREDl RVPINSTl RVPCONTRl.
End RVPTVl.
Module RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM.
  Include RiscvPmpIrisBase LeftOrRightRight RVPCOM.
End RVPBASEr.
Module RVPPREDr : RiscvPmpIrisInstancePredicates LeftOrRightRight RVPCOM RVPBASEr.
  Include RiscvPmpIrisInstancePredicates LeftOrRightRight RVPCOM RVPBASEr.
End RVPPREDr.
Module RVPINSTr : RiscvPmpIrisInstance LeftOrRightRight RiscvPmpBlockVerifFailLogic RVPCOM RVPBASEr RVPPREDr.
  Include RiscvPmpIrisInstance LeftOrRightRight RiscvPmpBlockVerifFailLogic RVPCOM RVPBASEr RVPPREDr.
End RVPINSTr.
Module RVPCONTRr : RiscvPmpIrisInstanceWithContracts LeftOrRightRight RVPCOM RVPBASEr RVPPREDr RVPINSTr.
  Include RiscvPmpIrisInstanceWithContracts LeftOrRightRight RVPCOM RVPBASEr RVPPREDr RVPINSTr.
End RVPCONTRr.
Module RVPTVr : RiscvPmpBlockVerifTotalVerifier LeftOrRightRight RVPCOM RVPBASEr RVPPREDr RVPINSTr RVPCONTRr.
  Include RiscvPmpBlockVerifTotalVerifier LeftOrRightRight RVPCOM RVPBASEr RVPPREDr RVPINSTr RVPCONTRr.
End RVPTVr.
Module RVPBASE2 : RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr.
  Include RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr.
End RVPBASE2.
Module RVPPRED2 : RiscvPmpIrisInstancePredicates2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2.
  Include RiscvPmpIrisInstancePredicates2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2.
End RVPPRED2.
Module RVPADEQ2 : RiscvPmpIrisAdeqParams2 RVPCOM RVPBASEl RVPBASEr RVPBASE2.
  Include RiscvPmpIrisAdeqParams2 RVPCOM RVPBASEl RVPBASEr RVPBASE2.
End RVPADEQ2.
Module RVPINST2 : RiscvPmpIrisInstance2 DefaultFailLogic RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2 RVPPRED2 RVPADEQ2.
  Include RiscvPmpIrisInstance2 DefaultFailLogic RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2 RVPPRED2 RVPADEQ2.
End RVPINST2.
Module Export RVPV2 := BinaryBlockVerifier RVPCOM RVPBASEl RVPPREDl RVPINSTl RVPCONTRl RVPTVl RVPBASEr RVPPREDr RVPINSTr RVPCONTRr RVPTVr RVPBASE2 RVPPRED2 RVPADEQ2 RVPINST2.
