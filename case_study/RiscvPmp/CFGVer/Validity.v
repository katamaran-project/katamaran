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


(* ========================================================================= *)
(* Validity.v -- THE SEALED VALIDITY OF A CONTRACT (PLAN-valid-blk-annot.md    *)
(* Phase 4).                                                                 *)
(*                                                                           *)
(* `ValidCFGVerifierContract c` is a property of the contract alone: there   *)
(* is an annotated program `a` whose VC holds, which strips to the contract's *)
(* code, and whose block annotations are valid (Adequacy.annotsValid).  The  *)
(* ONLY place annotations cross into the soundness bridges: EndToEnd.v and   *)
(* GenCompose.v take this and nothing annotation-level.  Its own file        *)
(* because both need it and they are siblings after Adequacy.v; putting it   *)
(* in either would serialize the other behind it.                            *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.VerifierRel
     RiscvPmp.CFGVer.SpecIris
     RiscvPmp.CFGVer.TablesRel
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.Adequacy.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import iris.proofmode.tactics.
Import IrisInstanceBinary.
Import RiscvPmpIrisInstance2.
Import RiscvPmpSemantics.
Import RiscvPmpIrisAdeqParams2.
Import SmallStepNotations.
Import IrisModelBinary.RiscvPmpIrisBase2.
Import iris.algebra.excl.
Import iris.algebra.gmap.
Import IrisModel.RiscvPmpIrisBase.

  (* ====================================================================== *)
  (* THE ANNOTATION-FREE VALIDITY -- a SEALED projection                     *)
  (* ====================================================================== *)

  (* WHY THIS IS AN EXISTENTIAL, AND WHY THAT IS NOT A DODGE.

     `cfg_vc c a` implies NO annotation-free SYMBOLIC statement about `c`.  A
     hint makes the VC strictly EASIER -- a block skips instructions, a havoc
     discards terms -- so the un-annotated run is a different, harder
     computation and `cfg_vc c a -> cfg_vc c (cfg_instrs c)` is false, on fuel
     alone for a program of any size (PLAN-contract-ast §2.2).  Every symbolic
     statement is "the executor over THIS TABLE succeeded", and the table IS
     the annotation.  So of the three properties one must bend:

       symbolic  /  annotation-free  /  derivable-without-rework

     Bending "symbolic" gives the semantic form (myWP2_loop) -- correct, but it
     drags Iris into a proposition that `ai_block` is meant to quote, which is
     the pollution this definition exists to avoid.  Bending "derivable" gives
     the un-annotated VC, which holds today only because no program in the tree
     uses a hint at its entry point, and breaks the first time one does.  So
     "annotation-free" is what bends -- and only inside the BODY.

     THE SEAL is what makes that honest.  `AnnotInstr` occurs in no statement,
     no premise and no consumer: the only ways in and out are the two lemmas
     below, and `Opaque` stops `unfold`/`cbn`/`destruct` from reaching the
     binder.  So a hint really does never leave the symbolic executor layer --
     it is a proof device, sealed inside the proposition that says a proof
     device was found.

     A property of `c` ALONE: no base, no Σ.  Since PLAN-valid-blk-annot
     Phase 4 the block condition is `annotsValid a` -- every ai_block carries
     its own blkValid proof, no top-level re-entry -- a pure Prop that no
     longer mentions Iris or cfg_init_addr (it used to be an Iris-level
     blocksSound at `cfg_init_addr c`, a field since removed).  EVERY bridge below takes this and
     nothing annotation-level: annotations appear only where a contract is
     proved valid. *)
  Definition ValidCFGVerifierContract {R : LCtx} (c : @CFGVerifierContract R) : Prop :=
    exists a : list AnnotInstr,
      cfg_vc c a
      /\ strip a = cfg_instrs c
      /\ annotsValid a.

  (* THE ONLY WAY IN.  Order is chosen so that `exact <the example's VC>`
     pins `a` before the other two goals are looked at. *)
  Lemma ValidCFGVerifierContract_intro {R : LCtx} (c : @CFGVerifierContract R)
      (a : list AnnotInstr)
      (Hvc : cfg_vc c a)
      (Hstrip : strip a = cfg_instrs c)
      (Hval : annotsValid a) :
    ValidCFGVerifierContract c.
  Proof. exists a. split; [exact Hvc | split; [exact Hstrip | exact Hval]]. Qed.

  (* THE ONLY WAY OUT. *)
  Lemma ValidCFGVerifierContract_elim {R : LCtx} (c : @CFGVerifierContract R) :
    ValidCFGVerifierContract c ->
    exists a : list AnnotInstr,
      cfg_vc c a
      /\ strip a = cfg_instrs c
      /\ annotsValid a.
  Proof. exact (fun H => H). Qed.

  Global Opaque ValidCFGVerifierContract.

  (* One line at a call site, and it names no annotation: the hint list is
     recovered by unification from the example's own VC. *)
  (* Closes `annotsValid a` for a program with no block annotations.  TWO
     alternatives because a program list reaches here in two syntactic shapes:
     `list_AST_AnnotInstr l` when a named `list AST` is coerced wholesale, and
     a plain cons-list of per-element coercions when the literal is written
     inline (Verifier.v's `Local Arguments List.cons {_} & _ _` makes the
     coercion fire elementwise inside a bracket literal).  Only the first
     matches ai_block_none_of_AST; `repeat constructor` handles the second,
     since each `ai_fire true (AST_AnnotInstr a) = None` closes by eq_refl.
     (Replaced EndToEnd's solve_no_blocks, which closed the old Iris-level
     blocksSound premise the same way.) *)
  Ltac solve_annots_none :=
    apply annotsValid_of_none;
    solve [ apply ai_block_none_of_AST | repeat constructor ].

  Ltac solve_valid H :=
    eapply ValidCFGVerifierContract_intro;
      [ exact H | apply strip_of_AST | solve_annots_none ].
