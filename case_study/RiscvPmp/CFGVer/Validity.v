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

     A property of `c` ALONE: no base, no Σ.  EVERY bridge below takes this
     and nothing annotation-level: annotations appear only where a contract
     is proved valid.

     THE LIST IS TYPED (2026-09-29).  The witness is an
     `AnnotInstrV blkValid` list, so every block annotation CARRIES its
     validity proof (vb_ok) and no validity predicate is ever proved about a
     list: the VC runs over its erasure `map eraseV LV`.  (Until 2026-09-29
     the witness was an erased `list AnnotInstr` plus a hand-proved
     `annotsValid`; that predicate now only appears on the way OUT, as
     annotsValid_of_V.  Until PLAN-loop-rule.md a third conjunct banned
     top-level re-entry annotations, which no longer exist.) *)
  Definition ValidCFGVerifierContract {R : LCtx} (c : @CFGVerifierContract R) : Prop :=
    exists LV : list (AnnotInstrV blkValid),
      cfg_vc c (List.map eraseV LV)
      /\ List.map aiv_instr LV = cfg_instrs c.

  (* THE ONLY WAY IN.  `LV` is explicit: it cannot be recovered from the VC
     by unification (the VC mentions only its erasure), and the call site
     has it by name anyway.  Hvc is typically `exact <the example's VC>`,
     which holds by CONVERSION: the erasure of a literal list reduces to the
     literal erased list the light file verified. *)
  Lemma ValidCFGVerifierContract_intro {R : LCtx} (c : @CFGVerifierContract R)
      (LV : list (AnnotInstrV blkValid))
      (Hvc : cfg_vc c (List.map eraseV LV))
      (Hcode : List.map aiv_instr LV = cfg_instrs c) :
    ValidCFGVerifierContract c.
  Proof. exists LV. split; [exact Hvc | exact Hcode]. Qed.

  (* Erasing a typed list gives valid annotations: each block's proof is
     its own vb_ok. *)
  Lemma annotsValid_of_V (LV : list (AnnotInstrV blkValid)) :
    annotsValid (List.map eraseV LV).
  Proof.
    apply List.Forall_map, List.Forall_forall.
    intros a _ b Hb. unfold eraseV in Hb; cbn in Hb.
    destruct (aiv_block a) as [x|]; cbn in Hb; [|discriminate].
    injection Hb as <-. exact (vb_ok x).
  Qed.

  (* THE ONLY WAY OUT, in the erased form the bridges consume. *)
  Lemma ValidCFGVerifierContract_elim {R : LCtx} (c : @CFGVerifierContract R) :
    ValidCFGVerifierContract c ->
    exists a : list AnnotInstr,
      cfg_vc c a
      /\ strip a = cfg_instrs c
      /\ annotsValid a.
  Proof.
    intros (LV & Hvc & Hcode). exists (List.map eraseV LV).
    split; [exact Hvc|]. split; [rewrite strip_eraseV; exact Hcode|].
    apply annotsValid_of_V.
  Qed.

  Global Opaque ValidCFGVerifierContract.

  (* A plain program as a typed list: no ghosts, no blocks. *)
  Lemma map_aiv_instr_AST (l : list AST) :
    List.map aiv_instr (List.map (@AST_AnnotInstrV blkValid) l) = l.
  Proof. induction l as [|i l IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

  (* One line at a call site for a program with NO block annotations, and it
     names no annotation: the typed list is the plain code, and the
     example's VC matches its erasure by conversion (eraseV of an
     AST_AnnotInstrV is AST_AnnotInstr, by reflexivity).  Pinning LV to
     `cfg_instrs c` before `exact H` is what keeps unification out of it. *)
  Ltac solve_valid H :=
    lazymatch goal with
    | |- ValidCFGVerifierContract ?c =>
        apply (@ValidCFGVerifierContract_intro _ c
                 (List.map (@AST_AnnotInstrV blkValid) (cfg_instrs c)));
        [ exact H | apply map_aiv_instr_AST ]
    end.
