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

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Semantics
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.Machine
     RiscvPmp.Sig.

Import RiscvPmpProgram.
Import RiscvPmpBlockVerifExecutor.
Import Assembly.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Module SWAP.

  Import asn.notations.

  Example block1 : list AST :=
	[ ADD [bv 1] [bv 1] [bv 2]
	; SUB [bv 2] [bv 1] [bv 2]
	; SUB [bv 1] [bv 1] [bv 2]
	].

  Definition Σ1 : LCtx := ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

  Example pre1 : Assertion Σ1 :=
	x1 ↦ term_var "x" ∗
	x2 ↦ term_var "y".

  Example post1 : Assertion Σ1 :=
	x1 ↦ term_var "y" ∗
	x2 ↦ term_var "x".

  Example vc1 : 𝕊 ε :=
	SymProp.demonic_close (BlockVerification.VC pre1 block1 post1).

  Lemma sat_vc1 : VerificationConditionWithErasure (Erasure.erase_symprop vc1).
  Proof. vm_compute. constructor. cbv - [Z.sub Z.add]. lia. Qed.

  Example vc2 : 𝕊 ε :=
	let vc1 := BlockVerificationDerived.VC pre1 block1 post1 in
	let vc2 := Postprocessing.prune vc1 in
	let vc3 := Postprocessing.solve_evars vc2 in
	let vc4 := Postprocessing.solve_uvars vc3 in
	vc4.

  Lemma sat_vc2 : VerificationConditionWithErasure (Erasure.erase_symprop vc2).
  Proof. vm_compute. constructor. cbv - [Z.sub Z.add]. lia. Qed.

  Section ContractAddr.

	Example pre1' : Assertion  {| wctx := Σ1 ▻ ("a"::ty_xlenbits) ; wco := nil |} :=
	  (x1 ↦ term_var "x") ∗ x2 ↦ term_var "y".

	Example post1' : Assertion	{| wctx := Σ1 ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits) ; wco := nil |} :=
		x1 ↦ term_var "y" ∗
		x2 ↦ term_var "x" ∗
		term_var "an" = term_binop bop.plus (term_var "a") (term_val _ (Z.of_nat 12 : Val ty.int)).

  End ContractAddr.

  Example vc3 : 𝕊 ε :=
    RiscvPmpSignature.postprocess
          (BlockVerificationDerived2.VC__addr pre1' block1 post1').

  Lemma sat_vc3' : BlockVerificationDerived2.safeE vc1.
  Proof. vm_compute. constructor. cbv - [Z.sub Z.add]. lia. Qed.

End SWAP.

Module SUM.

  Definition zero : RegIdx := [bv 0].
  Definition ra : RegIdx := [bv 1].
  Definition a0 : RegIdx := [bv 2].
  Definition a4 : RegIdx := [bv 3].
  Definition a5 : RegIdx := [bv 4].
  Definition rra := x1.
  Definition ra0 := x2.
  Definition ra4 := x3.
  Definition ra5 := x4.

  (* C SOURCE *)
  (* int sum(int n) { *)
  (*	 int s = 0; *)
  (*	 for (int i = 0; i != n; ++i) { *)
  (*		 s = s + i; *)
  (*	 } *)
  (*	 return s; *)
  (* } *)

  (* 0000000000000000 <sum>: *)
  (*	0:	00050713			addi	a4,a0,0 *)
  (*	4:	00050e63			beq	a0,zero,20 <.L4> *)
  (*	8:	00000793			addi	a5,zero,0 *)
  (*	c:	00000513			addi	a0,zero,0 *)
  (* 0000000000000010 <.L3>: *)
  (*   10:	00f5053b			addw	a0,a0,a5 *)
  (*   14:	0017879b			addiw	a5,a5,1 *)
  (*   18:	fef71ce3			bne	a4,a5,10 <.L3> *)
  (*   1c:	00008067			jalr	zero,0(ra) *)
  (* 0000000000000020 <.L4>: *)
  (*   20:	00008067			jalr	zero,0(ra) *)

  Example block_sum : list AST :=
	[ ADDI a4 a0 0
	; BEQ a0 zero 0x20
	; ADDI a5 zero 0
	; ADDI a0 zero 0
	].

  Example block_l3 : list AST :=
	[ ADD a0 a0 a5
	; ADDI a5 a5 1
	; BNE a4 a5 (-0x8)
	].

  Example block_l4 : list AST :=
	[ RET
	].

  Example sum : list AST :=
	block_sum ++ block_l3 ++ block_l4.

  Import asn.notations.
  Local Notation "x - y" := (term_binop bop.minus x y) : exp_scope.
  Local Notation "x + y" := (term_binop bop.plus x y) : exp_scope.
  Local Notation "x * y" := (term_binop bop.times x y) : exp_scope.

  Section BlockSum.

	Let Σ1 : LCtx := ["n" ∷ ty.int].

	Example sum_pre : Assertion Σ1 :=
	  asn.exist "s" _ (ra0 ↦ term_var "s") ∗
	  ra4 ↦ term_var "n" ∗
	  asn.exist "i" _ (ra5 ↦ term_var "i") ∗
	  term_val ty.int 0%Z <= term_var "n".

	Example sum_post : Assertion Σ1 :=
	  ra0 ↦ term_val ty.int 0%Z ∗
	  ra4 ↦ term_var "n" ∗
	  ra5 ↦ term_val ty.int 0%Z ∗
	  term_val ty.int 0%Z <= term_var "n".

	Example vc_sum : 𝕊 Σ1 :=
	  BlockVerification.VC sum_pre block_sum sum_post.

	(* Eval compute in vc_sum. *)

  End BlockSum.

  Definition Σ1 : LCtx := ["n" ∷ ty.int; "s" ∷ ty.int; "i" ∷ ty.int].

  (* Example sum_pre : Assertion Σ1 := *)
  (*   ra0 ↦ term_var "s" ∗ *)
  (*   ra4 ↦ term_var "n" ∗ *)
  (*   ra5 ↦ term_var "i" ∗ *)
  (*   asn_bool (term_binop bop.le (term_val ty.int 0%Z) (term_var "n")) ∗ *)
  (*   asn_eq (term_val ty.int 0%Z) (term_var "s") ∗ *)
  (*   asn_eq (term_val ty.int 0%Z) (term_var "i"). *)

  (* Example sum_loop : Assertion Σ1 := *)
  (*   ra0 ↦ term_var "s" ∗ *)
  (*   ra4 ↦ term_var "n" ∗ *)
  (*   ra5 ↦ term_var "i" ∗ *)
  (*   asn_eq *)
  (*	 (term_val ty.int 2%Z * term_var "s") *)
  (*	 (term_var "i" * (term_var "i" - term_val ty.int 1%Z)). *)

  (* Example sum_post : Assertion Σ1 := *)
  (*   ra0 ↦ term_var "s" ∗ *)
  (*   ra4 ↦ term_var "n" ∗ *)
  (*   ra5 ↦ term_var "i" ∗ *)
  (*   asn_eq (term_var "i") (term_var "n") ∗ *)
  (*   asn_eq *)
  (*	 (term_val ty.int 2%Z * term_var "s") *)
  (*	 (term_var "n" * (term_var "n" - term_val ty.int 1%Z)). *)

End SUM.

Module MEMCOPY.

  Open Scope hex_Z_scope.

  (* C SOURCE *)
  (* #include <stdlib.h> *)
  (* void mcpy(char* dst, char* src, size_t size) { *)
  (*	 for (; size != 0; --size) { *)
  (*		 *dst = *src; *)
  (*		 ++dst; *)
  (*		 ++src; *)
  (*	 } *)
  (* } *)

  (* ASSEMBLY SOURCE (modified) *)
  (* mcpy: *)
  (*   beq a2,zero,.L2 *)
  (* .L1: *)
  (*   lb a3,0(a1) *)
  (*   sb a3,0(a0) *)
  (*   addi a0,a0,1 *)
  (*   addi a1,a1,1 *)
  (*   addi a2,a2,-1 *)
  (*   bne a2,zero,.L1 *)
  (* .L2: *)
  (*   ret *)

  (* DISASSEMBLY *)
  (* 0000000000000000 <mcpy>: *)
  (*	0:	00060e63			beqz	a2,1c <.L2> *)
  (* 0000000000000004 <.L1>: *)
  (*	4:	00058683			lb	a3,0(a1) *)
  (*	8:	00d50023			sb	a3,0(a0) *)
  (*	c:	00150513			addi	a0,a0,1 *)
  (*   10:	00158593			addi	a1,a1,1 *)
  (*   14:	fff60613			addi	a2,a2,-1 *)
  (*   18:	fe0616e3			bnez	a2,4 <.L1> *)
  (* 000000000000001c <.L2>: *)
  (*   1c:	00008067			ret *)

  Definition zero : RegIdx := [bv 0].
  Definition ra : RegIdx := [bv 1].
  Definition a0 : RegIdx := [bv 2].
  Definition a1 : RegIdx := [bv 3].
  Definition a2 : RegIdx := [bv 4].
  Definition a3 : RegIdx := [bv 5].
  Definition rra := x1.
  Definition ra0 := x2.
  Definition ra1 := x3.
  Definition ra2 := x4.
  Definition ra3 := x5.

  Example memcpy : list AST :=
	[ BEQ a2 zero 0x1c
	; LOAD 0 a1 a3
	; STORE 0 a3 a0
	; ADDI a0 a0 1
	; ADDI a1 a1 1
	; ADDI a2 a2 (-1)
	; BNE a2 zero (-0x14)
	; RET
	].

  Definition Σ1 : LCtx :=
		["dst" :: ty_xlenbits; "src" :: ty_xlenbits; "size" :: ty.int;
		 "srcval" :: ty.list ty_word; "ret" :: ty_xlenbits].

  Import asn.notations.
  Local Notation "a '↦[' n ']' xs" := (asn.chunk (chunk_user ptstomem [a; n; xs])) (at level 79).
  Local Notation "'∃' w ',' a" := (asn.exist w _ a) (at level 79, right associativity).

  Example memcpy_pre : Assertion Σ1 :=
	pc	↦ term_val ty_xlenbits 0%Z ∗
	rra ↦ term_var "ret" ∗
	ra0 ↦ term_var "dst" ∗
	ra1 ↦ term_var "src" ∗
	ra2 ↦ term_var "size" ∗
	term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
	(∃ "dstval", term_var "dst" ↦[ term_var "size" ] term_var "dstval").

  Example memcpy_post : Assertion Σ1 :=
	pc ↦ term_var "ret" ∗
	rra ↦ term_var "ret" ∗
	(∃ "v", ra0 ↦ term_var "v") ∗
	(∃ "v", ra1 ↦ term_var "v") ∗
	(∃ "v", ra2 ↦ term_var "v") ∗
	term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
	term_var "dst" ↦[ term_var "size" ] term_var "srcval".

  Example memcpy_loop : Assertion Σ1 :=
	pc	↦ term_val ty_xlenbits 0%Z ∗
	rra ↦ term_var "ret" ∗
	ra0 ↦ term_var "dst" ∗
	ra1 ↦ term_var "src" ∗
	ra2 ↦ term_var "size" ∗
	asn.formula (formula_relop bop.neq (term_var "size") (term_val ty.int 0)) ∗
	term_var "src" ↦[ term_var "size" ] term_var "srcval" ∗
	(∃ "dstval", term_var "dst" ↦[ term_var "size" ] term_var "dstval").

End MEMCOPY.
