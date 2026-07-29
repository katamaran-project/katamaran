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
(* CFGVer/Spec.v — first file in the CFGVer compilation order.               *)
(*                                                                           *)
(* Defines Assembly (instruction-builder synonyms: ADD, SUB, BEQ, ADDI,      *)
(* JALR/RET, MUL family, ...) and CFGVer's OWN leakage-aware `Specification` *)
(* instance (RiscvPmpCFGVerifSpec, independent of the plain one in           *)
(* ../Contracts.v): secLeakvar/inv_leakage-annotated SepContracts for the    *)
(* primitive functions (rX, wX, fetch, mem_read/write, decode, leak, ...),   *)
(* the SYMBOLIC executor built from it, and the ValidContract proofs.        *)
(*                                                                           *)
(* DELIBERATELY Iris-free, and free of the shallow/refine/soundness stack.   *)
(* The Iris wiring (RiscvPmpIrisInstanceWithContracts) and the shallow       *)
(* executor live in SpecIris.v instead. That split is what lets Contracts.v, *)
(* GenContract.v and every Example/*.v avoid loading the binary Iris model   *)
(* (~0.98 GB) and the shallow/refine/soundness stack (~0.31 GB) — they need  *)
(* only to vm_compute the symbolic executor. Only the soundness chain        *)
(* (Adequacy.v, EndToEnd.v) needs SpecIris.v.                                *)
(*                                                                           *)
(* DON'T re-add an Iris or ShallowExecutor require here — it silently puts   *)
(* ~1.3 GB back onto every example file.                                     *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Bitvector
     Sep.Hoare
     Specification
     MicroSail.SymbolicExecutor.
From Katamaran Require Import
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts.

Import RiscvPmpProgram.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.

Module Assembly.
  (* Instruction synonyms. *)
  Definition ADD (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_ADD.
  Definition SUB (rd rs1 rs2 : RegIdx) : AST :=
    RTYPE rs2 rs1 rd RISCV_SUB.
  Definition BEQ (rs1 rs2 : RegIdx) (imm : bv 13) : AST :=
    BTYPE imm rs2 rs1 RISCV_BEQ.
  Definition BNE (rs1 rs2 : RegIdx) (imm : bv 13) : AST :=
    BTYPE imm rs2 rs1 RISCV_BNE.
  Definition ADDI (rd rs1 : RegIdx) (imm : bv 12) : AST :=
    ITYPE imm rs1 rd RISCV_ADDI.
  Definition JALR (rd rs1 : RegIdx) (imm : bv 12) : AST :=
    RISCV_JALR imm rs1 rd.
  Definition RET : AST :=
    JALR (bv.of_N 0) (bv.of_N 1) bv.zero.
  Definition MV (rd rs1 : RegIdx) : AST :=
    ADDI rd rs1 bv.zero.
  Definition MUL (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd false true true.
  Definition MULH (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true true true.
  Definition MULHSU (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true true false.
  Definition MULHU (rd rs1 rs2 : RegIdx) : AST :=
    Base.MUL rs2 rs1 rd true false false.
End Assembly.

Module RiscvPmpCFGVerifSpec <: Specification RiscvPmpBase RiscvPmpSignature RiscvPmpProgram.
  Include SpecificationMixin RiscvPmpBase RiscvPmpSignature RiscvPmpProgram.
  Section ContractDefKit.

  Import asn.notations.
  Notation asn_bool t := (asn.formula (formula_bool t)).
  Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).
  Notation "a '↦ᵣ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70).
  Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  (* Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])). *)
  (* Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])). *)
  (* Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])). *)
  (* Notation asn_inv_mmio bytes := (asn.chunk (chunk_user (inv_mmio bytes) [env])). *)
  (* Notation asn_mmio_checked_write bytes a w := (asn.chunk (chunk_user (mmio_checked_write bytes) [a; w])). *)
  Notation asn_inv_leakage := (asn.chunk (chunk_user inv_leakage [env])).

  Definition term_eqb {Σ} (e1 e2 : Term Σ ty_regno) : Term Σ ty.bool :=
    term_binop (bop.relop bop.eq) e1 e2.

  Definition term_eqb_1 {Σ} (e1 e2 : Term Σ (ty.bvec 1)) : Term Σ ty.bool :=
    term_binop (bop.relop bop.eq) e1 e2.

  Local Notation "e1 '=?' e2" := (term_eqb e1 e2).

  Definition z_term {Σ} : Z -> Term Σ ty.int := term_val ty.int.

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx.map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env.tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (ctx.in_cat_left Σ (ctx.in_map (fun '(y::τ) => y::τ) xIn)))).

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Fixpoint asn_exists {Σ} (Γ : NCtx string Ty) : Assertion (Σ ▻▻ Γ) -> Assertion Σ :=
    match Γ return Assertion (Σ ▻▻ Γ) -> Assertion Σ with
    | ctx.nil => fun asn => asn
    | ctx.snoc Γ (x :: τ) =>
      fun asn =>
        @asn_exists Σ Γ (asn.exist x τ asn)
    end.

  Definition asn_with_reg {Σ} (r : Term Σ ty_regno) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
     asn.match_bool (r =? term_val ty_regno (bv.of_N 0)) (asn_default)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 1)) (asn x1)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 2)) (asn x2)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 3)) (asn x3)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 4)) (asn x4)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 5)) (asn x5)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 6)) (asn x6)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 7)) (asn x7)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 8)) (asn x8)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 9)) (asn x9)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 10)) (asn x10)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 11)) (asn x11)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 12)) (asn x12)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 13)) (asn x13)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 14)) (asn x14)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 15)) (asn x15)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 16)) (asn x16)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 17)) (asn x17)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 18)) (asn x18)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 19)) (asn x19)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 20)) (asn x20)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 21)) (asn x21)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 22)) (asn x22)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 23)) (asn x23)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 24)) (asn x24)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 25)) (asn x25)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 26)) (asn x26)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 27)) (asn x27)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 28)) (asn x28)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 29)) (asn x29)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 30)) (asn x30)
    (asn.match_bool (r =? term_val ty_regno (bv.of_N 31)) (asn x31)
     ⊥))))))))))))))))))))))))))))))).

    Definition asn_with_reg_1 {Σ} (r : Term Σ (ty.bvec 1)) (asn : Reg ty_xlenbits -> Assertion Σ) (asn_default : Assertion Σ) : Assertion Σ :=
     asn.match_bool (term_eqb_1 r (term_val (ty.bvec 1) (bv.of_N 0))) (asn_default)
    (asn.match_bool (term_eqb_1 r (term_val (ty.bvec 1) (bv.of_N 1))) (asn x1)⊥).

  Definition asn_reg_ptsto {Σ} (r : Term Σ ty_regno) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty_word bv.zero).

  Definition asn_reg_ptsto_1 {Σ} (r : Term Σ (ty.bvec 1)) (w : Term Σ ty_word) : Assertion Σ :=
    asn_with_reg_1 r (fun r => asn.chunk (chunk_ptsreg r w)) (w = term_val ty_word bv.zero).

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

  (* TODO: abstract away the concrete type, look into unions for that *)
  (* TODO: length of list should be 16, no duplicates *)
  (* Definition pmp_entries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfgidx ty_pmpaddridx)) :=
    term_list
      (cons (term_val ty_pmpcfgidx PMP0CFG ,ₜ term_val ty_pmpaddridx PMPADDR0)
            (cons (term_val ty_pmpcfgidx PMP1CFG ,ₜ term_val ty_pmpaddridx PMPADDR1) nil)). *)

  End ContractDefKit.

  Import RiscvPmpSpecification.

  Import asn.notations.
  (* TODO: This notation is already defined with a different meaning in
     asn.notations. Resolve this.
   *)
  (* Notation "a '*↦ₘ[' n ']' xs" := (asn.chunk (chunk_user (@ptstomem n) [a; xs])) (at level 79). *)
  Local Notation "a '↦ₘ[' bytes ']' t" := (asn.chunk (chunk_user (@ptstomem bytes) [a; t])) (at level 70).
  Local Notation "a '↦ᵣ[' bytes ']' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes) [a; t])) (at level 70).
  #[global] Notation "r '↦ᵣ' val" := (asn_reg_ptsto r val) (at level 70) : asn_scope.
  #[global] Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70) : asn_scope.
  #[global] Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user (@ptstomem_readonly bytes_per_word) [a; t])) (at level 70) : asn_scope.
  Local Notation "a '↦ᵢ' t" := (asn.chunk (chunk_user ptstoinstr [a; t])) (at level 70).
  Local Notation "a <ₜ b" := (term_binop bop.lt a b) (at level 60).
  Local Notation "a <=ₜ b" := (term_binop bop.le a b) (at level 60).
  Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
  Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
  Local Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn.match_sum T ty.unit opt xl alt_inl "_" alt_inr).
  (* Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])). *)
  (* Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])). *)
  (* Local Notation asn_pmp_access addr width es m p := (asn.formula (formula_user pmp_access [addr;width;es;m;p])). *)
  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
  (* TODO: clean up above notations to get rid of the following one *)
  Local Notation asn_cur_privilege val := (asn.chunk (chunk_ptsreg cur_privilege val)).
  Local Notation asn_bool t := (asn.formula (formula_bool t)).
  (* Local Notation asn_in_mmio n l := (asn.formula (formula_user (in_mmio n) [l])). *)
  (* Local Notation asn_inv_mmio bytes := (asn.chunk (chunk_user (inv_mmio bytes) [env])). *)
  (* Local Notation asn_mmio_checked_write bytes a w := (asn.chunk (chunk_user (mmio_checked_write bytes) [a; w])). *)
  Import bv.notations.

  Definition sep_contract_rX : SepContractFun rX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "reg_val" :: ty_word];
       sep_contract_localstore      := [term_var "rs"];
      sep_contract_precondition    := secLeakvar "rs" ∗ term_var "rs" ↦ᵣ term_var "reg_val";
       sep_contract_result          := "result_rX";
       sep_contract_postcondition   := asn.formula (formula_propeq (term_var "result_rX") (term_var "reg_val")) ∗
                                       term_var "rs" ↦ᵣ term_var "reg_val";
    |}.

  Definition sep_contract_wX : SepContractFun wX :=
    {| sep_contract_logic_variables := ["rs" :: ty_regno; "v" :: ty_xlenbits; "reg_val" :: ty_xlenbits];
       sep_contract_localstore      := [term_var "rs"; term_var "v"];
      sep_contract_precondition    := secLeakvar "rs" ∗ term_var "rs" ↦ᵣ term_var "reg_val";
       sep_contract_result          := "result_wX";
       sep_contract_postcondition   := term_var "result_wX" = term_val ty.unit tt ∗
                                       if: term_eqb (term_var "rs") (term_val ty_regno [bv 0])
                                       then term_var "rs" ↦ᵣ term_val ty_word bv.zero
                                       else term_var "rs" ↦ᵣ term_var "v"
    |}.

  Definition sep_contract_fetch_instr : SepContractFun fetch :=
    {| sep_contract_logic_variables := ["a" :: ty_xlenbits; "i" :: ty_ast(* ; "entries" :: ty.list ty_pmpentry *)];
       sep_contract_localstore      := [];
       sep_contract_precondition    :=
        (* ORDER IS LOAD-BEARING: a pure `secLeakvar`/formula conjunct must come
           AFTER whatever chunk pins its logic variable.  `call_contract`
           (Symbolic/Monads.v) instantiates a contract's logic variables
           ANGELICALLY, and `consume` walks ∗ left-to-right, so a conjunct
           placed before the chunk that unifies its variable is asserted while
           that variable is still an unconstrained evar — unprovable, and the
           obligation survives into the VC as a residual.  `postprocess`'s
           solve_evars then substitutes the variable, so the leftover *prints*
           as the trivially-true `secLeak p` and looks like a solver bug; it
           isn't, the solver never saw it in that form (diagnosed 2026-07-29).
           Here `sep_contract_localstore` is [], so nothing pins "a" until the
           pc chunk below.  Reordering these two conjuncts removes all 28
           secLeak asserts from key_schedule_loop2's VC (3.17 MB -> 524 KB).
           Same invariant, same reason: the trailing secLeakvar "paddr" in
           mem_write_value / checked_mem_write.

           LIMIT OF THE REWRITE: this only works when the conjunct crosses a
           CHUNK, which merely adds an equation.  It must NOT be applied across
           a PATTERN MATCH on the same variable — that eliminates the variable,
           so the moved conjunct degrades to a statement about a literal and the
           precondition genuinely weakens.  See the note on
           sep_contract_checked_mem_read, where trying it makes the contract
           unprovable against its own body. *)
        asn.chunk (chunk_ptsreg pc (term_var "a")) ∗
        secLeakvar "a" ∗ (* Technically this can be concluded from the formula_le, but I think it is better explicit *)
          term_var "a" ↦ᵢ term_var "i" ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "a"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "a")) (term_val ty.int (Z.of_nat bytes_per_instr))) <= term_val ty.int (Z.of_N maxAddr) ∗
                                                                                                                 asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
                                                 (* asn_pmp_entries (term_var "entries") ∗ *)
                                                 (* asn_pmp_access (term_var "a") (term_val ty_word bv_instrsize) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Execute) *) ∗
                                                                                                                 asn.chunk (chunk_user inv_leakage [env]);
       sep_contract_result          := "result_fetch";
       sep_contract_postcondition   :=
        secLeakvar "a" ∗
         asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
         asn.exist "encoded_instr" _
         (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "encoded_instr") ∗
                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])) ∗
           asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
           (* asn_pmp_entries (term_var "entries") *);
    |}.

  Definition sep_contract_checked_mem_read {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_read bytes H) :=
     {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "cmem_val" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        (* "inv" STAYS IN FRONT — do not "fix" this the way
           sep_contract_fetch_instr was fixed.  The only thing that would pin
           "inv" is the match_bool below, and that is a pattern match, which
           ELIMINATES the variable rather than merely constraining it: after it,
           secLeakvar "inv" degrades to "this literal is public" and the
           precondition no longer states that the caller's `inv` was public.
           Measured 2026-07-29: moving it makes this contract unprovable against
           its own body (all three restrict_bytes cases reduce to false = true).
           Crossing a CHUNK is information-preserving; crossing a pattern match
           on the same variable is not.  The residual this leaves at call sites
           is `secLeak <literal>`, which solve_vc closes trivially — unlike the
           fetch case, where it was `secLeak (p + c)`. *)
         secLeakvar "inv" ∗
           secLeakvar "paddr" ∗
        asn.match_bool (term_var "inv")
          (term_var "paddr" ↦ᵣ[ bytes ] term_var "cmem_val")
          (term_var "paddr" ↦ₘ[ bytes ] term_var "cmem_val") ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗
                                                                                                           asn.chunk (chunk_user inv_leakage [env]);
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=
         secLeakvar "inv" ∗
           secLeakvar "paddr" ∗
           asn.formula (formula_propeq (term_var "result_mem_read") (term_union (memory_op_result bytes) KMemValue (term_var "cmem_val"))) ∗
         asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "cmem_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "cmem_val");
    |}.


  Definition sep_contract_checked_mem_write {bytes} {H: restrict_bytes bytes} : SepContractFun (@checked_mem_write bytes H) :=
    {| sep_contract_logic_variables := [(* "inv" :: ty.bool; *) "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"];
      sep_contract_precondition    :=
        (* asn.match_bool (term_var "inv") *)
        (*   ((* asn_in_mmio bytes (term_var "paddr") ∗ *) *)
        (*     ∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗ *)
        (*    term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits)))(*  ∗ *) *)
        (*    (* asn_inv_mmio bytes ∗ *) *)
        (*    (* asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") *)) *)
        (*   ( *)
            ∃ "cmem_val", term_var "paddr" ↦ₘ[ bytes ] term_var "cmem_val" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)(* ) *) ∗
                                                                                                            asn.chunk (chunk_user inv_leakage [env]) ∗
    (* Deliberately LAST — do not move to the front.  See the ordering note on
       sep_contract_fetch_instr: a secLeakvar consumed before the chunk that
       pins its variable becomes an undischargeable VC residual. *)
    secLeakvar "paddr";
      sep_contract_result          := "result_checked_mem_write";
      sep_contract_postcondition   :=
        term_var "result_checked_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        (* asn.match_bool (term_var "inv") ⊤ *) (term_var "paddr" ↦ₘ[ bytes ] term_var "data");
    |}.

  (* Definition sep_contract_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : SepContractFun (@pmpCheck bytes H) := *)
  (*   {| sep_contract_logic_variables := ["addr" :: ty_xlenbits; "acc" :: ty_access_type; "priv" :: ty_privilege; "entries" :: ty.list ty_pmpentry]; *)
  (*      sep_contract_localstore      := [term_var "addr"; term_var "acc"; term_var "priv"]; *)
  (*      sep_contract_precondition    := *)
  (*       asn_pmp_entries (term_var "entries") *)
  (*         ∗ term_var "priv" = term_val ty_privilege Machine *)
  (*                               ∗ asn_pmp_access (term_var "addr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "priv") (term_var "acc"); *)
  (*      sep_contract_result          := "result_pmpCheck"; *)
  (*      sep_contract_postcondition   := *)
  (*        term_var "result_pmpCheck" = term_inr (term_val ty.unit tt) *)
  (*        ∗ asn_pmp_entries (term_var "entries"); *)
  (*   |}. *)

  (* Definition sep_contract_pmp_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_read bytes H) := *)
  (*   {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; "w" :: ty_bytes bytes; "m" :: ty_privilege]; *)
  (*     sep_contract_localstore      := [term_var "typ"; term_var "m"; term_var "paddr"]; *)
  (*     sep_contract_precondition    := *)
  (*       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗ *)
  (*         term_var "m" = term_val ty_privilege Machine ∗ *)
  (*         (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ *)
  (*         (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗ *)
  (*         asn_cur_privilege (term_var "m") ∗ *)
  (*         asn_pmp_entries (term_var "entries") ∗ *)
  (*         asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ"); *)
  (*     sep_contract_result          := "result_mem_read"; *)
  (*     sep_contract_postcondition   := *)
  (*       term_var "result_mem_read" = term_union (memory_op_result bytes) KMemValue (term_var "w") ∗ *)
  (*       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "w") (term_var "paddr" ↦ₘ[ bytes ] term_var "w") ∗ *)
  (*       asn_cur_privilege (term_val ty_privilege Machine) ∗ *)
  (*       asn_pmp_entries (term_var "entries"); *)
  (*   |}. *)


  (* Definition sep_contract_pmp_mem_write {bytes} {H: restrict_bytes bytes} : SepContractFun (@pmp_mem_write bytes H) := *)
  (*   {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes; "typ" :: ty_access_type; "m" :: ty_privilege; "entries" :: ty.list ty_pmpentry]; *)
  (*     sep_contract_localstore      := [term_var "paddr"; term_var "data"; term_var "typ"; term_var "m"]; *)
  (*     sep_contract_precondition    := *)
  (*       asn.match_bool (term_var "inv") *)
  (*         (asn_in_mmio bytes (term_var "paddr") ∗ *)
  (*          term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) ∗ *)
  (*          asn_inv_mmio bytes ∗ *)
  (*          asn_mmio_checked_write bytes (term_var "paddr") (term_var "data")) *)
  (*         (∃ "w", term_var "paddr" ↦ₘ[ bytes ] term_var "w" ∗ *)
  (*          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ *)
  (*          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)) ∗ *)
  (*       asn_cur_privilege (term_var "m") ∗ *)
  (*       term_var "m" = term_val ty_privilege Machine ∗ *)
  (*       asn_pmp_entries (term_var "entries") ∗ *)
  (*       asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var "m") (term_var "typ"); *)
  (*     sep_contract_result          := "result_mem_write"; *)
  (*     sep_contract_postcondition   := *)
  (*       term_var "result_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗ *)
  (*       asn.match_bool (term_var "inv") ⊤ (term_var "paddr" ↦ₘ[ bytes ] term_var "data") ∗ *)
  (*       asn_cur_privilege (term_var "m") ∗ *)
  (*       asn_pmp_entries (term_var "entries"); *)
  (*   |}. *)

  Definition sep_contract_mem_read {bytes} {H : restrict_bytes bytes} : SepContractFun (@mem_read bytes H) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "typ" :: ty_access_type; "paddr" :: ty_xlenbits; (* "entries" :: ty.list ty_pmpentry; *) "mem_val" :: ty_bytes bytes];
      sep_contract_localstore      := [term_var "typ"; term_var "paddr"];
      sep_contract_precondition    :=
        (* "inv" stays in front — see the note on sep_contract_checked_mem_read. *)
        secLeakvar "inv" ∗
          secLeakvar "paddr" ∗
        asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "mem_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "mem_val") ∗
          (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
          (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr) ∗
          asn_cur_privilege (term_val ty_privilege Machine)(*  ∗ *)
          (* asn_pmp_entries (term_var "entries") ∗ *)
          (* asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_var "typ") *) ∗
          asn.chunk (chunk_user inv_leakage [env]);
      sep_contract_result          := "result_mem_read";
      sep_contract_postcondition   :=

        secLeakvar "inv" ∗
          secLeakvar "paddr" ∗
        asn.formula (formula_propeq (term_var "result_mem_read") (term_union (memory_op_result bytes) KMemValue (term_var "mem_val"))) ∗
                                       asn.match_bool (term_var "inv") (term_var "paddr" ↦ᵣ[ bytes ] term_var "mem_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "mem_val") ∗
          asn_cur_privilege (term_val ty_privilege Machine)(*  ∗ *)
          (* asn_pmp_entries (term_var "entries") *);
    |}.

  (* Access type `Write` needed here, as `mem_write_value` calls `pmp_mem_write` with this access type*)
  Definition sep_contract_mem_write_value {bytes} {H: restrict_bytes bytes} : SepContractFun (@mem_write_value bytes H) :=
    {| sep_contract_logic_variables := [(* "inv" :: ty.bool; *) "paddr" :: ty_xlenbits; "data" :: ty_bytes bytes(* ; "entries" :: ty.list ty_pmpentry *)];
      sep_contract_localstore      := [term_var "paddr"; term_var "data"];
      sep_contract_precondition    :=
        (* asn.match_bool (term_var "inv") *)
        (*   ((* asn_in_mmio bytes (term_var "paddr") ∗ *) *)
        (*    term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits))) (* ∗ *) *)
        (*    (* asn_inv_mmio bytes ∗ *) *)
        (*    (* asn_mmio_checked_write bytes (term_var "paddr") (term_var "data") *)) *)
          (∃ "mem_val", term_var "paddr" ↦ₘ[ bytes ] term_var "mem_val" ∗
           (term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗
           (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)) ∗
        asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
        (* asn_pmp_entries (term_var "entries") ∗ *)
        (* asn_pmp_access (term_var "paddr") (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_val ty_privilege Machine) (term_val ty_access_type Write) *) ∗
        asn.chunk (chunk_user inv_leakage [env]) ∗
    (* Deliberately LAST — do not move to the front; see sep_contract_fetch_instr. *)
    secLeakvar "paddr";
      sep_contract_result          := "result_mem_write";
      sep_contract_postcondition   :=
        term_var "result_mem_write" = term_union (memory_op_result 1) KMemValue (term_val ty_byte [bv 1]) ∗
        (* asn.match_bool (term_var "inv") ⊤ *) (term_var "paddr" ↦ₘ[ bytes ] term_var "data") ∗
        asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
        (* asn_pmp_entries (term_var "entries") *);
    |}.


  Definition sep_contract_tick_pc : SepContractFun tick_pc :=
    {| sep_contract_logic_variables := ["ao" :: ty_xlenbits; "an" :: ty_xlenbits];
       sep_contract_localstore      := [];
       sep_contract_precondition    := asn.chunk (chunk_ptsreg pc (term_var "ao")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an"));
       sep_contract_result          := "result_tick_pc";
       sep_contract_postcondition   := asn.chunk (chunk_ptsreg pc (term_var "an")) ∗
                                                 asn.chunk (chunk_ptsreg nextpc (term_var "an")) ∗
                                                 term_var "result_tick_pc" = term_val ty.unit tt;
    |}.

  Definition sep_contract_within_phys_mem : SepContractFun within_phys_mem :=
    {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "width" :: ty.int];
       sep_contract_localstore      := [term_var "paddr"; term_var "width"];
       sep_contract_precondition    :=
        let paddr_int : Term _ ty.int := term_unsigned (term_var "paddr") in
        (term_val ty.int (Z.of_N minAddr) <= paddr_int) ∗
          (term_binop bop.plus paddr_int (term_var "width")) <= term_val ty.int (Z.of_N maxAddr);
       sep_contract_result          := "result_within_phys_mem";
       sep_contract_postcondition   :=
         term_var "result_within_phys_mem" = term_val ty.bool true;
    |}.

  Definition sep_contract_execute_EBREAK : SepContractFun execute_EBREAK :=
    RiscvPmpExecutor.Symbolic.Statistics.extend_postcond_with_debug sep_contract_execute_EBREAK.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | rX                         => Some sep_contract_rX
      | wX                         => Some sep_contract_wX
      | fetch                      => Some sep_contract_fetch_instr
      | @mem_read bytes H          => Some (@sep_contract_mem_read bytes H)
      | @mem_write_value bytes H   => Some (@sep_contract_mem_write_value bytes H)
      | tick_pc                    => Some sep_contract_tick_pc
      (* | @pmpCheck bytes H          => Some (@sep_contract_pmpCheck bytes H) *)
      | within_phys_mem            => Some sep_contract_within_phys_mem
      (* | pmpMatchAddr               => Some sep_contract_pmpMatchAddr *)
      (* | @pmp_mem_read bytes H      => Some (@sep_contract_pmp_mem_read bytes H) *)
      (* | @pmp_mem_write bytes H     => Some (@sep_contract_pmp_mem_write bytes H) *)
      | @checked_mem_read bytes H  => Some (@sep_contract_checked_mem_read bytes H)
      | @checked_mem_write bytes H => Some (@sep_contract_checked_mem_write bytes H)
      | execute_EBREAK            => Some sep_contract_execute_EBREAK
      | _                         => None
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Definition sep_contract_read_ram {bytes} : SepContractFunX (read_ram bytes) :=
    {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits; "ram_val" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"];
       sep_contract_precondition    :=
        asn.match_bool (term_var "inv")  (term_var "paddr" ↦ᵣ[ bytes ] term_var "ram_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "ram_val");
       sep_contract_result          := "result_read_ram";
       sep_contract_postcondition   :=
        asn.match_bool (term_var "inv")
        (term_var "paddr" ↦ᵣ[ bytes ] term_var "ram_val") (term_var "paddr" ↦ₘ[ bytes ] term_var "ram_val") ∗
        asn.formula (formula_propeq (term_var "result_read_ram") (term_var "ram_val"));
    |}.

  Definition sep_contract_write_ram {bytes} : SepContractFunX (write_ram bytes) :=
    {| sep_contract_logic_variables := ["paddr" :: ty_word; "data" :: ty_bytes bytes];
       sep_contract_localstore      := [term_var "paddr"; term_var "data"];
       sep_contract_precondition    := ∃ "ram_val", (asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "ram_val"]));
       sep_contract_result          := "result_write_ram";
       sep_contract_postcondition   :=  term_var "paddr" ↦ₘ[ bytes ] term_var "data";
    |}.

  (* Note; we define the contract like tvhis, because it matches the PRE of `checked_mem_read` quite well*)
  (* Definition sep_contract_within_mmio `(H : restrict_bytes bytes) : SepContractFunX (within_mmio H) := *)
  (*   {| sep_contract_logic_variables := ["inv" :: ty.bool; "paddr" :: ty_xlenbits]; *)
  (*       sep_contract_localstore      := [term_var "paddr"]; *)
  (*       sep_contract_precondition    := *)
  (*       asn.match_bool (term_var "inv") *)
  (*         (asn_in_mmio bytes (term_var "paddr") ∗ *)
  (*          term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes)) < (term_val ty.int (Z.of_N (bv.exp2 xlenbits)))) *)
  (*         ((term_val ty.int (Z.of_N minAddr) <= term_unsigned (term_var "paddr"))%asn ∗ (term_binop bop.plus (term_unsigned (term_var "paddr")) (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)); *)
  (*       sep_contract_result          := "result_is_within"; *)
  (*       sep_contract_postcondition   := term_var "result_is_within" = term_var "inv" *)
  (*   |}. *)

  (* NOTE: No new contract for `read`, as femtokernel does not perform any reads for now *)
  (* NOTE: for now no resources in `POST`; add those once we need to reinstate local state *)
  (* NOTE: if overflow is important, a no-overflow statement can be added to the `asn_mmio_checked_write` resource *)
  (* Definition sep_contract_mmio_write (bytes : nat) {H: restrict_bytes bytes} : SepContractFunX (mmio_write H) := *)
  (*   {| sep_contract_logic_variables := ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes]; *)
  (*       sep_contract_localstore      := [term_var "paddr"; term_var "data"]; *)
  (*       sep_contract_precondition    := *)
  (*          asn_in_mmio bytes (term_var "paddr") ∗ *)
  (*          asn_inv_mmio bytes ∗ *)
  (*          asn_mmio_checked_write bytes (term_var "paddr") (term_var "data"); *)
  (*       sep_contract_result          := "result_write_mmio"; *)
  (*       sep_contract_postcondition   := ⊤; *)
  (*   |}. *)

  Definition sep_contract_decode    : SepContractFunX decode :=
    {| sep_contract_logic_variables := ["code" :: ty_word; "instr" :: ty_ast];
       sep_contract_localstore      := [term_var "code"];
       sep_contract_precondition    := asn.chunk (chunk_user encodes_instr [term_var "code"; term_var "instr"]);
       sep_contract_result          := "result_decode";
       sep_contract_postcondition   := term_var "result_decode" = term_var "instr";
    |}.

  Definition sep_contract_leak    : SepContractFunX leak :=
    {| sep_contract_logic_variables := ["leak" :: ty_leak_event];
      sep_contract_localstore      := [term_var "leak"];
      sep_contract_precondition    := asn.chunk (chunk_user inv_leakage [env]) ∗
    secLeakvar "leak";
      sep_contract_result          := "result";
      sep_contract_postcondition   := ⊤;
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | read_ram bytes  => sep_contract_read_ram
      | write_ram bytes => sep_contract_write_ram
      (* | within_mmio res => sep_contract_within_mmio res *)
      (* | mmio_read bytes => sep_contract_mmio_read bytes *)
      (* | mmio_write res  => @sep_contract_mmio_write _ res *)
      | decode          => sep_contract_decode
      | leak            => sep_contract_leak
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Definition lemma_open_gprs : SepLemma open_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_close_gprs : SepLemma close_gprs :=
    {| lemma_logic_variables := ctx.nil;
       lemma_patterns        := env.nil;
       lemma_precondition    := ⊤;
       lemma_postcondition   := ⊤;
    |}.

  Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"];
       lemma_precondition    := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
      lemma_postcondition   := ∃ "op", (asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "op"]) ∗
                                          asn.chunk (chunk_user encodes_instr [term_var "op"; term_var "i"]) ∗
                                          secLeakvar "op"
                                       )
    |}.

  Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
    {| lemma_logic_variables := ["paddr" :: ty_word; "cl" :: ty_word; "i" :: ty_ast];
       lemma_patterns        := [term_var "paddr"; term_var "cl"];
       lemma_precondition    := asn.chunk (chunk_user (ptstomem bytes_per_word) [term_var "paddr"; term_var "cl"]) ∗
                                  asn.chunk (chunk_user encodes_instr [term_var "cl"; term_var "i"]) ∗
                                  secLeakvar "cl";
       lemma_postcondition   := asn.chunk (chunk_user ptstoinstr [term_var "paddr"; term_var "i"]);
    |}.

  (* Definition lemma_extract_pmp_ptsto bytes : SepLemma (extract_pmp_ptsto bytes) := *)
  (*   {| lemma_logic_variables := ["paddr" :: ty_xlenbits]; *)
  (*      lemma_patterns        := [term_var "paddr"]; *)
  (*      lemma_precondition    := ⊤; *)
  (*      lemma_postcondition   := ⊤; *)
  (*   |}. *)

  (* Definition lemma_return_pmp_ptsto bytes : SepLemma (return_pmp_ptsto bytes) := *)
  (*   {| lemma_logic_variables := ["paddr" :: ty_xlenbits]; *)
  (*      lemma_patterns        := [term_var "paddr"]; *)
  (*      lemma_precondition    := ⊤; *)
  (*      lemma_postcondition   := ⊤; *)
  (*   |}. *)

  Definition map_wordwidth (w : WordWidth) : nat :=
    match w with
    | BYTE => 1
    | HALF => 2
    | WORD => 4 end.

  (* Use bounds Lemma to calculate bounds on truncation *)
  Local Lemma wordwidth_upper_bound widthh : IsTrue (map_wordwidth widthh * byte <=? bytes_per_word * byte)%nat.
  Proof. destruct widthh; now compute. Qed.
  Local Hint Resolve wordwidth_upper_bound : typeclass_instances.

  Import TermNotations.

  (* Definition lemma_close_mmio_write (immm : bv 12) (widthh : WordWidth): SepLemma (close_mmio_write immm widthh) := *)
  (*   {| lemma_logic_variables := ["paddr" :: ty_xlenbits; "w" :: ty_xlenbits]; *)
  (*      lemma_patterns        := [term_var "paddr"; term_var "w"]; *)
  (*      lemma_precondition    := *)
  (*       (term_val ty_xlenbits RiscvPmpIrisInstance.write_addr) = (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) ∗ *)
  (*       (term_var "w") = (term_val ty_xlenbits (bv.of_nat 42)); *)
  (*      lemma_postcondition   := *)
  (*       asn_mmio_checked_write (map_wordwidth widthh) (term_var "paddr" +ᵇ term_sext (term_val (ty.bvec 12) immm)) (term_truncate (map_wordwidth widthh * byte) (term_var "w")); *)
  (*   |}. *)

   Definition LEnv : LemmaEnv :=
     fun Δ l =>
       match l with
       | open_gprs                    => lemma_open_gprs
       | close_gprs                   => lemma_close_gprs
       | open_ptsto_instr             => lemma_open_ptsto_instr
       | close_ptsto_instr            => lemma_close_ptsto_instr
       (* | open_pmp_entries             => lemma_open_pmp_entries *)
       (* | close_pmp_entries            => lemma_close_pmp_entries *)
       (* | extract_pmp_ptsto bytes      => lemma_extract_pmp_ptsto bytes *)
       (* | return_pmp_ptsto bytes       => lemma_return_pmp_ptsto bytes *)
       (* | close_mmio_write immm widthh => lemma_close_mmio_write immm widthh *)
      end.
End RiscvPmpCFGVerifSpec.

Module RiscvPmpCFGVerifExecutor :=
  MakeExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram RiscvPmpCFGVerifSpec.

Module RiscvPmpSpecVerif.
  Import RiscvPmpCFGVerifSpec.
  Import RiscvPmpCFGVerifExecutor.Symbolic.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.

  Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContract c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithFuelDebug {Δ τ} (fuel : nat) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractWithFuel fuel c (FunDef f)
    | None => False
    end.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflect c (FunDef f)
    | None => False
    end.

  Definition ValidContractWithFuel {Δ τ} (fuel : nat) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => ValidContractReflectWithFuel fuel c (FunDef f)
    | None => False
    end.

  Ltac symbolic_simpl :=
    apply validcontract_with_erasure_sound;
    vm_compute;
    constructor;
    cbn.

  Lemma valid_execute_rX : ValidContract rX.
  Proof.
    now vm_compute.
  Qed.

  Lemma valid_execute_wX : ValidContract wX.
  Proof. now vm_compute. Qed.

  (* Import SymProp.notations. *)
  (* Set Printing Depth 200. *)
  (* Eval vm_compute in (postprocess (RiscvPmpCFGVerifExecutor.SHeapSpecM.vcgen RiscvPmpCFGVerifExecutor.default_config 1 *)
  (*            sep_contract_fetch_instr (FunDef fetch))). *)

  Lemma valid_execute_fetch : ValidContract fetch.
  Proof. now vm_compute. Qed.

  (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
  (* Proof. compute. Admitted. *)

  Lemma valid_execute_tick_pc : ValidContract tick_pc.
  Proof. now vm_compute. Qed.


  Import RiscvPmpCFGVerifExecutor.

  (* Definition test := (postprocess *)
  (*                       (SPureSpec.replay *)
  (*                          (postprocess (RiscvPmpCFGVerifExecutor.vcgen RiscvPmpCFGVerifExecutor.default_config 1 sep_contract_read fun_checked_read wnil)))). *)
  Import SymProp.notations.
  (* Eval vm_compute in test. *)

  Lemma valid_checked_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_read bytes H).
  Proof. destruct H; now vm_compute. Qed.

  Lemma valid_checked_mem_write {bytes} {H : restrict_bytes bytes} : ValidContract (@checked_mem_write bytes H).
  Proof. destruct H; now vm_compute. Qed.

  (* Lemma valid_pmp_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_read bytes H). *)
  (* Proof. destruct H; now vm_compute. Qed. *)

  (* Lemma valid_pmp_mem_write {bytes} {H : restrict_bytes bytes} : ValidContract (@pmp_mem_write bytes H). *)
  (* Proof. destruct H; now vm_compute. Qed. *)

  Import Bitvector.bv.notations.

  (* Lemma valid_pmpMatchAddr : ValidContractDebug pmpMatchAddr. *)
  (* Proof. *)
  (*   symbolic_simpl. *)
  (*   intros; split; intros; bv_comp; auto. *)
  (*   destruct (v + v0 <=ᵘ? v1)%bv eqn:?; bv_comp; auto. *)
  (* Qed. *)

  (* Lemma valid_pmpCheck {bytes : nat} {H : restrict_bytes bytes} : ValidContractWithFuelDebug 4 (@pmpCheck bytes H). *)
  (* Proof. *)
  (*   destruct H; apply verification_condition_with_erasure_sound; vm_compute; *)
  (*     constructor; cbn; *)
  (*     repeat (intros; split; intros); *)
  (*     repeat match goal with *)
  (*       | H: (?b1 || ?b2)%bool = true |- _ => *)
  (*           apply Bool.orb_true_iff in H *)
  (*       | H: ?P /\ ?Q |- _ => *)
  (*           destruct H *)
  (*       | H: ?P \/ ?Q |- _ => *)
  (*           destruct H as [H|H] *)
  (*       | H: negb ?b = true |- _ => *)
  (*           apply Bool.negb_true_iff in H; *)
  (*           subst *)
  (*       | H1: ?a <=ᵘ ?b, H2: ?b <ᵘ ?a |- False => *)
  (*           unfold bv.ult, bv.ule in *; apply N.le_ngt in H1; apply (H1 H2) *)
  (*       end; *)
  (*     subst; *)
  (*     unfold Pmp_check_perms, decide_pmp_check_perms, pmp_check_RWX in *; *)
  (*     simpl in *; *)
  (*     try discriminate; *)
  (*     try Lia.lia. *)
  (* Qed. *)

  Lemma valid_mem_read {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof. destruct H; now vm_compute. Qed.

  Lemma valid_mem_write_value {bytes} {H : restrict_bytes bytes} : ValidContract (@mem_write_value bytes H).
  Proof. destruct H; now vm_compute. Qed.

  Lemma valid_contract_within_phys_mem : ValidContractDebug within_phys_mem.
  Proof. symbolic_simpl. intros. Lia.lia. Qed.

  Lemma valid_contract_execute_EBREAK : ValidContractDebug execute_EBREAK.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      RiscvPmpCFGVerifSpec.CEnv f = Some c ->
      ValidContract f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract_with_fuel_debug : forall {Δ τ} (fuel : nat) (f : Fun Δ τ) (c : SepContract Δ τ),
      RiscvPmpCFGVerifSpec.CEnv f = Some c ->
      ValidContractWithFuelDebug fuel f ->
      Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? fuel f c Hcenv Hvc.
    unfold ValidContractWithFuelDebug in Hvc.
    now rewrite Hcenv in Hvc.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    now rewrite Hcenv in Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros.
    destruct f; try discriminate H; eexists.
    - refine (valid_contract _ H valid_execute_rX).
    - refine (valid_contract _ H valid_execute_wX).
    - refine (valid_contract _ H valid_execute_tick_pc).
    - refine (valid_contract_debug _ H valid_contract_within_phys_mem).
    - refine (valid_contract _ H valid_mem_read).
    - refine (valid_contract _ H valid_checked_mem_read).
    - refine (valid_contract _ H valid_checked_mem_write).
    (* - refine (valid_contract _ H valid_pmp_mem_read). *)
    (* - refine (valid_contract _ H valid_pmp_mem_write). *)
    (* - refine (valid_contract_with_fuel_debug _ _ H valid_pmpCheck). *)
    (* - refine (valid_contract_debug _ H valid_pmpMatchAddr). *)
    - refine (valid_contract _ H valid_mem_write_value).
    - refine (valid_contract _ H valid_execute_fetch).
    - refine (valid_contract_debug _ H valid_contract_execute_EBREAK).
  Qed.
End RiscvPmpSpecVerif.
