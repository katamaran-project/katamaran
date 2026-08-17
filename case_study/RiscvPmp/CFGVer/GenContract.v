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
(* GenContract.v — the contract GENERATOR.                                   *)
(*                                                                           *)
(* Builds CFGVerifierContracts from reg_spec / mem_full_spec lists           *)
(* (gen_contract), their constant-value parametric-base variant              *)
(* (gen_contract_param), and the base-RELATIVE variant (gen_contract_rel     *)
(* over param_val / reg_spec_rel / mem_spec_rel), plus the concretize maps   *)
(* that send _rel specs to ordinary specs at a concrete base.  Pure          *)
(* assertion-level machinery: nothing here is part of the trusted            *)
(* end-to-end statements.                                                    *)
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
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts.

From iris.proofmode Require string_ident tactics.

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
Import asn.notations.

    (* ------------------------------------------------------------------ *)
    (* Contract generator                                                   *)
    (*                                                                      *)
    (* reg_spec: (register, is_public, optional_init_value)                 *)
    (*   is_public = true  → secLeak assertion added (register is SyncVal) *)
    (*   optional_init_value = Some v → register holds concrete value v    *)
    (*                        = None  → register holds an existential       *)
    (*                                                                      *)
    (* mem_full_spec: (address, is_public, optional_init_value)             *)
    (*   is_public = true  → memory word at address is same in both worlds  *)
    (*   optional_init_value = Some v → memory word holds concrete value v  *)
    (*                        = None  → memory word holds an existential     *)
    (* ------------------------------------------------------------------ *)

    Definition gen_reg_asn {Σ} (s : reg_spec) : Assertion Σ :=
      let '(r, is_pub, opt_v) := s in
      match opt_v with
      | Some v => r ↦ᵣ term_val ty_xlenbits v
      | None =>
        asn.exist "v" ty_xlenbits
          (if is_pub
           then r ↦ᵣ term_var "v" ∗ secLeakvar "v"
           else r ↦ᵣ term_var "v")
      end.

    Definition gen_pre {Σ} (specs : list reg_spec) : Assertion Σ :=
      List.fold_right (fun s acc => gen_reg_asn s ∗ acc) ⊤ specs.

    Definition gen_mem_asn {Σ} (s : mem_full_spec) : Assertion Σ :=
      let '(a, is_pub, opt_v) := s in
      match opt_v with
      | Some v => term_val ty_xlenbits a ↦ₘ term_val ty_xlenbits v
      | None =>
        asn.exist "mv" ty_xlenbits
          (if is_pub then term_val ty_xlenbits a ↦ₘ term_var "mv" ∗ secLeakvar "mv"
                     else term_val ty_xlenbits a ↦ₘ term_var "mv")
      end.

    Definition gen_mem_pre {Σ} (specs : list mem_full_spec) : Assertion Σ :=
      List.fold_right (fun s acc => gen_mem_asn s ∗ acc) ⊤ specs.

    (* ------------------------------------------------------------------ *)
    (* BYTE-GRANULAR data cells (PLAN-byte-memory.md).                     *)
    (*                                                                      *)
    (* A `lbu`/`sb` program consumes `ptstomem 1` chunks, but the width is  *)
    (* part of the predicate INDEX (Sig.v:365), so a resident `ptstomem 4`  *)
    (* chunk cannot discharge a consume of `ptstomem 1` -- the symbolic     *)
    (* chunk matcher has no split rule.  The builders below hand out FOUR   *)
    (* one-byte chunks per spec entry instead of one word chunk.            *)
    (*                                                                      *)
    (* The DECLARATION UNIT STAYS A WORD: a byte-expanded entry still       *)
    (* describes the 4 bytes at a word-aligned address, so stride stays 4   *)
    (* and the trusted statement layer (mem_full_spec, gen_init_mem,        *)
    (* gen_public_addrs, declare_*, HDataAddrs) is untouched.  Only the     *)
    (* chunk count changes (1 -> 4 per entry).                              *)
    (*                                                                      *)
    (* BYTE ORDER is little-endian, lowest address first, and all three of  *)
    (* these must agree:                                                    *)
    (*   get_word         (Noninterference.v:139) = app b(a) (app b(a+1) ...) *)
    (*   interp_ptstomem  (IrisInstance.v:206)    peels bv.appView byte _,   *)
    (*                                            putting the LOW part at addr *)
    (*   word_byte j      (below)                 = vector_subrange (8*j) 8   *)
    (* and `bv.app xs ys` places `xs` in the LOW bits (Bitvector.v:443,535), *)
    (* while `vector_subrange s l = drop s (take (s+l) _)` (Bitvector.v:1001) *)
    (* -- so j = 0 is the byte at the LOWEST address.  Get this wrong and the *)
    (* Iris wiring in EndToEnd.v will not close.                             *)
    (* ------------------------------------------------------------------ *)

    (* Byte j of a 32-bit VALUE, j = 0 being the byte at the lowest address.
       The four offsets are spelled out as LITERALS rather than computed as
       8*j: vector_subrange's size side-condition is an IsTrue whose Hint
       Extern only fires once the boolean is convertible to `true`
       (Prelude.v:296), which a symbolic j never is. *)
    Definition word_byte (j : nat) (v : Val ty_xlenbits) : Val (ty_bytes 1) :=
      match j with
      | 0   => bv.vector_subrange 0 8 v
      | 1   => bv.vector_subrange 8 8 v
      | 2   => bv.vector_subrange 16 8 v
      | _   => bv.vector_subrange 24 8 v
      end.

    (* BYTE-ORDER REGRESSION ANCHOR.  These pin the convention down by
       computation, because a silent flip here would not surface until the
       Iris wiring in EndToEnd.v (PLAN-byte-memory.md §5.3) failed to close,
       far from the cause.  0xAABBCCDD: byte 0 is the LOW byte 0xDD, and it is
       the one at the LOWEST address -- because get_word
       (Noninterference.v:139) puts `ram a` FIRST in the bv.app nest and
       bv.app's first argument is the low half (Bitvector.v:443,535). *)
    Goal word_byte 0 (bv.of_N 0xAABBCCDD) = bv.of_N 0xDD. vm_compute. reflexivity. Qed.
    Goal word_byte 1 (bv.of_N 0xAABBCCDD) = bv.of_N 0xCC. vm_compute. reflexivity. Qed.
    Goal word_byte 2 (bv.of_N 0xAABBCCDD) = bv.of_N 0xBB. vm_compute. reflexivity. Qed.
    Goal word_byte 3 (bv.of_N 0xAABBCCDD) = bv.of_N 0xAA. vm_compute. reflexivity. Qed.
    (* ... and that they reassemble in ADDRESS order under bv.app, i.e. in
       exactly the shape get_word produces. *)
    Goal bv.app (@bv.of_N 8 0xDD) (bv.app (@bv.of_N 8 0xCC)
           (bv.app (@bv.of_N 8 0xBB) (bv.app (@bv.of_N 8 0xAA) bv.nil)))
         = @bv.of_N 32 0xAABBCCDD.
    Proof. vm_compute. reflexivity. Qed.

    (* Byte j of a 32-bit TERM, same convention and same literal-offset
       reason.  Used for PVBaseOff, where the word is symbolic (p + k) and
       cannot be split at definition time. *)
    Definition term_word_byte {Σ} (j : nat) (t : Term Σ ty_xlenbits)
        : Term Σ (ty_bytes 1) :=
      match j with
      | 0   => term_unop (uop.vector_subrange 0 8) t
      | 1   => term_unop (uop.vector_subrange 8 8) t
      | 2   => term_unop (uop.vector_subrange 16 8) t
      | _   => term_unop (uop.vector_subrange 24 8) t
      end.

    (* The four one-byte chunks of a word, given a function from byte offset to
       the chunk's ADDRESS TERM and the four byte terms.
       Written with chunk_user directly rather than a notation: the
       width-parameterised `↦ₘ[ bytes ]` is Local to Spec.v:229, and the
       ambient `↦ₘ` (Contracts.v:461) is hardcoded to bytes_per_word -- using
       it here would silently reintroduce a word-width chunk.

       `addr_of` is a FUNCTION rather than a base term plus an added offset so
       each caller can emit the address in the executor's CANONICAL form:
       `term_val <literal>` at a concrete base, `p + <literal>` at a symbolic
       one.  Building `(p + k) + j` instead would leave a nested bvadd that
       the load's computed address (`p + (k+j)` after peval folding) need not
       match, and only the j = 0 chunk -- where the offset folds away -- would
       ever be consumable. *)
    Definition byte_chunks {Σ} (addr_of : N -> Term Σ ty_xlenbits)
        (b0 b1 b2 b3 : Term Σ (ty_bytes 1)) : Assertion Σ :=
      asn.chunk (chunk_user (@ptstomem 1) [addr_of 0%N; b0]) ∗
      asn.chunk (chunk_user (@ptstomem 1) [addr_of 1%N; b1]) ∗
      asn.chunk (chunk_user (@ptstomem 1) [addr_of 2%N; b2]) ∗
      asn.chunk (chunk_user (@ptstomem 1) [addr_of 3%N; b3]).

    (* Concrete-base byte address: a single literal, folded at definition time. *)
    Definition byte_addr_val {Σ} (a : Val ty_xlenbits) (j : N)
        : Term Σ ty_xlenbits :=
      term_val ty_xlenbits (bv.add a (bv.of_N j)).

    (* Byte-expanded reading of ONE mem_full_spec (concrete-base family). *)
    Definition gen_mem_asn_bytes {Σ} (s : mem_full_spec) : Assertion Σ :=
      let '(a, is_pub, opt_v) := s in
      match opt_v with
      | Some v =>
          (* pinned: split the literal word into four literal bytes *)
          byte_chunks (byte_addr_val a)
            (term_val (ty_bytes 1) (word_byte 0 v))
            (term_val (ty_bytes 1) (word_byte 1 v))
            (term_val (ty_bytes 1) (word_byte 2 v))
            (term_val (ty_bytes 1) (word_byte 3 v))
      | None =>
          (* existential: ONE word variable, each chunk a byte projection of it.
             Equally general (word <-> its four bytes is a bijection) but it
             costs ONE logic variable per entry instead of four.  MEASURED: at
             N = 32, four-independent-byte-variables costs +43% vm_compute and
             +56% Qed, and turns a VC doubling-slope of 1.02 into 1.39 --
             |Σ| feeds the Sub/Valuation transported at every world extension,
             so variable count is a first-order cost, not a rounding error.
             An earlier version of this used four bare byte variables on the
             theory that bare variables are the smallest terms the executor can
             carry; that optimises chunk-value size while inflating Σ, and Σ is
             what gets transported.  See PLAN-byte-memory.md §10.
             Bonus: `secLeakvar` on the WORD is exactly what the Iris side
             offers for a public entry (interp_mem_with_public_memory hands out
             a SyncVal word), removing §7's public-existential caveat. *)
          asn.exist "mw" ty_xlenbits
            (byte_chunks (byte_addr_val a)
               (term_word_byte 0 (term_var "mw"))
               (term_word_byte 1 (term_var "mw"))
               (term_word_byte 2 (term_var "mw"))
               (term_word_byte 3 (term_var "mw"))
             ∗ (if is_pub then secLeakvar "mw" else ⊤))
      end.

    Definition gen_mem_pre_bytes {Σ} (specs : list mem_full_spec) : Assertion Σ :=
      List.fold_right (fun s acc => gen_mem_asn_bytes s ∗ acc) ⊤ specs.

    (* extra_exit_offs: base-relative byte offsets of exit addresses BEYOND
       the fall-through one (which is always included).  Needed when control
       flow can leave the program other than by falling off the end, e.g. a
       branch whose taken target lies past the program (jump_if_zero). *)
    Definition gen_contract
        (init_addr : N)
        (reg_specs : list reg_spec)
        (mem_specs : list mem_full_spec)
        (instrs : list AST)
        (extra_exit_offs : list N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : CFGVerifierContract :=
      @MkCFGVerifierContract [ctx] init_addr
        (term_val ty_xlenbits (bv.of_N init_addr))
        (exits_of_offs (term_val ty_xlenbits (bv.of_N init_addr))
           ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
        (asn_init_pc (bv.of_N init_addr) ∗ gen_pre reg_specs ∗ gen_mem_pre mem_specs)
        instrs ec fl.

    (* ================================================================ *)
    (* PARAMETRIC-BASE SUPPORT — READING GUIDE (Examples.v side).        *)
    (*                                                                    *)
    (* Goal: prove noninterference for a program loaded at an ARBITRARY   *)
    (* base address, from ONE symbolic-base VC (proved once), rather than *)
    (* re-running vm_compute per concrete base.                           *)
    (*                                                                    *)
    (* Two facts make it work:                                            *)
    (*  - The symbolic VC (Valid_CFG_VC, ~line 350) runs the TERM-TABLE   *)
    (*    executor (Verifier.scfg_verification_condition) over       *)
    (*    `table_of_list p 0 i`, so the base placement term `p` may be a  *)
    (*    genuine VARIABLE.  The base must be `term_var "p"`, NOT          *)
    (*    `term_val (bv.of_N n)`: the latter makes vm_compute DIVERGE      *)
    (*    (bv.of_N of a symbolic N at width 32 does not reduce).           *)
    (*  - The end-to-end/memory side is tied to the term table by         *)
    (*    FAITHFULNESS at the concrete valuation ι = [p ↦ of_N init_addr]. *)
    (*                                                                    *)
    (* Read in this order:                                                *)
    (*   • exits_of_offs / asn_pc_eq (above, ~176/619) — build the exit    *)
    (*     term set `p ⊕ off` and the entry-pc assertion `pc = p`.        *)
    (*   • itable_faith_of_list / etable_faith_exits_of_offs (~230/265) — *)
    (*     discharge the Verifier.v faithfulness guards at ι.             *)
    (*   • gen_contract_param (just below) — parametric contract for       *)
    (*     CONSTANT-valued specs (base bound added to the precondition).  *)
    (*   • param_val / reg_spec_rel / mem_spec_rel + gen_*_asn_rel        *)
    (*     (Stage 2 section below) — base-RELATIVE specs (PVBaseOff k = p+k),*)
    (*     needed for cmovznz4's data pointers p+116/132/148.             *)
    (*   • gen_contract_rel — the contract built from _rel specs.          *)
    (*   • concretize_reg/_mem + gen_pre_rel_concretize /                 *)
    (*     gen_mem_pre_rel_concretize (outside the section, ~line 3333) — *)
    (*     THE KEY TRICK: interpreting the symbolic _rel precondition at   *)
    (*     ι equals interpreting gen_pre/gen_mem_pre of the specs          *)
    (*     concretized at init_addr, so we REUSE gen_implpre unchanged     *)
    (*     instead of re-proving a 130-line Iris induction.               *)
    (*   • gen_contract_noninterferent_rel — the base-relative bridge.     *)
    (*   • cmovznz4_noninterferent_param — the headline; the base-0 and    *)
    (*     base-256 concrete lemmas are corollaries of it.                *)
    (* NOTE (axiom hygiene): the concretize lemmas avoid                  *)
    (* functional_extensionality (an axiom here) — see their proofs.      *)
    (* ================================================================ *)

    (* Parameterized-base analog of gen_contract (PLAN-symbolic-base.md Phase 4.2).
       The base is a genuine term VARIABLE term_var "p" (Σ = ["p"∷ty_xlenbits]),
       NOT term_val (bv.of_N init_addr) — the latter makes the VC's vm_compute
       diverge on bv.of_N of a symbolic N at width 32.  cfg_init_addr / cfg_exitCond
       are still stored (the end-to-end/memory side needs them) but are ignored by
       Valid_CFG_VC, so the VC is proved ONCE, uniformly in init_addr, and reused
       for every concrete base via the ι = ["p" ↦ SyncVal (bv.of_N init_addr)]
       instantiation in gen_contract_noninterferent_param.

       Two deltas from gen_contract's precondition: the entry-pc assertion is
       asn_pc_eq (term_var "p") (pc starts at the symbolic base) rather than
       asn_init_pc (bv.of_N init_addr); and a base BOUND
       unsigned p + 4·len ≤ lenAddr is added so the instruction-fetch upper
       bounds are dischargeable (the `(bound)` premise the noninterference
       theorem carries down to it). *)
    Definition gen_contract_param
        (init_addr : N)
        (reg_specs : list reg_spec)
        (mem_specs : list mem_full_spec)
        (instrs : list AST)
        (extra_exit_offs : list N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      @MkCFGVerifierContract ["p" :: ty_xlenbits] init_addr
        (term_var "p")
        (exits_of_offs (term_var "p")
           ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
        (asn_pc_eq (term_var "p")
           ∗ asn.formula (formula_relop bop.le
                (term_binop bop.plus (term_unop uop.unsigned (term_var "p"))
                   (term_val ty.int (Z.of_N (4 * N.of_nat (length instrs)))))
                (term_val ty.int (Z.of_N lenAddr)))
           ∗ gen_pre reg_specs ∗ gen_mem_pre mem_specs)
        instrs ec fl.

    (* ------------------------------------------------------------------ *)
    (* Stage 2: base-RELATIVE parametric-value specs.  Unlike reg_spec /   *)
    (* mem_full_spec (constant Val), the register init value and memory     *)
    (* address here may depend on the symbolic base p (PVBaseOff k = p+k).  *)
    (* This is what cmovznz4 needs — data pointers p+116/132/148 and data   *)
    (* words at p+116..p+160 — and cannot be expressed with gen_contract_   *)
    (* param's constant term_val values (of_N (init_addr+k) would also make *)
    (* vm_compute diverge).  A concretize map (below, outside the section)  *)
    (* sends these to ordinary reg_spec/mem_full_spec at ι=[p↦of_N ia], so  *)
    (* the noninterference bridge reuses gen_implpre / gen_implpre_mem.     *)
    Inductive param_val : Type :=
    | PVExist                          (* existential (private/public per is_pub) *)
    | PVConst (v : Val ty_xlenbits)    (* base-independent constant *)
    | PVBaseOff (k : N).               (* base p + k *)

    Definition reg_spec_rel : Type := RegIdx * bool * param_val.
    Definition mem_spec_rel : Type := N * bool * param_val.   (* address = p + k *)

    Definition gen_reg_asn_rel (s : reg_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      let '(r, is_pub, pv) := s in
      match pv with
      | PVExist =>
          asn.exist "v" ty_xlenbits
            (if is_pub then r ↦ᵣ term_var "v" ∗ secLeakvar "v" else r ↦ᵣ term_var "v")
      | PVConst v => r ↦ᵣ term_val ty_xlenbits v
      | PVBaseOff k =>
          r ↦ᵣ term_binop bop.bvadd (term_var "p") (term_val ty_xlenbits (bv.of_N k))
      end.

    Definition gen_pre_rel (specs : list reg_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      List.fold_right (fun s acc => gen_reg_asn_rel s ∗ acc) ⊤ specs.

    Definition gen_mem_asn_rel (s : mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      let '(k, is_pub, pv) := s in
      let addr := term_binop bop.bvadd (term_var "p") (term_val ty_xlenbits (bv.of_N k)) in
      match pv with
      | PVExist =>
          asn.exist "mv" ty_xlenbits
            (if is_pub
             then term_binop bop.bvadd (term_var "p") (term_val ty_xlenbits (bv.of_N k)) ↦ₘ term_var "mv" ∗ secLeakvar "mv"
             else term_binop bop.bvadd (term_var "p") (term_val ty_xlenbits (bv.of_N k)) ↦ₘ term_var "mv")
      | PVConst v => addr ↦ₘ term_val ty_xlenbits v
      | PVBaseOff k2 =>
          addr ↦ₘ term_binop bop.bvadd (term_var "p") (term_val ty_xlenbits (bv.of_N k2))
      end.

    Definition gen_mem_pre_rel (specs : list mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      List.fold_right (fun s acc => gen_mem_asn_rel s ∗ acc) ⊤ specs.

    (* Base-relative byte address, in the canonical `p + <literal>` form: the
       offset k+j is folded into ONE literal rather than left as (p+k)+j.
       `pterm` is passed in rather than written as term_var "p" here because the
       caller's Σ differs between the outer level and the inside of the four
       asn.exist binders below. *)
    Definition byte_addr_rel {Σ} (pterm : Term Σ ty_xlenbits) (k : N) (j : N)
        : Term Σ ty_xlenbits :=
      term_binop bop.bvadd pterm (term_val ty_xlenbits (bv.of_N (k + j))).

    (* Byte-expanded reading of ONE mem_spec_rel (base-relative family).
       Same contract as gen_mem_asn_rel -- address p+k, declaration unit a
       word -- but hands out four ptstomem 1 chunks at p+k .. p+k+3.
       See the byte-order note at gen_mem_asn_bytes above. *)
    Definition gen_mem_asn_rel_bytes (s : mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      let '(k, is_pub, pv) := s in
      match pv with
      | PVConst v =>
          byte_chunks (byte_addr_rel (term_var "p") k)
            (term_val (ty_bytes 1) (word_byte 0 v))
            (term_val (ty_bytes 1) (word_byte 1 v))
            (term_val (ty_bytes 1) (word_byte 2 v))
            (term_val (ty_bytes 1) (word_byte 3 v))
      | PVBaseOff k2 =>
          (* UNTESTED path: the stored word is the symbolic address p+k2, so
             its bytes stay symbolic subranges.  check_scalar does not need
             this (its arrays are PVExist/PVConst); kept only for uniformity.
             A wrong reading here can never be unsound -- it can only make the
             VC or the ImplPre unprovable. *)
          let w := term_binop bop.bvadd (term_var "p") (term_val ty_xlenbits (bv.of_N k2)) in
          byte_chunks (byte_addr_rel (term_var "p") k)
            (term_word_byte 0 w) (term_word_byte 1 w)
            (term_word_byte 2 w) (term_word_byte 3 w)
      | PVExist =>
          (* ONE word variable per entry, not four byte ones — see the measured
             justification at gen_mem_asn_bytes above. *)
          asn.exist "mw" ty_xlenbits
            (byte_chunks (byte_addr_rel (term_var "p") k)
               (term_word_byte 0 (term_var "mw"))
               (term_word_byte 1 (term_var "mw"))
               (term_word_byte 2 (term_var "mw"))
               (term_word_byte 3 (term_var "mw"))
             ∗ (if is_pub then secLeakvar "mw" else ⊤))
      end.

    Definition gen_mem_pre_rel_bytes (specs : list mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      List.fold_right (fun s acc => gen_mem_asn_rel_bytes s ∗ acc) ⊤ specs.

    (* bound: an N ≥ (max accessed byte offset)+4, so the fetch/access upper
       bounds are dischargeable from unsigned p + bound ≤ lenAddr. *)
    Definition gen_contract_rel
        (init_addr : N)
        (reg_specs : list reg_spec_rel)
        (mem_specs : list mem_spec_rel)
        (instrs : list AST)
        (extra_exit_offs : list N)
        (bound : N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      @MkCFGVerifierContract ["p" :: ty_xlenbits] init_addr
        (term_var "p")
        (exits_of_offs (term_var "p")
           ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
        ( asn_pc_eq (term_var "p")
          ∗ asn.formula (formula_relop bop.le
               (term_binop bop.plus (term_unop uop.unsigned (term_var "p"))
                  (term_val ty.int (Z.of_N bound)))
               (term_val ty.int (Z.of_N lenAddr)))
          ∗ gen_pre_rel reg_specs ∗ gen_mem_pre_rel mem_specs )
        instrs ec fl.

    (* gen_contract_rel with an ADDITIONAL, byte-expanded data list
       (PLAN-byte-memory.md §5.2).  Byte expansion is opt-in PER SPEC ENTRY so
       the 4x chunk multiplier is paid only where a `lbu`/`sb` actually needs
       it: `mem_specs` entries get one ptstomem 4 chunk as before,
       `byte_mem_specs` entries get four ptstomem 1 chunks.

       On the trusted side the two lists are simply CONCATENATED
       (mem_specs ++ byte_mem_specs) -- same type, stride still 4 -- so
       HDataAddrs's contiguous layout is unchanged.  Keep mem_specs first and
       both blocks contiguous.

       gen_contract_rel itself is deliberately left byte-identical rather than
       refactored to delegate here: nine vm_compute VC proofs reduce through
       it, so the duplication is cheaper than the perturbation. *)
    Definition gen_contract_rel_bytes
        (init_addr : N)
        (reg_specs : list reg_spec_rel)
        (mem_specs : list mem_spec_rel)
        (byte_mem_specs : list mem_spec_rel)
        (instrs : list AST)
        (extra_exit_offs : list N)
        (bound : N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      @MkCFGVerifierContract ["p" :: ty_xlenbits] init_addr
        (term_var "p")
        (exits_of_offs (term_var "p")
           ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
        ( asn_pc_eq (term_var "p")
          ∗ asn.formula (formula_relop bop.le
               (term_binop bop.plus (term_unop uop.unsigned (term_var "p"))
                  (term_val ty.int (Z.of_N bound)))
               (term_val ty.int (Z.of_N lenAddr)))
          ∗ gen_pre_rel reg_specs ∗ gen_mem_pre_rel mem_specs
          ∗ gen_mem_pre_rel_bytes byte_mem_specs )
        instrs ec fl.

  (* ================================================================== *)
  (* Stage 2: base-RELATIVE noninterference bridge (gen_contract_rel).    *)
  (* Sends the base-relative param specs to ordinary reg_spec /           *)
  (* mem_full_spec at the concrete base ia via concretize_*, so the       *)
  (* interpretation of the symbolic precondition (gen_pre_rel /           *)
  (* gen_mem_pre_rel) matches gen_pre / gen_mem_pre of the concretized     *)
  (* specs (concretize lemmas below) — letting us REUSE gen_implpre /      *)
  (* gen_implpre_mem unchanged.                                            *)
  (* ================================================================== *)

  Definition concretize_reg (ia : N) (s : reg_spec_rel) : reg_spec :=
    let '(r, pub, pv) := s in
    (r, pub, match pv with
             | PVExist => None
             | PVConst v => Some v
             | PVBaseOff k => Some (bv.of_N (ia + k))
             end).

  Definition concretize_mem (ia : N) (s : mem_spec_rel) : mem_full_spec :=
    let '(k, pub, pv) := s in
    (bv.of_N (ia + k), pub,
     match pv with
     | PVExist => None
     | PVConst v => Some v
     | PVBaseOff k2 => Some (bv.of_N (ia + k2))
     end).
