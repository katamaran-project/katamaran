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
        (instrs : list AnnotInstr)
        (extra_exit_offs : list N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : CFGVerifierContract :=
      @MkCFGVerifierContract [ctx] init_addr
        (term_val ty_xlenbits (bv.of_N init_addr))
        (exits_of_offs (term_val ty_xlenbits (bv.of_N init_addr))
           ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
        (asn_init_pc (bv.of_N init_addr) ∗ gen_pre reg_specs ∗ gen_mem_pre mem_specs)
        instrs ec fl asn_no_post.

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

    (* gen_contract_param is defined further down, after the base-relative
       builders it now delegates to (PLAN-unify-generators.md stage 1). *)

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

    (* A constant-value register spec is exactly the base-INDEPENDENT special
       case of a base-relative one: an absent value is the existential class, a
       present one a base-independent constant.  Nothing maps to PVBaseOff, which
       is the whole point -- reg_spec cannot express a base-dependent value.
       This is what lets gen_contract_param delegate to gen_contract_rel_classed
       (PLAN-unify-generators.md stage 1); it is a bijection onto the
       PVBaseOff-free subset, inverted by concretize_reg at any base
       (concretize_reg_to_rel below). *)
    Definition reg_spec_to_rel (s : reg_spec) : reg_spec_rel :=
      let '(r, is_pub, ov) := s in
      (r, is_pub, match ov with
                  | None => PVExist
                  | Some v => PVConst v
                  end).

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

    (* ------------------------------------------------------------------ *)
    (* ONE EXISTENTIAL PER PUBLICNESS CLASS (2026-08-18).                   *)
    (*                                                                      *)
    (* gen_mem_pre_rel emits one `asn.exist` per PVExist entry, so |Sigma|  *)
    (* grows with the declared cell count.  That is the dominant cost       *)
    (* driver: measured QUADRATIC in |Sigma| and ~30-46x more expensive per *)
    (* unit than a chunk, against a chunk axis that is exactly linear       *)
    (* (diagnostics/check-scalar-combined-cost-drivers.md §6.6,             *)
    (* key-schedule-loop2-cost-drivers.md final sections).                  *)
    (*                                                                      *)
    (* This builder emits ONE existential per publicness class instead: an  *)
    (* N-cell class becomes a single `bv (xlenbits * N)` variable whose      *)
    (* cells are successive `bvtake`/`bvdrop` slices.  EQUIVALENT, not       *)
    (* weaker -- N independent words are in bijection with one N-word       *)
    (* vector -- so unlike PVConst-pinning it costs nothing in generality.  *)
    (* Measured 3.49x at N=32 on key_schedule_loop's shape, within 0.16% of *)
    (* the (weaker) shared-variable arm.                                    *)
    (*                                                                      *)
    (* Same trick gen_mem_asn_bytes already uses for the four bytes of one  *)
    (* word (PLAN-byte-memory.md §10 driver (C)), one level up.             *)
    (*                                                                      *)
    (* WHY THE WIDTH IS COMPUTED FROM THE LIST: uop.vector_subrange carries *)
    (* an implicit `IsTrue (s + l <=? n)` that Prelude.v:297's Hint Extern   *)
    (* discharges only for LITERAL offsets, so a fold over a runtime list    *)
    (* cannot use it.  uop.bvtake/bvdrop have NO side condition -- they are *)
    (* typed on `m + n` -- and `mem_class_width (cons s r)` is              *)
    (* DEFINITIONALLY `xlenbits + mem_class_width r`, so the slices          *)
    (* typecheck with zero proof obligations.                               *)
    (* ------------------------------------------------------------------ *)
    (* Generic in the KEY type so ONE cells builder -- and hence ONE ImplPre
       induction -- serves both the base-relative family (keys are offsets `k`,
       addresses `p + k`) and the concrete family (keys are literal addresses).
       Indexing the width by the KEY LIST rather than by a list of address
       TERMS is deliberate: `length (map f specs) = length specs` is only
       propositional, so a term-list index does not typecheck against a width
       computed from the spec list. *)
    Fixpoint mem_class_width {K} (ks : list K) : nat :=
      match ks with
      | nil      => 0
      | cons _ r => xlenbits + mem_class_width r
      end.

    (* Cells of ONE class, peeling xlenbits bits off the class variable per
       entry.  `addr_of` is a function for the same reason byte_chunks takes
       one: the caller's Σ differs inside the asn.exist binder. *)
    Fixpoint gen_mem_cells_class {Σ} {K} (ks : list K)
        (addr_of : K -> Term Σ ty_xlenbits)
        (mw : Term Σ (ty.bvec (mem_class_width ks))) : Assertion Σ :=
      match ks return Term Σ (ty.bvec (mem_class_width ks)) -> Assertion Σ with
      | nil      => fun _ => ⊤
      | cons k r => fun mw =>
          (addr_of k ↦ₘ term_unop (uop.bvtake xlenbits) mw)
          ∗ gen_mem_cells_class r addr_of (term_unop (uop.bvdrop xlenbits) mw)
      end mw.

    (* Classification, on both spec forms.  concretize_mem maps PVExist to
       None and preserves the publicness bit, so these two agree under it --
       which is what lets the classed concretize lemma commute the filters
       with the map. *)
    Definition mem_spec_is_exist (s : mem_spec_rel) : bool :=
      let '(_, _, pv) := s in match pv with PVExist => true | _ => false end.
    Definition mem_spec_is_pub (s : mem_spec_rel) : bool :=
      let '(_, b, _) := s in b.
    (* The mem_full_spec classifiers are for the ImplPre bridge, which has to
       partition the CONCRETE resource list by the same classes; nothing in the
       symbolic precondition uses them. *)
    Definition mem_full_is_exist (s : mem_full_spec) : bool :=
      let '(_, _, ov) := s in match ov with None => true | _ => false end.
    Definition mem_full_is_pub (s : mem_full_spec) : bool :=
      let '(_, b, _) := s in b.

    Definition mem_rel_keys (specs : list mem_spec_rel) : list N :=
      List.map (fun s => let '(k, _, _) := s in k) specs.
    Definition mem_full_keys (specs : list mem_full_spec) : list (Val ty_xlenbits) :=
      List.map (fun s => let '(a, _, _) := s in a) specs.

    (* Empty classes emit NOTHING -- an `asn.exist` of width 0 would cost a
       logic variable for no cells, which is exactly what this builder exists
       to avoid.  The classes are separate definitions rather than one
       parameterized by a name because `secLeakvar` needs a literal. *)
    (* Stated at the KEYS level, with a thin specs-level wrapper below.  This
       split is not cosmetic: the ImplPre bridge must `destruct` the key list to
       handle the empty class, and `destruct (mem_rel_keys specs)` fails with
       "Conclusion depends on the bodies of ..." because the existential's type
       mentions `mem_class_width (mem_rel_keys specs)`.  With the keys as a
       plain variable the destruct is trivial. *)
    Definition gen_mem_pub_class_ks (ks : list N)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      match ks with
      | nil => ⊤
      | _   =>
          asn.exist "mwpub" (ty.bvec (mem_class_width ks))
            (gen_mem_cells_class ks
               (fun k => term_binop bop.bvadd (term_var "p")
                           (term_val ty_xlenbits (bv.of_N k)))
               (term_var "mwpub")
             ∗ secLeakvar "mwpub")
      end.

    Definition gen_mem_priv_class_ks (ks : list N)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      match ks with
      | nil => ⊤
      | _   =>
          asn.exist "mwpriv" (ty.bvec (mem_class_width ks))
            (gen_mem_cells_class ks
               (fun k => term_binop bop.bvadd (term_var "p")
                           (term_val ty_xlenbits (bv.of_N k)))
               (term_var "mwpriv"))
      end.

    Definition gen_mem_pub_class_rel (specs : list mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      gen_mem_pub_class_ks (mem_rel_keys specs).

    Definition gen_mem_priv_class_rel (specs : list mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      gen_mem_priv_class_ks (mem_rel_keys specs).

    (* PVConst / PVBaseOff entries mint no variable already, so they keep
       gen_mem_asn_rel's treatment verbatim and only PVExist entries are
       grouped.  NOTE the resulting HEAP ORDER differs from gen_mem_pre_rel's
       (pinned entries first, then public, then private) -- sound, since ∗ is
       commutative, but it can move consume-scan positions and hence residual
       shapes, which matters when migrating an existing example. *)
    Definition gen_mem_pre_rel_classed (specs : list mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      gen_mem_pre_rel (List.filter (fun s => negb (mem_spec_is_exist s)) specs)
      ∗ gen_mem_pub_class_rel
          (List.filter (fun s => andb (mem_spec_is_exist s) (mem_spec_is_pub s)) specs)
      ∗ gen_mem_priv_class_rel
          (List.filter (fun s => andb (mem_spec_is_exist s) (negb (mem_spec_is_pub s))) specs).

    (* NO concrete (mem_full_spec) counterpart is defined, deliberately.  The
       obvious architecture -- mirror gen_mem_pre_rel_concretize, i.e. rewrite
       the rel assertion into a concrete classed one and then bridge -- does
       NOT typecheck: the two sides' existential widths are
       `mem_class_width (mem_rel_keys L)` and
       `mem_class_width (mem_full_keys (map (concretize_mem ia) L))`, which are
       equal only PROPOSITIONALLY (both are xlenbits * length L, but `length
       (map f L) = length L` is not definitional), so stating the bridge as an
       assertion equality would need a dependent transport across a type index
       -- the width-index trap in core-executor-internals §6.
       The ImplPre bridge therefore attacks `gen_mem_pre_rel_classed` DIRECTLY,
       keeping one width index throughout and handling the `p + of_N k` vs
       literal-address mismatch inside the induction with bv.of_N_add. *)

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

    (* ================================================================== *)
    (* BYTE-GRANULAR CLASSED BLOCK (PLAN-unify-generators.md stage 2).      *)
    (*                                                                     *)
    (* The byte twin of gen_mem_cells_class: ONE grouped variable per        *)
    (* publicness class -- so |Sigma| stops growing with the declared cell   *)
    (* count, which is the dominant VC cost driver -- but each cell's word   *)
    (* is additionally sliced into its four bytes, giving four ptstomem 1    *)
    (* chunks at k..k+3 instead of one ptstomem 4 at k.                      *)
    (*                                                                     *)
    (* This is NOT new slicing machinery: it stacks the two slicings that    *)
    (* already exist.  bvtake/bvdrop peel a cell word off the group exactly  *)
    (* as gen_mem_cells_class does, then term_word_byte peels the bytes off  *)
    (* that cell exactly as gen_mem_asn_rel_bytes does.  So the chunk        *)
    (* inventory is identical to gen_mem_pre_rel_bytes' and only the         *)
    (* variable count changes -- 1 per class instead of 1 per entry.         *)
    (*                                                                     *)
    (* Byte order is term_word_byte's: j = 0 is the byte at the LOWEST       *)
    (* address.  The regression anchors at word_byte pin that convention by  *)
    (* computation; getting it wrong surfaces only much later, as an Iris    *)
    (* wiring failure in EndToEnd.v.                                        *)
    (* ================================================================== *)
    Fixpoint gen_mem_cells_class_bytes {Σ} {K} (ks : list K)
        (addr_of : K -> N -> Term Σ ty_xlenbits)
        (mw : Term Σ (ty.bvec (mem_class_width ks))) : Assertion Σ :=
      match ks return Term Σ (ty.bvec (mem_class_width ks)) -> Assertion Σ with
      | nil      => fun _ => ⊤
      | cons k r => fun mw =>
          byte_chunks (addr_of k)
            (term_word_byte 0 (term_unop (uop.bvtake xlenbits) mw))
            (term_word_byte 1 (term_unop (uop.bvtake xlenbits) mw))
            (term_word_byte 2 (term_unop (uop.bvtake xlenbits) mw))
            (term_word_byte 3 (term_unop (uop.bvtake xlenbits) mw))
          ∗ gen_mem_cells_class_bytes r addr_of
              (term_unop (uop.bvdrop xlenbits) mw)
      end mw.

    (* Distinct binder names from the word classes' "mwpub"/"mwpriv": a contract
       may carry BOTH a word block and a byte block, and distinguishable names
       keep a VC dump readable.  Empty classes emit nothing, for the same reason
       as in the word case -- a width-0 asn.exist would cost a logic variable for
       no cells, which is the whole point of classing. *)
    Definition gen_mem_pub_class_ks_bytes (ks : list N)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      match ks with
      | nil => ⊤
      | _   =>
          asn.exist "mwpubb" (ty.bvec (mem_class_width ks))
            (gen_mem_cells_class_bytes ks
               (fun k j => byte_addr_rel (term_var "p") k j)
               (term_var "mwpubb")
             ∗ secLeakvar "mwpubb")
      end.

    Definition gen_mem_priv_class_ks_bytes (ks : list N)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      match ks with
      | nil => ⊤
      | _   =>
          asn.exist "mwprivb" (ty.bvec (mem_class_width ks))
            (gen_mem_cells_class_bytes ks
               (fun k j => byte_addr_rel (term_var "p") k j)
               (term_var "mwprivb"))
      end.

    (* Same three-way partition as gen_mem_pre_rel_classed, and the same heap
       ORDER consequence: pinned first, then public, then private, rather than
       spec order.  Sound (∗ commutes) but it can move consume-scan positions,
       so a migrating example's VC residual shape can in principle change. *)
    Definition gen_mem_pre_rel_bytes_classed (specs : list mem_spec_rel)
        : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
      gen_mem_pre_rel_bytes
        (List.filter (fun s => negb (mem_spec_is_exist s)) specs)
      ∗ gen_mem_pub_class_ks_bytes
          (mem_rel_keys
             (List.filter (fun s => andb (mem_spec_is_exist s) (mem_spec_is_pub s)) specs))
      ∗ gen_mem_priv_class_ks_bytes
          (mem_rel_keys
             (List.filter (fun s => andb (mem_spec_is_exist s) (negb (mem_spec_is_pub s))) specs)).

    (* bound: an N ≥ (max accessed byte offset)+4, so the fetch/access upper
       bounds are dischargeable from unsigned p + bound ≤ lenAddr. *)
    Definition gen_contract_rel
        (init_addr : N)
        (reg_specs : list reg_spec_rel)
        (mem_specs : list mem_spec_rel)
        (instrs : list AnnotInstr)
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
        instrs ec fl asn_no_post.

    (* ================================================================== *)
    (* THE UNIFIED BUILDER (PLAN-unify-generators.md stage 3).             *)
    (*                                                                     *)
    (* One contract builder over the base-relative param_val vocabulary,   *)
    (* classing by default, with granularity carried by WHICH LIST an entry *)
    (* is in.  There is deliberately no `gran` field on the entries: a      *)
    (* class's grouped existential width must be computable from a list you *)
    (* are inducting on DIRECTLY, and a filtered-and-projected list is      *)
    (* exactly the configuration that only typechecks with a dependent      *)
    (* transport across a type index (core-executor-internals §6, the       *)
    (* width-index trap this project has hit three times).  Two homogeneous *)
    (* lists keep each width a function of one list, the way                *)
    (* mem_class_width (mem_rel_keys L) already is.                         *)
    (*                                                                     *)
    (* Move to per-entry granularity only if a real example needs the two   *)
    (* granularities INTERLEAVED at one address range.  None does, and the  *)
    (* trusted-side concatenation (mem_specs ++ byte_mem_specs) already     *)
    (* assumes they are contiguous blocks.                                 *)
    (*                                                                     *)
    (* Data thus partitions into at most SIX classes -- {word,bytes} x      *)
    (* {pinned,public,private} -- each emitting one grouped existential,    *)
    (* empty classes emitting nothing (gen_mem_pub_class_ks nil = Top).     *)
    (* Verified 2026-08-18 across every live example: no data block MIXES   *)
    (* publicness, and no call site has both lists non-empty, so this       *)
    (* partitioning is the IDENTITY on all current code -- the heap-order   *)
    (* hazard (consume is order-sensitive) has no live instance.  It becomes *)
    (* real the first time one block genuinely mixes pinned/public/private. *)
    Definition gen_contract_u
        (init_addr : N)
        (reg_specs : list reg_spec_rel)
        (word_data : list mem_spec_rel)   (* word-granular class *)
        (byte_data : list mem_spec_rel)   (* byte-granular class *)
        (instrs : list AnnotInstr)
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
          ∗ gen_pre_rel reg_specs
          ∗ gen_mem_pre_rel_classed word_data
          ∗ gen_mem_pre_rel_bytes_classed byte_data )
        instrs ec fl asn_no_post.

    (* gen_contract_rel with the data block grouped into ONE existential per
       publicness class (see gen_mem_pre_rel_classed above).  Same statement
       strength as gen_contract_rel -- the two preconditions are equivalent,
       not merely comparable -- but |Sigma| no longer grows with the declared
       cell count, which is the dominant cost driver.  Byte-identical to
       gen_contract_rel except for the final conjunct. *)
    Definition gen_contract_rel_classed
        (init_addr : N)
        (reg_specs : list reg_spec_rel)
        (mem_specs : list mem_spec_rel)
        (instrs : list AnnotInstr)
        (extra_exit_offs : list N)
        (bound : N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      (* Delegates to gen_contract_u since 2026-08-18 (stage 3).  The only
         difference this makes to the precondition is a trailing
         `gen_mem_pre_rel_bytes []` (= Top) conjunct; verified absorbed by the
         standard `vm_compute; solve_vc; solve_symbase_fetch` line on Countdown's
         real blocks before wiring (Example/ZZUProbe3.v). *)
      gen_contract_u init_addr reg_specs mem_specs []
        instrs extra_exit_offs bound ec fl.

    (* Parameterized-base contract for a REGISTER-ONLY program
       (PLAN-symbolic-base.md Phase 4.2).  The base is a genuine term VARIABLE
       term_var "p" (Σ = ["p"∷ty_xlenbits]), NOT term_val (bv.of_N init_addr) --
       the latter makes the VC's vm_compute diverge on bv.of_N of a symbolic N at
       width 32.  cfg_init_addr / cfg_exitCond are still stored (the
       end-to-end/memory side needs them) but are ignored by Valid_CFG_VC, so the
       VC is proved ONCE, uniformly in init_addr, and reused for every concrete
       base via the ι = ["p" ↦ SyncVal (bv.of_N init_addr)] instantiation in
       gen_contract_noninterferent_param.

       DELEGATES to gen_contract_rel_classed since 2026-08-18
       (PLAN-unify-generators.md stage 1), which is sound because a constant-value
       reg_spec is the base-independent special case of a reg_spec_rel
       (reg_spec_to_rel) and because bound = 4*|instrs| is what this builder always
       hardcoded.  Three consequences worth knowing:

       - There is NO mem_specs parameter any more.  It was a
         list mem_full_spec -- ABSOLUTE addresses -- which cannot be translated to
         the base-relative mem_spec_rel the classed block needs without knowing the
         base.  Every one of its 15 call sites passed [], so nothing was lost; a
         register-only program is the only shape this builder ever served.  For
         data memory use gen_contract_rel_classed directly.
       - The data slot is therefore gen_mem_pre_rel_classed [], which is
         Top * Top * Top rather than gen_mem_pre []'s single Top.  Not
         syntactically equal, so delegation is NOT free by inspection; it was
         validated by probe (Example/ZZUnifyProbe.v) and then by all 9 example VCs
         closing with unmodified tactic lines.
       - The bridge gen_contract_noninterferent_param consumes that shape and so
         changed with it; see its ImplPre. *)
    Definition gen_contract_param
        (init_addr : N)
        (reg_specs : list reg_spec)
        (instrs : list AnnotInstr)
        (extra_exit_offs : list N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_u init_addr
        (List.map reg_spec_to_rel reg_specs) [] []
        instrs extra_exit_offs
        (4 * N.of_nat (length instrs))%N
        ec fl.

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
        (instrs : list AnnotInstr)
        (extra_exit_offs : list N)
        (bound : N)
        (ec : bv xlenbits -> bool)
        (fl : nat)
        : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      (* Delegates to gen_contract_u since 2026-08-18 (stage 3) -- a pure rename,
         the argument order already matches.  ONE semantic change: the word block
         is now CLASSED (gen_mem_pre_rel_classed) rather than one existential per
         entry (gen_mem_pre_rel).  That is equivalent-but-cheaper, and no caller
         is affected either way because EVERY call site of this builder -- the
         committed BearSSLCheckScalarLoop1 and all 28 rigs -- passes [] for the
         word list, so the slot was always Top.  Verified on Loop1's real byte
         block before wiring (Example/ZZUProbe3.v). *)
      gen_contract_u init_addr reg_specs mem_specs byte_mem_specs
        instrs extra_exit_offs bound ec fl.

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

  (* reg_spec_to_rel lands in the PVBaseOff-free subset of param_val, and there
     concretize_reg inverts it AT EVERY BASE -- note `ia` does not occur on the
     right, precisely because no constant-value reg_spec can be base-dependent.
     This is what lets gen_contract_noninterferent_param recover gen_pre over the
     ORIGINAL reg_specs after routing through gen_pre_rel_concretize, and so reuse
     gen_implpre unchanged rather than re-proving a ~130-line Iris induction
     (PLAN-unify-generators.md stage 1). *)
  Lemma concretize_reg_to_rel (ia : N) (s : reg_spec) :
    concretize_reg ia (reg_spec_to_rel s) = s.
  Proof. destruct s as [[r pub] ov]; destruct ov; reflexivity. Qed.

  Lemma map_concretize_reg_to_rel (ia : N) (specs : list reg_spec) :
    List.map (concretize_reg ia) (List.map reg_spec_to_rel specs) = specs.
  Proof.
    induction specs as [|s rest IH]; [reflexivity|].
    cbn [List.map].
    rewrite concretize_reg_to_rel.
    rewrite IH.
    reflexivity.
  Qed.
