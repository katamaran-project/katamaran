(* ========================================================================= *)
(* Example/ZZByteRevCommon.v — THROWAWAY ABLATION for PLAN-byte-memory.md §10.*)
(*                                                                           *)
(* QUESTION: loop 1's cost grows WORSE than quadratically with a RISING       *)
(* exponent (VC doubling-slopes 0.65 -> 1.39 -> 2.25), even though chunk-GC   *)
(* removed the O(steps^2) encodes_instr leak and coalesce removed the 2^N     *)
(* mask term.  Two candidate drivers remain:                                  *)
(*                                                                           *)
(*   (A) RESIDENT DATA CELLS x steps.  gc_heap (Verifier.v:307) filters only  *)
(*       `chunk_user encodes_instr`, so the N ptstomem 1 chunks stay in the   *)
(*       heap for every step and per-step consume work is linear in heap size.*)
(*   (B) PATH-CONDITION ACCUMULATION.  clang's loop 1 exits on `bne a0, a1`   *)
(*       with BOTH operands base-relative; with a symbolic base the solver    *)
(*       has no cancellation rule for `p+c1` vs `p+c2`, cannot decide, and    *)
(*       pushes one formula PER TAKEN ITERATION (observed directly: the N=4   *)
(*       residual carried H1,H2,H3 = p+0x11/0x12/0x13 <> p+0x14).             *)
(*                                                                           *)
(* THIS ABLATION removes (B) and keeps (A): identical byte-chunk count per N, *)
(* identical byte loads at an advancing symbolic address, but the loop exits  *)
(* on a PINNED CONCRETE counter (`addi a4,a4,-1; bne a4,x0`) so the branch    *)
(* decides by computation and nothing accumulates -- the KeyScheduleLoop      *)
(* shape.                                                                    *)
(*                                                                           *)
(* READ THE SLOPES, NOT THE ABSOLUTE TIMES: this body is 5 instructions to    *)
(* loop 1's 4, so the constant differs.  If this variant is AFFINE, (B) is    *)
(* the driver and a `bvadd` cancellation rule is the whole fix (bvadd is      *)
(* injective, so p+c1 = p+c2 <-> c1 = c2 holds unconditionally in Z/2^32 --   *)
(* no no-wrap side condition).  If it stays super-linear, (A) dominates and   *)
(* §8's chunk_gc widening is required.                                        *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

(* -16 in 13-bit two's complement: the BNE sits at byte offset 16. *)
Definition rev_back_offset : bv 13 := bv.of_N 8176.

Definition rev_instrs : list AST :=
  [ LBU A3 A0 (bv.of_N 0)                    (* lbu  a3, 0(a0)  *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI       (* addi a0, a0, 1  *)
  ; RTYPE A3 A2 A2 RISCV_OR                  (* or   a2, a2, a3 *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI    (* addi a4, a4, -1 *)
  ; BNE A4 X0 rev_back_offset                (* bne  a4, x0, .L *)
  ].

(* 5 instructions => data starts at p+20.
   A4 is the PINNED CONCRETE trip counter -- this is the whole point of the
   ablation: the branch condition evaluates to a literal every iteration, so
   no formula enters the path condition. *)
Definition rev_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 20)
  ; (A2, true,  PVConst (bv.of_N 0))
  ; (A3, false, PVExist)
  ; (A4, true,  PVConst (bv.of_N n))
  ].

(* Same chunk count as loop 1 at the same N: n/4 byte-expanded word entries. *)
(* HEAP-ORDER PROBE: identical spec SET to ZZByteCtrCommon.v, declared in the
   REVERSE order.  produce_chunk prepends (Monads.v: `cons (peval_chunk c) h`)
   and consume scans front-to-back, so declaration order fixes where a
   sequentially-accessed cell sits in the list.  If order is irrelevant this
   times the same as the counter variant; if it matters, one of the two
   orders is paying an O(N) scan on every single byte load. *)
Definition rev_byte_specs_rel (n : N) : list mem_spec_rel :=
  rev (map (fun i => ((20 + 4 * N.of_nat i)%N, false, PVExist))
           (seq 0 (Nat.div (N.to_nat n) 4))).

Definition rev_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia (rev_reg_specs_rel n) [] (rev_byte_specs_rel n)
    rev_instrs [] (20 + n)%N
    (pcOutOfInstrs_exitCond ia rev_instrs)
    (Nat.add (Nat.mul 5 (N.to_nat n)) 8).
