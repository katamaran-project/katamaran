(* ========================================================================= *)
(* Example/ZZCheckScalarFull.v -- THROWAWAY, PLAN-check-scalar-full.md §5.    *)
(*                                                                           *)
(* Whole-function BearSSL `check_scalar`: BOTH loops in ONE instruction      *)
(* list, translated from the REAL clang output of the REAL C function       *)
(* (guard branches included), not a hand-stitched concatenation of the      *)
(* loop1/loop2 probes (whose register allocations don't match this          *)
(* combined-context compile anyway -- codegen-context difference, same      *)
(* phenomenon already noted for loop2's 13- vs 16-instruction forms).        *)
(*                                                                           *)
(* ORIGINAL C -- BearSSL src/ec/ec_p256_m62.c:1610, compiled WHOLE with      *)
(* `clang --target=riscv32 -march=rv32i -mabi=ilp32 -mcmodel=medany -O2`     *)
(* (GT/CMP/EQ0/NEQ/LT0 as in BearSSLCheckScalar.v's header):                 *)
(*                                                                           *)
(*     uint32_t check_scalar(const unsigned char *k, size_t klen) {          *)
(*         uint32_t z; int32_t c; size_t u;                                  *)
(*         if (klen > 32) return 0;                                          *)
(*         z = 0;                                                            *)
(*         for (u = 0; u < klen; u++) z |= k[u];                             *)
(*         if (klen == 32) {                                                 *)
(*             c = 0;                                                        *)
(*             for (u = 0; u < klen; u++)                                    *)
(*                 c |= -(int32_t)EQ0(c) & CMP(k[u], P256_N[u]);             *)
(*         } else { c = -1; }                                                *)
(*         return NEQ(z, 0) & LT0(c);                                        *)
(*     }                                                                     *)
(*                                                                           *)
(* `-mcmodel=medany` matters: the DEFAULT (medlow) model addresses the       *)
(* `P256_N` rodata constant via `lui`/`addi %hi/%lo` -- an ABSOLUTE 32-bit    *)
(* address, which is simply the wrong primitive here regardless of tooling:  *)
(* every contract in this codebase is parametric in the load address "p",    *)
(* so baking in one fixed absolute address would be false unless the        *)
(* program happens to load exactly there. `medany` instead emits             *)
(* `auipc`/`addi %pcrel_hi/%pcrel_lo` -- a PC-RELATIVE address, i.e. "a fixed *)
(* distance from wherever this instruction itself ends up", which is        *)
(* exactly how every other address in this codebase is already modeled      *)
(* (p + fixed offset). `RISCV_AUIPC` is already a real, faithfully-modelled  *)
(* opcode in this case study -- nothing new needed there.                    *)
(*                                                                           *)
(* The `%pcrel_hi(P256_N)` / `%pcrel_lo(...)` operands are still SYMBOLIC    *)
(* text `asm_to_ast.py` will not parse (`UTYPE_OPS` requires a literal       *)
(* integer immediate, by design -- the tool "refuses to guess", and has no   *)
(* relocation-resolution logic of any kind; it only resolves BRANCH labels   *)
(* within the same listing, a much simpler same-file byte-count). Normally a *)
(* LINKER fills these in as its last step, using the final memory layout.    *)
(* There is no linker in this pipeline, so nothing ever would. But since we  *)
(* pick this program's ENTIRE memory layout ourselves anyway (code, then     *)
(* k[], then P256_N, contiguous -- the same convention every example here    *)
(* already uses for its own data), that layout is exactly the information a *)
(* linker would need, and we already have it. So the two placeholders were   *)
(* resolved BY HAND below, marked at the two lines that changed:             *)
(*   code = 35 instrs * 4 bytes = 140 bytes (p+0 .. p+139)                   *)
(*   k[]     : p+140 .. p+171  (32 bytes, SECRET)                            *)
(*   P256_N  : p+172 .. p+203  (32 bytes, PUBLIC)                            *)
(*   the auipc sits at instruction index 17, i.e. byte offset p+68           *)
(*   pcrel = (p+172) - (p+68) = 104  (independent of p, as it must be)       *)
(*   li_split(104) = hi20 0, lo12 104  (104 fits in the addi's 12 signed      *)
(*   bits outright, so auipc contributes nothing and addi does all the work) *)
(*                                                                           *)
(* Verified here is the WHOLE function, guard branches included, translated  *)
(* as-is (the dead `if (klen > 32) return 0;` block is NOT trimmed out --     *)
(* pinning A1 = 32 below makes the solver refute that branch's condition at  *)
(* FORK time, per cfgver-executor's documented mechanism ("a refuted fork    *)
(* collapses to SymProp.block before its continuation is built"), so the     *)
(* dead block's mid-function `ret` -- which the executor could not step      *)
(* through if it were ever actually reached -- is simply never visited).     *)
(* Prologue/epilogue are NOT trimmed either: this is the real entry point    *)
(* and the real final `ret` (dropped per the usual `--drop-ret` convention,  *)
(* reaching one-past-the-end is `pcOutOfInstrs_exitCond`).                   *)
(*                                                                           *)
(* Translated with tools/asm_to_ast.py --drop-ret (after the two manual      *)
(* relocation patches below); register names substituted from the tool's    *)
(* local a0.. aliases to this project's existing X0/X1/A0-A7.                *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzcsfixn4_instrs : list AST :=
  [ ITYPE (bv.of_Z 4) X0 A2 RISCV_ADDI       (* li    a2, 4  -- SMALL-N PROBE: was 32 *)
  ; BTYPE (bv.of_Z 12) A1 A2 RISCV_BGEU        (* bgeu  a2, a1, .LBB0_2 *)
  ; ITYPE (bv.of_Z 0) X0 A0 RISCV_ADDI         (* li    a0, 0  -- dead when klen=32 *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0               (* ret          -- dead, never reached *)
  ; ITYPE (bv.of_Z 1) X0 A3 RISCV_ADDI         (* li    a3, 1 *)
  ; ITYPE (bv.of_Z 0) X0 A2 RISCV_ADDI         (* li    a2, 0 *)
  ; BTYPE (bv.of_Z 112) X0 A1 RISCV_BEQ        (* beqz  a1, .LBB0_9 *)
  ; RTYPE A1 A0 A4 RISCV_ADD                   (* add   a4, a0, a1 *)
  ; ITYPE (bv.of_Z 0) A0 A5 RISCV_ADDI         (* mv    a5, a0 *)
  ; LOAD (bv.of_Z 0) A5 A6 true BYTE           (* lbu   a6, 0(a5)   -- loop 1 body *)
  ; ITYPE (bv.of_Z 1) A5 A5 RISCV_ADDI         (* addi  a5, a5, 1 *)
  ; RTYPE A6 A2 A2 RISCV_OR                    (* or    a2, a2, a6 *)
  ; BTYPE (bv.of_Z (-12)) A4 A5 RISCV_BNE      (* bne   a5, a4, .LBB0_4 *)
  ; ITYPE (bv.of_Z 4) X0 A4 RISCV_ADDI        (* li    a4, 4  -- SMALL-N PROBE: was 32 *)
  ; RTYPE A2 X0 A2 RISCV_SLTU                  (* snez  a2, a2 *)
  ; BTYPE (bv.of_Z 76) A4 A1 RISCV_BNE         (* bne   a1, a4, .LBB0_9 *)
  ; ITYPE (bv.of_Z 0) X0 A3 RISCV_ADDI         (* li    a3, 0 *)
  ; UTYPE (bv.of_Z 0) A1 RISCV_AUIPC           (* auipc a1, 0   <-- MANUALLY RESOLVED: replaces %pcrel_hi(P256_N); hi20=0 for our layout (P256_N at p+172, this instr at p+68, pcrel=104 fits in addi's low 12 bits alone) *)
  ; ITYPE (bv.of_Z 104) A1 A1 RISCV_ADDI       (* addi  a1, a1, 104   <-- MANUALLY RESOLVED: replaces %pcrel_lo(...); together with the auipc above, a1 := (that auipc's own address) + 104 = p+172 = &P256_N *)
  ; ITYPE (bv.of_Z 4) A1 A4 RISCV_ADDI        (* addi  a4, a1, 4  -- SMALL-N PROBE FIX: was 32, this is loop2's OWN trip-count literal, separate from a1/A1's pinned value *)
  ; LOAD (bv.of_Z 0) A0 A5 true BYTE           (* lbu   a5, 0(a0)   -- loop 2 body *)
  ; LOAD (bv.of_Z 0) A1 A6 true BYTE           (* lbu   a6, 0(a1) *)
  ; RTYPE A5 A6 A7 RISCV_SLTU                  (* sltu  a7, a6, a5 *)
  ; RTYPE A6 A5 A5 RISCV_SLTU                  (* sltu  a5, a5, a6 *)
  ; RTYPE A5 X0 A5 RISCV_SUB                   (* neg   a5, a5 *)
  ; RTYPE A7 A5 A5 RISCV_OR                    (* or    a5, a5, a7 *)
  ; RTYPE A3 X0 A6 RISCV_SLTU                  (* snez  a6, a3 *)
  ; ITYPE (bv.of_Z (-1)) A6 A6 RISCV_ADDI      (* addi  a6, a6, -1 *)
  ; RTYPE A5 A6 A5 RISCV_AND                   (* and   a5, a6, a5 *)
  ; RTYPE A3 A5 A3 RISCV_OR                    (* or    a3, a5, a3 *)
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI         (* addi  a1, a1, 1 *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI         (* addi  a0, a0, 1 *)
  ; BTYPE (bv.of_Z (-48)) A4 A1 RISCV_BNE      (* bne   a1, a4, .LBB0_7 *)
  ; SHIFTIOP (bv.of_Z 31) A3 A3 RISCV_SRLI     (* srli  a3, a3, 31 *)
  ; RTYPE A3 A2 A0 RISCV_AND                   (* and   a0, a2, a3 *)
  ].

(* A0 = &k[0] = p+140 (code is 35*4=140 bytes).  A1 = klen, PINNED to the
   real P-256 value 32 (public AND concrete, not just public): this is what
   makes all THREE guard branches above resolve to a single live path at
   fork time (cfgver-executor: a refuted fork's continuation is never
   built), so the dead early-return block is never symbolically visited.
   A2 = z accumulator, pinned 0 like loop1's own A2 -- becomes secret the
   moment the first secret byte is ORed in.  A3-A7 are all write-before-read
   scratch (loop1's leftover values in A4/A5 are overwritten before loop2
   ever reads them), so their precondition value is immaterial. *)
Definition zzcsfixn4_reg_specs_rel : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 140)
  ; (A1, true,  PVConst (bv.of_N 4))  (* SMALL-N PROBE: was 32 *)
  ; (A2, true,  PVConst (bv.of_N 0))
  ; (A3, false, PVExist)
  ; (A4, false, PVExist)
  ; (A5, false, PVExist)
  ; (A6, false, PVExist)
  ; (A7, false, PVExist)
  ].

(* k[]: 8 SECRET byte-expanded word entries at p+140, p+144, ..., p+168. *)
Definition zzcsfixn4_k_specs_rel : list mem_spec_rel :=
  [ (140%N, false, PVExist) ].  (* SMALL-N PROBE: 1 word-group, was 8 *)

(* P256_N: 8 PUBLIC-BUT-UNPINNED byte-expanded word entries at p+172, ...,
   p+200 -- tried as PVExist first per PLAN-check-scalar-full.md §4's own
   loop2 precedent, where the PVConst/subrange fallback was never needed. *)
Definition zzcsfixn4_n_specs_rel : list mem_spec_rel :=
  [ (172%N, true, PVExist) ].  (* SMALL-N PROBE: 1 word-group, was 8 *)

Definition zzcsfixn4_byte_specs_rel : list mem_spec_rel :=
  zzcsfixn4_k_specs_rel ++ zzcsfixn4_n_specs_rel.

(* Bound 204: the last declared byte (P256_N[31]) sits at offset 203. *)
(* Fuel 620: the real klen=32 dynamic path is li(1) + bgeu(1) + li,li(2) +
   beqz(1) + add,mv(2) + loop1 body 4*32=128 + li,snez(2) + bne(1) +
   li,auipc,addi,addi(4) + loop2 body 13*32=416 + srli,and(2) + exit(~1)
   = 561 steps; 620 leaves ~60 slack. *)
Definition zzcsfixn4_cfg_contract_param (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia zzcsfixn4_reg_specs_rel [] zzcsfixn4_byte_specs_rel
    zzcsfixn4_instrs [] 204%N
    (pcOutOfInstrs_exitCond ia zzcsfixn4_instrs) 110.  (* SMALL-N PROBE: was 620 *)

Lemma valid_zzcsfixn4_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (zzcsfixn4_cfg_contract_param ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
