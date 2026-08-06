(* ========================================================================= *)
(* Example/ZZByteVarCommon.v — THROWAWAY probe, PLAN-byte-memory.md §10.      *)
(*                                                                           *)
(* QUESTION: does the LOGIC-VARIABLE COUNT cost anything?                     *)
(*                                                                           *)
(* gen_mem_asn_rel_bytes's PVExist branch emits FOUR INDEPENDENT byte         *)
(* variables per word entry, so N secret bytes cost N logic variables (32 at  *)
(* the real klen).  That was a deliberate choice — bare variables are the     *)
(* smallest terms the executor can carry — but the trade was ASSERTED, never  *)
(* measured.  Semantically one variable suffices: N secret bytes are one      *)
(* bv (8N) existential with byte projections.                                 *)
(*                                                                           *)
(* This probe is the same program, same chunk count, same chunk ADDRESSES —   *)
(* only the chunk VALUES change: one bv 32 existential per word entry, with   *)
(* each byte a vector_subrange of it.  So 4 variables per entry become 1,     *)
(* i.e. 32 -> 8 at N = 32, while every chunk value grows from a bare variable *)
(* to a 2-node subrange term.  That is exactly the trade in question.         *)
(*                                                                           *)
(* (One variable for the WHOLE array — the fully collapsed form — would need  *)
(* a spec entry spanning several words, i.e. new vocabulary.  This 4x probe   *)
(* is the cheap version of the same question.)                                *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition var_back_offset : bv 13 := bv.of_N 8176.

Definition var_instrs : list AST :=
  [ LBU A3 A0 (bv.of_N 0)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI
  ; RTYPE A3 A2 A2 RISCV_OR
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 var_back_offset
  ].

Definition var_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 20)
  ; (A2, true,  PVConst (bv.of_N 0))
  ; (A3, false, PVExist)
  ; (A4, true,  PVConst (bv.of_N n))
  ].

(* THE DELTA: one bv 32 existential per entry instead of four bv 8 ones.
   Compare gen_mem_asn_rel_bytes's PVExist branch in GenContract.v. *)
Definition var_mem_asn (k : N)
    : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
  asn.exist "mw" ty_xlenbits
    (byte_chunks (byte_addr_rel (term_var "p") k)
       (term_word_byte 0 (term_var "mw"))
       (term_word_byte 1 (term_var "mw"))
       (term_word_byte 2 (term_var "mw"))
       (term_word_byte 3 (term_var "mw"))).

Definition var_mem_pre (n : N)
    : Assertion (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) :=
  List.fold_right (fun k acc => var_mem_asn k ∗ acc) ⊤
    (map (fun i => (20 + 4 * N.of_nat i)%N) (seq 0 (Nat.div (N.to_nat n) 4))).

(* gen_contract_rel_bytes with the byte list replaced by this builder.  Same
   shape as gen_contract_rel_bytes otherwise — see GenContract.v. *)
Definition var_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  @MkCFGVerifierContract ["p" :: ty_xlenbits] ia
    (term_var "p")
    (exits_of_offs (term_var "p")
       ((4 * N.of_nat (length var_instrs))%N :: []))
    ( asn_pc_eq (term_var "p")
      ∗ asn.formula (formula_relop bop.le
           (term_binop bop.plus (term_unop uop.unsigned (term_var "p"))
              (term_val ty.int (Z.of_N (20 + n)%N)))
           (term_val ty.int (Z.of_N lenAddr)))
      ∗ gen_pre_rel (var_reg_specs_rel n) ∗ gen_mem_pre_rel []
      ∗ var_mem_pre n )
    var_instrs (pcOutOfInstrs_exitCond ia var_instrs)
    (Nat.add (Nat.mul 5 (N.to_nat n)) 8).
