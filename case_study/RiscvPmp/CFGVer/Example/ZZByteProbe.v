(* ========================================================================= *)
(* Example/ZZByteProbe.v — THROWAWAY probe, PLAN-byte-memory.md §6 step 1.    *)
(*                                                                           *)
(* The go/no-go for byte-granular data cells: the SMALLEST possible program   *)
(* that performs a byte load against a byte-expanded data cell.  No example   *)
(* in this repo has ever used a BYTE-width memory access, so this is the      *)
(* first exercise of Machine.v's `mem_read 1` path.  Nothing here is part of  *)
(* any trusted statement; delete once check_scalar's loop 1 lands.            *)
(*                                                                           *)
(* Layout at base p:                                                          *)
(*   p+0 : LBU X1, 4(X2)   -- X1 := zext(mem[X2+4])                           *)
(*   p+4 : (fall-through exit; also the single data word)                     *)
(* X2 holds the base (PVBaseOff 0), so the loaded address is genuinely p+4 —  *)
(* base-RELATIVE, hence the _rel family.  X0 could not be used: it is         *)
(* hardwired to 0, making any address off it absolute.                        *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition byte_probe_instrs : list AST := [ LBU X1 X2 (bv.of_N 4) ].

Definition byte_probe_reg_specs_rel : list reg_spec_rel :=
  [(X1, false, PVExist); (X2, false, PVBaseOff 0)].

(* The one data word, declared PRIVATE and BYTE-EXPANDED: the executor gets
   four `ptstomem 1` chunks at p+4..p+7 instead of one `ptstomem 4`, so the
   lbu's consume of `ptstomem 1 (p+4) _` can match.  A resident ptstomem 4
   chunk could NOT discharge it — width is part of the predicate index
   (Sig.v:365) and the chunk matcher has no split rule. *)
Definition byte_probe_byte_specs_rel : list mem_spec_rel :=
  [(4%N, false, PVExist)].

(* bound = 8: last accessed byte offset 4, plus the declared word's width 4. *)
Definition byte_probe_cfg_contract_param (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia byte_probe_reg_specs_rel [] byte_probe_byte_specs_rel
    byte_probe_instrs [] 8
    (pcOutOfInstrs_exitCond ia byte_probe_instrs) 5.

Lemma valid_byte_probe_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (byte_probe_cfg_contract_param ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
