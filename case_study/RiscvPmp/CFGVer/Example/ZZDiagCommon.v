(* ========================================================================= *)
(* ZZDiagCommon.v — THROWAWAY diagnostic support (delete after use).          *)
(*                                                                           *)
(* Question: raw-tree NODE counts are exactly linear in N (PLAN-encoded-      *)
(* instr.md §7: nc_angbin 344/687/1373/2745) yet vm_compute is superlinear.   *)
(* So the cost per node must grow.  Every instrument so far counted nodes;    *)
(* this one measures what ACCUMULATES ALONG A PATH and what the nodes CARRY:  *)
(*                                                                           *)
(*   dc_pcsum  Σ over nodes of the enclosing path-condition length            *)
(*             (assertk + assumek both extend the world -- Propositions.v:414)*)
(*   dc_wsum   Σ over nodes of the live logical context size                  *)
(*             (+1 angelicv/demonicv, -1 assert_vareq/assume_vareq)           *)
(*   dc_tsize  Σ of the sizes of every Term held in the tree                  *)
(*   dc_tmax   largest single term                                            *)
(*                                                                           *)
(* Measured on the RAW tree, never the postprocessed one: postprocess prunes  *)
(* the solver-killed forks and substitutes variables away, hiding exactly the *)
(* work vm_compute already paid for.                                         *)
(*                                                                           *)
(* ONE heavy Eval per coqc process (see ZZCommon.v's header).                 *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZCommon.

(* ------------------------------------------------------------------ *)
(* Term size.  term_tuple / term_record are treated as LEAVES: the     *)
(* mutual fixpoint through Env is rejected by the guard checker (Env   *)
(* is parameterized by Term, not mutually inductive with it).  dc_nest *)
(* counts them, so the measure is EXACT whenever dc_nest = 0.          *)
(* ------------------------------------------------------------------ *)

Fixpoint tsize {Σ σ} (t : Term Σ σ) {struct t} : N :=
  match t with
  | term_var _         => 1
  | term_val _ _       => 1
  | term_relval _ _    => 1
  | term_binop _ t1 t2 => 1 + tsize t1 + tsize t2
  | term_unop _ t1     => 1 + tsize t1
  | term_tuple _       => 1
  | term_union _ _ t1  => 1 + tsize t1
  | term_record _ _    => 1
  end.

Fixpoint tnest {Σ σ} (t : Term Σ σ) {struct t} : N :=
  match t with
  | term_binop _ t1 t2 => tnest t1 + tnest t2
  | term_unop _ t1     => tnest t1
  | term_tuple _       => 1
  | term_union _ _ t1  => tnest t1
  | term_record _ _    => 1
  | _                  => 0
  end.

Fixpoint fsize {Σ} (F : Formula Σ) : N :=
  match F with
  | formula_user p ts     => 1
  | formula_bool t        => 1 + tsize t
  | formula_prop _ _      => 1
  | formula_relop _ t1 t2 => 1 + tsize t1 + tsize t2
  | formula_true          => 1
  | formula_false         => 1
  | formula_and F1 F2     => fsize F1 + fsize F2
  | formula_or F1 F2      => fsize F1 + fsize F2
  | formula_propeq t1 t2  => 1 + tsize t1 + tsize t2
  | formula_secLeak t     => 1 + tsize t
  end.

Fixpoint fnest {Σ} (F : Formula Σ) : N :=
  match F with
  | formula_user p ts     => 1      (* Env of terms, unmeasured *)
  | formula_bool t        => tnest t
  | formula_prop _ _      => 1      (* carries a Sub, unmeasured *)
  | formula_relop _ t1 t2 => tnest t1 + tnest t2
  | formula_true          => 0
  | formula_false         => 0
  | formula_and F1 F2     => fnest F1 + fnest F2
  | formula_or F1 F2      => fnest F1 + fnest F2
  | formula_propeq t1 t2  => tnest t1 + tnest t2
  | formula_secLeak t     => tnest t
  end.

(* ------------------------------------------------------------------ *)

Record DC : Set := MkDC
  { dc_nodes : N   (* total SymProp nodes                              *)
  ; dc_pcsum : N   (* Σ over nodes of enclosing path-condition length  *)
  ; dc_wsum  : N   (* Σ over nodes of live logical-context size        *)
  ; dc_tsize : N   (* Σ of all Term sizes held in the tree             *)
  ; dc_tmax  : N   (* largest single Term                              *)
  ; dc_depth : N   (* max tree depth                                   *)
  ; dc_nest  : N   (* unmeasured tuple/record/user leaves (0 = exact)  *)
  }.

Definition dcadd (a b : DC) : DC :=
  MkDC (dc_nodes a + dc_nodes b) (dc_pcsum a + dc_pcsum b)
       (dc_wsum a + dc_wsum b)   (dc_tsize a + dc_tsize b)
       (N.max (dc_tmax a) (dc_tmax b)) (N.max (dc_depth a) (dc_depth b))
       (dc_nest a + dc_nest b).

(* p = enclosing path-condition length, w = live context size. *)
Fixpoint dcount {Σ} (p w : N) (s : 𝕊 Σ) {struct s} : DC :=
  let here := MkDC 1 p w 0 0 0 0 in
  match s with
  | SymProp.angelic_binary o1 o2 =>
      dcadd here (dcadd (dcount p w o1) (dcount p w o2))
  | SymProp.demonic_binary o1 o2 =>
      dcadd here (dcadd (dcount p w o1) (dcount p w o2))
  | SymProp.error _ => here
  | SymProp.block   => here
  | SymProp.assertk fml _ k =>
      dcadd (MkDC 1 p w (fsize fml) (fsize fml) 0 (fnest fml))
            (dcount (p + 1) w k)
  | SymProp.assumek fml k =>
      dcadd (MkDC 1 p w (fsize fml) (fsize fml) 0 (fnest fml))
            (dcount (p + 1) w k)
  | SymProp.angelicv _ k => dcadd here (dcount p (w + 1) k)
  | SymProp.demonicv _ k => dcadd here (dcount p (w + 1) k)
  | @SymProp.assert_vareq _ x σ xIn t _ k =>
      dcadd (MkDC 1 p w (tsize t) (tsize t) 0 (tnest t))
            (dcount p (w - 1) k)
  | @SymProp.assume_vareq _ x σ xIn t k =>
      dcadd (MkDC 1 p w (tsize t) (tsize t) 0 (tnest t))
            (dcount p (w - 1) k)
  | SymProp.debug _ k => dcadd here (dcount p w k)
  end.

(* dc_depth is filled in by a second, cheap pass (folding it into dcount
   would need a max-with-child-depth, which dcadd cannot express). *)
Fixpoint spdepth {Σ} (s : 𝕊 Σ) {struct s} : N :=
  match s with
  | SymProp.angelic_binary o1 o2 => 1 + N.max (spdepth o1) (spdepth o2)
  | SymProp.demonic_binary o1 o2 => 1 + N.max (spdepth o1) (spdepth o2)
  | SymProp.error _              => 1
  | SymProp.block                => 1
  | SymProp.assertk _ _ k        => 1 + spdepth k
  | SymProp.assumek _ k          => 1 + spdepth k
  | SymProp.angelicv _ k         => 1 + spdepth k
  | SymProp.demonicv _ k         => 1 + spdepth k
  | @SymProp.assert_vareq _ _ _ _ _ _ k => 1 + spdepth k
  | @SymProp.assume_vareq _ _ _ _ _ k   => 1 + spdepth k
  | SymProp.debug _ k            => 1 + spdepth k
  end.

Definition dcensus {Σ} (s : 𝕊 Σ) : DC :=
  let d := dcount 0 0 s in
  MkDC (dc_nodes d) (dc_pcsum d) (dc_wsum d) (dc_tsize d)
       (dc_tmax d) (spdepth s) (dc_nest d).

(* ------------------------------------------------------------------ *)
(* ARM B — trip count varies, MEMORY CELL COUNT FIXED AT 1.            *)
(*                                                                     *)
(* zzn grows two things with N at once: the trip count AND the number  *)
(* of memory cells (zzn_mem_specs n = n cells, because A3 advances by  *)
(* 4 each trip).  Holding A3 still makes every trip store to the same  *)
(* cell, so the heap and the mem-spec list stay size 1 for all N.      *)
(* Everything else -- instruction count, fuel formula, register specs, *)
(* exit condition -- is byte-identical to zzn.                         *)
(* ------------------------------------------------------------------ *)

Definition zzf_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; STORE (bv.of_Z 0) A0 A3 WORD
  ; ITYPE (bv.of_Z 0) A3 A3 RISCV_ADDI   (* <-- 0, not 4: A3 stays put *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzn_back_offset
  ].

Definition zzf_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs n) [(56%N, false, PVExist)]
    zzf_instrs [] 60
    (pcOutOfInstrs_exitCond 0 zzf_instrs) (14 * n + 12).

(* ------------------------------------------------------------------ *)
(* ARM C — MEMORY CELL COUNT varies, trip count FIXED AT 1.            *)
(* The converse isolation: one trip, k cells declared in the heap.     *)
(* ------------------------------------------------------------------ *)

Definition zzm_contract (k : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs 1) (zzn_mem_specs k)
    zzn_instrs [] (56 + 4 * N.of_nat k)%N
    (pcOutOfInstrs_exitCond 0 zzn_instrs) (14 * 1 + 12).

(* ------------------------------------------------------------------ *)

Definition zzn_dc (n : nat) : DC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).

Definition zzf_dc (n : nat) : DC :=
  cfg_map (zzf_contract n) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).

Definition zzm_dc (k : nat) : DC :=
  cfg_map (zzm_contract k) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).
