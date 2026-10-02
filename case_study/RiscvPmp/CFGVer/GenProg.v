(* ========================================================================= *)
(* CFGVer/GenProg.v -- THE generic whole-program bridge                       *)
(* (PLAN-general-endtoend.md A3).  gen_prog_contract states a program's       *)
(* precondition in generator form (reg_spec_q registers, caller-proved facts, *)
(* gen_data_at data incl. DPtr pointer arguments); gen_prog_noninterferent   *)
(* turns its VC into noninterferent_strong with the ImplPre done once, via   *)
(* EndToEnd.cfg_instrs_endToEnd_gen.  Needs both GenCompose (exit fact) and  *)
(* EndToEnd (the core), which are otherwise independent -- hence its own     *)
(* file.                                                                     *)
(* ========================================================================= *)
From Coq Require Import
     ZArith.ZArith Lists.List micromega.Lia Strings.String.
From Katamaran Require Import
     Notations Bitvector Semantics
     RiscvPmp.CFGVer.Spec RiscvPmp.Machine RiscvPmp.Sig.
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
     RiscvPmp.CFGVer.GenSegment
     RiscvPmp.CFGVer.Adequacy
     RiscvPmp.CFGVer.Validity
     RiscvPmp.CFGVer.GenCompose
     RiscvPmp.CFGVer.EndToEnd.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.
Local Unset Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.
Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import IrisInstanceBinary.
Import RiscvPmpIrisInstance2.
Import RiscvPmpSemantics.
Import RiscvPmpIrisAdeqParams2.
Import IrisModelBinary.RiscvPmpIrisBase2.

(* ========================================================================== *)
(* gen_prog_noninterferent: ONE bridge for a whole program, ImplPre done once *)
(* (PLAN-general-endtoend.md A3).                                             *)
(* ========================================================================== *)
(* A whole-program contract in generator form: the code at the base variable
   `pb`, its exit the fall-through, and a precondition made of
     - registers as reg_spec_q (PQExist / PQConst / PQAt "x" k: the register
       holds a logic variable plus an offset -- pointer arguments, lengths),
     - arbitrary `facts` the caller proves at the statement's valuation,
     - the data, through gen_data_at from base + doff (DPtr for data that
       lives behind a pointer argument, anywhere).
   The bridge concludes noninterferent_strong at the statement the generator
   determines; its premises are a valuation, sync-ness of the register
   variables, NoDup, data_ok, and data_layout_ok (the cells disjoint from
   each other and from the code) -- no hand-written ImplPre. *)



Lemma gen_regs_q_concretize `{sailGS2 Σ'} {Σ} (ι : Valuation Σ) (va : RelVal ty_xlenbits)
    (specs : list (reg_spec_q Σ)) :
  Forall (reg_q_sync ι) specs ->
  asn.interpret (gen_pre (map (concretize_reg_q ι) specs)) ι.["a"∷ty_xlenbits ↦ va]
  ⊢ asn.interpret (gen_regs_q specs) ι.["a"∷ty_xlenbits ↦ va].
Proof.
  induction specs as [|[[r pub] pv] rest IH]; intros Hs; [done|].
  inversion Hs as [|? ? Hh Ht]; subst.
  cbn [gen_pre gen_regs_q map List.fold_right asn.interpret].
  iIntros "[Hh Hr]". iSplitL "Hh"; [|iApply (IH Ht with "Hr")].
  destruct pv as [|v|b bIn k]; cbn [concretize_reg_q gen_reg_asn gen_reg_asn_q].
  - destruct pub; cbn; iExact "Hh".
  - iExact "Hh".
  - cbn in Hh. unfold addr_off.
    assert (Hreg : forall {Γ} (ι0 : Valuation Γ) (t1 t2 : Term Γ ty_xlenbits),
        inst (T := fun Σ => Term Σ ty_xlenbits) t1 ι0 = inst (T := fun Σ => Term Σ ty_xlenbits) t2 ι0 ->
        asn.interpret (asn_regidx_pts r t1) ι0 ⊣⊢ asn.interpret (asn_regidx_pts r t2) ι0).
    { intros Γ ι0 t1 t2 E. unfold asn_regidx_pts. destruct (reg_convert r); cbn; [rewrite E|]; reflexivity. }
    match goal with |- context [asn_regidx_pts r ?t] => remember t as T eqn:ET end.
    assert (Hi : inst (T := fun Σ => Term Σ ty_xlenbits) T ι.["a"∷ty_xlenbits ↦ va]
                 = SyncVal (if bv.eqb (@bv.of_N xlenbits k) bv.zero then rv_val (env.lookup ι bIn)
                            else bv.add (rv_val (env.lookup ι bIn)) (bv.of_N k))).
    { subst T. destruct (bv.eqb (bv.of_N k) bv.zero); cbn [inst inst_term env.lookup]; rewrite Hh; reflexivity. }
    match goal with |- context [asn_regidx_pts r (if ?c then ?x else ?y)] =>
      remember (if c then x else y) as T2 eqn:ET2 end.
    assert (Hi2 : inst (T := fun Σ => Term Σ ty_xlenbits) T2 ι.["a"∷ty_xlenbits ↦ va]
                  = SyncVal (if bv.eqb (@bv.of_N xlenbits k) bv.zero then rv_val (env.lookup ι bIn)
                             else bv.add (rv_val (env.lookup ι bIn)) (bv.of_N k))).
    { subst T2. destruct (bv.eqb (bv.of_N k) bv.zero); cbn [inst inst_term];
      change (env.lookup (ι.["a"∷ty_xlenbits ↦ va]) (ctx.in_succ bIn)) with (env.lookup ι bIn);
      rewrite Hh; cbn [rv_val ty.projLeft]; reflexivity. }
    iPoseProof (proj1 (proj1 (bi.equiv_entails _ _) (Hreg _ _ T T2 (eq_trans Hi (eq_sym Hi2)))) with "Hh") as "Hh".
    destruct pub; cbn [asn.interpret]; [iFrame "Hh"; cbn; rewrite Hi2; done|iExact "Hh"].
Qed.


Lemma gen_prog_noninterferent {R : LCtx} (pb : string) (pIn : (pb∷ty_xlenbits ∈ R)%katamaran)
    regs facts doff data instrs fuel post (ι : Valuation R) (init_addr : N)
    (Hp : env.lookup ι pIn = SyncVal (bv.of_N init_addr))
    (Hsync : Forall (reg_q_sync ι) regs)
    (HND : NoDup (map reg_spec_idx (map (concretize_reg_q ι) regs)))
    (Hfacts : forall `{sailGS2 Σ}, ⊢ asn.interpret facts ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])
    (Hok : data_ok ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)] (init_addr + doff) data)
    (HLayout : data_layout_ok init_addr (length instrs)
       (map mem_full_to_spec (concretize_data ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)] (init_addr + doff) data)))
    (Hlen : (init_addr + 4 * N.of_nat (length instrs) < lenAddr)%N)
    (valid : ValidCFGVerifierContract (gen_prog_contract pb pIn regs facts doff data instrs fuel post)) :
  noninterferent_strong init_addr instrs (init_addr + 4 * N.of_nat (length instrs))%N
    (map (concretize_reg_q ι) regs)
    (concretize_data ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)] (init_addr + doff) data).
Proof.
  intros γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  eapply (@cfg_instrs_endToEnd_gen γ1 γ2 γ1' μ1 μ2 μ1' instrs
    (init_addr + 4 * N.of_nat (length instrs))%N n ws R ι
    _ HpubReg (map mem_full_to_spec (concretize_data ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)] (init_addr + doff) data)) HpubMem
    _ valid eq_refl init_addr).
  all: try assumption.
  - unfold gen_prog_contract, gen_seg_contract. cbn [cfg_exit].
    apply (seg_exit_table_ok _ _ init_addr (4 * N.of_nat (length instrs))). exact Hp.
  - intros Σ' GS'.
    iIntros "(Hregs & Hmem & Hpriv & #Hinv)".
    iPoseProof (gen_implpre (map (concretize_reg_q ι) regs) ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]
                  HpubReg HND HInitReg1 HInitReg2 with "Hregs") as "Hpre".
    iPoseProof (gen_regs_q_concretize ι _ regs Hsync with "Hpre") as "Hregs".
    assert (Ha : inst (T := fun Σ => Term Σ ty_xlenbits)
                   (t_add (@term_var _ pb _ (ctx.in_succ pIn)) (Z.of_N doff))
                   ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]
                 = SyncVal (@bv.of_N xlenbits (init_addr + doff))).
    { unfold t_add. cbn [inst inst_term].
      change (env.lookup (ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]) (ctx.in_succ pIn))
        with (env.lookup ι pIn).
      rewrite Hp. cbn. f_equal. rewrite bv.of_Z_N -bv.of_N_add. reflexivity. }
    iPoseProof (@gen_implpre_data _ _ _ ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)] μ1 μ2 data _
                  (init_addr + doff)%N Ha Hok HInitMem1 HInitMem2 with "Hmem") as "Hdata".
    iPoseProof (Hfacts Σ' GS') as "Hf".
    unfold gen_prog_contract, gen_seg_contract, extend_to_minimal_pre.
    cbn [cfg_precondition asn.interpret].
    iFrame "Hpriv Hinv Hdata Hregs Hf".
    assert (Hpa : inst (T := fun Σ => Term Σ ty_xlenbits) (@term_var _ pb _ (ctx.in_succ pIn))
                   ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)] = SyncVal (@bv.of_N xlenbits init_addr)).
    { cbn [inst inst_term].
      change (env.lookup (ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]) (ctx.in_succ pIn))
        with (env.lookup ι pIn). exact Hp. }
    unfold asn_pc_eq, gen_base_bound, gen_regs_at. cbn [asn.interpret List.fold_right].
    iSplitR; [iSplit; [iPureIntro|done]|].
    { cbn [instprop instprop_formula]. rewrite Hpa. reflexivity. }
    iSplitR; [iSplit; [iPureIntro|done]|].
    { cbn [instprop instprop_formula]. cbn [inst inst_term].
      change (env.lookup (ι.["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]) (ctx.in_succ pIn)) with (env.lookup ι pIn).
      rewrite Hp. cbn.
      rewrite data_unsigned_of_N_small; [|unfold lenAddr in Hlen; lia]. lia. }
    iSplit; [iPureIntro; cbn; reflexivity|done].
Qed.
