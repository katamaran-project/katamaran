(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarPtrResult.v -- BearSSL check_scalar with k  *)
(* a REAL POINTER ARGUMENT: k anywhere in memory that is in range and        *)
(* disjoint from the code and P256_N.  The end theorem is ONE application of *)
(* the generic bridge GenProg.gen_prog_noninterferent -- no hand-written     *)
(* ImplPre (PLAN-general-endtoend.md A3 probe).                              *)
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
     RiscvPmp.CFGVer.SpecLists
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.GenSegment
     RiscvPmp.CFGVer.Adequacy
     RiscvPmp.CFGVer.GenCompose
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamInstrs
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop2
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParam
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamResult
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarPtr
     RiscvPmp.CFGVer.GenProg.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
From Equations Require Import Equations.

Import RiscvPmpProgram.

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
Import SmallStepNotations.
Import IrisModelBinary.RiscvPmpIrisBase2.
Import iris.algebra.excl.
Import iris.algebra.gmap.
From Katamaran Require RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarPtrVC.

Lemma csp_erase : List.map eraseV cs_annotV = cs_annot.
Proof.
  unfold cs_annotV, cs_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV, cs_blockV, cs_block. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma csp_valid : ValidCFGVerifierContract csp.
Proof.
  apply (@ValidCFGVerifierContract_intro _ csp cs_annotV).
  - rewrite csp_erase. exact CheckScalarPtrVC.valid_csp.
  - exact cs_code.
Qed.

(* the statement's valuation: the load address, klen, and k's address *)
Definition csp_ι (ia ka : N) (l : bv xlenbits) : Valuation csCtx :=
  [env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["l"∷ty_xlenbits ↦ SyncVal l]
       .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N ka)].

(* ---- THE STATEMENT'S OWN DATA (PLAN-spec-layer D21) --------------------
   Written in the kernel's terms, not the region front-end: k may sit on
   EITHER side of the code, which back-to-back regions cannot express.  The
   two blocks are disjoint by the parameter premise, proved once below. *)
Definition check_scalar_ptr_blocks (ia ka : N) (l : bv xlenbits) : list mem_block :=
  [ {| blk_addr := ia + 144; blk_words := repeat Secret 8 |}                   (* P256_N *)
  ; {| blk_addr := ka;       blk_words := repeat Secret (klen_words l) |} ].   (* k *)

Lemma check_scalar_ptr_disjoint (ia ka : N) (l : bv xlenbits)
    (H : (ka + 4 * N.of_nat (klen_words l) <= ia \/ ia + 176 <= ka)%N) :
  blocks_disjoint (check_scalar_ptr_blocks ia ka l).
Proof.
  unfold blocks_disjoint, check_scalar_ptr_blocks, blk_end. cbn [blk_addr blk_words].
  constructor; [constructor; [|constructor] | constructor; constructor].
  cbn [blk_addr blk_words]. rewrite !repeat_length. cbn [N.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Definition check_scalar_ptr_mem (ia ka : N) (l : bv xlenbits)
    (H : (ka + 4 * N.of_nat (klen_words l) <= ia \/ ia + 176 <= ka)%N) : mem_layout :=
  {| blocks := check_scalar_ptr_blocks ia ka l; blocks_ok := check_scalar_ptr_disjoint ia ka l H |}.

Definition check_scalar_ptr_regs (ia ka : N) (l : bv xlenbits) : list reg_spec :=
  [ (A0, Known (bv.of_N ka));             (* k             *)
    (A1, Known l);                        (* klen          *)
    (X1, Known (bv.of_N (ia + 144)));     (* ra = the exit *)
    (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret) ].

(* THE END THEOREM: k at ANY address ka whose ⌈klen/4⌉ words are clear of
   the code and P256_N ([ia, ia + 176)), the whole layout in range. *)
Lemma check_scalar_ptr_noninterferent (init_addr ka : N) (l : bv xlenbits)
    (Hdis : (ka + 4 * N.of_nat (klen_words l) <= init_addr \/ init_addr + 176 <= ka)%N) :
  in_range init_addr cs_instrs (check_scalar_ptr_mem init_addr ka l Hdis) ->
  noninterferent_strong init_addr cs_instrs (init_addr + 4 * N.of_nat (length cs_instrs))
    (check_scalar_ptr_regs init_addr ka l) (check_scalar_ptr_mem init_addr ka l Hdis).
Proof.
  intros Hrange.
  assert (Hfit : (init_addr + 176 < lenAddr)%N /\ (ka + 4 * N.of_nat (klen_words l) < lenAddr)%N).
  { destruct Hrange as [_ Hb].
    unfold check_scalar_ptr_mem, check_scalar_ptr_blocks, blk_end in Hb.
    cbn [blocks] in Hb.
    inversion Hb as [|? ? H1 Hb']; subst. inversion Hb' as [|? ? H2 _]; subst.
    cbn [blk_addr blk_words length] in H1, H2. rewrite repeat_length in H2.
    cbn [N.of_nat Pos.of_succ_nat Pos.succ] in H1. lia. }
  destruct Hfit as [Hfit Hk].
  pose proof lenAddr_small_word as HL. change word with xlenbits in HL. change xlenbits with 32%nat in HL.
  assert (Hka : bv.bin (@bv.of_N xlenbits ka) = ka) by (apply bv.bin_of_N_small; cbn; lia).
  assert (Hlb : (bv.bin l + 3 < 4294967296)%N).
  { unfold klen_words in *.
    pose proof (Nat.div_mod (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
    pose proof (Nat.mod_upper_bound (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)). lia. }
  assert (Hc : data_count (csp_ι init_addr ka l)
                 (t_ceil4 (term_var "l")) = klen_words l).
  { assert (Hs : inst (T := fun Σ => Term Σ ty_xlenbits)
                   (term_var "l" : Term csCtx ty_xlenbits)
                   (csp_ι init_addr ka l)
                 = SyncVal (rv_val (inst (T := fun Σ => Term Σ ty_xlenbits)
                   (term_var "l" : Term csCtx ty_xlenbits)
                   (csp_ι init_addr ka l))))
      by reflexivity.
    rewrite (data_count_ceil4_eq _ _ Hs); [reflexivity|].
    change (data_count _ (term_var "l")) with (N.to_nat (bv.bin l)). lia. }
  pose proof (Nat.div_mod (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
  apply (ni_of_cells
           (regs' := map (concretize_reg_q (csp_ι init_addr ka l)) csp_regs)
           (cs := concretize_data (csp_ι init_addr ka l)
                    (init_addr + 144) csp_data));
    [ | | | | ].
  { (* clear of the code: P256_N right after it, k by the premise *)
    unfold clear_of_code, check_scalar_ptr_mem, check_scalar_ptr_blocks, blk_end.
    cbn [blocks blk_addr blk_words].
    change (length cs_instrs) with 36%nat.
    constructor; [|constructor; [|constructor]]; cbn [blk_addr blk_words];
      rewrite repeat_length; cbn [N.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  { exact Hrange. }
  { (* the registers: ra's value is p + 144 *)
    apply perm_of_eq. cbn. rewrite bv.of_N_add. reflexivity. }
  { (* D12: the statement's cells are exactly the generator's *)
    apply perm_of_eq.
    unfold csp_data. cbn [concretize_data].
    change (data_count _ (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
    change (bv.bin (rv_val (inst (term_var "k") (csp_ι init_addr ka l))))
      with (bv.bin (@bv.of_N xlenbits ka)).
    rewrite Hka Hc.
    unfold cells, check_scalar_ptr_mem, check_scalar_ptr_blocks.
    cbn [blocks List.map concat blk_addr blk_words].
    rewrite !words_at_repeat. rewrite !app_nil_r. cbn [pub_spec].
    reflexivity. }
  apply (gen_prog_noninterferent "p" _ csp_regs (asn.formula formula_true) 144 csp_data cs_instrs 40
           (asn.formula formula_true) (csp_ι init_addr ka l) init_addr).
  - reflexivity.
  - repeat constructor.
  - apply Prelude.nodup_fixed. reflexivity.
  - intros Σ' H'. iPureIntro. split; exact I.
  - (* data_ok *)
    unfold csp_data. cbn [data_ok].
    change (data_count _ (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
    change (data_count _ (term_val ty_xlenbits (bv.of_N 32))) with 32%nat.
    change (bv.bin (rv_val (inst (term_var "k") (csp_ι init_addr ka l))))
      with (bv.bin (@bv.of_N xlenbits ka)).
    rewrite Hka Hc.
    change (data_count _ (term_var "l")) with (N.to_nat (bv.bin l)).
    unfold klen_words in *.
    repeat split; try reflexivity; unfold maxAddr, minAddr in *; lia.
  - (* the layout: two runs, P256_N after the code and k at ka *)
    unfold csp_data. cbn [concretize_data].
    change (data_count _ (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
    change (bv.bin (rv_val (inst (term_var "k") (csp_ι init_addr ka l))))
      with (bv.bin (@bv.of_N xlenbits ka)).
    rewrite Hka Hc.
    rewrite !concretize_run_map app_nil_r.
    rewrite <- (app_nil_r (data_run ka (klen_words l) false)).
    change (data_run (init_addr + 144) 8 false ++ data_run ka (klen_words l) false ++ [])
      with (data_runs [(init_addr + 144, 8%nat, false); (ka, klen_words l, false)]%N).
    change (length cs_instrs) with 36%nat.
    apply data_layout_runs.
    + apply List.Forall_cons; [cbn -[lenAddr]; lia|]. apply List.Forall_cons; [cbn -[lenAddr klen_words]; lia|]. apply List.Forall_nil.
    + apply FOP_cons; [apply List.Forall_cons; [cbn -[lenAddr klen_words]; lia|]; apply List.Forall_nil|].
      apply FOP_cons; [apply List.Forall_nil|]. apply FOP_nil.
  - change (length cs_instrs) with 36%nat. lia.
  - exact csp_valid.
Qed.
