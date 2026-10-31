(* ========================================================================= *)
(* Example/Rsa/RsaCcopyGateResult.v -- PLAN-rsa.md GATE 2, end to end.       *)
(* HEAVY half of RsaCcopyGate.v.                                            *)
(*                                                                           *)
(* Three validity steps, innermost first (the RsaSpikeSubResult template),  *)
(* then ONE application of GenProg.gen_prog_noninterferent:                 *)
(*  1. br_ccopy's loop is a valid block, from its loop VC;                   *)
(*  2. br_ccopy is a valid block, from its own VC with the loop inside, its *)
(*     exit the return address r, public by its precondition;               *)
(*  3. the harness's contract is valid, br_ccopy a block on its first        *)
(*     instruction, the word ⇄ byte view ghosts around the call.            *)
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
     RiscvPmp.CFGVer.GenProg
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose
     RiscvPmp.CFGVer.Example.Rsa.RsaCcopy
     RiscvPmp.CFGVer.Example.Rsa.RsaCcopyGate.
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

(* A block-free annotation as a typed list; erases back by conversion. *)
Definition liftV (ai : AnnotInstr) : AnnotInstrV blkValid :=
  MkAnnotInstrV (ai_ghost_before ai) (ai_instr ai) (ai_ghost_after ai) None.

Lemma map_snd_combine_seq {A} (l : list A) k :
  List.map snd (List.combine (List.seq k (length l)) l) = l.
Proof. revert k; induction l as [|x l IH]; intros k; cbn; [reflexivity | f_equal; apply IH]. Qed.

(* ---- 1. br_ccopy's LOOP IS A VALID BLOCK --------------------------------- *)

Lemma ccl_loop_valid : blkValid (cclBlk "vs" "dv").
Proof.
  exact (blkValid_of_loop_seg (term_var "q") (term_var "q")
           ccl_instrs 40 14 [] (ccl_inv "vs" "dv") (ccl_post "vs" "dv")
           (List.map liftV (ccl_annot "vs" "dv"))
           (fun v iota => eq_refl) eq_refl valid_ccl_loop).
Qed.

(* ---- 2. br_ccopy IS A VALID BLOCK ---------------------------------------- *)

Definition ccf_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) =>
              MkAnnotInstrV (if Nat.eqb i 13 then ccf_glue true "vs" "dv" else nil) ins
                (if Nat.eqb i 2 then ccf_seeds "vs" "dv" else nil)
                (if Nat.eqb i 3 then Some (MkBlkAnnotV _ ccl_loop_valid) else None))
    (List.combine (List.seq 0 (length ccopy_instrs)) ccopy_instrs).

Lemma ccf_erase : List.map eraseV ccf_annotV = ccf_annot "vs" "dv".
Proof.
  unfold ccf_annotV, ccf_annot, ccf_annot_g. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma ccf_code : List.map aiv_instr ccf_annotV = ccopy_instrs.
Proof.
  unfold ccf_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length ccopy_instrs)) ccopy_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

(* the exit r is public: the leading secLeak r of the precondition *)
Lemma ccf_valid : blkValid (ccfBlk "vs" "dv").
Proof.
  exact (blkValid_of_seg_at (term_var "q") (term_var "q") (term_var "r") ccopy_instrs 12 ccf_regs
           _ (ccf_post "vs" "dv") ccf_annotV (fun v iota => eq_refl)
           (fun Σ GS v iota =>
              seg_exit_sync_pub (term_var "q") (term_var "q") (term_var "r") (term_var "r")
                ccopy_instrs 12 ccf_regs (ccf_pre "vs" "dv") (ccf_post "vs" "dv") iota v eq_refl)
           ccf_code
           (eq_ind_r (fun l => cfg_vc_loop (ccfRec "vs" "dv") l) valid_ccf ccf_erase)).
Qed.

(* ---- 3. THE HARNESS'S CONTRACT IS VALID ----------------------------------- *)

Definition cg_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) =>
              MkAnnotInstrV
                (if Nat.eqb i 0 then List.app (way_in "dv") (way_in "vs")
                 else if Nat.eqb i 1 then List.app (way_back "dv" "hx" (clem_arrv_of_bytes_any "dv"))
                                                   (way_back "vs" "hy" (clem_arrv_of_bytes "vs"))
                 else nil) ins nil
                (if Nat.eqb i 2 then Some (MkBlkAnnotV (ccfBlk "vs" "dv") ccf_valid) else None))
    (List.combine (List.seq 0 (length ccf_instrs)) ccf_instrs).

Lemma cg_erase : List.map eraseV cg_annotV = cg_annot.
Proof.
  unfold cg_annotV, cg_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma cg_code : List.map aiv_instr cg_annotV = ccf_instrs.
Proof.
  unfold cg_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length ccf_instrs)) ccf_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma cg_valid : ValidCFGVerifierContract (cgRec false cg_post).
Proof.
  apply (@ValidCFGVerifierContract_intro _ (cgRec false cg_post) cg_annotV).
  - rewrite cg_erase. exact valid_cg.
  - exact cg_code.
Qed.

(* ---- 4. THE STATEMENT'S OWN DATA ------------------------------------------
   Kernel blocks: the two integers sit behind POINTERS x (dst) and y (src),
   anywhere in range and clear of the code and of each other; each is its
   header word h (PUBLIC, the same h in both) then ml SECRET limb words. *)

Definition cc_blocks (x y : N) (ml : nat) (h : bv xlenbits) : list mem_block :=
  [ {| blk_addr := x; blk_words := Known h :: repeat Secret ml |}
  ; {| blk_addr := y; blk_words := Known h :: repeat Secret ml |} ].

Lemma cc_disjoint (x y : N) (ml : nat) (h : bv xlenbits)
    (H : (x + 4 + 4 * N.of_nat ml <= y \/ y + 4 + 4 * N.of_nat ml <= x)%N) :
  blocks_disjoint (cc_blocks x y ml h).
Proof.
  unfold blocks_disjoint, cc_blocks, blk_end. cbn [blk_addr blk_words].
  constructor; [constructor; [|constructor] | constructor; constructor].
  cbn [blk_addr blk_words length]. rewrite !repeat_length. lia.
Qed.

Definition cc_mem (x y : N) (ml : nat) (h : bv xlenbits)
    (H : (x + 4 + 4 * N.of_nat ml <= y \/ y + 4 + 4 * N.of_nat ml <= x)%N) : mem_layout :=
  {| blocks := cc_blocks x y ml h; blocks_ok := cc_disjoint x y ml h H |}.

(* ctl (A0) SECRET; dst, src, the byte length 4·ml + 4 public *)
Definition cc_regs (x y : N) (ml : nat) : list reg_spec :=
  [ (A0, Secret); (A1, Known (bv.of_N x)); (A2, Known (bv.of_N y));
    (A3, Known (bv.of_N (4 * N.of_nat ml + 4))); (X1, Secret); (A4, Secret); (A5, Secret); (A6, Secret) ].

(* ---- 5. PROOF SIDE --------------------------------------------------------- *)

Definition cc_ι (ia x y : N) (ml : nat) (h : bv xlenbits) : Valuation cgCtx :=
  [env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["x"∷ty_xlenbits ↦ SyncVal (bv.of_N x)]
       .["y"∷ty_xlenbits ↦ SyncVal (bv.of_N y)]
       .["n"∷ty_xlenbits ↦ SyncVal (bv.of_N (4 * N.of_nat ml + 4))]
       .["ml"∷ty_xlenbits ↦ SyncVal (bv.of_N (N.of_nat ml))]
       .["h"∷ty_xlenbits ↦ SyncVal h].

(* the byte length the harness's registers state, as the generator spells it *)
Lemma cc_len_bv (ml : nat) : (N.of_nat ml < 536870912)%N ->
  @bv.of_N 32 (4 * N.of_nat ml + 4) = bv.add (bv.mul (bv.of_N 4) (bv.of_N (N.of_nat ml))) (bv.of_Z 4).
Proof.
  intros Hml. change (@bv.of_Z 32 4) with (@bv.of_N 32 4).
  unfold bv.mul. change (bv.bin (@bv.of_N 32 4)) with 4%N.
  rewrite bv.bin_of_N_small; [|change (bv.exp2 32) with 4294967296%N; lia].
  rewrite bv.of_N_add. reflexivity.
Qed.

(* the limb count's facts, as the harness states them *)
Lemma cc_ml_nz (ml : nat) : (0 < N.of_nat ml < 536870912)%N -> @bv.of_N 32 (N.of_nat ml) <> bv.zero.
Proof.
  intros Hml E. apply (f_equal (@bv.bin 32)) in E.
  rewrite bv.bin_of_N_small in E; [|change (bv.exp2 32) with 4294967296%N; lia].
  change (bv.bin (@bv.zero 32)) with 0%N in E. lia.
Qed.
Lemma cc_ml_lt (ml : nat) : (0 < N.of_nat ml < 536870912)%N ->
  bv.ult (@bv.of_N 32 (N.of_nat ml)) (bv.of_N 536870912).
Proof.
  intros Hml. unfold bv.ult.
  rewrite bv.bin_of_N_small; [|change (bv.exp2 32) with 4294967296%N; lia].
  change (bv.bin (@bv.of_N 32 536870912)) with 536870912%N. lia.
Qed.

(* one cell in front of a well-laid-out list *)
Lemma data_layout_cons (start : N) (ncode : nat) (c : mem_cell) cs :
  (bv.bin (cell_addr c) + 4 <= lenAddr)%N ->
  (bv.bin (cell_addr c) + 4 <= start \/ start + 4 * N.of_nat ncode <= bv.bin (cell_addr c))%N ->
  Forall (data_cell_sep c) cs ->
  data_layout_ok start ncode cs -> data_layout_ok start ncode (c :: cs).
Proof. intros H1 H2 H3 [Hf Hp]. split; [constructor; [split; assumption | exact Hf] | constructor; assumption]. Qed.

(* a cell clear of every run is clear of every cell of the runs *)
Lemma cell_sep_runs (a : N) s (rs : list (N * nat * bool)) :
  (a + 4 <= lenAddr)%N ->
  Forall (fun '(off, m, _) => (off + 4 * N.of_nat m <= lenAddr)%N /\
            (a + 4 <= off \/ off + 4 * N.of_nat m <= a)%N) rs ->
  Forall (data_cell_sep (a, s)) (data_runs rs).
Proof.
  intros Ha Hr.
  pose proof lenAddr_small_word as HL. change word with xlenbits in HL. change xlenbits with 32%nat in HL.
  assert (Hb : bv.bin (cell_addr (a, s)) = a).
  { unfold cell_addr. cbn [fst]. apply bv.bin_of_N_small. change word with 32%nat. lia. }
  apply List.Forall_forall. intros b Hin.
  unfold data_runs in Hin. apply in_concat in Hin as [l [Hl Hin]].
  apply in_map_iff in Hl as [[[o2 m2] p2] [<- Hin2]].
  rewrite List.Forall_forall in Hr. destruct (Hr _ Hin2) as [Hm2 Hsep].
  pose proof (data_run_in o2 m2 p2 b Hm2 Hin) as Ib.
  unfold data_cell_sep. rewrite Hb. lia.
Qed.

(* ---- 6. THE END THEOREM, FOR EVERY HEADER h AND LIMB COUNT ml --------------
   x and y at ANY addresses whose words are clear of each other and of the
   code [ia, ia + 64), the whole layout in range; ctl secret. *)
Lemma ccopy_noninterferent (init_addr x y : N) (ml : nat) (h : bv xlenbits)
    (Hml : (0 < N.of_nat ml < 536870912)%N)
    (Hxy : (x + 4 + 4 * N.of_nat ml <= y \/ y + 4 + 4 * N.of_nat ml <= x)%N)
    (Hxc : (x + 4 + 4 * N.of_nat ml <= init_addr \/ init_addr + 64 <= x)%N)
    (Hyc : (y + 4 + 4 * N.of_nat ml <= init_addr \/ init_addr + 64 <= y)%N) :
  in_range init_addr ccf_instrs (cc_mem x y ml h Hxy) ->
  noninterferent_strong init_addr ccf_instrs (init_addr + 4 * N.of_nat (length ccf_instrs))
    (cc_regs x y ml) (cc_mem x y ml h Hxy).
Proof.
  intros Hrange.
  assert (Hfit : (init_addr + 64 < lenAddr)%N /\ (x + 4 + 4 * N.of_nat ml < lenAddr)%N
                 /\ (y + 4 + 4 * N.of_nat ml < lenAddr)%N).
  { destruct Hrange as [Hc Hb].
    unfold cc_mem, cc_blocks, blk_end in Hb. cbn [blocks] in Hb.
    inversion Hb as [|? ? H1 Hb']; subst. inversion Hb' as [|? ? H2 _]; subst.
    cbn [blk_addr blk_words length] in H1, H2. rewrite ?repeat_length in H1, H2.
    change (length ccf_instrs) with 16%nat in Hc. lia. }
  destruct Hfit as (Hfit & Hfx & Hfy).
  pose proof lenAddr_small_word as HL. change word with xlenbits in HL. change xlenbits with 32%nat in HL.
  set (ι := cc_ι init_addr x y ml h).
  assert (Hc : data_count ι (term_var "ml") = ml).
  { unfold data_count. cbn -[bv.of_N]. rewrite bv.bin_of_N_small; [apply Nat2N.id|].
    change (bv.exp2 xlenbits) with 4294967296%N. lia. }
  assert (Hx : bv.bin (rv_val (inst (term_var "x" : Term cgCtx ty_xlenbits) ι)) = x).
  { cbn. apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N in *. lia. }
  assert (Hy : bv.bin (rv_val (inst (term_var "y" : Term cgCtx ty_xlenbits) ι)) = y).
  { cbn. apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N in *. lia. }
  assert (Hx4 : bv.bin (rv_val (inst (clem_off (term_var "x") 4 : Term cgCtx ty_xlenbits) ι)) = (x + 4)%N).
  { cbn -[bv.add bv.of_N bv.of_Z]. change (@bv.of_Z xlenbits 4) with (@bv.of_N xlenbits 4).
    rewrite bv.of_N_add. apply bv.bin_of_N_small.
    replace (Z.to_N (bv.truncz 32 4)) with 4%N by reflexivity.
    replace (bv.exp2 32) with 4294967296%N by reflexivity. lia. }
  assert (Hy4 : bv.bin (rv_val (inst (clem_off (term_var "y") 4 : Term cgCtx ty_xlenbits) ι)) = (y + 4)%N).
  { cbn -[bv.add bv.of_N bv.of_Z]. change (@bv.of_Z xlenbits 4) with (@bv.of_N xlenbits 4).
    rewrite bv.of_N_add. apply bv.bin_of_N_small.
    replace (Z.to_N (bv.truncz 32 4)) with 4%N by reflexivity.
    replace (bv.exp2 32) with 4294967296%N by reflexivity. lia. }
  apply (ni_of_cells
           (regs' := map (concretize_reg_q ι) cg_regs)
           (cs := concretize_data ι (init_addr + 64) (cg_data false)));
    [ | | | | ].
  { (* clear of the code: the two premises *)
    unfold clear_of_code, cc_mem, cc_blocks, blk_end. cbn [blocks blk_addr blk_words].
    change (length ccf_instrs) with 16%nat.
    constructor; [|constructor; [|constructor]]; cbn [blk_addr blk_words length];
      rewrite repeat_length; lia. }
  { exact Hrange. }
  { apply perm_of_eq. reflexivity. }
  { (* the statement's cells are the generator's, the headers moved to the front *)
    unfold cg_data. cbn [concretize_data].
    rewrite Hx Hy Hx4 Hy4 Hc. unfold cells, cc_mem, cc_blocks.
    cbn [blocks List.map concat blk_addr blk_words words_at].
    rewrite !words_at_repeat. rewrite !app_nil_r. cbn [pub_spec].
    cbn [val_spec_map]. apply perm_skip. symmetry. apply Permutation_middle. }
  apply (gen_prog_noninterferent "q" _ cg_regs cg_facts 64 (cg_data false) ccf_instrs 10
           cg_post ι init_addr).
  - reflexivity.
  - repeat constructor.
  - apply Prelude.nodup_fixed. reflexivity.
  - (* the facts *)
    intros Σ' H'. unfold cg_facts. cbn -[bv.ult bv.of_N bv.add bv.mul bv.of_Z].
    repeat (iSplit; [try (iSplit; [|done]); try iPureIntro|]); try (iSplit; [iPureIntro|done]).
    all: first
      [ done
      | exact I
      | (f_equal; exact (cc_len_bv ml (proj2 Hml)))
      | reflexivity
      | exact (cc_ml_nz ml Hml)
      | exact (cc_ml_lt ml Hml)
      (* a relop fact is pointwise, `P /\ P` *)
      | (split; exact (cc_ml_nz ml Hml))
      | (split; exact (cc_ml_lt ml Hml)) ].
  - (* data_ok *)
    unfold cg_data. cbn [data_ok]. rewrite Hx Hy Hx4 Hy4 Hc.
    repeat split; try reflexivity; unfold maxAddr, minAddr in *; lia.
  - (* the layout: the two headers, then two runs *)
    unfold cg_data. cbn [concretize_data]. rewrite Hx Hy Hx4 Hy4 Hc.
    rewrite !concretize_run_map app_nil_r.
    rewrite <- (app_nil_r (data_run (y + 4) ml false)).
    change (data_run (x + 4) ml false ++ data_run (y + 4) ml false ++ [])
      with (data_runs [(x + 4, ml, false); (y + 4, ml, false)]%N).
    change (length ccf_instrs) with 16%nat.
    assert (Bx : bv.bin (@bv.of_N xlenbits x) = x).
    { apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N. lia. }
    assert (By : bv.bin (@bv.of_N xlenbits y) = y).
    { apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N. lia. }
    apply data_layout_cons; unfold cell_addr; cbn [fst]; rewrite ?Bx; [lia | lia | |].
    + constructor.
      * unfold data_cell_sep, cell_addr. cbn [fst]. rewrite Bx By. lia.
      * apply cell_sep_runs; [lia|].
        apply List.Forall_cons; [split; lia|]. apply List.Forall_cons; [split; lia|]. apply List.Forall_nil.
    + apply data_layout_cons; unfold cell_addr; cbn [fst]; rewrite ?By; [lia | lia | |].
      * apply cell_sep_runs; [lia|].
        apply List.Forall_cons; [split; lia|]. apply List.Forall_cons; [split; lia|]. apply List.Forall_nil.
      * apply data_layout_runs.
        -- apply List.Forall_cons; [split; lia|]. apply List.Forall_cons; [split; lia|]. apply List.Forall_nil.
        -- apply FOP_cons; [apply List.Forall_cons; [lia|]; apply List.Forall_nil|].
           apply FOP_cons; [apply List.Forall_nil|]. apply FOP_nil.
  - change (length ccf_instrs) with 16%nat. lia.
  - exact cg_valid.
Qed.
