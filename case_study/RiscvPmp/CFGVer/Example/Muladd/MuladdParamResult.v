(* ========================================================================= *)
(* Example/Muladd/MuladdParamResult.v -- PLAN-array-invariants: the PARAMETRIC muladd*)
(* (symbolic mlen, Sym6N) -- validity + seal; end theorem.  Untracked probe.*)
(*                                                                           *)
(* The only annotation-level content is the TYPED list mb_annotV: each of    *)
(* the five blocks carries its own blkValid proof, so nothing is proved      *)
(* about the list; the light VC valid_mb is reused through mb_erase.         *)
(* ========================================================================= *)
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
     RiscvPmp.CFGVer.GenCompose
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Muladd.MuladdParam.
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
From Katamaran Require
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopDAng RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopD0
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopG RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopI RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopK
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopM RiscvPmp.CFGVer.Example.Muladd.MuladdParamTail
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamTailVC RiscvPmp.CFGVer.Example.Muladd.MuladdParamVC
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

(* A block-free annotation (a loop body) as a typed list; erases back to the
   source list by conversion (see ZZMuladdBlkResult.liftV). *)
Definition liftV (ai : AnnotInstr) : AnnotInstrV blkValid :=
  MkAnnotInstrV (ai_ghost_before ai) (ai_instr ai) (ai_ghost_after ai) None
    (if ai_loop ai then true else false).

(* ---- 1. THE LOOP BLOCKS ARE VALID ---------------------------------------- *)

Lemma dAng_valid : blkValid MuladdParamLoopDAng.dAngBlk.
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q") MuladdParamLoopD.d_instrs 24 10 []
           MuladdParamLoopDAng.d_inv_ang MuladdParamLoopDAng.d_post_ang
           (List.map liftV (MuladdParamLoopDAng.d_ang_annot_with MuladdParamLoopDAng.dAngBlk))
           (fun v iota => eq_refl) eq_refl MuladdParamLoopDAng.valid_d_ang_rec).
Qed.

Lemma d0_valid : blkValid MuladdParamLoopD0.d0Blk.
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q") MuladdParamLoopD0.d0_instrs 20 10 []
           MuladdParamLoopD0.d0_inv MuladdParamLoopD0.d0_post
           (List.map liftV (MuladdParamLoopD0.d0_annot_with MuladdParamLoopD0.d0Blk))
           (fun v iota => eq_refl) eq_refl MuladdParamLoopD0.valid_d0_rec).
Qed.

Lemma g_valid : blkValid MuladdParamLoopG.gRecBlk.
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q") MuladdParamLoopG.g_instrs 108 35 []
           MuladdParamLoopG.g_inv MuladdParamLoopG.g_post
           (List.map liftV (MuladdParamLoopG.g_annot_with MuladdParamLoopG.gRecBlk))
           (fun v iota => eq_refl) eq_refl MuladdParamLoopG.valid_g_rec).
Qed.

Lemma in_valid : blkValid (MuladdParamLoopN.lnBlk MuladdParamLoopI.lnIN (@MuladdParamLoopI.k_scratch)).
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q")
           (MuladdParamLoopN.ln_instrs MuladdParamLoopI.lnIN) (MuladdParamLoopN.ln_exit MuladdParamLoopI.lnIN)
           (MuladdParamLoopN.ln_fuel MuladdParamLoopI.lnIN) []
           (MuladdParamLoopN.ln_inv MuladdParamLoopI.lnIN (@MuladdParamLoopI.k_scratch))
           (MuladdParamLoopN.ln_post MuladdParamLoopI.lnIN (@MuladdParamLoopI.k_scratch))
           (List.map liftV (MuladdParamLoopN.ln_annot MuladdParamLoopI.lnIN (@MuladdParamLoopI.k_scratch)))
           (fun v iota => eq_refl) eq_refl MuladdParamLoopI.valid_in).
Qed.

Lemma kn_valid : blkValid (MuladdParamLoopN.lnBlk MuladdParamLoopK.lnKN (@MuladdParamLoopK.k_scratch)).
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q")
           (MuladdParamLoopN.ln_instrs MuladdParamLoopK.lnKN) (MuladdParamLoopN.ln_exit MuladdParamLoopK.lnKN)
           (MuladdParamLoopN.ln_fuel MuladdParamLoopK.lnKN) []
           (MuladdParamLoopN.ln_inv MuladdParamLoopK.lnKN (@MuladdParamLoopK.k_scratch))
           (MuladdParamLoopN.ln_post MuladdParamLoopK.lnKN (@MuladdParamLoopK.k_scratch))
           (List.map liftV (MuladdParamLoopN.ln_annot MuladdParamLoopK.lnKN (@MuladdParamLoopK.k_scratch)))
           (fun v iota => eq_refl) eq_refl MuladdParamLoopK.valid_kn).
Qed.

Lemma mt_valid : blkValid (MuladdParamLoopN.lnBlk MuladdParamLoopM.lnMT (@MuladdParamLoopM.k_scratch)).
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q")
           (MuladdParamLoopN.ln_instrs MuladdParamLoopM.lnMT) (MuladdParamLoopN.ln_exit MuladdParamLoopM.lnMT)
           (MuladdParamLoopN.ln_fuel MuladdParamLoopM.lnMT) []
           (MuladdParamLoopN.ln_inv MuladdParamLoopM.lnMT (@MuladdParamLoopM.k_scratch))
           (MuladdParamLoopN.ln_post MuladdParamLoopM.lnMT (@MuladdParamLoopM.k_scratch))
           (List.map liftV (MuladdParamLoopN.ln_annot MuladdParamLoopM.lnMT (@MuladdParamLoopM.k_scratch)))
           (fun v iota => eq_refl) eq_refl MuladdParamLoopM.valid_mt).
Qed.

(* ---- 2. THE TAIL BLOCK (G, IN, KN, MT inside) IS VALID -------------------- *)

Definition tail_blockV (i : nat) : option (BlkAnnotV blkValid) :=
  if Nat.eqb i 12 then Some (MkBlkAnnotV MuladdParamLoopG.gRecBlk g_valid)
  else if Nat.eqb i 67 then Some (MkBlkAnnotV _ in_valid)
  else if Nat.eqb i 114 then Some (MkBlkAnnotV _ kn_valid)
  else if Nat.eqb i 141 then Some (MkBlkAnnotV _ mt_valid)
  else None.

Definition tail_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) => MkAnnotInstrV (MuladdParamTail.tail_before i) ins
                               (MuladdParamTail.tail_after i) (tail_blockV i) false)
    (List.combine (List.seq 0 (length MuladdParamTail.tail_instrs)) MuladdParamTail.tail_instrs).

Lemma map_snd_combine_seq {A} (l : list A) k :
  List.map snd (List.combine (List.seq k (length l)) l) = l.
Proof. revert k; induction l as [|x l IH]; intros k; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma tail_erase : List.map (eraseV MuladdParamTail.tailRec) tail_annotV = MuladdParamTail.tail_annot.
Proof.
  unfold tail_annotV, MuladdParamTail.tail_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV, tail_blockV, MuladdParamTail.tail_block. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma tail_code : List.map aiv_instr tail_annotV = MuladdParamTail.tail_instrs.
Proof.
  unfold tail_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length MuladdParamTail.tail_instrs)) MuladdParamTail.tail_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma tail_valid : blkValid MuladdParamTail.tailBlk.
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q") MuladdParamTail.tail_instrs 636 250
           MuladdParamTail.tail_regs MuladdParamTail.tail_pre MuladdParamTail.tail_post tail_annotV
           (fun v iota => eq_refl) tail_code
           (eq_ind_r (fun l => cfg_vc MuladdParamTail.tailRec l) MuladdParamTailVC.valid_tail tail_erase)).
Qed.

(* ---- 3. THE WHOLE FUNCTION: TYPED ANNOTATIONS AND THE SEAL --------------- *)

Definition sym6_blockV (i : nat) : option (BlkAnnotV blkValid) :=
  if Nat.eqb i 84 then Some (MkBlkAnnotV MuladdParamLoopDAng.dAngBlk dAng_valid)
  else if Nat.eqb i 113 then Some (MkBlkAnnotV MuladdParamLoopD0.d0Blk d0_valid)
  else if Nat.eqb i 123 then Some (MkBlkAnnotV MuladdParamTail.tailBlk tail_valid)
  else None.

Definition sym6_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) => MkAnnotInstrV (sym6_before i) ins (sym6_after i) (sym6_blockV i) false)
    (List.combine (List.seq 0 (length sym6_instrs)) sym6_instrs).

Lemma sym6_erase : List.map (eraseV sym6) sym6_annotV = sym6_annot.
Proof.
  unfold sym6_annotV, sym6_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV, sym6_blockV, sym6_block. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma sym6_code : List.map aiv_instr sym6_annotV = sym6_instrs.
Proof.
  unfold sym6_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length sym6_instrs)) sym6_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma sym6_valid : ValidCFGVerifierContract sym6.
Proof.
  apply (@ValidCFGVerifierContract_intro _ sym6 sym6_annotV).
  - rewrite sym6_erase. exact MuladdParamVC.valid_sym6.
  - exact sym6_code.
  - unfold sym6_annotV. apply List.Forall_map, List.Forall_forall. intros [i ins] _. reflexivity.
Qed.


Definition mlenN (b : bv xlenbits) : nat := Z.to_nat ((bv.unsigned b + 31) / 32).
Definition x_off (b : bv xlenbits) : N := 1148 + 4 * N.of_nat (mlenN b).

(* ---- ImplPre helpers: bitvector normal forms ------------------------- *)
(* Every address the contract states is a bv term over M = (31 + b) >> 5;
   these rewrite each shape to `bv.of_N (an N expression)`, which then meets
   the trusted statement's `bv.of_N (init_addr + ...)` by lia. *)

Lemma unsigned_of_N_small (e : N) : (e < 4294967296)%N -> bv.unsigned (@bv.of_N xlenbits e) = Z.of_N e.
Proof. change xlenbits with 32%nat in *. intros H. unfold bv.unsigned. f_equal. apply bv.bin_of_N_small. exact H. Qed.

Lemma mlen_bounds (b : bv xlenbits) : (64 < bv.unsigned b < 65536)%Z -> (3 <= mlenN b <= 2049)%nat.
Proof.
  intros Hb. unfold mlenN. split.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id; [|apply Z.div_pos; lia]. apply Z.div_le_lower_bound; lia.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id; [|apply Z.div_pos; lia]. apply Z.div_le_upper_bound; lia.
Qed.

Lemma mlen_shiftr (b : bv xlenbits) : (64 < bv.unsigned b < 65536)%Z ->
  bv.shiftr (bv.add (bv.of_N 31) b) (@bv.of_N 5 5) = bv.of_N (N.of_nat (mlenN b)).
Proof.
  intros Hb. pose proof (mlen_bounds b Hb) as HM.
  apply bv.unsigned_inj. rewrite unsigned_of_N_small; [|lia].
  (* unfold BEFORE the change: unfolding after it re-introduces an
     xlenbits-indexed bv.unsigned that Hb (now at 32) does not match *)
  unfold mlenN in *. change xlenbits with 32%nat in *.
  rewrite MuladdParamClose.unsigned_shiftr_c bv.unsigned_add. unfold bv.truncz.
  replace (bv.unsigned (@bv.of_N 5 5)) with 5%Z by reflexivity.
  replace (bv.unsigned (@bv.of_N 32 31)) with 31%Z by reflexivity.
  rewrite nat_N_Z Z2Nat.id; [|apply Z.div_pos; lia].
  cbn [Z.of_nat Z.pow]. rewrite (Z.mod_small (31 + bv.unsigned b)); [|cbn; lia].
  rewrite Z.mod_small; [|split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; cbn; lia]].
  f_equal; lia.
Qed.

Lemma ofN_add32 (a c : N) : bv.add (@bv.of_N xlenbits a) (bv.of_N c) = bv.of_N (a + c).
Proof. now rewrite bv.of_N_add. Qed.

Lemma shiftl2_ofN (k : N) : (k < 1073741824)%N ->
  bv.shiftl (@bv.of_N xlenbits k) (@bv.of_N 5 2) = bv.of_N (4 * k).
Proof. change xlenbits with 32%nat in *.
  intros Hk. apply bv.unsigned_inj. rewrite MuladdParamClose.unsigned_shiftl_c unsigned_of_N_small; [|lia].
  rewrite unsigned_of_N_small; [|lia]. unfold bv.truncz.
  replace (bv.unsigned (@bv.of_N 5 2)) with 2%Z by reflexivity.
  cbn [Z.of_nat Z.pow]. rewrite Z.mod_small; [|cbn; lia]. lia.
Qed.

Lemma negZ_add (j k : N) (z : Z) : z = (- Z.of_N j)%Z -> (j <= k)%N -> (k < 4294967296)%N ->
  bv.add (@bv.of_Z xlenbits z) (bv.of_N k) = bv.of_N (k - j).
Proof. change xlenbits with 32%nat in *.
  intros -> Hjk Hk. apply bv.unsigned_inj.
  rewrite bv.unsigned_add bv.unsigned_of_Z !unsigned_of_N_small; [|lia|lia].
  unfold bv.truncz. cbn [Z.of_nat Z.pow]. rewrite Zplus_mod_idemp_l. rewrite Z.mod_small; lia.
Qed.

Lemma add_negZ (j k : N) (z : Z) : z = (- Z.of_N j)%Z -> (j <= k)%N -> (k < 4294967296)%N ->
  bv.add (bv.of_N k) (@bv.of_Z xlenbits z) = bv.of_N (k - j).
Proof. intros. rewrite bv.add_comm. now apply negZ_add. Qed.

Lemma ofZ_ofN32 (z : Z) (c : N) : z = Z.of_N c -> (c < 4294967296)%N -> @bv.of_Z xlenbits z = bv.of_N c.
Proof. change xlenbits with 32%nat in *.
  intros -> Hc. apply bv.unsigned_inj. rewrite bv.unsigned_of_Z unsigned_of_N_small; [|lia].
  unfold bv.truncz. cbn [Z.of_nat Z.pow]. rewrite Z.mod_small; lia.
Qed.

Lemma land_mask_nz (k : N) : (k < 4294967296)%N -> (N.modulo k 1073741824 <> 0)%N ->
  bv.land (@bv.of_N xlenbits k) (bv.of_N 1073741823) <> bv.zero.
Proof.
  intros Hk Hm E. apply (f_equal bv.unsigned) in E.
  rewrite (MuladdParamClose.unsigned_land_ones _ _ 30) in E; [|reflexivity].
  rewrite unsigned_of_N_small in E; [|lia].
  change (bv.unsigned (@bv.zero xlenbits)) with 0%Z in E.
  apply Hm. change (2 ^ Z.of_N 30)%Z with 1073741824%Z in E.
  apply N2Z.inj. rewrite N2Z.inj_mod. exact E.
Qed.

Lemma sext_idx (b : bv xlenbits) p : @bv.sext xlenbits b xlenbits p = b.
Proof. exact (MuladdParamClose.sext_id32 b p). Qed.

(* ---- 4. THE END THEOREM, FOR EVERY HEADER b ------------------------------ *)


(* the valuation the statement concretizes the data at *)
Definition sym_ι (ia : N) (b : bv xlenbits) : Valuation (symCtx ▻ "a"∷ty_xlenbits) :=
  [env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["b"∷ty_xlenbits ↦ SyncVal b]
       .["x"∷ty_xlenbits ↦ SyncVal (bv.of_N (ia + x_off b))]
       .["a"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].

(* THE TRUSTED SPECS: x's pointer, then the contract's own register specs
   concretized at the load address; the data as the generator lays it out *)
Definition sym_reg_specs (ia : N) (b : bv xlenbits) : list reg_spec :=
  (A0, true, Some (bv.of_N (ia + x_off b))) :: map (concretize_reg ia) sym_regs.
Definition sym_mem_specs (ia : N) (b : bv xlenbits) : list mem_full_spec :=
  concretize_data (sym_ι ia b) (ia + 1128) sym_data.

Lemma inst_mm2 (ia : N) (b : bv xlenbits) : (64 < bv.unsigned b < 65536)%Z ->
  inst (T := fun Σ => Term Σ ty_xlenbits) (t_mm2 (term_var "b")) (sym_ι ia b)
  = SyncVal (@bv.of_N xlenbits (N.of_nat (mlenN b) - 2)).
Proof.
  intros Hb. pose proof (mlen_bounds b Hb) as HM.
  cbn -[bv.sext bv.shiftr bv.add bv.of_N bv.of_Z].
  rewrite sext_idx (mlen_shiftr b Hb). f_equal.
  apply (negZ_add 2 (N.of_nat (mlenN b)) (-2)); [reflexivity|lia|lia].
Qed.

Lemma data_count_mm2 (ia : N) (b : bv xlenbits) : (64 < bv.unsigned b < 65536)%Z ->
  data_count (sym_ι ia b) (t_mm2 (term_var "b")) = (mlenN b - 2)%nat.
Proof.
  intros Hb. pose proof (mlen_bounds b Hb) as HM. unfold data_count. rewrite inst_mm2; [|exact Hb].
  cbn [rv_val ty.projLeft]. change xlenbits with 32%nat. rewrite bv.bin_of_N_small; [|lia]. lia.
Qed.

Lemma sym_mem_len (ia : N) (b : bv xlenbits) : (64 < bv.unsigned b < 65536)%Z ->
  length (sym_mem_specs ia b) = (2 * mlenN b + 6)%nat.
Proof.
  intros Hb. pose proof (mlen_bounds b Hb) as HM.
  unfold sym_mem_specs, sym_data.
  repeat (progress (cbn [concretize_data length]; rewrite ?length_app ?length_map ?length_seq)).
  rewrite !data_count_mm2; try exact Hb. lia.
Qed.

Lemma sym_data_ok (ia : N) (b : bv xlenbits) : (64 < bv.unsigned b < 65536)%Z ->
  (ia + 1128 + 4 * N.of_nat (2 * mlenN b + 6) <= maxAddr)%N ->
  data_ok (sym_ι ia b) (ia + 1128) sym_data.
Proof.
  intros Hb Hfit. pose proof (mlen_bounds b Hb) as HM.
  unfold sym_data. cbn [data_ok]. rewrite !data_count_mm2; try exact Hb.
  rewrite !inst_mm2; try exact Hb.
  repeat split; try (unfold maxAddr, minAddr in *; lia); try reflexivity.
  cbn. f_equal. f_equal. unfold x_off. lia.
Qed.

(* THE END THEOREM: the whole parametric muladd, for every header b of the
   family (64 < b < 65536) whose data fits, at every load address. *)
Lemma muladd_param_noninterferent (init_addr : N) (b : bv xlenbits) :
  (64 < bv.unsigned b < 65536)%Z ->
  (init_addr + 1128 + 4 * N.of_nat (2 * mlenN b + 6) < lenAddr)%N ->
  noninterferent_strong init_addr sym6_instrs (init_addr + 1128)%N
    (sym_reg_specs init_addr b) (sym_mem_specs init_addr b).
Proof.
  intros Hb Hfit γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  assert (Hl : length sym6_instrs = 282) by (vm_compute; reflexivity).
  eapply (@cfg_instrs_endToEnd_with_memory γ1 γ2 γ1' μ1 μ2 μ1' sym6_instrs
    (init_addr + 1128)%N n ws symCtx
    ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
          .["b"∷ty_xlenbits ↦ SyncVal b]
          .["x"∷ty_xlenbits ↦ SyncVal (bv.of_N (init_addr + x_off b))])
    _ HpubReg (map mem_full_to_spec (sym_mem_specs init_addr b)) HpubMem
    sym6 sym6_valid eq_refl init_addr).
  - reflexivity.
  - apply (seg_exit_table_ok _ _ init_addr 1128). reflexivity.
  - (* HDataAddrs, by construction *)
    intros i spec Hi.
    change (map mem_full_to_spec (sym_mem_specs init_addr b))
      with (mem_full_to_spec <$> sym_mem_specs init_addr b) in Hi.
    rewrite list_lookup_fmap in Hi.
    destruct (sym_mem_specs init_addr b !! i) as [[[a pub] o]|] eqn:E; [|discriminate].
    injection Hi as <-. rewrite Hl.
    exact (concretize_data_addrs (sym_ι init_addr b) sym_data I (init_addr + 1128) i _ E).
  - (* ImplPre *)
    intros Σ' GS'.
    iIntros "(Hregs & Hmem & Hpriv & #Hinv)".
    pose proof (mlen_bounds b Hb) as HM.
    set (ι0 := [env].["p"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]
                    .["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]
               : Valuation (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits)).
    iPoseProof (gen_implpre (sym_reg_specs init_addr b) ι0 HpubReg
                  ltac:(apply Prelude.nodup_fixed; reflexivity)
                  HInitReg1 HInitReg2 with "Hregs") as "Hpre".
    cbn [sym_reg_specs gen_pre List.fold_right asn.interpret].
    iDestruct "Hpre" as "[HA0 Hregs]".
    pose proof (gen_pre_rel_concretize (Σ := Σ') sym_regs init_addr (SyncVal (@bv.of_N xlenbits init_addr))) as Hcz.
    rewrite -Hcz.
    (* the data, by the generator's ImplPre *)
    assert (Ha : inst (T := fun Σ => Term Σ ty_xlenbits) (t_off (term_var "p") 1128) (sym_ι init_addr b)
                 = SyncVal (@bv.of_N xlenbits (init_addr + 1128))).
    { cbn -[bv.of_N bv.of_Z bv.add]. f_equal.
      rewrite (ofZ_ofN32 1128 1128); [|reflexivity|lia]. apply ofN_add32. }
    iPoseProof (@gen_implpre_data _ _ _ (sym_ι init_addr b) μ1 μ2 sym_data
                  (t_off (term_var "p") 1128) (init_addr + 1128)%N Ha
                  (sym_data_ok init_addr b Hb ltac:(unfold maxAddr, minAddr; lia))
                  HInitMem1 HInitMem2 with "Hmem") as "Hdata".
    assert (Hp : inst (T := fun Σ => Term Σ ty_xlenbits)
                   (term_var "p" : Term (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) ty_xlenbits) ι0
                 = inst (T := fun Σ => Term Σ ty_xlenbits)
                   (term_var "p" : Term (symCtx ▻ "a"∷ty_xlenbits) ty_xlenbits) (sym_ι init_addr b))
      by (cbn; reflexivity).
    iPoseProof (bi.equiv_entails_1_1 _ _
                  (gen_regs_at_inst _ _ ι0 (sym_ι init_addr b) sym_regs Hp) with "Hregs") as "Hregs".
    unfold sym_ι in *.
    cbn [extend_to_minimal_pre cfg_precondition sym6 gen_seg_contract asn.interpret sym_pre].
    cbn -[gen_data_at gen_regs_at bv.of_N bv.of_Z bv.add bv.shiftr bv.sext bv.land bv.unsigned bv.ult mlenN x_off].
    iFrame "Hpriv Hinv Hdata Hregs".
    (* what remains: x's pointer register, and pure facts about b and p *)
    rewrite !sext_idx (mlen_shiftr b Hb).
    rewrite (negZ_add 1 (N.of_nat (mlenN b)) (-1) eq_refl ltac:(lia) ltac:(lia)) ofN_add32.
    assert (Hfit' : (init_addr + 1128 + 4 * N.of_nat (2 * mlenN b + 6) < 4096)%N)
      by (unfold lenAddr in Hfit; exact Hfit).
    assert (P1 : b <> bv.zero).
    { intros E. apply (f_equal bv.unsigned) in E. change (bv.unsigned (@bv.zero xlenbits)) with 0%Z in E. lia. }
    assert (P2 : bv.ult (@bv.of_N xlenbits 31) b).
    { apply MuladdParamClose.Z_ult. rewrite unsigned_of_N_small; [lia|lia]. }
    assert (P3 : bv.ult (@bv.of_N xlenbits 64) b).
    { apply MuladdParamClose.Z_ult. rewrite unsigned_of_N_small; [lia|lia]. }
    assert (P4 : bv.ult b (@bv.of_N xlenbits 65536)).
    { apply MuladdParamClose.Z_ult. rewrite unsigned_of_N_small; [lia|lia]. }
    assert (P5 : bv.land (@bv.of_N xlenbits (N.of_nat (mlenN b) - 1)) (bv.of_N 1073741823) <> bv.zero).
    { apply land_mask_nz; [lia|]. rewrite N.mod_small; lia. }
    assert (P6 : bv.land (@bv.of_N xlenbits (1073741823 + N.of_nat (mlenN b))) (bv.of_N 1073741823) <> bv.zero).
    { apply land_mask_nz; [lia|].
      replace (1073741823 + N.of_nat (mlenN b))%N with ((N.of_nat (mlenN b) - 1) + 1 * 1073741824)%N by lia.
      rewrite N.Div0.mod_add N.mod_small; lia. }
    assert (P7 : (bv.unsigned (@bv.of_N xlenbits init_addr) + Z.of_N (4 * N.of_nat 282) <= Z.of_N lenAddr)%Z).
    { rewrite unsigned_of_N_small; [unfold lenAddr; lia|lia]. }
    assert (P8 : (bv.unsigned (@bv.of_N xlenbits init_addr) + 1148 <= Z.of_N lenAddr)%Z).
    { rewrite unsigned_of_N_small; [unfold lenAddr; lia|lia]. }
    iSplitR; [iSplit; [iPureIntro; reflexivity|done]|].
    iSplitR; [iSplit; [iPureIntro; exact P7|done]|].
    iSplitL "HA0"; [cbn; iExact "HA0"|].
    repeat iSplit; try done; iPureIntro; first [assumption | exact I].
  - rewrite List.map_length sym_mem_len; [|exact Hb]. rewrite Hl. lia.
  - exact Hmem1.
  - exact Hmem2.
  - exact γ1curpriv.
  - exact γ2curpriv.
  - exact γ1pc.
  - exact γ2pc.
  - exact steps1.
  - exact Htrace.
Qed.
