(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarParamResult.v -- BearSSL check_scalar,     *)
(* the WHOLE function at every klen: validity + seal; the end theorem.      *)
(*                                                                           *)
(* The trusted statement fixes the layout the generator lays out: code at   *)
(* init_addr, P256_N's 32 bytes right after it (8 words), k right after     *)
(* those (⌈klen/4⌉ words), ra = the exit = init_addr + 144.  klen is ANY    *)
(* value whose bytes fit in memory; every byte of k and P256_N is private. *)
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
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamInstrs
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop2
     RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParam.
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
From Katamaran Require RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamVC.

(* A block-free annotation (a loop body) as a typed list *)
Definition liftV (ai : AnnotInstr) : AnnotInstrV blkValid :=
  MkAnnotInstrV (ai_ghost_before ai) (ai_instr ai) (ai_ghost_after ai) None
    (if ai_loop ai then true else false).

(* ---- 1. THE LOOP BLOCKS ARE VALID ---------------------------------------- *)

Lemma l1_valid : blkValid l1Blk.
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q") l1_instrs 16 12 [] l1_inv l1_post
           (List.map liftV l1_annot) (fun v iota => eq_refl) eq_refl valid_l1).
Qed.

Lemma l2_valid : blkValid l2Blk.
Proof.
  exact (blkValid_of_seg (term_var "q") (term_var "q") l2_instrs 52 30 [] l2_inv l2_post
           (List.map liftV l2_annot) (fun v iota => eq_refl) eq_refl valid_l2).
Qed.

(* ---- 2. THE WHOLE FUNCTION: TYPED ANNOTATIONS AND THE SEAL --------------- *)

Definition cs_blockV (i : nat) : option (BlkAnnotV blkValid) :=
  if Nat.eqb i 9 then Some (MkBlkAnnotV l1Blk l1_valid)
  else if Nat.eqb i 20 then Some (MkBlkAnnotV l2Blk l2_valid)
  else None.

Definition cs_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) => MkAnnotInstrV (cs_before i) ins (cs_after i) (cs_blockV i) false)
    (List.combine (List.seq 0 (length cs_instrs)) cs_instrs).

Lemma map_snd_combine_seq {A} (l : list A) k :
  List.map snd (List.combine (List.seq k (length l)) l) = l.
Proof. revert k; induction l as [|x l IH]; intros k; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma cs_erase : List.map (eraseV cs) cs_annotV = cs_annot.
Proof.
  unfold cs_annotV, cs_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV, cs_blockV, cs_block. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma cs_code : List.map aiv_instr cs_annotV = cs_instrs.
Proof.
  unfold cs_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length cs_instrs)) cs_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma cs_valid : ValidCFGVerifierContract cs.
Proof.
  apply (@ValidCFGVerifierContract_intro _ cs cs_annotV).
  - rewrite cs_erase. exact CheckScalarParamVC.valid_cs.
  - exact cs_code.
  - unfold cs_annotV. apply List.Forall_map, List.Forall_forall. intros [i ins] _. reflexivity.
Qed.

(* ---- 3. THE END THEOREM, FOR EVERY klen ---------------------------------- *)

(* ⌈klen/4⌉, k's word count *)
Definition klen_words (l : bv xlenbits) : nat := ((N.to_nat (bv.bin l) + 3) / 4)%nat.

Definition cs_ι (ia : N) (l : bv xlenbits) : Valuation (csCtx ▻ "a"∷ty_xlenbits) :=
  [env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["l"∷ty_xlenbits ↦ SyncVal l]
       .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N (ia + 176))]
       .["a"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].

(* THE TRUSTED SPECS: k's pointer and klen, public; the contract's own
   register specs concretized at the load address (ra = the exit); the data
   as the generator lays it out *)
Definition cs_reg_specs (ia : N) (l : bv xlenbits) : list reg_spec :=
  (A0, true, Some (bv.of_N (ia + 176))) :: (A1, true, Some l) :: map (concretize_reg ia) cs_regs.
Definition cs_mem_specs (ia : N) (l : bv xlenbits) : list mem_full_spec :=
  concretize_data (cs_ι ia l) (ia + 144) cs_data.

Lemma cs_count_l (ia : N) (l : bv xlenbits) :
  data_count (cs_ι ia l) (term_var "l") = N.to_nat (bv.bin l).
Proof. reflexivity. Qed.

Lemma cs_count_ceil (ia : N) (l : bv xlenbits) : (bv.bin l + 3 < 4294967296)%N ->
  data_count (cs_ι ia l) (t_ceil4 (term_var "l")) = klen_words l.
Proof.
  intros Hl.
  assert (Hc : inst (T := fun Σ => Term Σ ty_xlenbits)
                 (term_var "l" : Term (csCtx ▻ "a"∷ty_xlenbits) ty_xlenbits) (cs_ι ia l)
               = SyncVal (rv_val (inst (T := fun Σ => Term Σ ty_xlenbits)
                 (term_var "l" : Term (csCtx ▻ "a"∷ty_xlenbits) ty_xlenbits) (cs_ι ia l))))
    by reflexivity.
  rewrite (data_count_ceil4_eq (cs_ι ia l) _ Hc); [reflexivity|].
  rewrite cs_count_l. lia.
Qed.

Lemma cs_mem_len (ia : N) (l : bv xlenbits) : (bv.bin l + 3 < 4294967296)%N ->
  length (cs_mem_specs ia l) = (8 + klen_words l)%nat.
Proof.
  intros Hl. unfold cs_mem_specs, cs_data.
  cbn [concretize_data]. rewrite !length_app !length_map !length_seq.
  rewrite cs_count_ceil; [|exact Hl].
  change (data_count (cs_ι ia l) (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
  cbn [length]. lia.
Qed.

Lemma cs_data_ok (ia : N) (l : bv xlenbits) :
  (ia + 176 + 4 * N.of_nat (klen_words l) <= maxAddr)%N ->
  data_ok (cs_ι ia l) (ia + 144) cs_data.
Proof.
  intros Hfit.
  assert (Hl : (bv.bin l + 3 < 4294967296)%N).
  { unfold klen_words, maxAddr, minAddr, lenAddr in *.
    pose proof (Nat.div_mod (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
    pose proof (Nat.mod_upper_bound (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)). lia. }
  pose proof (Nat.div_mod (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
  unfold cs_data. cbn [data_ok].
  change (data_count (cs_ι ia l) (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
  change (data_count (cs_ι ia l) (term_val ty_xlenbits (bv.of_N 32))) with 32%nat.
  rewrite cs_count_l cs_count_ceil; [|exact Hl].
  unfold klen_words in *.
  repeat split; try reflexivity; try (unfold maxAddr, minAddr in *; lia).
  cbn. f_equal. f_equal. lia.
Qed.

(* THE END THEOREM: the whole check_scalar, at every klen whose data fits,
   at every load address. *)
Lemma check_scalar_param_noninterferent (init_addr : N) (l : bv xlenbits) :
  (init_addr + 176 + 4 * N.of_nat (klen_words l) < lenAddr)%N ->
  noninterferent_strong init_addr cs_instrs (init_addr + 144)%N
    (cs_reg_specs init_addr l) (cs_mem_specs init_addr l).
Proof.
  intros Hfit γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  assert (Hl : length cs_instrs = 36) by (vm_compute; reflexivity).
  assert (Hlb : (bv.bin l + 3 < 4294967296)%N).
  { unfold klen_words, lenAddr in *.
    pose proof (Nat.div_mod (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
    pose proof (Nat.mod_upper_bound (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)). lia. }
  eapply (@cfg_instrs_endToEnd_with_memory γ1 γ2 γ1' μ1 μ2 μ1' cs_instrs
    (init_addr + 144)%N n ws csCtx
    ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
          .["l"∷ty_xlenbits ↦ SyncVal l]
          .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N (init_addr + 176))])
    _ HpubReg (map mem_full_to_spec (cs_mem_specs init_addr l)) HpubMem
    cs cs_valid eq_refl init_addr).
  - reflexivity.
  - apply (seg_exit_table_ok _ _ init_addr 144). reflexivity.
  - (* HDataAddrs, by construction *)
    intros i spec Hi.
    change (map mem_full_to_spec (cs_mem_specs init_addr l))
      with (mem_full_to_spec <$> cs_mem_specs init_addr l) in Hi.
    rewrite list_lookup_fmap in Hi.
    destruct (cs_mem_specs init_addr l !! i) as [[[a pub] o]|] eqn:E; [|discriminate].
    injection Hi as <-. rewrite Hl.
    exact (concretize_data_addrs (cs_ι init_addr l) cs_data (init_addr + 144) i _ E).
  - (* ImplPre *)
    intros Σ' GS'.
    iIntros "(Hregs & Hmem & Hpriv & #Hinv)".
    set (ι0 := [env].["p"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]
                    .["a"∷ty_xlenbits ↦ SyncVal (@bv.of_N xlenbits init_addr)]
               : Valuation (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits)).
    iPoseProof (gen_implpre (cs_reg_specs init_addr l) ι0 HpubReg
                  ltac:(apply Prelude.nodup_fixed; reflexivity)
                  HInitReg1 HInitReg2 with "Hregs") as "Hpre".
    cbn [cs_reg_specs gen_pre List.fold_right asn.interpret].
    iDestruct "Hpre" as "[HA0 [HA1 Hregs]]".
    pose proof (gen_pre_rel_concretize (Σ := Σ') cs_regs init_addr (SyncVal (@bv.of_N xlenbits init_addr))) as Hcz.
    rewrite -Hcz.
    assert (Ha : inst (T := fun Σ => Term Σ ty_xlenbits) (t_add (term_var "p") 144) (cs_ι init_addr l)
                 = SyncVal (@bv.of_N xlenbits (init_addr + 144))).
    { cbn -[bv.of_N bv.of_Z bv.add]. f_equal. rewrite -bv.of_N_add. reflexivity. }
    iPoseProof (@gen_implpre_data _ _ _ (cs_ι init_addr l) μ1 μ2 cs_data
                  (t_add (term_var "p") 144) (init_addr + 144)%N Ha
                  (cs_data_ok init_addr l ltac:(unfold maxAddr, minAddr; lia))
                  HInitMem1 HInitMem2 with "Hmem") as "Hdata".
    assert (Hp : inst (T := fun Σ => Term Σ ty_xlenbits)
                   (term_var "p" : Term (["p"∷ty_xlenbits] ▻ "a"∷ty_xlenbits) ty_xlenbits) ι0
                 = inst (T := fun Σ => Term Σ ty_xlenbits)
                   (term_var "p" : Term (csCtx ▻ "a"∷ty_xlenbits) ty_xlenbits) (cs_ι init_addr l))
      by (cbn; reflexivity).
    iPoseProof (bi.equiv_entails_1_1 _ _
                  (gen_regs_at_inst _ _ ι0 (cs_ι init_addr l) cs_regs Hp) with "Hregs") as "Hregs".
    unfold cs_ι in *.
    cbn [extend_to_minimal_pre cfg_precondition cs gen_seg_contract asn.interpret cs_pre].
    cbn -[gen_data_at gen_regs_at bv.of_N bv.of_Z bv.add bv.unsigned].
    iFrame "Hpriv Hinv Hdata Hregs".
    assert (P7 : (bv.unsigned (@bv.of_N xlenbits init_addr) + Z.of_N (4 * N.of_nat 36) <= Z.of_N lenAddr)%Z).
    { rewrite data_unsigned_of_N_small; [unfold lenAddr in *; lia|unfold lenAddr in *; lia]. }
    iSplitR; [iSplit; [iPureIntro; reflexivity|done]|].
    iSplitR; [iSplit; [iPureIntro; exact P7|done]|].
    iSplitL "HA0"; [cbn; iExact "HA0"|].
    iSplitR; [iSplit; [iPureIntro; exact I|done]|].
    iSplitL "HA1"; [cbn; iExact "HA1"|].
    repeat iSplit; try done; iPureIntro; first [assumption | exact I].
  - rewrite List.map_length cs_mem_len; [|exact Hlb]. rewrite Hl. lia.
  - exact Hmem1.
  - exact Hmem2.
  - exact γ1curpriv.
  - exact γ2curpriv.
  - exact γ1pc.
  - exact γ2pc.
  - exact steps1.
  - exact Htrace.
Qed.
