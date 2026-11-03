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
From Katamaran Require RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamVC.

(* A block-free annotation (a loop body) as a typed list *)
Definition liftV (ai : AnnotInstr) : AnnotInstrV blkValid :=
  MkAnnotInstrV (ai_ghost_before ai) (ai_instr ai) (ai_ghost_after ai) None.

(* ---- 1. THE LOOP BLOCKS ARE VALID ---------------------------------------- *)

Lemma l1_valid : blkValid l1Blk.
Proof.
  exact (blkValid_of_loop_seg (term_var "q") (term_var "q") l1_instrs 16 12 [] l1_inv l1_post
           (List.map liftV l1_annot) (fun v iota => eq_refl) eq_refl valid_l1).
Qed.

Lemma l2_valid : blkValid l2Blk.
Proof.
  exact (blkValid_of_loop_seg (term_var "q") (term_var "q") l2_instrs 52 30 [] l2_inv l2_post
           (List.map liftV l2_annot) (fun v iota => eq_refl) eq_refl valid_l2).
Qed.

(* ---- 2. THE WHOLE FUNCTION: TYPED ANNOTATIONS AND THE SEAL --------------- *)

Definition cs_blockV (i : nat) : option (BlkAnnotV blkValid) :=
  if Nat.eqb i 9 then Some (MkBlkAnnotV l1Blk l1_valid)
  else if Nat.eqb i 20 then Some (MkBlkAnnotV l2Blk l2_valid)
  else None.

Definition cs_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) => MkAnnotInstrV (cs_before i) ins (cs_after i) (cs_blockV i))
    (List.combine (List.seq 0 (length cs_instrs)) cs_instrs).

Lemma map_snd_combine_seq {A} (l : list A) k :
  List.map snd (List.combine (List.seq k (length l)) l) = l.
Proof. revert k; induction l as [|x l IH]; intros k; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma cs_erase : List.map eraseV cs_annotV = cs_annot.
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
Qed.

(* ---- 3. THE GENERATOR'S SIDE, FOR EVERY klen --------------------------- *)

(* ⌈klen/4⌉, k's word count *)
Definition klen_words (l : bv xlenbits) : nat := ((N.to_nat (bv.bin l) + 3) / 4)%nat.

(* the contract's parameters: the load address, klen, and k's address --
   right after P256_N (the arrays' values are chosen by the bridge) *)
Definition cs_ι (ia : N) (l : bv xlenbits) : Valuation csCtx :=
  [env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["l"∷ty_xlenbits ↦ SyncVal l]
       .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N (ia + 176))].

(* THE GENERATOR'S SPECS (proof side -- the statement below uses its own
   shallow data, PLAN-spec-layer D12, and check_scalar_cells proves the two
   agree) *)
Definition cs_mem_specs (ia : N) (l : bv xlenbits) : list mem_cell :=
  concretize_data (cs_ι ia l) (ia + 144) cs_data.

Lemma cs_count_l (ia : N) (l : bv xlenbits) :
  data_count (cs_ι ia l) (term_var "l") = N.to_nat (bv.bin l).
Proof. reflexivity. Qed.

Lemma cs_count_ceil (ia : N) (l : bv xlenbits) : (bv.bin l + 3 < 4294967296)%N ->
  data_count (cs_ι ia l) (t_ceil4 (term_var "l")) = klen_words l.
Proof.
  intros Hl.
  assert (Hc : inst (T := fun Σ => Term Σ ty_xlenbits)
                 (term_var "l" : Term csCtx ty_xlenbits) (cs_ι ia l)
               = SyncVal (rv_val (inst (T := fun Σ => Term Σ ty_xlenbits)
                 (term_var "l" : Term csCtx ty_xlenbits) (cs_ι ia l))))
    by reflexivity.
  rewrite (data_count_ceil4_eq (cs_ι ia l) _ Hc); [reflexivity|].
  rewrite cs_count_l. lia.
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
  cbn. f_equal; f_equal; lia.
Qed.

(* ---- 4. THE STATEMENT'S OWN DATA (PLAN-spec-layer D12/D14) ------------- *)

(* code: init_addr .. init_addr+143 (36 instructions); the data follows. *)
Definition check_scalar_data (l : bv xlenbits) : list region :=
  [ Bytes 32 Secret                 (* P256_N,      at init_addr+144 *)
  ; Bytes (bv.bin l) Secret ].      (* k[0 .. l-1], at init_addr+176 *)

Definition check_scalar_regs (ia : N) (l : bv xlenbits) : list reg_spec :=
  [ (A0, Known (bv.of_N (ia + 176)));     (* k             *)
    (A1, Known l);                        (* klen          *)
    (X1, Known (bv.of_N (ia + 144)));     (* ra = the exit *)
    (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret) ].

Lemma klen_words_N (l : bv xlenbits) : N.of_nat (klen_words l) = ((bv.bin l + 3) / 4)%N.
Proof.
  unfold klen_words. rewrite Nat2N.inj_div. rewrite Nat2N.inj_add. rewrite N2Nat.id. reflexivity.
Qed.

(* D12: the statement's cells are exactly the generator's. *)
Lemma check_scalar_cells (ia : N) (l : bv xlenbits) : (bv.bin l + 3 < 4294967296)%N ->
  cells (compile (ia + 4 * N.of_nat (length cs_instrs)) (check_scalar_data l))
  = cs_mem_specs ia l.
Proof.
  intros Hl.
  assert (Hk : N.to_nat ((bv.bin l + 3) / 4) = klen_words l)
    by (rewrite <- klen_words_N; apply Nat2N.id).
  unfold cs_mem_specs, cs_data. cbn [concretize_data].
  rewrite cs_count_ceil; [|exact Hl].
  change (data_count (cs_ι ia l) (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
  unfold compile, cells, check_scalar_data. cbn [blocks place region_words region_size].
  cbn [List.map concat blk_addr blk_words].
  rewrite !words_at_repeat. rewrite Hk.
  change (length cs_instrs) with 36%nat.
  rewrite app_nil_r.
  cbn [val_spec_map pub_spec].
  reflexivity.
Qed.

(* THE END THEOREM: the whole check_scalar, at every klen whose data fits,
   at every load address -- one application of the generic bridge. *)
Lemma check_scalar_param_noninterferent (init_addr : N) (l : bv xlenbits) :
  fits (init_addr + 4 * N.of_nat (length cs_instrs)) (check_scalar_data l) ->
  noninterferent_strong init_addr cs_instrs (init_addr + 4 * N.of_nat (length cs_instrs))
    (check_scalar_regs init_addr l)
    (compile (init_addr + 4 * N.of_nat (length cs_instrs)) (check_scalar_data l)).
Proof.
  intros Hfit0.
  assert (Hl : length cs_instrs = 36) by (vm_compute; reflexivity).
  assert (Hfit : (init_addr + 176 + 4 * N.of_nat (klen_words l) < lenAddr)%N).
  { unfold fits, layout_size in Hfit0. unfold check_scalar_data in Hfit0. simpl in Hfit0.
    rewrite repeat_length in Hfit0. rewrite N2Nat.id in Hfit0. rewrite klen_words_N. lia. }
  assert (Hlb : (bv.bin l + 3 < 4294967296)%N).
  { rewrite klen_words_N in Hfit. unfold lenAddr in Hfit. change (2 ^ 12)%N with 4096%N in Hfit.
    pose proof (N.div_mod (bv.bin l + 3) 4 ltac:(lia)).
    pose proof (N.mod_lt (bv.bin l + 3) 4 ltac:(lia)). lia. }
  apply (ni_of_cells (regs' := map (concretize_reg_q (cs_ι init_addr l)) cs_regs)
                     (cs := cs_mem_specs init_addr l));
    [ apply compile_clear; lia | apply compile_in_range; [lia | assumption]
    | apply perm_of_eq; cbn; rewrite bv.of_N_add; reflexivity
    | apply perm_of_eq; apply check_scalar_cells; exact Hlb | ].
  apply (gen_prog_noninterferent "p" _ cs_regs (asn.formula formula_true) 144 cs_data cs_instrs 40
           (asn.formula formula_true) (cs_ι init_addr l) init_addr).
  - reflexivity.
  - repeat constructor.
  - apply Prelude.nodup_fixed. reflexivity.
  - intros Σ' H'. iPureIntro. split; exact I.
  - apply cs_data_ok. unfold maxAddr, minAddr in *. lia.
  - (* the layout: one run, P256_N then k, right after the code *)
    pose proof (Nat.div_mod (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
    pose proof (Nat.mod_upper_bound (N.to_nat (bv.bin l) + 3) 4 ltac:(lia)).
    unfold cs_data. cbn [concretize_data].
    change (data_count _ (t_ceil4 (term_val ty_xlenbits (bv.of_N 32)))) with 8%nat.
    rewrite cs_count_ceil; [|exact Hlb].
    rewrite !concretize_run_map app_nil_r.
    rewrite <- (app_nil_r (data_run (init_addr + 144 + 4 * N.of_nat 8) (klen_words l) false)).
    change (data_run (init_addr + 144) 8 false
              ++ data_run (init_addr + 144 + 4 * N.of_nat 8) (klen_words l) false ++ [])
      with (data_runs [(init_addr + 144, 8%nat, false);
                       (init_addr + 144 + 4 * N.of_nat 8, klen_words l, false)]%N).
    rewrite Hl.
    apply data_layout_runs.
    + apply List.Forall_cons; [cbn -[lenAddr]; lia|]. apply List.Forall_cons; [cbn -[lenAddr klen_words]; lia|]. apply List.Forall_nil.
    + apply FOP_cons; [apply List.Forall_cons; [cbn -[lenAddr klen_words]; lia|]; apply List.Forall_nil|].
      apply FOP_cons; [apply List.Forall_nil|]. apply FOP_nil.
  - rewrite Hl. lia.
  - exact cs_valid.
Qed.
