(* ========================================================================= *)
(* Example/Rsa/RsaSpikeSubResult.v -- PLAN-rsa.md Phase 1, spike S1a: a      *)
(* FUNCTION CALL as a block, end to end.  HEAVY half.                        *)
(*                                                                           *)
(* Three validity steps, innermost first, then ONE application of the        *)
(* generic bridge GenProg.gen_prog_noninterferent:                           *)
(*  1. the word loop is a valid block, from its loop VC (the loop rule);     *)
(*  2. br_i31_sub is a valid block, from its own VC with the loop inside --  *)
(*     an ordinary segment whose exit is the return address r, public by its *)
(*     precondition (seg_exit_sync_pub);                                     *)
(*  3. the whole program's contract is valid, the callee a block on its     *)
(*     first instruction.                                                   *)
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
     RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN
     RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSub.
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

(* ---- 1. THE WORD LOOP IS A VALID BLOCK ------------------------------------ *)

Lemma sub_loop_valid : blkValid (lnBlk lnSub (@sub_scratch)).
Proof.
  exact (blkValid_of_loop_seg (term_var "q") (term_var "q")
           (ln_instrs lnSub) (ln_exit lnSub) (ln_fuel lnSub) []
           (ln_inv lnSub (@sub_scratch)) (ln_post lnSub (@sub_scratch))
           (List.map liftV (ln_annot lnSub))
           (fun v iota => eq_refl) eq_refl valid_sub_loop).
Qed.

(* ---- 2. br_i31_SUB IS A VALID BLOCK -------------------------------------- *)

(* sub_annot, typed: the loop block at index 11 carries its validity *)
Definition sub_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) =>
              MkAnnotInstrV (if Nat.eqb i 25 then sub_hand_back else nil) ins
                (if Nat.eqb i 10 then sub_seeds else nil)
                (if Nat.eqb i 11 then Some (MkBlkAnnotV _ sub_loop_valid) else None))
    (List.combine (List.seq 0 (length sub_instrs)) sub_instrs).

Lemma sub_erase : List.map eraseV sub_annotV = sub_annot.
Proof.
  unfold sub_annotV, sub_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma sub_code : List.map aiv_instr sub_annotV = sub_instrs.
Proof.
  unfold sub_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length sub_instrs)) sub_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

(* the exit r is public: the leading secLeak r of the precondition *)
Lemma sub_valid : blkValid subBlk.
Proof.
  exact (blkValid_of_seg_at (term_var "q") (term_var "q") (term_var "r") sub_instrs 30 sub_regs
           _ sub_post sub_annotV (fun v iota => eq_refl)
           (fun Σ GS v iota =>
              seg_exit_sync_pub (term_var "q") (term_var "q") (term_var "r") (term_var "r")
                sub_instrs 30 sub_regs sub_pre sub_post iota v eq_refl)
           sub_code
           (eq_ind_r (fun l => cfg_vc_loop subRec l) valid_sub sub_erase)).
Qed.

(* ---- 3. THE WHOLE PROGRAM'S CONTRACT IS VALID ---------------------------- *)

Definition s1a_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) =>
              MkAnnotInstrV nil ins nil
                (if Nat.eqb i 2 then Some (MkBlkAnnotV subBlk sub_valid) else None))
    (List.combine (List.seq 0 (length s1a_instrs)) s1a_instrs).

Lemma s1a_erase : List.map eraseV s1a_annotV = s1a_annot.
Proof.
  unfold s1a_annotV, s1a_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma s1a_code : List.map aiv_instr s1a_annotV = s1a_instrs.
Proof.
  unfold s1a_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length s1a_instrs)) s1a_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma s1a_valid : ValidCFGVerifierContract s1aRec.
Proof.
  apply (@ValidCFGVerifierContract_intro _ s1aRec s1a_annotV).
  - rewrite s1a_erase. exact valid_s1a.
  - exact s1a_code.
Qed.

(* ---- 4. THE STATEMENT'S OWN DATA ------------------------------------------
   Kernel blocks, not regions: the two arrays sit behind POINTERS, anywhere
   in range and clear of the code and of each other. *)

(* an i31 integer with header h has (h + 31) / 32 limbs *)
Definition limbs (h : bv xlenbits) : nat := N.to_nat ((bv.bin h + 31) / 32).

(* a at xa: its header (public, = h) and its limbs (secret); b's limbs at
   xb + 4 (public; b's header is not read, so not owned) *)
Definition sub_call_blocks (xa xb : N) (h : bv xlenbits) : list mem_block :=
  [ {| blk_addr := xa;     blk_words := Known h :: repeat Secret (limbs h) |}
  ; {| blk_addr := xb + 4; blk_words := repeat Public (limbs h) |} ].

Lemma sub_call_disjoint (xa xb : N) (h : bv xlenbits)
    (H : (xa + 4 + 4 * N.of_nat (limbs h) <= xb + 4 \/ xb + 4 + 4 * N.of_nat (limbs h) <= xa)%N) :
  blocks_disjoint (sub_call_blocks xa xb h).
Proof.
  unfold blocks_disjoint, sub_call_blocks, blk_end. cbn [blk_addr blk_words].
  constructor; [constructor; [|constructor] | constructor; constructor].
  cbn [blk_addr blk_words length]. rewrite !repeat_length. lia.
Qed.

Definition sub_call_mem (xa xb : N) (h : bv xlenbits)
    (H : (xa + 4 + 4 * N.of_nat (limbs h) <= xb + 4 \/ xb + 4 + 4 * N.of_nat (limbs h) <= xa)%N)
    : mem_layout :=
  {| blocks := sub_call_blocks xa xb h; blocks_ok := sub_call_disjoint xa xb h H |}.

Definition sub_call_regs (xa xb : N) : list reg_spec :=
  [ (A0, Known (bv.of_N xa));     (* a *)
    (A1, Known (bv.of_N xb));     (* b *)
    (X1, Secret); (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret) ].

(* ---- 5. PROOF SIDE: the generator's valuation and its limb count ---------- *)

Definition sub_call_ι (ia xa xb : N) (h : bv xlenbits) : Valuation s1aCtx :=
  [env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["xa"∷ty_xlenbits ↦ SyncVal (bv.of_N xa)]
       .["xb"∷ty_xlenbits ↦ SyncVal (bv.of_N xb)]
       .["h"∷ty_xlenbits ↦ SyncVal h].

Lemma limbs_bv (h : bv xlenbits) : (bv.bin h < 65536)%N ->
  bv.add (bv.of_Z (-1)) (bv.shiftr (bv.add (bv.of_N 63) h) (@bv.of_N 5 5))
  = @bv.of_N xlenbits (N.of_nat (limbs h)).
Proof.
  intros Hh. unfold limbs. change xlenbits with 32%nat in *. apply bv.unsigned_inj.
  rewrite bv.unsigned_add MuladdParamClose.unsigned_shiftr_c bv.unsigned_add bv.unsigned_of_Z.
  unfold bv.truncz.
  replace (bv.unsigned (@bv.of_N 5 5)) with 5%Z by reflexivity.
  replace (bv.unsigned (@bv.of_N 32 63)) with 63%Z by reflexivity.
  rewrite N2Nat.id. unfold bv.unsigned.
  rewrite (bv.bin_of_N_small (n := 32)); [|cbn; apply N.div_lt_upper_bound; lia].
  cbn [Z.of_nat Z.pow Pos.of_succ_nat Pos.pow Pos.mul Pos.succ Pos.iter].
  rewrite (Z.mod_small (63 + _)); [|lia].
  rewrite (Z.mod_small ((63 + _) / _)); [|split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]].
  rewrite Zplus_mod_idemp_l. change (2 ^ 5)%Z with 32%Z.
  (* (h + 63) / 32 = (h + 31) / 32 + 1 *)
  replace (63 + Z.of_N (bv.bin h))%Z with ((Z.of_N (bv.bin h) + 31) + 1 * 32)%Z by lia.
  rewrite Z.div_add; [|lia].
  replace (-1 + ((Z.of_N (bv.bin h) + 31) / 32 + 1))%Z with ((Z.of_N (bv.bin h) + 31) / 32)%Z by lia.
  rewrite N2Z.inj_div. change (Z.of_N 32) with 32%Z. rewrite N2Z.inj_add. change (Z.of_N 31) with 31%Z.
  apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; cbn; lia.
Qed.

(* data_layout_runs with one cell in front: an i31 integer's HEADER word
   before its limb run (the statement's a-block) *)
Lemma data_layout_cell_cons (start : N) (ncode : nat) (a : N) s (rs : list (N * nat * bool)) :
  (a + 4 <= lenAddr)%N ->
  (a + 4 <= start \/ start + 4 * N.of_nat ncode <= a)%N ->
  Forall (fun '(off, m, _) => (off + 4 * N.of_nat m <= lenAddr)%N /\
            (a + 4 <= off \/ off + 4 * N.of_nat m <= a)%N) rs ->
  data_layout_ok start ncode (data_runs rs) ->
  data_layout_ok start ncode ((a, s) :: data_runs rs).
Proof.
  intros Ha Hc Hr [Hf Hp].
  pose proof lenAddr_small_word as HL. change word with xlenbits in HL. change xlenbits with 32%nat in HL.
  assert (Hb : bv.bin (cell_addr (a, s)) = a).
  { unfold cell_addr. cbn [fst]. apply bv.bin_of_N_small. change word with 32%nat. lia. }
  split.
  - constructor; [rewrite Hb; lia | exact Hf].
  - constructor; [|exact Hp].
    apply List.Forall_forall. intros b Hin.
    unfold data_runs in Hin. apply in_concat in Hin as [l [Hl Hin]].
    apply in_map_iff in Hl as [[[o2 m2] p2] [<- Hin2]].
    rewrite List.Forall_forall in Hr. destruct (Hr _ Hin2) as [Hm2 Hsep].
    pose proof (data_run_in o2 m2 p2 b Hm2 Hin) as Ib.
    unfold data_cell_sep. rewrite Hb. lia.
Qed.

(* ---- 6. THE END THEOREM, FOR EVERY HEADER h -------------------------------
   a and b at ANY addresses xa, xb whose words are clear of each other and of
   the code [ia, ia + 124), the whole layout in range. *)
Lemma sub_call_noninterferent (init_addr xa xb : N) (h : bv xlenbits)
    (Hh : (0 < bv.bin h < 65536)%N)
    (Hab : (xa + 4 + 4 * N.of_nat (limbs h) <= xb + 4 \/ xb + 4 + 4 * N.of_nat (limbs h) <= xa)%N)
    (Hac : (xa + 4 + 4 * N.of_nat (limbs h) <= init_addr \/ init_addr + 124 <= xa)%N)
    (Hbc : (xb + 4 + 4 * N.of_nat (limbs h) <= init_addr \/ init_addr + 124 <= xb + 4)%N) :
  in_range init_addr s1a_instrs (sub_call_mem xa xb h Hab) ->
  noninterferent_strong init_addr s1a_instrs (init_addr + 4 * N.of_nat (length s1a_instrs))
    (sub_call_regs xa xb) (sub_call_mem xa xb h Hab).
Proof.
  intros Hrange.
  assert (Hfit : (init_addr + 124 < lenAddr)%N /\ (xa + 4 + 4 * N.of_nat (limbs h) < lenAddr)%N
                 /\ (xb + 4 + 4 * N.of_nat (limbs h) < lenAddr)%N).
  { destruct Hrange as [Hc Hb].
    unfold sub_call_mem, sub_call_blocks, blk_end in Hb. cbn [blocks] in Hb.
    inversion Hb as [|? ? H1 Hb']; subst. inversion Hb' as [|? ? H2 _]; subst.
    cbn [blk_addr blk_words length] in H1, H2. rewrite ?repeat_length in H1, H2.
    change (length s1a_instrs) with 31%nat in Hc. lia. }
  destruct Hfit as (Hfit & Hfa & Hfb).
  pose proof lenAddr_small_word as HL. change word with xlenbits in HL. change xlenbits with 32%nat in HL.
  (* the generator's data at the valuation: the two pointers and the count *)
  assert (Hc : data_count (sub_call_ι init_addr xa xb h)
                 (t_limbs (term_var "h")) = limbs h).
  { unfold data_count. cbn -[bv.add bv.shiftr bv.of_N bv.of_Z bv.sext limbs].
    rewrite (MuladdParamClose.sext_id32 h) (limbs_bv h ltac:(lia)).
    rewrite bv.bin_of_N_small; [apply Nat2N.id|].
    unfold limbs. change (bv.exp2 xlenbits) with 4294967296%N.
    rewrite N2Nat.id. apply N.div_lt_upper_bound; lia. }
  assert (Hxa : bv.bin (rv_val (inst (term_var "xa" : Term s1aCtx ty_xlenbits)
                   (sub_call_ι init_addr xa xb h))) = xa).
  { cbn. apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N in *. lia. }
  assert (Hxb : bv.bin (rv_val (inst (t_off4 (term_var "xb") : Term s1aCtx ty_xlenbits)
                   (sub_call_ι init_addr xa xb h))) = (xb + 4)%N).
  { cbn -[bv.add bv.of_N]. rewrite bv.of_N_add. apply bv.bin_of_N_small.
    change (bv.exp2 xlenbits) with 4294967296%N in *. lia. }
  apply (ni_of_cells
           (regs' := map (concretize_reg_q (sub_call_ι init_addr xa xb h)) s1a_regs)
           (cs := concretize_data (sub_call_ι init_addr xa xb h)
                    (init_addr + 124) s1a_data));
    [ | | | | ].
  { (* clear of the code: the two premises *)
    unfold clear_of_code, sub_call_mem, sub_call_blocks, blk_end. cbn [blocks blk_addr blk_words].
    change (length s1a_instrs) with 31%nat.
    constructor; [|constructor; [|constructor]]; cbn [blk_addr blk_words length];
      rewrite repeat_length; lia. }
  { exact Hrange. }
  { apply perm_of_eq. reflexivity. }
  { (* the statement's cells are exactly the generator's *)
    apply perm_of_eq. unfold s1a_data. cbn [concretize_data].
    rewrite Hxa Hxb Hc. unfold cells, sub_call_mem, sub_call_blocks.
    cbn [blocks List.map concat blk_addr blk_words words_at].
    rewrite !words_at_repeat. rewrite !app_nil_r. cbn [pub_spec].
    reflexivity. }
  apply (gen_prog_noninterferent "q" _ s1a_regs s1a_facts 124 s1a_data s1a_instrs 10
           s1a_post (sub_call_ι init_addr xa xb h) init_addr).
  - reflexivity.
  - repeat constructor.
  - apply Prelude.nodup_fixed. reflexivity.
  - (* the facts: 0 < h < 2^16 *)
    intros Σ' H'. unfold s1a_facts. cbn -[bv.ult bv.of_N].
    iSplit; (iSplit; [iPureIntro | done]).
    + match goal with |- ?P /\ ?P => cut P; [intros HP; exact (conj HP HP)|] end. apply MuladdParamClose.Z_ult. unfold bv.unsigned. replace (bv.bin bv.zero) with 0%N by reflexivity.
      apply N2Z.inj_lt. exact (proj1 Hh).
    + match goal with |- ?P /\ ?P => cut P; [intros HP; exact (conj HP HP)|] end. apply MuladdParamClose.Z_ult. unfold bv.unsigned. replace (bv.bin (bv.of_N 65536)) with 65536%N by reflexivity.
      apply N2Z.inj_lt. exact (proj2 Hh).
  - (* data_ok *)
    unfold s1a_data. cbn [data_ok]. rewrite Hxa Hxb Hc.
    repeat split; try reflexivity; unfold maxAddr, minAddr in *; lia.
  - (* the layout: a's header, then two runs *)
    unfold s1a_data. cbn [concretize_data]. rewrite Hxa Hxb Hc.
    rewrite !concretize_run_map app_nil_r.
    rewrite <- (app_nil_r (data_run (xb + 4) (limbs h) true)).
    change (data_run (xa + 4) (limbs h) false ++ data_run (xb + 4) (limbs h) true ++ [])
      with (data_runs [(xa + 4, limbs h, false); (xb + 4, limbs h, true)]%N).
    change (length s1a_instrs) with 31%nat.
    apply data_layout_cell_cons; [lia | lia | |].
    + apply List.Forall_cons; [split; lia|]. apply List.Forall_cons; [split; lia|]. apply List.Forall_nil.
    + apply data_layout_runs.
      * apply List.Forall_cons; [split; lia|]. apply List.Forall_cons; [split; lia|]. apply List.Forall_nil.
      * apply FOP_cons; [apply List.Forall_cons; [lia|]; apply List.Forall_nil|].
        apply FOP_cons; [apply List.Forall_nil|]. apply FOP_nil.
  - change (length s1a_instrs) with 31%nat. lia.
  - exact s1a_valid.
Qed.
