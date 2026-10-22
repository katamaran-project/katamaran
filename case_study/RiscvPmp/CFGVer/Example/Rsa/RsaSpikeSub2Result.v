(* ========================================================================= *)
(* Example/Rsa/RsaSpikeSub2Result.v -- PLAN-rsa.md Phase 1, spike S1b: a     *)
(* caller that is itself a function, end to end.  HEAVY half.                *)
(*                                                                           *)
(*  1. rsa_spike_sub2 is a valid block: its own VC, br_i31_sub a block        *)
(*     inside it carrying S1a's validity (RsaSpikeSubResult.sub_valid), the  *)
(*     exit r public by its precondition (seg_exit_sync_pub);               *)
(*  2. the whole program's contract is valid, the caller a block on its     *)
(*     first instruction;                                                    *)
(*  3. ONE application of GenProg.gen_prog_noninterferent.                   *)
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
     RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSub
     RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSubResult
     RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSub2.
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

(* ---- 1. rsa_spike_sub2 IS A VALID BLOCK --------------------------------- *)

(* sub2_annot, typed: br_i31_sub at index 20 carries S1a's validity *)
Definition sub2_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) =>
              MkAnnotInstrV nil ins nil
                (if Nat.eqb i 20 then Some (MkBlkAnnotV subBlk sub_valid) else None))
    (List.combine (List.seq 0 (length sub2_instrs)) sub2_instrs).

Lemma sub2_erase : List.map eraseV sub2_annotV = sub2_annot.
Proof.
  unfold sub2_annotV, sub2_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma sub2_code : List.map aiv_instr sub2_annotV = sub2_instrs.
Proof.
  unfold sub2_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length sub2_instrs)) sub2_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma sub2_valid : blkValid sub2Blk.
Proof.
  exact (blkValid_of_seg_at (term_var "q") (term_var "q") (term_var "r") sub2_instrs 40 sub2_regs
           _ sub2_post sub2_annotV (fun v iota => eq_refl)
           (fun Σ GS v iota =>
              seg_exit_sync_pub (term_var "q") (term_var "q") (term_var "r") (term_var "r")
                sub2_instrs 40 sub2_regs sub2_pre sub2_post iota v eq_refl)
           sub2_code
           (eq_ind_r (fun l => cfg_vc_loop sub2Rec l) valid_sub2 sub2_erase)).
Qed.

(* ---- 2. THE WHOLE PROGRAM'S CONTRACT IS VALID ---------------------------- *)

Definition s1b_annotV : list (AnnotInstrV blkValid) :=
  List.map (fun '(i, ins) =>
              MkAnnotInstrV nil ins nil
                (if Nat.eqb i 2 then Some (MkBlkAnnotV sub2Blk sub2_valid) else None))
    (List.combine (List.seq 0 (length s1b_instrs)) s1b_instrs).

Lemma s1b_erase : List.map eraseV s1b_annotV = s1b_annot.
Proof.
  unfold s1b_annotV, s1b_annot. rewrite List.map_map. apply List.map_ext.
  intros [i ins]. unfold eraseV. cbn.
  repeat (destruct (Nat.eqb i _)); reflexivity.
Qed.

Lemma s1b_code : List.map aiv_instr s1b_annotV = s1b_instrs.
Proof.
  unfold s1b_annotV. rewrite List.map_map.
  transitivity (List.map snd (List.combine (List.seq 0 (length s1b_instrs)) s1b_instrs)).
  - apply List.map_ext. intros [i ins]. reflexivity.
  - apply map_snd_combine_seq.
Qed.

Lemma s1b_valid : ValidCFGVerifierContract s1bRec.
Proof.
  apply (@ValidCFGVerifierContract_intro _ s1bRec s1b_annotV).
  - rewrite s1b_erase. exact valid_s1b.
  - exact s1b_code.
Qed.

(* ---- 3. THE STATEMENT'S OWN DATA ------------------------------------------
   S1a's two arrays, plus the callee's frame: the four words below sp. *)

Definition sub2_call_blocks (xa xb sp : N) (h : bv xlenbits) : list mem_block :=
  [ {| blk_addr := xa;      blk_words := Known h :: repeat Secret (limbs h) |}   (* a *)
  ; {| blk_addr := xb + 4;  blk_words := repeat Public (limbs h) |}             (* b's limbs *)
  ; {| blk_addr := sp - 16; blk_words := repeat Secret 4 |} ].                  (* the frame *)

Lemma sub2_call_disjoint (xa xb sp : N) (h : bv xlenbits)
    (Hab : (xa + 4 + 4 * N.of_nat (limbs h) <= xb + 4 \/ xb + 4 + 4 * N.of_nat (limbs h) <= xa)%N)
    (Haf : (xa + 4 + 4 * N.of_nat (limbs h) <= sp - 16 \/ sp <= xa)%N)
    (Hbf : (xb + 4 + 4 * N.of_nat (limbs h) <= sp - 16 \/ sp <= xb + 4)%N)
    (Hsp : (16 <= sp)%N) :
  blocks_disjoint (sub2_call_blocks xa xb sp h).
Proof.
  unfold blocks_disjoint, sub2_call_blocks, blk_end. cbn [blk_addr blk_words].
  repeat (first [apply FOP_cons | apply FOP_nil | apply List.Forall_cons | apply List.Forall_nil]).
  all: cbn [blk_addr blk_words length]; rewrite ?repeat_length; lia.
Qed.

Definition sub2_call_mem (xa xb sp : N) (h : bv xlenbits)
    (Hab : (xa + 4 + 4 * N.of_nat (limbs h) <= xb + 4 \/ xb + 4 + 4 * N.of_nat (limbs h) <= xa)%N)
    (Haf : (xa + 4 + 4 * N.of_nat (limbs h) <= sp - 16 \/ sp <= xa)%N)
    (Hbf : (xb + 4 + 4 * N.of_nat (limbs h) <= sp - 16 \/ sp <= xb + 4)%N)
    (Hsp : (16 <= sp)%N) : mem_layout :=
  {| blocks := sub2_call_blocks xa xb sp h; blocks_ok := sub2_call_disjoint xa xb sp h Hab Haf Hbf Hsp |}.

Definition sub2_call_regs (xa xb sp : N) : list reg_spec :=
  [ (A0, Known (bv.of_N xa));     (* a  *)
    (A1, Known (bv.of_N xb));     (* b  *)
    (X2, Known (bv.of_N sp));     (* sp *)
    (X1, Secret); (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret);
    (S0, Secret); (S1, Secret); (S2, Secret) ].

Definition sub2_call_ι (ia xa xb sp : N) (h : bv xlenbits) : Valuation s1bCtx :=
  [env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)]
       .["sp"∷ty_xlenbits ↦ SyncVal (bv.of_N sp)]
       .["xa"∷ty_xlenbits ↦ SyncVal (bv.of_N xa)]
       .["xb"∷ty_xlenbits ↦ SyncVal (bv.of_N xb)]
       .["h"∷ty_xlenbits ↦ SyncVal h].

(* ---- 4. THE END THEOREM, FOR EVERY HEADER h -------------------------------
   a, b and the stack at ANY addresses whose words are clear of each other
   and of the code [ia, ia + 204), the whole layout in range. *)
Lemma sub_call2_noninterferent (init_addr xa xb sp : N) (h : bv xlenbits)
    (Hh : (0 < bv.bin h < 65536)%N)
    (Hsp : (16 <= sp)%N)
    (Hab : (xa + 4 + 4 * N.of_nat (limbs h) <= xb + 4 \/ xb + 4 + 4 * N.of_nat (limbs h) <= xa)%N)
    (Haf : (xa + 4 + 4 * N.of_nat (limbs h) <= sp - 16 \/ sp <= xa)%N)
    (Hbf : (xb + 4 + 4 * N.of_nat (limbs h) <= sp - 16 \/ sp <= xb + 4)%N)
    (Hac : (xa + 4 + 4 * N.of_nat (limbs h) <= init_addr \/ init_addr + 204 <= xa)%N)
    (Hbc : (xb + 4 + 4 * N.of_nat (limbs h) <= init_addr \/ init_addr + 204 <= xb + 4)%N)
    (Hfc : (sp <= init_addr \/ init_addr + 204 <= sp - 16)%N) :
  in_range init_addr s1b_instrs (sub2_call_mem xa xb sp h Hab Haf Hbf Hsp) ->
  noninterferent_strong init_addr s1b_instrs (init_addr + 4 * N.of_nat (length s1b_instrs))
    (sub2_call_regs xa xb sp) (sub2_call_mem xa xb sp h Hab Haf Hbf Hsp).
Proof.
  intros Hrange.
  assert (Hfit : (init_addr + 204 < lenAddr)%N /\ (xa + 4 + 4 * N.of_nat (limbs h) < lenAddr)%N
                 /\ (xb + 4 + 4 * N.of_nat (limbs h) < lenAddr)%N /\ (sp < lenAddr)%N).
  { destruct Hrange as [Hc Hb].
    unfold sub2_call_mem, sub2_call_blocks, blk_end in Hb. cbn [blocks] in Hb.
    inversion Hb as [|? ? H1 Hb']; subst. inversion Hb' as [|? ? H2 Hb'']; subst.
    inversion Hb'' as [|? ? H3 _]; subst.
    cbn [blk_addr blk_words length] in H1, H2, H3. rewrite ?repeat_length in H1, H2, H3.
    change (length s1b_instrs) with 51%nat in Hc. lia. }
  destruct Hfit as (Hfit & Hfa & Hfb & Hfs).
  pose proof lenAddr_small_word as HL. change word with xlenbits in HL. change xlenbits with 32%nat in HL.
  (* the generator's data at the valuation: three pointers and the count *)
  assert (Hc : data_count (sub2_call_ι init_addr xa xb sp h).["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
                 (t_limbs (term_var "h")) = limbs h).
  { unfold data_count. cbn -[bv.add bv.shiftr bv.of_N bv.of_Z bv.sext limbs].
    rewrite (MuladdParamClose.sext_id32 h) (limbs_bv h ltac:(lia)).
    rewrite bv.bin_of_N_small; [apply Nat2N.id|].
    unfold limbs. change (bv.exp2 xlenbits) with 4294967296%N.
    rewrite N2Nat.id. apply N.div_lt_upper_bound; lia. }
  assert (Hxa : bv.bin (rv_val (inst (term_var "xa" : Term (s1bCtx ▻ "a"∷ty_xlenbits) ty_xlenbits)
                   (sub2_call_ι init_addr xa xb sp h).["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])) = xa).
  { cbn. apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N in *. lia. }
  assert (Hxb : bv.bin (rv_val (inst (t_off4 (term_var "xb") : Term (s1bCtx ▻ "a"∷ty_xlenbits) ty_xlenbits)
                   (sub2_call_ι init_addr xa xb sp h).["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])) = (xb + 4)%N).
  { cbn -[bv.add bv.of_N]. rewrite bv.of_N_add. apply bv.bin_of_N_small.
    change (bv.exp2 xlenbits) with 4294967296%N in *. lia. }
  assert (Hf : bv.bin (rv_val (inst (t_add (term_var "sp") (-16) : Term (s1bCtx ▻ "a"∷ty_xlenbits) ty_xlenbits)
                   (sub2_call_ι init_addr xa xb sp h).["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])) = (sp - 16)%N).
  { cbn -[bv.add bv.of_N bv.of_Z]. change xlenbits with 32%nat in *.
    apply N2Z.inj. f_equal.
    assert (E : @bv.add 32 (bv.of_N sp) (bv.of_Z (-16)) = bv.of_N (sp - 16)).
    { apply bv.unsigned_inj. rewrite bv.unsigned_add bv.unsigned_of_Z. unfold bv.unsigned, bv.truncz.
      rewrite !(bv.bin_of_N_small (n := 32)); try (cbn; lia).
      cbn [Z.of_nat Z.pow Pos.of_succ_nat]. rewrite Zplus_mod_idemp_r.
      rewrite Z.mod_small; [|cbn in *; lia]. lia. }
    rewrite E. apply bv.bin_of_N_small. cbn; lia. }
  (* the frame's four cells, as concretize_data spells them, are one run *)
  assert (Hfr : [((sp - 16)%N, @Secret (Val ty_word)); ((sp - 16 + 4)%N, Secret);
                 ((sp - 16 + 4 + 4)%N, Secret); ((sp - 16 + 4 + 4 + 4)%N, Secret)]
                = data_run (sp - 16) 4 false).
  { unfold data_run. cbn [seq List.map pub_spec].
    replace (sp - 16 + 4 * N.of_nat 0)%N with (sp - 16)%N by lia.
    replace (sp - 16 + 4 * N.of_nat 1)%N with (sp - 16 + 4)%N by lia.
    replace (sp - 16 + 4 * N.of_nat 2)%N with (sp - 16 + 4 + 4)%N by lia.
    replace (sp - 16 + 4 * N.of_nat 3)%N with (sp - 16 + 4 + 4 + 4)%N by lia.
    reflexivity. }
  apply (ni_of_cells
           (regs' := map (concretize_reg_q (sub2_call_ι init_addr xa xb sp h)) s1b_regs)
           (cs := concretize_data (sub2_call_ι init_addr xa xb sp h).["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
                    (init_addr + 204) s1b_data));
    [ | | | | ].
  { (* clear of the code: the three premises *)
    unfold clear_of_code, sub2_call_mem, sub2_call_blocks, blk_end. cbn [blocks blk_addr blk_words].
    change (length s1b_instrs) with 51%nat.
    repeat (first [apply List.Forall_cons | apply List.Forall_nil]).
    all: cbn [blk_addr blk_words length]; rewrite ?repeat_length; lia. }
  { exact Hrange. }
  { apply perm_of_eq. reflexivity. }
  { (* the statement's cells are exactly the generator's *)
    apply perm_of_eq. unfold s1b_data. cbn [concretize_data].
    rewrite Hxa Hxb Hc Hf. unfold cells, sub2_call_mem, sub2_call_blocks.
    cbn [blocks List.map concat blk_addr blk_words words_at val_spec_map].
    rewrite Hfr !words_at_repeat app_nil_r. reflexivity. }
  apply (gen_prog_noninterferent "q" _ s1b_regs s1b_facts 204 s1b_data s1b_instrs 10
           s1b_post (sub2_call_ι init_addr xa xb sp h) init_addr).
  - reflexivity.
  - repeat constructor.
  - apply Prelude.nodup_fixed. reflexivity.
  - (* the facts: 0 < h < 2^16 *)
    intros Σ' H'. unfold s1b_facts. cbn -[bv.ult bv.of_N].
    iSplit; (iSplit; [iPureIntro | done]).
    + apply MuladdParamClose.Z_ult. unfold bv.unsigned. replace (bv.bin bv.zero) with 0%N by reflexivity.
      apply N2Z.inj_lt. exact (proj1 Hh).
    + apply MuladdParamClose.Z_ult. unfold bv.unsigned. replace (bv.bin (bv.of_N 65536)) with 65536%N by reflexivity.
      apply N2Z.inj_lt. exact (proj2 Hh).
  - (* data_ok *)
    unfold s1b_data. cbn [data_ok]. rewrite Hxa Hxb Hc Hf.
    repeat split; try reflexivity; unfold maxAddr, minAddr in *; lia.
  - (* the layout: a's header, then three runs *)
    unfold s1b_data. cbn [concretize_data]. rewrite Hxa Hxb Hc Hf.
    rewrite !concretize_run_map. cbn [val_spec_map]. rewrite Hfr.
    rewrite <- (app_nil_r (data_run (sp - 16) 4 false)).
    change (data_run (xa + 4) (limbs h) false ++ data_run (xb + 4) (limbs h) true ++ data_run (sp - 16) 4 false ++ [])
      with (data_runs [(xa + 4, limbs h, false); (xb + 4, limbs h, true); (sp - 16, 4%nat, false)]%N).
    change (length s1b_instrs) with 51%nat.
    apply data_layout_cell_cons; [lia | lia | |].
    + repeat (first [apply List.Forall_cons; [split; lia|] | apply List.Forall_nil]).
    + apply data_layout_runs.
      * repeat (first [apply List.Forall_cons; [split; lia|] | apply List.Forall_nil]).
      * repeat (first [apply FOP_cons | apply FOP_nil | apply List.Forall_cons; [lia|] | apply List.Forall_nil]).
  - change (length s1b_instrs) with 51%nat. lia.
  - exact s1b_valid.
Qed.
