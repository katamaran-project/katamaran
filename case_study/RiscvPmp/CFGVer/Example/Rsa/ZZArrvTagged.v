(* ZZ probe (not built): the TAGGED arrv LoopN (PLAN-arrv D14-D17, Phase D'),
   measured as ZZArrvSplit.v measured Old/Amb/NV (2026-10-26): node counts of
   the raw and the postprocessed tree, then the discharge split, after one
   warm-up VC.  Prediction (diagnostics/arrv-loop-cost-drivers.md §5): 0
   surviving angelicv in the postprocessed tree, cost ≈ Old (8.6 s warm). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSub.

Fixpoint zzcnt {Σ} (p : SymProp.SymProp Σ) : nat * nat * nat * nat :=
  (* (nodes, angelic_binary, assertk, angelicv) *)
  let add4 '(a,b,c,d) '(e,f,g,h) := (Nat.add a e, Nat.add b f, Nat.add c g, Nat.add d h) in
  match p with
  | SymProp.angelic_binary o1 o2 => add4 (1,1,0,0) (add4 (zzcnt o1) (zzcnt o2))
  | SymProp.demonic_binary o1 o2 => add4 (1,0,0,0) (add4 (zzcnt o1) (zzcnt o2))
  | SymProp.assertk _ _ k => add4 (1,0,1,0) (zzcnt k)
  | SymProp.assumek _ k => add4 (1,0,0,0) (zzcnt k)
  | SymProp.angelicv _ k => add4 (1,0,0,1) (zzcnt k)
  | SymProp.demonicv _ k => add4 (1,0,0,0) (zzcnt k)
  | @SymProp.assert_vareq _ _ _ _ _ _ k => add4 (1,0,0,0) (zzcnt k)
  | @SymProp.assume_vareq _ _ _ _ _ k => add4 (1,0,0,0) (zzcnt k)
  | @SymProp.dropk _ _ _ _ k => add4 (1,0,0,0) (zzcnt k)
  | SymProp.debug _ k => add4 (1,0,0,0) (zzcnt k)
  | _ => (1,0,0,0)
  end.

(* warm-up: one untimed VC *)
Goal cfg_vc_loop subRec sub_annot.
Proof. solve_mb_vc. Qed.

Definition raw := cfg_map (lnRec lnSub (@sub_scratch))
  (fun p ex P _ fl Q => CFG_VC_loop_triple p ex P (ln_annot lnSub) fl Q).
Definition pp := cfg_map (lnRec lnSub (@sub_scratch))
  (fun p ex P _ fl Q => cfg_postprocess (CFG_VC_loop_triple p ex P (ln_annot lnSub) fl Q)).
Time Eval vm_compute in ("Tag_raw", zzcnt raw).
Time Eval vm_compute in ("Tag_pp", zzcnt pp).
Goal cfg_vc_loop (lnRec lnSub (@sub_scratch)) (ln_annot lnSub).
Proof.
  intros. Time vm_compute. Time solve_vc. let n := numgoals in idtac "Tag_GOALS" n.
  Time all: (try solve_symbase_fetch; cbn [Erasure.inst_symprop]; cbn -[Erasure.inst_symprop] in * |-).
  Time all: mb_search.
Time Qed.

(* the whole VC, warm, as RsaSpikeSub.valid_sub_loop states it *)
Goal cfg_vc_loop (lnRec lnSub (@sub_scratch)) (ln_annot lnSub).
Proof. Time solve_mb_vc. Time Qed.
