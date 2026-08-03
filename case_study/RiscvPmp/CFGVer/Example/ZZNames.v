(* ========================================================================= *)
(* ZZNames.v — THROWAWAY diagnostic probe (delete after use).                 *)
(*                                                                           *)
(* The four-arm experiment established that the cost driver is the LIVE       *)
(* logic-variable context, not the path condition:                           *)
(*   wco / 15, wctx held  -> 0.82x                                           *)
(*   wctx x 1.97, wco held -> 2.19x                                          *)
(* and that of the 156 demonic variables introduced per trip, only 127 are    *)
(* eliminated by assume_vareq -- so ~29/trip (about 2 per instruction) stay   *)
(* live forever.                                                             *)
(*                                                                           *)
(* This probe identifies WHICH ones.  It collects, over the whole raw tree,   *)
(*   - the name of every `demonicv` binding, and                             *)
(*   - the name eliminated by every `assume_vareq`,                           *)
(* as two lists.  Diffing the multisets offline names the survivors, which    *)
(* points straight at the code that creates them.                            *)
(*                                                                           *)
(* Both sides of every branch are concatenated, so these are multisets over   *)
(* the entire tree rather than along one path.  That is fine for identifying  *)
(* WHICH names never get eliminated: a name absent from the elimination list  *)
(* entirely cannot have been eliminated on any path.                          *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.

Fixpoint zz_dnames {Σ} (s : 𝕊 Σ) : list LVar :=
  match s with
  | SymProp.angelic_binary o1 o2 => zz_dnames o1 ++ zz_dnames o2
  | SymProp.demonic_binary o1 o2 => zz_dnames o1 ++ zz_dnames o2
  | SymProp.error msg => nil
  | SymProp.block     => nil
  | SymProp.assertk fml msg k => zz_dnames k
  | SymProp.assumek fml k     => zz_dnames k
  | SymProp.angelicv b k      => zz_dnames k
  | SymProp.demonicv b k      => cons (name b) (zz_dnames k)
  | @SymProp.assert_vareq _ x σ xIn t msg k => zz_dnames k
  | @SymProp.assume_vareq _ x σ xIn t k     => zz_dnames k
  | SymProp.debug b k         => zz_dnames k
  end.

(* Names eliminated by demonic-side unification. *)
Fixpoint zz_enames {Σ} (s : 𝕊 Σ) : list LVar :=
  match s with
  | SymProp.angelic_binary o1 o2 => zz_enames o1 ++ zz_enames o2
  | SymProp.demonic_binary o1 o2 => zz_enames o1 ++ zz_enames o2
  | SymProp.error msg => nil
  | SymProp.block     => nil
  | SymProp.assertk fml msg k => zz_enames k
  | SymProp.assumek fml k     => zz_enames k
  | SymProp.angelicv b k      => zz_enames k
  | SymProp.demonicv b k      => zz_enames k
  | @SymProp.assert_vareq _ x σ xIn t msg k => zz_enames k
  | @SymProp.assume_vareq _ x σ xIn t k     => cons x (zz_enames k)
  | SymProp.debug b k         => zz_enames k
  end.

Definition zz_dn (n : nat) : list LVar :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    zz_dnames (CFG_VC_triple p exits P i fl)).

Definition zz_en (n : nat) : list LVar :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    zz_enames (CFG_VC_triple p exits P i fl)).

Goal True. idtac "ZZ ===== DEMONICV NAMES (N=2) =====". exact I. Qed.
Eval vm_compute in (zz_dn 2).

Goal True. idtac "ZZ ===== ASSUME_VAREQ ELIMINATED NAMES (N=2) =====". exact I. Qed.
Eval vm_compute in (zz_en 2).
