(* THROWAWAY: TERM-size (not node-count) measure over a SymProp.
   Node censuses are blind to solve_uvars re-inlining variable definitions:
   that shrinks the node count while EXPANDING the terms in surviving nodes. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZQ.

Fixpoint tsize {Σ σ} (t : Term Σ σ) {struct t} : N :=
  match t with
  | term_var _         => 1
  | term_val _ _       => 1
  | term_relval _ _    => 1
  | term_binop _ t1 t2 => 1 + tsize t1 + tsize t2
  | term_unop _ t1     => 1 + tsize t1
  | term_tuple ts      => 1 + tesize ts
  | term_union _ _ t1  => 1 + tsize t1
  | term_record _ ts   => 1 + tnesize ts
  end
with tesize {Σ σs} (ts : Env (Term Σ) σs) {struct ts} : N :=
  match ts with
  | env.nil        => 0
  | env.snoc ts' b t => tesize ts' + tsize t
  end
with tnesize {Σ Δ} (ts : NamedEnv (Term Σ) Δ) {struct ts} : N :=
  match ts with
  | env.nil        => 0
  | env.snoc ts' b t => tnesize ts' + tsize t
  end.

Fixpoint fsize {Σ} (F : Formula Σ) : N :=
  match F with
  | formula_user p ts     => 1 + tesize ts
  | formula_bool t        => 1 + tsize t
  | formula_prop _ _      => 1
  | formula_relop _ t1 t2 => 1 + tsize t1 + tsize t2
  | formula_true          => 1
  | formula_false         => 1
  | formula_and F1 F2     => fsize F1 + fsize F2
  | formula_or F1 F2      => fsize F1 + fsize F2
  | formula_propeq t1 t2  => 1 + tsize t1 + tsize t2
  | formula_secLeak t     => 1 + tsize t
  end.

(* Total size of all TERMS held in the tree. *)
Fixpoint sptsize {Σ} (s : 𝕊 Σ) : N :=
  match s with
  | SymProp.angelic_binary o1 o2 => sptsize o1 + sptsize o2
  | SymProp.demonic_binary o1 o2 => sptsize o1 + sptsize o2
  | SymProp.error _              => 0
  | SymProp.block                => 0
  | SymProp.assertk fml _ k      => fsize fml + sptsize k
  | SymProp.assumek fml k        => fsize fml + sptsize k
  | SymProp.angelicv _ k         => sptsize k
  | SymProp.demonicv _ k         => sptsize k
  | @SymProp.assert_vareq _ x σ xIn t _ k => tsize t + sptsize k
  | @SymProp.assume_vareq _ x σ xIn t k   => tsize t + sptsize k
  | SymProp.debug _ k            => sptsize k
  end.

(* (raw term size, postprocessed term size) in ONE pair so a single Eval gets both. *)
Definition zzn_ts (n : nat) : N * N :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    (sptsize (CFG_VC_triple p exits P i fl),
     sptsize (postprocess (CFG_VC_triple p exits P i fl)))).

Definition zzc_ts (n : nat) : N * N :=
  cfg_map (zzc_contract n) (fun ia p exits P i ec fl =>
    (sptsize (CFG_VC_triple p exits P i fl),
     sptsize (postprocess (CFG_VC_triple p exits P i fl)))).
