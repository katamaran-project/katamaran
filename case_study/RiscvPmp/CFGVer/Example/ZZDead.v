(* ========================================================================= *)
(* ZZDead.v — THROWAWAY diagnostic probe (delete after use).                  *)
(*                                                                           *)
(* Phase A of PLAN-unquantify-gate.md: answer "how many demonicv binders in   *)
(* the raw VC have zero occurrences?" WITHOUT porting unquantify/            *)
(* GenOccursCheck.v.  Same trick as ZZNames.v: collect LVar NAMES (not de     *)
(* Bruijn indices), so every Fixpoint here stays non-dependent -- no ctx.In   *)
(* manipulation, no Σ bookkeeping across assert_vareq's context-shrinking.    *)
(*                                                                           *)
(* Approximation direction: names are not uniquely freshened (ZZNames.v       *)
(* already established this -- it found bare `an`/`encoded_instr`, not        *)
(* `an0`/`an1`/...), so a name occurring ANYWHERE masks ALL binders of that    *)
(* name.  This UNDER-reports dead binders: it can only say "at least this      *)
(* many are dead."  A positive count is trustworthy; a near-zero count is NOT *)
(* conclusive on its own (escalate to the index-level Phase B check before     *)
(* declaring the hypothesis dead).                                           *)
(*                                                                           *)
(* Messages are NOT traversed for occurrences, and this is not an              *)
(* approximation -- it matches the real unquantify's semantics exactly.       *)
(* Checked directly in main's theories/Syntax/Messages.v: `boxMsg` ERASES the *)
(* message via the existing `Erase` typeclass (the same mechanism             *)
(* erase_symprop' uses before printing) and reboxes it as context-independent  *)
(* (`genoccurscheck_amessage := fun m => weakenInit (boxMsg m)`).  So a         *)
(* variable occurring only inside msg_heap/msg_pathcondition is STILL dead as  *)
(* far as unquantify is concerned; the original plan's "messages counted vs    *)
(* messages ignored" two-variant design is moot -- there is only one correct   *)
(* answer and it is "ignore them," now confirmed from source rather than       *)
(* assumed.                                                                  *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
From Coq Require Import Strings.String.

Import env.notations.
Import ctx.notations.

(* Generic fold over any Env, extracting LVar occurrences per element. *)
Fixpoint zz_env_fold {B : Set} {D : B -> Set} (f : forall b, D b -> list LVar)
  {Δ : Ctx B} (E : Env D Δ) : list LVar :=
  match E with
  | env.nil        => nil
  | env.snoc E' b d => zz_env_fold f E' ++ f b d
  end.

Fixpoint zz_tvars {Σ σ} (t : Term Σ σ) : list LVar :=
  match t with
  | @term_var _ l _ _  => cons l nil
  | term_val _ _       => nil
  | term_relval _ _    => nil
  | term_binop op t1 t2 => zz_tvars t1 ++ zz_tvars t2
  | term_unop op t     => zz_tvars t
  | term_tuple ts      => zz_env_fold (fun _ t => zz_tvars t) ts
  | term_union U K t   => zz_tvars t
  | term_record R ts   => zz_env_fold (fun _ t => zz_tvars t) ts
  end.

Fixpoint zz_fvars {Σ} (F : Formula Σ) : list LVar :=
  match F with
  | formula_user p ts      => zz_env_fold (fun _ t => zz_tvars t) ts
  | formula_bool t         => zz_tvars t
  | formula_prop ζ P       => zz_env_fold (fun _ t => zz_tvars t) ζ
  | formula_relop op t1 t2 => zz_tvars t1 ++ zz_tvars t2
  | formula_true           => nil
  | formula_false          => nil
  | formula_and F1 F2      => zz_fvars F1 ++ zz_fvars F2
  | formula_or F1 F2       => zz_fvars F1 ++ zz_fvars F2
  | formula_propeq t1 t2   => zz_tvars t1 ++ zz_tvars t2
  | formula_secLeak t      => zz_tvars t
  end.

Fixpoint zz_cvars {Σ} (c : Chunk Σ) : list LVar :=
  match c with
  | chunk_user p ts   => zz_env_fold (fun _ t => zz_tvars t) ts
  | chunk_ptsreg r v   => zz_tvars v
  | chunk_conj c1 c2   => zz_cvars c1 ++ zz_cvars c2
  | chunk_wand c1 c2   => zz_cvars c1 ++ zz_cvars c2
  end.

Fixpoint zz_heapvars {Σ} (h : SHeap Σ) : list LVar :=
  match h with
  | nil       => nil
  | cons c h' => zz_cvars c ++ zz_heapvars h'
  end.

(* All occurrences reachable from the tree that count as "not dead" --
   messages deliberately NOT inspected (see header).  Binder names introduced
   by angelicv/demonicv are NOT added here (they are declarations, not uses).
   Crucially mirrors ZZNames.v's zz_enames ASYMMETRY: assume_vareq's
   eliminated variable x IS counted as used (that is what "eliminated by
   assume_vareq" means -- solve_uvars only substitutes away a demonic var via
   this side), but assert_vareq's x is NOT -- an angelic equation on a
   demonic var does not eliminate it.  This is exactly why `an` survives
   (its equation is an assert_vareq, per exec_instruction_epilogue) and
   getting this backwards would silently un-flag it as dead.

   Deliberately do NOT credit the replacement term t's free variables at
   assert_vareq/assume_vareq (an earlier draft did, and it was a real bug):
   k's own type already excludes x∷σ from its context, so whatever
   substitution assume_vareq's elimination performs has ALREADY happened
   syntactically before k was built -- if t's free variables (e.g.
   encoded_instr, substituted in for a downstream use of result_fetch) are
   genuinely needed later, they show up DIRECTLY as term_var occurrences
   inside some later assertk/assumek's fml, which zz_svars's recursion into
   k already finds.  Crediting t unconditionally at the elimination site
   double-counts vacuous equations as "used" regardless of whether anything
   downstream ever needed x -- caught by comparing zz_an_count/
   zz_encoded_instr_count against the known-dead expectation before trusting
   the aggregate number. Constructor list copied verbatim from ZZNames.v's
   zz_dnames (11 constructors; pattern_match{,_var} stay commented out in our
   𝕊, matching Propositions.v:157-159). *)
Fixpoint zz_svars {Σ} (s : 𝕊 Σ) : list LVar :=
  match s with
  | SymProp.angelic_binary o1 o2 => zz_svars o1 ++ zz_svars o2
  | SymProp.demonic_binary o1 o2 => zz_svars o1 ++ zz_svars o2
  | SymProp.error msg => nil
  | SymProp.block     => nil
  | SymProp.assertk fml msg k => zz_fvars fml ++ zz_svars k
  | SymProp.assumek fml k     => zz_fvars fml ++ zz_svars k
  | SymProp.angelicv b k      => zz_svars k
  | SymProp.demonicv b k      => zz_svars k
  | @SymProp.assert_vareq _ x σ xIn t msg k => zz_svars k
  | @SymProp.assume_vareq _ x σ xIn t k     => cons x (zz_svars k)
  | SymProp.debug msg k       => zz_svars k
  end.

(* Demonic binder names (copied verbatim from ZZNames.v's zz_dnames). *)
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
  | SymProp.debug msg k       => zz_dnames k
  end.

Definition zz_notin (l : LVar) (used : list LVar) : bool :=
  negb (List.existsb (String.eqb l) used).

(* THE gate number: demonicv binder names with zero occurrences anywhere in
   the tree (formulas/terms only, messages excluded per the header note). *)
Definition zz_dead (n : nat) : list LVar :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    let s := CFG_VC_triple p exits P i fl in
    List.filter (fun l => zz_notin l (zz_svars s)) (zz_dnames s)).

Definition zz_dead_count (n : nat) : nat :=
  List.length (zz_dead n).

(* Baseline for scaling comparison: total demonicv introduced (should match
   zzn_raw_nc's nc_demonicv -- 629 at N=4 per ZZ-ARMS.md's BASELINE row). *)
Definition zz_dnames_count (n : nat) : nat :=
  List.length (cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    zz_dnames (CFG_VC_triple p exits P i fl))).

(* Direct membership counts for the two named survivors from the memory note,
   so the report doesn't need to hand-decode Ascii strings. *)
Definition zz_count_named (l : LVar) (n : nat) : nat :=
  List.count_occ String.string_dec (zz_dead n) l.

Definition zz_an_count (n : nat) : nat := zz_count_named "an" n.
Definition zz_encoded_instr_count (n : nat) : nat := zz_count_named "encoded_instr" n.

(* Distinct dead names (dedup), so the report doesn't need to hand-decode a
   duplicate-laden Ascii dump. *)
Fixpoint zz_nodup (seen : list LVar) (l : list LVar) : list LVar :=
  match l with
  | nil => nil
  | cons x xs =>
      if zz_notin x seen
      then cons x (zz_nodup (cons x seen) xs)
      else zz_nodup seen xs
  end.

Definition zz_dead_distinct (n : nat) : list LVar :=
  zz_nodup nil (zz_dead n).

(* Concrete witness support: find actual FORMULAS mentioning a given name,
   erased to the Σ-independent EFormula (Propositions.v:1819) so results from
   different tree depths (different Σ, e.g. after an assert_vareq shrinks the
   context) can be collected into one list without a dependent-typing clash.
   Skips demonicv/angelicv/assert_vareq/assume_vareq nodes themselves (they
   carry no Formula), only assertk/assumek contribute. *)
Fixpoint zz_find_fmls_with (target : LVar) {Σ} (s : 𝕊 Σ) : list EFormula :=
  match s with
  | SymProp.angelic_binary o1 o2 => zz_find_fmls_with target o1 ++ zz_find_fmls_with target o2
  | SymProp.demonic_binary o1 o2 => zz_find_fmls_with target o1 ++ zz_find_fmls_with target o2
  | SymProp.error msg => nil
  | SymProp.block     => nil
  | SymProp.assertk fml msg k =>
      (if zz_notin target (zz_fvars fml) then nil else cons (erase_formula fml) nil)
      ++ zz_find_fmls_with target k
  | SymProp.assumek fml k =>
      (if zz_notin target (zz_fvars fml) then nil else cons (erase_formula fml) nil)
      ++ zz_find_fmls_with target k
  | SymProp.angelicv b k => zz_find_fmls_with target k
  | SymProp.demonicv b k => zz_find_fmls_with target k
  | @SymProp.assert_vareq _ x σ xIn t msg k => zz_find_fmls_with target k
  | @SymProp.assume_vareq _ x σ xIn t k     => zz_find_fmls_with target k
  | SymProp.debug msg k       => zz_find_fmls_with target k
  end.

Definition zz_show_an (n : nat) : list EFormula :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    zz_find_fmls_with "an" (CFG_VC_triple p exits P i fl)).
