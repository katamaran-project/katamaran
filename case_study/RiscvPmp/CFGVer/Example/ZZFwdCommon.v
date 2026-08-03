(* ========================================================================= *)
(* ZZFwdCommon.v — THROWAWAY diagnostic support file (delete after use).      *)
(*                                                                           *)
(* Phase 0 of CFGVer/PLAN-unquantify-forward.md: measure how many logic       *)
(* variables a FORWARD, per-step world-GC could actually drop.                *)
(*                                                                           *)
(* This is NOT the number PLAN-unquantify-gate.md's Phase B produced.  That   *)
(* one counted binders dead given the WHOLE FINISHED TREE (114 of 115 at      *)
(* N=4).  Mid-execution we cannot see the future, so a variable is droppable  *)
(* only if it is absent from the state the continuation can still read:       *)
(*                                                                           *)
(*     live(w) = fv(heap) u fv(apc) u fv(tbl) u fv(exits) u fv(wco w)         *)
(*                                                                           *)
(* fv(wco w) is the one in doubt: a freshly-demonic `an` plausibly occurs in  *)
(* the path condition via the fetch equality, which would make it FORWARD-    *)
(* LIVE even though postprocess+unquantify prove it globally dead.  So we     *)
(* measure with and without that root and report the gap.                     *)
(*                                                                           *)
(* METHOD — the counts ride out on `nc_debug`.  Rather than encode numbers    *)
(* in debug STRINGS and parse them back, the probe emits exactly k dummy      *)
(* SymProp.debug nodes at each recursion point, where k is the count for      *)
(* that step.  ZZCommon's existing `ncount` then sums them into `nc_debug`,   *)
(* which is 0 in the real executor (verified: every ZZ run to date reports    *)
(* nc_debug := 0), so it is a clean channel needing no new extraction code.   *)
(* The reported figure is therefore the SUM over all trips; divide by the     *)
(* trip count, or difference across N, to get per-trip.                       *)
(*                                                                           *)
(* The probe is purely ADDITIVE: it never shrinks a world, never substitutes, *)
(* and hands the continuation `acc_refl`.  So every other NC counter must     *)
(* come out identical to the corresponding ZZRun figure -- that is the        *)
(* control, exactly as in the Phase B measurement.                            *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZCommon.

Section FwdProbe.

  Import ModalNotations.
  Import SStoreSpec (evalStoreSpec).
  Import SHeapSpec SHeapSpec.notations.
  Import asn.notations.

  (* Count the elements of an LCtx satisfying a decidable predicate that may
     depend on the membership proof.  Mirrors env.tabulate's recursion
     (Environment.v:215) but sums instead of building an Env -- there is no
     fold over Env in the codebase. *)
  (* NOTE: `ctx.In`, not the `∈` notation -- stdpp's ElemOf wins that name
     here (Prelude exports stdpp.gmap) and the body then fails to unify. *)
  Fixpoint count_ctx (Σ : LCtx) : (forall b, ctx.In b Σ -> bool) -> N :=
    match Σ with
    | ctx.nil       => fun _ => 0%N
    | ctx.snoc Σ' b =>
        fun f =>
          (* `@` because Prelude's `Set Implicit Arguments` makes Σ implicit
             at use sites even though the Fixpoint binds it explicitly. *)
          (@count_ctx Σ' (fun y yIn => f y (ctx.in_succ yIn))
           + (if f b ctx.in_zero then 1 else 0))%N
    end.

  (* ctx.fresh renames duplicate binders to `base "." number` (Context.v:707),
     so an equality test on the raw name only ever matches the FIRST binder of
     each name.  Match on the base instead. *)
  Definition base (b : LVar ∷ Ty) : string := fst (ctx.split_at_dot (name b)).

  (* The chunk GC.  encodes_instr is duplicable (Sig.v:332) and
     heap_extractions KEEPS duplicable chunks on consume (Chunks.v:58), so
     decode matches its chunk but never removes it and each fetch's fresh
     existential is pinned forever.  Dropping the chunk between steps is an
     INCOMPLETENESS risk only, never unsoundness -- and it does not even cost
     completeness here: the chunk is needed only by its own step's decode,
     which has already run by the time we reach the recursion point, and the
     next step's fetch mints a fresh one from `a ↦ᵢ i` (retained). *)
  Definition is_encodes_instr {Σ} (c : Chunk Σ) : bool :=
    match c with
    | chunk_user encodes_instr _ => true
    | _                          => false
    end.

  Definition gc_heap {Σ} (gc : bool) (h : SHeap Σ) : SHeap Σ :=
    if gc then List.filter (fun c => negb (is_encodes_instr c)) h else h.

  Fixpoint repeat_debug {Σ} (n : nat) (P : 𝕊 Σ) : 𝕊 Σ :=
    match n with
    | O    => P
    | S n' => SymProp.debug amsg.empty (repeat_debug n' P)
    end.

  (* mode 0 : |wctx w|            -- total live context, the denominator
     mode 1 : dead ignoring wco   -- upper bound on what any forward GC sees
     mode 2 : dead including wco  -- what a forward GC can SOUNDLY drop
     mode 3 : LIVE named "an"             -- name-resolved breakdown of the
     mode 4 : LIVE named "encoded_instr"     stubborn half.  Modes 3+4+5 must
     mode 5 : LIVE named neither             sum to (mode 0 - mode 2). *)
  (* NOTE: the `⊢` TYPE-quantifier notation is NOT usable in an Example file --
     Prelude exports iris.proofmode.tactics, so `⊢` parses as bi entailment.
     Spell the world quantification out instead. *)
  Definition gc_probe (gc : bool) (mode : nat) :
    forall w, SInstrTable w -> SExitTable w -> STerm ty_xlenbits w ->
              SHeapSpec Unit w :=
    fun w tbl exits apc POST h0 =>
      (* count against the POST-GC heap -- that is the state the continuation
         can actually still read. *)
      let h : SHeap (wctx w) := gc_heap gc h0 in
      let keys : list (Term (wctx w) ty_xlenbits) :=
        List.app (List.map fst tbl) exits in
      let k :=
        @count_ctx (wctx w)
          (fun b bIn =>
             let dead : bool :=
               match occurs_check bIn h, occurs_check bIn apc,
                     occurs_check bIn keys, occurs_check bIn (wco w) with
               | Some _, Some _, Some _, Some _ => true
               | _, _, _, _                     => false
               end in
             (* live-and-named-p *)
             let lnm : bool -> bool := fun p => if dead then false else p in
             match mode with
             | O    => true
             | S O  =>
                 match occurs_check bIn h, occurs_check bIn apc,
                       occurs_check bIn keys with
                 | Some _, Some _, Some _ => true
                 | _, _, _                => false
                 end
             | S (S O)             => dead
             | S (S (S O))         => lnm (String.eqb (base b) "an")
             | S (S (S (S O)))     => lnm (String.eqb (base b) "encoded_instr")
             | _                   =>
                 lnm (negb (orb (String.eqb (base b) "an")
                                (String.eqb (base b) "encoded_instr")))
             end) in
      repeat_debug (N.to_nat k) (POST w acc_refl tt h).

  (* Verbatim copy of Verifier.v:275-292 with one extra ADDITIVE line. *)
  Fixpoint sexec_cfg_addr_probe (gc : bool) (mode : nat) (fuel : nat) :
    forall w, SInstrTable w -> SExitTable w -> STerm ty_xlenbits w ->
              SHeapSpec (STerm ty_xlenbits) w :=
    fun w tbl exits apc =>
      let emsg (s : string) : SHeapSpec (STerm ty_xlenbits) w :=
        error (fun _ => amsg.mk {| debug_string_pathcondition := wco w;
                                   debug_string_message := s |}) in
      match fuel with
      | O    => emsg "sexec_cfg_addr_probe: out of fuel"
      | S n' =>
          angelic_binary
            (if is_exit exits apc then pure apc
             else emsg "sexec_cfg_addr_probe: exit branch chosen but pc matches no declared exit term")
            (match lookup_instr tbl apc with
             | None   => emsg "sexec_cfg_addr_probe: no instruction key matches this pc term"
             | Some i =>
                 ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
                 ⟨ θ2 ⟩ _    <- gc_probe gc mode (persist_itable θ1 tbl)
                                  (persist_etable θ1 exits) apc' ;;
                 sexec_cfg_addr_probe gc mode n'
                   (persist_itable (θ1 ∘ θ2) tbl) (persist_etable (θ1 ∘ θ2) exits)
                   (persist__term apc' θ2)
             end)
      end.

  (* Verbatim copies of Verifier.v:318-338, retargeted at the probe. *)
  Definition sexec_triple_addr_probe {Σ : LCtx} (gc : bool) (mode : nat)
    (req : Assertion (Σ ▻ ("a"::ty_xlenbits)))
    (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) (fuel : nat)
    (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
    forall w, SHeapSpec Unit w :=
    fun w =>
      ⟨ θ0 ⟩ δ <- demonic_ctx id Σ ;;
      ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
      let δ1 := env.snoc (persist (A := Sub Σ) δ θ1) _ a in
      ⟨ θ2 ⟩ _ <- produce req δ1 ;;
      let a2 := persist__term a θ2 in
      let ζ := persist (A := Sub Σ) δ (θ1 ∘ θ2) in
      ⟨ θ3 ⟩ na <- sexec_cfg_addr_probe gc mode fuel
                     (subst_itable ζ tbl) (subst_etable ζ exits) a2 ;;
      let δ3 := persist δ1 (θ2 ∘ θ3) in
      consume ens δ3.["an"∷ty_xlenbits ↦ na].

  Definition scfg_verification_condition_probe {Σ : LCtx} (gc : bool) (mode : nat)
    (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
    (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits))
    (fuel : nat)
    (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
    forall w : World, 𝕊 w :=
    fun w =>
      SHeapSpec.run (sexec_triple_addr_probe gc mode req tbl exits fuel ens (w := w)).

End FwdProbe.

(* Mirror of Contracts.v:109's CFG_VC_triple. *)
Definition CFG_VC_triple_probe {Σ} (gc : bool) (mode : nat)
  (p     : Term Σ ty_xlenbits)
  (exits : list (Term Σ ty_xlenbits))
  (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
  (i  : list AST)
  (fl : nat) :=
  scfg_verification_condition_probe (Σ := Σ) gc mode
    (extend_to_minimal_pre P) (table_of_list p 0 i) exits fl
    (asn.formula (formula_bool (term_val ty.bool true))) wnil.

(* baseline: no GC (the sixth arm's numbers) *)
Definition zzn_fwd_nc (mode : nat) (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (CFG_VC_triple_probe false mode p exits P i fl)).

(* with the encodes_instr chunk GC at the recursion point *)
Definition zzn_fwdgc_nc (mode : nat) (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (CFG_VC_triple_probe true mode p exits P i fl)).
