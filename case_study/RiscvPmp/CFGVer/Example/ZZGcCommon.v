(* ========================================================================= *)
(* ZZGcCommon.v — THROWAWAY diagnostic support file (delete after use).       *)
(*                                                                           *)
(* Phase 1 of CFGVer/PLAN-unquantify-forward.md, Option A: an actual FORWARD  *)
(* per-step world-GC, built in the THROWAWAY probe chain rather than in       *)
(* Verifier.v.  Rationale: changing the real sexec_cfg_addr drags in          *)
(* rexec_cfg_addr and its RefineCompat instances, and the plan itself warns   *)
(* that Option A may come out SLOWER (wsubst re-traverses wco once per        *)
(* dropped variable).  Measure first, pay the refinement cost only if the     *)
(* number justifies it.                                                      *)
(*                                                                           *)
(* Unlike ZZFwdCommon's probe this is NOT additive: it really shrinks the     *)
(* world.  So the NC control changes shape -- nc_demonicv is EXPECTED to drop *)
(* here, which is the whole point.  The invariant that must still hold is     *)
(* nc_error: dropping only dead variables must not create new error nodes.    *)
(*                                                                           *)
(* Composes with ZZFwdCommon's `gc : bool` chunk GC, since the two attack     *)
(* different halves (`an` vs `encoded_instr`) and the seventh arm showed the  *)
(* chunk GC is a precondition for `encoded_instr` being droppable at all.     *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZFwdCommon.

Section FwdGC.

  Import ModalNotations.
  Import SStoreSpec (evalStoreSpec).
  Import SHeapSpec SHeapSpec.notations.
  Import asn.notations.

  (* First dead-AND-inhabited binder, with its membership proof and the
     witness we will substitute for it.  ty.inhabit returns None for
     tuple/union/record, so those are simply never dropped -- a sound, silent
     under-approximation (TypeDecl.v:960).  xlenbits is bvec, which inhabits,
     so both `an` and `encoded_instr` are covered. *)
  Fixpoint find_dead (Σ : LCtx) :
    (forall b, ctx.In b Σ -> bool) ->
    option (sigT (fun b : LVar ∷ Ty => (ctx.In b Σ * Val (type b))%type)) :=
    match Σ with
    | ctx.nil       => fun _ => None
    | ctx.snoc Σ' b =>
        fun f =>
          match @find_dead Σ' (fun y yIn => f y (ctx.in_succ yIn)) with
          | Some (existT y (yIn, v)) => Some (existT y (ctx.in_succ yIn, v))
          | None =>
              if f b ctx.in_zero
              then match ty.inhabit (type b) with
                   | Some v => Some (existT b (ctx.in_zero, v))
                   | None   => None
                   end
              else None
          end
    end.

  (* Chained single-variable drops.  Each step is an ordinary acc_subst_right
     (Worlds.v:381) -- we substitute the dead variable by an arbitrary
     inhabitant rather than removing it outright, which is exactly what makes
     this need NO new core machinery.  Fuel bounds the chain; it is decreasing
     so the Fixpoint is accepted even though `w` changes. *)
  Fixpoint gc_tri (fuel : nat) (w : World)
      (h : SHeap (wctx w)) (apc : Term (wctx w) ty_xlenbits)
      (keys : list (Term (wctx w) ty_xlenbits)) {struct fuel} :
      sigT (fun w' => Tri w w') :=
    match fuel with
    | O    => existT w tri_id
    | S fl =>
        (* `@` because Prelude's `Set Implicit Arguments` makes Σ implicit at
           use sites even though the Fixpoint binds it explicitly -- the same
           trap as count_ctx in ZZFwdCommon.v. *)
        match @find_dead (wctx w)
                (fun b bIn =>
                   match occurs_check bIn h, occurs_check bIn apc,
                         occurs_check bIn keys, occurs_check bIn (wco w) with
                   | Some _, Some _, Some _, Some _ => true
                   | _, _, _, _                     => false
                   end) with
        | None => existT w tri_id
        | Some (existT b (bIn, v)) =>
            let t : Term (wctx w - b) (type b) := term_val (type b) v in
            let ζ : Sub (wctx w) (wctx w - b) := sub_single bIn t in
            match gc_tri fl (@wsubst w (name b) (type b) bIn t)
                    (subst h ζ) (subst apc ζ) (subst keys ζ) with
            | existT w'' ν => existT w'' (tri_cons (name b) t ν)
            end
        end
    end.

  Fixpoint ctx_len (Σ : LCtx) : nat :=
    match Σ with
    | ctx.nil       => O
    | ctx.snoc Σ' _ => S (ctx_len Σ')
    end.

  (* The chunk GC as a first-class SHeapSpec step (the seventh arm ran it as a
     side-effect of the counting probe; here it has to stand on its own). *)
  (* NOTE the unused STerm argument: with only `forall w, SHeapSpec Unit w`,
     `w` appears solely in the RETURN type, so `Set Implicit Arguments` leaves
     it EXPLICIT and the bind notation cannot elaborate the call. Mentioning w
     in an argument type makes it strict-implicit, which is exactly why
     gc_probe/gc_dead_roots take their roots explicitly. *)
  Definition chunk_gc (gc : bool) :
    forall w : World, STerm ty_xlenbits w -> SHeapSpec Unit w :=
    fun w _ POST h => POST w acc_refl tt (gc_heap gc h).

  (* The SHeapSpec combinator.  It lives at SHeapSpec level, not SPureSpec,
     because the liveness set depends on the heap (PLAN §3).  tbl/exits are
     extra roots that no existing combinator knows about, so they are passed
     in explicitly by the caller -- which is why the call site is in the
     executor rather than buried in Monads.v. *)
  Definition gc_dead_roots :
    forall w, SInstrTable w -> SExitTable w -> STerm ty_xlenbits w ->
              SHeapSpec Unit w :=
    fun w tbl exits apc POST h =>
      let keys : list (Term (wctx w) ty_xlenbits) :=
        List.app (List.map fst tbl) exits in
      match gc_tri (ctx_len (wctx w)) w h apc keys with
      | existT w' ν =>
          SymProp.assume_triangular ν
            (POST w' (acc_triangular ν) tt (subst h (sub_triangular ν)))
      end.

  (* Verbatim copy of Verifier.v:275-292 with the chunk GC (`gc`, from
     ZZFwdCommon) and the world GC (`wgc`) both switchable, so the four
     combinations are one recompile apart. *)
  Fixpoint sexec_cfg_addr_gc (gc : bool) (wgc : bool) (fuel : nat) :
    forall w, SInstrTable w -> SExitTable w -> STerm ty_xlenbits w ->
              SHeapSpec (STerm ty_xlenbits) w :=
    fun w tbl exits apc =>
      let emsg (s : string) : SHeapSpec (STerm ty_xlenbits) w :=
        error (fun _ => amsg.mk {| debug_string_pathcondition := wco w;
                                   debug_string_message := s |}) in
      match fuel with
      | O    => emsg "sexec_cfg_addr_gc: out of fuel"
      | S n' =>
          angelic_binary
            (if is_exit exits apc then pure apc
             else emsg "sexec_cfg_addr_gc: exit branch chosen but pc matches no declared exit term")
            (match lookup_instr tbl apc with
             | None   => emsg "sexec_cfg_addr_gc: no instruction key matches this pc term"
             | Some i =>
                 ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
                 (* chunk GC: drop the retained encodes_instr chunks *)
                 ⟨ θ2 ⟩ _    <- chunk_gc gc apc' ;;
                 (* world GC: substitute away everything now forward-dead *)
                 ⟨ θ3 ⟩ _    <- (if wgc
                                 then gc_dead_roots
                                        (persist_itable (θ1 ∘ θ2) tbl)
                                        (persist_etable (θ1 ∘ θ2) exits)
                                        (persist__term apc' θ2)
                                 else pure tt) ;;
                 sexec_cfg_addr_gc gc wgc n'
                   (persist_itable (θ1 ∘ θ2 ∘ θ3) tbl)
                   (persist_etable (θ1 ∘ θ2 ∘ θ3) exits)
                   (persist__term apc' (θ2 ∘ θ3))
             end)
      end.

  Definition sexec_triple_addr_gc {Σ : LCtx} (gc wgc : bool)
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
      ⟨ θ3 ⟩ na <- sexec_cfg_addr_gc gc wgc fuel
                     (subst_itable ζ tbl) (subst_etable ζ exits) a2 ;;
      let δ3 := persist δ1 (θ2 ∘ θ3) in
      consume ens δ3.["an"∷ty_xlenbits ↦ na].

  Definition scfg_verification_condition_gc {Σ : LCtx} (gc wgc : bool)
    (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
    (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits))
    (fuel : nat)
    (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
    forall w : World, 𝕊 w :=
    fun w =>
      SHeapSpec.run (sexec_triple_addr_gc gc wgc req tbl exits fuel ens (w := w)).

End FwdGC.

Definition CFG_VC_triple_gc {Σ} (gc wgc : bool)
  (p     : Term Σ ty_xlenbits)
  (exits : list (Term Σ ty_xlenbits))
  (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
  (i  : list AST)
  (fl : nat) :=
  scfg_verification_condition_gc (Σ := Σ) gc wgc
    (extend_to_minimal_pre P) (table_of_list p 0 i) exits fl
    (asn.formula (formula_bool (term_val ty.bool true))) wnil.

(* node census, for the nc_error safety control and the nc_demonicv win *)
Definition zzn_gc_nc (gc wgc : bool) (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (CFG_VC_triple_gc gc wgc p exits P i fl)).
