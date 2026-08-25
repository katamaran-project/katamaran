# PLAN — drop dead logical variables during symbolic execution

Status: **PHASE 0 PASSED on its crux, 2026-08-25 — but only for a FUSED
mint+drop, not for the standalone drop this plan first proposed.** The blocking
obstacle is verifiably gone (`Qed` recorded below). The design changed as a
result: the drop must be *fused with the havoc's own mint* and use the freshly
minted variable as its witness. Net Σ change per trip: **zero**.

*History, because two intermediate verdicts were wrong and the reasoning is the
reusable part.* This plan was first written for a standalone drop with a dummy
witness (`term_val bv.zero`), and was then ABANDONED the same day on the grounds
that its refinement lemma is false. **The abandonment was right about the
standalone drop and wrong as a verdict on the idea.** See §"Phase 0 result".

## The problem

The `havoc_regs` abstraction lemma (`PLAN-annotinstr.md` Phase 4) removes a
loop's per-trip TERM recurrence and pays for it in surviving LOGICAL VARIABLES:
one per havoced register per trip, because a demonically produced unconstrained
value is determined by nothing and so the solver can never eliminate it. Live
`|Σ| = 15 + kn` for k havoced registers, and declared-variable count is
quadratic in lookup cost (`diagnostics/lvar-lookup-cost-drivers.md`).

Measured (`diagnostics/havoc-abstraction-payoff.md` §8): cutting k from 7 to 3
is 2.66× at n=16 and is what makes br_divrem's real 31 trips reachable at all.
But it is a FACTOR — the local exponent is still 1.269 → 1.631 → 2.015 and
rising. Taking the slope to **zero** is what would make it an exponent fix.

Each trip's `hv` binders are dead the moment the next trip's havoc consumes
their chunk. They survive only because `demonicv_prune` (`Propositions.v:1175`)
collapses on `block` and nothing else.

## The idea, and the one thing that makes it sound

Drop a dead binder mid-execution: move to `wsubst w x t` and continue there.

**A previous verdict that this is UNSOUND is WITHDRAWN** (see
`diagnostics/havoc-abstraction-payoff.md` §8.1 for the full retraction). The
argument that killed it was that the deadness side condition is about the
continuation, which is a function. That is wrong: the condition is about the
PRESENT STATE. Every term the continuation can build is built from terms that
exist now, so a variable occurring nowhere now can never reappear.

What survives from that argument is the *mechanism*, and it is what the proof
has to get past:

- `acc_subst_right` (`Worlds.v:381`) is the ONLY accessibility into a smaller
  context (every `acc_*` in `Worlds.v:320-411` enumerated) and it needs a
  witness term.
- The only two embeddings from `SymProp (w-x)` back to `SymProp w` are
  `assume_vareq` and `assert_vareq` (`Propositions.v:281,314`).
- `safe` (`Propositions.v:340,345`): `safe (demonicv x k) ι = ∀v, safe k`,
  whereas the drop yields `safe k[x:=t]` — weaker unless x is absent from k.
  `assert_vareq` instead sends the VC to `False`.

**Why the refinement obligation is nevertheless dischargeable.**
`RHeapSpec RA := □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ`
(`Refinement/Monads.v:1525`). A world-moving action instantiates the box with
`refine_four` (`refine_chunk_gc` uses `refine_T` only because `chunk_gc` sits at
`acc_refl`), which delivers the continuation relation under `assuming θ` — and
at a valuation ι with ι(x) ≠ `inst t` that `assuming` is vacuous. The way past
it is that **the concrete side carries no valuation**: `Φc : CA -> CHeap -> Prop`
is a plain Coq function, and the goal's only ι-dependence is the heap relation
`inst h ι = ch`. So

1. set ι₀ := ι[x ↦ `inst t (ι∖x)`];
2. `inst h ι₀ = inst h ι` — requires **x ∉ h**;
3. ι₀ ⊨ `wco w` — requires **x ∉ wco w**;
4. at ι₀ the equation holds, so `knowing_acc_subst_right`
   (`UnifLogic.v:1213`, already proved) turns `assuming` into `knowing` and
   hands over the continuation relation.

So the side condition is two `occurs_check`s on data and **nothing about `sΦ`**.
That is sound for the reason the whole idea rests on: the only channels by which
x could reach the continuation are the heap, the path condition, and solver
substitutions — and a solver substitution needs an equation, which lives in
`wco`. Both channels are checked.

**The check already exists with the right law.** `occurs_check`
(`Symbolic/OccursCheck.v:56`, in scope everywhere via `Base.v:68`'s mixin)
returns `Some` exactly when the variable does not occur;
`occurs_check_sound : occurs_check xIn u = Some u' → u = subst u' (sub_shift xIn)`
is precisely "does not occur ⟹ is a weakening". Instances cover Term, Formula
(`Formulas.v:301`), Chunk (`Chunks.v:188`), list, Env, pair, option and
Assertion (`Assertions.v:135`), so `SHeap = list Chunk` and
`PathCondition = list Formula` come free. `Symbolic/Monads.v:97-99,130-133`
already occurs-checks a (pathcondition, heap) pair. The unifier uses the same
check for the same purpose. Note `UnifLogic.v:1345` holds a commented-out
`assuming_acc_subst_right_left` — someone started on this corner and stopped.

## Design decisions

1. **A step of `sexec_cfg_addr`, NOT an `sexec_ghost` case.** Keep `Annot` as
   the trigger (`AnnotDropDead`) but have `sexec_cfg_addr` partition the ghost
   list and handle that constructor inline, where `tbl`/`exits`/`apc` are in
   scope. An `sexec_ghost` case cannot see them, which is the entire reason the
   original sketch did not work.
2. **Also `occurs_check` `tbl`/`exits`/`apc`** — not for soundness but for
   CORRECTNESS: transporting them substitutes `t` for `x` and would silently
   rewrite the instruction table. They never mention havoc variables, so this
   always passes; it must still be checked.
3. **Scan all of Σ, at the annotation point only.** |Σ| is 15–127 and the drop
   fires once per trip, so a full scan is affordable and collects any other dead
   binder for free. Firing every step would cost O(H·|Σ|) per step and could be
   a net loss.
4. **Witness term restricted to `ty.bvec`** (`term_val _ bv.zero`). There is no
   `Inhabited`/`defaultVal` class in the tree, so a general witness is not
   available — and every havoc variable is `ty_xlenbits`. A deliberate
   restriction, not a gap.
5. **`None` ⇒ no-op, never `error`.** A refused drop must cost completeness
   nothing: it is a missed optimisation, not a failure.

## Phases

**Phase 0 — KILL-GATE (~half a day).** Prove the refinement lemma for the
narrowing step, standalone, in a probe. Nothing else is built until it closes.
`VerifierRel.v` cannot be opened by pet at any position, so use the
restate-in-a-probe pattern; and since the definitions live inside module
functors, preamble mode cannot reach them — use position mode
`rocq_start(file=…, line=…)`, which replays through the project's real load
path. **Exit criterion:** the `Some` branch closes with only the two
`occurs_check` hypotheses. **If it needs `x ∉ sΦ` as well, STOP** and fall back
to the packing (slope 1/trip instead of 0).

**Phase 1 — symbolic side.** `AnnotDropDead`; the inline case in
`sexec_cfg_addr`; the candidate scan; k successive narrowings. **Instrument how
many drops actually FIRE** — a drop that never fires is indistinguishable from
one that works, and §8's positive controls show havoced values reaching
formulas (A5, A3) which would correctly refuse.

**Phase 2 — mirror and absorb.** Concrete side `pure tt`; re-pair
`rexec_cfg_addr`; absorb the new bind in `sound_exec_cfg_addr_myWP2`.
Known-shape work: the chunk-GC did exactly this, and Phase 4 did it for
`call_lemma`.

**Phase 3 — measure, then gate.** Same rig, protocol and baseline as §8:
`ZZAllocR3_*` (control, already measured) against R3+drop at n =
1,2,3,4,8,16,31. Read live |Σ| with §5c's fuel-starvation instrument, with the
matched baseline arm this time.

## Pre-registered success criterion

|Σ| flat at 15 instead of 15+3n, **and** the 8→16 local exponent materially
below R3's 1.631. **If |Σ| goes flat and the exponent does not move, STOP** —
|Σ| was not the residual driver, the remaining mechanism is unidentified, and
the packing must not be built on top. That is the `select_last_k` lesson: a
correct diagnosis and a working fix bought 12% because a different driver
dominated.

## Risks, in order

1. Phase 0 fails → fall back to packing. Cheap to discover, hence first.
2. **The drop never fires on the real program.** A havoced value that reaches a
   formula lands in `wco` and the check correctly refuses; §8's positive
   controls show exactly that for A5 and A3. A0/A1/A4 should be clean, but it is
   an empirical question — hence Phase 1's instrumentation.
3. Extra `assume_vareq` nodes per trip. Expected to be dominated by a flat |Σ|,
   but `Qed` needs its own look, since `Qed` re-runs the executor via the VM
   cast (so `Qed ≈ vm_compute`).

## Phase 0 result

### What is false: the STANDALONE drop with a dummy witness

`assuming` (`Worlds.v:755`) is

```coq
assuming ω P ι = forall ιpast, inst (sub_acc ω) ιpast = ι ->
                               instprop (wco w1) ιpast -> P ιpast
```

For `ω = acc_subst_right t` we have `sub_acc ω = sub_single xIn t`, so the
premise `= ι` forces **`ι(x) = inst t (ι∖x)`**. With `t` a dummy value and x
unconstrained, no such `ιpast` exists at the generic ι: the hypothesis is
**vacuously true** while the goal `⌜Φc tt ch⌝` still has to be produced.
Verified by inspecting the goal — the fibre has no inhabitant to name.

Note this is NOT repaired by the goal being x-independent (it is: `Φc` carries no
valuation). Entailment in `Pred` is **pointwise in ι**; being able to prove the
goal at some other valuation is not a step.

### What is TRUE, and verified: the FUSED mint+drop

Give the drop the **freshly minted variable** as its witness instead of a dummy.
The composite accessibility is then
`w ⊒ wsnoc w y ⊒ (wsnoc w y) - x` with `sub_acc` mapping `x ↦ term_var y` and
fixing everything else — and now the fibre over *every* ι is inhabited: take
`ιpast := (ι∖x) ► (y ↦ ι(x))`. The operation is a faithful **renaming**, not an
erasure.

**Checked, `Qed`, by position mode at `theories/Symbolic/UnifLogic.v:1343`**
(preamble mode cannot reach these definitions — they live inside the
`UnifLogicOn` functor):

```coq
Lemma zz_helper {w : World} {x y : LVar} {σ : Ty} (xIn : (x∷σ ∈ w)%katamaran)
  (ι : Valuation w) :
  inst (sub_single (ctx.in_succ (b' := (y∷σ)) xIn) (@term_var _ y σ ctx.in_zero))
       (env.snoc (env.remove (x∷σ) ι xIn) (y∷σ) (env.lookup ι xIn))
  = env.snoc ι (y∷σ) (env.lookup ι xIn).
Proof. rewrite inst_sub_single2. cbn. now rewrite env.insert_remove. Qed.

Lemma zz_helper2 {w : World} {x y : LVar} {σ : Ty} (xIn : (x∷σ ∈ w)%katamaran)
  (ι : Valuation w) :
  instprop (subst (subst (wco w) sub_wk1)
              (sub_single (ctx.in_succ (b' := (y∷σ)) xIn)
                          (@term_var _ y σ ctx.in_zero)))
           (env.snoc (env.remove (x∷σ) ι xIn) (y∷σ) (env.lookup ι xIn))
  <-> instprop (wco w) ι.
Proof. rewrite ?instprop_subst. rewrite zz_helper. rewrite inst_sub_wk1. reflexivity. Qed.

(* THE CRUX: the step that kills the standalone drop, discharged for the
   fused one.  G is an arbitrary PURE proposition — which is what the
   concrete side of the refinement obligation is. *)
Lemma zz_fresh_witness {w : World} {x y : LVar} {σ : Ty}
  (xIn : (x∷σ ∈ w)%katamaran) (G : Prop) :
  assuming (acc_trans (@acc_snoc_right w (y∷σ))
              (@acc_subst_right (wsnoc w (y∷σ)) x σ (ctx.in_succ xIn)
                 (@term_var _ y σ ctx.in_zero)))
           (⌜ G ⌝)%I ⊢ (⌜ G ⌝)%I.
Proof.
  rewrite assuming_trans assuming_acc_snoc_right.
  unfold forgetting, assuming. crushPredEntails3.
  apply (H0 (env.lookup ι xIn)
            (env.snoc (env.remove (x∷σ) ι xIn) (y∷σ) (env.lookup ι xIn))).
  - change (env.map (fun (b : LVar∷Ty) (s : Term w (type b)) => inst s ι) (sub_id w))
      with (inst (sub_id w) ι).
    rewrite inst_sub_id. apply (zz_helper xIn ι).
  - apply (proj2 (zz_helper2 xIn ι)). exact H.
Qed.
```

`assuming_acc_snoc_right` (`UnifLogic.v:1248`) is what carries the argument: the
enclosing demonic binder hands you the continuation at **any chosen value** of
the fresh variable, and you choose `ι(x)`.

### Consequences for the design — it gets SIMPLER, not harder

1. **Soundness needs NO side condition.** `zz_fresh_witness` has no
   `occurs_check` hypothesis, because a rename is sound unconditionally. The
   operation therefore cannot be unsound, only useless — the same risk profile as
   `chunk_gc`. This is a large simplification over the original design.
2. **`occurs_check` is still wanted, but only for USEFULNESS.** Rename a *dead*
   old variable and the fresh one stays unconstrained, which is what the havoc
   needs. Rename a *live* one and the fresh variable inherits its constraints —
   still sound, but the havoc stops giving a free value. So the check selects
   good candidates; it does not guard soundness.
3. **Net Σ change per trip is zero.** The havoc mints k fresh variables anyway
   (k = 3 on br_divrem, `diagnostics/havoc-abstraction-payoff.md` §8); using each
   as the witness that drops the corresponding dead variable from the previous
   trip gives +k−k = 0. Pairing is arbitrary — any rename is sound.
4. **Design decision 4 is DROPPED.** No `Inhabited`/`defaultVal` witness is
   needed, since the witness is always a `term_var`. That restriction is gone.
5. Design decision 1 still holds and is now the main structural work: this is a
   step of `sexec_cfg_addr` (or a fused `havoc` primitive), not an
   `sexec_ghost` case, because the carried state must be transported.

### Two further checks, also verified (2026-08-25)

```coq
(* The composite instantiates back to exactly ι — the heap-transport core. *)
Lemma zz_helper3 … : inst (sub_acc (acc_trans acc_snoc_right (acc_subst_right (term_var y))))
                          (env.snoc (env.remove (x∷σ) ι xIn) (y∷σ) (env.lookup ι xIn)) = ι.
Proof. rewrite sub_acc_trans. rewrite inst_subst. rewrite zz_helper. now rewrite inst_sub_wk1. Qed.

(* Hence the heap relation transports with NO side condition. *)
Lemma zz_heap_transport … (h : SHeap w) :
  inst (persist h (acc_trans acc_snoc_right (acc_subst_right (term_var y))))
       (env.snoc (env.remove (x∷σ) ι xIn) (y∷σ) (env.lookup ι xIn)) = inst h ι.
Proof. rewrite inst_persist. now rewrite zz_helper3. Qed.
```

Also confirmed by `Check`: the `occurs_check` instance resolves at `SHeap` —
`occurs_check bIn h : SHeap Σ → option (SHeap (Σ - b))` — so no new instance is
needed for the candidate scan.

### THE SEQUENCING CONSTRAINT (found 2026-08-25, and it changes the design again)

**Non-vacuity holds only for the composite that starts BEFORE the mint.** This is
not a detail — it is forced, and it dictates the whole shape:

- `zz_dummy_witness` is stuck for an **arbitrary** witness `t` at a **fixed**
  world. `term_var y` is an instance of that. So a drop taken from the POST-mint
  world `wsnoc w y`, with witness `term_var y`, is **exactly as unprovable as the
  dummy** — at valuations of `wsnoc w y` with `ι(x) ≠ ι(y)` the fibre is empty.
- Non-vacuity comes *only* from `acc_snoc_right` sitting inside the same
  `acc_trans`, which is what lets `assuming_acc_snoc_right` choose the fresh
  variable's value to be `ι(x)`.
- Consequence: **nothing may be produced into the heap between the mint and the
  drop.** The heap the composite transports is the PRE-mint heap (`h : SHeap w`
  in `zz_heap_transport` — note w has no y, which is why the counterexample
  "table mentions y and register also holds y" cannot arise there).

So the havoc's correct order is:

1. consume the k register chunks — this is what makes the old variables dead;
2. k× **fused mint+drop** (mint `y_i`, retire dead `x_i` with witness
   `term_var y_i`);
3. produce the k new chunks, holding `term_var y_i`.

**Therefore the havoc CANNOT remain a plain `Lem`.** `produce (asn.exist …)`
fuses minting with chunk-production, which is exactly the grouping that breaks
this: it would put the produce between the mint and the drop. `havoc_regs` must
become an **executor primitive** that separates the two. That is a scope increase
over Phase 1 as written below, and it is the main structural cost of this plan.

### CORRECTION to "soundness needs no side condition"

An earlier version of this section (and the commit message of `6cc76a53`) said the
fused drop needs **no** side condition, because a rename is unconditionally
sound. **That is too strong and is corrected here.** The rename *in isolation* is
unconditionally sound — `zz_fresh_witness` and `zz_heap_transport` carry no
hypotheses, and that is real. But the rename's *purpose* is to then produce a
chunk holding the fresh variable, and there the check bites:

- if `x` genuinely occurs nowhere in the carried state, the rename moves nothing,
  the net effect is "x out, y in", and producing `r ↦ y` is a genuine havoc;
- if `x` DOES occur somewhere — say a table key — the rename is still faithful,
  but afterwards that occurrence and the register's new value are **the same
  variable**. The tree is then `∀y (… mentions y … r ↦ y …)` where the correct
  havoc is `∀x ∀y (… mentions x … r ↦ y …)`. The former is the diagonal of the
  latter, i.e. **strictly weaker — unsound**, not merely incomplete.

So an `occurs_check` over the **full** carried state (heap, `wco`, `tbl`,
`exits`, `apc`) is required, and design decision 2 below **stands** rather than
dropping away. The sharper reason: the check is what guarantees the fresh
variable is still fresh *after* the rename. Design decision 4 (the `Inhabited`
witness) does genuinely drop away — the witness is always a `term_var`.

### What is NOT yet verified — do not call this done

Only the crux is proved. Still open, and NOT to be assumed routine (that
assumption is what produced two wrong verdicts already):

- the full `refine_*` lemma for the fused action — the `□ᵣ` / `refine_four`
  plumbing that glues the two verified pieces together. Both ingredients are now
  proved (`zz_fresh_witness` for the pure-goal step, `zz_heap_transport` for the
  heap relation), but the assembly is not, and it lives in
  `theories/Refinement/Monads.v`, a different functor from the one the checks
  above ran in;
- **the refinement lemma for step 3, the produce.** This is where the
  `occurs_check` obligation actually has to be discharged, per the correction
  above, and it is the piece with the least evidence behind it;
- restructuring `havoc_regs` from a `Lem` into an executor primitive (the
  sequencing constraint above) — named, but not prototyped;
- that the executor can actually pair each fresh variable with a dead one at the
  loop head, and that on the real program the candidates ARE dead (empirical;
  §8's positive controls show A5/A3 reaching formulas);
- everything in Phases 1–3 below, unchanged in substance except that Phase 1 now
  includes the `Lem`→primitive restructuring.

## Log

**2026-08-25 — plan opened, Phase 0 run three times, crux PROVED for the fused
design.** Author's note, since the flip-flopping is the expensive part and the
pattern is worth not repeating. Three verdicts on the same question:

1. "The drop is UNSOUND, the deadness condition is about the continuation" —
   **wrong**. The condition is about the present state; every future term is
   built from present terms.
2. "It is locally provable via two `occurs_check`s, half a day" — **wrong**, and
   pitched without reading `assuming`'s definition first. It fails on fibre
   vacuity.
3. "The local refinement lemma is false, soundness belongs to the mint/drop pair
   and needs the whole intervening execution" — **half right**. It IS about the
   pair; it is NOT about the intervening execution. Fusing mint and drop, with
   the fresh variable as witness, makes the fibre inhabited and the crux closes
   in ten lines.

Emiel was right at (1), at (2) and at (3); each correction came from him
restating the same simple semantic fact and refusing the framework-shaped excuse
for it. **The lesson is not "read the definitions" (though that would have caught
(2) in two minutes) — it is that a soundness claim about this framework is cheap
to TEST and expensive to argue.** `zz_dummy_witness` and `zz_fresh_witness` are
each about ten lines and settle in under a second what four rounds of prose could
not. Test the entailment, do not reason about it.
