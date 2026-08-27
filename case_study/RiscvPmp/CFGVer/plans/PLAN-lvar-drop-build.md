# PLAN — build the dead-logical-variable drop

Successor to `PLAN-lvar-drop.md`, which is the *investigation* record and stays
that. This is the *build* plan. Read `PLAN-lvar-drop.md`'s status block and its
Phase 0 verdict first; do not read its design section, which is a superseded
third verdict left in place deliberately.

**Status: PHASE A DONE AND NEGATIVE (2026-08-27). The per-step support lemma is
not merely hard, it is FALSE — refuted by a `Qed`. Exit criteria row 3 fires:
STOP AND RE-SCOPE. Phases B-F are not started and should not be started as
written. Read §2bis before anything else on this page.**

---

## §0 Decision record, and the caveat it overrides

`PLAN-lvar-drop.md` recommends DO NOT FUND, on the grounds that the measured
payoff on `br_divrem` is a **factor of ~2-3x** (§10 of
`diagnostics/havoc-abstraction-payoff.md`) rather than the exponent change that
plan pre-registered as its criterion. **The owner has decided to proceed anyway,
starting with the support lemma.** That is recorded here once and not relitigated
below.

Two things make the decision reasonable even against the br_divrem number, and
both are open questions rather than arguments:

1. **Scaling is unresolved.** Every figure is from one 27-instruction loop at
   `|Σ| ≤ 63`. Per-variable cost is known NOT to be constant — 19.5x a chunk at
   `|Σ|`=25, 65x at 89, 111x at 153
   (`diagnostics/check-scalar-combined-cost-drivers.md`). A whole function sitting
   at `|Σ|` = 150 would pay several times more per variable than `br_divrem` does.
   §10 below prices this cheaply and does not block Phase A.
2. **Phase A is the cheap half of the risk.** It is hours, it touches nothing
   trusted, and it either de-risks the remaining week or kills the plan for a
   sharp reason. Starting there is right regardless of the payoff estimate.

---

## §1 What is already established (do not re-derive)

- **The drop is SOUND.** `zz_drop_equiv` (`Qed`): dropping a variable and fixing
  it at an arbitrary value changes nothing, provided the continuation is typed at
  the smaller variable list. No side condition — the typing performs the
  occurs-check. Script in `PLAN-lvar-drop.md`.
- **A per-action lemma cannot justify it.** `zz_dummy_witness` sticks: quantified
  over an ARBITRARY continuation and checked pointwise in the valuation, the
  hypothesis is vacuous at most valuations. This is the whole reason Phase A
  exists.
- **The fused mint+drop is a dead end.** It makes the fibre non-empty but pins the
  fresh variable (`zz_pins`, `Qed`), so it is a rename and cannot serve as a
  havoc. Do not revisit.
- **The state transports cleanly.** `zz_helper3`, `zz_heap_transport` (`Qed`).
- **`occurs_check` is ready.** Instances for Term, Formula, Chunk, list, Env,
  Assertion and `Sub`; resolves at `SHeap`; `Symbolic/Monads.v:97-99` already
  runs it on a (pathcondition, heap) pair.
- **The liveness premise holds, and depends on the register set** (§9 of the
  diagnostics): the path condition pins nothing; the un-havoced registers do.
  7-register havoc → all 7 droppable per trip. 3-register → 1 of 3.
- **`|Σ|` costs 0.358 G words per variable at n=16**, and cost is precisely
  quadratic in `|Σ|` at fixed n (held-out 0.00%).

---

## §2 PHASE A — the support lemma. THE GATE. Hours, touches nothing trusted.

### A.1 The action, so the lemma has something to talk about

Give the action the already-shrunk heap, so it needs no `occurs_check` inside and
Phase A does not depend on Phase B:

```coq
Definition drop_var {w} x {σ} (xIn : x∷σ ∈ w) (t : Term (w - x∷σ) σ)
    (h' : SHeap (w - x∷σ)) : SHeapSpec Unit w :=
  fun Φ _ => SymProp.assume_vareq x t (Φ _ (acc_subst_right x t) tt h').
```

### A.2 The hypothesis to try FIRST — as an equation on data, not a semantic side condition

The temptation is to state "the continuation does not mention x" semantically.
Try instead the form that reduces the moving case to the non-moving one, because
the non-moving case is already solved (`refine_chunk_gc` closes with `refine_T`):

```
H : Φs w acc_refl tt (weaken h')  =  weaken (Φs (w - x∷σ) (acc_subst_right x t) tt h')
```

In words: running the continuation at the BIG world gives the same tree, up to
weakening, as running it at the SMALL world. That is exactly x-independence,
stated as an equality of data — provable by induction, and checkable.

**Why this shape is worth trying first.** With `H` you can rewrite the drop's
subtree into the big-world one, apply `zz_drop_equiv`'s reasoning to strip the
`assume_vareq` under the enclosing binder, and then finish with `refine_T` on the
unmoved continuation. If that works, the moving-world difficulty never has to be
confronted directly.

If it does not, the fallbacks in order: (ii) a semantic insensitivity condition
`∀ v, psafe (…) ι = psafe (…) ι[x↦v]`; (iii) a support bound "Φs's terms mention
only the contract's context", which is what will actually be dischargeable at the
call site but is the most work to state.

### A.3 Then answer the threadability question — this is as important as the lemma

The lemma is worthless if `H` cannot be supplied. `rexec_cfg_addr` has exactly
two continuation sources; both must be settled ON PAPER before Phase B:

1. **the recursive call** — `H` comes from the induction hypothesis. Check the
   induction is on fuel and that the IH is strong enough to carry `H`.
2. **the outer continuation**, from `rexec_triple_addr`, consuming the contract's
   postcondition. Its terms live over the contract's context and reach the current
   world by persistence. `H` becomes a hypothesis on `rexec_cfg_addr`'s statement,
   discharged once at the entry point.

### A.4 REQUIREMENT, not a hope: do not touch the generic lemmas

The drop must be **inlined into `sexec_cfg_addr`**, not composed via `bind`. If it
is a standalone action composed by `bind`, then `bind`'s *generic* refinement
lemma in `theories/Refinement/Monads.v` has to learn about the support condition —
and that file is shared by every case study. Inlined, `rexec_cfg_addr`'s own proof
handles the step directly and the generic lemmas are untouched.

**If Phase A concludes the generic lemmas must change, STOP and re-scope.** That
is a framework decision, not a case-study one.

### A.5 Mechanics

Position mode (`rocq_start(file=…, line=…)`); preamble mode cannot reach these
definitions, they are inside module functors. `theories/Refinement/Monads.v` for
the relation, `theories/Symbolic/Propositions.v:420` for the `safe`-level facts —
that is where this week's four lemmas were checked. Do NOT develop in
`VerifierRel.v`: pet cannot open it at any position; use the restate-in-a-probe
pattern (`Example/ZZDropRefineProbe.v`).

### A.6 Exit criteria

| outcome | verdict |
|---|---|
| lemma closes with A.2's hypothesis, and A.3 settles both sources without touching generic lemmas | **GO** to Phase B |
| closes only with a semantic condition that A.3 cannot discharge | **STOP**, report which source fails |
| requires changing `theories/Refinement/Monads.v` | **STOP and re-scope** (§A.4) |

Report the outcome before starting Phase B — decision checkpoint per `CLAUDE.md`.

---

## §2bis PHASE A RESULT — the support lemma is FALSE. STOP AND RE-SCOPE.

**Verdict: §2's exit-criteria row 3.** Not "we could not prove it" — *it does not
hold*. Three facts, all mechanised 2026-08-27 by position mode at
`theories/Symbolic/Propositions.v:2723` (cursor on the `Notation "'ℙ'"` line, so
`RProp`, `psafe`, `RHeap`, `□ᵣ`, `unconditionally` and the world arithmetic are
all in scope). `Print Assumptions` on both lemmas lists only the functor's own
abstract parameters (`𝑷`, `𝑯`, `varkit`, `typedeclkit`, …) — no holes.
Full scripts at the end of this section; they replay in ~1.5 s.

### A.2's hypothesis is NOT STATABLE — there is no `weaken : 𝕊 (w - x∷σ) → 𝕊 w`

```
Fail Definition zz_subst_symprop : Subst 𝕊 := _.
  (* "Cannot infer this placeholder of type Subst 𝕊 (no type class instance found)" *)
Goal Subst 𝕊. Fail typeclasses eauto. Abort.
```

`𝕊` has no `Subst` instance, and there cannot be a generic one: substituting an
arbitrary `Sub Σ1 Σ2` through `assume_vareq x …` would have to relocate `x`,
which need not exist in `Σ2`. So A.2's

```
H : Φs w acc_refl tt (weaken h')  =  weaken (Φs (w - x∷σ) (acc_subst_right x t) tt h')
```

is not an equation that can be written down: its two sides live at `w` and at
`w - x∷σ` and the framework has no transport between them in that direction. The
only two embeddings `𝕊 (w-x) → 𝕊 w` are `assume_vareq` and `assert_vareq`
(`Propositions.v:281,314`) — `PLAN-lvar-drop.md` states this and it is the same
wall. A.2's premise, that the moving case can be reduced to the non-moving one by
an equation on data, therefore has nothing to stand on.

### The per-step obligation is FALSE — `zz_drop_step_strong_false` (`Qed`)

So the fallbacks. `ZZDropStepObligationStrong` states the drop's refinement
obligation in exactly the shape §A.4 requires — **inlined**, no `bind`, no
generic lemma: continuations universally quantified and related by
`ℛ⟦□ᵣ(RUnit -> RHeap -> ℙ)⟧`, heaps related by `ℛ⟦RHeap⟧`, conclusion at the
enclosing world — and loads it with every side condition the plan hoped for:

- **Phase B's liveness premise, both roots**: `occurs_check yIn sh = Some h'` and
  `∃ pc', occurs_check yIn (wco w) = Some pc'`;
- **fallback (ii)**, semantic insensitivity of the continuation to the dropped
  variable, stated as `env.remove ι1 yIn = env.remove ι2 yIn → (psafe … ι1 ↔ psafe … ι2)`.

`zz_drop_step_strong_false : ZZDropStepObligationStrong -> False` closes with
`Qed`. The witness is one bool variable, `t := term_val ty.bool false`, empty
heaps, `cΦ := λ _ _, False`, `sΦ := λ _ _ _ _, error amsg.empty`, and
`ι := [x ↦ SyncVal true]`.

**Fallback (iii) dies with it, and this is the point of choosing that witness.**
The counterexample's continuation is `error amsg.empty` — it mentions **no
logical variables at all**, at any world. So it satisfies not just (ii) but *any*
support bound (iii) could state, including "Φs's terms mention only the
contract's context". No hypothesis *about the continuation* can rescue the
lemma, because the counterexample's continuation is already maximally
well-behaved.

### Why — `zz_drop_vacuous` (`Qed`), and this one is continuation-agnostic

```coq
Lemma zz_drop_vacuous {w y σ yIn} (t : Term (w - y∷σ) σ)
    (k : 𝕊 (W.wsubst w y t)) (ι : Valuation w) :
  env.lookup ι yIn <> inst t (env.remove (y∷σ) ι yIn) ->
  psafe (SymProp.assume_vareq y t k) ι.
```

For **every** continuation `k`: at any valuation off the fibre, the drop node is
already satisfied. It carries no information there. That is the whole obstruction,
and it does not depend on quantifying over `sΦ`, so it applies verbatim to the
real `rexec_cfg_addr` and not only to the arbitrary-continuation lemma above.

The quantifier structure, stated once:

- `ℛ⟦ℙ⟧ P SP` is `psafe SP -∗ ⌜P⌝`, and Pred entailment is **pointwise in ι**
  (`entails`, `Worlds.v:594`: `∀ ι, instprop (wco w) ι → P ι → Q ι`).
- With a dummy witness the drop's guard `ι(y) = inst t (ι∖y)` fails at almost
  every ι, so both the symbolic hypothesis (`zz_drop_vacuous`) and the `□ᵣ`
  continuation relation (empty fibre — `zz_dummy_witness`) are vacuous there.
- The concrete conclusion `cΦ tt ch` is ι-**independent** once `y ∉ sh`.

So `(∀ι. hyp) ⟹ (∀ι. concl)` is TRUE — that is exactly `zz_drop_equiv` — while
`∀ι. (hyp ⟹ concl)` is FALSE, and the second is what Pred entailment asks for.
The gap is a quantifier order, not an occurs-check. An equation on data (A.2)
cannot move a quantifier, and neither can a pointwise semantic condition (ii),
which is why both fail for the same reason.

### A.3 is moot

The threadability question — can `H` be supplied from the recursive call and from
`rexec_triple_addr`'s outer continuation — does not arise. There is no `H` to
thread: the shape it was to have is not statable (above), and no hypothesis of
that kind would help (also above). Nothing was learned about A.3 and nothing
needs to be.

### What a real fix would have to be, and it is bigger than §A.4's stop line

§A.4 drew the stop line at `theories/Refinement/Monads.v`. The actual re-scope is
elsewhere and larger, and it is exactly the "structural conclusion" of
`PLAN-lvar-drop.md`: a **new SymProp node plus a matching modality**, whose
`safe`/`psafe` forgets the variable rather than guarding on it —

```
safe (dropk y k) ι  :=  safe k (env.remove (y∷σ) ι yIn)
```

sound by `zz_drop_equiv`'s argument (the typing of `k` performs the occurs
check), with the refinement side using a `forgetting`-style modality rather than
`assuming`'s fibre.

**And there is a direction problem on top of that**, worth knowing before anyone
prices it. `forgetting {w1 w2} (ω : w1 ⊒ w2) P ι = P (inst (sub_acc ω) ι)`
(`Worlds.v:760`). To get the `Pred (w - y) → Pred w` that the drop needs, one
needs `sub_acc ω = sub_shift yIn : Sub (w - y) w`, i.e. an accessibility
`(w - y) ⊒ w` — the small world as the **past**. But the executor's `Box`/`□ᵣ`
continuation is indexed by `w ⊒ w'`, the small world as the **future**, and for
`ω : w ⊒ (w - y)` the `sub_acc` is necessarily a substitution that kills `y`,
whence `assuming`'s fibre. Since `assuming` is *defined* from `sub_acc`
generically, making it behave like `forgetting` for one accessibility means
changing what an accessibility is, or adding a field to it. That is a
`Worlds.v` + `Propositions.v` change with its own soundness burden, touching
every case study — strictly more than the `Refinement/Monads.v` risk §A.4 was
watching for.

Whether that is worth doing is a framework decision and is **not** taken here.
The input to it is §10, which is unaffected by this result and is now the only
cheap work left on this page.

### The scripts, verbatim (replayed clean in one run, 1.5 s)

Position mode: `rocq_start(file="theories/Symbolic/Propositions.v", line=2722,
character=40)`. Preamble mode cannot reach these — functor internals.

```coq
Import ctx.notations ctx.resolution env.notations.
Import UL.logicalrelation UL.logicalrelation.notations.
Import iris.proofmode.tactics.
Open Scope ctx_scope.

Fail Definition zz_subst_symprop : Subst 𝕊 := _.
Goal Subst 𝕊. Fail typeclasses eauto. Abort.

Lemma zz_drop_vacuous {w : World} {y : LVar} {σ : Ty} {yIn : (y∷σ ∈ w)%katamaran}
    (t : Term (w - y∷σ) σ) (k : 𝕊 (W.wsubst w y t)) (ι : Valuation w) :
  env.lookup ι yIn <> inst t (env.remove (y∷σ) ι yIn) ->
  psafe (SymProp.assume_vareq y t k) ι.
Proof.
  intros Hne. cbn. unfold W.assuming. intros ιp Heq Hpc. exfalso.
  cbn in Heq. rewrite inst_sub_single2 in Heq.
  apply Hne. rewrite <- Heq. rewrite env.remove_insert. now rewrite env.lookup_insert.
Qed.

Definition ZZDropStepObligationStrong : Prop :=
  forall (w : World) (y : LVar) (σ : Ty) (yIn : (y∷σ ∈ w)%katamaran)
         (t : Term (w - y∷σ) σ) (h' : SHeap (w - y∷σ))
         (cΦ : unit -> SCHeap -> Prop)
         (sΦ : forall w' : World, (w ⊒ w') -> Unit w' -> SHeap w' -> 𝕊 w')
         (ch : SCHeap) (sh : SHeap w),
    (* Phase B's liveness side condition: y is dead in the heap ... *)
    occurs_check yIn sh = Some h' ->
    (* ... and in the path condition. *)
    (exists pc', occurs_check yIn (wco w) = Some pc') ->
    (* Fallback (ii): the continuation is semantically insensitive to y. *)
    (forall (ι1 ι2 : Valuation w),
        env.remove (y∷σ) ι1 yIn = env.remove (y∷σ) ι2 yIn ->
        (psafe (sΦ w W.acc_refl tt sh) ι1 <-> psafe (sΦ w W.acc_refl tt sh) ι2)) ->
    (⊢ ℛ⟦□ᵣ (RUnit -> RHeap -> ℙ)⟧ cΦ sΦ -∗
       ℛ⟦RHeap⟧ ch sh -∗
       ℛ⟦ℙ⟧ (cΦ tt ch)
            (SymProp.assume_vareq y t (sΦ (W.wsubst w y t) (W.acc_subst_right t) tt h')))%I.

Section ZZDrop.
  Context (x : LVar).
  Let zzb : Binding LVar Ty := x∷ty.bool.
  Let zzw : World := W.wlctx (ctx.snoc ctx.nil zzb).
  Let zzxIn : ctx.In zzb (W.wctx zzw) := ctx.in_zero.

  Lemma zz_drop_step_strong_false : ZZDropStepObligationStrong -> False.
  Proof.
    intros HO.
    specialize (HO zzw x ty.bool zzxIn (@term_val (zzw - (x∷ty.bool)) ty.bool false) nil
                   (fun _ _ => False) (fun _ _ _ _ => SymProp.error amsg.empty) nil nil).
    specialize (HO eq_refl).
    specialize (HO (ex_intro _ _ eq_refl)).
    specialize (HO (fun ι1 ι2 _ => conj (fun H => H) (fun H => H))).
    destruct HO as [HO].
    specialize (HO (env.snoc env.nil zzb (SyncVal true)) I I).
    cbn in HO. rewrite !wand_unfold in HO. apply HO.
    3: { cbn. unfold W.assuming. intros ιp Heq Hpc. cbn in Heq.
         unfold ty.valToRelVal in Heq. cbn in Heq.
         apply (f_equal (fun e => env.lookup e zzxIn)) in Heq.
         cbn in Heq. discriminate. }
    2: { cbn. reflexivity. }
    unfold RBox, RImpl. cbn. unfold W.unconditionally, W.assuming.
    intros w2 ω ιp Heq Hpc a ta.
    rewrite !wand_unfold. intros Ha ch2 sh2.
    rewrite !wand_unfold. intros Hh2 Hs.
    exact Hs.
  Qed.
End ZZDrop.
```

Two mechanics worth keeping, both cost time here:

- **pet OOMs (>7.6 GB) on position mode in `theories/Refinement/Monads.v`** and on
  `Example/ZZGhostRefineProbe.v` past its `Lemma` line. `Propositions.v:2723` is
  the position that works and it has everything except `RHeapSpec`/`CHeapSpec` —
  which the *unfolded* per-step statement above does not need. Prefer it.
- Inside the functor `LVar` is abstract, so a literal variable name will not
  typecheck (`cannot unify "string" and "LVar"`). `Context (x : LVar)` — which
  also makes the counterexample stronger, being parametric in the name. And
  `[ctx x∷σ]` needs `Open Scope ctx_scope`; `ctx.remove` needs its `In`-proof
  explicit (`@ctx.remove _ (W.wctx w) b bIn`) or `cbn` stalls on an evar.

### What is NOT claimed

- Nothing here contradicts `zz_drop_equiv`. The drop remains **sound**; the VC it
  produces is equivalent to the one without it. What is false is the *per-step
  refinement lemma*, which is a statement about the framework's proof shape.
- Nothing here rules out a justification that exploits the *specific* structure of
  the executor's remaining steps rather than a step lemma. `zz_drop_vacuous` makes
  that look unpromising — the drop node is uninformative off the fibre no matter
  what follows it — but it was not scoped, attempted, or refuted.
- Phases B-F were not started. §3's translation-is-a-root warning and §7's
  register-set re-measurement remain unexercised and still look right; they are
  simply not reachable from here.

---

## §3 PHASE B — the liveness computation. Half a day to a day.

For each variable in `wctx w`, `occurs_check` against **all** roots:

```
heap ∪ apc ∪ wco w ∪ tbl ∪ exits ∪ THE ACCUMULATED TRANSLATION
```

**The translation is a root and is easy to forget** — `PLAN-unquantify-forward.md`
omits it. If the solver ever eliminated a contract variable in favour of a term
mentioning a per-trip variable, the outer continuation mentions it once persisted,
while heap and path condition look clean. `occurs_check` has a `Sub` instance and
the translations are already threaded at the call site.

Output a `Tri w w'` — one `tri_cons` per dropped variable, witness from
`ty.inhabit` (`theories/Syntax/TypeDecl.v:960`; returns `None` for
tuple/union/record, so those are silently never dropped, which is a sound
under-approximation).

Two fiddly parts, both plumbing rather than design: enumerating `wctx w` with
`In`-proofs, and the dependent fold (each step's type mentions the previous
step's smaller context), which needs a termination measure — the context shrinks.

**Instrument it.** Emit how many drops actually FIRE. A drop that never fires is
indistinguishable from one that works.

---

## §4 PHASE C — the executor step. Small.

Call Phase B at the loop head; continue at the smaller world via
`SymProp.assume_triangular` + `acc_triangular` (`Worlds.v:428`), the machinery the
solver already exercises on every `assume`/`assert`.

Inlined in `sexec_cfg_addr` (§A.4), not an `sexec_ghost` case — the step needs
`tbl`, `exits`, `apc` and the translations, none of which a ghost annotation can
see. Gate it behind a flag so the old path stays byte-identical and A/B is one
recompile apart.

---

## §5 PHASE D — concrete mirror, then re-pair the refinement. Moderate; historically unpredictable.

- `cexec_cfg_addr` gains `pure tt` in the matching position — there are no logical
  variables concretely, so the drop has no concrete content.
- `rexec_cfg_addr` re-paired at the changed point, using Phase A's lemma.

**Budget for trouble here.** This file has a 300 s+ compile hang in its history
whose root cause was never found, and `rsolve` has consumed multiple GB. Develop
in a probe, not in place. Skills: `cfgver-refinement`, `cfgver-rsolve`.

---

## §6 PHASE E — absorb in adequacy. Small.

`sound_exec_cfg_addr_myWP2` (`Adequacy.v`) accounts for the new step. Chunk-GC
precedent (`PLAN-chunk-gc.md` §12) is the template; Phase 4 of
`PLAN-annotinstr.md` did the same for `call_lemma`.

---

## §7 PHASE F — measure, then gate.

1. **RE-MEASURE THE REGISTER SET.** §9.5 of the diagnostics: 7 registers make all
   7 droppable, 3 make only 1, so the landed "havoc three registers" advice is
   drop-conditional. With the drop in place the ordering may reverse. Arms:
   `{3,7} registers × {drop on, drop off}` at n = 4, 8, 16, 31. Do not assume
   three registers still wins.
2. Protocol exactly as §8.2/§10.1: `allocated_words`, baseline re-measured on the
   commit, one `Eval` per process, fuel `27n+60`, every cell classified `block`
   vs `error`.
3. Pre-registered criterion: **report the growth ratio, not a percentage.** A flat
   percentage off the top is not a fix (§6 of `PLAN-unquantify-forward.md`).
4. Gate: `GATE_JOBS=1 ./scripts/gate.sh` — full build, no proof holes, 14 end
   theorems axiom-clean. Topic branch, `git merge --no-ff`.

---

## §8 Risk register

| risk | severity | mitigation |
|---|---|---|
| Phase A needs the generic refinement lemmas | **highest** | it is Phase A's explicit exit criterion; stop rather than proceed |
| support condition not dischargeable for the outer continuation | high | A.3, settled on paper before any code |
| `rexec_cfg_addr` re-pairing hangs or OOMs | moderate | probe-first; `cfgver-rsolve`; precedent exists |
| drop never fires on the real program | moderate | Phase B instrumentation; §9 says it should fire at 7 registers |
| the drop costs more than it saves | moderate | one state traversal per dropped variable per trip; `PLAN-unquantify-forward.md` §3 flags this and it is a plausible outcome, not a bug |
| payoff is only 2-3x | **accepted** | §0 |
| standing obligation: new executor cases must extend the support lemma | permanent | same burden already carried for the concrete mirror |

---

## §9 Honesty clauses (binding)

- Report the **growth ratio**, never a bare percentage.
- No wall-clock deltas under ~15% on this box without user-CPU or back-to-back runs.
- One heavy `Eval` per `coqc` process.
- `count_nodes = 1` does NOT mean discharged — it is 1 for `error` too. Classify
  `block` vs `error` explicitly, every cell.
- Any claim that a VC verifies must state whether proof holes remain.
- If Phase A fails, say so and stop. The measured 2.66x register-set win is
  already landed and `br_divrem`'s 31 trips already discharge; nothing here is
  unblocking anything.

---

## §10 Parallel, cheap, non-blocking — the scaling question

The padding experiment (§10.1 of the diagnostics) is example-agnostic: prepend k
unused existentials to any contract, measure. Run it on the whole-function
examples — `Example/BearSSLModpowFull.v`, `Example/BearSSLCheckScalar.v` — and
report per program:

1. its actual `|Σ|` (unknown for both at time of writing)
2. marginal G words per declared variable there
3. that marginal as a **fraction of the program's total cost**

Item 3 answers whether the `|Σ|` axis grows or shrinks in relative weight with
program size — the open question behind §0.1. An afternoon, no new machinery, and
it cannot mislead: it is a direct measurement on the programs that matter rather
than an extrapolation from the smallest one.

---

## Log

**2026-08-27 — plan opened.** Owner decision: proceed, Phase A first.

**2026-08-27 — Phase A DONE, NEGATIVE. Exit row 3: STOP AND RE-SCOPE.** See
§2bis. A.2's hypothesis is not statable (no `Subst 𝕊`, so no
`weaken : 𝕊 (w-x) → 𝕊 w`); the per-step obligation is FALSE even with Phase B's
`occurs_check` deadness on heap *and* path condition and fallback (ii)'s semantic
insensitivity assumed (`zz_drop_step_strong_false`, `Qed`); and the reason is
continuation-agnostic (`zz_drop_vacuous`, `Qed`) — a quantifier-order gap, not an
occurs-check gap, so fallback (iii) dies too. A real fix is a new SymProp node
plus a `forgetting`-style modality in `Worlds.v`/`Propositions.v`, which is
*larger* than the `Refinement/Monads.v` risk §A.4 was watching for, and it has a
direction problem (the drop needs the small world as the accessibility's PAST,
the executor's `□ᵣ` indexes it as the FUTURE). Not taken. §10 is the only cheap
work left on this page and is unaffected.
