# PLAN — `dropk`: drop dead logical variables with a projecting SymProp node

Successor to `PLAN-lvar-drop-build.md`, which is now the *investigation record*
and stays that. This is the executable build plan.

**Status: PHASE 0 NOT STARTED. Design settled and de-risked 2026-08-27 (seven
`Qed`s across two sessions). No owner funding decision has been taken on this
page — see §0.**

**Read before doing anything:** `PLAN-lvar-drop-build.md` §2bis (why the obvious
design is FALSE) then §2ter (why this one is not). Do **not** read that page's
§2–§10, which are written for the refuted design; their content is carried
forward here where it survives. Do **not** read `PLAN-lvar-drop.md` at all except
its status block.

---

## §0 What is and is not decided

**Decided:** the *design*. `dropk` is self-contained — no new `Acc` constructor,
no change to `unconditionally`/`RBox`, no new modality (§2ter, four `Qed`s).

**Not decided, and this plan does not decide it:** whether the payoff justifies
the work. The measured prize is **~3× at n=16** on `br_divrem`, and R3's growth
exponent is 1.63 with the residual driver **unidentified** — so this is a factor,
not an exponent fix, and `|Σ|` is demonstrably not all of the wall. §8 prices it
cheaply and in parallel; run that first if you want the number before funding.

Nothing here unblocks anything. The landed 3-register havoc already reaches
`br_divrem`'s real 31 trips.

---

## §1 Established — do NOT re-derive

Seven `Qed`s. All checked by position mode at
`rocq_start(file="theories/Symbolic/Propositions.v", line=2722, character=40)`.
Scripts are in `PLAN-lvar-drop-build.md` §2bis and §2ter; they replay in ~2 s.

**About soundness of the drop itself**

- `zz_drop_equiv` — dropping a variable and fixing it at an arbitrary value
  changes nothing, *no side condition*: the continuation's TYPE puts it at the
  smaller list, so the typing performs the occurs-check.
- `zz_pins` — the fused mint+drop pins the fresh variable. It is a rename, net
  `|Σ|` change zero. **Dead end; do not revisit.**

**About why the `assume_vareq` design is dead**

- `zz_drop_vacuous` — for *every* continuation `k`, `psafe (assume_vareq x t k) ι`
  already holds at any ι off the fibre.
- `zz_drop_step_strong_false` — the per-step obligation is FALSE even granting
  `occurs_check` deadness on heap *and* path condition and semantic
  insensitivity of the continuation. The counterexample's continuation is
  variable-free, so no hypothesis *about the continuation* can rescue it.
- There is no `Subst 𝕊` and there cannot be a generic one, so
  `weaken : 𝕊 (w-x) → 𝕊 w` is not definable.

**About why `dropk` is not dead**

- `zz_forgetting_stronger` — `forgetting zz_bwd Q ι → assuming (zz_fwd t) Q ι`,
  for any witness.
- **`zz_box_at_chosen`** — the money lemma. `unconditionally P ι` yields
  `P zzw' (zz_fwd (term_relval σ (env.lookup ι xIn))) (inst (sub_shift xIn) ι)`:
  the box delivers the continuation **at the shrunk valuation, with no vacuity,
  at every ι**.
- `zz_box_delivers_forgetting` — with `ZZAccIndep`, that is exactly the
  `forgetting`-strength payload `dropk` needs.
- `zz_persist_indep` — `subst a (sub_single xIn t) = a'` whenever
  `occurs_check xIn a = Some a'`, **for every `t`**. So x-free captured data
  persists identically along every witness; this is `ZZAccIndep`'s discharge
  route, and it is the same occurs-check §4 computes.

**Structural facts worth not rediscovering**

- `Acc` has **two** constructors (`Worlds.v:280`): `acc_refl` and
  `acc_sub ζ (ent : wco w2 ⊢ subst (wco w1) ζ)`. Every named `acc_*` is a
  Definition. Adding an accessibility is a Definition, not a framework change.
- `subst_shift_single` holds for **any** `t`, so `wsubst w x t` is the *same
  world* for every witness. Witnesses change only `sub_acc`, never the target.
- `term_relval : ∀ {Σ} σ, RelVal σ → Term Σ σ` is a **constructor of `Term`**.
  Every value has a closed term at every context. This is what makes the
  per-ι witness choice legal.
- `|Σ|` costs **0.358 G words per variable at n=16**, and cost is precisely
  quadratic in `|Σ|` at fixed n (held-out 0.00%). But see §7's honesty clause —
  the naive quadratic extrapolation is known to over-estimate badly.
- The liveness premise holds and **depends on the register set**: 7-register
  havoc → all 7 droppable per trip; 3-register → 1 of 3. §7 re-measures this.

---

## §2 The design, concretely

```coq
(* theories/Symbolic/Propositions.v — new SymProp constructor, NO witness term *)
| dropk {Σ} (x : LVar) {σ} (xIn : x∷σ ∈ Σ) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ

safe  (dropk x k) ι  :=  safe k (env.remove (x∷σ) ι xIn)
psafe (dropk x k)    :=  forgetting (acc_forget …) (psafe k)
```

```coq
(* theories/Symbolic/Worlds.v — five lines, obligation by occurs_check_sound *)
Definition acc_forget {w} x {σ} (xIn : x∷σ ∈ w) (pc' : PathCondition (w - x∷σ))
    (H : occurs_check xIn (wco w) = Some pc') : MkWorld (w - x∷σ) pc' ⊒ w
  := acc_sub (sub_shift xIn) _.
```

The whole design in one line: **keep the witness out of the trusted semantics and
in the accessibility, where a proof may still choose it per-ι.**

---

## §3 PHASE 0 — the full drop-step obligation. THE GATE. Hours, touches nothing.

§2ter settled the *box channel*. It did **not** prove the whole obligation: the
heap relation still has to transport across the projection, and the `RUnit` / ℙ
base cases still have to close.

Restate the complete per-step obligation in a probe, with `dropk`'s `psafe`
modelled as `forgetting zz_bwd (psafe …)` (faithful — that is its intended
definition) and `ZZAccIndep` assumed, and prove it. Mirror
`ZZDropStepObligationStrong` from §2bis so the two are comparable line by line.

Heap transport is the new work: you need `ℛ⟦RHeap⟧ ch sh` at ι to give
`ℛ⟦RHeap⟧ ch h'` at `ι∖x`, i.e. `inst h' (ι∖x) = inst sh ι` given
`occurs_check xIn sh = Some h'`. That should fall straight out of
`occurs_check_sound` + `inst_subst`; if it does not, say so.

| outcome | verdict |
|---|---|
| closes with `ZZAccIndep` and the occurs-check premises | **GO** to Phase 1 |
| closes only with an extra hypothesis | report it, then judge it against §4's dischargeability before continuing |
| does not close | **STOP** and report the residual goal verbatim |

Report before Phase 1 — decision checkpoint per `CLAUDE.md`.

## §4 PHASE 1 — settle `ZZAccIndep`'s threadability ON PAPER. Hours.

`PLAN-lvar-drop-build.md` §A.3 asked this for the old design and it was moot
there. **It is not moot here.** In the executor the drop sits mid-chain, so
`ZZAccIndep` is about the *composite* continuation. Two sources, both must be
settled before any `theories/` edit:

1. **the recursive call** — comes from the induction hypothesis. Check the
   induction is on fuel and that the IH is strong enough to carry it.
2. **the outer continuation**, from `rexec_triple_addr`. Its terms live over the
   contract's context and reach the current world by persistence, so
   `zz_persist_indep` should apply directly — that is the case this design was
   built for. It becomes a hypothesis on `rexec_cfg_addr` discharged once at the
   entry point.

**Exit:** both settled on paper → GO. Either one not dischargeable → **STOP**,
report which.

## §5 PHASE 2 — the framework change. Mechanical, broad, point of no return.

Only after Phases 0 and 1 close. This touches `theories/`, shared by every case
study.

- `dropk` constructor, plus its case in every `𝕊` consumer. In
  `Propositions.v` that is **~10**: `safe` (:329), `safe_debug` (:368),
  `wsafe` (:407), `prune` (:1215), two `ectx` walks (:1395, :1596), :1846,
  `uqSymProp` (:1938), `Erasure` (:2069), `psafe` (:2436). Find the rest by
  grepping `assume_vareq` — every site that matches on it needs a `dropk` case.
- **`prune` and `Erasure` are the two real proofs**; the rest is boilerplate.
  Budget accordingly.
- `acc_forget` in `Worlds.v`; the `psafe` case's `forgetting` lemma in
  `UnifLogic.v`.
- Re-prove whatever breaks: `psafe_safe` (:2455) at minimum.

**Kill-gate: the whole project must still build.** `GATE_JOBS=1 ./scripts/gate.sh`.
Do this *before* writing any CFGVer code on top.

**The `skill-path-guard` hook now demands `pred-modalities` on writes to
`Worlds.v`/`UnifLogic.v`, and `core-executor-internals` is NOT required for
`Propositions.v`** — read `pred-modalities` anyway; §7 of it is this design.

## §6 PHASE 3–6 — the CFGVer side. Carried over unchanged.

These are unchanged from `PLAN-lvar-drop-build.md` §3–§6 and were never
invalidated; that page's text is the reference, this is the summary.

**Phase 3 — liveness computation.** For each variable in `wctx w`, `occurs_check`
against **all** roots: `heap ∪ apc ∪ wco w ∪ tbl ∪ exits ∪ THE ACCUMULATED
TRANSLATION`. *The translation is a root and is easy to forget* —
`PLAN-unquantify-forward.md` omits it, and if the solver ever eliminated a
contract variable in favour of a term mentioning a per-trip variable, the outer
continuation mentions it once persisted while heap and path condition look clean.
Output a `Tri w w'`. Two fiddly parts, both plumbing: enumerating `wctx w` with
`In`-proofs, and the dependent fold. **Instrument it — emit how many drops
actually FIRE.** A drop that never fires is indistinguishable from one that works.

Note `dropk` needs no witness, so `ty.inhabit`'s `None` on tuple/union/record is
no longer a restriction — that under-approximation from the old design is gone.

**Phase 4 — executor step.** Inlined in `sexec_cfg_addr`, not an `sexec_ghost`
case: the step needs `tbl`, `exits`, `apc` and the translations, none of which a
ghost annotation can see. Gate behind a flag so the old path stays byte-identical
and A/B is one recompile apart.

**Phase 5 — concrete mirror, then re-pair the refinement.** `cexec_cfg_addr`
gains `pure tt` (no logical variables concretely). `rexec_cfg_addr` re-paired
using Phase 0's lemma. **Budget for trouble**: this file has a 300 s+ compile hang
in its history whose root cause was never found, and `rsolve` has consumed
multiple GB. Develop in a probe, not in place. Skills: `cfgver-refinement`,
`cfgver-rsolve`.

**Phase 6 — absorb in adequacy.** `sound_exec_cfg_addr_myWP2` accounts for the
new step. Templates: `PLAN-chunk-gc.md` §12, and Phase 4 of `PLAN-annotinstr.md`
which did the same for `call_lemma`.

## §7 PHASE 7 — measure, then gate.

1. **RE-MEASURE THE REGISTER SET.** 7 registers make all 7 droppable, 3 make only
   1, so the landed "havoc three registers" advice is drop-conditional and **may
   invert**. Arms: `{3,7} registers × {drop on, drop off}` at n = 4, 8, 16, 31.
   Do not assume three still wins.
2. Protocol: `allocated_words`, baseline re-measured **on the commit**, one
   `Eval` per process, fuel `27n+60`, every cell classified `block` vs `error`.
3. Pre-registered criterion: **report the growth ratio, not a percentage.** A flat
   percentage off the top is not a fix.
4. Gate: `GATE_JOBS=1 ./scripts/gate.sh` — full build, no proof holes, 14 end
   theorems axiom-clean. Topic branch, `git merge --no-ff`.

## §8 PARALLEL, CHEAP, NON-BLOCKING — price it first if you want the number

Example-agnostic and unaffected by everything above: prepend `k` unused
existentials to a contract and measure. Run it on the whole-function examples,
`Example/BearSSLModpowFull.v` and `Example/BearSSLCheckScalar.v`, and report per
program: (1) its actual `|Σ|`, unknown for both at time of writing; (2) marginal
G words per declared variable there; (3) that marginal as a **fraction of the
program's total cost**.

Item 3 answers whether the `|Σ|` axis grows or shrinks in relative weight with
program size — the open question behind §0. An afternoon, no new machinery, and
it cannot mislead: a direct measurement on the programs that matter rather than
an extrapolation from the smallest one.

---

## §9 Do NOT retry these

- **The fused mint+drop.** `zz_pins`: it is a rename, net `|Σ|` change zero.
- **The `assume_vareq` design.** `zz_drop_step_strong_false`. Three hypothesis
  shapes die to one counterexample.
- **A post-pass over the finished tree** deleting dead `demonicv` binders. Sound,
  easy, and **saves nothing** — the `|Σ|` cost is paid during execution in solver
  lookups, not after the tree exists. `demonicv_prune` (`Propositions.v:1175`)
  already does this shape.
- **Naive `|Σ|²` extrapolation.** It says a flat world is worth 17.6× at n=16;
  the measured figure is ~3× by three routes that all over-estimate. Measure.

---

## §10 Mechanics that cost time in the last two sessions

- **Probe position:** `rocq_start(file="theories/Symbolic/Propositions.v",
  line=2722, character=40)` — the `Notation "'ℙ'"` line, which has `World`,
  `Pred`, `psafe`, `RProp`, `Rel`/`RSat`, `RHeap`, `unconditionally` and all three
  modalities in scope. Then `Import ctx.notations ctx.resolution env.notations`,
  `Import UL.logicalrelation UL.logicalrelation.notations`, `Open Scope ctx_scope`.
- **pet OOMs (>7.6 GB)** on position mode in `theories/Refinement/Monads.v` and on
  `Example/ZZGhostRefineProbe.v` past its `Lemma` line. State the *unfolded* form
  of a refinement obligation at the `Propositions.v` position instead — only
  `RHeapSpec`/`CHeapSpec` are unavailable there and the unfolded statement does
  not need them.
- **`LVar` is abstract inside the functor** — a literal name fails with `cannot
  unify "string" and "LVar"`. Use `Context (x : LVar)`, which also makes any
  counterexample stronger for being parametric.
- **`ctx.remove` needs its `In`-proof explicit** (`@ctx.remove _ (wctx w) b bIn`)
  or `cbn` stalls on an unresolved evar.
- **`⊢` collides.** `Import Entailment` brings the `InstProp` entailment, which
  shadows Pred's. Dodge it entirely: state Pred lemmas **pointwise**
  (`… ι -> … ι`) rather than as entailments. Costs nothing and avoids a
  ten-minute detour.
- **`crushPredEntails3` does not touch `RSat`/`RBox`/`RImpl`** — they are
  `simpl never`. `unfold RBox, RImpl` first, then `cbn`, then
  `rewrite !wand_unfold` to turn Pred wands into implications.
- **`occurs_check_sound` returns `OccursCheckSoundPoint`**, which is an
  `option.wlp`. Recipe: `pose proof (occurs_check_sound xIn a) as HH;
  unfold OccursCheckSoundPoint in HH; rewrite Ha in HH; now inversion HH`.
- **`Program Definition` obligations**: `intros` before rewriting, and split
  `rewrite a, b.` into separate sentences — the comma form hit a parse error in
  obligation mode.
- **Verify each `Qed` landed.** Nested proofs are allowed here, so a missing
  `Qed.` silently swallows a lemma. Check the feedback says "X is defined".

---

## §11 Risk register

| risk | severity | mitigation |
|---|---|---|
| Phase 0's heap transport does not close | high | it is Phase 0's explicit exit criterion; report the residual goal rather than working around it |
| `ZZAccIndep` not dischargeable for the recursive call | high | §4, settled on paper before any `theories/` edit |
| the ~10 `𝕊` cases break another case study | moderate | Phase 2's kill-gate is a full build, run before any CFGVer work |
| `prune` / `Erasure` cases turn out to be real research | moderate | do those two first within Phase 2; if either resists, stop there rather than after the boilerplate |
| `rexec_cfg_addr` re-pairing hangs or OOMs | moderate | probe-first; precedent exists; `cfgver-rsolve` |
| drop never fires on the real program | moderate | Phase 3 instrumentation |
| the drop costs more than it saves | moderate | one state traversal per candidate variable per trip; a plausible outcome, not a bug |
| payoff is only ~3× | **accepted / undecided** | §0; §8 prices it |
| standing obligation: new executor cases and new `𝕊` functions must extend this | permanent | same burden already carried for the concrete mirror |

---

## §12 Honesty clauses (binding)

- Report the **growth ratio**, never a bare percentage.
- No wall-clock deltas under ~15% on this box without user-CPU or back-to-back
  runs — `.vo` page-cache state swings them by 2×.
- One heavy `Eval` per `coqc` process.
- `count_nodes = 1` does **not** mean discharged — it is 1 for `error` too.
  Classify `block` vs `error` explicitly, every cell.
- Any claim that a VC verifies must state whether proof holes remain.
- `rocq_compile_file` verifies TACTICS; only `make` verifies a FILE.
- If a phase fails, say so and stop. Nothing here is unblocking anything.
- This page has an ancestor that went through **six** verdicts before Phase A and
  a seventh after it. Do not trust any statement about this idea that is not in a
  status block backed by a named `Qed`.

---

## §13 Branch

Current work sits on `issue/annot-havoc-spike`, **unmerged**, gate green at
`6fc12d73`. Decide with the owner whether to merge that first or branch from it;
either way this is a topic branch and lands through
`GATE_JOBS=1 ./scripts/gate.sh` + `git merge --no-ff` (`branch-workflow` skill).

---

## Log

**2026-08-27 — plan opened**, superseding `PLAN-lvar-drop-build.md` after that
page's §2ter settled the re-scope positive. Design de-risked, nothing built,
no funding decision taken.
