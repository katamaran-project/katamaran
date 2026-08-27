# PLAN — build the dead-logical-variable drop

Successor to `PLAN-lvar-drop.md`, which is the *investigation* record and stays
that. This is the *build* plan. Read `PLAN-lvar-drop.md`'s status block and its
Phase 0 verdict first; do not read its design section, which is a superseded
third verdict left in place deliberately.

**Status: PHASE A not started. Owner decision taken 2026-08-27: proceed, starting
with the support lemma.**

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
