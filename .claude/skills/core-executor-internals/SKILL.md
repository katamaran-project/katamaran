---
name: core-executor-internals
description: >
  Katamaran's CORE generic symbolic-execution monad (SPureSpec/SHeapSpec) and its
  refinement/soundness proof — the framework-wide layer underneath every case
  study's own executor (CFGVer's sexec_cfg_addr, MinimalCaps' equivalents, etc.),
  not specific to any one of them. Use when reading or modifying the generic
  choice combinators (demonic_finite, demonic_pattern_match, angelic_finite,
  angelic_pattern_match — theories/Symbolic/Monads.v), the generic statement-level
  executor `sexec`'s dispatch over Stm constructors (theories/MicroSail/
  SymbolicExecutor.v), or their refinement lemmas (refine_<combinator>,
  theories/Refinement/Monads.v, stated via the ℛ⟦⟧ logical relation and usually
  proved with Iris). ALSO use when investigating WHY a symbolic-execution proof
  is unexpectedly slow or looks exponential — the combinators do enumerate every
  branch, but assume/assert prune refuted forks at construction via
  combined_solver, so exponential growth almost always traces to symbolic TERM
  DUPLICATION in the register store instead, in ANY case study, not just CFGVer
  (see "Slow/exponential symbolic execution" below). NOT for CFGVer's
  own executor layer built on top of this (cfgver-executor), and NOT for the
  rsolve tactic that closes CFGVer's own relational goals (cfgver-rsolve) — this
  skill is about the shared core monad's own refinement lemmas, one layer
  further down than either of those.
---

# Core symbolic-execution monad internals

The layer every case study's own executor is built on. If you're working purely
inside `case_study/RiscvPmp/CFGVer/`, you usually want **cfgver-executor**
instead (CFGVer's `sexec_cfg_addr`, built ON this layer) or **cfgver-refinement**
(the `sexec_cfg_addr`/`cexec_cfg_addr` relational pair, also built on this).
Reach for THIS skill when the question is about the generic machinery itself —
reading it, changing it, or explaining a symptom that traces back to it.

## The two sides of the monad

- **`CPureSpec`/`CHeapSpec`** — the CONCRETE side: plain, deterministic Coq
  computation, no symbolic terms.
- **`SPureSpec`/`SHeapSpec`** — the SYMBOLIC side: world-indexed
  (`⊢ ... : World -> Type`), what every case study's symbolic executor runs on.

Both sides expose the SAME named combinators (choice, pattern-matching, assume/
assert). Every symbolic combinator has a matching `refine_<name>` lemma in
`theories/Refinement/Monads.v` proving it agrees with its concrete counterpart.

### `⊢`/`Valid` vs an implicit `{w}` — a niladic monadic action needs the latter

`⊢ A` is `Valid A := forall w, A w` — a genuine EXPLICIT Pi type, not an
implicit-argument sugar. A function like `sexec_instruction : ⊢ STerm ty_xlenbits
-> STerm ty_xlenbits -> STerm ty_word -> SHeapSpec (STerm ty_xlenbits)` can still
be called bare inside a `⟨θ⟩ x <- ma ;; mb` bind chain with only its three
`STerm` VALUE arguments (no explicit world) — because those arguments are
themselves world-indexed, and ordinary unification against them pins `w`
without ever needing `⊢`'s own leading `forall w` filled in explicitly.

A NILADIC `⊢`-typed action — no world-indexed value argument at all, e.g. a
helper like `sexec_ghost : Annot -> ⊢ SHeapSpec Unit` (CFGVer's AnnotInstr
migration, `PLAN-annotinstr.md`) — has nothing for that unification to hook
onto, and probing this confirmed it fails in BOTH positions of the bind
notation:
```
Check (fun (w0 : World) (a : Annot) => (sexec_ghost a) : SHeapSpec Unit w0).
(* Error: cannot unify "(□(Unit -> SHeap -> 𝕊)) w0" and "World" *)
```
(`SHeapSpec Unit w0` unfolds to a CPS function type itself, so Coq tries to
match `sexec_ghost a`'s `forall w, ...` against it AS a Pi comparison — domain
`World` vs domain `□(...) w0` — and fails; it does not "auto-apply" the missing
world argument the way it happens to for an argument-value-pinned case.)

**Fix: declare the niladic helper with an implicit `{w : World}`, not `⊢`** —
exactly `chunk_gc`'s existing shape (`Definition chunk_gc {w : World} :
SHeapSpec Unit w := ...`). An implicit argument DOES get filled from the
expected type when the term is used bare; an explicit Pi does not. This is easy
to get wrong by analogy with a same-file neighbor that happens to have value
arguments — check whether the neighbor's `⊢` is actually being exercised
argument-free before copying its shape.

## Choice combinators (`theories/Symbolic/Monads.v`)

- `demonic_finite F := demonic_list (finite.enum F)` (~line 431) —
  **unconditionally enumerates every value of the finite type `F`**, with no
  check of whether the real answer is already known/decidable. Universal
  ("demonic") choice: used wherever the executor must consider every
  possibility (e.g. picking a pattern-match case).
- `angelic_finite`/`angelic_list` — same shape, EXISTENTIAL ("angelic") choice:
  used where the executor gets to pick (e.g. CFGVer's exit-vs-continue choice
  in `sexec_cfg_addr`).
- `demonic_pattern_match'`/`demonic_pattern_match` (~line 574-618) — the
  pattern-match dispatcher: `demonic_finite (PatternCase pat)` picks a case,
  THEN `assume_formula` constrains the reconstructed value to equal the real
  scrutinee. This is what `if`/`match` on ANY type desugars through (`stm_if`
  is sugar over a boolean `stm_pattern_match`). The dispatcher fast-paths
  uniquely-reversible patterns (`pat_var`, `pat_unit`, statically-known
  `pat_union` via `term_get_union` — the method-Y cases); upstream also had
  `term_get_val` fast paths for `pat_bool`/`pat_enum` etc., kept commented
  out (~line 490-571) with matching commented refinement-proof cases.
- `angelic_pattern_match'`/`angelic_pattern_match` — same shape, angelic choice
  + `assert_formula` (the proof-*obligation*-generating counterpart, used on
  the concrete/refinement side).

**Construction-time pruning DOES exist — one step after the fork.**
`demonic_finite` enumerates every case blindly, but each case's
`assume_formula` (= `assume_pathcondition`, same file ~357-372) runs
`combined_solver` on the new constraint AT CONSTRUCTION TIME: if it
contradicts the path condition (e.g. `term_val false = term_val true` from a
folded concrete scrutinee — `simplify_eq_val` refutes literal mismatches
outright), the result is `SymProp.block` and the case's CONTINUATION is never
built. The angelic side prunes the same way through `assert_pathcondition`
(→ `SymProp.error`). A fork on an already-concrete scrutinee therefore costs
O(1) per dead case — verified empirically 2026-07-19 (a 10-trip
concrete-counter BNE loop shows no growth). Scrutinees arrive already
`peval`'d (`eval_exp`, SymbolicExecutor.v ~403; `peval_binop'` folds val-val
binops including relational comparisons).

## How an `assert` is discharged against the path condition (`Symbolic/Solver.v`)

The other half of what `combined_solver` does: not just refuting forks, but
*discharging* an asserted formula that already follows from `wco`. Worth knowing
because a failure here leaks one residual node per step into the VC.

`solver_generic w C` (`Solver.v` ~3007) is three stages, in this order:

1. `simplify_pathcondition C` — per-formula rewriting (`simplify_formula`).
   Structural: `simplify_secLeak` decomposes `secLeak` through
   binop/unop/union down to variable leaves, `term_val ⇒ true`. It does **not**
   consult `wco`.
2. `assumption_pathcondition (wco w) C1` → `assumption_formula`, which walks
   `wco` and calls `formula_simplifies F F'` per entry. Its first line is
   `if formula_eqb hyp fact then Some formula_true`, and `formula_eqb` **does**
   cover `formula_secLeak` — so `assume F ;; assert F` needs nothing
   type-specific.
3. `unify_pathcondition`.

`combined_solver` (~3053) runs `solver_generic` several times, which is why a
leftover `formula_true` from stage 2 clears on a later pass (one pass leaves
`[formula_true]`, the composite leaves `[ctx]`).

**Both `assume` and `assert` extend the world with their residual** —
`wpathcondition w C = MkWorld (wctx w) (wco w ++ C)` (`Worlds.v:104`), used by
`assume_pathcondition` *and* `assert_pathcondition` (`Monads.v` ~334-372). So an
un-discharged assert permanently enlarges `wco` with a redundant copy, and every
later `wco` walk pays for it — a term-size-independent quadratic if it happens
per step.

### Fixed 2026-07-28: `formula_simplifies` manufactured untested conjuncts

An **ordering** bug, not a resource one — the earlier write-up of this called it
"burning a path-condition entry", which is wrong and actively misleading:
`assumption_formula` recurses on the tail in *both* the `Some` and `None`
branches, so returning `Some` consumes nothing extra.

The real invariant is *"the formula arriving at step `F'` has already been tested
against every entry newer than `F'`"* — the walk only ever offers a formula the
entries **older** than the current one. The `formula_relop bop.eq` case broke it
by *manufacturing* conjuncts mid-walk: it returned
`Some (propeq t1 t2 ∧ secLeak t1 ∧ secLeak t2)` **ignoring its `fact`
argument**, so those conjuncts had been tested against nothing at all.

And because the rewrite ignored `fact`, it fired at the **first** step of the
walk — against the newest `wco` entry. So the conjuncts did get tested against
entries 2…n as the walk continued, and the *only* entry that could never
discharge them was the newest one. Hence the otherwise baffling measurement
(`wco = [secLeak p]`, hypothesis `p = p+p`): `secLeak p` is entry 1, the one
entry that can't help, and adding **any** unrelated newer entry shifts it to
position 2 where it does discharge.

Fixed by testing each manufactured conjunct against `fact` at the moment of
creation (`formula_discharge`, a non-recursive helper because
`formula_simplifies` recurses structurally on `hyp` and so cannot call itself on
a formula it just built). Since the rewrite always fires at step 1, closing the
step-1 gap closes it completely. `smart_and` then drops a discharged conjunct
instead of leaving a `formula_true` node. `formula_simplifies_spec`'s relop case
is now a uniform congruence proof (`instpred_relop_eq_split` for the
`fact`-independent split, then `formula_discharge_spec` per conjunct) rather than
a case analysis on the `formula_eqb` tests.

Note this was *usually* masked by `combined_solver`'s repeated passes. For the
`secLeak`-specific semantics these formulas carry, see **secret-data-walls**.

### An assert is discharged against what was known WHEN IT RAN, not when you read it

The corollary of the above that costs the most time. `consume` walks `∗`
left-to-right (`Monads.v:1067`) and `call_contract` (`Monads.v:1085`) hands a
contract's logic variables over as unconstrained ANGELIC evars — only those in
`sep_contract_localstore` are pinned first, by `assert_eq_nenv`. So a pure
conjunct sitting ahead of the chunk that unifies its variable is offered to
`combined_solver` as `assert (P ?x)` with *nothing* known about `?x`. No amount
of solver power helps: equation rewriting / congruence closure would not either,
because at that moment no equation about `?x` exists yet. It is an ordering
problem.

What makes it hard to see is that `postprocess`'s `solve_evars`/`solve_uvars`
then substitute `?x` throughout the tree, so the surviving residual **prints in
its instantiated form** — typically as something an `assumek` directly above it
discharges outright. Diagnosed 2026-07-29 in CFGVer, where
`assumek (secLeak p)` / `assertk (secLeak p)` sat adjacent and undischarged;
feeding `combined_solver` that exact world and path condition returns residual
`[ctx]` in 22 ms, proving the solver never saw that form.

Two consequences worth internalising:
- **Never conclude "the solver is broken" from a printed residual.** Rebuild the
  world by hand and call `combined_solver` on it (preamble mode, ~20 ms). If it
  discharges, the printed formula is not the one it was given.
- `consume`'s order-sensitivity is a real wart, not a fact of life: `∗` is
  commutative so the assertion's *meaning* is order-independent, yet the VC is
  not. The principled fix is to have `consume` discharge pure `asn.formula`
  obligations *after* the spatial chunks (sound by ∗-commutativity, and monotone
  — a pure obligation checked later is checked with strictly more in `wco`).
  Cost is the refinement burden: `refine_consume` must be re-proved and every
  case study recompiled. A more general alternative is `replay` (`Monads.v:765`),
  which re-runs a finished `SymProp` tree back through the solver-backed monad so
  every assert is re-offered in its substituted form; caveats are that its
  `pattern_match` cases are commented out as NOT IMPLEMENTED and it costs another
  full traversal. Neither has been attempted.

The authoring-side rule, and the one case where reordering is UNSOUND (crossing a
pattern match on the same variable eliminates it, weakening the precondition),
are in **cfgver-contracts**.

**What this fix did NOT do — measured, do not re-run it.** It has *zero* effect
on `key_schedule_loop2`'s VC: `assertk (formula_le)` 16, `assertk`/`assumek
(formula_secLeak)` 28/28, `debug` 132 — every count identical before and after.
The reason is structural: that VC contains **no** `formula_relop` and **no**
`formula_propeq` node at all, so the `bop.eq` case never shapes its residuals.
The gate passes and all 9 examples still discharge, so the fix is worth keeping —
but it is not the cause of the `key_schedule_loop` blowup, and that lead is
**refuted**, not merely unconfirmed. See `project-solver-secleak-residuals` for
where the investigation actually stands.

Two traps if you touch this proof: `instpred_formula (formula_and F1 F2)` is
definitionally `∗` (`Worlds.v:924`) but `Arguments instpred_formula [w] !fml`
means `cbn` unfolds it whenever the formula is **constructor-headed** — so `cbn`
reduces concrete conjuncts like `formula_secLeak t1` and then `iApply` no longer
matches a lemma stated over `instpred hyp`. Rewrite with
`instpred_formula_and'`/`smart_and_spec` instead. And `tauto` cannot see through
`∗` (cf. the explicit `change` at `Worlds.v:1850`); `exact`/`apply` work, since
they use conversion.

## Adding a NEW solver rule — the recipe

Three rules exist to copy from: `try_bvadd_cancel` (relop eq/neq, guarded),
`try_bvadd_cancel_propeq` (propeq, unguarded), `try_fetch_bound` (relop le,
discharges against `wco`). Ordered by what costs time if you get it wrong.

**1. Dump the real shapes before writing anything.** The formula you must match
is *not* what the residual goal prints as after `solve_vc`, and it is not what
the contract wrote either. Get the truth from the smallest program that shows
the shape (1–2 instructions is enough):

```coq
Eval vm_compute in (cfg_map <contract>
  (fun ia p exits P i ec fl => postprocess (CFG_VC_triple p exits P i fl))).
```

That prints assumptions (i.e. `wco`) and goals *together*, which is the only way
to see whether the hypothesis you plan to use is even in the path condition, and
in what form. Doing this cost 30 s and settled three open questions at once.

**2. Know the normal form.** `simplify_relop`'s `le` arm is
`simplify_le t1 t2 = singleton (peval_formula_le t1 t2)` and
`peval_formula_le t1 t2 = peval_formula_le' (peval (term_minus t2 t1))` — so a
`t1 <= t2` obligation reaches you as `0 <= t2 - t1`, and an assumption put in by
a contract is stored in `wco` in *that same* normalised form. Match one shape,
not two.

**3. Hook at a `{w : World}` level.** You need `wco`, and the `{Σ}`-generic
helpers (`peval_formula_le'`, `simplify_le`) cannot see it. `simplify_relop` is
World-indexed: add your dispatch to its arm for your relop, mirroring how
`eq`/`neq` dispatch through `try_bvadd_cancel`, with `None` falling through to
the pre-existing behaviour. Then extend `simplify_relop_spec`'s `destruct op`
(it has one branch per RelOp constructor — `eq neq le lt bvsle bvslt bvule
bvult`, so miscounting the `idtac`s is a loud error, not a silent fallthrough).

**4. NEVER return `error` for "cannot decide".** `Some error` means *refuted*.
Returning it because you failed to find your hypothesis makes the solver refute
satisfiable paths — unsoundness in the dangerous direction, and it will not show
up as a failed build. Every failure path falls through untouched.

**5. Cheap outermost guard.** Your rule runs on every formula of that relop, so
gate anything expensive (a `wco` scan is O(|wco|)) behind a cheap syntactic
match on the goal. Measured with such a guard: a program with no matching
obligations is unchanged to four significant figures.

**6. `Equations` will not let two type indices meet.** Matching two arguments
that each bind a width — or taking one width as a parameter and binding the
other from a pattern — fails with *"The pattern n2 should be equal to n1, it is
forced by typing"*. Two ~6-minute builds went to learning this twice. The fix is
not a cleverer pattern: **return NON-dependent data** (a `Z`, a
`Term Σ ty.int`, a plain `nat`) and rebuild the wrapped subterm so the caller
compares at a fixed type where `Term_eqb` is homogeneous. A rule that needs no
term pattern-matching at all should be a plain `Definition`. Use plain
`Equations` (not `(noind)`/`(noeqns)`) for anything you will `funelim`.

**7. The spec is `instpred d ⊣⊢ instpred F`, and `instpred` at world `w` is
ALREADY relative to `wco w`.** So `Some empty` is legitimate for a formula that
merely *follows from* the path condition — you are not claiming a tautology.
This is exactly how `secLeakT` / `pathconditions_contains_secLeakT_spec` work.
`MkBientails { fromBientails : forall ι, instprop (wco w) ι -> P ι <-> Q ι }`
(`Worlds.v:594`): `constructor`, **two** intros, then an iff. `instpred empty`
needs `instpred_dlist_empty`'s `fromBientails` (idiom at `Solver.v` ~2232).

**8. Prove at `instprop` (plain Prop) level, lift ONCE.** `instpred_prop`
(`Worlds.v:790`) bridges them; there is no need for any Iris reasoning.
`instprop_formula`'s relop case is
`match bop.eval_relop_relprop op (inst t1 ι) (inst t2 ι) with SyncVal p => p | _ => False end`.
Working structure: inversion lemmas for each recognizer (`funelim`, cf.
`bvadd_cancel_pair_spec`) → per-formula soundness → induction over the
`PathCondition` → one lift.

**9. Decide the publicness guard deliberately.** `formula_relop` has the
`NonSyncVal ⇒ False` wall (`secret-data-walls`), so a rule that must *hold* for
a secret operand needs `secLeakT` — that is why `try_bvadd_cancel` has one.
Two ways to legitimately not need it: `formula_propeq` has no wall at all
(`try_bvadd_cancel_propeq`), and if you *derive from a hypothesis that mentions
the operand under the same wall*, the secret case is vacuous because the
hypothesis is itself `False` (`try_fetch_bound`). Check which case you are in
rather than copying a guard.

**10. Iteration order, because `Solver.v` is expensive and semi-opaque.**
`rocq_compile_file` cannot build it (`-arg -w all`, see `rocq-implementation`
§1); `make -f Makefile.coq theories/Symbolic/Solver.vo`, ~5m45s, and it
invalidates every downstream `.vo`. Position-mode `rocq_start` past ~line 2400
times out, and even where it succeeds you cannot `Check` the definitions —
they live in `Module Import GenericSolver` inside `Module Type GenericSolverOn`,
so that inner `Import` does not escape and even *pre-existing* siblings are
unreachable from a position state. Consequences:

- **Prove the semantic core in preamble mode first.** `Bitvector` and
  `Syntax.TypeDecl` both load standalone, and `ty.liftBinOpRV`/`liftUnOpRV` are
  what `bop.evalRel`/`uop.evalRel` reduce to — so the real RelVal argument,
  including the `SyncVal`/`NonSyncVal` split, restates faithfully there and runs
  in ~100 ms. `RiscvPmp.Sig` does **not** load in a preamble.
- The definitions' own elaboration genuinely cannot be pre-checked. Accept one
  build for that, and keep them as non-dependent as possible (see 6) so there is
  little left to fail.
- **After the build, unit-test FIRING before anything big.** A file requiring
  only `RiscvPmp.Sig` plus `Import GenericSolver`, with
  `Eval vm_compute in <your recognizer> <term transcribed from the step-1 dump>`
  — and **negative cases**, since a rule returning `empty` fails unsoundly, not
  loudly. This localises "which function did not match" instead of leaving you
  to bisect a residual count, and it costs ~60 s rather than a full chain.
- **Then one real example with a real `Qed`.** Residual counts taken under the
  `Admitted` protocol do *not* show the VC still closes, and a downstream closer
  like CFGVer's `solve_symbase_fetch` is `solve [...]`, which fails if reached
  with a goal it cannot handle.
- **Then `./scripts/gate.sh`** — this is the only check that catches an unsound
  `empty`, via `Print Assumptions` on the end theorems. Use `GATE_JOBS=1` on a
  ≤16 GB box; the default `-j3` runs three ~3 GB `coqc` processes.

Externally your definitions are `RiscvPmpSignature.GenericSolver.<name>`.

## Generic statement executor (`theories/MicroSail/SymbolicExecutor.v`)

`sexec (inline_fuel : nat) : Exec` (~line 609) is the top-level `Fixpoint`
every case study calls to symbolically execute a `Stm`. Its dispatch
(~line 426-490) is a plain match over statement constructors — `stm_val`,
`stm_let`, `stm_call`, `stm_pattern_match` (→ `demonic_pattern_match`, above),
`stm_seq`, `stm_read_register`, etc.

## Refinement lemmas (`theories/Refinement/Monads.v`)

Every combinator above has a `refine_<name>` lemma (e.g.
`refine_demonic_pattern_match'`, ~line 574-595) proving
`ℛ⟦R...⟧ (CPureSpec.<name>) (SPureSpec.<name>)` — the symbolic combinator
agrees with its concrete counterpart under the `ℛ⟦⟧` logical relation.
Proofs are Iris-based (`iIntros`/`iApply (refine_bind ...)`/`rsolve`
patterns). This is the layer that has to keep working if you touch a core
combinator: changing `demonic_pattern_match'`, for instance, means
re-proving `refine_demonic_pattern_match'`, not just editing the function —
and since every case study goes through these same combinators, "no
regression" realistically means recompiling more than just one case study.

## Slow/exponential symbolic execution: look at TERM SIZE, not forking

(Corrected 2026-07-19 — an earlier version of this section blamed
`demonic_finite`'s unconditional forking; probes disproved that, superseded
text archived in
`.claude/archive/term-explosion-diagnosis-correction-2026-07-19.md`.)
The executor's symbolic register store holds raw `Term`s with **no
sharing**: a loop body that rebuilds a register from k ≥ 2 copies of its own
previous value multiplies that term's size by k per iteration (k^trips
total), and every subsequent peval/solver pass plus the final vm_compute
pays linearly in term size. CFGVer's key_schedule masking loop (3 copies of
the secret per iteration, ~2.5×/trip measured) is the worked example — full
write-up in **cfgver-executor**'s "Backward-branch loops" section and the
`project-key-schedule-loop-scaling` memory note. The same holds in any case
study: diagnose by counting per-iteration references to registers holding
growing symbolic terms, not by counting branches (concrete-scrutinee
branches are pruned at construction, see above).

## Fix directions (not yet attempted)

A `peval`/decidability short-circuit in `demonic_pattern_match'` would NOT
help the loop-scaling problem above — construction-time pruning already
covers the concrete-scrutinee case. The relevant directions are: value
naming/sharing at register writes (fresh symbolic name + definitional
equation per write, SSA-style — beware `unify_pathcondition` substituting
the definition straight back in), a sharing-aware term representation
(hash-consing), or, at the contract level, loop-invariant-style VCs (fresh
symbolic register values each iteration). Any core change here still
carries the refinement burden: the matching `refine_*` lemmas must be
re-proved and every case study recompiled. Tracked in `TODO.md`'s
`GHASH::key_schedule` section.
