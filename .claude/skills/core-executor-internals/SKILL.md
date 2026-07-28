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

### Known bug: `formula_simplifies` burns a path-condition entry

`assumption_formula` consumes exactly one `wco` entry per recursion step and
never revisits it. The `formula_relop bop.eq` case (`Solver.v` ~2834) returns
`Some (propeq t1 t2 ∧ secLeak t1 ∧ secLeak t2)` **ignoring its `fact`
argument** — an unconditional rewrite in a function whose contract is "simplify
`hyp` given `fact`". The entry is therefore spent without being used, and a
`secLeak t1` sitting exactly there is left undischarged. Measured 2026-07-28
with `wco = [secLeak p]` and goal `p = p+p`: `secLeak p` survives, and adding
**any** unrelated newer entry makes it discharge. Usually masked by
`combined_solver`'s repeated passes. Fix = apply `fact` to the two spawned
conjuncts; needs a `formula_simplifies_spec` update, recorded as a TODO at the
site. For the `secLeak`-specific semantics these formulas carry, see
**secret-data-walls**.

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
