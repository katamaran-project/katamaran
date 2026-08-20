# PLAN — migrate CFGVer's instruction surface from `AST` to `AnnotInstr`

Status: **DESIGN, not started. Written 2026-08-19.** No code exists yet.

## Why

Two capabilities we currently lack, both hit repeatedly on 2026-08-19:

1. **State inspection at intermediate stages.** The symbolic heap is *not* in the
   VC — it is an `SHeapSpec` accumulator, visible only where a debug or error
   node was planted (`diagnostics/lvar-lookup-cost-drivers.md` §1). Today the only
   snapshot point is the precondition boundary, and fuel truncation gives `False`
   with no state (`error msg => False` in both `safe` and `safe_debug`). A
   per-position `AnnotDebugBreak` fixes this.
2. **Replacing a runaway term with a fresh logical variable.**
   `diagnostics/lvar-lookup-cost-drivers.md` §8 and the `br_divrem` analysis show
   the muladd blocker is exponential *term* growth: the occurrence vector is
   multiplied per trip by `[[7,4],[4,6]]`, dominant eigenvalue
   `(13+√65)/2 ≈ 10.53`, giving ~10³¹·⁶ leaves at the real 31 trips. **No `peval`
   rule can fix this** — collapsing the borrow idiom only takes λ to ≈6.56, and
   every matrix entry stays ≥ 2 because the mask depends on both accumulators and
   is consumed by both. The only fix is to spend a logical variable per trip to
   buy term size, and `AnnotLemmaInvocation` is the syntax for that.

`AnnotInstr` already exists in `BlockVer/Verifier.v:490` and
`BinaryBlockVer/Verifier.v:444` (which has a *relational* annotated executor —
the closest thing to a template). It has never been used by CFGVer, and the only
mention outside BlockVer is `.claude/TODO.md:195`, "Ask Dominique or Sander
whether `AnnotInstr` is worth looking at". BlockVer is commented out of
`_CoqProject`, has no `.vo` in this tree, and `Machine.v` has changed since with
an explicit "no longer checked against BlockVer" disclaimer — so **this plan
ports the mechanism, it does not revive BlockVer.** Nothing here requires
BlockVer to compile.

## The design decision

Annotations are **ghost**: they occupy no bytes, have no encoding, and must not
appear in the machine semantics. CFGVer's table is keyed by pc *terms* and
`table_of_list` assigns `off, off+4, …` per element (`Tables.v:208`), so a naive
`list AnnotInstr` would let an annotation consume an address slot. That must not
happen.

**Chosen shape: annotations are a ghost PREFIX attached to the following
instruction, and the grouping happens inside `table_of_list`.**

```coq
(* CFGVer's own ghost annotation — no AnnotAST constructor, since the AST is
   already the table entry's payload. *)
Inductive Annot :=
| AnnotDebugBreak
| AnnotLemmaInvocation {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp [ctx]) Δ).

Inductive AnnotInstr := AnnotAST (i : AST) | AnnotGhost (a : Annot).
```

- authoring stays flat (`list AnnotInstr`), BlockVer-style;
- `table_of_list : … -> list AnnotInstr -> list (Term Σ ty_xlenbits * list Annot * AST)`
  does grouping **and** address assignment in one pass, advancing the offset only
  on `AnnotAST`;
- `strip : list AnnotInstr -> list AST` keeps only the `AnnotAST`s and is what
  every trusted-layer and concrete-side consumer sees.

**Rejected alternative: a separate pc-keyed annotation table.** Cheaper (leaves
`SInstrTableW` alone) but it reintroduces exactly the failure mode
`Verifier.v:252`'s comment documents for the word column — two lookups per step
that must agree, forcing a "tables disagree" error case the executor cannot rule
out and the refinement proof must carry, plus a duplicate
`persist`/`subst`/faith family. That comment says both shapes were implemented
for the word and fused was smaller; the same argument applies here, so follow the
existing precedent and fuse.

**Precedent for the column itself:** `SInstrTableW` already carries an extra
middle column (the instruction word). Adding a second is the same move, and the
`persist_itableW` / `subst_itable` / `lookup_instr` / `itable_rel` family already
shows every site that needs updating.

**Authoring ergonomics come free:** `FemtoKernel.v:160` already does
`Local Coercion AST_AnnotAST (a : AST) := AnnotAST a`. With that coercion in
`Example/Prelude.v`, all 12 existing `*_instrs : list AST` literals keep parsing
unchanged. This is the single biggest cost saver in the migration.

## The invariant that makes this safe

> **The trusted statement surface must be unchanged for every currently-verified
> program, verified by `reflexivity`, not by inspection.**

`Noninterference.v` mentions `AST` in five places (`pcOutOfInstrs_exitCond`,
`pcOutOfInstrs_fallthrough`, `mem_has_instr`, `mem_has_instrs`, and line 269).
**None of them change.** They keep taking `list AST`; the callers feed them
`strip prog`. For an unannotated program `strip` must reduce to the original
list *syntactically*:

```coq
Lemma strip_id_<prog> : strip <prog>_instrs = <prog>_instrs_ast.
Proof. reflexivity. Qed.
```

one per program, so the 14 existing end theorems are provably about the same
machine program as before. If any of these needs more than `reflexivity`, the
migration has changed the trusted surface and must stop.

## Phases and gates

### Phase 0 — feasibility probe, no migration (½ day)

Add `Annot`/`AnnotInstr` + `strip` + the coercion in a throwaway `ZZAnnot*.v`,
and check three things that would each sink the design:

1. the coercion really makes an existing `list AST` literal typecheck as
   `list AnnotInstr` (FemtoKernel says yes; confirm in CFGVer's notation soup);
2. `strip` on a coerced literal is `reflexivity`-equal to the original;
3. a trailing ghost run (annotation after the last instruction) has nowhere to
   attach — decide now whether that is a hard error or gets an explicit
   `cfg_exit_annots` field. **Recommend: hard error in v1**, since the loop
   invariant we actually want attaches to the back-edge target, which is an
   instruction.

**GATE 0:** all three hold, in a file that compiles. If (1) fails the whole
"existing examples untouched" premise dies and the cost estimate below triples.

### Phase 1 — symbolic side only (2–3 days)

`Verifier.v`, `Tables.v`, `Contracts.v`, `GenContract.v`. `SInstrTable` /
`SInstrTableW` gain the `list Annot` column; `table_of_list` groups; `lookup_instr`
returns it; `sexec_cfg_addr` runs the ghost prefix before `sexec_instruction`.
Only `AnnotDebugBreak` is interpreted in this phase — `AnnotLemmaInvocation` gets
a `SymProp.error "not yet supported"` case, so the constructor exists without any
soundness debt.

`cfg_instrs : list AnnotInstr` in `CFGVerifierContract`; every `GenContract`
builder takes `list AnnotInstr` and passes `strip` to the trusted-layer premises
(`exits_of_list`'s `length instrs` becomes `length (strip instrs)`).

**GATE 1:** the light branch builds; all 12 `Example/*.v` compile **unchanged**
apart from an import; all 12 `strip_id_*` lemmas close by `reflexivity`; the
per-example VC cost is within noise of today's (the ghost column is `[]`
everywhere, so it should be *identical* — a measurable regression here means the
column is being persisted/substituted when empty, which is a bug to fix, not
accept).

### Phase 2 — concrete mirror and refinement (1–2 weeks, the risky phase)

`VerifierRel.v` (`cexec_cfg_addr`, `RefineCompat`, `rexec_cfg_addr`),
`TablesRel.v` (`itable_rel` gains the column).

`AnnotDebugBreak` is **semantically transparent** — `safe (debug d k) = safe k`
(`Propositions.v:361`) — so the concrete mirror ignores it and the relational
obligation is a no-op. That is what makes Phase 2 tractable at all.

**Risk, named:** `cfgver-rsolve` documents `rsolve` failing, hanging, or eating
multiple GB, and `RefineCompat` instances being hand-written. A new table column
touches every instance. Budget accordingly and expect this phase, not Phase 1, to
dominate.

**GATE 2:** heavy branch builds; `scripts/gate.sh` green at `GATE_JOBS=1`; all 14
end theorems axiom-clean.

### Phase 3 — `AnnotDebugBreak` as a usable tool (1 day)

Plant one at a chosen pc and dump `(pathcondition, heap)` per trip via
`DebugCFGVerifierContract` + `vc_debug` (`safe_debug` keeps `Debug` records;
`prune` preserves debug nodes, `Propositions.v:1221`). This is the deliverable
that pays for Phases 0–2 on its own.

**GATE 3:** per-trip heap and path condition dumped for `ZZKslHeapCommon` at
`t=2`, showing the heap is static (which this plan asserts but has not measured).

### Phase 4 — `AnnotLemmaInvocation` (separate effort, do NOT bundle)

Symbolic `call_lemma (LEnv l) args` on both sides plus the relational lemma.
CFGVer's `LEnv` is already non-empty (`Spec.v:631` `lemma_open_gprs`,
`lemma_close_gprs`, `lemma_open_ptsto_instr`, …), so adding a lemma is an
established pattern rather than new infrastructure.

**This phase does not solve muladd, and saying so is the point.** The abstraction
lemma — "consume `A0 ↦ <huge term>`, produce `∃v, A0 ↦ v ∗ inv v`" — is only as
sound as its `LEnv` proof, and `inv` must be weak enough to hold every trip and
strong enough to still prove the postcondition. That is the loop-invariant design
problem, per example. **`AnnotInstr` is a delivery vehicle for
`PLAN-loop-invariant.md`, not an alternative to it**, and Phase 4 should be
costed there.

## Before funding this: what it buys, in the required terms

Per `cfgver-scaling-diagnostics`' "before proposing a fix":

1. **Predicted speedup at the N we care about: zero, for Phases 0–3.** The ghost
   column is empty for every existing program, so cost is unchanged by
   construction (GATE 1 checks this). The payoff is *capability*, not speed.
2. **Constant factor or exponent?** Phases 0–3: neither. Phase 4 plus a real
   invariant is an **exponent** change — λ ≈ 10.53 → 1 for `br_divrem` — which is
   the only thing that makes its 31 trips reachable.
3. **Is the mechanism still dominant after the fix?** For muladd, yes: term
   growth is the whole story there (heap fixed by construction, |Σ| flat at 67,
   mints/nodes/`sigint` all exactly proportional to steps). Unlike the
   `select_last_k` episode there is no larger driver hiding behind it.

## Honest risks

- **Phase 2 is the whole cost.** If `rsolve`/`RefineCompat` fights the new
  column, this plan's estimate is wrong by a lot. Consider a Phase-1-only
  landing (symbolic side, `Admitted` refinement, nothing merged) purely to get
  the diagnostic capability on a branch, and decide about Phase 2 after.
- **A ghost annotation that fires per-trip changes the executed step count** if
  interpreted, which perturbs exactly the measurements we use it to take. Dump
  with it, measure without it.
- **`strip` in the trusted premises is a real change to how the statements are
  *written***, even when provably the same list. Anyone auditing
  `Example/*Result.v` will now have to check `strip` is a plain projection. Keep
  its definition to one line and the `strip_id_*` lemmas per program.
- Not measured, only read: the claim that the empty ghost column costs nothing.
  GATE 1 exists because I do not believe it on faith.

## Files

| file | change |
|---|---|
| `Verifier.v` | `Annot`/`AnnotInstr`, `SInstrTable(W)` column, `persist_itable(W)`, `subst_itable`, `lookup_instr`, `sexec_cfg_addr` ghost cases |
| `Tables.v` | `table_of_list` groups + assigns addresses; `exits_of_list`/`exits_of_offs` over `strip` |
| `Contracts.v` | `cfg_instrs : list AnnotInstr`; `CFG_VC_triple` |
| `GenContract.v` | all builders take `list AnnotInstr`, pass `strip` to trusted premises |
| `VerifierRel.v` | `cexec_cfg_addr` mirror, `RefineCompat`, `rexec_cfg_addr` |
| `TablesRel.v` | `itable_rel` column |
| `Adequacy.v`, `EndToEnd.v` | `strip` at the `mem_has_instrs` / `gen_implpre` boundary |
| `Noninterference.v` | **UNCHANGED** — still `list AST`. This is the invariant. |
| `Example/Prelude.v` | the `AST → AnnotInstr` coercion |
| `Example/*.v` (12) | ideally import-only; plus one `strip_id_*` lemma each |
| `Example/*Result.v` (12) | ideally unchanged |
| `asm_to_ast.py` | unchanged — keeps emitting `list AST`, the coercion adapts it |
