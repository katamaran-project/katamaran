# PLAN — migrate CFGVer's instruction surface from `AST` to `AnnotInstr`

Status: **SUPERSEDED, 2026-08-20 — `AnnotInstr` as committed (2274a22b,
323db24c) has a foundational shape bug and needs to be redesigned before
Phase 2 is attempted again.** See the 2026-08-20 "Foundational rethink" Log
entry below before touching this again: `AnnotInstr := AnnotAST i | AnnotGhost
a` is a SUM (either a bare instruction or a bare annotation), not a PRODUCT
(an instruction together with its annotations) — that's the root cause of
`table_of_list`'s grouping-fold complexity, the "trailing ghost is a hard
error" special case, and is suspected (not confirmed) to be involved in
Phase 2's `rexec_ghost` compile hang. Phase 0/1's commits stay in git history
as reference for the coercion/import mechanics, but `Annot`/`AnnotInstr`/
`table_of_list`'s core shape needs reworking, not incremental patching.
**cfgver-executor**'s "Ghost annotations" section still describes the
committed (pre-rethink) Phase 1 code accurately — it has not been touched to
match this entry, since the code it documents hasn't changed yet.

## Log

**2026-08-20, Phase 0.** GATE 0 passed in a throwaway probe
(`Example/ZZAnnotProbe0.v`, gitignored, still on disk). Two things this
write-up's "Authoring ergonomics come free" section understated, found by the
probe:
1. The `AST -> AnnotInstr` coercion only fires inside a FRESH `[...]` literal
   if a companion `Local Arguments List.cons {_} & _ _.` is also in scope
   (FemtoKernel.v:160 has this line too, silently doing the real work).
2. A SECOND coercion (`list AST -> list AnnotInstr := List.map`) is needed to
   reuse an EXISTING `_instrs : list AST` `Definition` (e.g. `cmovznz4_instrs`)
   unedited — the per-element coercion does not fire on an already-elaborated
   value, only while elaborating a fresh literal. Both are required together;
   this is why "all 12 examples keep parsing unchanged" needed two coercions,
   not the one FemtoKernel precedent alone suggested.

**2026-08-20, Phase 1a (`Verifier.v` only, commit 2274a22b).** `Annot`/
`AnnotInstr`/`strip`, the `DebugAnnot` record (mirrors `BlockVer`'s
`DebugBlockver`; a currently-compiling reference implementation for the whole
mechanism, including a WORKING relational refinement proof for it, lives on
`main`'s `BlockVer/PartialVerifier.v` — `KatamaranRel`'s own `BlockVer/` copy is
disabled and does not compile, don't use it as the reference), the ghost column
on `SInstrTable`/`SInstrTableW`, `sexec_ghost`/`sexec_ghosts` (only
`AnnotDebugBreak` interpreted; `AnnotLemmaInvocation` errors), and
`sexec_cfg_addr` running the ghost prefix. `rocq_compile_file mode=full`: clean.

One design-time bug caught and fixed BEFORE it could break anything downstream:
the two coercions were first written `Local Coercion`, which never survives
export. Fixed to plain `Coercion` (Prelude.v `Require Export`s `Verifier.v`, so
a non-Local coercion there reaches every `Example/*.v`) — see
**cfgver-executor**'s "Ghost annotations" section for why this matters and
exactly which two coercions are needed.

A real, generic Rocq/Katamaran gotcha surfaced and is now written up in
**core-executor-internals**: `sexec_ghost`/`sexec_ghosts` (niladic — no
world-indexed value argument) had to be declared with an implicit `{w : World}`
(`chunk_gc`'s shape), not `⊢`/`Valid` — a bare `⊢`-typed action with nothing to
pin its world from unification fails in a bind chain in ways that read like
notation bugs but aren't.

**2026-08-20, Phase 1b (`Tables.v`/`Contracts.v`/`GenContract.v`, commit
323db24c, done by a delegated Haiku session).** `table_of_list` groups ghosts
and only advances the address on `AnnotAST`; `CFGVerifierContract.cfg_instrs`
and all six `gen_contract*` builders take `list AnnotInstr`; the four builders
that compute an exit offset/bound from `length instrs` switched to
`length (strip instrs)`. GATE 1 verified green (by me, after the delegated
session stopped short of running it): `Tables.v`/`Contracts.v`/`GenContract.v`
compile, all 12 `Example/*.v` compile unchanged, 9 of them have a
separately-named `_instrs` list and all 9 pass a `strip_id_<prog>` reflexivity
check (the other 3 — `Jumps`/`MvSwap`/`SetX2` — build their list inline inside
the contract literal, so there is no named object to state the lemma about;
their unchanged compilation is the only evidence for those three); a timing
spot-check on `Cmovznz4`/`KeyScheduleLoop` showed nothing looking like a
regression.

**Two real gotchas from this step, both written up more fully elsewhere:**
- `rocq_compile_file`'s dune-fallback path (this subtree has no `dune` file at
  all, so every compile here goes through a `coqc`-into-`_build/default`
  fallback) can fail to resolve a SIBLING file's freshly-rebuilt `.vo` even
  right after that sibling compiled clean — read as a real error, it looks
  exactly like a missing/misnamed module. **`make -f Makefile.coq <target>.vo`
  is the reliable path**; full account in **rocq-implementation**'s tooling
  section.
- The delegated session, hitting that same confusion, took a shortcut: it
  switched `Tables.v`/`Contracts.v`/`GenContract.v`'s `Require` of `Verifier.v`
  from bare (qualified-name-only, the documented convention — see
  `CFGVer/CLAUDE.md`'s "Importing CFGVer.Verifier downstream") to
  `Require Import` (unqualified). This works today ONLY because BlockVer is
  disabled in `_CoqProject` on this branch, and is flagged as a latent,
  not-yet-reverted deviation in `CFGVer/CLAUDE.md` — read that note before
  touching these three files' imports again, and before ever re-enabling
  BlockVer alongside CFGVer.

**GATE 2 status (not started):** `VerifierRel.v` and `TablesRel.v` still assume
the pre-migration table shapes and fail to compile — confirmed, expected, not a
regression. This is genuinely the risky phase the original write-up below
warned about; nothing about Phase 1 landing easily should be read as evidence
Phase 2 will too. `main`'s `BlockVer/PartialVerifier.v` (see Phase 1a above) is
now known to have a short, currently-compiling `rexec_annotated_block_addr`
proof (`iInduction b; cbn; rsolve; destruct instr; cbn; rsolve` — a few lines)
worth reading before starting Phase 2's `rexec_cfg_addr` update, as real
precedent rather than just the disabled `KatamaranRel` copy's text.

**2026-08-20, Phase 2 attempt and foundational rethink.** A session attempted
Phase 2 on `VerifierRel.v`/`TablesRel.v`. The mechanical tuple-shape fixes
(propagating the ghost column through `itable_rel`/`itable_relW`/`wtable_rel`/
the `persist`/`forgetting` lemmas/`rexec_cfg_addr`'s `lookup_instr`
destructuring) went fine and are worth redoing verbatim once the type below
lands — that part of the diff is in `git stash` (`"AnnotInstr Phase 2 WIP
..."`) on `KatamaranRel`, not committed, not applied. One incidental find
worth keeping regardless of the redesign: `rexec_triple_addr`'s own signature
had a hardcoded literal table type (`list (Term Σ ty_xlenbits * AST)`)
instead of the `SInstrTable (wlctx Σ)` alias, so it silently didn't pick up
the word-column change either, historically — always use the alias, never
spell out the tuple.

The actual blocker: a new `rexec_ghost` lemma (bridging the new
`sexec_ghosts` step to a concrete no-op) hung at compile (300s+, `Set
Typeclasses Debug.` didn't help, `rocq_start` OOMs pet on this file
regardless of position/theorem mode) on its `AnnotDebugBreak` case, under
*every* tactic tried — including the exact idiom that compiles fine for the
equivalent case in `main`'s `rexec_annotated_block_addr` (`destruct; cbn;
rsolve.`). Root cause NOT found. Leading (unconfirmed) hypothesis: unfolding
`sexec_ghost`'s `match` forces the kernel to carry motive/type information
for the `AnnotLemmaInvocation` branch too — a dependently-typed constructor
(`AnnotLemmaInvocation {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp [ctx]) Δ)`) — even
while computing the unrelated `AnnotDebugBreak` branch, since the hang
reproduced identically with that branch fully `admit`ted. Not proven; worth
checking first if this resurfaces.

Digging into *why* this needed a lemma BlockVer never needed (BlockVer has no
`sexec_ghost`/`sexec_ghosts` split at all — its `sexec_annotated_block_addr`
recurses on the `list AnnotInstr` itself and handles ghosts inline) surfaced
a foundational problem with `AnnotInstr` itself, not just with this one
proof:

- `AnnotInstr := AnnotAST (i : AST) | AnnotGhost (a : Annot)` is a **sum
  type** — a value is either a bare instruction or a bare annotation, never
  both. `table_of_list`'s `pending`-accumulator grouping fold exists purely
  to repair that after the fact (walk the list, collect ghosts, attach them
  to the next `AnnotAST`), and the "a trailing ghost run is a hard error"
  rule (Phase 0's GATE 0 decision, item 3) exists because the sum type can
  represent a state (a dangling ghost with nothing to attach to) that should
  never have been representable in the first place.
- A tempting-looking simplification — store raw `AnnotInstr` in the table,
  one entry per original list element, letting a ghost share its following
  instruction's address rather than getting its own — was checked concretely
  and rejected: `lookup_instr` is one `List.find` (first match wins), so if
  a ghost entry and its instruction entry share an address, `lookup_instr`
  returns the ghost forever and the executor can never reach the real
  instruction at that address, on any visit, ever. Not a style problem, a
  correctness bug.
- **The fix: make `AnnotInstr` a product, not a sum** —
  ```coq
  Record AnnotInstr := MkAnnotInstr
    { ai_ghost_before : option Annot
    ; ai_instr        : AST
    ; ai_ghost_after  : option Annot  (* see below; may start absent *)
    }.
  ```
  With this, `table_of_list` becomes a straight `mapi` (one address per
  record, no grouping fold, no `pending`), "trailing ghost with nothing to
  attach to" becomes unrepresentable rather than an error case to declare,
  and "what happens if you jump to this pc" has one unambiguous answer
  everywhere (a whole record, always). `option Annot` rather than `list
  Annot` additionally drops `sexec_ghosts`/`rexec_ghosts` entirely (no
  current use case wants two ghosts stacked on one instruction) — under this
  shape only `sexec_ghost`/`rexec_ghost` need to exist, non-recursive.
  `itable_rel`/`itable_relW`/`cexec_cfg_addr` need no change beyond widening
  the wildcard pattern — they already ignore the ghost column(s) entirely.
- **Ghosts run BEFORE their instruction** (matches the current, already-
  implemented order — this doesn't need to change, only how it's
  represented). Both current/planned annotation kinds need it: a per-trip
  `AnnotDebugBreak` dump should show the state as the trip *begins* (Phase
  3's own goal), and Phase 4's `AnnotLemmaInvocation` (replace a term with a
  fresh logical variable) is useless if it runs after the instruction that
  would otherwise consume the huge term — the abstraction has to happen
  before that instruction executes.
- **An `ai_ghost_after` slot is easy to add later, not merely for symmetry.**
  Once branching exists, "after instruction `i`" and "before `i`'s successor
  `j`" are NOT the same thing — the latter only fires if the branch that
  reaches `j` is actually taken, the former fires every time `i` executes
  regardless of where control goes next. Adding it later is mechanical: one
  more `option Annot` field, one more bind in `sexec_cfg_addr`'s chain
  (threading its world-substitution through, same move already made three
  times for `chunk_gc`/ghost-before/the instruction itself), and reusing the
  *same* `rexec_ghost` lemma a second time in `rexec_cfg_addr`'s proof — it's
  generic over "one `Annot`, refined by a concrete no-op" and doesn't care
  where it's invoked. `itable_rel`/`cexec_cfg_addr` still need nothing.
- Also recommended, independent of the product-vs-sum fix: defer
  `AnnotLemmaInvocation`'s dependent constructor out of `Annot` until Phase 4
  actually implements it (right now it's a stub `error "not yet supported"`
  case with no soundness content) — matches the plan's own "Phase 4 is a
  separate effort, do NOT bundle" instruction below, keeps the type flat
  (`AnnotInstr := AnnotAST i | AnnotDebugBreak`-shaped for now, no `Annot`
  wrapper needed until there's a second ghost kind), and removes exactly the
  dependently-typed constructor the hang hypothesis above points at.

**Net effect: Phase 0 and Phase 1 need to be redone against the corrected
type**, not just Phase 2. The 2274a22b/323db24c commits stay as reference for
the coercion mechanics (`AST_AnnotAST`/`list_AST_AnnotInstr`, the `Local
Coercion` pitfall, the `{w}`-vs-`⊢` gotcha) — those don't depend on
sum-vs-product and should still apply — but `Annot`/`AnnotInstr`/
`table_of_list`/`SInstrTable`/`SInstrTableW` all need to be rebuilt against
the record shape above before Phase 1's GATE 1 can be re-claimed, let alone
Phase 2 attempted again. Nothing has been committed reflecting any of this;
`KatamaranRel` currently sits exactly at 323db24c.

---

Original design write-up follows, unedited except where a numbered Log entry
above says otherwise.

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
