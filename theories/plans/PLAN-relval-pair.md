# PLAN — RelVal as a plain pair (drop the SyncVal tag from the semantics)

Status: PLAN, not started (2026-10-06). Branch to be created off `KatamaranRel`
(proposed name `issue/relval-pair`); `KatamaranRel` is untouched until merge.

## 0. One-paragraph summary

`RelVal σ = RV (Val σ)` has two constructors, `SyncVal v` and `NonSyncVal vl vr`,
and the tag is *visible to the semantics*: `SyncVal v ≠ NonSyncVal v v`, and
`secLeak`, `formula_bool`, `formula_relop` all read it. Nothing in the Iris
soundness needs that. `semWP2` is defined over plain `Val` stores, `reg_pointsTo2`
and `mem_inv2` only see `projLeft`/`projRight`, `semTriple`'s postcondition
picks its `RelVal` existentially, and every consumer of `SyncVal` in the model
(`leak_sound`, `iris_rule_stm_assertk`, `iris_rule_stm_pattern_match`) only uses
it as evidence that `projLeft = projRight`. This plan makes `RelVal σ` a plain
pair, keeps `SyncVal v` as a *definition* for `(v, v)`, and keeps `secLeak` as
the name of the relational atom, now meaning `projLeft = projRight`. The
interface stays the same. What changes is that everything previously cut off by
`SyncVal a ≠ NonSyncVal a a` becomes repairable (§6).

This is Binsec/Rel's semantics: the shared vs. paired split is not part of the
meaning, so "untainting" (concluding `secLeak` from a value-level equality) is
sound. Today it is not even expressible.

## 1. Decisions already made (by Emiel, 2026-10-06; don't re-ask)

- **Representation:** a pair. `SyncVal a` stays as a construct but is just a
  definition for `(a, a)`.
- **`secLeak` keeps its name and interface.** It now means "both projections are
  equal" instead of "tagged SyncVal".
- **Everything is still lifted.** Terms denote `RelVal`, and ops lift through
  `liftUnOp`/`liftBinOp`. This is NOT a move to two valuations or to a unary
  executor.
- **Solver/peval proofs should be done ONCE, side-generically, not twice.** The
  basis already exists: `rv_proj side` and `teq side` in
  `theories/Symbolic/PartialEvaluation.v:146–165`.
- **Separate branch.**

## 2. Decisions (all settled by Emiel, 2026-10-06; don't re-ask)

- **D1 (Phase 1): concrete representation. DECIDED: record.**
  A one-constructor record `RV A := NonSyncVal { rvL : A; rvR : A }` with
  `#[projections(primitive)]`, so `NonSyncVal (rvL x) (rvR x) ≡ x` holds
  definitionally and `NonSyncVal v v` *is* `SyncVal v` by conversion. (Rejected:
  `A * A`, because `RelVal (ty.prod σ1 σ2)` would become `(Val σ1 * Val σ2) *
  (Val σ1 * Val σ2)`, which collides visually and in unification with the
  `RVOfPair*` conversions.) With `NonSyncVal` as the constructor's name, the
  construction sites need no edit. Only *matches* on `SyncVal` need rewriting.
- **D2 (Phase 6, repair R2): guard for multi-case patterns. DECIDED: same
  case.** The executor asserts only that both sides take the same CASE. The
  payload may differ. Design in R2 (§6). Phases 1–5 keep today's
  `secLeak scrutinee` guard (sound, just stronger than needed).
- **D3 (Phase 5): implicit publicness. DECIDED: comparisons become pointwise;
  this is the main selling point.** A `relop`/`bool` over a `NonSyncVal` stops
  failing and means "holds on both sides". Theorems whose preconditions relied
  on the old collapse get strictly stronger, and that is intended. Add an
  explicit `secLeakvar` only where a *proof* needs agreement (e.g. a loop
  counter that later reaches a branch or a leak), not to preserve old
  statements. Still LIST every trusted statement whose meaning changed, in
  the merge commit message.

## 3. New semantics, definition by definition

| Definition (file) | Today | After |
|---|---|---|
| `RV A` (`Syntax/TypeDecl.v:170`) | `SyncVal a \| NonSyncVal l r` | one constructor `NonSyncVal l r` (D1a); `SyncVal a := NonSyncVal a a` |
| `projLeftRV`/`projRightRV` | match | projections (primitive) |
| `liftUnOpRV`/`liftBinOpRV` (`TypeDecl.v:226,270`) | Sync fast path, else Nonsync | pointwise, no case |
| `isSyncVal`/`isSyncValProp`/`secLeak_bool` | tag test | `bool_decide (l = r)` / `l = r` (needs `Val` eq_dec, which exists) |
| `secLeak` (`Syntax/Formulas.v:117`) | `SyncVal ⇒ True`, `NonSync ⇒ False` | `projLeft rv = projRight rv`; `secLeakOtherDef` becomes a lemma by eta |
| `formula_bool t` (`Formulas.v:142`) | `SyncVal p ⇒ p = true`, `NonSync ⇒ False` | `projLeft = true ∧ projRight = true` |
| `formula_relop` (`Formulas.v:147`), `eval_relop_relprop` (`Syntax/BinOps.v:367`) | `SyncVal p ⇒ p`, else `False` | `pL ∧ pR` |
| `formula_propeq` | `RelVal` equality (tag-sensitive) | pair equality = both projections equal |
| `RVOfPairToPairOfRV`, list/record/union/tuple (un)folds (`TypeDecl.v:622–800`) | lose publicness on split | exact, componentwise |
| `relValOfVals` (`Syntax/Patterns.v:428`) | `if eq_dec then SyncVal else NonSyncVal` | the identity (`NonSyncVal v1 v2`); delete |

**Soundness invariant to keep in view.** Every formula except `secLeak` is
*pointwise* (holds on both sides), and `secLeak` is the only relational atom.
`formula_propeq` is pointwise too once `RelVal` equality is pair equality.

## 4. The "prove it once" bridge (Phase 2; everything later leans on it)

1. `rv_ext : (∀ side, rv_proj side a = rv_proj side b) → a = b`. This is eta, by
   `reflexivity` under D1a.
2. `rv_proj_lift{Un,Bin}Op : rv_proj side (liftBinOp f a b) = f (rv_proj side a)
   (rv_proj side b)`. These already exist as `comProj{Left,Right}LiftBinOp`;
   restate them generically over `side`.
3. Optional, decide at Phase 3: a unary `inst1 : Term Σ σ → Env Val Σ → Val σ`
   and `rv_proj side (inst t ι) = inst1 t (env.map (rv_proj side) ι)`. With it,
   any `Val`-level fact about terms transfers in one line. Without it, `teq side`
   already covers equalities.
4. Formula version: for pointwise `F`, `instprop F ι ↔ ∀ side, instprop_side F
   side ι`. Solver rules that only rewrite pointwise formulas are then proved
   once, for a generic `side`.

Consequence: `teq true t u → teq false t u → inst t ι = inst u ι` holds with NO
leaf condition (today `teq_leaves_inst`, `PartialEvaluation.v:328`, needs
`same_leaves`).

## 5. Cross-cutting risk: implicit publicness disappears

Today `formula_relop` and `formula_bool` on a `NonSyncVal` are `False`. So
*assuming* `x < n`, `x = 3`, or a bool path condition silently implies `x` is
public, and a precondition `x < n` makes the end-to-end theorem quantify only
over runs where `x` agrees. After the change these become pointwise and imply
nothing about agreement.

- **Proof breakage:** any proof that got `secLeak` from a relop/bool in the
  path condition or a precondition. Expect it in `Contracts.v`, `GenSegment.v`,
  `GenCompose.v` (loop counters `i < n` in invariants), and in `solve_vc`
  residuals. Fix with an explicit `secLeakvar`.
- **Trusted-surface change:** `Noninterference.v` and `Example/*Result.v` gain
  strictly STRONGER meaning wherever such a precondition sits on a non-`secLeak`
  variable (the theorem now covers runs where the two sides differ). Make a list
  per D3. Diff the trusted surface at the end as usual.
- **Branch soundness does not depend on this.** `demonic_pattern_match'`
  (`Symbolic/Monads.v`) asserts `secLeak` on the scrutinee before splitting,
  so the mixed case (left takes one branch, right the other) is excluded by
  the assertion, not by the `False` collapse. Verify this for every demonic
  branch in `Symbolic/Monads.v`, `Shallow/Monads.v` and CFGVer's `Verifier.v`
  in Phase 4. **A demonic branch with no `secLeak` assertion in front of it would
  become UNSOUND.** (Today it is vacuous on the mixed case for the same reason,
  so it is likely already guarded, but check rather than assume.)

## 6. Repairs: what becomes possible (the payoff)

Each is its own sub-phase and commit, after the port (Phases 1–5) is green with
unchanged theorems.

- **R1 peval drop-operand rules.** `x - x ⇝ 0`, `0 * x ⇝ 0`, `x & 0 ⇝ 0`, and
  ring normalisation without padding. Delete `same_leaves`, `is_sync`, the
  leaf certificate, `pad`/`pad_atom` (`PartialEvaluation.v:249–500`), and the
  "axioms FAIL" header comment. Re-enable upstream's `TermRing_bv` (disabled in
  196eae12 for exactly this reason) if it is cheaper than the local port.
- **R2 pattern matching: guard = "same case", per pattern class.**
  Method-Y canonicalization (`Patterns.v:424–720`, `Shallow/Monads.v:368–925`)
  collapses first, because reversal is injective per side.
  - *Single-case* (`PatternCase = unit`: `pat_var`, `pat_unit`, `pat_pair`,
    `pat_tuple`, `pat_record`, `pat_bvec_split`): NO guard. Fresh variables
    plus `assume propeq (reverse tt ts) t`. This removes the "NON-UNIQUE …
    NonSyncVal b b vs SyncVal b" fallbacks in `Symbolic/Monads.v`. The gain
    includes splitting a SECRET bitvector with `pat_bvec_split`.
  - *Case = value* (`pat_bool`, `pat_enum`, `pat_bvec_exhaustive`): keep
    `secLeak scrutinee`, which already IS "same case".
  - *Case + payload* (`pat_sum`, `pat_list`, `pat_union`): assert `secLeak` of a
    bool case test, then split demonically on the case, introduce fresh payload
    variables, and `assume propeq`. Under pointwise formulas (D3), agreement of
    the test bools is exactly "same case". New unops (none exist today:
    `UnOps.v` only has the `inl`/`inr` constructors):
    `uop.sum_is_inl : UnOp (sum σ τ) bool`,
    `uop.union_is U K : UnOp (union U) bool` (one bool per constructor, which
    avoids needing a `Ty` of union tags: agreement on every `union_is U K` ⟺
    same constructor; `unionk U` is finite),
    and for lists either `uop.list_is_nil` or `term_eq t nil`, if `relop eq` is
    available at list type. Nested `pat_union U p`: after the `K` guard, recurse
    into `p K` on the fresh payload variable, so the inner pattern applies its
    own class's guard.
  - Each new unop needs `peval` rules for a known constructor
    (`sum_is_inl (inl x) ⇝ true`, `union_is U K (fold K' x) ⇝ K =? K'`), so the
    guard on a syntactically known constructor closes by computation, as the
    `term_get_union` fast path does today.
  - Soundness side: `iris_rule_stm_pattern_match` (`Iris/BinaryWeakestPre.v:1265`)
    already only needs `is_Some (pattern_match_relval pat rv)`, i.e. same case,
    so the Iris layer is unchanged. Work goes into the symbolic and shallow
    `demonic_pattern_match`, their refinement lemmas, and the angelic
    counterparts (consume side), which take the same guard.
  - Regression probes: a secret `inl`/`inr` payload; `MemValue v` with secret
    `v` and an unknown constructor; a secret list head; `pat_bvec_split` on a
    secret word.
- **R3 componentwise publicness.** Splitting a pair/record/list keeps each
  component's `secLeak`. This comes automatically from Phase 1; add the
  `secLeak` split/join lemmas to the solver.
- **R4 untainting.** `secLeak t` provable by value reasoning: run `secLeakT` on
  the peval normal form (so `secLeak (x - x)` closes), and add a rule
  `secLeak t1 ∧ t1 = t2 ⊢ secLeak t2` from path-condition equalities.
- **R5 constraints on secrets.** `relop`/`bool` formulas over secrets are now
  meaningful assumptions (e.g. a secret range `k < 2^m` in a precondition).
  Revisit `secret-data-walls`: a wall now only fires where `secLeak` is
  *asserted* (branch, leak), not wherever a secret meets a formula.
- **R6 `iris_rule_stm_assertk`** (`Iris/BinaryWeakestPre.v:1097`): premise
  `∃ v, eval e δ = SyncVal v` becomes `secLeak (eval e δ)`. Do the same for any
  other `SyncVal`-shaped premise in that file.

## 7. Phases

Light check per phase (build the touched closure with `make -f Makefile.coq
<file>.vo` or rocq-mcp), ONE full gate at the end (`GATE_JOBS=1`).

0. **Baseline.** Create the branch. Record full-gate wall time plus the per-example
   VC times (the `vm_compute. solve_vc.` steps), and snapshot the trusted
   surface (`Noninterference.v`, `Example/*Result.v`, `*_instrs`/`*_specs`).
1. **Value layer: `Syntax/TypeDecl.v`.** New `RV` per D1, `SyncVal` as a
   definition (plus a `Notation`/view lemma so that `destruct`-style proofs can
   be rewritten mechanically), pointwise lifts, `Derive NoConfusion`/`EqDec`.
   Delete `liftBinOpSyncImpliesSyncArgs`, `liftUnOpRV{Sync,NonSync}Val`,
   `unliftIsSyncImpliesAllSync` and the like, or restate them as `secLeak`
   facts. Replace `Ltac destructRVs` (it matches on `SyncVal`).
2. **Semantics layer: `Formulas.v`, `BinOps.v`, `Patterns.v`,
   `Symbolic/Instantiation.v`.** §3 table, §4 bridge lemmas.
3. **Solver: `Symbolic/Solver.v` (~75 sites), `PartialEvaluation.v`.**
   - `instpred_formula_secLeak_{binop,unop}` (`Solver.v:229,248`) go from `⊣⊢` to `⊢`.
     Only the `⊢` direction is used (`rewrite -…` in `secLeakT_spec`, :288,
     :293). Grep shows no other user.
   - Audit every site that maps `NonSyncVal ⇒ error/False` (:92, :108, :569–591)
     for direction. On a constant `term_val`, decide `l = r` and the bool.
   - Port the ~15 `apply (f_equal SyncVal)` proof scripts (:1450–1687) via §4.
   - Keep `same_leaves` for now (still sound, just unnecessary); deleting it is R1.
4. **Worlds, logic and monads: `Symbolic/Worlds.v` (repₚ/eqₚ lemmas at
   :1059–1236, `formula_eqs_nctx_sync` :1536), `UnifLogic.v`, `Propositions.v`,
   `Symbolic/Monads.v`, `Shallow/Monads.v`, `MicroSail/*` refinement.** Keep
   the `secLeak` branch guards unchanged; do the §5 demonic-branch audit.
5. **Iris and case study.** `Iris/Binary{WeakestPre,Adequacy,Instance}.v`,
   `RiscvPmp/{Machine,ModelBinary,IrisInstanceBinary,IrisModelBinary}.v`, then
   CFGVer in `_CoqProject` order (`Contracts`, `Verifier`, `VerifierRel`,
   `SpecIris`, `Adequacy`, `EndToEnd`, `GenSegment`, `GenCompose`, `GenProg`,
   `Example/*`). The heavy files (`GenCompose.v` ~198 lines, `EndToEnd.v` ~161,
   `VerifierRel.v` ~57, `Adequacy.v` ~53) mostly destruct `RelVal`s, so this is
   mechanical with §4. Do the §5 audit here and settle D3.
   **Milestone: "pure port" commit**, with every theorem green and the trusted
   statements unchanged except as recorded under D3.
6. **Repairs R1–R6**, one commit each, with a light check after each.
   Add a regression example per repair. A natural one is a `ZZ*.v` probe that
   was blocked before: `x - x` public; a secret in a `pat_pair`; a secret
   range precondition.
7. **Docs** (same commits as the code, per the hygiene rule).
   - Rewrite `relval-model`; shrink `relval-rewrite-over-secrets` to "every
     Val identity lifts" (its whole caveat is gone); rewrite `secret-data-walls`
     (only asserted `secLeak` is a wall now). Touch `cfgver-contracts` if
     `secLeakvar` guidance changes.
   - Their `description:` lines name `SyncVal`/`NonSyncVal ⇒ False`, so editing
     them needs a `skill-routing-maintenance` consult (hook-enforced).
   - Mark memory `project_pmr_canonicalization` superseded.
8. **Full gate + measurements.** Compare against the Phase 0 baseline, and diff
   the trusted surface.

## 8. Risks

- **Performance (the real unknown).** `liftBinOp` on two `SyncVal`s computes `f`
  once today and twice after the change, and `secLeak` on constants becomes an
  `eq_dec`. VCs are mostly symbolic, so this should be small, but it is
  UNMEASURED. Phase 0 exists so this is a comparison, not a guess. If
  `vm_compute` regresses, a mitigation is a solver fast path for `term_val`
  (literal `SyncVal`) that never computes the right side.
- **Implicit publicness** (§5): the main source of proof breakage, plus a
  deliberate change to trusted-statement meaning that must be listed.
- **Hidden reliance on `False` collapse in an unguarded demonic branch** (§5):
  would turn into unsoundness, not a build error. This is the one item that a
  green build does not catch, hence the explicit audit.
- **Scope:** ~1,300 matching lines across 108 files. Excluded: `BlockVer/*`,
  `Staging/*` (including the second, standalone `RelVal` in
  `Staging/BinaryExecutor/ShallowExecutorRel.v`), and all `ZZ*.v` probes. None
  of these are in `_CoqProject`. Probes are left to rot or are fixed on demand.

## 9. Out of scope

- Going to two valuations or a unary executor (discussed 2026-10-06; rejected in
  favour of keeping the lift).
- Changing lockstep `semWP2` itself. It is already tag-free.

## 10. Phase 0 baseline (DONE 2026-10-06, commit 936ec9a3)

Forced `-j1` rebuild (`make -B`, `TIMED=1 TIMING=1`) of the gate closure
(`Results.vo` + `GenCompose.vo`), then `GATE_JOBS=1 ./scripts/gate.sh`.
Data in `theories/plans/relval-pair-baseline/`: `per-file.tsv` (146 files: user /
real / sys seconds, peak RSS), `per-sentence-timing.tar.gz` (every `.v.timing`),
`build.time`, `gate.time`, `gate.log`.

- **Compare on USER CPU time**, not wall clock: the box swapped (wall 3h41 for
  4,135 s user + 473 s sys); peak-RSS figures of the heaviest files are also
  pressure-affected.
- Build: **4,135 s user** total. Heaviest: `MuladdParamVC` 651 s / 10.5 GB,
  `MuladdParamTailVC` 357 s, `Solver.v` 345 s, `InvMixColumns` 137 s,
  `BearSSLCheckScalarLoop1` 128 s, `Refinement/Monads.v` 127 s.
- Gate: PASSED, 24 end theorems axiom-clean; axiom probe 332 s user, 10.4 GB.
- Trusted surface: 22 files (`Noninterference.v` + 21 `Example/*Result.v`), 78
  lemma/theorem declarations, at commit 936ec9a3.

Phase 8 comparison: same command, same targets, then diff `per-file.tsv` and the
per-sentence timings (`make` can diff `.v.timing` files directly).
