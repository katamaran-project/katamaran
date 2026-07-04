# Next session briefing

CLAUDE.md and the `/katamaran` skill are auto-loaded — read them for full context.
This file tracks the approved task list and current starting point.

---

## Current state

All CFGVer noninterference proofs are one-liners via `gen_contract_noninterferent`.
All contracts are defined using `gen_contract`. See commit history for details.

First realistic example (from the "Breaking Bad" paper discussion) is done:
`cmovznz4` (HACL*'s constant-time conditional move), hand-translated from
`clang -O2 -march=rv32i` output into a `list AST`, proved noninterferent
end-to-end (`cmovznz4_noninterferent` in `CFGVer/Examples.v`). `cin` and
scratch registers private, `x`/`y` data public, `r` private, addresses
hardcoded right after the code (see Priority 1 below re: why). A script at
`case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` mechanically translates
RV32I assembly (as pasted from Compiler Explorer) into the `list AST` Coq
literal, tagging each entry with its source line for auditability — use it
for future examples instead of hand-transcribing.

---

## TODO list

**Priority 1 (hardcoded start PC):**
- `init_addr = 0` is hardcoded throughout CFGVer. This needs to be a parameter
  so that programs can be placed at arbitrary addresses.
- Note: we will NOT move from instruction lists to address maps; lists are fine.
- Concrete motivating case from `cmovznz4`: real pointer-argument functions
  (x/y/r passed in registers, addresses only known at call time) can't be
  verified as such yet -- `gen_mem_asn`/`gen_contract` only support memory at
  a *literal* address fixed at contract-authoring time. Current workaround is
  to hardcode the pointer registers to concrete addresses right after the
  code (`countdown_mem`'s pattern), which sidesteps needing arbitrary-start
  support but doesn't reflect real calling-convention pointer arguments.
  Revisit once init_addr is parameterized; may also need a genuinely new
  "pointer-relative" memory-ownership generator (symbolic base register +
  literal offset) plus a matching two-world memory-extraction lemma for
  `gen_contract_noninterferent` -- sketched and then abandoned as out of
  scope for `cmovznz4` (see commit history), still open for a future example
  that actually needs real pointer arguments.

**Cleanup / refactoring:**
- Consolidate everything in CFGVer, so BlockVer can be deleted.
- Rename everything in CFGVer to remove mentions to BlockVer.
- Remove `sound_sblock_verification_condition` in favor of
  `sound_sblock_verification_condition_myWP2_loop`.
- `Examples.v` is too large; split into: logic lemmas, examples, memory helpers.

**Modularity (longer term, discuss with Dominique):**
- Parameterize hardcoded start PC at 0 (see Priority 1).
- Add exit resources (resources required when reaching the exit condition).
  Subtle: execution must stop *first time* exit condition is reached.
- Ask Dominique or Sander whether `AnnotInstr` is worth looking at.

**Known remaining Admits (expected):**
- `valid_jmp_fwd` (BlockVer): BlockVer cannot handle JAL. Intentional.

**ROOT-CAUSED: pattern matching demands full `secLeak` on the scrutinee,
which for LOAD forces the loaded value to be public.**

*Symptom.* `cmovznz4_noninterferent` needs `x`/`y` public (see
`cmovznz4_mem_specs`). A/B-isolated to: a single `LOAD` with the loaded
memory word PRIVATE fails; with it PUBLIC it succeeds -- independent of the
destination register, the address, or any `RTYPE`. So specifically "the
value read from memory by LOAD must be `secLeak`."

*Mechanism (full chain, confirmed by reading the code):*
1. Every `LOAD` runs `extend_value` (Machine.v:528), which does
   `match: value in union (memory_op_result bytes)`, where `value` is the
   loaded word wrapped `KMemValue cmem_val`.
2. The symbolic executor lowers `stm_pattern_match` (SymbolicExecutor.v:475)
   to `demonic_pattern_match`.
3. `demonic_pattern_match'` (Monads.v:551) opens with
   `assertSecLeak … t` on the scrutinee `t`, i.e.
   `assert_formula (formula_secLeak t)` (Monads.v:436). (The message string
   "Pattern matched term is not secLeak" at SymbolicExecutor.v:461 is the
   same check surfaced in `stm_assertk`.)
4. `formula_secLeak` on a union reduces (Solver.v:2232,
   `simplify_secLeak (term_union U K tl) => dlist_secLeak tl`) to `secLeak`
   of the *payload*. So `secLeak (KMemValue cmem_val)` becomes
   `secLeak cmem_val` -- exactly the residual `secLeak (bv 32)` goal.
5. It is baked into the *shallow spec too*, not just the optimizer:
   ShallowExecutor.v:251 `demonic_pattern_match pat v <-> secLeak v /\
   demonic_pattern_match' pat v`. So the requirement lives at every layer
   (shallow spec -> symbolic mirror -> refinement -> erasure), which is why
   re-enabling the commented-out constructor fast-path in Monads.v alone
   would NOT help -- it would break refinement against this shallow spec.

*Why it is over-conservative.* `secLeak` = fully synchronized (`SyncVal`,
same value in both worlds). But a pattern match only needs both worlds to
select the *same case* (same constructor); the payload variables it binds
are `RelVal` and may legitimately be `NonSyncVal` (differ per world). The
semantics already allow this: `semWP2_pattern_match` (BinaryWeakestPre.v:770)
computes `pc1`, `pc2` for the two worlds *independently* and requires the
continuation for the actual `(pc1,pc2)`; the symbolic executor collapses to
one `pc`, so soundness only needs `pc1 = pc2` (case-sync), NOT full value
sync. Confirms this is a tooling limitation, not a property of the program:
real CT crypto LOADs secret values (HACL* `cmovznz4` selects between secret
bignums/points in the Montgomery ladder; `Hacl.Spec.Bignum.Base.mask_select`
has a generic `limb_t` signature -- see the "Breaking Bad" paper).

*Fix plan: weaken the pattern-match precondition from `secLeak v`
(full sync) to `secLeakCase pat v` (both worlds select the same
`PatternCase`).* In dependency order:
  1. `Syntax/Formulas.v`: add concrete `secLeakCase pat rv` (both
     projections of `rv` hit the same `PatternCase`) and a symbolic
     `formula_secLeakCase pat t` constructor + subst/inst/occurs_check
     boilerplate.
  2. `MicroSail/ShallowExecutor.v`: change `demonic/angelic_pattern_match`
     (+ the `_unfold` lemmas) to use `secLeakCase` instead of `secLeak`.
  3. `MicroSail/ShallowSoundness.v`: re-prove pattern-match soundness w.r.t.
     `semWP2_pattern_match` under the weaker precondition. **This is the
     crux/risk** -- but the WP already handles `pc1`/`pc2` independently, so
     case-sync (`pc1=pc2`) is exactly what collapsing to one `pc` needs; the
     bound payload becomes `NonSyncVal (world1 payload) (world2 payload)`.
  4. `Symbolic/Monads.v`: `assertSecLeak` -> `assertSecLeakCase` in
     `demonic/angelic_pattern_match'`.
  5. `Symbolic/Solver.v`: simplify `formula_secLeakCase pat (term_union K tl)`
     -> `True` (constructor statically known). This is what discharges LOAD
     automatically; also handle other term shapes conservatively.
  6. `Symbolic/UnifLogic.v`: update `refine_*_pattern_match*` + add a
     `RefineCompat` instance for the new formula so `rsolve` still closes.
  7. `Symbolic/Propositions.v`: handle the new formula in the Erasure
     (`erase_formula`/`inst_eformula`) so `safeE`/`postprocess`/
     `VerificationConditionWithErasure` (CFGVer's `Valid_CFG_VC`) still work.

*Blast radius.* ~6-7 core theory files, in the metatheory shared by ALL
case studies (RiscvPmp *and* MinimalCaps); every case study must still
compile. The risk is concentrated in the ShallowSoundness re-proof (3) and
in threading the new formula through Solver (5) + Erasure (7) without
breaking existing proofs. Definitely a "scope with Dominique" change.

*Recommended de-risking spike before committing to the full proof:* wire
through steps 1,2,4,5,6,7 but leave the ShallowSoundness lemma (3) `Admitted`,
then check that (a) `cmovznz4` with `x`/`y` PRIVATE now closes and (b) all
existing case studies still compile. If both hold, the fix is "correct in
shape" and only the honest soundness re-proof remains.

*Spike RAN and CONFIRMED (2026-07-03).* Minimal version: in
`Symbolic/Monads.v`, replaced the `assertSecLeak` in `demonic_pattern_match'`
with a `pure` no-op (drops the scrutinee-secLeak obligation for demonic
matches) and set `cmovznz4_mem_specs` all-PRIVATE. Findings:
  - **(a) CONFIRMED:** a full `coqc` build of `CFGVer/Examples.vo` succeeded,
    i.e. `valid_cmovznz4_cfg_contract`'s `vm_compute. solve_vc. Qed.` closed
    *with x/y secret*, and `cmovznz4_noninterferent` (private mem_specs)
    closed too. So removing the pattern-match payload-secLeak obligation is
    exactly what unblocks LOAD-of-secret — root cause verified, not just
    reasoned.
  - **(b) blast radius, empirically:** the *only* proof that broke was
    `theories/Refinement/Monads.v : refine_demonic_pattern_match'` (the
    shallow-vs-symbolic refinement of `demonic_pattern_match'`) — `iApply
    refine_assertSecLeak` no longer matches once the symbolic side drops the
    assert. Admitting that single lemma let the entire theories + RiscvPmp +
    CFGVer chain rebuild to `.vo` with no further breakage. That admit is
    exactly the stand-in for the real work (steps 2/3/6: keep shallow +
    symbolic in sync via `secLeakCase` and re-prove the refinement).
  - Tooling notes for next time: petanque/Fleche needs real `.vo` deps (not
    `.vos`) for interactive elaboration, and aggressively caches — testing a
    core-executor change requires deleting stale `.vo` and doing a full `.vo`
    rebuild (a `.vos` build is faster but can't be queried interactively and
    skips the `Qed` that is the actual pass/fail signal). The batch
    `Examples.vo` compile *is* the test (its `Qed` check = the answer); no
    interactive session needed.

*Follow-up (2026-07-03): the constructor fast-path and the true root.* Tried
the cleaner fix — re-enable the commented-out structural fast-path fixpoint
in `Symbolic/Monads.v`'s `demonic_pattern_match` wrapper (inspect the term:
`term_get_union`/`term_get_pair` → read case+payload directly, skip the
`secLeak` assert; fall back to `demonic_pattern_match'` for opaque terms).
Results:
  - **The fixpoint definition typechecks.** Guard checker is fine (recursion
    `demonic (p K)` is the same shape as `PatternCase`/`EqDec_PatternCase`/
    `Finite_PatternCase` in `Patterns.v`), and the dependent reassembly
    `existT (existT K pc) δpc` works because `PatternCaseCtx (existT K pc) ≡
    PatternCaseCtx pc` definitionally. The *only* gotcha was that inside the
    `fix` body `σ` is implicit, so the recursive call is `demonic (p K) scr'`
    — the old commented code's `demonic (unionk_ty U K) (p K) …` (passing σ
    explicitly) is the bug that likely stalled this before.
  - **The refinement is NOT a standalone lemma — it is false against the
    current shallow spec, and the true root is `pattern_match_relval`.** The
    shallow `CPureSpec.demonic_pattern_match` (Shallow/Monads.v:338) is
    `assertSecLeak v ;; demonic_pattern_match' pat v`, and its whole
    characterization goes through `pattern_match_relval` (Patterns.v:425):
    `option_map … (option_map (pattern_match_val p) (ty.RVToOption rv))`,
    where `RVToOption` sends `SyncVal v ↦ Some v` and **`NonSyncVal _ _ ↦
    None`**. So the shallow model matches a `RelVal` by collapsing it to a
    single `Val` — which only works when it is `SyncVal`; *any* `NonSyncVal`
    (even `NonSyncVal v v`, even same-constructor) is unmatchable. The
    symbolic union fast-path skips a `secLeak` that is genuinely not
    derivable there (a `term_union K tl` interprets to `liftUnOp K (inst tl)`,
    `NonSyncVal` iff `tl` is), so the refinement cannot hold against this
    shallow spec.
  - **This `RVToOption`-at-the-root is the same wall as the earlier
    semantic-`secLeak` and `SyncVal/NonSyncVal`-at-the-leaves attempts.** All
    three are really trying to change *how a `RelVal` is pattern-matched*. The
    real fix: redefine `pattern_match_relval` to match a `NonSyncVal` **per
    projection with a same-case check** (`pattern_match_val` both sides; if
    the `PatternCase`s agree, return `Some` with the payloads zipped into
    `NonSyncVal`; else `None`), then re-establish its tower
    (`pattern_match_relval_inverse_*`, `wp_demonic/angelic_pattern_match`,
    drop `assertSecLeak` from the shallow `demonic/angelic_pattern_match`,
    re-prove `ShallowSoundness`), then the symbolic side + the refinement
    fall out. This is a foundational change to `Patterns.v` — genuinely
    "scope with Dominique," not a lemma. The fixpoint wrapper above is ready
    to drop in once the shallow layer is weakened.

*Concrete implementation plan for the `pattern_match_relval` rewrite
(2026-07-03).*

  **New definition.** Keep the `SyncVal` branch exactly as today (so all
  existing `SyncVal`-path lemmas are untouched); add a `NonSyncVal` branch
  that matches per-projection with a same-case check:
```coq
  Definition relNamedEnv {Δ : NCtx N Ty} (δ1 δ2 : NamedEnv Val Δ)
    : NamedEnv RelVal Δ :=
    env.zipWith (fun _ v1 v2 => NonSyncVal v1 v2) δ1 δ2.

  Definition pattern_match_relval {σ} (p : Pattern σ) (rv : RelVal σ)
    : option (MatchResultRel p) :=
    match rv with
    | SyncVal v => Some (matchResultToMatchResultRel (pattern_match_val p v))
    | NonSyncVal v1 v2 =>
        let '(existT pc1 δ1) := pattern_match_val p v1 in
        let '(existT pc2 δ2) := pattern_match_val p v2 in
        match eq_dec pc1 pc2 with
        | left e =>
            Some (existT pc1
              (relNamedEnv δ1
                 (eq_rect_r (fun pc => NamedEnv Val (PatternCaseCtx pc)) δ2 e)))
        | right _ => None   (* worlds take different branches ⇒ a leak *)
        end
    end.
```
  `eq_rect_r … e` transports `δ2 : NamedEnv Val (PatternCaseCtx pc2)` to
  `PatternCaseCtx pc1` so `relNamedEnv` can zip the two payload envs. (Exact
  `env` combinator name TBD — `env.zipWith`/`env.map2`.)

  **Do NOT add a branching/non-branching classification of PatternCases**
  (an approach tried before to cut duplication). It is subsumed by the
  uniform `eq_dec pc1 pc2`: for non-branching patterns (`pat_var`,
  `pat_pair`, `pat_unit`, `pat_bvec_split`, `pat_tuple`, `pat_record`)
  `PatternCase = unit`, so `eq_dec tt tt` computes to `left eq_refl`, the
  `None` branch is dead, and `eq_rect_r … eq_refl` reduces to `δ2`
  definitionally (no transport). Branching patterns (`pat_bool`, `pat_sum`,
  `pat_enum`, `pat_bvec_exhaustive`, `pat_union` — the last recursively via
  `sigma_eqdec` in the existing `EqDec_PatternCase`) genuinely need the
  check, and `eq_dec` supplies it. The kernel of truth behind the
  classification — that `PatternCaseCtx` is *constant in the case* for
  non-branching patterns, so no transport is needed there — is obtained for
  free (transport along `eq_refl` = identity); a first-class Coq split forces
  coverage/closure proofs re-threaded through `PatternCaseCtx` and is more
  work, not less.

  **Tower to re-establish (in order); the `eq_rect` is where it bites:**
  1. `pattern_match_relval_inverse_right'`/`_left` — **DONE & verified
     (2026-07-03)**, against the canonicalizing definition, in the
     `=== STEP 1 EXPERIMENT ===` block in `Patterns.v` (non-destructive:
     adds `relValOfVals`, `canonNamedEnv`, `pattern_match_relval_new`,
     `canonMatchResultRel`, `canonRelVal`, and the two inverse lemmas;
     leaves the old `pattern_match_relval` untouched). Zero admits, full
     `coqc` Qed. Key points that made it work:
       - CANONICALIZING zip (`relValOfVals`: `SyncVal` when the two agree,
         `NonSyncVal` only when they differ) — never creates `NonSyncVal v v`,
         so no irreversible contamination (this was the crux Dominique hit
         with the plain `nonsyncNamedEnv`).
       - The inverse-right statement is `= Some (canonMatchResultRel r)` (NOT
         `= Some r`): the round-trip recovers `r` *up to canonicalization*,
         since a pre-existing `NonSyncVal v v` collapses to `SyncVal v` — but
         that is semantically transparent. inverse-left is the conditional
         form `pattern_match_relval_new p rv = Some r -> reverse' r =
         canonRelVal rv`.
       - Key structural helper: `liftUnOp_unlift_canon` —
         `liftUnOpRV f (unliftNamedEnv (canonNamedEnv δ1 δ2)) =
         relValOfVals (f δ1) (f δ2)` for injective `f`; proved via
         `projLeftRVunliftNamedEnv`/`projRightRVunliftNamedEnv` + a case on
         whether the unlift is `SyncVal`/`NonSyncVal` (no messy `eq_dec` on
         whole envs). `reverse`'s injectivity comes from
         `pattern_match_val_inverse_right` + `inj_pair2_eq_dec`.
       - `eq_dec pc1 pc2` collapse: `destruct e` (J-elim) reduces `eq_rect_r`
         along the case-equality to the identity — cleaner than UIP-rewriting.
     **DONE: renamed `_new` → the real `pattern_match_relval`** (2026-07-03):
     old def + old 3 inverse lemmas replaced by the canonicalizing def +
     canonicalizing inverse lemmas. Added support lemmas `canonNamedEnv_diag`,
     `projLeft/Right_map_canonNamedEnv`, `projLeft/Right_map_valToRelVal`,
     `canonRelVal_idem`, `pattern_match_relval_canon` (matching sees through
     top-level contamination: `pattern_match_relval p (NonSyncVal v v) =
     pattern_match_relval p (SyncVal v)`), `pattern_match_relval_result_canonical`
     (`= Some r → canonMatchResultRel r = r`). Full `coqc` Qed, `.vo` kept.
  2. **DONE & verified (2026-07-03): `Shallow/Monads.v` fully compiles.**
     The design turned out subtler than "drop `secLeak`" — contamination bites
     at TWO levels and the naive drop is UNSOUND:
       - **Payload**: `angelic/demonic_ctx` yield raw `vs` (possible
         `NonSyncVal a a` leaves). So the primed ops must
         `pure (canonMatchResultRel (existT pc vs))`, NOT `pure (existT pc vs)`
         — else the biconditional breaks in opposite directions for ∃/∀.
       - **Scrutinee**: `pattern_match_relval pat (NonSyncVal v1 v1)` returns
         `Some(canonical)`, but the primed op's `reverse pc vs = v` constraint
         can never reconstruct a contaminated `NonSyncVal v1 v1` (empty ctx ⇒
         `reverse` is always `SyncVal`). Fix: canonicalize the scrutinee at the
         wrapper — `..._pattern_match pat v := … pat (canonRelVal v)`.
       - **Guard**: dropping the guard entirely makes DEMONIC miss genuine
         branch-leaks (∀ is vacuously true when the worlds branch, but the spec
         `option.wp Φ None = False`). Correct guard is the WEAKER
         `is_Some (pattern_match_relval pat v)` ("branches agree"), encoded as
         `match … Some ⇒ True | None ⇒ False`, NOT `secLeak v` (fully sync).
         Angelic needs no guard (∃ self-fails).
     Final statements: `wp_angelic_pattern_match' … (Hcanon : canonRelVal v = v)
     : angelic' pat v Φ ↔ option.wp Φ (pattern_match_relval pat v)`;
     `wp_demonic_pattern_match' … (Hcanon) : demonic' pat v Φ ↔ option.WLP Φ
     (pattern_match_relval pat v)` (liberal wp — vacuous on branch); the
     unprimed wrappers use `canonRelVal_idem` + `pattern_match_relval_canon`,
     and demonic combines `is_Some ∧ wlp ↔ wp`. `ShallowExecutor.v`
     `demonic_pattern_match_unfold` + `wp_demonic_pattern_match'` updated to
     match (the latter now `↔ option.wlp`, takes `Hcanon`); `wp_demonic_pattern_match`
     (→ `option.wp`) unchanged.
  3. `ShallowSoundness` pattern-match case (`ShallowSoundness.v:268-309`) —
     IN PROGRESS. Old proof used `assertSecLeak_sound` + old `demonic_pattern_match_unfold`
     (secLeak form) + old `pattern_match_relval_inverse_right` (unlift Sync/None
     form). All three changed. Must rework: new unfold gives
     `(match Some/None) ∧ demonic' pat (canonRelVal v) …`; new inverse_right is
     `= Some (canonMatchResultRel (existT pc δpc))`.
  4. Symbolic side + refinement — the symbolic side must mirror the shallow:
     canonicalize the payload + scrutinee + same-branch guard. This is where the
     symbolic `canonRelVal`/`canonMatchResultRel` analogs are needed (comparing
     symbolic terms) — likely the hardest remaining step. `refine_demonic_pattern_match'`
     and the wrapper induction.

  ─────────────────────────────────────────────────────────────────────────────
  ## METHOD X vs METHOD Y for the pattern-match refinement (decided 2026-07-03)

  While proving the refinement (step 4) we found the canonicalizing design
  (steps 1–3 above = "METHOD X") does not localize: canonicalization has to be
  consistent all the way down to the RelVal algebra. **We are switching to
  METHOD Y.** X is preserved here for a possible future, more-principled pass.

  **The driving case (cmovznz4):** `fun_extend_value` (`RiscvPmp/Machine.v:528`)
  matches `value : ty_memory_op_result` (a UNION) with `KMemValue (pat_var
  "result") => …`. `value` is built as `MemValue tmp`, so `term_get_union`
  statically fixes the constructor; the secret loaded word `tmp` is bound by the
  inner `pat_var`. No control-flow divergence, only the address leaks ⇒ safe, but
  the conservative executor asserts `secLeak` on the union scrutinee and fails.
  NB: keeping `secLeak` on `pat_var` does NOT fix cmovznz4 — the secret is bound
  by exactly that inner `pat_var`, so `pat_var` must fast-path too.

  **Key structural fact — the real axis is UNIQUE-REVERSIBILITY, not control flow:**
  - Uniquely reversible ⇒ safe to fast-path (RAW payload, no `secLeak`, no canon,
    STANDARD `RMatchResult`, no store-propagation problem): `pat_var`, `pat_unit`,
    statically-known-`K` `pat_union` (recurse). `reverse` pins the payload, so
    concrete(raw) == symbolic(raw).
  - Non-unique / branching ⇒ keep `secLeak`: `pat_pair`/`pat_tuple`/`pat_record`
    (multi-leaf — a coinciding leaf makes `reverse` non-unique: `SyncVal b` and
    `NonSyncVal b b` both reverse to the same thing) and
    `pat_bool`/`pat_enum`/`pat_sum`/`pat_list` (real control flow). `secLeak`
    forces the scrutinee sync ⇒ payload unique/canonical for free.

  ### METHOD Y (CHOSEN) — case-split by unique-reversibility, NO canonicalization
  - `pattern_match_relval` becomes RAW (`ty.nonsyncNamedEnv`, not `canonNamedEnv`).
    Same-branch `NonSyncVal` ⇒ `Some (existT pc (nonsyncNamedEnv δ1 δ2))`;
    different branch ⇒ `None`. (SyncVal branch unchanged.)
  - Shallow `demonic/angelic_pattern_match pat v := λ Φ, option.wp Φ
    (pattern_match_relval pat v)` — uniform, but reduces per-pattern-case (via
    `pattern_match_val`), so it lines up case-by-case with the symbolic fixpoint
    in the refinement induction. (`_sync` variants + `refine_purespec_mono`,
    already in-tree, bridge the `secLeak`-fallback cases where symbolic keeps
    `secLeak`; the `_sync` lemmas only touch the SyncVal branch, so raw=canon
    there and they are unaffected by the raw switch.)
  - Emiel added the symbolic fast-path fixpoint (`Symbolic/Monads.v`
    `angelic/demonic_pattern_match`): var/unit → `pure`; pair → `term_get_pair ?
    pure : secLeak-primed`; union → `term_get_union ? recurse : secLeak-primed`;
    default → secLeak-primed.
  - `refine_{angelic,demonic}_pattern_match` (unprimed): re-prove by INDUCTION on
    `pat` — fast-path cases with standard `RMatchResult`; default via the
    primed/`_sync` lemma. Old `apply refine_*_pattern_match'` is stale (symbolic
    is a fixpoint now, no longer defeq to the primed).
  - Pros: no RelVal-algebra change, no store-propagation problem, TCB untouched
    for now. Cons: per-pattern case-split; `secLeak` stays imprecise for the
    non-fast-pathed shapes (conservative symbolic incompleteness, not unsoundness).

  ### METHOD Y progress (2026-07-03) — compiles with admits
  DONE & compiling:
  - `Patterns.v`: `pattern_match_relval` RAW (`ty.nonsyncNamedEnv`); raw
    `pattern_match_relval_inverse_right` (case-split: SyncVal→`Some (existT pc δpc)`,
    NonSyncVal→`Some (existT pc (nonsyncNamedEnv δL δR))`). Canon defs kept for X;
    canon-specific lemmas (`pattern_match_relval_canon`, `_result_canonical`,
    canon `inverse_left`) removed.
  - `Shallow/Monads.v`: shallow `angelic/demonic_pattern_match := match
    pattern_match_relval … with Some r ⇒ pure r | None ⇒ error`; primed ops back to
    raw `pure (existT pc vs)`; `_sync` forward re-proved via raw `inverse_right`;
    `mon_*` (`unfold; destruct pattern_match_relval; typeclasses eauto`), `wp_*`
    (`destruct …; [wp_some|wp_none]; reflexivity`).
  - `Refinement/Monads.v`:
    - `refine_purespec_mono` invocation fixed:
      `iApply (refine_purespec_mono (c := …_sync pat v) (fun Φ H => …_sync_entails H))`.
    - `refine_{angelic,demonic}_pattern_match'` (primed fallback helpers): PROVED
      (route S-primed → shallow `_sync` → shallow unprimed).
    - `refine_demonic_pattern_match` (unprimed, by `induction pat; cbn -[RSat]`):
      PROVED for pat_var (assert `pattern_match_relval (pat_var x) v = Some (existT tt
      [x↦v])` by `destruct v; reflexivity`, then `rewrite … option.wp_some`, `iApply
      ("rΦ" with "[Hv] HSP"); rsolve`), pat_unit (same via `destruct v; cbn`), and all
      8 default/branching cases (`iApply refine_demonic_pattern_match'`). pat_union
      SKELETON verified to the core (term_get_union_spec; None→primed; Some→
      repₚ_inversion_union → `rewrite wp`).

  REMAINING (well-scoped):
  1. **union CORE — DONE (2026-07-03).** Proved `pattern_match_relval_union` in
     Patterns.v (`= option.map (wrap K) (pattern_match_relval (p K) t)`; SyncVal via
     `unionv_unfold_fold`, NonSyncVal via a 4-way `eq_dec`/`sigma_eqdec` split with
     `Eqdep_dec.UIP_dec`/`inj_pair2_eq_dec`). Union case of
     `refine_demonic_pattern_match` completed: `rewrite pattern_match_relval_union,
     option.wp_map, <- wp_demonic_pattern_match; iApply (H K with "Hvt [rΦ] HSP")`;
     continuation via `iIntros … "!> %mr %smr Hmr"; destruct; subst;
     rewrite forgetting_unconditionally; iApply ("rΦ" with "[Hmr]"); now iExists eq_refl`.
     `refine_demonic_pattern_match` now has ONLY `pat_pair` admitted.
  2. **pat_pair** case (`admit`) — full recipe now in-file (add
     `pattern_match_relval_pair` to Patterns.v — like `_union` but single-case, no
     eq_dec — then `term_get_pair_spec` + `repₚ_term_prod` + `option.wp_some` + `rΦ`).
     Simpler than union; optional (not needed for cmovznz4). (Sonnet.)
  3. **refine_angelic_pattern_match** (fully `Admitted`) — mirror the demonic
     induction (angelic uses `RMsg`/`msg`; otherwise identical). (Sonnet.)
  4. Downstream plumbing broken by the shallow redefinition — `ShallowExecutor.v`
     (`demonic_pattern_match_unfold`, `wp_demonic_pattern_match'` referenced the
     removed canon lemmas), then `ShallowSoundness.v` pattern-match case, then the
     case study. (Sonnet, mostly mechanical; ShallowSoundness may need care.)

  ### METHOD X (DEFERRED) — uniform canonicalization (the principled version)
  What commit `95e2fd54` + the current WIP tree implement (canonicalizing
  `pattern_match_relval`; shallow canonicalizes payload `canonMatchResultRel` +
  scrutinee `canonRelVal`; branches-agree guard; demonic primed ↔ `option.wlp`).
  Elegant and case-split-free, BUT to make the *refinement* go through it
  cascades:
  - Match payloads flow into the store (`δ0 ►► δpc`) ⇒ `RStore`/`RNEnv`/`RVal`
    must also canonicalize (concrete = `canonRelVal (inst symbolic)`).
  - Then ordinary computed store values (from `evalRel = liftBinOp (eval op)`,
    which yields `NonSyncVal c c` for a non-injective op) must be canonical too ⇒
    the concrete RelVal ALGEBRA (`liftBinOp`/`liftUnOp`/`bop.evalRel`/
    `uop.evalRel`/`inst_term`) must canonicalize (produce `relValOfVals`, never
    raw `NonSyncVal v v`).
  - Payoff: no contaminated `NonSyncVal v v` exists ANYWHERE; `secLeak` becomes
    EXACT ("worlds genuinely differ"); no per-pattern case-split.
  - `projLeft`/`projRight` commutation lemmas SURVIVE canonicalization (it
    preserves projections), so the interface is stable; what breaks is any proof
    inspecting the raw `NonSyncVal a b` STRUCTURE of a lifted-op result.
  - Deferred: foundational change to the trusted RelVal base. Revisit if we want
    the cleaner, case-split-free theory. The step-1/2 canon machinery
    (`canonNamedEnv`, `canonRelVal`, `canonMatchResultRel`, `canonRelVal_idem`,
    `pattern_match_relval_canon`, `pattern_match_relval_result_canonical`,
    `canonMatchResultRel_allsync`) is what X would build on — keep it in
    `Patterns.v` even after Y switches `pattern_match_relval` to raw.

  ### Also-still-true (END-TO-END, both methods)
  `secLeak` is baked into the TRUSTED program-logic rule: `Sep/Hoare.v:188`
  `rule_stm_pattern_match` requires `⌜secLeak rv⌝ ∗ Q rv δ`;
  `Iris/BinaryWeakestPre.v:1260` `iris_rule_stm_pattern_match` (proven) discharges
  it via `destruct rv; try contradiction` to collapse `rv` to one `SyncVal`. To
  let a non-branching secret through end-to-end, weaken these to branches-agree
  and re-prove the Iris rule vs `semWP2_pattern_match` (handle the same-
  `PatternCase` `NonSyncVal` case). Under Y the fast-path avoids `stm_pattern_match`'s
  secLeak at the EXECUTOR level for the safe shapes; check whether the TCB rule
  also needs weakening when wiring end-to-end.
  ─────────────────────────────────────────────────────────────────────────────

  **Optional refinement (do AFTER the plain tower proves).** Make
  `relNamedEnv` canonicalize: `if v1 =? v2 then SyncVal v1 else NonSyncVal
  v1 v2` (needs `EqDec` on the leaf `Val`s — available). Then `NonSyncVal v v`
  produces `SyncVal` payloads, so downstream `secLeak` recognizes
  morally-sync values — folding the `NonSyncVal tt tt` frustration into the
  same fix. Kept optional/deferred because canonicalization complicates the
  inverse-lemma proofs (step 1), so land the plain version first.

**Gotchas found while proving `cmovznz4_noninterferent`:**
- `fuel` must exceed the raw instruction count, and it's not obvious by how
  much. Every existing example already had slack (jmp_fwd: 2 instrs/fuel 5,
  swap: 3/5, countdown_mem: 4/10); `cmovznz4` initially used `fuel = 29`
  (exactly the instruction count) and got stuck on a bare `False` VC goal
  deep in the proof that looked like a missing `secLeak` fact but wasn't --
  bumping to `fuel = 35` made it disappear entirely. No documented rule yet
  for how much slack is actually required; worth deriving one (or exposing a
  clearer error) instead of trial-and-error next time.
- `gen_contract_noninterferent`'s `HDataAddrs` proof obligation must case-split
  on *every* index in `mem_specs`, not just index 0 -- the pattern in
  `countdown_mem_noninterferent` (`intros [|i] ...`) only works because that
  example has exactly one memory entry. Copy-pasting it for a longer
  `mem_specs` list silently breaks (`discriminate` fails on real, in-bounds
  entries): destructure `i` through every concrete index instead, e.g.
  `intros [|[|[|...[|i]...]]] spec H; cbn in H; try (inversion H; subst;
  vm_compute; done); discriminate.` for N entries.

---

## Potential next tasks (not yet approved)

- Prove `jmp_bwd` (backward jump / loop) as a second CFGVer example.
- Continue with more "Breaking Bad"-style realistic examples now that
  `cmovznz4` established the pattern (register/memory reg_specs split into
  public/private, `asm_to_ast.py` for translation). Next ones will likely
  want real pointer arguments -- see the Priority 1 note above.
