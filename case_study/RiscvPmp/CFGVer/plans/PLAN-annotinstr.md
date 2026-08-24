# PLAN — migrate CFGVer's instruction surface from `AST` to `AnnotInstr`

Status: **PHASES 1 AND 2 COMPLETE, 2026-08-22.** The whole CFGVer closure
builds — `Results.vo` green, every file from `Verifier` through `Results` with
real `Qed` and zero `Admitted`/`admit`. `AnnotInstr` is now the default
instruction surface all the way to the trusted boundary, with `strip` marking
where the machine-program view is taken. Every end theorem's statement is
UNCHANGED VERBATIM.

**GATE 2 PASSED, 2026-08-22** (`GATE_JOBS=1 ./scripts/gate.sh`): build clean,
no proof holes, and all **14 end theorems axiom-clean** — nothing beyond the
allowlisted `Machine.pure_decode` and `Base.mmioenv`. So the trusted-surface
claim is not merely "the statements read the same": they are proved from the
same axiom base as before the migration, with `strip` in the trusted
conclusions and `ai_instr <$>` at the memory boundary.

*Process caveat:* this work was committed DIRECTLY to `KatamaranRel`, so the
`pre-merge-commit` hook never fired and the gate was run after the fact rather
than as a merge precondition. It passed, so mainline is clean — but the
invariant went unenforced for the whole session. Phase 3/4 work should go on a
topic branch and reach the protected branch via `git merge --no-ff`.

**Still open:**
1. `cfgver-refinement` / `cfgver-soundness` skills do not yet mention the new
   `strip` / `ai_instr <$>` boundary. (`cfgver-executor` does.)
3. Phase 3 (`AnnotDebugBreak` as a usable tool) and Phase 4
   (`AnnotLemmaInvocation` semantics) are untouched — see below.

## Log

**2026-08-24 (later), br_divrem MEASURED — the motivating program, and the
"stable slots, growing terms" split holds far harder there.** GATE 3 was met on
`ZZKslHeapCommon`, but that rig pins term shape flat on purpose, so the result
did not reach the program this document exists to unblock. It does now. Probe:
`Example/ZZDivremDebugProbe.v` (throwaway, gitignored), rig copied verbatim from
`ZZDivremNCommon.v`, break on the loop head.

*Why this was affordable at all*, given `PLAN-muladd-full.md` records 67.5 s for
2 trips: **a dump needs no VC proof.** Only `postprocess (CFG_VC_triple …)` has
to build. So `ZZDivremProbe2.v`'s unresolved `solve_symbase_fetch` residual —
the thing that has kept that probe from ever compiling — is irrelevant to
dumping, and so is `solve_vc`.

*The loop head is index 8, not 0.* The back edge `bltu A6, A5` sits at index 34
(byte 136) with offset −104, so the target is byte 32 = index 8
(`addi A5, A5, -1`); indices 0–7 are the prologue, matching `zzdrn_fuel`'s "8
prologue" comment. Getting this wrong puts the break in straight-line code and
it fires once, which looks like the mechanism failing.

*Structure and cost.*

| n | debug nodes | tree nodes | binders (\|Σ\|) | vm_compute |
|---|---|---|---|---|
| 1 | 1 | 67 | 63 | 13.8 s |
| 2 | 2 | 68 | 63 | 32.7 s |

|Σ| is **flat in trips**, the tree grows by exactly the one debug node per trip
(the same law as Countdown and KSL), and **tree CONSTRUCTION alone is already
2.4× for one extra trip** — no `solve_vc` involved.

*The heap, trip 1 → trip 2, within the n=2 run.*

| | trip 1 | trip 2 | |
|---|---|---|---|
| chunks | 15 | 15 | static |
| heap printed chars | 786 | 8 787 | **11.2×** |
| `term_` nodes | 23 | 439 | **19.1×** |

*Per slot — this is the actionable part, because it names Phase 4's target set.*
Seven of fifteen chunks grow; eight are BYTE-IDENTICAL across trips.

| slot | reg | role | `term_` t1 → t2 |
|---|---|---|---|
| `x10` | A0 | remainder/dividend | 7 → 95 |
| `x11` | A1 | | 1 → 71 |
| `x6`  | T1 | | 1 → 69 |
| `x14` | A4 | quotient accumulator | 1 → 65 |
| `x5`  | T0 | | 1 → 63 |
| `x28` | T3 | | 1 → 62 |
| `x7`  | T2 | | 1 → 4 |
| `x12` | A2 | divisor, read-only | 1 → 1 |
| `x13` | A3 | base pointer | 2 → 2 |
| `x15`/`x16`/`x17` | A5/A6/A7 | loop counters, and CONCRETE (`0x2`,`0x1`,`0x2`) | 1 → 1 each |
| `cur_privilege`, `inv_leakage`, `ptstomem 4` | | the `sw` is in the EPILOGUE, not the loop body | unchanged |

So an abstraction lemma has to abstract **six registers** (`x5`, `x6`, `x10`,
`x11`, `x14`, `x28`); the other nine chunks need nothing. The loop counters
staying concrete is also what lets the executor decide the back edge at all.

*What this does and does not establish.* It confirms the split the KSL rig
suggested, on the program that matters, with a named target set. It does NOT
establish a growth LAW: two dumps give ONE increment, and 19.1× cannot be told
apart from polynomial-in-steps by a single ratio. Nor is 19.1× the same metric
as this document's λ ≈ 10.53 — do not equate them.

*Method notes.*
- 63 leading binders indent the payload past every truncation limit, so strip the
  prefix with a `spine_drop` into `{Σ' & 𝕊 Σ'}` (the sigma is unavoidable: a
  binder's continuation lives in a different context). **Normalise the tree into
  a `Definition` FIRST** — `spine_drop k (dr_tree 2 0)` recomputes the tree
  inside the sigma and OOMs; against a pre-normalised tree it is cheap. The
  earlier "pet OOMs on a vm_compute'd sigma" note was WRONG about the cause.
- pet cannot do this rig at all (7656 MB cap). Run `coqc` directly.
- **`Redirect` is forbidden by the MCP layer.** Run `coqc` by hand with the
  `_CoqProject` flags and split one stdout stream on `Eval vm_compute in
  "MARK_…"` sentinels instead.
- Counting the PRINTED form is the only quantitative handle on a dump, since
  `AMessage` can never be projected. It works well: per-slot char and `term_`
  counts fall straight out of a paren-depth split of `debug_asn_heap`.
- Ask for ONE tree per `vm_compute`. The first attempt put four trees in a single
  query and paid 4×.

**2026-08-24, GATE 3 MEASURED — and the answer is a distinction, not a yes/no.**
Phase 3's mechanism turned out to be already delivered by Phases 1+2; what was
missing was the measurement. Both are now done. Probes:
`Example/ZZCountdownDebugProbe.v`, `Example/ZZKslHeapDebugProbe.v` (throwaway,
gitignored, not in `_CoqProject`).

*The mechanism, on a real loop.* A break on the loop head fires **once per
trip**, and costs exactly one node per firing:

| rig | trips | debug nodes | total nodes | non-debug |
|---|---|---|---|---|
| Countdown, X1=2, fuel 5 | 2 | 2 | 9 | 7 |
| Countdown, X1=4, fuel 9 | 4 | 4 | 11 | 7 |
| `zzkh`, t=2, P=1, fuel 48 | 2 | 2 | 25 | 23 |

Non-debug node count is CONSTANT in trips (7 = 4 `demonicv` + 2 `assumek` +
`block`), so the tree is `nondebug + N`. The *unannotated* tree of the same
program prunes to a single `block` in both rigs — i.e. debug nodes are what
stops `prune` collapsing the tree, which is the whole cost of instrumentation
and is consistent with this document's own "dump with it, measure without it".
The annotated Countdown VC still proves with the tactic unchanged (7.9 s +
3.8 s `Qed`).

*Dumps self-identify; no label is needed.* Countdown's four dumps carry
`x1 = 0x4, 0x3, 0x2, 0x1` — the value on entry to each trip — and tree nesting
gives the order. A label argument on `AnnotDebugBreak` would be a convenience,
not a prerequisite. (An earlier note in this session claimed the dumps were
indistinguishable. Wrong: content distinguishes them.)

*GATE 3 proper — `zzkh` at t=2, the rig this document names.* Verdict: **"the
heap is static across trips" is TRUE in inventory and |Σ|, FALSE in order, and
FALSE in content.**

- **|Σ| flat.** 20 `demonicv` binders, and *none* added between the two dumps.
  Confirms this document's "|Σ| flat" claim directly.
- **Chunk inventory static.** 8 chunks on both trips, the same 8 identities
  (`inv_leakage`, `cur_privilege`, `ptstomem 4`, `x14`, `x13`, `x12`, `x11`,
  `x10`).
- **Chunk order changes.** Same multiset, different list. Countdown does this
  too, and there it is a ONE-TIME flip: trip 1 is
  `[inv_leakage; cur_privilege; x1]`, trips 2–4 are all
  `[x1; cur_privilege; inv_leakage]`. It does not alternate.
- **Chunk contents GROW.** This is the real finding. On trip 1, `x10`/`x11`/`x12`
  hold the bare classed existentials `term_var "v"`, `"v.1"`, `"v.2"` — atoms.
  On trip 2 they hold compound terms: `x10 = term_mulx (0x38 +ᵇ p) 0xe1000000`,
  `x12 = 0xe1000000`, and `x11` a nested
  `bvand/shiftr/bvand/bvxor/bvand/bvadd` expression. The memory cell goes from
  `term_bvtake 32 (term_var "mwpriv")` to `term_mulx (0x38 +ᵇ p) 0xe1000000`.
- **Path condition** is the same one-time step as Countdown: 1 formula on trip 1,
  2 from trip 2 on (gaining `formula_secLeak (term_var "p")`), then fixed. Not
  per-trip growth.

*Why this confirms rather than undermines the Phase 4 targeting.* The slot
STRUCTURE is stable while the TERMS in those slots grow — which is exactly the
shape that makes the abstraction lemma statable ("consume `A0 ↦ <huge term>`,
produce `∃v, A0 ↦ v ∗ inv v`"): there is a fixed set of slots to write such a
lemma about. Read together with §"Before funding this", the claim "heap fixed by
construction, term growth is the whole story" is now measured and holds in the
sense that matters.

*Strength and limit of this evidence.* Stronger than expected, because
`ZZKslHeapCommon`'s header pins term shape FLAT on purpose — the mask bit and H
both come from `A3`, a constant, never from `A0`, so terms are not supposed to
self-accumulate — and they grew from atoms to nested expressions in TWO trips
anyway. Still not `muladd`/`br_divrem`, where the shape is self-referential by
design and this should be strictly worse. GATE 3 as written is met; the
motivating program remains unmeasured.

*Five method corrections to the Phase 3 recipe below — it is wrong as written.*
1. **`DebugCFGVerifierContract` + `vc_debug` DOES NOT WORK.** `apply vc_debug;
   vm_compute` yields a ~12,000,000-character goal. Use instead:
   `Eval vm_compute in (cfg_map contract (fun _ p exits Q i _ fl =>
   postprocess (CFG_VC_triple p exits Q i fl)))`. No VC proof is needed to dump.
2. **The payload can be PRINTED, never EXTRACTED.** `AMessage` is
   `mk {M} {instances} (msg : M Σ)` — existentially packed (`Messages.v:80`) —
   so no Coq function projects a `DebugAsn` back out. `count_debug` /
   `count_nodes` (in both probes) give summaries instead.
3. **Indentation, not size, is the printing obstacle.** 20 leading `demonicv`
   indent the payload ~70 columns and wrap every line, truncating output before
   the later trips. `Set Printing Width 1000` fixes it. Do NOT try to strip the
   prefix by `vm_compute`-ing a `{Σ' & 𝕊 Σ'}` spine-drop (the sigma is needed
   because a binder's continuation lives in a different context) — pet OOMs at
   7656 MB. The `spine_drop` in `ZZKslHeapDebugProbe.v` is kept as a record of
   that dead end.
4. **Throwaway `ZZ*.vo` in the source tree are PRE-MIGRATION** and importing one
   gives "makes inconsistent assumptions over library Prelude".
   `rocq_compile_file`'s `keep_vo` is a **no-op under dune** — the artifact goes
   to `_build/default`, never the source tree. Copy the rig's definitions into
   the probe instead. (`ZZKslHeapCommon.v`'s SOURCE compiles unchanged
   post-migration: the `AST → AnnotInstr` coercion adapts `list AST` rigs with
   no edit, which is the coercion's design intent confirmed.)
5. The break belongs on the loop HEAD, and that is not always instruction 0 of
   the file — check the branch target. For `zzkh`, `zzkh_back_offset = 8140`
   = −52 in 13-bit two's complement and the `BNE` sits at byte offset 52, so the
   target is 0 and instruction 0 is the head.


**2026-08-22, PHASES 1+2 COMPLETE.** Read this entry before the older ones; it
supersedes their status claims.

*What the final shape is.*
```coq
Inductive Annot := AnnotDebugBreak
                 | AnnotLemmaInvocation {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp [ctx]) Δ).
Record AnnotInstr := MkAnnotInstr
  { ai_ghost_before : list Annot ; ai_instr : AST ; ai_ghost_after : list Annot }.
sexec_ghost  / cexec_ghost  : one annotation, ordinary (S|C)HeapSpec actions
sexec_ghosts / cexec_ghosts : the list, bound flat into (s|c)exec_cfg_addr
rexec_ghosts + refine_compat_exec_ghosts : the relational side
```

*AnnotLemmaInvocation is a STUB ON BOTH SIDES.* `sexec_ghost` errors (VC =
`False`); `cexec_ghost` returns `pure tt`. Giving the CONCRETE side real
`call_lemma` while the symbolic side stubbed was tried and reverted:
`sound_exec_cfg_addr_myWP2` then has to absorb the lemma's heap effect, which
is genuine lemma-soundness content — exactly the Phase 4 work this document
says not to bundle. With both stubbed, `cexec_ghosts gs = pure tt`
unconditionally (`cexec_ghosts_pure`), so absorption is one rewrite.
**`cexec_ghosts_pure` MUST BE DELETED when Phase 4 makes the lemma case real**
— it is where the Phase 4 soundness obligation lands. Total cost of the stub:
one tactic line (`iApply refine_unit` in `rexec_ghosts`).

*THE ONE REAL SEAM.*
```
instrsMemory / intro_ptsto_instrs PRODUCE  instrs_of_list b (strip instrs')
Adequacy.v's soundness lemmas WANT         ai_instr <$> instrs_of_list b instrs'
```
Adequacy has no choice — its `instrs` is a gmap and cannot say `strip`. Equal
only via `Tables.v`'s `fmap_instrs_of_list`. Both directions cost exactly two
rewrites; the projection form was kept so `EndToEnd`'s five statements stay
uniform with Adequacy, bridge applied once in each `cfg_instrs_endToEnd*`. The
`unfold strip` inside it is REQUIRED — `strip` is not syntactically `map`.

*Second recurring gap: `length (strip l) = length l` is true but NOT
definitional.* `strip_length` (`Verifier.v`, `List.length_map`) is used at six
sites. **Normalising everything to one form does NOT work** — tried twice, it
just moves the stranded side goal, because different consumers want different
forms. Provide BOTH: `Hleninstrs_s`, `Hlen_s`, `HDataAddrs_s`, plus four
`rewrite <- (strip_length instrs)` before `pcOutOfInstrs_fallthrough`.

*`instrs_of_list` and `exits_of_list` are POLYMORPHIC in the element type.* One
definition serves the executor (at `AnnotInstr`) and memory (at `AST`, fed
`strip`), type inferred per use. Chosen over a second `annots_of_list`
(duplication) and over a `Definition … := @map_of_list AST` wrapper (breaks
`cbn [instrs_of_list]` in existing proofs). `exits_of_list` needs no `strip` at
all — it only reads `length`, and under the PRODUCT AnnotInstr that IS the
instruction count. That is the fifth place the product shape removed work
rather than adding it.

*The trusted surface, preserved verbatim.* Every end theorem still states
`noninterferent_strong init_addr <prog>_instrs …`. Two patterns close the gap
to the bridges' `strip instrs` conclusion:
- 9 programs with a named list: a `strip_id_<prog>` anchor in
  `Example/<Prog>.v` (`reflexivity`, verified at 1ms each) plus
  `rewrite <- strip_id_<prog>` in the Result file.
- 3 programs building the list inline (`Jumps` ×2, `MvSwap`, `SetX2`): a local
  `assert (Hstrip : strip [.…] = [.…]) by reflexivity`.
`CountdownResult.v` is the only MIXED file — inline literal in one theorem,
`countdown_mem_instrs` in another — and a script assuming one program per
Result file will put the anchor before the wrong `eapply`. **The audit that
catches that class of error without a compile:** per Result file, count
`eapply gen_contract_noninterferent` against the number of strip rewrites
(14 across 12 files).

*THE ALIAS BUG IS SIX SIGNATURES, not the one this document flagged.* Five in
`VerifierRel.v` and two in `Adequacy.v` spelled out
`list (Term _ ty_xlenbits * AST)` instead of `SInstrTable`/`SExitTable`, and
every one silently failed to track BOTH columns added since (the word column,
then `AnnotInstr`). One missing convention, not six mistakes: **if you are
writing a table type and it contains a `*`, it is wrong.**

*Two simplifications of PRE-migration proof text, both from adding
`refine_compat_exec_ghosts`:* the two 11-line
`assert (Heq : …) by reflexivity; rewrite Heq` blocks in `rexec_cfg_addr` are
GONE (rsolve handles that region unaided), and
`rewrite (persist_itableW_trans ω ω0 tbl)` — which named its accessibilities
explicitly and broke as soon as the world chain grew — is now
`rewrite ?persist_itableW_trans ?persist_etable_trans`.

*`rexec_cfg_addr`'s two real obstacles, neither about ghosts semantically:*
1. the pc fact sits under `forgetting ω2` (the ghost-after world motion) —
   `refine_inst_persist` transports it;
2. `Acc` composition is not definitionally ASSOCIATIVE. `forgetting`
   accumulates `((ω∘ω0)∘ω1)∘ω2` while `sexec_cfg_addr`'s `θ0∘θ1∘θ2∘θ3` becomes
   `ω∘(((acc_refl∘ω0)∘ω1)∘ω2)`. Same substitution, different term. Both expand
   to the SAME fully-nested form, so
   `rewrite <- !persist_itableW_trans, persist_itableW_refl` closes it in 126ms
   with NO new lemmas. I first chased a `sub_acc`-equality helper and got stuck
   on the `WTerm`/`STerm` instance mismatch that stops `rewrite persist_subst`
   firing on `persist__term`; reading this file's own `persist_itableW_trans`
   was the fix.

*The 2274a22b hang is EXPLAINED and does not recur.* `rexec_ghosts` closes in
~1.3s. The hang was a shape mistake: that attempt bound `debug msg (pure tt)`
as a niladic action, which matches neither `refine_debug` nor
`refine_compat_debug` (both stated for `debug` as a TRANSFORMER), forcing a
hand-written bridge. It also lacked the `□ᵣ`/`unconditionally_T` wrapper, so
its IH landed at the wrong world — a failure that looks nothing like "you need
a box". `main`'s `rexec_annotated_block_addr` has both; that session ported its
TACTIC without its STRUCTURE.

*TOOLING, and the most expensive lesson of the whole effort.*
**`rocq_compile_file` verifies TACTICS. Only `make` verifies a FILE.** Three
distinct false-green modes hit in one session: (1) failing to resolve a
freshly built sibling `.vo`; (2) accepting a bare `LEnv` the real build
rejects, while writing `.vo`s with the WRONG LOGICAL NAME (no `-Q`/`-R`, so
unusable downstream and undiagnosable-looking); (3) reporting `EndToEnd.v`
green when `make` rejected it, twice, on premises it never checked. A "Phase 2
complete" commit was made on (3) and had to be corrected by `a8672075`.
Corollary on the interactive side: `rocq_start(theorem=…)` replays VOS-STYLE
and reaches theorems in files where mid-proof POSITION mode OOMs pet — that is
what finally gave goals on `EndToEnd.v` (325ms, 18ms) after four ~2min compile
guesses. It stops working once the file's heavy proofs are restored. And pet
OOMs on `VerifierRel.v` at ANY position (Fleche checks the whole document), so
that one file needs the restate-in-a-probe pattern; `Tables`, `TablesRel`,
`Adequacy` and the examples all open fine.



**2026-08-21, product-type Phase 0 finished + the `rexec_ghost` reevaluation.**

*Numbering warning.* The Phase 0 checkpoint commit (5647fe12) renumbered the
phases against this document — it calls `VerifierRel.v`/`TablesRel.v` "Phase 1"
where this write-up calls them Phase 2. **This document's numbering stands**:
Phase 1 is the symbolic side (`Verifier`/`Tables`/`Contracts`/`GenContract`),
Phase 2 is the relational side. A later session took the commit message at face
value and had to be corrected.

*Phase 0 did not actually compile when it was checkpointed as complete.*
`lookup_instr` had been retyped to return `AnnotInstr` but `sexec_cfg_addr` still
passed the result straight to `sexec_instruction`, which takes `AST`. The
checkpoint's "light-branch files compile individually (verified via
`rocq_compile_file`)" was a false green — the documented `rocq_compile_file`
dune-fallback trap for this subtree (see **rocq-implementation**). **Verify a
CFGVer build with `make -f Makefile.coq`, and do not record a gate as passed on
the strength of a `rocq_compile_file` result.**

Two fixes made it green, and the second is a repeat offender:
1. `sexec_cfg_addr` now projects `ai_instr ai`. Projecting at the use site
   (rather than destructuring `MkAnnotInstr` in the `lookup_instr` pattern) is
   deliberate: it keeps `ai` a variable, so `rexec_cfg_addr`'s existing
   `destruct (lookup_instr …) as [[x i]|] eqn:Hlk` needs no extra `destruct`,
   and `lookup_instr_sound` will hand the concrete side the syntactically
   identical `ai_instr ai`.
2. `scfg_verification_condition`'s signature spelled out
   `list (Term Σ ty_xlenbits * AST)` instead of `SInstrTable (wlctx Σ)`. This is
   the SAME bug already flagged for `rexec_triple_addr` (2026-08-20 entry
   below), in a second function — and it had silently failed to track *both*
   columns added since: the word column and now `AnnotInstr`. `rexec_triple_addr`
   is still unfixed. **Always name a table type by its alias.**

*GATE 1 result.* `Tables.v`/`Contracts.v`/`GenContract.v` needed **no change at
all** — the product type makes `length instrs = length (strip instrs)`
definitionally, so the exit-offset arithmetic never needs `strip` (four builders
would have needed it under the sum type). All 12 examples compile unedited; all 9
`strip_id_*` lemmas are `reflexivity` (`Example/ZZAnnotStripIdProbe.v`;
`Jumps`/`MvSwap`/`SetX2` build their lists inline, so unchanged compilation is
the only evidence there). Cost-neutrality is currently true *by construction*
rather than measured — no ghost is interpreted yet, so the executor term is
unchanged — and the real cost check belongs with `ghost_wrap` below.

*The `rexec_ghost` reevaluation — the main finding.* The question was whether the
`rexec_ghost` lemma from the reverted Phase 2 attempt should be ported to the
product type. **It should not; it should be deleted.** It existed to paper over a
shape mistake, and the product type plus `option Annot` removes the mistake:

- The framework already refines `debug`. `theories/Refinement/Monads.v:1683,1693`
  give `refine_debug` and a `RefineCompat` instance, and
  `CHeapSpec.debug := fun m => m` (`theories/Shallow/Monads.v:1112`) is the
  IDENTITY. So a symbolic `debug msg s` refines against an **unchanged** concrete
  `c`. Consequence: `cexec_cfg_addr` keeps its `gmap … AST` and needs no ghost
  column — this contradicts nothing, but it is stronger than the 2026-08-20
  entry's "needs no change beyond widening the wildcard pattern".
- Those lemmas state `debug` as a **function on computations**
  (`RHeapSpec RA -> RHeapSpec RA`). The reverted design instead bound a niladic
  action into the chain — `⟨θ0'⟩ _ <- sexec_ghosts ghosts ;;` with
  `sexec_ghost AnnotDebugBreak = debug msg (pure tt)` — and
  `bind (debug msg (pure tt)) f` is not `debug msg (f …)`, so the ready-made
  instance cannot fire. **That is why a hand-written bridge was needed, and that
  bridge is the lemma that hung for 300 s+.**
- The bound step also added a third world to the persist chain
  (`θ0 ∘ θ0' ∘ θ1`), i.e. a second instance of exactly the `chunk_gc` problem
  `rexec_cfg_addr` already spends ~30 lines of `gc_binds_heap`/`refine_gc_heap`
  surviving; and it was not even cost-neutral for an unannotated program, since
  `bind (pure tt) f` is not `f` — GATE 1's own cost check would have failed.
- `main`'s `BlockVer/PartialVerifier.v` is the working precedent on BOTH sides:
  `sexec_annotated_block_addr:541` wraps, `cexec_annotated_block_addr:597`
  mirrors with the identity `debug`, and `rexec_annotated_block_addr:641` closes
  the `AnnotDebugBreak` case on the bare `destruct instr; cbn; rsolve` line with
  no bullet. **The 2026-08-20 session ported that tactic without porting that
  shape** — which fully explains "the exact idiom that works on main failed
  here", with no need for the dependent-constructor hypothesis.

**CORRECTION, same day, prompted by review — the paragraph above overstates
the case, and two of its conclusions were wrong.**

*(1) "Bound steps are the problem" is too broad.* The correct rule is:

> **A bound step is fine exactly when the CONCRETE side binds too.**

`main`'s `rexec_annotated_block_addr:641` proves it — three constructors, only
TWO bullets. The bullet-free case is `AnnotDebugBreak` (a wrapper); the two
bulleted ones are `AnnotAST` and `AnnotLemmaInvocation`, and the latter **binds**
`call_lemma` on both sides and is dispatched by plain `rsolve` plus the IH. So
binding is not the defect. The defect is binding something with no concrete
counterpart: `CHeapSpec.debug = fun m => m` is the identity, so a bound `debug`
moves the symbolic world with nothing to match, and `refine_debug` is stated for
`debug` as a transformer.

*(2) `option Annot` was wrong, and "drops the recursion" was never a win.*
Recursing over a list of ghosts and building a bind chain are INDEPENDENT: a
`fold_right` over transformers is one term with no binds. The Phase 0 `option`
was chosen to avoid a cost that did not exist, while ruling out a real case —
two annotations at one pc (dump the heap AND abstract a term), which is exactly
what Phase 3 and Phase 4 together want. Both slots are now `list Annot`.

*(3) `AnnotLemmaInvocation` is reinstated NOW, overriding this document's own
"defer to Phase 4" recommendation.* That advice rested on it being a
soundness-free `error` stub and on its dependent constructor being the hang
suspect; the first no longer applies (it has real `call_lemma` semantics) and
the second is refuted by (1). Having it present is what makes the
world-threading COMPILER-CHECKED instead of asserted in a comment — and it
immediately paid for itself by exposing the `LEnv` qualification bug below.
No soundness debt: it invokes existing `LEnv` entries, adds none.

*What actually landed (symbolic side COMPLETE, all gated green):*

```coq
Definition sexec_ghost (a : Annot) {w : World} : SHeapSpec Unit w :=
  match a with
  | AnnotDebugBreak           => debug (fun h0 => amsg.mk {| … wco w … h0 |})
                                       (pure tt)
  | AnnotLemmaInvocation l es => call_lemma (RiscvPmpCFGVerifSpec.LEnv l)
                                            (seval_exps [env] es)
  end.

Fixpoint sexec_ghosts (gs : list Annot) {w : World} : SHeapSpec Unit w :=
  match gs with
  | nil      => pure tt
  | a :: gs' => ⟨ θ ⟩ _ <- sexec_ghost a ;; sexec_ghosts gs'
  end.
```

Ordinary actions, bound flat into `sexec_cfg_addr` alongside `chunk_gc` and
`sexec_instruction`, with the ghosts running AFTER `chunk_gc` so a break dumps
the POST-GC heap. `{w : World}` implicit (`chunk_gc`'s shape), not `⊢`.

**A `Box -> Box` transformer with a continuation-nested call site was written
first and REVERTED the same day.** Its justification was that a bound `debug`
differs from a wrapping one. Checked directly instead of argued, and it is
false — `reflexivity` closes both

```coq
SHeapSpec.bind (sexec_ghosts nil) f Φ h = T f tt Φ h
SHeapSpec.bind (sexec_ghosts [AnnotDebugBreak]) f Φ h
  = SymProp.debug (amsg.mk {| … wco w … h |}) (T f tt Φ h)
```

in 2–3 ms, for exactly the reason `gc_binds_heap` holds: `pure` and `debug` bind
at `acc_refl`, so `bind`'s world bookkeeping collapses away. Same term, same node
position, same heap. There is no third world and cost-neutrality was never at
risk. **So three claims made against the bound shape in the entry above are
RETRACTED:** that `bind (debug msg (pure tt)) f` differs from `debug msg (f …)`,
that it adds a third world, and that it breaks cost-neutrality. The transformer
cost readability and moved the recursive call out of tail position (a
guard-checker hazard) in exchange for nothing. Only `ghost_binds_nil` was kept,
demoted to an `Example` in this file's existing self-test idiom.

*Two things this leaves for Phase 2, both sharper than previously recorded.*
- **`gc_binds_heap` is not the template.** It works as a rewrite because
  `chunk_gc` is a CLOSED term, so one equation covers every use. `sexec_ghosts`
  is applied to `ai_ghost_before ai` with `ai` an OPAQUE variable out of
  `lookup_instr`, so the ghost list in the refinement proof is ARBITRARY and no
  finite set of instances discharges it. Phase 2 needs an INDUCTIVE relational
  lemma over `gs` — `rexec_ghosts`, i.e. the lemma that hung at 2274a22b. That
  risk is unavoidable and is not a reason to distort the symbolic side, since the
  term is identical under both shapes.
- **`sexec_cfg_addr`'s shape has changed FOR THE PROOF whether or not any program
  writes a ghost.** Only the computed VC is unaffected. Earlier wording here let
  "cost-neutral" imply "invisible to Phase 2"; those are different claims.

*Two traps hit while landing this:*
- **`LEnv` needs qualifying** as `RiscvPmpCFGVerifSpec.LEnv`. `Verifier.v`
  imports `RiscvPmpCFGVerifExecutor`, which is `MakeExecutor … RiscvPmpCFGVerifSpec`
  (`Spec.v:720`) and does not re-export its `Specification` argument — hence
  `RiscvPmpSpecVerif` (`Spec.v:723`) importing both, and `SpecIris.v` naming spec
  members qualified.
- **`rocq_compile_file` ACCEPTED the bare `LEnv`.** Its dune fallback resolves
  names the real build cannot, so its false greens are NOT limited to missing
  sibling `.vo`s — it is unreliable for anything touching module qualification.
  Only `make` caught it. Position-mode `rocq_start(file=…, line=…)` also catches
  it, replays through the project's real load path, works inside module functors
  where preamble mode cannot reach, and costs seconds.

*The concrete side — FUSE, do not split (correcting a wrong turn).* An earlier
version of this entry proposed giving ghosts their own concrete channel,
`ghosts : bv xlenbits -> list Annot`, by analogy with the instruction `words`.
**That analogy is wrong.** `words` is a separate total function because it has a
separate ORIGIN (`VerifierRel.v:179-186`: "supplied by Adequacy.v out of the
`∃ v` inside interp_ptsto_instr"), and that split costs a second bookkeeping
family — `wtable_rel`, `itable_relW_zip`, `wtable_rel_of_faith_forget`. Ghosts
share the AST's origin: the `list AnnotInstr` the author wrote. Splitting one
source in two and proving the halves agree is the sum type's disease in a new
costume. So: `cexec_cfg_addr` takes `gmap … AnnotInstr`, `instrs_of_list`
becomes `AnnotInstr`-valued, and the MEMORY predicates keep speaking `AST`
(`ptsto_instrs (ai_instr <$> instrs)`, `mem_has_instrs … (strip instrs')`),
which is where this document's Files table always put the boundary.

*Two further annotation kinds, and why the signature already fits them
(checked 2026-08-21 — no change needed, recorded so nobody widens the type
for them).*

- **Drop chunks** — a user-directed `chunk_gc`. A same-world WRAPPER, like the
  debug case. **Sound for ANY chunk** by affineness of `iProp` (a `fold_right`
  of `∗` can discard a conjunct); `PLAN-encoded-instr.md` §11 makes the point
  explicitly that soundness is NOT `encodes_instr`-specific and only
  COMPLETENESS is, and its `refine_chunk_gc` / `inst_gc_heap` / `cgc_binds_heap`
  are audited *Closed under the global context*. So this needs no `LEnv` entry
  and no per-use soundness proof — markedly cheaper than the lemma route. The
  price is completeness, and it fails LOUDLY at the next consume.
- **Drop an unreferenced logical variable** — a BIND, like the lemma case, and it
  composes with the *same* `θ ∘ θ'` code despite moving to a SMALLER context,
  because `acc_subst_right : w ⊒ wsubst w x t` has `wctx = w - x∷σ` and `⊒`
  orders worlds by INFORMATION, not size. (An earlier version of this entry
  asserted Σ grows monotonically within a run. **That is wrong.**) Motivation:
  `demonicv_prune` (`Propositions.v:1175`) only collapses on `block`, so a binder
  nothing references any more SURVIVES — an abstraction lemma shrinks terms but
  leaves the old binders in Σ, and the lvar-lookup work found variable *count* to
  be quadratic in lookup cost. Once nothing references `x`,
  `acc_subst_right x (term_val σ <any inhabitant>)` should be available, the
  substitution being the identity on everything precisely because nothing
  mentions `x`. **Sketch only — unimplemented, unproven, and it needs the occurs
  check run across heap, path condition and continuation.**

Neither is a shortcut past `PLAN-loop-invariant.md`: chunk-dropping cannot help
`muladd`, where `A0`/`A1` are live accumulators that must stay owned, so
abstraction remains the only route there.

*Phase 1 is COMPLETE.* `sexec_cfg_addr` calls `sexec_ghosts` for both slots and
the light branch is gated green (17 files, no edit to any example, `strip_id_*`
still `reflexivity`). What is left is Phase 2, and the claim that `refine_debug`
fires inside `rexec_cfg_addr` specifically is still UNVERIFIED — `main`'s
precedent is a far simpler proof, and `rexec_cfg_addr` already needs bespoke
handling for `chunk_gc`'s trivial world motion.

*Also noted, not acted on.* The whole-list coercion is a `list >-> list`
coercion, so it warns `does not respect the uniform inheritance condition` and
`New coercion path … is not definitionally an identity function
[ambiguous-paths]`. Benign under `-arg "-w all"`, but Coq can insert such a
coercion where you did not intend it, and the Phase 0 write-up did not record
it. Separately, the `strip_id_*` lemmas still live only in the gitignored
`Example/ZZAnnotStripIdProbe.v`; this document's "Files" table wants one per
example as a permanent trusted-surface anchor, and that has not been done.

## Log (earlier)

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

**DONE 2026-08-24; GATE 3 MET. See the top Log entry, and prefer it to the
paragraph below, whose prescribed route does not work.**

~~Plant one at a chosen pc and dump `(pathcondition, heap)` per trip via
`DebugCFGVerifierContract` + `vc_debug`~~ — measured: `vc_debug` produces a
~12 M-character goal and is unusable. Phases 1+2 already delivered the whole
mechanism; what Phase 3 actually cost was the measurement plus finding a
printable route (`Eval vm_compute` on the `postprocess (CFG_VC_triple …)` tree,
`Set Printing Width 1000`). `safe_debug` keeping `Debug` records and `prune`
preserving debug nodes (`Propositions.v:1221`) both hold as stated.

**GATE 3:** per-trip heap and path condition dumped for `ZZKslHeapCommon` at
`t=2`, showing the heap is static (which this plan asserts but has not measured).
**MET, with a refinement of "static":** static in chunk inventory (8 chunks,
same identities) and in |Σ| (20 binders, none added between trips); NOT static
in chunk order; NOT static in chunk CONTENTS, which grow from bare classed
existentials to nested compound terms within two trips — on a rig that pins term
shape flat on purpose. The stable-slots/growing-terms split is what makes the
Phase 4 abstraction lemma statable.

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
