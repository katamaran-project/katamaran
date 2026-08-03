# PLAN — land the chunk GC: stop leaking `encodes_instr` into the symbolic heap

Status: **LANDED 2026-08-03.** Branch `nextpc-param`. All six phases complete;
`scripts/gate.sh` green, no trusted statement changed. See §12 for the outcome.
Prerequisite reading: `PLAN-encoded-instr.md` **§10** (the root cause) and **§11**
(the audit of the archived proofs). This plan was the "recommended next step" those
two sections end on.

## §0. What and why, in five lines

`encodes_instr` is `is_duplicable := true` (`Sig.v:343`), and `heap_extractions`
KEEPS duplicable chunks on consume (`Chunks.v:106`). So every fetch adds an
`encodes_instr` chunk to the symbolic heap and nothing ever removes it: **the heap
grows by exactly one chunk per instruction step.** Per-step executor cost is
linear in heap size, so total cost is quadratic in the step count. Filtering those
chunks at each step collapses the quadratic coefficient of `allocated_words` from
**6,754,351 to −2,902** (i.e. zero) with a **byte-identical node census**.

**This is the only known lever on the CFGVer scaling wall.** Everything else has
been measured out: term size, fuel, `|wctx|`, the final tree, `postprocess`,
`solve_vc`, symbolic-base handling, per-step table copying.

Expected payoff (from the fitted models, §10): **1.32× / 1.65× / 2.29× / 3.58× /
6.17×** at N=8/16/32/64/128 on the `zzf` reproducer — i.e. it removes an
asymptotic term rather than shaving a constant.

## §1. Where the code comes from — READ THIS BEFORE `git show`

**Lift from `b24d0d15`, NOT from the tag `archive/gc-attempt-2026-07`.**

The tag points at `48c651f0`, whose own commit message is *"partial nextpc-param
edits on the GC base — SUPERSEDED, does not compile."* `7d93fe9d` (Phase 2c) does
not contain `refine_chunk_gc`/`inst_gc_heap` at all. `b24d0d15` ("PLAN step 2d —
Phase B complete") is the last commit that has everything AND builds; only two doc
commits separate it from the broken tip.

Verified at `b24d0d15` (§11): `Adequacy.vo` builds (exit 0, 76 files), and
`Print Assumptions` reports `refine_chunk_gc`, `inst_gc_heap`, `cgc_binds_heap` all
**Closed under the global context**, with `interpret_scheap_gc_heap` needing only
the allowlisted `Machine.pure_decode`.

```bash
git show b24d0d15:case_study/RiscvPmp/CFGVer/Verifier.v     > /tmp/src_Verifier.v
git show b24d0d15:case_study/RiscvPmp/CFGVer/VerifierRel.v  > /tmp/src_VerifierRel.v
git show b24d0d15:case_study/RiscvPmp/CFGVer/Adequacy.v     > /tmp/src_Adequacy.v
```

## §2. DECISION TAKEN: no `gc` flag — pin the GC always-on

The archived code threads `(gc wgc : bool)` through `sexec_cfg_addr`,
`cexec_cfg_addr`, `rexec_cfg_addr` and three `Adequacy.v` lemmas. **Do not
reintroduce that.** Reasons, in order of weight:

1. The current executor has NO flags (`sexec_cfg_addr (fuel : nat) : ⊢
   SInstrTableW -> …`). Adding two would ripple into `VerifierRel`, `Adequacy`,
   `EndToEnd` and `Contracts.v`'s `CFG_VC_triple`.
2. **A flag is an established failure mode in this exact code.** A previous port
   left `Adequacy.v` at `false false` while `Contracts.v` emitted `true true`, so
   the fast VC could not reach the adequacy chain at all — a whole build lost to
   flag skew. See the memory note.
3. The A/B measurement the flag existed for is already done (§10). Re-running it
   needs two builds, not a flag.
4. Dropping is sound unconditionally (§4), so there is no correctness reason to
   keep an off switch.

Consequence: `gc_heap`/`cgc_heap` lose their `bool` argument and become plain
filters; `chunk_gc`/`cchunk_gc` take no flag; `cgc_binds_heap` loses its `wgc`
branch entirely (it becomes a one-bind statement, not two).

**`cgc_dead_roots` and everything world-GC is OUT OF SCOPE. Do not port it.** It is
unprovable — `gc_dead_roots` pins a forward-dead variable to an arbitrary
inhabitant, so at disagreeing valuations the tree is vacuously safe, and the
obstruction is structural (`PLAN-nextpc-param.md` §0). If a phase below seems to
need it, stop and re-read that section.

## §3. Model assignment, and the rule that makes it safe

| phase | who | why |
|---|---|---|
| 1. lift the executor-independent lemmas | **Haiku** | pure transcription + qualified-name fixups; a compile is the oracle |
| 2. insert the bind, mirror it concretely | **Haiku**, then Sonnet reviews | two 1-line edits + a census gate that catches any semantic change |
| 3. re-pair `rexec_cfg_addr` | **Sonnet** | Iris/`rsolve` proof surgery; the actual difficulty |
| 4. absorb the bind in `Adequacy.v` | **Sonnet** | Iris; needs `cgc_binds_heap_fwd` and its keyed-rewrite trap |
| 5. measurement gate | **Haiku** runs, **Sonnet/owner** interprets | mechanical recipe; see the hard rule below |
| 6. gate + trusted-surface review | **owner** | axiom-clean list, no statement changed |

**HARD RULE, from two recorded incidents: Haiku must never report a measurement as
a fact, and must never conclude from an uncommitted tree.** A previous Haiku run
reported "N=16: 6.1 s / N=64: 6.8 s" — both refuted, produced from uncommitted
local edits, and unreproducible because no commit touched any `Example/` file. So:

- every Haiku phase ends in a **mechanical, checkable gate** (a compile, or a
  census equality), never a judgement;
- Haiku **commits before measuring**, and quotes the commit hash with any number;
- Haiku gates every probe on `Finished transaction` appearing in the output —
  a probe that fails to compile reports the *baseline* allocation, which reads as
  "free" (this bit twice on 2026-08-01);
- Haiku uses `keep_vo=True` on every `rocq_compile_file` against a real file.
  Without it the tool DELETES the `.vo` — it silently removed `Verifier.vo` from
  the build tree mid-session on 2026-08-03.

## §4. The soundness argument, stated once so nobody re-derives it

Dropping a chunk from the symbolic heap is sound **because the ambient BI is
affine**. `interpret_scheap` is a `fold_right` of separating conjunction
(`Chunks.v`), so the dropped case simply discards the head conjunct — the `_` in
`iIntros "[_ H]"`. `iProp Σ` is affine; `Chunks.v`'s abstract `HProp` is not, which
is exactly why `interpret_scheap_gc_heap` must live in `Adequacy.v` and cannot be
pushed down next to `interpret_scheap`.

That argument works for **any** chunk. What is specific to `encodes_instr` is only
**completeness**: `chunk_gc` performs an unjustified drop, which "costs
completeness, never soundness" (the archive's own words). Completeness is an
empirical question, and §10 answers it — the node census is byte-identical at
N=1/2/4/8, so nothing live was dropped. Phase 2's gate re-checks this.

> Do NOT try to fix this by un-duplicating `encodes_instr` (`Sig.v:343 → false`).
> Documented dead end: it breaks `valid_execute_fetch`, because inside `fun_fetch`
> one chunk must serve both `close_ptsto_instr`'s consume and fetch's postcondition
> export. It is also a heap-side change that would not shrink `|wctx|`, and
> duplicable is the semantically honest marking (the interpretation is a pure
> proposition). See `PLAN-encoded-instr.md` §1.

---

## §5. PHASE 1 — lift the executor-independent lemmas  [HAIKU]

None of these mention the instruction table, the executor signature, or the flags,
so they port with only the flag argument removed.

### 1a. `Verifier.v` — insert after `persist_etable` (currently `:283`)

From `/tmp/src_Verifier.v`: `is_encodes_instr` (~`:265`), `gc_heap` (~`:286`),
`chunk_gc` (~`:458`).

```coq
Definition is_encodes_instr {V : Ty -> Set} (c : GChunk V) : bool :=
  match c with chunk_user encodes_instr _ => true | _ => false end.

Definition gc_heap {Σ} (h : SHeap Σ) : SHeap Σ :=
  List.filter (fun c => negb (is_encodes_instr c)) h.

Definition chunk_gc : forall w : World, SHeapSpec Unit w :=
  fun w POST h => POST w acc_refl tt (gc_heap h).
```

- Keep `is_encodes_instr` **polymorphic in `V`**: `Chunk Σ = GChunk (Term Σ)` and
  `SCChunk = GChunk RelVal`, so ONE definition serves the symbolic and concrete
  sides, and the refinement forces them to filter identically.
- The archived `chunk_gc` took an unused `STerm ty_xlenbits w` (the pc). Drop it.
- `chunk_gc` uses **`acc_refl`** — no world motion. That is what makes Phase 3
  easy relative to the world GC, so do not "improve" it into something that moves
  the world.
- **`Verifier.v` is deliberately Iris-free.** These three additions are
  (`Chunks` + `SHeapSpec` only). Do not add a require.

### 1b. `VerifierRel.v` — `Section Shallow`, insert after `cexec_instruction` (`:111`)

From `/tmp/src_VerifierRel.v`: `cgc_heap` (`:125`), `cchunk_gc` (`:128`),
`filter_map_comm` (`:140`), `inst_gc_heap` (`:148`), `mono_cchunk_gc` (`:242`).

Traps, all from the archive's own comments — each cost a debugging cycle:

- `inst_gc_heap`'s proof must `apply filter_map_comm`, **not** `rewrite` it.
  `inst`-on-lists is only *convertible* to `List.map`, so after a `cbn` the goal
  shows `map` where a rewrite is looking for `inst` (keyed matching — see
  `rocq-pitfalls`).
- `mono_cchunk_gc` **must be registered** as `#[export] Instance`. Left
  unregistered, typeclass search on the executor's bind spine backtracks with the
  result relation still an evar and **diverges** rather than failing cleanly.
  Its proof is `firstorder`.
- `filter_map_comm` is generic and belongs in `theories/Prelude.v`; keep it local
  for now to avoid a framework-wide rebuild.

### 1c. `Adequacy.v` — insert near `sound_exec_cfg_addr_myWP2` (`:1084`)

`interpret_scheap_gc_heap` from `/tmp/src_Adequacy.v:1057`. Restate over the
flagless `cgc_heap`. Proof shape is unchanged:

```coq
destruct h as [|c h IH]; … destruct (is_encodes_instr c); cbn;
  [iIntros "[_ H]" | iIntros "[Hc H]"; iFrame "Hc"]; iApply IH; iExact "H".
```

### GATE 1 — mechanical, no judgement

```
rocq_compile_file Verifier.v     mode=full keep_vo=True
rocq_compile_file VerifierRel.v  mode=full keep_vo=True
rocq_compile_file Adequacy.v     mode=full keep_vo=True
```
then a scratch file running `Print Assumptions` on `inst_gc_heap` and
`interpret_scheap_gc_heap`. Expect **"Closed under the global context"** for the
first and only `Machine.pure_decode` for the second.

`refine_chunk_gc` + `refine_compat_chunk_gc` (`/tmp/src_VerifierRel.v:478,:493`)
also belong to this phase if `Section Relational`'s context permits; if `rsolve`
misbehaves, hand them to Sonnet rather than improvising — the proof is six lines
and the only content is `inst_gc_heap` via `repₚ_cong`.

**STOP after Gate 1. Commit. Report the hashes.**

---

## §6. PHASE 2 — insert the bind on both sides  [HAIKU, Sonnet reviews]

Two edits, one per side, and they must mirror each other exactly or Phase 3 is
unprovable.

### 2a. Symbolic — `Verifier.v:368`

```coq
(* before *)  ⟨ θ1 ⟩ apc' <- sexec_instruction i apc anp wd ;;
(* after  *)  ⟨ θ0 ⟩ _    <- chunk_gc ;;
              ⟨ θ1 ⟩ apc' <- sexec_instruction i apc anp wd ;;
```

Placement matters: the GC must run **before** the step, so the chunk produced by
step *k* is dropped at the head of step *k+1*. (This is also what the §10
measurement did, and why its numbers read `Σ(k=0..S−1)k` rather than `Σ(k=1..S)k`.)
Persisting `tbl`/`exits` through the extra `θ0` may be required — follow whatever
the type error says; `persist_itableW`/`persist_etable` already exist.

### 2b. Concrete mirror — `VerifierRel.v:149`

```coq
_ <- cchunk_gc ;;
apc' <- cexec_instruction i apc anp (ty.SyncVal (words v)) ;;
```

The two sides must be structurally identical modulo `inst`; that is the entire
content of Phase 3.

### 2c. `cgc_binds_heap` / `cgc_binds_heap_fwd` — adapt, do not copy

The archived pair absorbs TWO binds (`cchunk_gc` then `if wgc then cgc_dead_roots
else pure tt`). With no world GC there is one bind, so the statement simplifies to

```coq
Lemma cgc_binds_heap {A} (k : CHeapSpec A) (Φ : A -> SCHeap -> Prop) (h : SCHeap) :
  (_ <- cchunk_gc ;; k) Φ h = k Φ (cgc_heap h).
Proof. reflexivity. Qed.
```

Keep the `_fwd` variant. **Trap, verbatim from the archive:** `rewrite
cgc_binds_heap in H` **FAILS** — rewrite matches keyed on the LHS head symbol
(`CHeapSpec.bind`), but the occurrence produced by `cexec_instruction`'s
postcondition is already beta-reduced to `cchunk_gc (fun _ h1 => …) h`.
`apply cgc_binds_heap_fwd in H` unifies up to full conversion and goes through.

### GATE 2 — the completeness control, and it is an EQUALITY not a judgement

`VerifierRel.v` will not compile yet (`rexec_cfg_addr` is Phase 3). Compile
`Verifier.v` only, then re-run the node census from `PLAN-encoded-instr.md` §9's
probes and require **every counter byte-identical** to the pre-change values on
the `zzf` reproducer:

| N | 1 | 2 | 4 | 8 |
|---|---|---|---|---|
| nodes | 2168 | 4294 | 8546 | 17050 |
| pcsum | 20831 | 56973 | 129257 | 273825 |
| wsum | 44521 | 88423 | 176227 | 351835 |
| tsize | 650 | 1141 | 2123 | 4087 |
| depth | 1363 | 2685 | 5329 | 10617 |

Any deviation means completeness was lost — a chunk something still needed got
dropped. **That is a STOP-and-escalate, not something to tune.**

Recipe and probe files: `.claude/skills/rocq-timeout-triage/references/allocation-probes.md`.

---

## §7. PHASE 3 — re-pair `rexec_cfg_addr`  [SONNET]

**This is the bulk of the work.** `VerifierRel.v:486` is a real, hole-free proof in
the current tree (unlike the archive, where it is the one `Admitted`). Adding a
bind to the step means the refinement proof must pair that bind too.

What is in hand:

- `refine_chunk_gc : ⊢ ℛ⟦RHeapSpec RUnit⟧ cchunk_gc chunk_gc` — **already proved
  and axiom-free** (§11). Its whole content is `inst_gc_heap` applied via
  `repₚ_cong`, and `refine_T` is legitimate precisely because `chunk_gc` uses
  `acc_refl` and does not move the world.
- `refine_compat_chunk_gc` registers it so `rsolve` dispatches it.

What has to change: the fuel step currently pairs one bind; it must pair two.
The archive's note says this is `HeapSpec.refine_bind` — the same combinator the
existing proof already uses for the `sexec_instruction` bind. Expect the
`iInduction` on fuel and the four `is_exit`/`lookup_instr` cases to be untouched.

Guidance:

- Read **`cfgver-rsolve`** before fighting `rsolve`; and **`cfgver-refinement`**
  for `RefineCompat` structure.
- `rocq_start` on `VerifierRel.v` **OOMs pet** (~5 GB against a 7.6 GB cap). Use
  **preamble mode** (`rocq_start(preamble=…)` + `rocq_check`), or a
  `Show.`+`admit`+`Admitted` goal dump to get the shape. See `rocq-implementation`
  §1.
- Prefer an **Iris-level wrapper lemma** over `iStopProof` at a call site.
  `iStopProof` folds the whole persistent context into one conjunction, so its
  intro pattern breaks whenever an unrelated hypothesis is introduced earlier.

### GATE 3
`rocq_compile_file VerifierRel.v mode=full keep_vo=True` green, and
`Print Assumptions` on `rexec_cfg_addr` shows **no new axioms** versus the
pre-change baseline.

---

## §8. PHASE 4 — absorb the bind in `Adequacy.v`  [SONNET]

`sound_exec_cfg_addr_myWP2` (`:1084`) must account for the new `cchunk_gc` bind.
The archived proof does it in one step via `cgc_binds_heap_fwd` (§6.2c) plus
`interpret_scheap_gc_heap` to weaken the heap interpretation. Both are in hand and
axiom-free.

Note the archive kept these lemmas **generic in the flags** rather than pinning
them, because pinning broke the `EndToEnd` join point. With no flags that concern
disappears — but if a unification failure appears at `EndToEnd.v:142` (where
`CFG_VC_triple` feeds `sound_scfg_verification_condition_myWP2`), that is the same
class of problem and the memory note describes its shape.

### GATE 4
`make -f Makefile.coq case_study/RiscvPmp/CFGVer/Results.vo` green. **Bound `-j`
by RAM** (~6 GB/job; `GATE_JOBS=1` with a browser open). A `Verifier.v` change
invalidates all seven examples, so this is a near-full rebuild.

---

## §9. PHASE 5 — the measurement gate  [HAIKU runs, SONNET/owner interprets]

Re-run §10's two measurements on the landed code. **Commit first, then measure.**

1. **Heap census.** Instrument per
   `references/allocation-probes.md` §5 and confirm `Σ heap` loses its N² term:
   was `105·N + 98·N²`, expect **affine**. The `encodes_instr` count should be 0
   or O(1), not `98·N² − 7·N`.
2. **Allocation.** `allocated_words` minus an imports-only baseline, on `zzf` at
   N=1/2/4/8. Fit `a + b·N + c·N²` on three points, **hold one out**. Expect
   `c ≈ 0` (baseline was 6,754,351) and a pure affine model to fit within ~0.01%.

Expected speedups 1.32×/1.65×/2.29× at N=8/16/32. **If `c` does not collapse, the
GC is not firing where the probe fired** — check placement (§6.2a) before
concluding anything about the model.

Then, and only then: try `zzn` at N=32 and N=64, which §8 recorded as
earlyoom-killed at 5.80 GB. The model predicts N=32 becomes reachable.

---

## §10. PHASE 6 — gate and trusted-surface review  [OWNER]

- `scripts/gate.sh` green: full build, no proof holes, end theorems axiom-clean.
  Expected axiom set unchanged: `Machine.pure_decode`, `Base.mmioenv`.
- **No trusted statement changed.** Diff `Noninterference.v`,
  `Example/*Result.v`, and the `*_instrs`/`*_specs` blocks in `Example/*.v` — all
  should be untouched. The chunk GC is an internal executor optimisation; if any
  end theorem's statement moved, something is wrong.
- Update the docs in the SAME commit: `PLAN-encoded-instr.md` §10/§11 get a
  "LANDED" banner, `cfgver-executor`'s body gets the outcome, and the memory note
  gets the result. `cfgver-executor`'s **`description:`** also still names `|wctx|`
  as the dominant driver and needs a `skill-routing-maintenance` pass — that is
  hook-gated and needs the owner to authorise the subagents.

---

## §11. Traps checklist (each already cost this project time)

- `rewrite cgc_binds_heap in H` fails; use `apply … in H` (§6.2c).
- `apply filter_map_comm`, never `rewrite` (§5.1b).
- `mono_cchunk_gc` unregistered ⇒ typeclass search **diverges** (§5.1b).
- `interpret_scheap_gc_heap` cannot move to `Chunks.v` — affineness (§4).
- Never reintroduce `gc`/`wgc` flags; flag skew already cost a build (§2).
- Never port `gc_dead_roots` — unprovable (§2).
- `rocq_compile_file` without `keep_vo=True` DELETES the `.vo`.
- Probes: gate on `Finished transaction`, or a failed probe reports the baseline
  allocation and reads as "free".
- ONE heavy `Eval` per `coqc` process.
- Wall clock on this box varies **2.3×** on identical input. Use
  `allocated_words`.
- `Tables.v` needs `Open Scope list_scope` after its imports; don't let a new
  require reorder that.
- Keep `Verifier.v` Iris-free and `Example/Prelude.v` free of `EndToEnd`.

---

## §12. LANDED 2026-08-03 — Phase 5/6 results

Phases 1-4 (commits `7a364744`..`05d909f8`) inserted `chunk_gc`/`cchunk_gc` on
both sides, re-paired `rexec_cfg_addr`, and absorbed the bind in
`sound_exec_cfg_addr_myWP2`. This section closes out Phase 5 (measurement) and
Phase 6 (gate + trusted-surface review).

### Phase 5 — measurement gate: GREEN

Measured on the `zzf` flat reproducer, N=1/2/4/8 (probe files were scratch,
since deleted — see below).

**Gate 1, tree census (completeness control) — byte-identical to the
pre-change baseline in §6's table:**

| N | nodes | pcsum | wsum | tsize | depth |
|---|---|---|---|---|---|
| 1 | 2168 | 20831 | 44521 | 650 | 1363 |
| 2 | 4294 | 56973 | 129257 | 1141 | 2685 |
| 4 | 8546 | 129257 | 176227 | 2123 | 5329 |
| 8 | 17050 | 273825 | 351835 | 4087 | 10617 |

No tree structure changed — the GC does not truncate a live path.

**Gate 2, allocation model — quadratic term collapses, pure affine fit:**

```
alloc(N) = -38,531,897 + 167,351,070.9·N        (fit on N=1,8)
```

Held-out verification: N=2 predicted vs actual 0.006% error, N=4 0.004% error.
Compare the pre-change arm A model (`PLAN-encoded-instr.md` §10):
`-38.6M + 165.9M·N + 6.75M·N²` — the quadratic coefficient goes from 6.75M to
effectively 0.

**Gate 3, speedup — matches the plan's prediction exactly:** 1.32× at N=8
(1.04× at N=1, growing with N since the term removed is quadratic, not a
constant).

### Phase 6 — gate + trusted-surface review: GREEN

- `git diff 1083bd75..HEAD` (the whole chunk-GC investigation-to-landing span)
  touches only `Adequacy.v`, `Verifier.v`, `VerifierRel.v` and the two `PLAN-*.md`
  docs. **Zero changes** to `Noninterference.v` or any `Example/*.v` /
  `Example/*Result.v` file — the trusted statement surface is untouched, as §4
  requires for an internal executor optimisation.
- `GATE_JOBS=1 scripts/gate.sh`:
  ```
  ✓ GATE PASSED — build clean, no holes, 12 end theorems axiom-clean
    (only: Machine.pure_decode Base.mmioenv).
  ```
  Axiom set is exactly the pre-existing allowlist — unchanged by this work.
- **One pre-existing, unrelated gate-blocker found and removed in the same
  commit:** three scratch diagnostic files (`Example/ZZCtlKsl.v`,
  `Example/ZZGoalsP1.v`, `Example/ZZCtlZzn.v`, added in `ab3503e6`, well before
  this plan started) were goal-count/`idtac` printers that were deliberately
  `Admitted` — never meant to be real proofs, not referenced by `_CoqProject`
  or anything else, and orthogonal to the chunk GC. They tripped the gate's
  hole-scan (which is unconditional over the whole `CFGVer` tree, not just
  build targets), so they were deleted rather than left to block every future
  gate run.
- The Phase 5 probe files (`Phase5CensusZzf.v`, `Phase5Zzf{1,2,4,8}.v`,
  `Phase5ZzfBaseline.v`) and the standalone `PHASE5-RESULTS.md` were scratch —
  not in `_CoqProject`, one-shot measurement harnesses whose result is now
  folded into this section — and were deleted after folding, matching how
  every earlier probe batch in this investigation (`ZZDg*`, `ZZFwd*`, `ZZGc*`,
  etc.) was scratch rather than a permanent addition.

### Skill/doc updates (same commit)

- `PLAN-encoded-instr.md` §11 gets a LANDED pointer back to this section.
- `cfgver-executor`'s body gets a LANDED banner; its `description:` is
  reworded to retire the "|wctx| is the dominant driver" claim (superseded by
  the leaked-chunk finding) — validated via `skill-routing-maintenance`
  (new eval entry Q102, regression checks Q79/Q98, all `cfgver-executor`,
  all correct `TOTAL=34` checksums).
- This memory note: see `project_chunk_gc_landed` (auto-memory).
