# PLAN-unify-generators — collapse the contract-generator family

Status: **ALL STAGES DONE. 0 and 1 on 2026-08-18; 3a, 3b and 2 on 2026-08-18/19.**
Gate green at every stage (7 runs), 14 end theorems axiom-clean throughout, all 29
end-theorem statements byte-identical.

### Where it landed, against the goals

| goal | outcome |
|---|---|
| **G1** nothing becomes unproved | **MET.** 7 green gates; no `Result` file modified after stage 1's bullet adjustments; statements byte-identical. |
| **G2** fewer lines | **MISSED on the numbers, met on the intent.** Builder *implementations* 5 → **1**, bridge *implementations* 9 → **2**; but NAMES are 6 and 6 (wrappers survive deliberately), `GenContract.v` GREW 714 → 885, `EndToEnd.v` 2038 → 1930. See §G2 note. |
| **G3** byte payoff measured | **MET, and it beat the prediction.** 8 entries mint **1** variable not 8 (measured); cost **1.10×/1.32×/1.77×** at 2/4/8 cells vs a predicted ~1.1× at 8. NOT an established exponent fix — held-out fit fails. `diagnostics/byte-classed-block-payoff.md`. |
| **G4** diagnostics stay valid | **MET, and it found a defect.** check_scalar loop1 re-run; its conclusion confirmed, its *tables* retracted as cross-protocol, same defect found in loop2. Imports baseline moved 434.8M → 604.3M. |
| **G5** non-goals | Respected — per-step demonic `|Σ|` untouched, residual growth still unidentified, no example's proof obligation changed. |

**The single most useful thing learned:** the wrappers are the point, not a
shortfall. Collapsing them would have exported ~50 lines of ritual into 13
trusted-surface `Result` files (measured on a worked example, §stage 3b), which is
a net maintainability *loss* by the criterion this plan exists to serve. G2 counts
names; the thing worth counting is implementations.

**Read this before starting stage 3:** stage 1 was billed here as "Low risk" and a
line-count win. Both were wrong, in opposite directions. It required narrowing a
BRIDGE's statement (not just a builder's) and it GREW total lines. What it actually
bought was maintenance value — two duplicated implementations collapsed into
delegations — which is a real but different currency from the one G2 counts. Price
stage 3 in that currency, not in lines.

Written 2026-08-18 after the classed-existential work
(`PLAN-classed-existentials.md`) added a fifth contract builder and a ninth
noninterference bridge.

### Stage 0 outcome, measured

| metric | baseline (`c68a0890`) | after stage 0 | plan's stage-0 target |
|---|---|---|---|
| `GenContract.v` lines | 714 | **714** (untouched) | — |
| `EndToEnd.v` lines | 2038 | **1955** (−83) | ≤ 1880 — **NOT MET** |
| contract builders | 5 | **5** | 4 — **CANCELLED, premise false** |
| noninterference bridges | 9 | **7** | 7 ✓ |

Deleted: `gen_contract_noninterferent` and `gen_contract_noninterferent_rel_simple`
(both bridges, both zero-user). `EndToEnd.vo` rebuilt with `make -f Makefile.coq`
(the authority, exit 0) and the deletions confirmed absent from the artifact via
`strings`. The `≤ 1880` target was missed because it had been sized assuming a
builder deletion that turned out to be impossible; the two dead bridges are only
83 lines between them.

**Cost of the deletion, for the record:** 12 stale references across 6 skills had
to be repaired in the same commit, 3 of them in `description:` frontmatter (so the
`skill-edit-guard` hook required a `skill-routing-maintenance` consult; recorded as
`results-2026-08-18.json`, no judges run — the edit was classified routing-neutral
because the replacement keeps `gen_contract_noninterferent` as a substring). So
"delete the genuinely dead" is free on the Rocq side and NOT free on the docs side.
Weigh that before treating stage 3's bridge collapse (9 → 2) as merely structural:
its doc footprint will be several times this one's.

### Stage 1 outcome, measured

| metric | after stage 0 | after stage 1 | note |
|---|---|---|---|
| `GenContract.v` total lines | 714 | **760** (+46) | grew |
| `EndToEnd.v` total lines | 1955 | **1959** (+4) | grew |
| `GenContract.v` CODE lines (comments stripped) | 350 | **361** (+11) | new reusable machinery |
| `EndToEnd.v` CODE lines (comments stripped) | 1561 | **1526** (−35) | the deleted ritual |
| contract builders | 5 | **5** | `gen_contract_param` survives, now a wrapper |
| noninterference bridges | 7 | **7** | `_param` survives, now a delegation |

**Net: code −24 lines, totals +50** — the growth is ~74 lines of comment recording
the two traps below. Duplicated *logic* did shrink: `gen_contract_param` shed ~12
lines of copied contract-record boilerplate, and `gen_contract_noninterferent_param`
shed a ~40-line copy of the `cfg_instrs_endToEnd_with_memory` + `ImplPre` ritual.
Neither builder nor bridge COUNT moved, and by design cannot until stage 3 deletes
the wrappers.

**The bridge could delegate too — this was not in the plan.** Stage 1 as written
only said "`gen_contract_param` delegates", and the obvious reading was that the
bridge's `ImplPre` would have to be RE-PROVED against the new
`gen_mem_pre_rel_classed []` shape. It does not: at `mem_specs = []`,
`gen_contract_noninterferent_rel_classed`'s conclusion collapses to
`_param`'s, so `_param` delegates to it and the ~40-line copy is simply deleted.
That is the bridge-side mirror of the builder-side delegation and is where most of
stage 1's actual value sits. Knock-ons: `_param` lost its `HDataAddrs` premise
(vacuous at `[]`) and the `4*|mem_specs|` term in `Hlen`, so `_param_simple` and
`Example/JumpsResult.v` each lost a bullet and their VC moved from position 5 to 4.

**Trusted surface did not move**, which is worth recording because this stage
narrows a lemma: `_param_simple`'s statement already read `… reg_specs []` with
exactly the `Hlen` the new `_param` requires, so it is byte-identical and the 8
`Result` files that use it needed NO edits. `JumpsResult.v`'s theorem statement is
likewise unchanged — only its proof bullets moved.

`mem_specs` was dropped from `gen_contract_param` rather than kept as a stub. It was
a `list mem_full_spec` — ABSOLUTE addresses — and the classed block needs
base-relative `mem_spec_rel` offsets; there is no translation without knowing the
base. All 15 call sites passed `[]` (9 committed contracts + 6 rigs), so nothing was
lost. This also *supersedes* the "no classed counterpart of `gen_contract_param`"
note at `GenContract.v:536`: the width-index obstruction is real for a NON-EMPTY
concrete block, but that case is now unrepresentable rather than unimplemented.

#### Two traps, both of which cost a build or would have

1. **Every data argument of the `_rel*` bridges is IMPLICIT** (each occurs in some
   premise's type, under `Set Implicit Arguments`), so the first *explicit*
   argument is `HND`. Passing them positionally fails with
   `"map reg_spec_to_rel reg_specs" has type "list reg_spec_rel" while it is
   expected to have type "NoDup (...)"` — which reads like a statement bug. Use
   `(name := v)`. Folded into `cfgver-endtoend-internals` §Implicit-argument
   asymmetry.
2. **Unification will not solve `map f ?l ≡ []`.** So a bare
   `eapply gen_contract_noninterferent_rel_classed` can never pin `?mem_specs := []`
   from the conclusion's `map (concretize_mem ia) ?mem_specs` slot. Naming the
   implicit works because it goes through CONVERSION (`map f [] ≡ []`) instead.
   Caught in 9 ms by a scratch preamble probe, *before* paying for a build — the
   one time in this stage that the interactive-first rule paid off directly.
   Also note `bound`, `fuel` and `extra_exit_offs` are likewise undetermined by the
   conclusion; pin all four by name and the "discharge `valid_contract` FIRST"
   ordering hazard cannot arise at all.

Process note: `rocq_start` position mode on `EndToEnd.v` **OOMed pet at >7.6 GB**,
so the new bridge proof could not be checked in-file at all — the plan's own
"develop in `Example/ZZClassBridge.v`" advice does not help either, because that
file `Require`s the very `EndToEnd.vo` being changed and would test the stale one.
Abstract preamble probes plus one confirming build was the working loop.

## Why

`GenContract.v` has **5 contract builders** and `EndToEnd.v` has **9**
noninterference bridges, and they are near-copies of each other along two
independent dimensions (base treatment × data-block shape) plus a
general/`_simple` split.

That is ordinary duplication, and it would be worth reducing on its own. But
there is also a concrete functional payoff, which is what makes this more than
tidying: **`check_scalar_loop1` cannot use the classed data block today**, so its
8 byte entries still mint 8 logic variables where 1 would do. `|Σ|` is the
dominant cost driver in every one of the four `diagnostics/` records, and the
classed builder was measured as an *exponent* reduction (1.72 → 1.22 at N=8→16,
`diagnostics/key-schedule-loop2-cost-drivers.md` §Re-measurement 2026-08-18).
The reason loop1 is excluded is **not** the width-index trap — its specs are
already `list mem_spec_rel`. It is simply that no byte-granular classed block has
been written. Unifying the family is the natural place to add one.

### There is a recorded decision AGAINST this — read it before starting

`GenContract.v:662`:

> "`gen_contract_rel` itself is deliberately left byte-identical rather than
> refactored to delegate here: nine `vm_compute` VC proofs reduce through it, so
> the duplication is cheaper than the perturbation."

That was correct when written and must not be dismissed. Three things weakened it
since, and if any of them stops being true this plan should be reconsidered:

1. ~~`gen_contract` dropped to **zero users** — including its bridge
   `gen_contract_noninterferent`, whose only two remaining mentions are prose in
   comments.~~ **RETRACTED 2026-08-18.** The bridge half was right (zero users,
   deleted in stage 0). The builder half was **wrong**: `gen_contract` has three
   live users — `Example/MvSwap.v:93` (`mv_nonzero_start_ex`, a committed example
   with a live VC proof, inside the gate's build closure) and five uses in
   `ZZKslConcCommon.v`, which is explicitly the **concrete-base control arm** for
   the KSL cost measurements. That is the same argument this document uses to
   rescue `gen_contract_rel` one section below, so the error was
   self-inconsistent: it failed this plan's own rule *"dead-for-experiments is not
   dead-for-examples; check rig users before calling any builder unused"*. The
   check that catches it is `grep` over `Example/ZZ*.v`, which are gitignored and
   so invisible to a `git ls-files`-based sweep. `gen_contract` is a KEEP, and
   with it the `5 → 2` builder target in G2 is unreachable as stated — the floor
   is **3** (unified + `gen_contract_rel` + `gen_contract`), unless the two
   control arms are first re-expressed over the unified builder.
2. **All nine `gen_contract_param` call sites pass `mem_specs = []`** — its
   concrete `mem_full_spec` data block, the one thing that genuinely cannot be
   classed, has no users at all.
3. There is now a measurable payoff (item above), not only structural benefit.

### The assumption behind stage 1 has already been TESTED

The perturbation worry is concrete: `gen_mem_pre []` is `⊤`, while
`gen_mem_pre_rel_classed []` is `⊤ ∗ ⊤ ∗ ⊤` — **not** syntactically equal, so
delegation is not free by inspection. `Example/ZZUnifyProbe.v` (throwaway, run
2026-08-18) put SetX2's contract in both forms and proved both with the identical
`intros; vm_compute; solve_vc; solve_symbase_fetch`. **Both closed.** So the
register-only configuration can delegate without touching a single proof script.
Re-create that probe before starting stage 1 if it has rotted; it is ~20 s.

## Goals — all measurable, all checked before the plan is called done

### G1. Nothing that is proved today becomes unproved

- **All 14 gate theorems still `Print Assumptions`-clean**, showing only
  `Machine.pure_decode` and `Base.mmioenv`: `swap`, `jumpIfZero`, `jmp_fwd`,
  `countdown`, `countdown_mem`, `set_X2_to_42`, `cmovznz4`, `precompute`,
  `key_schedule_loop2`, `muladd_q`, `modpow_win`, `modpow_win_full`,
  `check_scalar`, `check_scalar_loop1` (all `_noninterferent_param`).
- **All 29 end theorems in `Example/*Result.v` still compile**, and their
  STATEMENTS are byte-identical — the trusted surface must not move. Check with
  `git diff` restricted to statement lines, as was done for the classed
  migration.
- **`./scripts/gate.sh` green** (`GATE_JOBS=1` on a ≤16 GB box) at the end of
  every stage that touches a builder — not only at the end of the plan.
- **No `Admitted`/`Axiom` anywhere**, which the gate's step 2 checks.

### G2. Fewer lines, and the reduction is verified not asserted

Baseline, measured 2026-08-18 at commit `5afab603`:

| metric | now | target |
|---|---|---|
| `GenContract.v` | 714 lines | ≤ 650 |
| `EndToEnd.v` | 2038 lines | ≤ 1750 |
| contract builders | 5 | ~~**2**~~ → **3** (revised 2026-08-18) — the unified one, plus TWO measurement controls that must survive: `gen_contract_rel` (unclassed arm) and `gen_contract` (concrete-base arm, see the retraction in §Why) |
| data/reg block builders | 7 | ≤ 4 |
| noninterference bridges | 9 | **2** (`_u` + `_u_simple`) |

~~Stage-0-only targets (achievable with zero risk): builders 5 → **4**, bridges
9 → 7, `EndToEnd.v` ≤ 1880.~~ **Superseded 2026-08-18 by what stage 0 actually
achieved:** builders 5 → 5, bridges 9 → 7, `EndToEnd.v` 2038 → 1955. The builder
and line targets both assumed the retracted zero-users claim. (Both
`gen_contract_rel` and `gen_contract` stay — they are measurement controls.)

Record the actual numbers at each stage. **A stage that reduces duplication but
grows total lines is a legitimate outcome** — a `gran`-indexed builder may need
more machinery than the copies it replaces — but it must then be justified on the
functional payoff (G3), not filed as a line-count win.

### G3. The check_scalar payoff is realised and measured

- A byte-granular classed data block exists, and `check_scalar_loop1` uses it.
- `loop1_byte_specs_rel`'s 8 entries mint **1** logic variable, not 8.
- **Measured** with a matched pair on the `ZZVC*`/`allocated_words` protocol
  (`diagnostics/key-schedule-loop2-cost-drivers.md` §Reproduction), one axis, one
  heavy sentence per process, gated on `Finished transaction` + `Error`. Report
  the ratio whatever it is. Predicted small at 8 cells by the measured
  cell-count curve (1.00× at 1, 1.02× at 2, 1.20× at 12, 1.41× at 16) — **so a
  ~1.1× result here is the expected outcome, not a failure**, and the value is
  that loop1's cost stops growing per declared byte-cell as the array grows.

### G4. The diagnostics stay valid, and are re-run where inputs changed

The four `diagnostics/` records are completed causal records, not living docs.
This plan must not silently invalidate them.

- **Re-run** any record whose measured configuration this plan changes. On
  current understanding that is the check_scalar set, *if and only if* loop1
  migrates to the byte-classed block (G3) — its rigs
  (`ZZByteLoop1*`, `ZZByteLoop2*`, `ZZPadShr*`, `ZZComb*`) are built on the
  builder being changed.
- **Do not re-run** records whose inputs are untouched; say so explicitly in the
  record rather than leaving it ambiguous (the pattern established by the
  2026-08-18 follow-on notes).
- **All 34 `ZZ*Common.v` rigs must still compile.** They are not in
  `_CoqProject` and the gate does not keep them green, so a builder signature
  change breaks them silently. Compile-check all 34 at the end of each stage —
  this is the acceptance criterion most likely to be forgotten, because nothing
  enforces it.
- Any figure this plan overturns gets the retraction discipline in
  `cfgver-scaling-diagnostics`: marked `RETRACTED <date>` in place, never
  deleted, with the plans/memory citations fixed in the same commit.

### G5. Non-goals, stated so they do not creep in

- **Not** removing the per-step demonic-variable source of `|Σ|`. Different
  mechanism, different plan.
- **Not** identifying the residual exp ≈ 1.22 growth left after the classed
  builder (`diagnostics/key-schedule-loop2-cost-drivers.md` §Re-measurement,
  item 4). That is the more valuable open question but it is a *diagnosis* task,
  not a refactor.
- **Not** changing what any example proves. Statements are frozen (G1).

## The design

One builder over `param_val`, granularity carried on the data list, classing by
default:

```coq
gen_contract_u (init_addr : N)
               (reg_specs  : list reg_spec_rel)
               (word_data  : list mem_spec_rel)   (* word-granular class  *)
               (byte_data  : list mem_spec_rel)   (* byte-granular class  *)
               (instrs) (extra_exit_offs) (bound) (ec) (fl)
```

**Granularity is carried by WHICH LIST an entry is in — there is deliberately no
`gran` field** (hence two data arguments, exactly as `gen_contract_rel_bytes`
already has). An earlier draft of this plan sketched an
`Inductive gran := GWord | GBytes` on the entries; that is the wrong shape here
and would reintroduce the width-index trap this project has hit three times
(`core-executor-internals` §6): a class's grouped existential width would then be
a function of a *filtered-and-projected* list rather than of a list you are
inducting on directly, which is exactly the configuration that only typechecks
with a dependent transport. Two homogeneous lists keep each class's width
computable from one list, the way `mem_class_width (mem_rel_keys L)` already is.

Only move to a per-entry granularity if a real example needs the two granularities
*interleaved* at one address range; none does today, and the trusted-surface
concatenation (`mem_specs ++ byte_mem_specs`, `GenContract.v:651`) already assumes
they are contiguous blocks.

The data block then partitions into at most **six** classes — `{word, bytes} ×
{pinned, public, private}` — each emitting one grouped existential, empty classes
emitting nothing (as `gen_mem_pub_class_ks nil = ⊤` already does).

Subsumption:

| today | becomes |
|---|---|
| `gen_contract_param` | `word_data = byte_data = []`, `None ↦ PVExist`, `Some v ↦ PVConst v`, `bound = 4·(length instrs)` |
| `gen_contract_rel_classed` | `byte_data = []` |
| `gen_contract_rel_bytes` | both lists, **and byte entries now classed** (the G3 win) |
| `gen_contract` | ~~deleted (0 users)~~ **KEPT** — 3 live users, incl. the concrete-base control arm (retraction, §Why) |
| `gen_contract_rel` | **KEPT — see below. Not dead.** |

## Stages

### Stage 0 — DONE 2026-08-18. Smaller again than "smaller than it first looked".

**Deleted, both bridges:** `gen_contract_noninterferent` (definition only; every
other mention was prose, and the `_param` bridge does not reuse it — it calls
`cfg_instrs_endToEnd_with_memory` directly) and
`gen_contract_noninterferent_rel_simple` (0 users anywhere outside `EndToEnd.v`,
including 0 across all 254 `ZZ*.v` rigs).

**NOT deleted: `gen_contract`.** It has live users — see the retraction in §Why.
No builder was deleted, so `GenContract.v` is byte-identical and stage 0 never
touched the example path at all: `Example/*.v` does not require `EndToEnd.v`
(`Prelude.v` stops at `GenContract.v`), so not one of the 16 `valid_*_param` VCs
was re-elaborated. That is also why the acceptance criterion this plan flags as
"most likely to be forgotten" — all 34 `ZZ*Common.v` rigs still compiling — is
satisfied *by construction* here rather than by testing: no builder signature
moved. It becomes a genuine risk at stage 2, which does change a builder.

Verified before editing: all 12 `Example/*Result.v` files use only the surviving
bridges (`_param`, `_param_simple`, `_rel_classed_simple`, `_rel_bytes_simple`) —
neither deleted bridge was reachable from any example.

**KEEP `gen_contract_rel` and `gen_contract_noninterferent_rel`.** This is a
correction to the first draft of this plan, which listed them as dead on the
strength of having no *committed example* users. They have **22 rig users**, and
those are not incidental: `gen_contract_rel` is the **unclassed control arm** for
every `|Σ|` measurement in
`diagnostics/key-schedule-loop2-cost-drivers.md` — `ZZKslChunkDistinctCommon.v`
and eleven sibling `ZZKsl*` rigs are built on it, and the whole classed result
(CD vs CLS) is stated as a ratio against it. Deleting it would not just break
rigs, it would make the win this plan is built on **unmeasurable**, and would
violate G4 directly. Dead-for-examples is not dead-for-experiments; check rig
users before calling any builder unused.

**Also keep `gen_mem_pre_rel`**: `gen_mem_pre_rel_classed` uses it for the pinned
group (`GenContract.v:530`).

**Also keep `gen_contract_noninterferent_param`** (the general, non-`_simple`
form): `Example/JumpsResult.v:60` uses it, because Jumps has extra exit offsets
so `_simple` does not apply.

Actual stage-0 reach: builders 5 → **5**, bridges 9 → **7**, `EndToEnd.v` −83 lines.

Acceptance: gate green, line counts recorded (see the table at the top); the rig
criterion is vacuous here for the reason given above.

### Stage 1 — `gen_contract_param` delegates. Low risk.

Redefine it in terms of the classed builder with the `option Val → param_val`
translation. The probe says the VC is unchanged for the register-only shape; all
nine users are that shape.

Acceptance: the 9 `valid_*_param` VCs close **with unmodified tactic lines** — if
any needs a tactic change, stop and report rather than editing the script, since
that would mean the delegation is not transparent after all.

### Stage 2 — DONE 2026-08-19. The payoff, larger than predicted.

Landed in four commits: `de708143` (definitions), `1ee11cfc` (Iris lemmas, moved
out of the gitignored harness into tracked `EndToEnd.v`), `4a67326c` (wiring —
`loop1` migrates automatically), plus the diagnostics write-up.

**The plan's expectation of "a new bv-slicing induction" was wrong in a useful
way.** No new slicing machinery was needed: the definition stacks the two
slicings that already existed (`bvtake`/`bvdrop` peels a cell off the group as in
`gen_mem_cells_class`; `term_word_byte` peels bytes off the cell as in
`gen_mem_asn_rel_bytes`), so the chunk inventory is unchanged and only the
variable count moves. On the proof side the per-cell obligation turned out to be
*exactly* the `PVExist` branch of the existing `gen_mem_asn_of_ptstomem_bytes`
minus its `iExists` — the classed witness is fixed by the group hypothesis rather
than supplied per entry — so that branch was factored out as an abstract-address
lemma (`ptstomem4_split_bytes`) and reused by both inductions.

**VC transparency held**: `Example/BearSSLCheckScalarLoop1.v` is untouched and its
VC closes with its unmodified tactic line.

Measured (G3): **1.10× / 1.32× / 1.77×** at 2 / 4 / 8 declared cells — the ratio
GROWS with cell count, so more than a constant factor, but the held-out fit fails
on both arms (−14% / −23%) so **no exponent law may be quoted**. The plan
predicted ~1.1× at 8 cells by extrapolating the WORD curve; that understates the
byte case, plausibly because each byte cell projects four chunks from the variable
where a word cell projects one (hypothesis, not measured).

Three traps, all found interactively in `ZZClassBridge.v` at ~200 ms rather than by
~2-minute `EndToEnd.v` builds — position mode works on that small file and OOMs
`pet` on `EndToEnd.v`, which is exactly why the plan says to develop there:
`bv.of_N_add` must be used BACKWARDS (it collapses a sum) while `bv.add_assoc`
goes FORWARDS; `get_word_byte2` takes the offset first unlike the `c` variants;
and byte 3's address arrives as `of_N 1 + (a + of_N 2)`.

#### original stage-2 text

New: a `gen_mem_cells_class`-analogue that emits four `ptstomem 1` chunks per key
via `term_word_byte` slices of the grouped variable, plus the matching
`ImplPre` lemmas (mirroring `gen_mem_cells_class_intro{,_sync}` and
`interp_mem_group_{pub,priv}`), then migrate loop1.

Expect this to be the bulk of the proof work — it is a new bv-slicing induction,
though `bv.take_app`/`bv.drop_app` should carry it exactly as they did for the
word case. Develop in `Example/ZZClassBridge.v`, not in `EndToEnd.v` (an
in-progress `Admitted` there fails the gate).

Acceptance: G3 measured; gate green; the check_scalar diagnostics re-run per G4.

### Stage 3 — OPTIONAL. Collapse to one builder and two bridges.

Fold `_classed` and `_bytes` into `gen_contract_u`, bridges 9 → 2.

**This is where nearly all the risk is, for purely structural benefit.**
Partitioning by `(gran × publicness)` genuinely reorders the heap for a *mixed*
data block, and `consume` is order-sensitive. The classed migration was painless
only because all four blocks were homogeneous, all-private `PVExist` — see
`PLAN-classed-existentials.md` §"Phase 4 turned out NOT to be the risky one",
which is explicit that the risk is real precisely for mixed blocks. All-or-nothing
behind a green gate; expect per-example debugging.

**Recommendation: stop after stage 2** unless the remaining duplication is
actively causing problems. Stages 0–1 already take bridges 9 → 6 and remove both
dead builders, and stage 2 delivers the only measurable win.

## Files

Generator: `GenContract.v`. Bridges: `EndToEnd.v`. Migrated examples: whichever
stage touches them (`Example/BearSSLCheckScalarLoop1.v` at stage 2). Development
harness: `Example/ZZClassBridge.v`. Feasibility probe (recreate as needed):
`Example/ZZUnifyProbe.v`. Cost measurement: the `Example/ZZVC*{Cls,Base}.v`
pattern.

## Traps carried forward from the classed work

- **`make -f Makefile.coq <file>.vo` is the authority for `EndToEnd.v`**, not
  `rocq_compile_file` — the latter reported success on a file `coqc` rejects and
  left a `.vo` without the new lemmas. Verify with
  `strings EndToEnd.vo | grep <newname>`.
- **`pet` OOMs replaying `EndToEnd.v` in position mode**; iterate against
  `Example/ZZClassBridge.v` (import block copied through line 94).
- **`μ1`/`μ2` are implicit in the `_class` ImplPre lemmas** and cannot be passed
  positionally *or* fully by name; positional-and-μ-free is the working form.
- In `EndToEnd.v`'s notation environment `rewrite A, B` and one-element
  `cbn [map]` are both **syntax errors**.
- A stale `ZZ*Common.vo` fails with *"makes inconsistent assumptions over
  library"* — rebuild the rig chain after any `Prelude`-closure change.
