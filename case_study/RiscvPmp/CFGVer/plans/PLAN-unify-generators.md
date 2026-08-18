# PLAN-unify-generators — collapse the contract-generator family

Status: **NOT STARTED. Written 2026-08-18 after the classed-existential work
(`PLAN-classed-existentials.md`) added a fifth contract builder and a ninth
noninterference bridge.** Stage 0 is free; stages 1–2 are de-risked by a probe
that already ran; stage 3 is deliberately optional and carries almost all of the
risk.

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

1. `gen_contract` dropped to **zero users** — including its bridge
   `gen_contract_noninterferent`, whose only two remaining mentions are prose in
   comments.
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
| contract builders | 5 | **2** — the unified one plus `gen_contract_rel`, retained as the unclassed measurement control |
| data/reg block builders | 7 | ≤ 4 |
| noninterference bridges | 9 | **2** (`_u` + `_u_simple`) |

Stage-0-only targets (achievable with zero risk): builders 5 → **4**, bridges
9 → 7, `EndToEnd.v` ≤ 1880. (`gen_contract_rel` stays — it is a measurement
control, see stage 0.)

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
| `gen_contract` | deleted (0 users) |
| `gen_contract_rel` | **KEPT — see below. Not dead.** |

## Stages

### Stage 0 — delete the genuinely dead. No risk. Smaller than it first looked.

**Delete:** `gen_contract` (0 users) and `gen_contract_noninterferent` (its only
two remaining mentions are prose in comments — checked), plus
`gen_contract_noninterferent_rel_simple` (0 users anywhere outside `EndToEnd.v`,
including 0 across all 254 `ZZ*.v` rigs).

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

Revised stage-0 reach: builders 5 → 4, bridges 9 → 7.

Acceptance: gate green, all 34 `ZZ*Common.v` rigs compile, line counts recorded.

### Stage 1 — `gen_contract_param` delegates. Low risk.

Redefine it in terms of the classed builder with the `option Val → param_val`
translation. The probe says the VC is unchanged for the register-only shape; all
nine users are that shape.

Acceptance: the 9 `valid_*_param` VCs close **with unmodified tactic lines** — if
any needs a tactic change, stop and report rather than editing the script, since
that would mean the delegation is not transparent after all.

### Stage 2 — byte-granular classed block. The payoff.

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
