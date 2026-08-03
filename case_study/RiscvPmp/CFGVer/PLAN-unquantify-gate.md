# PLAN — unquantify / dead-binder gate for the |wctx| scaling wall

**Status:** not started. Written 2026-07-29 for a Sonnet session to execute.
**Owner decision needed at the end of Phase A. Do not proceed to Phase B without it.**

---

## 0. Why this exists (read once, then skip)

The CFGVer loop scaling wall was root-caused on 2026-07-29 to the **live
logic-variable context `|wctx|`** — see the `project-key-schedule-loop-scaling`
memory note and `Example/ZZ-ARMS.md`. Two demonic variables per instruction step
are introduced and never eliminated:

- **`an`** — `Verifier.v:130`, `exec_instruction_prologue`:
  `asn.exist "an" ty_xlenbits (nextpc ↦ term_var "an")`.
- **`encoded_instr`** — `Spec.v:311`, the `fetch_instr` postcondition.

Katamaran `main` has a pass we do not have: **`unquantify`**
(`theories/Symbolic/Propositions.v:1929` on main, introduced in commit
`aaabac4a`, proofs finished in `b8cee590`/`6709bb58`/`ff772598`/`00c5d773`).
It rebuilds a `SymProp` bottom-up and **drops any `angelicv`/`demonicv` binder
whose bound variable does not occur in the body** (guarded by `ty.inhabit`).
Our `postprocess` has no such pass: `demonicv_prune`
(`theories/Symbolic/Propositions.v:1175`) drops a binder only when the body is
`block`, and `solve_uvars` eliminates demonic vars only by *substitution* from an
`assume_vareq`. A demonic binder with zero occurrences and no defining equation
is currently **never removed**.

Working hypothesis, worth testing because both variables now look
occurrence-dead:

- `an`'s only occurrence is the heap chunk `nextpc ↦ an`, which `step`
  overwrites. The epilogue's `"an"` is a *different* variable (the angelic `na`
  from `angelic None`, `Verifier.v:154`), and being angelic it is the one the
  solver eliminates.
- `encoded_instr`'s occurrences were: the `result_fetch = term_union …` equation
  (becomes a triangular substitution, discharged), the
  `encodes_instr(encoded_instr, i)` chunk (consumed by `sep_contract_decode`,
  `Spec.v:589`, and not re-produced), and `secLeak encoded_instr` — **which has
  just been deleted from the working tree** (this is exactly the `removal` arm
  in `ZZ-ARMS.md`).

If both are genuinely dead, per-trip `|wctx|` growth goes from ~29 to ~0 and only
the constant 6 contract-entry existentials remain — i.e. `|wctx|` flat in `N`
instead of linear.

### The objection this plan does NOT resolve, and must not pretend to

**Post-hoc `unquantify` will not speed up `vm_compute`.** The `|wctx|` cost is
paid at *introduction*: each `demonic` extends `w` to `w ▻ b` and weakens heap,
store and path condition through `sub_wk1 : Sub Σ (Σ▻b)`. Deleting the binder
from the finished tree refunds none of that. The actual fix, if this gate passes,
is a **forward world-GC** at each `sexec_cfg_addr` iteration (restrict the world
to the minimal context the current heap/store/wco mentions, continue there,
re-wrap with the dropped binders) — a real refactor of the monad's world
discipline, because shrinking the world breaks the monotone accessibility
threading.

**So this plan measures whether that refactor is worth doing. It does not do it,
and it will not make anything faster.** Any report claiming a speedup from this
work is wrong.

---

## 1. The gate criterion (the single number)

Count `demonicv` binders in the raw VC of the flat reproducer whose bound
variable has **no occurrence in the body**.

Calibration from `ZZ-ARMS.md`: the `WCTX` arm added 2 unconstrained
`asn.exist _ ⊤` per instruction step and moved the `demonicv` census counter
**629 → 741 at N=4, i.e. +112 = 2 × 56 steps** (14 instrs/trip × 4 trips). So in
this largely-linear tree each introduced variable contributes exactly one
`demonicv` node.

| dead-binder count at N=4 | reading | action |
|---|---|---|
| **~112 (−2/step, −28/trip)** | both `an` and `encoded_instr` dead | **GO** — Phase B, then propose the world-GC refactor |
| **~56 (−1/step)** | only one is dead | partial; use the names output to say which, then ask the owner |
| **< ~20** | neither is dead | **STOP** — the whole avenue is dead, report and close |

Also record the same at N=1 and N=2 and check it scales linearly (28 / 56 / 112).
A count that does *not* scale with N means the probe is measuring something
structural rather than per-step and must not be trusted.

---

## 2. Ground rules

- **Throwaway branch, never merged.** `git switch -c unquantify-gate`.
- **Phase A touches nothing under `theories/`.** That is the point — a `Base.v`
  edit invalidates the entire build.
- **All new files are `ZZ*`-prefixed, in `case_study/RiscvPmp/CFGVer/Example/`,
  and deliberately NOT added to `_CoqProject`** (run by direct `coqc`), matching
  the existing harness convention in commit `2dc85154`.
- **ONE heavy `Eval` per `coqc` process.** Several in one process contaminate
  each other badly (same computation measured 0.68/1.09/1.13 s at N=1 across
  runs; peak RSS 3.30 vs 5.35 GB). This is why `ZZRun1/2/4.v` are separate files.
- **Report intermediate findings** after Phase A step A.3 and after A.5 — do not
  run the whole plan silently.
- Commit with the `WIP (LLM):` prefix and the `Co-Authored-By: Claude Opus 5`
  trailer, per `CLAUDE.md`.

---

## Phase A — the cheap gate (no `theories/` changes)

**Goal:** answer §1 without porting anything. Expect ~1–2 h.

### A.1 — Clean the tree

The working tree currently has uncommitted changes to
`case_study/RiscvPmp/CFGVer/Spec.v` (the `secLeak encoded_instr` removal — this
IS the `removal` arm of `ZZ-ARMS.md`) and `Example/KeyScheduleLoop.v`.

```
git switch -c unquantify-gate
git add case_study/RiscvPmp/CFGVer/Spec.v case_study/RiscvPmp/CFGVer/Example/KeyScheduleLoop.v
git commit    # "WIP (LLM): drop secLeak encoded_instr from the fetch contract (removal arm)"
```

Sanity-check that removing this assumption has not broken verification. It is a
called contract's *postcondition*, so the caller **assumes** it — removing it is
sound but makes the VC strictly harder. Build one existing example end-to-end and
confirm it still discharges:

```
make -f Makefile.coq -j2 case_study/RiscvPmp/CFGVer/Example/Cmovznz4.vo
```

If it fails, **stop and report** — the rest of the plan is measuring a tree that
no longer verifies, and the owner needs to decide whether to keep the removal.

### A.2 — Rebuild the harness prerequisite

```
make -f Makefile.coq -j2 case_study/RiscvPmp/CFGVer/Example/Prelude.vo   # ~42 s
coqc $(cat _CoqProject | grep -- '-Q' | tr '\n' ' ') case_study/RiscvPmp/CFGVer/Example/ZZCommon.v
```

(Derive the exact `coqc` invocation from `_CoqProject`'s `-Q` lines; the ZZ files
are not in `_CoqProject` by design. If unsure, crib the flags from a `make`
invocation with `VERBOSE=1`.)

### A.3 — Write `ZZDead.v` (the probe)

New file `case_study/RiscvPmp/CFGVer/Example/ZZDead.v`, modelled directly on
`ZZNames.v` (same `From Katamaran Require Import
RiscvPmp.CFGVer.Example.ZZCommon.` header, same `cfg_map … CFG_VC_triple`
plumbing at the bottom).

It needs a **name-level occurrence collector**. Names, not de Bruijn indices, so
that every `Fixpoint` stays non-dependent and no `ctx.In` manipulation is needed
— this is the trick that makes `ZZNames.v` work and it is why Phase A is cheap.

Write, in this order:

1. `zz_tvars {Σ σ} (t : Term Σ σ) : list LVar` — collect `l` at every
   `term_var l σ`. **Our `Term` has an extra constructor vs `main`:
   `term_relval` (`theories/Syntax/Terms.v:64`). Treat it like `term_val` —
   contributes nothing.** `term_tuple`/`term_record` need `env` traversal; crib
   the shape from an existing `Env`-recursive function in `Terms.v`.
2. `zz_fvars {Σ} (F : Formula Σ) : list LVar` — over `Formula`. **Our `Formula`
   has two constructors `main` does not: `formula_propeq` and `formula_secLeak`
   (`theories/Syntax/Formulas.v:70-71`).** Both just recurse into their terms.
   `formula_prop` carries a `Sub Σ' Σ` — traverse it as an `Env` of terms.
3. `zz_cvars {Σ} (c : Chunk Σ) : list LVar` — over `Chunk` (4 constructors,
   identical to `main`).
4. `zz_mvars {Σ} (m : AMessage Σ) : list LVar` — **the subtle one, see A.4.**
5. `zz_svars {Σ} (s : 𝕊 Σ) : list LVar` — over `𝕊`, unioning the above at
   `assertk`/`assumek`/`assert_vareq`/`assume_vareq`/`error`/`debug`. Copy the
   constructor list verbatim from `ZZNames.v`'s `zz_dnames`: **our `𝕊` has 11
   constructors — `pattern_match`/`pattern_match_var` are commented out at
   `theories/Symbolic/Propositions.v:157-159`** (this is a real divergence from
   `main` and it works in our favour; see B.4).
6. `zz_dead (n : nat) : list LVar` — the answer: the multiset of `demonicv`
   binder names that do **not** appear in `zz_svars` of the whole tree.

Return `list LVar` (not a count) so the names are visible; also emit
`List.length` for the headline number.

**Soundness direction of the name-level approximation.** Names are not uniquely
freshened here — `ZZNames.v` already established this, since it found bare `an`
and `encoded_instr` rather than `an0`, `an1`, …. So a name that occurs *anywhere*
will mask *all* binders of that name. That means the probe **under-reports** dead
binders: it can only say "at least this many are dead". That is the conservative
direction for a GO decision, so a positive result is trustworthy. **A negative
result is not conclusive** — if `zz_dead` comes back near zero, do not close the
avenue on that alone; escalate to the index-level check in Phase B before
declaring the hypothesis dead.

### A.4 — Run it BOTH ways (this is not optional)

`assertk` carries an `AMessage`, and our messages carry `msg_heap` and
`msg_pathcondition` (`theories/Symbolic/Propositions.v:85-93`). The heap holds
`nextpc ↦ an`. `unquantify` on `main` **does** count message payloads as
occurrences — that is precisely why commit `aaabac4a` added `GenOccursCheck`
instances for every Debug record in `Monads.v` and `SymbolicExecutor.v`.

So produce two numbers:

- **(a) messages counted** — `zz_mvars` traverses `msg_heap`/`msg_pathcondition`.
  This is what `unquantify` would actually see.
- **(b) messages ignored** — `zz_mvars _ := nil`. This is what matters after
  `erase_symprop'` discards messages before `safeE`.

If **(b) ≫ (a)**, that is an informative and *encouraging* result, not a
failure: the binders are dead in the part of the tree that survives to `safeE`,
and the fix must erase messages before (or during) the elimination. Say so
explicitly in the report rather than reading (a) as a refutation.

### A.5 — Measure

One `Eval` per process, per the ground rules. Create `ZZDeadRun1.v`,
`ZZDeadRun2.v`, `ZZDeadRun4.v` mirroring `ZZRun1/2/4.v` (3 lines each), for each
of variants (a) and (b) — or gate the variant behind a definition in `ZZDead.v`
and rebuild between runs, whichever is less error-prone.

Record, in a table: N, variant, `zz_dead` length, the distinct names in it, and
the baseline `nc_demonicv` from `zzn_raw_nc` (expected 629 at N=4).

**Report to the owner here** with the table and the §1 verdict. Stop if STOP.

---

## Phase B — precise index-level confirmation (only on GO)

**Goal:** confirm A's name-level lower bound with the real thing, and get a
directly comparable `demonicv` census delta. Expect ~half a day. **Definitions
only — see B.3.**

### B.1 — Port `GenOccursCheck.v`

Take the **final state from `main`**, not from `aaabac4a` (four follow-up commits
fixed the proofs):

```
git show main:theories/Symbolic/GenOccursCheck.v > theories/Symbolic/GenOccursCheck.v
```

Add to `_CoqProject` immediately after `theories/Symbolic/OccursCheck.v`
(mirrors `main:_CoqProject:91`).

Wire into `theories/Base.v`, a two-line edit mirroring `main`:
- line 60 area: add `Symbolic.GenOccursCheck` to the `Require` list, next to
  `Symbolic.OccursCheck`
- line 67: `OccursCheckOn TY <+ InstantiationOn TY <+`
  → `OccursCheckOn TY <+ GenOccursCheckOn TY <+ InstantiationOn TY <+`

**This invalidates the entire build** (`Base.v` is near the bottom of the
layering). Budget a full rebuild up to `Example/Prelude.vo`; bound `-j` by RAM
(~3.6 GB/process floor — see the `project-compile-cost` memory note).

**Compile `GenOccursCheck.v` alone first** (`rocq_compile_file(mode="vos")`, then
`mode="full", keep_vo=True`) before touching anything else. If it does not go
through in ~1 h of fixing, stop and report — the divergence is worse than
estimated and the owner should re-scope.

### B.2 — Known divergences requiring new match arms

`main` and `bearssl-breaking-bad` forked at `a163bb7a`; `main` has 56 commits
touching `theories/` since, and our branch changed ~10.8k lines there. These are
the ones that will actually bite:

| what | where | fix |
|---|---|---|
| `term_relval` (we have it, `main` does not) | `theories/Syntax/Terms.v:64` | add a case to `substSU_term` and to the `Term` `gen_occurs_check` instance; treat exactly like `term_val` (carries no logic vars) |
| `formula_propeq`, `formula_secLeak` (we have them, `main` does not) | `theories/Syntax/Formulas.v:70-71` | add two arms to `GenOccursCheckFormula` (`main:theories/Syntax/Formulas.v:256-263`); shape them like the `formula_relop` / `formula_bool` arms |
| `formula_prop` is over `abstract_named RelVal`, `main` has `abstract_named Val` | `theories/Syntax/Formulas.v:64` | type-level only; the `gen_occurs_check` arm does not inspect the predicate |
| `Chunk` | — | **identical** (4 constructors), port as-is |
| `pattern_match` / `pattern_match_var` in `𝕊` | `theories/Symbolic/Propositions.v:157-159`, commented out in ours | **delete those two arms** from `to_uqSymProp`; see B.4 |

Also port the supporting `GenOccursCheck` instances the commit added to
`theories/Syntax/{Chunks,Formulas,Messages}.v` and
`theories/Symbolic/OccursCheck.v` (+20/+25/+31/+3 lines respectively in
`aaabac4a`).

### B.3 — Port `unquantify` — DEFINITIONS ONLY

Port the `UQSymProp` block, the `uq_*` smart constructors, `to_uqSymProp` and
`unquantify` from `main:theories/Symbolic/Propositions.v` (~lines 1750–2210) into
ours. Our `Propositions.v` has diverged ~951 lines, so this will not apply as a
patch — port by hand.

**Skip or `Admitted` every soundness lemma, including `unquantify_sound`.** This
is a *measurement*, not a verification: we only ever count nodes, never rely on
the result being equivalent. This is what keeps Phase B to half a day instead of
days. The branch is throwaway and must never be merged — state that in the commit
message.

The `Program Definition`s (`uq_angelicv`, `uq_demonicv`, `uq_assertk`,
`uq_debug`) carry obligations that are genuine proofs; if they resist, discharge
with `Admitted` via `Admit Obligations` rather than fighting them.

### B.4 — Note on `pattern_match`

`main`'s `to_uqSymProp` maps `pattern_match`/`pattern_match_var` to `uq_block`,
which looks unsound in isolation (`block` is `True`). It is moot for us: those
constructors are commented out in our `𝕊`, so the arms simply get deleted. Do
not port them, and do not spend time on the apparent unsoundness.

### B.5 — Measure

Add to `ZZCommon.v` (or a new `ZZUnq.v`):

```coq
Definition zzn_unq_nc (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (unquantify (CFG_VC_triple p exits P i fl))).
```

Plus a `postprocess`-first variant mirroring `main`'s
`postprocess_unquantify P := unquantify (postprocess P)`, since that is the
composition `main` actually uses.

New `ZZUnqRun1/2/4.v`, one `Eval` each. Compare `nc_demonicv` against the
baseline `zzn_raw_nc` (629 at N=4).

**Controls — check these before believing the number.** Every other counter
(`nc_angbin`, `nc_dembin`, `nc_assertk`, `nc_assumek`, `nc_asserteq`,
`nc_assumeeq`, `nc_error`, `nc_block`) should be **unchanged**. `unquantify` only
drops binders; if any other counter moves, the tree was truncated and the
`demonicv` delta is meaningless. This control is what distinguished the clean
`WCTX` arm from the confounded `PADDED` arm in the original experiment — do not
skip it.

Note `00c5d773`'s warning: *"unquantify explodes with compute, not with
vm_compute"*. We use `vm_compute` throughout, so this is fine — but never switch
these probes to `cbv`/`compute`.

---

## Phase C — report and decide

Write up, for the owner:

1. The dead-binder table (N=1/2/4, variants (a) and (b), names).
2. The Phase B `demonicv` census delta with its controls.
3. Whether the §1 gate passed, failed, or was partial.
4. **If GO:** a scoped proposal for the forward world-GC in `sexec_cfg_addr` —
   one `gen_occurs_check` pass over (heap, store, wco) per instruction step,
   using `meetSU` to combine the three minimal contexts (the pattern Dominique
   wrote out five times for the Debug records in `aaabac4a`'s `Monads.v` /
   `SymbolicExecutor.v` hunks). Flag the hard part honestly: shrinking the world
   mid-execution breaks the monad's monotone accessibility threading, so this is
   a refactor of the world discipline, not a drop-in.
5. Fold the result into the `project-key-schedule-loop-scaling` memory note and
   `Example/ZZ-ARMS.md` as a fifth arm.

Do **not** claim a speedup. Phase A and Phase B produce node counts only.

---

## Abort conditions

Stop and report, rather than pushing on, if any of these hit:

- A.1's `Cmovznz4.vo` build fails (the `secLeak` removal broke verification).
- `zz_dead` does not scale roughly linearly in N (probe is measuring the wrong
  thing).
- Phase B's `GenOccursCheck.v` does not compile after ~1 h of divergence-fixing.
- Phase B's controls show any non-`demonicv` counter moving.
- Any single `Eval` exceeds ~10 min at N=4 — check `rocq-timeout-triage` before
  waiting longer.
