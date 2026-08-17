---
name: rocq-implementation
description: >
  Entry point for WRITING, REPAIRING, or UNDERSTANDING an actual Rocq/Coq proof
  in this repo — the tactic-and-internals level, as opposed to deciding what to
  prove. Load this BEFORE the first attempt whenever you are about to hand-write
  a proof body, fix a tactic that just failed with a Coq error (lia "Cannot find
  witness", "Wrong bullet", rewrite/set "found no subterm", "No applicable
  tactic"), hit ANY Iris / separation-logic proof-mode failure (iApply, iExact,
  iFrame, iMod, iDestruct, iIntros; wands, separating conjunction, fancy
  updates, persistent-vs-spatial), pick tactics for a bitvector / gmap /
  relational (SyncVal-NonSyncVal) goal, add a peval or solver case, or iterate
  on a proof body at all. Load it EQUALLY for the reference questions that come
  up mid-proof: what a value or constructor sitting in your hypothesis actually
  denotes (e.g. `NonSyncVal vl vr`), what a core framework definition or
  combinator does, or WHERE a framework lemma lives and how it is proved — the
  material answering those is held in the tier-2 library skills this skill
  routes to, which are listed WITHOUT descriptions and are reachable only from
  here, so nothing else will surface them. Prefer loading this even for a proof
  that looks routine: the traps it routes to are ones you cannot recognise from
  the goal alone, and each has already cost this project multiple full compiles.
  NOT for choosing WHAT to verify or building a contract (cfgver-new-example,
  cfgver-contracts, cfgver-gen-contract), NOT for discharging a CFGVer
  verification condition (cfgver-solve-vc), NOT for why secret data collapses a
  VC to False (secret-data-walls), and NOT for a compile that is slow, hanging,
  or silently killed (rocq-timeout-triage, then rocq-compile-oom) — those are
  peers, not children, and should fire on their own.
---

# Writing and repairing Rocq proofs in this repo

This skill has two jobs: make you iterate on proof scripts at the right cost,
and hand you off to the skill that already documents the trap you are about to
hit. Both exist because the alternative has been measured, repeatedly, and it
is expensive.

## 1. Iterate with rocq-mcp, not with `coqc`

Always prefer rocq-mcp tools over spawning `coqc` manually. The gap is not
stylistic — it is roughly three orders of magnitude per iteration.

### The rule, stated as a checkable condition

> **Never run `coqc`/`make` on a file you just edited unless the immediately
> preceding action interactively verified the part you changed.**

This is the trigger condition, and it is here because "prefer rocq-mcp" was
not enough on its own. On 2026-08-16 a session used preamble mode correctly
for the hard part of a `Solver.v` lemma, then fell straight back to full
rebuilds for the *wiring* — six ~6-minute compiles to fix two tactic names
and a binder name. The failure mode is filing "verify the assembled file" as
a different activity from "iterate on a tactic", then sliding from the first
into the second. Both relapses happened at the wiring step, which feels like
plumbing rather than proving. It is not: a wrong binder name is a tactic
error like any other.

Before every build, ask the question literally: *did my last action check
this change interactively?* If no, there is almost always a shape question
you can extract and check in ~100 ms first (see the module-functor note
below). One confirming compile at the end is the sanctioned use; the second
consecutive one is the smell.

This is now enforced, not just advised: `.claude/hooks/coqc-guard.sh` denies
a build whose target's own source is newer than its `.vo` unless a
`rocq_check` / `rocq_start` / `rocq_step_multi` has happened since that
change. A prerequisite-only change does not trip it, so dependency rebuilds
are unaffected. If you hit that denial, do the interactive check — the
override exists but is the user's to set.

```
rocq_compile_file(file, mode="vos")               # fast type-check, statements only
rocq_compile_file(file, mode="full")              # validates proof bodies
rocq_compile_file(file, mode="full", keep_vo=True) # so downstream files can Require it
```

`vos` catches statement errors cheaply and does **not** check `Proof. … Qed.`,
so a green `vos` says nothing about whether your tactics work.

**Except when it does — and knowing which is worth real time.** `-vos` skips a
proof body UNLESS the enclosing section has section **variables** (`Context` /
`Variable`) whose usage must be read off the proof term, and no `Proof using`
annotation says otherwise. A bare `Section` is not enough. Verified both ways on
scratch files: an unsectioned `Lemma zz : 1 = 2. Proof. congruence. Qed.`
compiles clean under `-vos`; the same lemma inside
`Section S. Context (X : Type).` fails.

Practical consequence in this repo (measured 2026-08-01):

| where | section variables? | `vos` runs proofs? |
|---|---|---|
| `VerifierRel.v` `Section Soundness`, `Adequacy.v` | `Context {Σ} {GS}` | **yes** |
| `VerifierRel.v` `Section Shallow` / `Section Relational` | none | **no** |
| file top level (`Tables.v`) | n/a | **no** |
| inside a plain `Module` (`Spec.v`, `SpecIris.v`) | n/a | **no** |

So DO still treat a green `vos` as "statements only" when planning. But when a
`vos` sweep surprises you by reporting a *tactic* failure, that is not a bug —
it is a sectioned file — and conversely, do not conclude from a long run of
green `vos` sweeps that the proofs in `Section Relational` or in a `Module` have
been checked. They have not.

### Exception: `rocq_compile_file` cannot compile `theories/Symbolic/Solver.v`

It drops `_CoqProject`'s `-arg` lines, and this project passes `-arg "-w all"`.
Verified 2026-07-28 on a three-line probe: `#[export] Notation` is an **Error**
under bare `coqc` and a **Warning** under `coqc -w all` (Coq 8.20.1). So the
pre-existing `#[export] Notation dlist_secLeak` at `Solver.v:2230` fails as a hard
error, in **both** `vos` and `full` mode, with a message pointing at code you did
not touch:

```
Error: This command does not support this attribute: export.
[unsupported-attributes,parsing,default]
```

Build it with `make -f Makefile.coq theories/Symbolic/Solver.vo` instead — the
project's own path, and what the gate uses. Budget ~5m45s for that file. Suspect
this whenever `rocq_compile_file` reports an error on a line your diff never
went near; check `_CoqProject` for `-arg` before believing it.

### A `rocq_start(theorem=…)` timeout does NOT mean interactive mode is unavailable

This is the single most expensive misreading available here, so it is worth
knowing exactly why it happens. `rocq_start(theorem=X)` has to replay the whole
file prefix to reach `X`. In a large `theories/` file that replay alone exceeds
the 300 s `ROCQ_QUERY_TIMEOUT_CAP` (measured 2026-07-28: ~line 2380 of
`Symbolic/Solver.v`, twice). That is a property of **that one mode**, not of
rocq-mcp. Concluding "interactive is unavailable for this file" and falling back
to full compiles cost three ~5-minute compiles for two tactic errors that
preamble mode then found in 28 ms each.

### Preamble mode is the way out

```
rocq_start(preamble="From Katamaran Require Import …")
rocq_check(from_state=…, body="…")
```

Imports are content-hash-cached and stay warm across iterations, so each tactic
check costs ~30 ms. The catch is that a preamble carries no file context, so you
must restate your goal as a **standalone lemma**.

This is also the answer when pet runs out of memory rather than time: it OOMs on
very large files (the pre-split monolithic `CFGVer/Examples.v` needed >7.6 GB).
The 2026-07-17 split keeps CFGVer files small enough for interactive work, but if
a file grows heavy again, reach for preamble mode — **not** a `coqc` loop, which
is 100–1000× slower per iteration.

**"It's inside a module functor" is not an exemption.** Most of `theories/` lives
in functors (`SolverOn`, `SignatureMixin`, …), so a preamble genuinely cannot
`Require` the definitions — and a stale `.vo` makes requiring a case study's
instantiation fail on digest mismatch anyway. Rebuilding the chain to get a warm
instantiation costs ~15 min. But you usually do not need the real types: if the
failure is about **shape** — a tactic that will not apply, an evar that will not
resolve, a bullet or context problem — restate it over abstract parameters
(`Context (Formula : Type) (G : Formula -> PROP) …`) and the failure reproduces in
~100 ms. Worked example, plus the two `Persistent`/`BiAffine` side conditions you
must supply or you get spurious failures: **iris-proofmode**, "Debugging an IPM
failure inside a module functor". Measured 2026-07-28: this found in 100 ms what
two 5m45s blind compiles of `Solver.v` had failed to localise.

**A "does this stay transparent through the module boundary" question is ALSO a
shape question** — test it the same way, in a two-line throwaway snippet, before
ever blaming the real file. Worked incident (`Symbolic/Solver.v`,
`try_bvadd_cancel_spec`, 2026-08-07): a hypothesis obtained from a lemma whose
conclusion was `instpred (formula_secLeak t)` refused to reduce past that folded
form under `cbn`/`unfold instpred_formula_secLeak`, even though
`instpred_formula_secLeak t` is definitionally *exactly* that term one
`InstPred`-dispatch layer down. Four consecutive ~6-minute `make` recompiles of
the real file were burned narrowing this down — all of it avoidable, because the
actual question ("does `Module Type X := ConcreteModule` preserve
`Definition`-transparency for a functor parameterized over `X`?") has nothing to
do with Katamaran and reproduces in a preamble in under 100 ms:

```coq
Module Concrete. Definition foo (n : nat) : nat := n + 1. End Concrete.
Module Type Empty. End Empty.
Module Type Sig := Empty <+ Concrete.
Module Functor (Import X : Sig).
  Lemma test (n : nat) : foo n = n + 1. Proof. reflexivity. Qed. (* succeeds *)
End Functor.
```

It succeeds — the definition IS transparent generically. So the real bug wasn't
module opacity; it was that `cbn` (and plain `unfold`) sometimes will not fire
through a class-method-then-Fixpoint dispatch chain (`instpred`'s `InstPred`
projection, then `instpred_formula`'s match) even when the target is fully
convertible. `change OLD with NEW in H` (full conversion, not `cbn`'s
unfolding heuristics) does — same snippet, `change foo with (fun x => x + 1) in
H` closes it instantly, under a binder too. **Lesson: when `cbn`/`unfold`
stalls on something you can independently prove equal by `reflexivity`, reach for
`change ... with ... in H` instead of adding more `cbn`/`unfold` calls** — and
prototype the module-boundary question itself in a scratch snippet before
touching the real file, exactly like any other shape question.

To get the goal's exact shape without guessing it, temporarily replace the proof
body with:

```coq
match goal with |- ?G => idtac "ZZ:" G end. admit.
```

plus `Admitted.`, run `coqc` in the **background**, and kill it the moment `ZZ:`
appears — you only need the print, not the rest of the file. Port the verified
tactic back and pay exactly **one** full compile to confirm. (Dumping a goal or
a large term this way, and that one confirming compile, are the legitimate uses
of `coqc`.)

### Verify each `Qed.` actually landed

Nested `Proof`s are allowed in this codebase, which means a **missing `Qed.` does
not error**: the next `Lemma` silently opens a nested proof, and the lemma you
thought you finished never enters the environment. Check that the `feedback`
field says "X is defined" after every `Qed.` rather than assuming silence is
success.

Save the `state_id` from `rocq_start`. `ROCQ_MAX_STATES` is not raised here, so
sessions can expire; a `state not found` error means restart, not that anything
is broken.

### Reaching a lemma with `rocq_start` does not mean the lemma compiles

`rocq_start(theorem=X)` replays the file prefix **vos-style — proof bodies are
skipped**. So a successful `rocq_start` at a later position tells you the file
*parses and typechecks* up to there, and nothing whatsoever about whether the
proofs before it work. Only a `rocq_check` of an actual body, or a `mode="full"`
compile, runs a proof. Do not read "`rocq_start` got to line 900" as "everything
before line 900 is proved" — the file may be full of `Admitted`s and broken
tactics and it will still succeed.

### A rebuilt `.vo` is invisible until you restart pet

Coq will not reload a library already loaded into the process, and pet is a
long-lived process. So after you recompile a `.vo` that an open session has
already `Require`d, a lemma you just added to it is **not there**:

```
Locate cgc_binds_heap.   ->   No object of basename cgc_binds_heap
rewrite cgc_binds_heap.  ->   The reference ... was not found
```

…with a `.vo` on disk minutes *newer* than the source. This reads exactly like a
module-path or qualification bug, and you will go looking for one. Fix:
`rocq_start(…, force_restart=True)`. Rule of thumb: **edit → rebuild the `.vo` →
restart pet**, in that order, every time. (Measured 2026-07-31: cost more time
than the proof step it interrupted.)

Note `rocq_compile_file` now warns about this itself — "N interactive session(s)
in this workspace may be holding stale dependency state" — so treat that line as
an instruction, not noise.

## 2. Route to the skill that already knows the trap

The skills below are **tier 2**: they are listed without descriptions and do not
compete for the initial routing decision, so this table is how you reach them.
Load one when its trigger matches — including *before* your first attempt where
noted, since several of these traps are invisible in the goal statement and only
announce themselves as a confusing failure ten minutes later.

| Load | When |
|---|---|
| **bv-pitfalls** | Any bitvector goal. Load **proactively, before the first attempt** at a new `bv` inequality/monotonicity proof — not only after one fails. Covers `lia` choking on 2^32-sized literals (`bv.exp2 xlenbits`); `Cannot find witness` when the bound you need is *already in context* (`cbn` unfolds `bv.unsigned` in the goal to `Z.of_N (bv.bin a)` while `bv.unsigned_bounds` keeps it folded, so `lia` sees two unrelated atoms — fix with `unfold bv.unsigned in *`); a blanket `cbn` unfolding the width index `xlenbits` into unary Peano so bv-indexed lemmas stop matching syntactically (`cbn -[xlenbits]`); `bv.of_N_add`'s orientation (it *collapses* a sum of two `of_N`s, it does not expand one); and `bv.finite.elem_of_enum` (there is no `all_spec`). |
| **rocq-pitfalls** | A generic tactic error with no Katamaran flavour: bullet discipline ("Wrong bullet"), non-failure-atomic combos like `try (eapply L; eauto)` leaving stray goals, SSReflect `rewrite` syntax surprises, the goal-printing debug settings, open notations hijacking `+`/`-`/`*`/`=` so a plain `N`/`Z` goal type-errors against `Term` (fix with an explicit `%N`/`%Z`), and `injection H as ->` picking the wrong rewrite direction. |
| **iris-proofmode** | Separation-logic proof mode: `iApply`/`iExact`/`iFrame`/`iMod`/`iDestruct`/`iIntros` failures, wands and separating conjunction, fancy updates, persistent vs spatial hypotheses, `big_sepM`/`big_sepL`. |
| **relval-model** | `SyncVal` or `NonSyncVal` appears in your goal or definition and you need to know what it denotes — the relational value model and its homomorphic lifting. |
| **relval-rewrite-over-secrets** | **Before** proving any `peval` case, solver rule, or `Term` rewrite that could touch secret data. If both sides are pure terms the rewrite is automatically sound relationally with **no** `NonSyncVal` case analysis — worth knowing before you build one. |

Not a skill but the same reflex: **`references/peval-mask-algebra.md`** (in this
skill's directory) before adding a `peval` rule or a new `BinOp`/`UnOp`
constructor. It holds the branchless-mask canonical forms (`uop.expand`,
`bop.coalesce`) and, more importantly, the five-file plumbing table for a new
constructor plus the traps that make a `peval` rule silently do nothing.
| **core-executor-internals** | The generic `SPureSpec`/`SHeapSpec` monad and its refinement lemmas. Also the section on **how an `assert` is discharged against the path condition**: `solver_generic`'s three stages, `combined_solver`'s repeated passes, the `wpathcondition` world-extension quadratic, and the known `formula_simplifies` fact-burning bug. **AND the recipe for AUTHORING A NEW SOLVER RULE** — load it before your first edit to `Symbolic/Solver.v`: where to hook, why `Some error` for "cannot decide" is unsoundness, whether your rule needs a `secLeakT` guard, the `Equations` two-type-index refusal, and the iteration order that keeps you off ~6-minute rebuilds (prove the semantics in preamble mode over `Syntax.TypeDecl`; unit-test firing; one real `Qed`; then `gate.sh` at `GATE_JOBS=1`). |
| **cfgver-rsolve** | `rsolve` fails, hangs, dies in a `Qed`, or eats multiple GB; a `RefineCompat` instance is missing and must be written. |
| **cfgver-wp2** | `semWP2_unfold`/`semWP2_fix` and binary adequacy mechanics — an unreduced match after `rewrite semWP2_unfold`, `env.drop_cat` terms, an `iMod` that cannot eliminate an `inl`/`inr` modality. |
| **cfgver-gen-contract-internals** | Only when **modifying or extending the contract generator itself** (`gen_reg_asn`, `gen_pre`, `gen_implpre`, `declare_public_registers`). Merely *using* `gen_contract` is `cfgver-gen-contract`, tier 1. |
| **cfgver-endtoend-internals** | Only when **modifying the wiring lemmas themselves** (`cfg_instrs_endToEnd`, `cfg_instrs_verified`/`_safe`, the `_with_mem` variants). Merely *using* the wiring is `cfgver-endtoend`, tier 1. |

### These are tier 1 — do not wait for this skill

They keep their own descriptions and should fire on their own. If you are here
and one of them is what you actually need, go straight there:

- **cfgver** — the CFGVer hub, for multi-layer or unclear requests
- **cfgver-new-example** — verifying a new program end-to-end (the most common task)
- **cfgver-solve-vc** — discharging a VC: `vm_compute` + `solve_vc`, residuals, bare `False`
- **secret-data-walls** — why a VC over secret data collapses to `False`; the `NonSyncVal ⇒ False` boundary
- **gmap-pitfalls** — `gmap` lookups that will not reduce; stdpp's Zify rewrite breaking `lia`
- **rocq-timeout-triage** — anything running far past its own history, or an actual timeout
- **rocq-compile-oom** — a compile silently *killed* (`Terminated`/`Error 143`, no Coq error)

## Why this skill exists

Written 2026-07-28, after a full session ran start to finish with **zero** Skill
calls and re-derived by hand facts already documented in `bv-pitfalls` (the
`lia` atom-mismatch trap), `secret-data-walls` (`formula_relop` sends
`NonSyncVal` to `False`), `cfgver-solve-vc`, and `core-executor-internals` —
while also abandoning the always-loaded rocq-mcp workflow after one misread
timeout.

The diagnosis was not that any individual description was wrong. It was that
about ten child and library skills were all competing for the *same* initial
routing decision on overlapping symptom keywords, and none of them reliably won.
Tiering fixes that by giving the entry trigger to one skill and turning the rest
into a routing table.

So if you are tempted to "simplify" this by handing the tier-2 skills their
descriptions back: that is the arrangement this replaced, and it demonstrably
did not fire. The two halves are load-bearing together — the parent is only
useful because it routes, and the children are only findable because the parent
does.
