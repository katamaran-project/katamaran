# Katamaran — Claude Code Project Guide

Katamaran is a Rocq/Coq framework for formal security verification of RISC-V PMP programs.
The active development area is `case_study/RiscvPmp/CFGVer/`.

> **Detailed CFGVer reference lives in modular skills under `.claude/skills/`.**
> Start at the **`cfgver`** hub (routing map + importing idiom + example status),
> which routes to dependency-layered sub-skills that auto-load only when relevant:
> - **`cfgver-new-example`** — the 6-step recipe for verifying a new program (most common task)
> - **`cfgver-executor`** — symbolic executor `sexec_cfg_addr` + VC (gmap store)
> - **`core-executor-internals`** — the CORE generic `SPureSpec`/`SHeapSpec` monad
>   underneath every case study's own executor (not CFGVer-specific; library skill)
> - **`relval-model`** — the `SyncVal`/`NonSyncVal` relational value representation
>   (`RelVal = RV (Val σ)`, homomorphic lifting) (not CFGVer-specific; library skill)
> - **`pred-modalities`** — the `Pred`/world/modality layer under every refinement
>   proof: why a substitution runs BACKWARDS on valuations, the FIBRE of an
>   accessibility, and `assuming`/`knowing`/`forgetting` as the standard adjoint
>   triple (`knowing ⊣ forgetting ⊣ assuming`). Load it when a refinement
>   hypothesis looks strong but proves nothing — the usual cause is a modality
>   gone vacuous on an empty fibre, invisible in the goal (library skill)
> - **`relval-rewrite-over-secrets`** — why a pure `bv`/`Val`-identity rewrite is
>   auto-sound over secrets, no `NonSyncVal` case-split (library skill)
> - **`secret-data-walls`** — the three `NonSyncVal ⇒ False` walls (`formula_bool`/
>   `formula_relop`/`secLeak`), `term_eq` danger, prefer pure-`bv` forms (library skill)
> - **`cfgver-refinement`** — concrete mirror `cexec_cfg_addr` (what to mirror), `RefineCompat`, `rexec_cfg_addr`
> - **`cfgver-rsolve`** — driving/debugging the `rsolve` tactic (library skill)
> - **`cfgver-soundness`** — the soundness chain (VC → myWP2_loop → leakage)
> - **`cfgver-wp2`** — binary WP2 proof mechanics (`semWP2_unfold`; library skill)
> - **`cfgver-contracts`** — the `CFGVerifierContract` record + hand-written contracts
> - **`cfgver-gen-contract`** — the generator user guide (spec triples, 5 premises)
> - **`cfgver-gen-contract-internals`** — the generator machinery (`gen_implpre` etc.; library skill)
> - **`cfgver-solve-vc`** — VC discharge: residuals, `DebugCFGVerifierContract`, tight-fuel `False`
> - **`cfgver-endtoend`** — `cfg_instrs_endToEnd` wiring + `ImplPre` (register path)
> - **`cfgver-endtoend-internals`** — the wiring lemmas' proof bodies (library skill)
> - **`cfgver-memory`** — public-memory infra + data-memory end-to-end (`_with_mem` variants)
> - **`cfgver-scaling-diagnostics`** — running/writing up a cost-driver investigation
>   (`diagnostics/` convention, cost-driver catalog, one-axis-at-a-time ablation discipline)
>
> **Skill routing is TWO-TIERED (since 2026-07-28).** Eleven pitfall/library skills
> are set to `name-only` in `.claude/settings.json`'s `skillOverrides`: they are
> listed WITHOUT their description, so they no longer compete for the initial
> routing decision, and are reached from a tier-1 parent's routing table instead
> (still invokable by name). Rationale: a session made ZERO Skill calls because
> ~10 overlapping symptom-keyword descriptions all competed and none won.
> - **`rocq-implementation`** is the tier-1 entry point for WRITING, REPAIRING or
>   UNDERSTANDING an actual proof script — tactic errors, bv/gmap/Iris/relational
>   goals, adding a `peval`/solver case, plus "what does this value mean" and
>   "where does this lemma live". It carries the mandatory rocq-mcp preamble-mode
>   workflow and routes to the tier-2 set below.
> - **Tier-2 (`name-only`, reached via `rocq-implementation`):** `bv-pitfalls`,
>   `rocq-pitfalls`, `iris-proofmode`, `core-executor-internals`, `relval-model`,
>   `relval-rewrite-over-secrets`, `pred-modalities`, `cfgver-rsolve`, `cfgver-wp2`,
>   `cfgver-gen-contract-internals`, `cfgver-endtoend-internals`. Several are
>   labelled "library skill" in the list above; that label now also means
>   name-only. **Note `secret-data-walls` is labelled a library skill but is
>   deliberately TIER-1** — it keeps its description.
> - **Tier-1 peers that must fire on their own** (do NOT route them through the
>   parent): `cfgver` (hub), `cfgver-new-example`, `cfgver-solve-vc`,
>   `secret-data-walls`, `gmap-pitfalls`, and for a step running way longer than
>   expected **`rocq-timeout-triage`** (the general "figure out why before
>   waiting longer" entry point), which routes to **`rocq-compile-oom`** for the
>   silently-killed/OOM signature, and **`cfgver-scaling-diagnostics`** for
>   running/writing up a scaling-driver investigation as a durable record (the
>   fuller treatment of `rocq-timeout-triage`'s own one-factor-at-a-time step).
>
> Caveat measured the same day: `name-only` *de-weights* competition, it does not
> remove it — a bare NAME can still win on an exact jargon match (`iApply` →
> `iris-proofmode`). That is benign (it lands on the right child), but do not
> assume the tiering is airtight.
> Zero-cost references files live under `skills/cfgver/references/`
> (e.g. `registers.md`).
> Meta-skills for the skill system itself: **`skill-routing-maintenance`** —
> check/tune which skill fires for a query (read-only Haiku-judge eval, see
> Maintenance protocol below); **`skill-usage-audit`** — retrospective sweep
> of a whole conversation for silent misses, misfires, and content gaps,
> which then calls into `skill-routing-maintenance` (routing fixes) or
> `skill-creator` (a genuinely new skill). Distinct from drafting a
> brand-new skill from scratch (`skill-creator` plugin).

---

## Collaboration style

- **Report before acting.** Before any significant edit, proof attempt, or design
  decision, state in one sentence what I'm about to try and why — so the user can
  redirect before I commit.

- **Decision checkpoints.** When I hit a fork (e.g. "option A or B?"), stop and
  ask explicitly rather than pick one and run with it.

- **Surface intermediate findings.** During deep exploration, report what I've
  found every few steps rather than one large dump at the end.

- **Come back when stuck.** If I've been working on something for a while without
  clear progress, stop and report back — don't keep going silently. Say what I've
  tried, where I'm at, and ask how to proceed.

---

## Project layout

| Path | Logical name | Purpose |
|------|-------------|---------|
| `case_study/RiscvPmp/` | `Katamaran.RiscvPmp` | RISC-V PMP case study |
| `case_study/RiscvPmp/BlockVer/` | `…BlockVer` | Linear (block) verifier |
| `case_study/RiscvPmp/CFGVer/` | `…CFGVer` | CFG verifier (active work) |
| `theories/` | `Katamaran` | Core framework |

`_CoqProject` defines the `-Q` mappings and the exact compilation order.
CFGVer compilation order (post 2026-07-17 split of the old `Examples.v`):
`Spec.v` → `Verifier.v` → `Tables.v` → `Contracts.v` → `GenContract.v` → then two
independent branches — the LIGHT example branch `Example/Prelude.v` (shared
import preamble) → `Example/*.v`, and the HEAVY adequacy branch `SpecIris.v` →
`VerifierRel.v` → `TablesRel.v` → `Adequacy.v` → `EndToEnd.v` — rejoining at
`Example/<Prog>Result.v` (the per-program end-to-end theorems) →
`Results.v` (re-export shell, the merge gate's build target).
`Noninterference.v` + `Example/*Result.v` + the `*_instrs`/`*_specs` data blocks
in `Example/*.v` are the TRUSTED STATEMENT surface — diff these to know whether
what is being proved changed.
**Two layering invariants, each worth >1 GB or ~40 s and each easy to undo by
accident:** (1) the light files (`Spec`, `Verifier`, `Tables`, `Contracts`,
`GenContract`, `Example/*`) must stay free of Iris / `ShallowExecutor` /
`MicroSail.Soundness` requires — adding one puts ~1.2 GB back on all seven
examples; (2) `Example/Prelude.v` must stay free of `EndToEnd`, or the 85 s
`Adequacy`→`EndToEnd` chain serializes ahead of every example instead of
alongside them. Fuller detail (per-file skill pointers, the light/heavy split
table, the `Tables.v` `Open Scope list_scope` trap, the
`Require`-vs-`Require Import Verifier` landmine) lives in
`case_study/RiscvPmp/CFGVer/CLAUDE.md`, loaded automatically when touching
that subtree.

---

## rocq-mcp workflow

Always prefer rocq-mcp tools over spawning `coqc` manually — the gap is ~3 orders
of magnitude per iteration.

```
rocq_compile_file(file, mode="vos")                # fast type-check, STATEMENTS ONLY
rocq_compile_file(file, mode="full")               # validates proof bodies
rocq_compile_file(file, mode="full", keep_vo=True) # so downstream files can Require it
s = rocq_start(file=..., theorem="my_lemma")       # interactive
s = rocq_check(from_state=s["state_id"], body="intros. iIntros ...")
```

**Dependency rule**: before compiling a CFGVer file, its Required CFGVer
dependencies need `.vo`s — compile them with `keep_vo=True` first (or build the
target's closure via `make -f Makefile.coq <file>.vo`) — otherwise `Cannot find
a physical path bound to …CFGVer.<Dep>`.

> **The rocq-mcp gotchas live in the `rocq-implementation` skill, §1** — not
> here, so they stay in one place and can be as long as they need to be. It
> covers: why a green `vos` says nothing about your tactics; why
> `rocq_compile_file` cannot build `theories/Symbolic/Solver.v`; why a
> `rocq_start(theorem=…)` timeout does NOT mean interactive mode is unavailable,
> and preamble mode as the way out (including inside module functors, and when
> pet OOMs); why reaching a lemma with `rocq_start` does not mean it compiles;
> why a missing `Qed.` silently swallows a lemma instead of erroring; and why a
> rebuilt `.vo` is invisible to an open session until `force_restart=True`.
> Load it before hand-writing or repairing any proof body.

**rocq plugin commands (LLM4Rocq):** six have auto-trigger wrapper skills
(`rocq-golf`, `rocq-review`, `rocq-refactor`, `rocq-doctor`, `rocq-checkpoint`,
`rocq-formalize`). The rest are **suggest-only** — propose them at the right
moment, never run them uninvited: `/rocq:autoprove` and `/rocq:autoformalize`
(unbounded autonomous loops — need an explicit go-ahead PLUS a scope bound),
`/rocq:prove` (guided Admitted-filling session), `/rocq:draft` (statement
skeletons only), `/rocq:learn` (interactive tutorial).

---

## Pitfalls — where to look

The old symptom→fix table is dispersed into on-demand skills (verbatim archive of
every removed row: `.claude/archive/claude-md-prune-2026-07-16.md`):

- generic Rocq (bullets, eauto atomicity, SSReflect rewrite, print debugging) → **rocq-pitfalls**
- bitvector traps (lia vs 2^32, enum membership, cbn width unfolding) → **bv-pitfalls**
- stdpp gmap traps (unreducible lookup matches, Zify-vs-lia) → **gmap-pitfalls**
- Iris proof mode (iApply/iFrame/iMod lore, syntactic matching) → **iris-proofmode**
- layer-specific CFGVer gotchas → the matching **cfgver-\*** skill (see hub map)

---

## Maintenance protocol (CLAUDE.md + skills)

Keep `CLAUDE.md` lean — it loads every session. It holds only always-relevant facts;
everything else lives in the skills.

**Abstraction-level rule:** document each concept ONLY at the level where its
audience touches it (e.g. `secLeakvar` is assertion-level: it belongs to
hand-written contracts, not to the gen_contract spec-list guide). In user-facing
skills, lower-level mechanisms may appear only as a NOT-clause or a one-line
"under the hood" pointer; the mechanism itself goes in the `-internals` skill.

**Where a new piece of knowledge goes:**
- Symptom→fix → the matching pitfalls skill (`rocq-`/`bv-`/`gmap-pitfalls`,
  `iris-proofmode`) or the layer's `cfgver-*` skill. Generic Rocq content: check
  whether the `rocq` plugin already covers it before writing anything.
- New definition/lemma/pattern in one layer → the matching `cfgver-*` sub-skill
  (present tense, verified against the code, not from memory).
- Rarely-needed detail reachable from a parent → a `references/*.md` file under the
  parent skill (zero listing cost).
- Cross-layer workflow or recipe changes → the `cfgver` hub.
- Session-specific state / history → auto-memory files, never skills.
- Removed content → append verbatim to the dated archive under `.claude/archive/`.

**Hygiene rules:** update the skill in the SAME commit as the code change it
documents (docs travel with code) — concretely, before committing, grep the
skills for every lemma/definition/file name your commit renames, removes, or
moves and fix or delete the stale reference rather than leaving it for a
future session to trip over (a memory or skill naming something that no
longer exists is worse than one that says nothing); skills are git-tracked —
review their diffs like code; **any time you are about to `Write` a new
`.claude/skills/**/SKILL.md`, or `Edit` a skill's `description:` or the
skill-map at the top of this file, route through the meta-skills FIRST —
`skill-creator` to author/split a genuinely new skill, `skill-routing-
maintenance` to re-validate cross-family routing after any description/map
change — rather than hand-authoring or hand-editing skills ad-hoc (this
mechanical file-operation cue exists because a 2026-07-20 session created,
split, and re-described skills directly, bypassing both meta-skills);**
**this rule is now HOOK-ENFORCED, not advisory** — `.claude/hooks/skill-edit-
guard.sh` (a blocking `PreToolUse` hook) *denies* a `Write` of a new `SKILL.md`
without a `skill-creator` consult, and denies an `Edit` whose diff touches a
`description:` without a `skill-routing-maintenance` consult; skill *body* edits
stay ungated. If you hit that denial, do the consult rather than looking for a
way around it — the override (`CLAUDE_SKILL_GUARD_OFF=1`) is only settable in
the environment Claude Code was launched with, i.e. by the user, not from a
session. A sibling hook `.claude/hooks/agent-guard.sh` denies routing-judge
subagents that are not `subagent_type: routing-judge`, and denies more than 6
subagent spawns per 120 s (both added after a 2026-07-28 eval run cost ~850k
tokens). Note `git checkout .claude/settings.json` silently removes every hook
if that file is ever uncommitted.

**Skills do not reliably load unless a hook makes them load (2026-08-17).** Two
data points — the 2026-07-28 zero-Skill-calls session, and a 2026-08-17 session
that edited `Symbolic/Solver.v` without `core-executor-internals` *while the
skill was named in a routing table it had just read* — say advisory nudges are
decoration. `skill-nudge.sh` fired in the second case, was read, and changed
nothing. Three tiers of intervention now exist, and only the last two work:

- **advisory** — `skill-nudge.sh` (Read/Grep). Kept; assume it does nothing.
- **deny** — `.claude/hooks/skill-path-guard.sh` (PreToolUse Write|Edit), a
  TABLE of path → required-skill rules. Any `*.v` write requires
  `rocq-implementation`; on top of that each documented file demands its own
  skill (`Solver.v`/`Monads.v`/`SymbolicExecutor.v` →
  `core-executor-internals`; `Worlds.v`/`UnifLogic.v` → `pred-modalities`; `Verifier.v` → `cfgver-executor`; `VerifierRel.v` →
  `cfgver-refinement`; `Adequacy.v`/`SpecIris.v` → `cfgver-soundness`;
  `GenContract.v` → `cfgver-gen-contract-internals`; `EndToEnd.v` →
  `cfgver-endtoend-internals`; `Example/*Result.v` + `Noninterference.v` →
  `cfgver-endtoend`; other `Example/*.v` → `cfgver-new-example`;
  `diagnostics/*.md` → `cfgver-scaling-diagnostics`). **That mapping is
  transcribed from `CFGVer/CLAUDE.md`'s file table and is meant to track it** —
  if one changes, change both. `ZZ*.v` probes are exempt from the CFGVer rules
  but not the blanket one; `plans/*.md` is deliberately ungated (no skill
  governs "what we intend to build"). All missing skills are reported in ONE
  denial, and each fires at most once per session. Override:
  `CLAUDE_V_GUARD_OFF=1`.
- **deny** — `.claude/hooks/git-workflow-guard.sh` (PreToolUse Bash), now TWO
  mechanisms. (1) A **hard deny**: `main` is never a push or merge TARGET —
  `git push` naming `main`, `git push --all/--mirror`, a bare `git push` or any
  `git merge` while HEAD is `main`. This repo integrates on **`KatamaranRel`**;
  `main` is upstream and only read. Merging `main` INTO a topic branch, and
  pushing a topic branch, stay allowed. Not satisfiable by loading a skill;
  separate override `CLAUDE_ALLOW_MAIN=1` so that silencing (2) does not unlock
  it. Deliberately biased towards a false DENY (a branch named `<x>/main` reads
  as main) — the opposite bias from every other guard here, because a wrong
  allow is an irreversible write to a shared upstream. 23-case test suite.
  (2) The pre-existing skill gate: `git merge` / `git push` / `checkout -b` /
  `switch -c` require `branch-workflow`. Commit, status, log, diff and
  path-checkout are NOT gated (milestone commits are `rocq-checkpoint`'s
  business). Override: `CLAUDE_GIT_GUARD_OFF=1`.

  Both are backed by `skill-load-marker.sh` (PreToolUse Skill), which records
  every skill invocation as `$TMPDIR/claude-skillload-<slug>-<session-id>` —
  deliberately separate from `meta-skill-marker.sh`, which is load-bearing for
  `skill-edit-guard.sh` and would block all skill authoring if broken.
- **inject** — `.claude/hooks/rocq-error-injector.sh` (PostToolUse): names the
  right pitfalls skill when a known error string appears in tool output
  (`Cannot find witness` → bv- vs gmap-pitfalls, disambiguated by whether the
  file imports gmap; `Wrong bullet`/`found no subterm` → rocq-pitfalls; Iris
  tactic failures → iris-proofmode; `Terminated`/`Error 143` → rocq-compile-oom;
  `VerificationConditionWithErasure` → cfgver-solve-vc). **The strongest
  mechanism available**, because it needs no cooperation — the content arrives
  whether or not anyone thinks to ask. Prefer it for symptom-keyed skills, where
  the symptom is a deterministic string rather than a prose match.

**Consequence for authoring: a new skill needs a GATE decided at the same time
as its content.** When `skill-creator` drafts one, finish the job by answering
"what action, if taken without this skill, should be denied — or what tool-output
string should inject it?" A skill with neither should be assumed not to fire; the
wording of its blurb is the weakest of the three levers and, for a `name-only`
tier-2 skill, is not shown at all. `skill-creator` lives in the plugin cache
(`~/.claude/plugins/cache/…`), so this note lives here rather than in it —
editing a plugin would be overwritten on update and would leak into unrelated
projects. The corresponding "is this even a routing problem?" triage is in
**skill-routing-maintenance**, and the gate-vs-words classification in
**skill-usage-audit**.

Two traps when testing a Write/Edit hook: **`Edit` validates `old_string` BEFORE
`PreToolUse` runs**, so a deliberately-bogus-string "harmless test" never
reaches the hook and reads as "my hook is broken" (it is not) — use a real edit;
and a guard whose pattern matches text that merely *mentions* its trigger will
misfire — **four** instances in one day: a case-insensitive `Error:` grep
matching the printed lemma name `instpred_dlist_error:`; a `pgrep -f` wait loop
matching its own command line and so reporting a running build as finished; and
the rocq plugin's `guardrails.sh` twice blocking read-only commands because a
quoted string contained "restore" and later "git push". Match against the
specific field (`.tool_input.command`, not the whole payload) and anchor on the
token as a *command word* — `git-workflow-guard.sh` does this, and correctly
allows `echo 'remember to git push later'`.
after changing any skill *description* or
noticing a misfire/silent non-fire, use the **`skill-routing-maintenance`**
skill (read-only Haiku-judge
validation against `.claude/skill-evals/cfgver-routing/eval_set.json` — do
**not** reach for the `skill-creator` plugin's `run_loop.py`/`run_eval.py` for
this, which write real temporary command files into the live
`.claude/commands/` directory and left exactly that kind of debris loaded
into every turn's context after a crashed background run on 2026-07-18,
burning a full session's token budget; reach for `skill-creator` only when
drafting a genuinely *new* skill from scratch); at the end of a working
session, ask Claude to fold what was learned back into the skills.

Previous Claude sessions: commits tagged `WIP (LLM):` are primarily LLM-generated.
