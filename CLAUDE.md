# Katamaran — Claude Code Project Guide

Katamaran is a Rocq/Coq framework for formal security verification of RISC-V PMP programs.
The active development area is `case_study/RiscvPmp/CFGVer/`.

> **Detailed CFGVer reference lives in modular skills under `.claude/skills/`.**
> Start at the **`cfgver`** hub (routing map + importing idiom + example status),
> which routes to dependency-layered sub-skills that auto-load only when relevant:
> - **`cfgver-new-example`** — the 6-step recipe for verifying a new program (most common task)
> - **`cfgver-executor`** — symbolic executor `sexec_cfg_addr` + VC (gmap store)
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
>
> Standalone pitfall skills (generic, not CFGVer-specific): **`rocq-pitfalls`**
> (bullets, eauto atomicity, SSReflect rewrite, goal-print debugging),
> **`bv-pitfalls`**, **`gmap-pitfalls`**, **`iris-proofmode`**. Zero-cost
> references files live under `skills/cfgver/references/` (e.g. `registers.md`).

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
`Spec.v` → `Verifier.v` → {`Noninterference.v`, `Tables.v`} → `Contracts.v` →
`GenContract.v` → `Adequacy.v` → `EndToEnd.v` → `Example/*.v` (independent) →
`Results.v` (aggregator holding the concrete end-to-end theorems).
`Noninterference.v` + `Results.v` + the `*_instrs`/`*_specs` data blocks in
`Example/*.v` are the TRUSTED STATEMENT surface — diff these to know whether
what is being proved changed.

---

## rocq-mcp workflow

Always prefer rocq-mcp tools over spawning `coqc` manually.

`ROCQ_MAX_STATES` is **not** overridden — the server uses its default limit.
Consequence: interactive sessions (`rocq_start`) may expire if idle or if many
states accumulate. Always save the `state_id` from `rocq_start` and check for
`state not found` errors before assuming a session is still live; restart with
`rocq_start` if needed.

```
# 1. Fast type-check (skips proof bodies) — use first
rocq_compile_file(file, mode="vos")

# 2. Full compile — use to validate proofs
rocq_compile_file(file, mode="full")

# 3. Keep .vo so downstream files can Require it
rocq_compile_file(file, mode="full", keep_vo=True)

# 4. Interactive proof development
s = rocq_start(file=..., theorem="my_lemma")
s = rocq_check(from_state=s["state_id"], body="intros. iIntros ...")
```

**Dependency rule**: before compiling a CFGVer file, its Required CFGVer
dependencies need `.vo`s — compile them with `keep_vo=True` first (or build the
target's closure via `make -f Makefile.coq <file>.vo`) — otherwise `Cannot find
a physical path bound to …CFGVer.<Dep>`.

**VOS vs full**: use `vos` to catch statement errors cheaply; use `full` only when
the proof body matters. VOS does NOT check `Proof.…Qed.`.

**Tooling gotchas:**
- `rocq_start(theorem=X)` loads the file prefix vos-style — proof bodies SKIPPED.
  Only `rocq_check` of a body or a `mode=full` compile actually runs proofs; don't
  infer a lemma passed just because a later `rocq_start` reached it.
- Nested Proofs are allowed in this codebase: a missing `Qed.` does NOT error —
  the next `Lemma` silently opens a nested proof and the previous name never enters
  the environment. Verify the `feedback` field shows "X is defined" after every `Qed.`.
- pet (interactive rocq-mcp) OOMs on very large files (the pre-split monolithic
  `Examples.v` needed >7.6 GB). The 2026-07-17 split keeps CFGVer files small
  enough for interactive work; if a file grows heavy again, iterate via
  `rocq_compile_file` (coqc) or a truncated mirror file.

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
documents (docs travel with code); skills are git-tracked — review their diffs like
code; after changing any skill *description*, re-check routing against
`.claude/skill-evals/cfgver-routing/eval_set.json`; when a skill misfires or fails
to fire in a live session, log the query into that eval_set.json with the correct
expected winner before moving on (`.claude/skill-evals/mine_skill_fires.py` lists
recent user-message → skill-fired pairs for post-hoc review; silent non-fires it
cannot see); at the end of a working session, ask Claude to fold what was learned
back into the skills.

Previous Claude sessions: commits tagged `WIP (LLM):` are primarily LLM-generated.
