---
name: skill-routing-maintenance
description: >
  Validates and tunes skill TRIGGERING — which skill (if any) fires for a
  given query — across this project's whole `.claude/skills/` family.
  Read-only, no live side effects: independent Haiku-model judges, one per
  query, shown ONLY the current name+description listing (never a skill's
  full body, never a live command file). Use when asked to "check routing",
  "check skill triggers", "did the right skill fire", tune or fix a skill's
  `description:` so it triggers correctly, log a misfire into the eval set,
  or re-validate routing after ANY skill description edit — a wording change
  to one skill can silently steal queries from, or stop competing with,
  another. Trigger PROACTIVELY right after changing any skill's
  `description:` field, and whenever a skill misfires (wrong skill fired) or
  silently fails to fire (the right skill never fired) is noticed in a live
  session — even without being asked to "check" anything. This is ALSO the
  right tool — not `skill-creator` — for "run an eval loop", "benchmark
  trigger accuracy", or "iterate on the description" whenever the skill in
  question ALREADY EXISTS: `skill-creator`'s own bundled description uses
  that exact same vocabulary, but only for a skill being drafted for the
  first time. The deciding question is always "does this skill already
  exist", never which words the request happens to use. NOT for drafting a
  brand-new skill from scratch or writing its first SKILL.md body (that's the
  `skill-creator` plugin, including ITS OWN first-draft test-prompt/
  triggering check — a new skill's initial eval loop stays inside
  `skill-creator`, not here). NOT for editing a skill's BODY content/
  instructions (ordinary editing, not a routing question). Do NOT reach for
  `skill-creator`'s `run_loop.py`/`run_eval.py` for this project's routing
  work — they write real temporary command files into the live
  `.claude/commands/` to make a candidate description "visible" for testing,
  and a background run that crashes before its own cleanup leaves that debris
  loaded into every future turn's context (happened 2026-07-18, burned a full
  session's token budget).
---

# Skill routing maintenance

This project has no separate "skill maintainer" tool to reach for — this
*is* it: a lightweight, homegrown, read-only method for answering "does this
skill fire when it should, and only when it should?" across the whole
`.claude/skills/` family (currently 26+ skills: the `cfgver-*` layers, the
generic pitfalls skills, the `rocq-*` wrapper skills). It lives in
`.claude/skill-evals/cfgver-routing/` despite the directory name — the eval
set covers routing for every project skill, not just CFGVer ones.

Distinct from **skill-creator** (the bundled plugin): that tool is for
*drafting a new skill from zero* — interview, first draft, first test
prompts. Once a skill exists and the question is "why didn't it fire" or "did
my edit break something else", this skill is the tool, not skill-creator's
`run_loop.py` (see the NOT-clause above and the incident it references —
that plugin makes a skill "visible" for isolated testing by writing live
files into `.claude/commands/`, which is unsafe to run unattended against a
real project directory).

## The three files

- **`eval_set.json`** — the ground truth: `{purpose, notes, evals: [{id,
  query, expected, kind}]}`. `expected` is the ONE correct winning skill name
  (or `"none"`) for that query. `kind` records why the query exists
  (`should-trigger`, `adversarial` — a deliberate near-miss against a
  competing skill, or a regression guard). `notes` is a running changelog:
  bump it with a short dated note every time you add entries, explaining what
  gap prompted them.
- **`results-<date>[-b/-c...].json`** — dated snapshots of judge-run
  outcomes. Never overwrite a prior dated file; append a new one (with a
  letter suffix for a same-day second run). This is the history of "routing
  was verified to look like X as of date Y" — useful for noticing when a
  skill's behavior drifted across unrelated edits.
- **`mine_skill_fires.py`** — mines this project's session transcripts for
  `(user message → skill fired)` pairs, for post-hoc review. Makes no API
  calls (mining is free), but shows an output-token estimate and asks
  confirmation before printing, since its output does cost tokens once read.
  It can only surface *over*-triggers (wrong skill fired) — a skill that
  should have fired but silently didn't is invisible to it; that half still
  needs a human noticing live, same as always.

## Workflow

**1. Capturing a misfire (live, or found via mining).** Write down the exact
query, the skill that actually fired (if any), and what should have fired
instead — then append a new entry to `eval_set.json`'s `evals` array with the
next `id`, the right `expected`, a `kind` explaining the scenario, and bump
`notes`. Do this *before* touching any skill's description — the eval entry
is what will prove whether your fix actually worked, and it's also what
future edits get regression-checked against.

**2. Validating.** Extract the current name+description listing for every
skill under `.claude/skills/` (one read pass over each `SKILL.md`'s
frontmatter — cheap, no tool needed beyond `Read`/`grep`). For each query
under test, spawn one Haiku judge (`Agent` tool, `model: "haiku"` or the
project's default judge model) whose ENTIRE input is that listing plus the
query, asked to name the single skill that should fire (or `"none"`) —
nothing else. This mirrors real triggering, which is decided on name+
description alone, never the body. Keep judges independent (one per query,
no shared context) so a wrong verdict on one query can't bias another.

Scope the run to what changed: a single description edit only needs the
handful of queries that plausibly compete for that skill's territory (the
new/edited entries plus 1-2 known near-neighbors as a regression check) — you
don't need to re-run all 49+ entries every time. A fuller sweep (the whole
eval set) is worth doing after a batch of changes, or periodically.

**3. Recording.** Write a new `results-<date>[-suffix].json` with each
query's verdict vs. `expected` and a pass/fail, plus a one-line `method` and
`note` explaining what prompted this run. Never overwrite an existing dated
file.

**4. If there's a real gap.** Tighten ONLY the specific skill's `description`
— add a clause covering the missed case, or a NOT-clause excluding the false
positive — rather than a broad rewrite. Small, targeted edits are easier to
regression-check and less likely to introduce a new competing false-positive
elsewhere. Re-run the directly affected query plus any near-neighbor queries
from step 2 to confirm no regression, then fold the result into a new dated
results file per step 3.

**5. Committing.** `eval_set.json`, the new `results-*.json`, and the edited
`SKILL.md` description(s) are ordinary git-tracked files — commit them
together so the eval entry and the fix it validates travel as one unit,
matching this project's usual "docs travel with the code change" convention.
