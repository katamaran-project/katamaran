---
name: skill-usage-audit
description: >
  Retrospective sweep of THIS conversation (not historical transcript mining)
  for skill-usage problems: places a skill should have fired but didn't
  (silent miss), fired but was the wrong one or over-triggered (misfire), or
  where information was looked up by hand (Read/Grep/Bash/WebFetch on
  internal APIs, conventions, source) that logically belongs in a skill —
  either an existing skill missing that content, or a genuinely new skill
  that doesn't exist yet. Use when asked to "check if we used skills
  correctly", "audit this session/conversation for skill gaps", "did we look
  something up that should've been in a skill", "should skill X have fired
  here", or after a live correction like "the X skill should have triggered"
  once the immediate task is handled and it's worth asking why. Drives the
  fix, not just the diagnosis: routing problems get logged as eval entries
  and validated via **skill-routing-maintenance**; content gaps in an
  existing skill get a direct body/reference-file edit; a domain with no
  matching skill at all gets handed to **skill-creator** for first-draft
  authoring (never drafted here). NOT for fixing a single already-identified
  misfire/query in isolation (skill-routing-maintenance handles that directly
  without a full conversation sweep) and NOT for mining PAST sessions'
  transcripts (skill-routing-maintenance's mine_skill_fires.py does that).
---

# Skill usage audit

A retrospective on the conversation so far: did the skill system actually
help, or did work happen around it? This formalizes the review pattern from
the `key_schedule_loop2` session (2026-07-19) — asking "were all the skills
triggered when needed" turned up two real gaps (an unused `cfgver-gen-contract`
consult and a missing AST/register reference), which became eval entries, a
description edit, a new reference file, and cross-references between skills.

## Why this is a separate skill from skill-routing-maintenance

**skill-routing-maintenance** answers "does skill X fire for query Y" —
one query, one skill's description, a Haiku judge. It's the mechanism this
skill delegates to once a routing problem is *identified*.

**skill-usage-audit** answers the broader question: *looking back over what
just happened, where did the skill system fall short — in triggering OR in
content?* It reads the conversation itself (tool calls, what was searched,
what fired when), not a hypothetical query in isolation, and it also catches
a class of problem routing-maintenance doesn't: a skill whose description is
fine but whose *body* is missing something the conversation needed, or a gap
with no skill at all.

## Workflow

### 1. Scope the sweep

Default to the whole conversation so far. If the user points at a specific
stretch ("did we handle the part where..."), scope to that instead — no need
to re-litigate parts already reviewed in this session.

### 2. Look for three patterns

Walk the conversation's actual tool calls and turns, not just the final
output, looking for:

**a. Manual lookup that duplicates a skill's stated territory.** Any
`Read`/`Grep`/`Bash`/`WebFetch` used to reconstruct facts about an internal
API, convention, file layout, or behavior — for each one, check the *current*
name+description listing (same source of truth skill-routing-maintenance
uses) for a skill whose description already claims that territory. If one
exists and wasn't loaded, that's a silent miss even if the task still
succeeded — the lookup cost tokens and time a skill would have saved, and it
risks rediscovering something wrong that the skill would have gotten right.

**b. A skill never fired despite matching its own description.** Terse
follow-ups, requests bundled with a side task, or a live user correction
("the X skill should have triggered here") are the classic triggers this
project has already hit — check `eval_set.json`'s existing `silent-miss`
entries (Q46-49, Q56, Q58, etc. in `.claude/skill-evals/cfgver-routing/`) for
the shape of prior misses before assuming a new one is truly novel.

**c. A skill fired but was the wrong one, or fired outside its real
territory.** Less common than (a)/(b) in practice, but check especially
after a recent description edit — a broadened trigger phrase can start
stealing queries that belong elsewhere (this is why every description edit
gets a regression check, not just a hit check, on its near-neighbors).

### 3. Classify each finding before fixing anything

For each candidate from step 2, decide which bucket it's in — this
determines the fix, and picking the wrong bucket wastes a heavier tool on a
light problem or vice versa:

| Finding shape | Bucket | Fix |
|---|---|---|
| Skill exists, description already covers it, just wasn't invoked | pure routing / proactive-triggering | Log an eval entry (`kind: silent-miss`), no description change needed — the entry itself is the regression guard. |
| Skill exists, description is too narrow to have caught this | routing + content | Tighten the description (small, targeted clause — not a rewrite), then **must** run skill-routing-maintenance per the project's Maintenance protocol before considering it done. |
| Skill's domain matches, but the specific fact/convention isn't in its body or a `references/*.md` file | content gap, existing skill | Direct edit — add the missing content to the body, or a new reference file if it's rarely-needed detail (per the project's reference-file convention: zero listing cost, cataloged in the parent's body). No routing re-check needed unless the description also changed. |
| No skill's description plausibly covers this domain at all | missing skill | Do NOT draft it here. Hand off to **skill-creator** for the first-draft/interview step — this skill's job stops at "here's the gap and why it's not just an extension of an existing skill." |

### 4. Apply and validate

- Small, targeted fixes (an eval entry, a reference file, a body addition) —
  apply directly.
- Any description-field edit — apply, then invoke **skill-routing-maintenance**
  scoped to that skill's new/edited entries plus 1-2 near-neighbors (its own
  scoping guidance), never a full-sweep run for a single edit.
- A genuinely new skill — surface it to the user before invoking
  **skill-creator**; unlike a body edit or an eval entry, this is a standing
  addition to the project's skill family and worth a explicit go-ahead, not
  an assumed yes.
- Cross-reference both directions when two skills now point at the same
  gotcha (e.g. skill A's residual table gets a pointer to skill B's fuller
  explanation, and skill B gets a pointer back) — a one-directional link is
  half the fix.

### 5. Report

A short list, most-actionable first: what was found, which bucket, what was
done (or what's proposed and awaiting go-ahead). Don't pad it with a full
transcript replay — the user was there for the conversation; they need the
diagnosis and the fix, not a recap.

## What this is not

Not a substitute for noticing misfires live — `skill-routing-maintenance`'s
own description already asks for that proactively, "even without being asked
to check anything." This skill is the *systematic* pass for when a live catch
already happened once and it's worth asking "what else did we miss the same
way," or when the user wants a deliberate retrospective rather than relying
on catching things in the moment.
