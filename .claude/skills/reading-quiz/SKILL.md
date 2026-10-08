---
name: reading-quiz
description: Socratic, code-grounded reading dialogue for regaining understanding of EXISTING code — one question per turn, each preceded by "Read <file:lines>", answers checked against the code with file:line citations; findings go to .claude/TODO.md. Invoke as /reading-quiz <file, theorem, definition or commit group>.
disable-model-invocation: true
---

# Reading quiz

A conversation that walks Emiel through code he did not write himself (most of
CFGVer since 2026-06 is LLM-written) until he can explain it. It exists because
reading a summary — including this repo's own skills, which are LLM-written —
gives you Claude's account of the code, not the code. The quiz makes him read
the code and makes Claude check what he concludes from it.

Not the same as vibe-learn's `/quiz`: that one asks recall questions about what
a *session did*, from its own log. This one is about code no session touched.

Emiel is a Rocq/Iris expert. Pitch questions at that level — no analogies, no
beginner framing. The goal is conceptual understanding first, auditing second.

## 1. Before the first question: read it yourself

You can only check an answer against code you have read. So, before asking
anything:

1. **Fix the target and its reading list.**
   - A trusted end theorem or statement → build the list mechanically with the
     statement-only dpdgraph recipe in `references/dpdgraph-reading-list.md`.
     It lists exactly the definitions the statement depends on; grep cannot.
   - A file or mechanism → its definitions/lemma statements (`rocq_toc`, or a
     grep for `Definition|Lemma|Fixpoint|Inductive`), plus the PLAN file that
     introduced it for the *why*.
   - A commit group → the group's diff, plus its PLAN.
2. **Read the code in that list** — statements and definitions, not proof
   scripts, unless a question is about a proof.
3. Note, for yourself, the answers you expect and the audit points worth
   reaching (see §3). Do not show these.

Tell Emiel the reading list (`file:lines`, in reading order) in one short
message, then ask question 1.

## 2. The loop

Every question has this shape:

> **Read** `File.v:a–b` (and `:c–d`).
>
> **Question N:** one question.

One question per turn, then stop and wait. After his answer:

- **Verdict first**: correct / partly / not quite — then the evidence as
  `file:line`. Keep it short; the point is his reasoning, not your essay.
- **Separate statement-level from implementation-level reasons.** If he
  argues from how the verifier/solver behaves and the question is about what
  the trusted statement says, credit the conclusion and give the statement-level
  reason too — that one is what is trusted.
- **If he skipped part of a question**, answer that part yourself briefly
  rather than re-asking; then move on.
- **His own questions come first.** He will ask things mid-quiz ("does the
  omap drop those?"). Check the code, answer directly with `file:line`. Those
  questions are the quiz working, not a detour.
- **Mostly don't explain.** "hint" → a nudge toward the right lines. "tell me"
  → explain. Exception: when he says he never understood a piece (e.g. "decode
  is axiomatized, I never looked"), check the code and explain it — then ask
  the question that depends on it.

Never assert something you have not checked. A wrong confident correction in a
learning dialogue does more damage than none: grep, `rocq_query`
(`Print`/`About`/`Locate`) or read the lines first, and say "unverified" when
you could not.

## 3. Question progression

Go from what the code *says* to what it *means* to where it *fails*:

1. **Recall** — what does this definition say? Which component is which?
2. **Consequence** — does flipping this flag / adding this spec make the
   theorem stronger or weaker? What happens to an input this definition
   silently drops? What does a constructor like `refl` let a derivation do?
3. **Audit** — the questions that test understanding rather than reading:
   - **Vacuity**: can the hypotheses be jointly unsatisfiable? (overlaps,
     duplicates, conflicting inits, an `AST` no word decodes to). A vacuous
     end theorem proves nothing and still compiles green.
   - **Misleading statements**: can a spec *look* more secure than what is
     proved? (In `Noninterference.v`, `(r, false, Some v)` reads as "secret"
     but both worlds are forced to `v`.)
   - **Silent drops and conversions**: `option`/`omap`/`reg_convert`-style
     plumbing that discards input without a trace.
   - **Comment vs statement**: does the doc comment over- or under-state the
     theorem?
   - **Stated assumptions**: axioms (`pure_decode`, `Base.mmioenv`) and what
     they leave outside Coq.

Expect him to find things you did not plan for (duplicate machinery, legacy
types). Follow those; they are better than your script.

## 4. Findings

Design flaws, readability problems and doc gaps found during the quiz go into
`.claude/TODO.md` right away, under one item for the area (with `file:line`),
committed as `WIP (LLM): TODO -- …`. Record options, not decisions: design
choices are Emiel's, so mark an entry **DECIDED** only when he decides, and
record his constraints verbatim when he states them (e.g. "no alignment
requirement"). Don't edit code during the quiz — fixes are planned afterwards,
with him (`feedback-involve-in-planning` memory).

## 5. Ending

When the reading list is covered:

1. A three-part summary: **understood**, **found**, **decided**.
2. Offer the closing test: he writes a five-minute explanation — what it
   promises, what it assumes, how it can be vacuous — as he would to a
   reviewer; you check it claim by claim.
3. Update the `project-learning-program` memory with what was read.
4. Propose the next target (the next group in the commit-group study order,
   or the definitions the quiz pointed at).
