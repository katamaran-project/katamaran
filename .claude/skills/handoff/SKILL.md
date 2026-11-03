---
name: handoff
description: End a plan phase cleanly so the next phase starts in a FRESH session with nothing lost — update the plan's status line and Handoff section, refresh the memory pointer, commit, write the one-line pointer .claude/HANDOFF (announced by the SessionStart hook after /clear), and tell the user to /clear and say "go". Invoke as /handoff [plan or phase, if not obvious].
disable-model-invocation: true
---

# Handoff — end a phase so the next session starts cold and loses nothing

Why this exists (PLAN-context-economy, 2026-11-03): token cost is dominated by
session LENGTH — 72% of October's cost was re-reading context, median request
322k. One session per plan phase fixes that, but only if switching is cheap and
loses nothing. The plan file is the carrier; this skill makes it current, and
`.claude/hooks/handoff-announce.sh` puts it in front of the next session.

The test for every step: **could a fresh session start the next phase from the
plan's status line + Handoff section alone, without asking anything?**

## Steps

1. **Identify** the plan, the phase just finished, and the next one — from the
   conversation and the plan's status line. If two plans are in play or it is
   unclear, ask one question; do not guess.

2. **Update the plan** (present tense, checked against the repo, not from memory):
   - **Status line**: phases done with commit hashes, and the next phase.
   - **The finished phase's result**, in place under that phase: what landed,
     facts established (especially ones that contradicted an assumption), traps
     hit and their fix, what was deliberately NOT done and why.
   - **Decisions** made this session, numbered like the plan's existing ones,
     with whose decision it was. Answered open questions move out of "Open
     questions".
   - **Handoff section**, rewritten, not appended to:
     - the start line, literally: `Execute <PLAN-name> Phase <N>`;
     - what to read — only the status line, this section, and anything it names;
     - preconditions (e.g. a build that must exist, a branch to be on);
     - open questions the next phase must ask before starting.
   Leave out conversation narrative and anything re-derivable: point to the
   diagnostics file or commit instead of restating numbers.

3. **Memory pointer**: if a `project_*` memory points at this plan, update its
   `description:` and its `MEMORY.md` line to the new status and next step.

4. **Commit** the plan together with any finished work: `WIP (LLM):` subject,
   Co-Authored-By trailer. Stage with `git add -u` plus the named new files —
   never `git add -A <dir>`, which sweeps in untracked ZZ probes — and check
   `git diff --cached --name-only | grep ZZ` is empty.

5. **Write the pointer** `.claude/HANDOFF` (gitignored, per machine), ONE line:
   ```
   <plan path from repo root> | Execute <PLAN-name> Phase <N> | <YYYY-MM-DD> <short commit>
   ```
   If the plan is now finished, delete `.claude/HANDOFF` instead, so no stale
   pointer gets announced.
   **If the next phase cannot start without Emiel's answer** (an open question
   or a design choice; PLAN-context-economy D13), append a 4th field:
   ```
   <plan path> | Execute <PLAN-name> Phase <N> | <YYYY-MM-DD> <short commit> | NEEDS-EMIEL: <the question>
   ```
   This field is the one thing that stops `.claude/tools/phase-runner.sh`.
   The announcer shows the question, and the next session asks it before
   starting. The question must also be written in the Handoff section, with
   enough context to be answered from there.

6. **Tell the user**, in three lines at most: what was recorded, the commit, and
   the next step — `/clear`, then reply **go**.
   **Exception:** if this session changed `.claude/settings.json` hooks, say to
   EXIT and relaunch `claude` instead. Hook configuration is captured when a
   session starts, so a `/clear` in the same process may not run the new hooks,
   including the announcer itself.

**Headless runs** (`phase-runner.sh`): this skill stays user-invoked. A
`phase-worker` instead reads this file and does steps 2–4 at every milestone,
and step 5 (pointer, incl. `NEEDS-EMIEL`) at DONE or at a question-STUCK. It
skips step 6, because nobody is there to read it.

## What the next session sees

On startup or `/clear`, the SessionStart hook shows "Pending handoff: Execute
<PLAN> Phase <N> … Reply "go"", and tells the model to read only the plan's
status line and Handoff section. Nothing else is needed from the user.
