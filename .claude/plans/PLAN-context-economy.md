# PLAN-context-economy — keep long autonomous runs from ballooning context

Status 2026-11-03: Phase 0 DONE (`5b5abc52`, idle-resume guard). Phase 1 DONE
(`dc6b57c3`, telemetry hook). D11 handoff automation DONE (`/handoff` skill +
`handoff-announce.sh`, committed with this status). **Next: Phase 2 (agents).**

## Why (measured, October 2026 transcripts: 31 sessions, 6,536 requests)

- ~321M input-equivalent tokens (weights: cache read 0.1, write 1.25/2, output 5).
  **Cache reads = 72%**: the whole context is re-read on every request.
- Median request context **322k**, p90 646k, max 928k. 56% of cache-read volume
  comes from requests above 400k. Only 8 compactions in 31 sessions.
- Sessions are ONE task each (`/clear` between tasks works), but a task is a whole
  plan: 4–5 days, 500–800 requests. Growth happens in autonomous stretches
  (PLAN-spec-layer: 842k on 14 prompts), so reminders to the user do not reach it.
- Re-caching after >1 h idle: 37 events above 100k, **~10%** of cost; largest 901k.
- Subagents were CHEAP: 0.14–0.6M each vs ~10M per main session, 2% overall.
  Past blow-ups were tiny-task fan-outs (28 judges × 30k; run_loop), or one agent
  given a huge sweep (commit grouping, 336k context, 2.5M).
- Fixed start-up context ~63k. Project-controlled part (CLAUDE.md, MEMORY.md,
  skill listing) ~15–17k ≈ 3–4% of cost. Skill bodies are large
  (cfgver-executor 55k chars, cfgver-scaling-diagnostics 56k, core-executor-internals 39k).
- Tool output volume: file reading (sed/cat/Read) ~4.5M chars > rocq_check 1.9M chars.

## Decisions (Emiel, 2026-11-03)

- D1 Idle resume: block ONCE, explaining what continue / compact / clear cost and
  recommending one. **DONE** — `.claude/hooks/idle-resume-guard.sh` (+ 14 tests).
- D2 Growth: NOT reminders. A small-context **coordinator** (the session Emiel talks
  to) receives TERSE updates from a **worker** doing the iterating, and decides to
  stop it and restart fresh from a handoff, or let it compact.
- D3 One worker/session per PLAN PHASE, started from the plan's handoff section,
  which the worker keeps current at every milestone (so a restart is cheap anytime).
- D4 Delegate reading FROM THE FIRST TURN (not "above 200k" — the carrying cost is
  independent of current context size). Test: do I need the TEXT (about to edit it /
  code against exact definitions → read it myself, narrowly) or a CONCLUSION
  (→ reader agent returning conclusion + file:line + the few verbatim lines)?
- D5 Proof delegation is a GOOD fit (fixed statement = independent thread with a
  crisp oracle; goal dumps stay out of the coordinator). Contract: statement fixed,
  no `Admitted`/`Axiom`, attempt budget, returns a green-checked script OR a stuck
  report (goal at the stuck point, what was tried, what info is missing). Statement
  changes, new premises and design choices stay with the coordinator.
- D6 Codify as a NEW tier-1 skill (working name `session-economy`) + project agents,
  all via `skill-creator` (hook-enforced). Pointer from `phase-check`.
- D7 Skill slimming: separate, WITH Emiel, fresh session, `cfgver-executor` first:
  one line per section, Emiel marks keep / `references/` / archive.

- D8 Coordinator events: telemetry crossings 150k / 300k / 450k (the hook's
  default steps; 600k/750k may stay as backstops) + the worker's own one-line
  messages on STUCK and DONE. No per-milestone events.
- D9 The coordinator MAY stop a worker and restart it fresh from the handoff ANY
  time, without asking. Consequence for `phase-worker`: its handoff must be
  current at EVERY milestone (green build, commit), so a restart loses at most the
  work since the last milestone.
- D10 Workers run Opus, in the SAME working tree; one editing worker at a time;
  the coordinator does not edit.
- D11 Session changes are automated: `/handoff` (updates the plan's handoff,
  writes the one-line pointer `.claude/HANDOFF`, commits) → `/clear` → a
  SessionStart hook announces the pending handoff → user says "go".
  (Hooks cannot trigger `/clear` themselves.)

  **D11 result.** `.claude/skills/handoff/SKILL.md` (user-invoked only,
  `disable-model-invocation: true`, like `reading-quiz`; made via skill-creator,
  no trigger evals since it is never model-invoked) and
  `.claude/hooks/handoff-announce.sh` (SessionStart, source startup|clear only;
  11 offline tests). Pointer `.claude/HANDOFF` is gitignored. The usage script
  now lives at `.claude/tools/transcript-usage.py`.

## Established facts (checked 2026-11-03)

- Tools in-session: `TaskStop` stops a background agent; a background subagent can
  `SendMessage` to `"main"` mid-run; `SendMessage` reaches other local sessions;
  `Monitor` streams filtered lines of a status file as notifications.
- Hooks DO fire inside subagents: subagent transcripts contain PreToolUse and
  PostToolUse `hook_success` records, and one `hook_additional_context`.
- Docs agent claims, NOT yet verified: agent frontmatter `maxTurns` and
  `autoCompactWindow`; hook input in a subagent carries `agent_id`/`agent_type`;
  a `PreCompact` and a `SubagentStop` hook exist. Its "TaskStop / cross-session
  messaging not documented" contradicts the in-session tool descriptions — trust
  the tools.
- Real transcript records put `"message"` (with nested `"type"`s and `"usage"`)
  BEFORE the record's own `"type":"assistant"`: never grep for an ordered pair.
- Subagent transcripts: `<project>/<session>/subagents/agent-<id>.jsonl` (+ `.meta.json`).

## Phases

1. **Telemetry hook** (PostToolUse, all tools). Append one line per threshold
   crossing / error / stall to `$TMPDIR/claude-telemetry-<session>.log`:
   `ts agent ctx tool`. First check what `transcript_path`/`agent_id` a hook sees
   INSIDE a subagent (one trivial background agent, 2–3 tool calls). Never blocks;
   offline tests like `idle-resume-guard.test.sh`.
   **Phase 1 result (2026-11-03).** `.claude/hooks/context-telemetry.sh`, wired as
   PostToolUse matcher `*`, 13 offline tests (`context-telemetry.test.sh`), 0.02 s
   on a 16 MB transcript, prints nothing (zero context cost for the agent).
   - PROBED (temporary line in the already-registered rocq-error-injector, then
     reverted): inside a subagent the hook input has `agent_id`, `agent_type`,
     `prompt_id`, `scratchpad_dir`, `effort`; **`transcript_path` is the PARENT's**.
     The hook therefore reads `<dir>/<session_id>/subagents/agent-<agent_id>.jsonl`
     (verified on real data: the probe agent reported its own 19k, not the
     parent's 236k). `scratchpad_dir` is the session's, same for every agent.
   - Log: `<scratchpad>/telemetry/events.log`, one line per first crossing of
     150k/300k/450k/600k/750k (`CLAUDE_TELEMETRY_STEPS`), e.g.
     `… | phase-worker:abc1234 "Phase 2 of PLAN-x" | ctx 310k (crossed 300k) | calls 2 | Bash`.
     The main session is labelled `main` (the coordinator sees its own growth too).
   - Coordinator recipe: `Monitor` with
     `touch <scratchpad>/telemetry/events.log; tail -n0 -F <scratchpad>/telemetry/events.log`,
     `timeout_ms` max, re-arm on expiry.
   - NOT done, deliberately: stall events (a 30-min compile is normal silence)
     and error events (failed tools fire a different hook event — check it
     exists before relying on it).
   - Trap hit and fixed: `IFS=$'\t' read` COLLAPSES empty fields (tab is IFS
     whitespace), so a main-session call (no agent_id) shifted every field; use
     `\x1f`. Bash `TMPDIR` is unset in this environment — use `scratchpad_dir`.
   - Hook config is captured at session start: both hooks apply from the next
     session on. The probe worked mid-session only because a registered SCRIPT
     is re-read on every run.
2. **Agents** (`.claude/agents/`): `phase-worker` (executes one plan phase, keeps the
   handoff current, messages main in a fixed one-line format on milestone / stuck /
   done, budget), `rocq-prover` (D5 contract; knows preamble mode and the rocq-mcp
   false-green traps by pointer to `rocq-implementation`), `reader` (D4 return
   format; minimal tools to keep the start-up floor near Explore's 19k, not
   general-purpose's 53k). Verify `maxTurns`/`autoCompactWindow` with a trivial agent.
   Check whether `skill-path-guard.sh` recognises a skill loaded INSIDE a subagent
   (its marker is keyed by session id).
3. **Skill** `session-economy` via `skill-creator`; gate = named by the telemetry
   hook and idle guard when they fire, plus a pointer from `phase-check`. CLAUDE.md
   skill-map line → `skill-routing-maintenance` (scoped: ~6 queries).
4. **Trial** on one real plan phase. Measure coordinator context at the end and
   total weighted cost against a comparable October session
   (`.claude/tools/transcript-usage.py`; note transcripts older than ~30 days are
   gone, so compare against an October session soon).
5. **Skill slimming** (D7), its own session with Emiel.

## Open questions for Emiel

None open (answered 2026-11-03 as D8–D10).

## Risks

- Every handoff loses detail; worker mistakes come back confident → the
  coordinator re-checks with cheap oracles (compile + hole scan of the touched
  lemma), never by re-reading the worker's whole output.
- Comprehension debt can worsen: Emiel sees summaries, not the work. Design and
  statement changes stay in the coordinator, where Emiel is.
- Coordinator overhead: if events are not rare, the coordinator becomes the new
  long session.

## Handoff (for the next session)

Start line: **Execute PLAN-context-economy Phase 2**

Read: the status line, Decisions D8–D10 (they fix `phase-worker`'s message
format, stop rights, model and working tree), "Established facts", and Phase 2.
Nothing else is needed; the evidence behind the numbers is in the 2026-11-03
session.

Preconditions: the first session after 2026-11-03 must be a NEW `claude`
process (hooks were added that day; config is captured at session start). The
first live check of three hooks happens then: the announcer should have shown
this handoff; `telemetry/events.log` should appear in the scratchpad once the
session passes 150k.

Notes for Phase 2: agents are not skills, so no skill-creator consult (Phase 3
needs one). Still to verify there: frontmatter `maxTurns`/`autoCompactWindow`
(trivial agent), and whether `skill-path-guard.sh` accepts a skill loaded INSIDE
a subagent (its marker is keyed by session id; a subagent shares the parent's
session_id, per the Phase 1 probe). `phase-worker` must keep the Handoff section
current at every milestone (D9) and is the natural caller of the `/handoff`
steps — it cannot invoke the user-only skill, so give it the steps by pointer to
`.claude/skills/handoff/SKILL.md`. No open questions.
