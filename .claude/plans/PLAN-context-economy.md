# PLAN-context-economy — keep long autonomous runs from ballooning context

Status 2026-11-03: Phase 0 DONE (`5b5abc52`, idle-resume guard). Phase 1 DONE
(`dc6b57c3`, telemetry hook). D11 handoff automation DONE (`/handoff` skill +
`handoff-announce.sh`). Phase 2 DONE (three agents + per-agent skill markers;
live checks passed 2026-11-03: `maxTurns` works, `reader` starts at 22.9k,
per-agent marker live; `zz-probe` deleted). **Next: Phase 2b (runner).**

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

- D12 Claude restarts ITSELF during long solo work, by two mechanisms (Emiel,
  2026-11-03, "I want Claude to be able to do this himself"):
  (a) within a session: the coordinator restarts workers (Phase 2, D9);
  (b) across sessions: a phase-runner script chains headless `claude -p`
  sessions, one per phase, driven by `.claude/HANDOFF` (Phase 2b).
- D13 Runner stop rule: an OPEN QUESTION or DESIGN CHOICE in the handoff — and
  only that (red build, phase cap, token budget were offered and NOT chosen).
  Machine-readable form: `/handoff` writes a 4th pointer field
  `NEEDS-EMIEL: <question>`; the runner stops on it, the announcer shows it.
  No-progress guard (Emiel, 2026-11-03): ALLOW N RETRIES — the runner stops
  when the pointer line is unchanged after N consecutive runs. N not fixed by
  Emiel; default 2 unless he says otherwise.
- D14 Skill-load markers are PER AGENT (Emiel, 2026-11-03, on the Phase 2
  probe): a subagent's hook input carries the parent's `session_id`, so a skill
  the coordinator loaded would otherwise satisfy a worker that never loaded it.
  Each agent must load its own skills.

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
   **Phase 2 result so far (2026-11-03).**
   - Agents written: `.claude/agents/phase-worker.md` (Opus, all tools; ends
     with ONE line `DONE|STUCK | <PLAN> Phase <N> | <commit> | <clause>` — ending
     the run IS the D8 message, a STUCK worker is resumed by SendMessage with
     context intact; updates the plan per `handoff/SKILL.md` steps 2–4 at every
     milestone, step 5 only at DONE; never merges/pushes or decides design),
     `rocq-prover.md` (Opus, Read/Grep/Glob/Edit/Bash/Skill + rocq-mcp; D5
     contract, default budget 25 `rocq_check`s, PROVED/STUCK report, loads
     `rocq-implementation` first), `reader.md` (Sonnet — Claude's pick, not
     Emiel's; Read/Grep/Glob/Bash; `ANSWER / EVIDENCE path:line / NOT CHECKED`).
   - PROBED: **agent files are read at session start only** — a file written
     mid-session is "Agent type not found". Frontmatter therefore untested.
   - PROBED: **a subagent CAN start subagents** (general-purpose → nested
     general-purpose completed), so `phase-worker` starts `reader`/`rocq-prover`
     itself; the coordinator does not relay.
   - PROBED: a Skill loaded inside a subagent wrote its marker under the
     PARENT's session id → D14. Fix: the same 3-line snippet in
     `skill-load-marker.sh`, `skill-path-guard.sh`, `phase-check-guard.sh`,
     `git-workflow-guard.sh` appends `_<agent_id>` to the key when present; main
     session unchanged. `test-skill-agent-key.sh` 17/17 (real marker hook vs the
     three guards, both directions, id sanitising); existing suites 32+23+11
     still green. Live from the moment of the edit (scripts re-read per run).
   - **Live checks DONE (2026-11-03, new process).** (1) The Agent tool lists
     `phase-worker`, `rocq-prover`, `reader`, `zz-probe`. (2) `maxTurns: 2`
     WORKS: asked for 4 Bash calls, the probe stopped after 2 with "stopped at
     its 2-turn limit"; a stopped agent can be continued by SendMessage.
     `autoCompactWindow: 50000` raised no error but is UNVERIFIED (the probe
     never passed 28k); no real agent uses it, so nothing to drop. (3) `reader`
     (Sonnet) on "where is `skill-load-marker.sh` registered": correct
     ANSWER/EVIDENCE/NOT CHECKED report (settings.json PreToolUse, matcher
     `Skill`, nowhere else); start-up context **22.9k** (Explore 19k,
     general-purpose 53k), 4 requests, 25k tokens total. (4) Live per-agent
     marker: a subagent's `Skill` call wrote
     `/tmp/claude-skillload-gmap-pitfalls-<sid>_<agent_id>` and NO bare-`<sid>`
     marker — D14 holds live. (5) `zz-probe.md` deleted. Side finding:
     `transcript-usage.py` with no arguments finds 0 sessions and dies on a
     ZeroDivisionError (`line 110`) — guard it in Phase 2b, where it is the
     benchmark tool. Telemetry log: no line, as expected (nothing crossed 150k).
2b. **Phase runner** (D12b, D13). A script (e.g. `.claude/tools/phase-runner.sh`):
   read `.claude/HANDOFF` → stop if it carries `NEEDS-EMIEL:` (or is absent) →
   run ONE headless session with the start line, transcript/stream logged to a
   file → on exit, re-read the pointer and loop. Extend `/handoff` and
   `handoff-announce.sh` with the 4th field. To verify, not assume: how auto
   permission mode behaves under `claude -p`; that rocq-mcp and the project
   hooks load headless; how the user is told a run stopped (desktop
   notification?). **Benchmark ONE phase before chaining** (July 2026: an
   unmeasured `claude -p` fan-out drained the quota) — measure it with
   `transcript-usage.py`. Ask Emiel about the no-progress guard (D13) first.
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

Read: the status line, D8–D10 + D13–D14, "Established facts", and Phase 2
(its "result so far"). Then Phase 2b. Nothing else is needed.

Preconditions: a NEW `claude` process (the agents were added 2026-11-03; agent
files, like hooks, are captured at session start). `.claude/agents/zz-probe.md`
must still exist (untracked).

Phase 2 live checks, cheap, in this order — record each result in Phase 2:
1. The Agent tool lists `phase-worker`, `rocq-prover`, `reader`, `zz-probe`.
2. `zz-probe` asked for 4 single Bash calls: does `maxTurns: 2` cut it off?
   `autoCompactWindow` is only checkable indirectly — note whether the agent
   errors on it; if unverifiable cheaply, say so and drop it from the agents.
3. One `reader` run on a real question (e.g. "where is `skill-load-marker.sh`
   registered and on which matcher"): check the report shape, and its start-up
   context from `<scratchpad>/telemetry/events.log` or
   `.claude/tools/transcript-usage.py` on its subagent transcript (target:
   near Explore's 19k).
4. A live per-agent marker: a subagent loads a skill → the marker is
   `claude-skillload-<slug>-<sid>_<agent_id>` in /tmp.
5. Delete `zz-probe.md`. `phase-worker` and `rocq-prover` get their real test
   in Phase 4 (trial), not here.

Then Phase 2b (runner), with the no-progress guard = N retries (D13, default
N=2). Benchmark ONE headless run before chaining.
