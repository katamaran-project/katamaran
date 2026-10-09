# PLAN: a readable spec layer for `noninterferent_strong`

Status: rev 2 (2026-10-08), Phase S DONE, Phase 0 next. Based on `KatamaranRel` (D8);
every `file:line` below was re-checked there on 2026-10-08. Written from two
`/reading-quiz` sessions (`Noninterference.v`; the spec front-ends) whose
findings are in `.claude/TODO.md` (Priority 0 and the A–G list). Phase 0
(design, led by Emiel) runs before anything is implemented: §2 says what is
decided and what is open.

**This plan has two goals of equal weight**: the refactor, and Emiel learning
to use the learning tools installed on 2026-10-08 — VibeWise, vibe-learn,
while-you-wait — plus the repo's own `/reading-quiz`. Every phase in §3 has a
**Learning** block: the exercise, what to watch for, and how we know it
landed. §5 is the tool reference; §6 the end-of-plan review.

## 0. Goal

The trusted statement must be **easy to read and hard to misread**. Today a
reader of a Result file has to see through three problems:

1. **Misleading specs.** Every spec carries a `pub : bool` AND an optional
   initial value. `(r, false, Some v)` reads as "r is secret" but is public:
   `noninterferent_strong` forces both worlds to `v`
   (`Noninterference.v:272–273`). Live instance: cmovznz4's pointer registers
   A1–A3 (`Example/Cmovznz4.v:179–183`, `PVBaseOff 116/132/148`, flagged
   `false`). The `(bool, value)` pair exists in all four spec front-ends.
2. **Conversion plumbing.** Registers go `RegIdx` → `reg_convert`
   (`Base.v:1019`) → `existT` into `{x : Ty & Reg x}` (`gen_public_regs`,
   `Noninterference.v:109`) → unpacked in `declare_public_registers`
   (`:250`); `reg_convert 00000 = None` drops `X0` silently. Memory keeps a
   legacy `mem_spec` (`:140`) beside `mem_full_spec` (`:95`); `get_word`
   (`:133`) and `mem_has_word` (`:118`) do one job. On the front-end side,
   `concretize_data` (`GenSegment.v:1920`) has statement-level no-ops (`DAt`,
   `arr_dir`) and reads values through `rv_val = ty.projLeft`
   (`GenSegment.v:1915`).
3. **Invisible assumptions and vacuity.** Hypotheses can be jointly
   unsatisfiable (byte overlaps, duplicate specs, an `AST` no word decodes to
   — `pure_decode` is an `Axiom`, `Machine.v:147`). The checks that rule this
   out exist, but only as bridge PREMISES (`gen_prog_noninterferent`,
   `GenProg.v:105`: `NoDup`, `data_layout_ok`, Sync), not on the trusted
   surface — and an auditor cannot rely on how a theorem was proved.

Plus (group B, bundled because Phase 4 rewrites these statements anyway):
muladd's program is `set_nth` reverting an earlier patch
(`Example/Muladd/MuladdParamInstrs.v:356`), its exit is the literal
`init_addr + 1128` instead of `init_addr + 4 * length instrs`, and
`MuladdParamResult.v`'s header still says "Untracked probe". And three
comment fixes in the trusted file: the `noninterferent_strong` comment
(`:258–260`) understates the theorem; `(* byte order correct? *)` (`:121`)
is unanswered; the decode trust assumption is stated nowhere.

## 1. Where the change lands (measured on KatamaranRel, 2026-10-08)

| front-end | defined | value part | concretized by |
|---|---|---|---|
| `reg_spec` / `mem_full_spec` (TRUSTED) | `Noninterference.v:93/95` | `option (Val …)` | — |
| `reg_spec_rel` / `mem_spec_rel` | `GenContract.v:333/334` | `param_val` = `PVExist \| PVConst v \| PVBaseOff k` (`:328`) | `concretize_reg/mem` (`:832/840`) |
| `reg_spec_q Σ` | `GenSegment.v:1769` | `param_val_q Σ` (`:1750`) | `concretize_reg_q` (`:2012`) |
| `data_spec Σ` | `GenSegment.v:1846` | `DCell pub (option term)`, `DArr`, `DBytes`, `DAt`, `DPtr` | `concretize_data` (`:1920`) |

Result statements show the FRONT-END specs
(`map (concretize_reg init_addr) cmovznz4_reg_specs_rel`), so fixing only the
trusted types would leave the misleading combinations on the page.

Reach (files, excluding `ZZ*` probes): `reg_spec` 13, `reg_spec_rel` 13,
`mem_spec_rel` 9, `mem_full_spec` 8, `concretize_reg` 9, `concretize_mem` 7,
`concretize_data` 6, `mem_spec` 5, `reg_convert` 11 (incl. `Contracts`,
`GenCompose`, `IrisInstance*`). `gen_*`/`declare_*`: only
`Noninterference.v` + `EndToEnd.v`. 21 tracked Result files.

## 2. Decisions

**DECIDED (Emiel, 2026-10-08):**
- **D1.** Sum type instead of `bool` + `option`, registers AND memory.
- **D2.** One pass: sum type + register plumbing + memory plumbing — one
  statement review, one gate.
- **D3.** No alignment requirement on memory specs.
- **D4.** `X0` unrepresentable by type.
- **D5.** A well-formedness PREMISE on fixed specs is no fix (a failing spec
  makes the theorem vacuous). Premises on universally quantified PARAMETERS
  are legitimate scope (e.g. CheckScalarPtr's `ka` disjointness), as long as
  they are visibly satisfiable.
- **D6.** Over-strict checks are acceptable.
- **D7.** `concretize_data` (and `data_ok`) are in scope.
- **D8.** Base on `KatamaranRel`; `issue/relval-pair` stays parked on its
  branch. Implementation happens on a topic branch `issue/spec-layer`
  created at the start of Phase 1 (branch-workflow skill), merged through
  the gate.
- **D9.** Group B (muladd program/exit/header) is part of Phase 4.

**DECIDED in Phase 0 (Emiel, 2026-10-09; VibeWise design checkpoints):**
- **D10. Spec type is parametric:** `spec V := Secret | Public | Known (v : V)`,
  one type instantiated per layer (trusted: `Val`; `_rel`: const / base
  offset; `_q`: const / named base + offset; data cells: `Term Σ`), so every
  `concretize_*` is a map over the `Known` payload and cannot turn `Secret`
  into `Public`. Reason (Emiel): "easier to understand what each new version
  adds". Still open: the front-end constructors and `data_spec`'s fit.
- **D11. Memory layout: proof-carrying base + shape-B front-end.** Order
  chosen: settle the layout BEFORE the rest of Q1. Trusted base = a record of
  address-keyed blocks (N addresses, so no bitvector wrap) and a
  disjointness proof IN THE TYPE; the code is one of the blocks. End
  theorems only NAME a layout value (`muladd_layout ia b`): disjointness is
  an obligation where the value is defined, never in the statement (Emiel:
  clutter), and an overlapping layout cannot be written (closes §0.3's
  overlap vacuity). Fits-in-memory stays a parameter premise; a layout may
  take a parameter premise as an argument (`csp_layout ia ka l Hka`).
  Front-end shape B — ordered contiguous runs separated by gaps ≥ 0, a
  pointer's position given as a gap, one layout per memory order — translates
  into the base with disjointness by shape (one generic lemma). `arr_dir` and
  `DAt` leave every statement-facing type (proof-only). The proof field is
  value-level only: the contract side already gets disjointness from `∗`.
  Before Phase 1: check that all 21 Result files' memory fits the base.
  Still open: where `dir` and `DAt`'s address-matching job live on the
  contract side.
- **D12 (= Q1b). Shallow statements:** end theorems take plain Coq data
  (N/bv expressions in the theorem's parameters), never `Term`s, a
  `Valuation` or `rv_val`; each Result proves once that its data equals the
  generator's deep specs. Drafts: `PLAN-spec-layer-statements.md`.
- **D13 (= Q6). Decode: no action.** Emiel: not a real issue — every program
  is defined as `AST`s first, so it is decodable by construction.
- **D14. Front-end data layout = regions back to back** (refines D11's
  shape B): `Word (spec word) | Array (Secret n | Public n | Known vs) |
  Bytes … | Gap n`, placed contiguously from the END OF THE CODE; a gap is
  its own region. Compiles to the D11 base (explicit blocks + disjointness
  proof); disjointness, incl. clear-of-code, by shape. Layouts the front-end
  cannot express (check_scalar's k on either side of the code) are written
  in the base directly. The CODE STAYS SEPARATE as today (`init_addr`,
  `instrs`, `mem_has_instrs`; Emiel: "let's not do too many things at
  once") — code as a region would need a real decoder, since
  `pure_decode` is an Axiom (`Machine.v:147`). REJECTED: `run_at`-style
  derived addresses (Emiel: hides crucial information) — register specs use
  literal address expressions. Proof-only structure (`dir`, `DAt`,
  muladd's top-limb split) never appears in a statement.

**Already established (the checks exist):** `gen_prog_noninterferent`
(`GenProg.v:105–116`) requires `NoDup` of register indices (`HND`), the
byte-level `data_layout_ok` (`HLayout`; `Adequacy.v:1055`: in range, clear of
code, cells pairwise disjoint as 4-byte ranges, NO alignment), and Sync
wherever `rv_val` is used (`data_ok`, `GenSegment.v:1941`; `reg_q_sync`;
`Hp`). Q4 is therefore about making them VISIBLE, not inventing them.

**OPEN — settled in Phase 0, Emiel proposes first:**
- **Q1. The spec types.** Shape of the sum type (e.g. `Secret | Public |
  Known v` for cells/registers; arrays only `Secret | Public`); one shared
  type or separate register/memory types; how `param_val`, `param_val_q`,
  `data_spec` mirror it (`PVBaseOff` = known, base-relative); **deep or
  SHALLOW specs in the statement** — the deep form (`Term`s + a `Valuation`
  of `RelVal`s) is what the generator needs for independent pointers and
  symbolic sizes, but the statement could take Coq functions of the
  parameters with a proved correspondence (no `RelVal` on the trusted
  surface; removes the `rv_val` question). Readability targets: cmovznz4,
  muladd (`A0` consed on by hand because `PVBaseOff` takes only a constant),
  CheckScalarPtr (valuation + `concretize_data`).
- **Q2. Register keys.** `Reg ty_xlenbits`, or a `RegIdx` sub-type without
  0? `Tables.v`'s `A0`/`T0`/… aliases are `RegIdx`; check `reg_convert`'s 11
  users.
- **Q3. Memory plumbing.** Delete `mem_spec`, or keep it internal to the
  proof chain (`Adequacy`, `GenProg` are stated in it)? Which word predicate
  survives; settle the byte order (`bv.app`'s bit order vs little-endian).
- **Q4. Where the checks become visible**: a decidable conjunct of each end
  theorem (`spec_ok … = true ∧ noninterferent_strong …`, by `reflexivity` —
  check it closes for symbolic sizes), the types, outer premises on
  parameters (D5), or a per-Result witness lemma.
- **Q6. The decode assumption**: a comment, or also a named `decodable
  instrs` the reader can see?

## 3. Phases

One session per phase is the intended rhythm (`/clear` between, the plan
and the TODO carry the state). Light check per phase (that phase's files
compile, `keep_vo`); ONE full gate at the end. Kill any compile >1.5× its
baseline CPU and investigate.

**Phase S — set-up (first session, ~15 min, before Phase 0).**
- Confirm the plugins loaded: `/vibe-wise:learn`, `/vibe-learn:learn` and
  `/reading-quiz` should all autocomplete. (`/vibe-wise:learn`, `/vibe-wise:reset`
  and `/reading-quiz` are `disable-model-invocation` — only YOU can start
  them, Claude never sees them as skills.) `.vibe-learn/session-log.jsonl`
  starts logging at the first prompt, not the first edit.
- Start while-you-wait in a terminal split (§5) and leave it running.
- DECIDED (2026-10-08): `.claude/wyw.json` AND `.claude/decks/` are
  **gitignored** (Emiel; against the plugin's commit-it design — decks are
  private study material). Decks go in `.claude/decks/`, the plugin's
  default; a fresh clone regenerates them from the TODO/this plan.
- **Learning:** none yet — just confirm all four tools respond.

**Phase 0 — design (Emiel leads; no code).**
- Settle Q1–Q4, Q6; rewrite §2 so every Q is DECIDED; produce a
  before/after of the cmovznz4 statement and sign it off as readable.
  Nothing is implemented before that sign-off.
- **Learning — VibeWise (first real use).** Run `/vibe-wise:learn`; do its
  onboarding honestly (it adapts to the level you state). For each open
  question: write your own answer FIRST, let VibeWise critique it, then
  decide. Exercise: once, deliberately pause ("pause learning") and resume
  (`/vibe-wise:learn`) to feel the difference. Watch for: does it ask
  before proposing? Does its critique find anything you missed? *Landed
  when:* every Q in §2 is DECIDED in your words, and you can say what
  VibeWise added that a plain conversation would not have.
- **Learning — vibe-learn on a design session.** At the end: `/learn`, then
  `/quiz`. A design session has few edits, so expect a thin log — that tells
  you what vibe-learn is (and is not) good for.

**Phase 1 — trusted layer (`Noninterference.v`).** Create `issue/spec-layer`
from `KatamaranRel`. New spec types and `gen_*`/`declare_*`, no
`reg_convert`, no sigma list, one memory-word predicate, the three comment
fixes. Check: compiles.
- **Learning — while-you-wait live review.** Before Claude starts, open
  Live review. Every hunk to the trusted file appears as it is written; flag
  the ones to discuss. *Landed when:* your review of the trusted diff is
  done by the time the phase ends, from the flags, not from a re-read.
- **Learning — `/explain`.** After: `/vibe-learn:explain Noninterference.v`
  and compare it with your own understanding from reading quiz 1. Note
  whether it took over a question `rocq-implementation` should have
  answered (the skipped routing check). *Landed when:* you can say where
  `/explain` is accurate and where `/reading-quiz` is the better tool.
- **VibeWise:** keep it ON — Phase 1 is still design-heavy.

**Phase 2 — bridges (`EndToEnd.v`, `Adequacy.v`, `GenProg.v`).** Re-prove
the `gen_implpre*`/extraction lemmas over the new types; `mem_spec` per Q3.
The bulk of the proof work.
- **Learning — `/reading-quiz`, explain-first mode, BEFORE starting:** on
  `EndToEnd.v`'s `gen_implpre*` bridges — you are about to have them
  rewritten, so understand what they do first.
- **VibeWise: PAUSE** for the proof grind; resume only if a design question
  surfaces (a lemma's statement, not its proof). *Landed when:* you toggled
  it at the right moments without being reminded.
- **while-you-wait:** during long compiles, try a quiz deck of the reading
  quizzes' findings (vacuity sources, the `(false, Some v)` trap, `rv_val`).
- **vibe-learn:** `/learn` at the end; `/quiz review` (shaky concepts from
  Phase 0/1 come back here — that is the spaced-repetition ledger working).

**Phase 3 — front-ends (`GenContract.v`, `GenSegment.v`).** `param_val`,
`param_val_q`, `data_spec`, `concretize_*`, `data_ok` per Q1. Measure one
example's VC cost before/after (the generated contract may change shape).
- **VibeWise: ON** — front-end shape is design.
- **while-you-wait:** live review again; compare with Phase 1 — is it still
  worth the per-tool-call overhead (§5)?
- **vibe-learn:** `/explain GenSegment.v` (a file you now know well — a good
  test of its accuracy); `/quiz`.

**Phase 4 — examples and Result files (+ group B).** 21 Result files, the
example data, muladd's literal program and exit expression, stale header.
Mechanical.
- **VibeWise: PAUSE.** **while-you-wait:** live review of every Result
  STATEMENT (trusted) — skim the rest. **vibe-learn:** `/learn`.

**Phase 5 — the visible checks (Q4).**
- **VibeWise: ON.** A design phase again.

**Phase 6 — full gate, statement review, merge.** `scripts/gate.sh` (end
theorems axiom-clean: only `pure_decode`, `Base.mmioenv`). Statement diff of
every Result file: `python3 scripts/stmtdiff.py 'Result\.v$|Noninterference\.v$' <commits>`.
Update CFGVer/CLAUDE.md's trusted-surface list (group E: also `Tables.v`
register names, which are already in statements) and grep the skills for
renamed names, in the last commit.
- **Learning — closing the loop.** `/reading-quiz` on the NEW
  `Noninterference.v` (Socratic mode — tests whether the redesign is
  readable to its own author). `/vibe-learn:digest`, then write your own
  five-minute explanation of the change and compare the two.
- **Merge comprehension check:** that explanation, checked against the diff,
  is the condition for merging into `KatamaranRel`. (The hook version is a
  separate small task right after — §6.)

## 4. Risks

- **Proof churn in `EndToEnd.v`** — rewritten, not edited (`gen_init_mem`
  alone has 43 occurrences).
- **VC cost** (Phase 3): the generator must not add per-spec case splits.
- **Symbolic sizes** make a decidable conjunct (Q4) non-trivial.
- **Readability is the acceptance criterion**, Emiel's call (Phase 0
  sign-off), not a green build.
- **Tool friction**: VibeWise left ON through Phases 2/4 will slow proof work
  badly; while-you-wait adds ~50–100 ms to every tool call and its daemon
  never exits; vibe-learn 0.13.0 can emit invalid SessionStart JSON when the
  previous summary contains `/\` or `\/`. None blocks the refactor — if one
  gets in the way, pause/stop it and note why for §6.

## 5. Tool reference

All installed `--scope local` (this repo only), active from session start.

**VibeWise** (planning). `/vibe-wise:learn` starts/resumes learn mode; first
run onboards and writes `.vibe-wise/` (gitignored). It asks for YOUR approach
first, then gives feedback (design checkpoint), and confirms each concrete
change before writing it (implementation checkpoint). "pause learning" sets
`Learning mode: paused`; `/vibe-wise:learn` resumes; `/vibe-wise:reset`
starts over (backs up the profile). Cost: ~12–15 KB of reads per session
start/compaction while active.

**while-you-wait** (while Claude works). `alias wyw='node ~/.claude/plugins/cache/anthropic-plugin-directory/while-you-wait/0.1.0-3c9582a8fbe8/bin/wyw.mjs'`;
`wyw tui` in a split, or `wyw web`. Live review (hunks as they are written;
flag to discuss), quiz decks (config in `.claude/wyw.json`, path fixed by the
plugin, gitignored per Phase S; decks in `.claude/decks/`), info cards,
games. AVOID the `repo-chat`/`quiz-from-diff` examples: each message is a
billed `claude -p` (~30–40k tokens). Stop with `pkill -f while-you-wait`.
Cost: two node processes per tool call; ~100 MB steady (node is 43 MB here).

**vibe-learn** (after work). `/learn [question]` recap from the session log;
`/quiz [topic|review]` recall questions, shaky ones return later;
`/explain [file|topic]` guided tour of a file the session touched;
`/digest` structured session report. Only knows what its log saw — not for
code no session touched (that is `/reading-quiz`). Writes `.vibe-learn/`
(gitignored; global health log off via `.vibe-learn/config.json`). A second
session in the same directory rotates the first one's log.

**`/reading-quiz`** (catching up on existing code; repo skill). Socratic
mode by default: "Read file:lines → one question", answers checked with
`file:line`; "hint" / "tell me". Explain-first mode when you want a
convoluted area explained before you read it. Findings go to the TODO.

## 6. End-of-plan review (Learning)

After Phase 6, one short session:
1. For each tool: did it earn its cost? Keep, change how it is used, or
   uninstall (`claude plugin uninstall <name> --scope local`). while-you-wait
   is the one most likely to go; vibe-learn's `/explain` routing is the open
   question.
2. Collect `/reading-quiz` feedback and revise the skill.
3. Build the merge-time comprehension gate as a hook (TODO group F) — this
   plan's Phase 6 was its manual dry run.
4. Update the `project-learning-program` memory.
