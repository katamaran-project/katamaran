# PLAN: a readable spec layer for `noninterferent_strong`

Status: rev 1.1 (2026-10-08; §2 extended with reading quiz 2 on the
front-ends: D7, existing checks, deep vs shallow), NOT STARTED. Written right after Emiel's reading
session on `Noninterference.v` (the first `/reading-quiz`), from the findings
in `.claude/TODO.md` Priority 0. Phase 0 (design, with Emiel) must run before
anything is implemented: §2 lists what is decided and what is still open.

This plan doubles as Emiel's hands-on introduction to the learning tools
installed on 2026-10-08 (VibeWise, vibe-learn, while-you-wait) — §5 says which
tool is used where and what to practise with it.

## 0. Goal

The trusted statement must be **easy to read and hard to misread**. Today a
reader of a Result file has to see through three problems:

1. **Misleading specs.** Every spec carries a `pub : bool` AND an optional
   initial value. `(r, false, Some v)` reads as "r is secret" but is public:
   `noninterferent_strong` forces both worlds to `v`
   (`Noninterference.v:272–273`). The same `(bool, option)` pair exists in
   all four spec front-ends, so the combination is writable everywhere.
2. **Conversion plumbing.** Registers go `RegIdx` → `reg_convert`
   (`Base.v:1019`, `option (Reg ty_xlenbits)`) → `existT` into
   `{x : Ty & Reg x}` (`gen_public_regs`, `:109`) → unpacked again in
   `declare_public_registers` (`:250`). The sigma type is BlockVer heritage.
   `reg_convert 00000 = None` drops any `X0` spec silently. Memory keeps a
   legacy `mem_spec = (addr, pub)` (`:140`) next to
   `mem_full_spec = (addr, pub, init)` (`:95`), and two word predicates do one
   job: `get_word` (`:133`) and `mem_has_word` (`:118`).
3. **Unstated assumptions and vacuity.** Hypotheses can be jointly
   unsatisfiable — overlapping byte ranges between data words, or between
   data and code, with different values; a register or address given two
   initial values; an `AST` no word decodes to (`pure_decode` is an `Axiom`,
   `Machine.v:147`). Any of these makes an end theorem true for free and it
   still compiles green.

Plus three comment fixes in the trusted file: the `noninterferent_strong`
comment (`:258–260`) understates the theorem (it covers every n-step prefix
that has not hit the exit, not only runs that reach it); `(* byte order
correct? *)` (`:121`) is an unanswered question; and the decode trust
assumption is stated nowhere.

## 1. Where the change lands (measured 2026-10-08)

Four spec front-ends, all carrying `(bool, value-ish)`:

| front-end | defined | value part | concretized by |
|---|---|---|---|
| `reg_spec` / `mem_full_spec` (TRUSTED) | `Noninterference.v:93/95` | `option (Val …)` | — |
| `reg_spec_rel` / `mem_spec_rel` | `GenContract.v:333/334` | `param_val` = `PVExist \| PVConst v \| PVBaseOff k` (`:328`) | `concretize_reg/mem` (`:832/840`) |
| `reg_spec_q Σ` | `GenSegment.v:1774` | `param_val_q Σ` (`PQExist \| PQConst \| PQAt`) | `concretize_reg_q` (`:2017`) |
| `data_spec Σ` | `GenSegment.v:1851` | `DCell pub (option term)`, `DArr pub dir n`, `DBytes pub n`, `DAt x`, `DPtr x` | `concretize_data` (`:1925`) |

**Key consequence for the design:** a Result statement shows the FRONT-END
specs (`map (concretize_reg init_addr) cmovznz4_reg_specs_rel`), so fixing
only the trusted `reg_spec` would leave the misleading combination on the
page. Readability requires changing the front-ends too.

Reach (files, excluding `ZZ*` probes): `reg_spec` 13, `reg_spec_rel` 13,
`mem_spec_rel` 9, `mem_full_spec` 8, `concretize_reg` 9, `concretize_mem` 7,
`concretize_data` 6, `mem_spec` 5 (`Adequacy`, `EndToEnd`, `GenProg`,
`Noninterference`, `BearSSLCheckScalarLoop1`), `reg_convert` 11 (incl.
`Contracts`, `GenCompose`, `IrisInstance*`). The `gen_*`/`declare_*` functions
are used only in `Noninterference.v` + `EndToEnd.v`. 21 tracked Result files.

Generator observation (relevant to Q1): `gen_reg_asn_q` (`GenSegment.v`)
already ignores `is_pub` for `PQConst` — a known value gets no `secLeak`
either way. The generators already treat "known" as its own class; only the
types don't say so.

## 2. Decisions

**DECIDED (Emiel, 2026-10-08):**
- **D1. Sum type** instead of `bool` + `option`, for BOTH registers and memory.
- **D2. One pass**: the sum type, the register plumbing and the memory
  plumbing are done together — one trusted-statement review, one full gate.
- **D3. No alignment requirement** on memory specs (one existed before and
  was removed — likely because of byte-granular data, `PLAN-byte-memory.md`,
  1c69aa4b; confirm in Phase 0).
- **D4. `X0` must be unrepresentable by type**, not filtered at runtime.
- **D5. A well-formedness PREMISE is not a fix**: a spec that fails it makes
  the end theorem vacuous. Checks must be proved (conjunct / VC), or made
  unnecessary by types.
- **D6. Over-strict checks are acceptable** ("not allowing some legitimate
  but fishy behaviour").
- **D7. `concretize_data` is in scope** (reading quiz 2): it is on the trusted
  surface and "a mess, the same as data_ok" — clean it up in this pass.

**Findings from reading quiz 2 (front-ends) that reshape the open questions:**
- **The checks already exist, as bridge premises.** `gen_prog_noninterferent`
  (`GenProg.v:105–116`) requires `NoDup` of the register indices (`HND`), the
  byte-level layout check `data_layout_ok` (`HLayout`; `Adequacy.v:1066`:
  in range, clear of code, cells pairwise disjoint as 4-byte ranges — NO
  alignment), and `SyncVal` wherever `rv_val` (= `ty.projLeft`,
  `GenSegment.v:1920`) is used (`data_ok`'s Sync conjuncts, `reg_q_sync`,
  `Hp`). But a bridge premise is NOT part of the trusted surface: a reader
  auditing the statement cannot rely on how it was proved, and a vacuous
  theorem proved some other way would look identical. So Q4 is not "invent a
  check" but "make the existing ones visible" (statement conjunct, or types).
- **Statement-level no-ops / silent conversions**: `DAt` and `arr_dir` do
  nothing in `concretize_data`; `rv_val` silently takes world 1's value of a
  `NonSyncVal`; `A0` in muladd is hand-concretized because `PVBaseOff` takes
  only a constant offset.
- **Deep vs shallow**: the deep form (`Term`s + a `Valuation` of `RelVal`s)
  is what the GENERATOR needs (independent pointers via `DPtr`, symbolic
  sizes). The STATEMENT could take a shallow spec (Coq functions of the
  parameters) with a proved correspondence — no `RelVal` on the trusted
  surface at all, which also removes the `rv_val` question.

**OPEN — settle in Phase 0, with Emiel proposing first (VibeWise, §5):**
- **Q1. The sum type's shape.** e.g. `Secret | Public | Known v` for cells and
  registers; arrays/bytes only `Secret | Public` (they have no init). One
  shared type, or separate register/memory types? How do the front-ends
  mirror it: does `param_val` become `PVSecret | PVPublic | PVConst v |
  PVBaseOff k` (`PVBaseOff` = known, base-relative)? And deep or SHALLOW
  specs in the statement (findings above)? Readability targets: cmovznz4
  (A1–A3 flagged secret but known), muladd (`A0` consed on by hand,
  `sym6_instrs` as a patch-of-a-patch, literal exit `+ 1128`), CheckScalarPtr
  (valuation + `concretize_data`).
- **Q2. Register keys.** `Reg ty_xlenbits` (no x0, and `reg_convert` leaves
  the statement), or a `RegIdx` sub-type excluding 0? `Tables.v`'s
  `A0`/`T0`/… aliases are `RegIdx` today, so spec authors need `Reg`-level
  names; check `reg_convert`'s 11 users for what else wants `RegIdx`.
- **Q3. Memory plumbing.** Delete `mem_spec` entirely, or keep it as an
  internal type of the proof chain (`Adequacy`, `GenProg` are stated in it)?
  Which of `get_word` / `mem_has_word` survives, and how is the byte order
  settled (check `bv.app`'s bit order against RISC-V little-endian)?
- **Q4. The overlap / vacuity check (brainstorm — D3, D5, D6 constrain it).**
  Start from `data_layout_ok` + `NoDup` (they exist, see the findings above);
  the question is mainly WHERE they become visible. Candidates: (a) a decidable byte-range disjointness check over all data
  words plus the code range, proved as a conjunct of each end theorem
  (`spec_ok … = true ∧ noninterferent_strong …`, by `reflexivity`); (b) a
  per-Result non-vacuity witness lemma; (c) promote the bridge's existing
  `data_layout_ok` premise (`DPtr` disjointness, proved inside each Result's
  proof today) into the statement as a proved conjunct. Symbolic sizes
  (`DArr` with a term count) make (a) a per-instance computation — check it
  closes by `vm_compute` for muladd/check_scalar at every size, or needs
  `lia`.
- **Q5. Branch base.** `issue/relval-pair` is not merged yet (its own
  "meaning changed" list, PLAN-relval-pair §11, is pending). Branch `issue/spec-layer` from `KatamaranRel` after
  relval-pair merges, or from relval-pair now?
- **Q6. The decode assumption.** Only a comment in the trusted file (cannot
  be checked in Coq while `pure_decode` is an `Axiom`), or also a named
  `Definition decodable instrs := ∃ ws, …` the reader can see?

## 3. Phases

Light check per phase (the files of that phase compile with `keep_vo`); ONE
full gate at the end (`feedback_light_gates`). Kill any compile that runs
>1.5× its baseline CPU and investigate (`feedback_compile_cutoff`).

- **Phase 0 — design (Emiel leads).** Optional warm-up: `/reading-quiz
  concretize_data` (the front-end most affected; also find what decides
  `NoDup` in muladd's statement — dpdgraph showed `NoDup_dec`). Then settle
  Q1–Q6, VibeWise on. Output: §2 rewritten with every Q decided, and a
  before/after of ONE Result statement (cmovznz4) that Emiel signs off as
  readable. Nothing is implemented before that sign-off.
- **Phase 1 — trusted layer (`Noninterference.v`).** New spec types and
  `gen_*`/`declare_*` over them; no `reg_convert`, no sigma list; one memory
  word predicate; the three comment fixes. Check: compiles. Emiel reviews the
  whole diff of this file — it is the trusted surface.
- **Phase 2 — bridges (`EndToEnd.v`, `Adequacy.v`, `GenProg.v`).** Re-prove
  the `gen_implpre*` / extraction lemmas over the new types; `mem_spec` per
  Q3. Expected to be the bulk of the proof work.
- **Phase 3 — front-ends (`GenContract.v`, `GenSegment.v`).** `param_val`,
  `param_val_q`, `data_spec` per Q1; `concretize_*` become trivial or
  disappear. Check one example's VC cost is unchanged (the generated contract
  may change shape).
- **Phase 4 — examples and Result files.** Mechanical: 13-ish example files,
  21 Result files. Every Result STATEMENT changes textually — that is the
  point — so each one is reviewed (Phase 6).
- **Phase 5 — the vacuity check** per Q4.
- **Phase 6 — full gate + statement review + merge check.** `scripts/gate.sh`
  (all end theorems axiom-clean: only `pure_decode`, `Base.mmioenv`). A
  statement diff of every Result file (the commit-grouping agent's
  `stmtdiff.py` — copy it into the repo first, the scratchpad copy is not
  durable). Then the merge-time comprehension check (§5): Emiel explains the
  change before it merges into `KatamaranRel`.

## 4. Risks

- **Proof churn in `EndToEnd.v`**: the init/public extraction lemmas reason
  about `omap` filtering (`gen_init_mem` alone has 43 occurrences). A sum
  type should make them simpler, but they are rewritten, not edited.
- **VC cost**: generators change shape (Phase 3). Measure before/after on one
  example; the generator must not add per-spec case splits to the VC.
- **Symbolic data sizes** make a proved disjointness check (Q4a) non-trivial.
- **Readability is the acceptance criterion**, and it is Emiel's call — the
  Phase 0 before/after sign-off is the test, not a green build.

## 5. Learning the tools along the way

The tools load at session start; all three are installed for this repo only
(`settings.local.json`). Each phase below says what to practise.

**VibeWise — planning (Phase 0, and every later design question).**
- Start the Phase 0 session with `/vibe-wise:learn`. First run does a short
  onboarding (experience level, goals) and writes `.vibe-wise/` (gitignored).
- What to expect: it asks for **your** approach before proposing anything,
  then gives feedback and trade-offs (design checkpoint), and confirms each
  concrete change before writing it (implementation checkpoint). Practise:
  answer Q1–Q6 yourself first; let it critique.
- **Pause it for long implementation runs** (Phases 2–4): say "pause
  learning" (sets `Learning mode: paused`); `/vibe-wise:learn` resumes.
  Costs ~12–15 KB of reads per session start/compaction while active.
- `/vibe-wise:reset` starts the profile over (backs up the old one).

**while-you-wait — while Claude works (Phases 1–4).**
- Before an implementation phase:
  `alias wyw='node ~/.claude/plugins/cache/anthropic-plugin-directory/while-you-wait/0.1.0-3c9582a8fbe8/bin/wyw.mjs'`,
  then `wyw tui` in a terminal split (or `wyw web` for a browser tab).
- Practise **Live review** on Phase 1: every hunk to the trusted file appears
  as Claude writes it; flag the ones to discuss, so your review of the trusted
  diff is done by the time the phase ends.
- Optional: a quiz **deck** of today's findings (vacuity sources, the
  `(false, Some v)` trap) to drill during long compiles. Decks are configured
  in `.claude/wyw.json` (path fixed by the plugin) — decide first whether
  that file is committed or gitignored; don't run `wyw init` before.
- Avoid the `repo-chat` / `quiz-from-diff` example activities: each message
  is a billed `claude -p` session (~30–40k tokens before any work).
- When done: `pkill -f while-you-wait` (no stop command; the daemon never
  exits on its own).

**vibe-learn — after work (end of every phase).**
- `/learn` — a recap of what the phase did, from its log. `/quiz` — recall
  questions; shaky answers come back in later sessions (`/quiz review`).
- `/explain <file>` on the file the phase changed most (e.g. `EndToEnd.v`
  after Phase 2). Watch whether it captures "explain this lemma" questions
  that `rocq-implementation` should answer — the routing check was skipped
  on purpose ("first just use it"); report it if it misroutes.
- `/digest` at the end of the plan — the report to compare against your own
  Phase 6 explanation.
- Known quirk: v0.13.0 can emit invalid SessionStart JSON when the previous
  summary contains backslashes (`/\`, `\/`); if a session starts with a hook
  error, that is why (fixed upstream in 0.13.3).

**`/reading-quiz` — catching up on existing code (Phase 0, Phase 6).**
- Phase 0: on `concretize_data` / the front-ends before designing them.
- Phase 6: on the new `Noninterference.v`, as the input to the merge check.

**Merge-time comprehension check (Phase 6).** Before `issue/spec-layer`
merges, Emiel writes the five-minute explanation (what changed, why, what the
statement now promises and assumes) and Claude checks it against the diff.
Making this a hook (`git-workflow-guard.sh` requiring a comprehension note
before merging into `KatamaranRel`) is wanted but NOT part of this plan — it
touches a load-bearing hook with a 23-case test suite; do it as its own small
task, ideally right after this plan as its first real use.
