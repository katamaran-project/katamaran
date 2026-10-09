# PLAN: a readable spec layer for `noninterferent_strong`

Status: rev 4 (2026-10-09): §2a migration mechanics added (PROPOSED,
awaiting Emiel's OK). rev 3 (2026-10-09), Phase S DONE, Phase 0 DONE (D10–D19); D11
scope check done (§1a, D20–D23); Phases 1–4 rewritten for D10–D26
(Phases 2 and 3 swapped, Phase 5 removed). Next: Phase 1. Based on `KatamaranRel` (D8);
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

### 1a. D11 scope check (2026-10-09, from source; example `.vo`s were stale)

**18 of the 21 Result files state `noninterferent_strong`;** the three
composed files (CountdownComposed, SwapComposed, TwoLoopsComposed) stop at
`myWP2_loop` and are out of scope. **10 are register-only** (memory `[]`):
InvMixColumns, BearSSLCheckScalar, BearSSLModpow, BearSSLMuladd, Countdown
(register theorem), CountdownRec, Jumps, MvSwap, PaddedLoop, Precompute,
SetX2. **8 have memory, and every one places it right at the end of the
code with no gaps:**

| Result | data at (instrs) | regions (D14) |
|---|---|---|
| Cmovznz4 | +116 (29) | `Array 4 Secret` ×3 |
| BearSSLCheckScalarLoop1 | +16 (4) | 8 words, byte-accessed: `Bytes 32 Secret` or `Array 8 Secret` |
| BearSSLModpowFull | +112 (28) | `Array 4 Secret; Array 12 Secret` (t2, base) |
| Countdown (mem theorem) | +16 (4) | `Word (Known 2)` |
| KeyScheduleLoop | +56 (14) | `Array 2 Secret` |
| CheckScalarParam | +144 (36) | `Bytes 32 Secret; Bytes (bv.bin l) Secret` |
| MuladdParam | +1128 (282) | as in the statement draft |
| CheckScalarPtr | +144; k anywhere | base directly (D21) |

So the base fits all 18 and only CheckScalarPtr needs it written by hand.
D15 holds: no Result register spec uses `X0`. More §0.1 instances:
countdown_mem `(X2, false, PVBaseOff 0)`, modpow_full `A0`/`A1`.

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
  Scope check DONE (§1a): the base fits all 18 statement-bearing Results.
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
  Arrays use the ONE parametric `spec` (D10) with the count outside:
  `Array (n : N) (s : spec (vec word n))` (`Bytes` likewise with `vec byte
  n`), so `Array 4 Secret` / `Array (M b) Public` read like words and a
  `Known` array of the wrong length cannot be written (Emiel, 2026-10-09).
- **D15 (= Q2). Register keys are GPR-only** (x1–x31, no `X0` by type),
  not `Reg ty_xlenbits` (which also holds `pc`, `mtvec`, `pmpaddr0`, …).
  Same pass as the memory change (D2: one statement review, one gate);
  `RegIdx`/`reg_convert` may stay internal, converted at the boundary.
- **D16. Statements write `compile` explicitly** — no `noninterferent`
  wrapper yet; `compile` takes the data's start address and regions, NOT
  the code (code stays separate, D14).
- **D17. `dir` / `DAt` on the contract side:** do without them if at all
  possible; if not, a hint-carrying variant of the region type (e.g. an
  adjusted `Array`) read only by the contract generator. Investigate in
  Phase 2 (the generator phase since the 2026-10-09 swap).
- **D18 (= Q3). Granularity: word-level wherever possible** (Emiel: for
  performance — do NOT make everything byte-granular). `Word`/`Array` are
  word blocks; only `Bytes` regions are byte-level. Instructions keep
  `mem_has_word` / `mem_has_instrs`. Legacy `mem_spec` goes; one word
  reader for data. Phase 1 must settle `(* byte order correct? *)`
  (`Noninterference.v:121`): does the statement's word assembly agree with
  the machine's own load (a `Word (Known w)` must mean what a `lw` sees)?
- **D19 (part of Q4). Clear of the code = a conjunct inside
  `noninterferent_strong`'s definition**, so an overlap makes the theorem
  unprovable, not vacuous, and nothing extra appears on the page (code is
  outside `compile`, D16, so it is not guaranteed by shape).
- **Sign-off (2026-10-09):** the after-statements in
  `PLAN-spec-layer-statements.md` rev 2 (cmovznz4, muladd, check_scalar)
  are readable — Phase 0's exit criterion for readability is met.
- **TODO (deferred, Emiel):** the per-Result proof that the shallow
  statement data equals the generator's deep specs (D12) — cost unknown
  with symbolic sizes; priced at the end of Phase 3, before Phase 4.

**DECIDED after the D11 scope check (Emiel, 2026-10-09; §1a):**
- **D20. Fixed-address corollaries stay, as SANITY CHECKS** (Emiel: "these
  are sanity checks, so keep them as sanity checks"). ~15 statements in 12
  Result files restate a parametric theorem at a fixed `init_addr`
  (`ni_rel_corollary`, or `apply …_param; unfold init_addr`). Phase 4
  rewrites them in the new types and labels them sanity checks, not end
  results.
- **D21. CheckScalarPtr is written in the BASE, with blocks** — the
  "k anywhere" form only, no front-end variant. Disjointness is proved from
  the parameter premise (D11: `cs_mem ia ka l H`). This is the test that a
  hand-written base layout works.
- **D22. `Bytes` regions round up to whole words, for now** — as
  `concretize_data` does today (the statement owns the pad bytes; fit uses
  `4 * klen_words l`). **TODO (Emiel): look into byte-exact ownership** —
  mark it at the definition of the rounding in the trusted file, not only
  here. Affects CheckScalarParam / CheckScalarPtr when `l mod 4 ≠ 0`.
- **D23. Exit = `ia + 4 * length instrs`** in every statement whose exit is
  the address right after the last instruction (Emiel: more readable than
  a literal); group B's muladd fix is one instance. A program exiting
  elsewhere keeps its literal.

**DECIDED while rewriting Phases 1–4 (Emiel, 2026-10-09):**
- **D24. The bridges are REWRITTEN over the new types** (`EndToEnd.v`,
  `Adequacy.v`, `GenProg.v`), not wrapped by a boundary lemma from the old
  statement (Emiel: "we will vet the end result thoroughly"). D18 stands:
  `mem_spec` goes everywhere. Only `RegIdx`/`reg_convert` may stay internal
  (D15). The vetting is Phase 6's statement review + comprehension check.
- **D25. Kernel and front-end are separate files.** `Noninterference.v` is
  the semantic kernel (`spec`, GPR keys, base memory, `noninterferent_strong`);
  `region`/`compile`/`fits`/the shape lemma go in a NEW file (name open,
  Phase 1) that requires only `Noninterference.v` (Emiel: the front-end is
  "the user interface — very important, but not the kernel"). It is on the
  statement-READING surface (statements write `compile`, D16), so it is
  listed with the trusted files, marked as front-end.
- **D26. Phase 5 is removed** — Q4 is covered by D11, D19 and D5.

**Already established (the checks exist):** `gen_prog_noninterferent`
(`GenProg.v:105–116`) requires `NoDup` of register indices (`HND`), the
byte-level `data_layout_ok` (`HLayout`; `Adequacy.v:1055`: in range, clear of
code, cells pairwise disjoint as 4-byte ranges, NO alignment), and Sync
wherever `rv_val` is used (`data_ok`, `GenSegment.v:1941`; `reg_q_sync`;
`Hp`). Q4 is therefore about making them VISIBLE, not inventing them.

**FORMERLY OPEN — all resolved 2026-10-09** (kept for the record): Q1 →
D10, D11, D12, D14 (front-end constructors of `_rel`/`_q` still to be
spelled out in Phase 2); Q2 → D15; Q3 → D18; Q4 → D11 (disjointness in the
type), D19 (clear of code), D5 (parameter premises); Q6 → D13.

**Phase 0 questions as originally posed** (all resolved — see above):
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

## 2a. Migration mechanics (PROPOSED by Claude, 2026-10-09 — needs Emiel's OK)

Written after Phase 0 with VibeWise paused. Every choice Phase 0 did NOT
make is tagged **[proposal]**; nothing tagged so is decided until Emiel
says so.

**Fact that shapes everything (`Noninterference.v:261–285`):** the memory
specs only produce two premises — public words equal
(`declare_public_memory`) and known words have their value
(`declare_init_memory`). A Secret cell or register produces NO premise.
So in the statement a `Secret` region means nothing by itself; it matters
only through disjointness (D11) and clear-of-code (D19), which can only make
the theorem HARDER to prove, never weaker.

### 2a.1 Approach: in place, layer by layer, in import order

Each phase rewrites its files in place, in the build order of §3. There is
NO parallel `_v2` copy: GenSegment (1837 lines) and EndToEnd (2405) are
too big to duplicate. Consequence: the branch is red from Phase 1 to
Phase 4. Mitigations: every file is compiled with `keep_vo` before its
dependents; one `WIP (LLM)` commit per file once it compiles; the old
statements stay in git for Phase 6's `stmtdiff`. **Out of scope:**
merging the bridge families (`_u`/`_rel`/`_param`/`_classed`/`_bytes`/
`gen_prog`). Each is rewritten as it stands — rewrite, don't redesign.

### 2a.2 Kernel, `Noninterference.v` (Phase 1)

| old | new |
|---|---|
| `reg_spec := RegIdx * bool * option (Val ty_xlenbits)` | `reg_spec := gpr * vspec (Val ty_xlenbits)` |
| `gen_public_regs : … → list {x : Ty & Reg x}` (omap + `existT` + `reg_convert`) | `public_regs : list reg_spec → list (Reg ty_xlenbits)` through the total `gpr_reg` |
| `declare_public_registers` over `list {x & Reg x}` | over `list (Reg ty_xlenbits)` |
| `gen_init_regs` | same role: `Known v` ↦ `(gpr_reg r, v)` |
| `mem_full_spec`, `mem_spec`, `mem_full_to_spec`, `gen_public_addrs`, `gen_full_public_addrs` | REMOVED (D18) |
| — | `block := {| blk_addr : N; blk_words : list (vspec word) |}`, `memory := {| blocks : list block; blocks_ok : blocks_disjoint blocks |}`, `cells : memory → list (N * vspec word)` |
| `gen_init_mem`, `declare_public_memory`, `declare_init_memory` | the same premises, over `cells m` (address `bv.of_N`) |
| `get_word` + `mem_has_word` (two readers) | `get_word` is THE data reader; `mem_has_word` stays for instructions only, with a proved lemma `mem_has_word μ a w ↔ get_word μ a = w` (one meaning) |
| `noninterferent_strong ia instrs exit regs (mems : list mem_full_spec)` | `… (m : memory) := clear_of_code ia instrs m ∧ ∀ …` (D19) |

- **[proposal] P1 — a kernel block is an address + a LIST of per-word
  `vspec`s.** No `vec`, no `Bytes`, no dependent types in the kernel:
  `Word`/`Array`/`Bytes` are front-end and compile to word lists, so D22's
  rounding (and its TODO) lives in `compile`, not in the kernel. D21's
  CheckScalarPtr base then reads
  `{| blk_addr := ka; blk_words := repeat Secret (klen_words l) |}`.
  Knock-on, amends D14: with rounding, the pad bytes of a `Known` byte
  string have no value, so **front-end `Bytes` takes only `Secret |
  Public` until D22's TODO is resolved** (no Result uses a `Known` `Bytes`).
- **[proposal] P2 — `gpr := { r : Reg ty_xlenbits | is_gpr r = true }`**,
  with `is_gpr` membership in `[x1; …; x31]` (Base.v's own registers). Then
  `gpr_reg := proj1_sig`: the kernel needs no `reg_convert` at all, and
  `X0`/`pc`/`mtvec` are unrepresentable. Statements keep writing `A0`:
  `Tables.v`'s aliases become `gpr` constants (`exist _ x10 eq_refl`), with
  `Coercion gpr_idx : gpr >-> RegIdx` so `ADDI A0 A0 …` still typechecks.
  `X0` stays a bare `RegIdx`. Internal agreement lemma (Tables, 31 cases):
  `reg_convert (gpr_idx g) = Some (gpr_reg g)`. Rejected:
  `{ i : RegIdx | i ≠ 0 }` (it keeps `reg_convert` in the kernel, with an
  unreachable default branch).
- **[proposal] Names.** `vspec`, not `spec`: `Katamaran.Prelude` already
  defines `spec` (`theories/Prelude.v:475`), and statements only ever write
  the constructors. The front-end file (D25) is `Layout.v`. `block` is
  also an executor op in `theories/Staging`, but that is never imported
  here. The draft's `memory ia cs_instrs` indexing is stale: under D19
  clear-of-code is a conjunct, not part of the type, so `memory` is not
  indexed.
- `vspec_map : (A → B) → vspec A → vspec B` sits next to `vspec`. Every
  `concretize_*` becomes a `vspec_map` (D10's guarantee: Secret stays
  Secret).
- Byte order (D18): prove `get_word` against the machine's 4-byte read (the
  `lw` path in `Machine.v`). If it disagrees, STOP and report — that would
  be a finding about every memory theorem proved so far, not a Phase 1 detail.

### 2a.3 Front-end, `Layout.v` (Phase 1, D25)

`region` exactly as D14 (with `Bytes` per P1). `compile (start : N) (rs :
list region) : memory` places regions back to back from `start`; `Gap n`
emits no block; `blocks_ok` is discharged INSIDE `compile` by one generic
lemma (`place_disjoint`), so no statement or Result ever proves
disjointness for a compiled layout. Two more generic lemmas:
`compile_clear : clear_of_code ia instrs (compile (ia + 4 * length instrs) rs)`
(by shape, D19) and `size`/`fits`. Statements read (D16, D23):
`fits … → noninterferent_strong ia instrs (ia + 4 * length instrs) regs
(compile (ia + 4 * length instrs) data)`.

### 2a.4 Generators, `GenContract.v` / `GenSegment.v` (Phase 2)

- Register keys are `gpr` in every front-end (`_param`, `_rel`, `_q`); the
  generators drop to `RegIdx` through `gpr_idx` (D15: internal).
- `(r, pub, PVExist | PVConst v | PVBaseOff k)` → `(r, vspec rel_val)` with
  `rel_val := RConst v | RBaseOff k`: `PVExist` ↦ `Public`/`Secret` by
  `pub`, `PVConst`/`PVBaseOff` ↦ `Known` (the flag was ignored there
  anyway). `param_val_q` likewise. `concretize_*` = `vspec_map`.
- `data_spec`: `DCell pub (option term)` → `DCell (vspec (Term Σ))`.
  **[proposal] `DArr`/`DBytes` keep their `bool` and `dir`, `DAt` stays —
  D17 resolved by D12:** shallow statements never show `data_spec`, so it
  already IS the "variant read only by the contract generator" D17 asks for.
  Nothing to remove.
- Generators emit lists in the SAME order `compile`/the statements use
  where that is free, so concrete-size correspondences close by
  `reflexivity` (2a.5).

### 2a.5 Bridges (Phase 3, D24)

- **Every bridge takes the statement's own data plus correspondence
  premises** (this is where D12 lands): `regs ≡ₚ <generator's concretized
  regs>` and `cells m ≡ₚ <generator's concretized cells>`. Permutation, not
  equality, because the kernel premises are `Forall`s (order-free) and
  `NoDup` survives permutation.
- The obligations that used to be premises: pairwise disjointness from
  `blocks_ok m` (lemma `cells_disjoint`); clear-of-code is now part of the
  CONCLUSION (D19), proved by `compile_clear` or, for D21, from the
  parameter premise; in range from `fits`. `data_layout_ok` shrinks to
  what is left.
- Rewrite order (each file committed once it compiles): `Adequacy.v`
  (`data_layout_ok`, `contig_data_layout`, `intro_mem_with_memory_at`,
  `instrsAndDataMemory_at`) → `EndToEnd.v` (`declare_init_mem_*`,
  `gen_init_mem_*`, `interp_mem_*`, `filter_*_concretize*`,
  `gen_implpre{,_mem,_mem_class,_mem_bytes,_mem_bytes_class,_data}`,
  `cfg_instrs_endToEnd_gen`, `gen_contract_noninterferent_{u,u_simple,rel,param,param_simple,rel_classed_simple,rel_bytes_simple}`,
  the `ni_rel_corollary` tactic) → `GenCompose.v` (4 uses) → `GenProg.v`
  (`gen_prog_noninterferent`, `data_layout_runs`).
- Generic correspondence lemmas, one per front-end constructor
  (`compile [Array n s]` vs `concretize_data [DArr …]`, etc.), so a symbolic-
  size Result folds lemmas instead of doing induction itself. Then the
  pricing run on cmovznz4 and muladd (§3 Phase 3).

### 2a.6 Results (Phase 4) — the per-file recipe

1. Data: `<prog>_data : list region` and `<prog>_regs ia : list reg_spec`,
   shallow (D12), from §1a's table.
2. Statement: as in 2a.3. Exit per D23.
3. Proof: the bridge, then the two `≡ₚ` facts — `reflexivity` /
   `vm_compute` at fixed sizes, the Phase 3 lemmas at symbolic sizes.
4. Sanity corollary at a fixed `init_addr` (D20), labelled as such.

Order: the 10 register-only files (memory `compile _ []`) → the fixed-size
memory files (Loop1, ModpowFull, Countdown mem, KeyScheduleLoop; Cmovznz4
was done in Phase 3) → symbolic sizes (CheckScalarParam, MuladdParam +
group B) → CheckScalarPtr (D21, base by hand) last. The four Results whose
proofs `intros` the definition directly (CheckScalarParam, MuladdParam,
PaddedLoop, CountdownRec) need their intro pattern split for D19's
conjunct.

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

**Build order (why Phases 2 and 3 swapped, 2026-10-09):** `GenContract.v`
and `GenSegment.v` state their generators over the trusted spec types, and
`EndToEnd.v` requires both, so nothing past the kernel compiles until the
generators do: `Noninterference.v` → front-end file → `GenContract` →
`GenSegment` → `Adequacy` … `EndToEnd` → `GenCompose` → `GenProg` → Results.
The branch is red from Phase 1 until Phase 4; each phase's light check
covers only its own files.

**Phase 1 — trusted kernel + statement front-end.** Create
`issue/spec-layer` from `KatamaranRel` (branch-workflow skill).
- **Mechanics: §2a.2 (kernel) and §2a.3 (front-end).** P1 (block
  content), P2 (GPR key type) and P3 (names) are PROPOSED there; Emiel
  signs them off before Phase 1 starts.
- **Kernel, `Noninterference.v`:** `spec V` (D10); GPR keys, `X0`
  unrepresentable, one total map to `Reg ty_xlenbits` — no `reg_convert`,
  no `existT` sigma list on the statement path (D15); base memory = blocks
  at `N` addresses + a disjointness proof in the type (D11); ONE data-word
  reader replacing `get_word`/`mem_has_word`, legacy `mem_spec` removed,
  instructions keep `mem_has_instrs` (D18); the clear-of-code conjunct
  inside `noninterferent_strong` (D19); `noninterferent_strong` over all of
  these. Settle `(* byte order correct? *)` (`:121`, D18): a `Word (Known
  w)` must mean what `lw` reads — a lemma, or a recorded argument. Fix the
  `noninterferent_strong` comment (`:258–260`). Still requires only
  `Semantics` + `Machine`.
- **Front-end file (D25), requires only `Noninterference.v`:** `region`
  (D14), `compile` (D16: data start + regions → base memory), `fits`, the
  ONE generic disjointness-by-shape lemma (D11) and clear-of-code by shape.
  The D22 rounding of `Bytes`, with its TODO at the definition.
- **Check:** both files compile (`keep_vo`). The three statements of
  `PLAN-spec-layer-statements.md` (cmovznz4, muladd, check_scalar — the
  latter in D21's base form) typecheck in a `ZZ` probe with `Admitted`
  bodies, and Emiel re-reads them against the REAL definitions:
  readability is re-checked before any proof depends on it.
- **Learning — while-you-wait live review.** Before Claude starts, open
  Live review. Every hunk to the two files appears as it is written; flag
  the ones to discuss. *Landed when:* your review of the diff is done by
  the time the phase ends, from the flags, not from a re-read.
- **Learning — `/explain`.** After: `/vibe-learn:explain Noninterference.v`
  and compare it with your own understanding from reading quiz 1. Note
  whether it took over a question `rocq-implementation` should have
  answered (the skipped routing check). *Landed when:* you can say where
  `/explain` is accurate and where `/reading-quiz` is the better tool.
- **VibeWise:** paused (design closed 2026-10-09, Emiel); resume only if a
  §2a proposal turns out wrong in contact with the code.

**Phase 2 — generator front-ends (`GenContract.v`, `GenSegment.v`).**
(Was Phase 3.) `param_val`, `param_val_q` and `data_spec`'s cells become
instances of `spec` (D10), so every `concretize_*` is a map over `Known`;
spell out the `_rel`/`_q` constructors D10 left open. `data_ok` (D7).
D17: per §2a.4's proposal, `dir`/`DAt` stay in `data_spec`, which shallow
statements (D12) never show. Mechanics: §2a.4. Move `Example/Cmovznz4.v`'s specs to the new constructors (the rest
waits for Phase 4) and measure its VC cost before/after: the generator must
not add per-spec case splits (§4).
- **Check:** both files compile (`keep_vo`); `valid_cmovznz4_*_param`
  still discharges, at a cost within 1.5× of before.
- **VibeWise:** paused unless a §2a.4 proposal fails.
- **while-you-wait:** live review again; compare with Phase 1 — is it still
  worth the per-tool-call overhead (§5)?
- **vibe-learn:** `/explain GenSegment.v` (a file you now know well — a good
  test of its accuracy); `/quiz`.

**Phase 3 — bridges, REWRITTEN (D24) (`Adequacy.v`, `EndToEnd.v`,
`GenProg.v`; `GenCompose.v` where it touches the spec types).** (Was
Phase 2.) Mechanics and lemma order: §2a.5. Re-prove the `gen_implpre*`/extraction lemmas and
`gen_prog_noninterferent` over the kernel types. Disjointness now comes
from the base's proof field and clear-of-code is a bridge OBLIGATION
(D19), so `data_layout_ok` shrinks to what the types do not give; `NoDup`
is over GPR keys. `RegIdx`/`reg_convert` may stay below the boundary
(D15). The bulk of the proof work. Last: price the deferred D12
correspondence proof (shallow statement data = the generator's deep specs)
on cmovznz4 (fixed sizes) and muladd (symbolic `b`), BEFORE Phase 4
commits 18 files to it.
- **Check:** these files compile (`keep_vo`); `Cmovznz4Result.v` goes
  through end to end.
- **Learning — `/reading-quiz`, explain-first mode, BEFORE starting:** on
  `EndToEnd.v`'s `gen_implpre*` bridges — you are about to have them
  rewritten, so understand what they do first.
- **VibeWise: PAUSE** for the proof grind; resume only if a design question
  surfaces (a lemma's statement, not its proof). *Landed when:* you toggled
  it at the right moments without being reminded.
- **while-you-wait:** during long compiles, try a quiz deck of the reading
  quizzes' findings (vacuity sources, the `(false, Some v)` trap, `rv_val`).
- **vibe-learn:** `/learn` at the end; `/quiz review` (shaky concepts from
  Phases 0–2 come back here — that is the spaced-repetition ledger working).

**Phase 4 — examples and Result files (+ group B).** The 18 Result files
of §1a (the three composed files are untouched) and their example data.
Shallow statements (D12) with the per-Result correspondence proof priced in
Phase 3; regions as in §1a's table; CheckScalarPtr in the base with blocks,
its disjointness proved from the parameter premise (D21); exit
`ia + 4 * length instrs` wherever the exit is the end of the code (D23);
fixed-address corollaries kept, rewritten, labelled sanity checks (D20);
group B: muladd's `set_nth` revert and the "Untracked probe" header.
Mechanical, except D21. Per-file recipe and order: §2a.6.
- **VibeWise: PAUSE** (resume for D21 if its disjointness proof raises a
  statement question). **while-you-wait:** live review of every Result
  STATEMENT (trusted) — skim the rest. **vibe-learn:** `/learn`.

**Phase 5 — REMOVED (D26, 2026-10-09).** Its subject, Q4's visible checks,
is covered by D11 (disjointness in the type), D19 (clear-of-code conjunct,
Phase 1) and D5 (parameter premises). Numbering kept so Phase 6 stays
Phase 6.

**Phase 6 — full gate, statement review, merge.** `scripts/gate.sh` (end
theorems axiom-clean: only `pure_decode`, `Base.mmioenv`). Statement diff of
every Result file: `python3 scripts/stmtdiff.py 'Result\.v$|Noninterference\.v$' <commits>`.
Update CFGVer/CLAUDE.md's trusted-surface list, file table and compile
order (the D25 front-end file; group E: also `Tables.v` register names,
which are already in statements) and grep the skills for
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
- **VC cost** (Phase 2): the generator must not add per-spec case splits.
- **Symbolic sizes** make D12's per-Result correspondence proof
  (shallow = deep) of unknown cost — priced at the end of Phase 3.
- **The branch is red from Phase 1 to Phase 4** — a light check proves only
  that phase's files; Phase 3's `Cmovznz4Result.v` is the first end-to-end
  signal.
- **Readability is the acceptance criterion**, Emiel's call (Phase 0
  sign-off), not a green build.
- **Tool friction**: VibeWise left ON through Phases 3/4 will slow proof work
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

Notes collected per phase (input for item 1):
- **Phase 0, VibeWise (2026-10-09, Emiel):** "felt like a little too much
  friction, but I think it's actually good, because I immediately noticed
  weird decisions I didn't agree on when we turned it off." Evidence: ON,
  Emiel originated most of D10/D11; PAUSED, Claude slipped in `run_at`
  derived addresses + undefined notation, rejected at once.

After Phase 6, one short session:
1. For each tool: did it earn its cost? Keep, change how it is used, or
   uninstall (`claude plugin uninstall <name> --scope local`). while-you-wait
   is the one most likely to go; vibe-learn's `/explain` routing is the open
   question.
2. Collect `/reading-quiz` feedback and revise the skill.
3. Build the merge-time comprehension gate as a hook (TODO group F) — this
   plan's Phase 6 was its manual dry run.
4. Update the `project-learning-program` memory.
