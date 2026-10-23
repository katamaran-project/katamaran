# PLAN-arrv — arrays whose contents are NAMED (`arrv`), replacing `arr`

Status: **DRAFT 2026-10-23, not started.** Branch `issue/rsa` (the spike
landed there: `138d2df9`, `dd9672f3`, `ab321701`; not merged, not pushed).
Part of PLAN-rsa.md Phase 2 (byte memory / mem* callees); log timings in
**PLAN-rsa.md §5** (same protocol: stamps, wait vs authoring, VC CPU/RSS,
annot LOC, attempts).

## HANDOFF — read this first

**Why this exists.** BearSSL copies whole i31 integers — a PUBLIC header
word + SECRET limbs — through memcpy/memmove/br_ccopy. `arr pub w s
[a; n; e]` carries ONE Coq-level publicness flag and hides its cell values
under ∃, so a callee's post cannot give the caller back what it knew: the
header comes back secret. Emiel's principle (2026-10-22, memory
`feedback-framing-keeps-info`): **a contract that does not need a fact must
not erase it — name the values in the post, and framing keeps the caller's
facts** (`secLeak h` stays in the path condition; the post says the copy
holds `h`).

**What already works (the spike, PLAN-rsa.md "Spike S2-arrv").**
- `Sig.v` `arrv (w : nat) (s : Z)`, args `[a; n; e; vs]`,
  `vs : list (bvec (8·w))`, precise on `[a]`; no publicness flag.
- `IrisInstanceBinary.interp_arrv`: `e = a + s·n`, `length L = length R`,
  `bv.of_nat (length L) = n` (count = length mod 2^32, so `n+1` wraps WITH
  the list), cell i = `interp_ptstomem (a + s·i) (NonSyncVal L_i R_i)` +
  range. Reads only the PROJECTIONS of vs.
- `Verifier.v` CLems + `SpecIris.v` soundness (all proved, `clemSem`
  complete): `clem_arrv_take_first` (EQUATION form: `∃ x r, … ∗
  ⌜vs = x :: r⌝`, for a variable value), `clem_arrv_take_cons` (PATTERN
  form on a syntactic `x :: r`, binds x to the caller's own term; no n≠0
  premise), `clem_arrv_add_first` (`x :: vs`), `clem_arrv_add_last`
  (`vs ++ [x]`).
- `theories/`: `peval_append` (`[] ++ t`, `(x :: t) ++ u`, `(a ++ b) ++ u`
  right-associated) and `peval_bvtake_zext` (`bvtake 8 (zext x) ~> x`:
  `lbu` then `sb`), `bv.take_zext`, `bv.leview_is_le`; all proved sound,
  self-tested.
- `Example/Rsa/RsaSpikeArrv.v`: a caller VC where a public header byte
  survives a value-contract memcpy BY FRAMING (controls: secret header,
  ∃ post → both rejected), and picolibc's real memcpy LOOP verified with
  `vs = done ++ rest` (0.40 s; controls rejected).

**Decided (Emiel).** D1 replace `arr` by `arrv` everywhere (2026-10-22),
D2 migrate DIRECTLY, no cost probe first (2026-10-23) — but record before/
after VC times per migrated file, D3 word arrays hold `list (bvec 32)`; the
word⇄byte view change at a call site goes through a new list UnOp
`bytes_of_words` with a cancelling peval rule (2026-10-23), D4 the view
change happens at the CALL SITE, callee contracts over bytes (2026-10-22).

**Next step:** Phase A, starting with the open question O1 below — ASK
Emiel before building (feedback: involve in planning; do not pick).

---

## §1. Facts the design must respect (each found the hard way)

1. **RelVal is not canonical.** `NonSyncVal v v ≠ SyncVal v`, and lifted
   `cons` is NOT injective: `cons x r = cons h ls` does not give `x = h`.
   Hence the two take forms, and hence **"an empty arrv holds `[]`" is
   UNSOUND** (`NonSyncVal [] []`). Never state it; absorb empty
   remainders instead (§3, `pad`/`join`).
2. **Publicness of a list is all-or-nothing** (`secLeak vs` iff vs is
   SyncVal), and it does NOT pass to parts by the solver: from `secLeak vs`
   and `vs = x :: r` nothing derives `secLeak x` (x could be `NonSyncVal h h`).
   A take from a PUBLIC array therefore needs its own lemma that promises
   `secLeak x ∗ secLeak r` (sound: the witness choice in
   `arrv_cons_split` picks SyncVal parts for a SyncVal list). Building up
   is fine: `secLeak` of a cons/append of public leaves is SyncVal.
3. **The solver/peval sees values only through terms.** Invariant
   equations re-establish only if both sides normalize to the same term:
   that is what `peval_append` and `peval_bvtake_zext` are for. Every new
   value-shaping lemma must come with the peval rule that makes its
   output meet the next iteration's input (and a self-test in
   `RsaSpikeArrv.v`-style concrete terms — inside PartialEvaluation's
   functor the terms are abstract, so self-tests there cannot fire on
   variables).
4. **A block's precondition must use `chunk_angelic`** for arrays whose
   address is a block variable (a plain chunk cannot search the heap).
5. **Implicit arguments are ON in `Verifier.v` and `SpecIris.v`**: a helper
   whose `w` is inferable from a later argument silently makes `w`
   implicit (give `Arguments … w …`), and helpers' list arguments become
   implicit (call with `@`).
6. **pet OOMs on `SpecIris.v` (>7.6 GB).** Prove step lemmas in PREAMBLE
   mode: `From Katamaran Require Import Base Bitvector Iris.BinaryWeakestPre
   Iris.BinaryAdequacy Iris.BinaryInstance Syntax.Predicates RiscvPmp.Base
   RiscvPmp.Machine RiscvPmp.IrisModelBinary RiscvPmp.IrisInstance
   RiscvPmp.Sig RiscvPmp.IrisInstanceBinary.` + iris proofmode, `Import
   RiscvPmpIrisBase2 RiscvPmpIrisInstance2.`, plus `Add Ring … (bv.ring_theory
   xlenbits)`; then one `rocq_compile_file` of SpecIris (~2 min).
7. **Memory.** The background-shell reaper kills long builds when RAM is
   short — and a piped `grep` loses the output, so a reaped run LOOKS like
   it built nothing (check `.vo` timestamps). Run heavy builds in the
   FOREGROUND in <10 min steps, `-j1`. A `theories/` edit costs ~15 min to
   the light chain (`Solver.v` ~6 min) + ~10 min heavy.

## §2. Scope (survey 2026-10-23)

19 non-probe files mention `arr`; none on the trusted statement surface
(`Noninterference.v`, `Layout.v` untouched — only proof-side changes):

| file | uses | what |
|---|---|---|
| `SpecIris.v` | 139 | arr step lemmas + 15 `clem_*_sound` |
| `Verifier.v` | 55 | CLem constructors + `clem_lemma` arms |
| `EndToEnd.v` | 15 | `interp_arr_intro` at program entry (~l.2239–2523) |
| `GenSegment.v` / `GenProg.v` | 10 / 1 | `DArr` data specs, LoopN-style specs |
| `IrisInstanceBinary.v`, `Sig.v`, `Contracts.v` | 8 / few / 1 | predicate, interp |
| Muladd: `MuladdParam`, `…Tail`, `…LoopN`, `…LoopD`, `…LoopDAng`, `…LoopD0` | 6–10 each | loop invariants, hand-overs |
| CheckScalar: `…Param`, `…Loop1`, `…Loop2` | 2–5 | byte loops |
| Rsa: `RsaSpikeSub`, `…Sub2`, `…Sb` | 4–10 | spikes |

CLem usage by examples: take_first 7 files, add_first 8, empty 5, drop 3,
flip 3, empty_elim 2, nonempty/add_last/lockstep/take_last 1 each;
split/join/bytes_of_words/to_bytes/of_bytes **0** (catalogue only).

## §3. The arrv lemma catalogue (old → new)

| arr lemma | arrv version | value effect | status / new machinery |
|---|---|---|---|
| take_first | `arrv_take_first` (equation) / `arrv_take_cons` (pattern) | `vs = x :: r` | DONE |
| — | `arrv_take_first_pub` | + `secLeak x ∗ secLeak r` from `secLeak vs` | NEW (§1.2) |
| add_first | `arrv_add_first` | `x :: vs` | DONE |
| add_last | `arrv_add_last` | `vs ++ [x]` | DONE |
| take_last | `arrv_take_last` (equation) | `vs = r ++ [x]` | NEW; snoc analogue of `arrv_cons_split` |
| nonempty | `arrv_nonempty` | unchanged | NEW, value-agnostic |
| empty | `arrv_empty` | `⊢ arrv a 0 a []` (needs `secLeak a`) | NEW; `[]` here is SOUND (we choose it) |
| empty_elim | `arrv_empty_elim` | gives `⌜a = e⌝` ONLY — never `vs = []` | NEW (§1.1) |
| lockstep | `arrv_lockstep` | address fact only | NEW |
| drop | `arrv_drop` | — | NEW |
| flip | `arrv_flip` | `rev vs` (`uop.rev` exists) | NEW + peval rules for rev — see O1 |
| join | `arrv_join` | `v1 ++ v2`; with n2 = 0 it is the "absorb an empty remainder" step | NEW |
| — | `arrv_pad` | `arrv a n e vs ∗ arrv b 0 c ws ⊢ arrv a n e (vs ++ ws) ∗ arrv b 0 c ws` | NEW (memcpy exit: dst gets src's empty rest) |
| split (constant k) | `arrv_split` (equation: `∃ v1 v2, vs = v1 ++ v2`) | | NEW, low priority (0 users) |
| bytes_of_words / to_bytes / of_bytes | value versions over `bytes_of_words` | words ⇄ bytes | Phase B (D3) |

## §4. Phases

Light check per phase (VCs + negative controls + the files touched build);
ONE full merge gate at the end (feedback: light gates).

### Phase A — complete the catalogue (no example changes yet)
- Answer O1 (flip) and O2 (public takes) with Emiel first.
- Add the NEW rows of §3 (except Phase B's) to `Verifier.v` + soundness in
  `SpecIris.v`, each with a 2–3-instruction VC + negative control in a
  probe on the `RsaSpikeArrv.v` template.
- Any peval rule a lemma needs (rev if O1 keeps flip) in
  `PartialEvaluation.v`, self-tested.
- GATE A: every new lemma used once in a green VC; heavy chain builds.

### Phase B — words ⇄ bytes with values (D3)
- New list UnOp `bytes_of_words : list (bvec 32) → list (bvec 8)`
  (little-endian, matching `get_word_read_ram`) and `words_of_bytes`; the
  five-file plumbing for a new UnOp is in rocq-implementation's
  `references/peval-mask-algebra.md`. peval: `words_of_bytes
  (bytes_of_words v) ~> v`, and cons/append distribution so a caller's
  `h :: ls` survives the round trip syntactically.
- Value versions of `to_bytes`/`of_bytes` (count `4n`, leftover bytes as
  their own array).
- GATE B: the v4 caller of `RsaSpikeArrv.v` redone with a WORD header + word
  limbs and a BYTE memcpy, header public after the call.

### Phase C — generators and the bridge
- `GenSegment`/`GenProg` `DArr pub …` → `∃ vs, arrv … vs ∗ (if pub then
  secLeak vs)` (or a named contract variable where a caller must refer to
  the value — decide per use, O3).
- LoopN-style loop specs (`MuladdParamLoopN.v`) over arrv.
- `EndToEnd.v`: `interp_arrv_intro` (cells → arrv with the list of their
  values: `NonSyncVal (left list) (right list)`) replacing
  `interp_arr_intro` at the three sites.
- GATE C: the two RSA end theorems (`sub_call_noninterferent`,
  `sub_call2_noninterferent`) green over arrv.

### Phase D — migrate the examples (D2: directly)
- Order: RSA spikes (small, known) → check_scalar (byte loops) → muladd
  (largest, most hand-overs). Per file: record VC CPU before (from
  PLAN-rsa §5 / the file's Time lines) and after.
- For each `arr true` site, check whether cell publicness is CONSUMED (a
  branch or address uses a cell value) — if so it needs
  `arrv_take_first_pub`; if not, plain take.
- GATE D: every migrated end theorem green.

### Phase E — delete `arr`
- Remove the `arr` constructor (`Sig.v`), `interp_arr` + its 15 step/sound
  lemmas, the 15 `clem_arr_*` constructors; grep skills
  (`cfgver-contracts` "Arrays", `cfgver-gen-contract-internals`) for every
  removed name and update them in the same commit (CLAUDE.md hygiene rule).
- GATE E = the full merge gate (`scripts/gate.sh`, `GATE_JOBS=1`,
  `GATE_PROBE_BATCH=18`, MuladdParamVC built first, last stage in the
  foreground). Watch for muladd's `t_mlen` (it spells `sext`; the
  `peval_sext` rule from Phase 1) and for any VC that relied on `append`
  or `bvtake` staying un-normalized (the two new peval rules are global).

### Then, back in PLAN-rsa Phase 2
memcpy/memset/memmove/br_ccopy FUNCTION contracts over arrv: entry seeds
(`arrv_empty` for the done arrays, `[] ++ vs ~> vs`), the `n = 0` path, exit
glue (`pad` + `join`/`empty_elim`), memmove's ROTATED ±1-stride loop
(entered at `.Lcopy`; one contract with a stride variable or two), and a
`MUX c x x ~> x` peval rule so br_ccopy keeps an equal header public under
a secret ctl.

## §5. Open questions — ASK Emiel, do not pick

- **O1 (flip).** muladd/check_scalar build DONE arrays backwards
  (`add_first` at stride −s) and then `flip` them — the different stride
  is deliberate: it gives every angelic array match ONE candidate
  (`CheckScalarParamLoop1.v` header). With values, flip = `rev vs`, which
  needs peval rules for `rev` (of cons/append/rev). Alternative: grow DONE
  arrays at their END with `add_last` at the forward stride (what the
  memcpy spike does) — no flip, no rev, but same-shape arrays make angelic
  matches ambiguous (fine at 4 arrays in the spike, 0.4 s; unmeasured at
  muladd's size). Proposal: keep the old shape where it exists (flip +
  rev), use add_last in new code; measure one muladd loop both ways if in
  doubt.
- **O2 (public takes).** `arrv_take_first_pub` as a separate lemma
  (proposal), or one lemma whose post says `secLeak vs → secLeak x ∧
  secLeak r` (needs an implication form the formula language may lack).
- **O3 (top-level values).** A top-level `DArr` value as ∃ in the
  precondition (simplest) or a named contract variable (needed only when
  the post must mention it, e.g. "the output array equals f(input)").

## §6. Log

Timings go in PLAN-rsa.md §5 (rows tagged `arrv`).
