# PLAN-arrv — arrays whose contents are NAMED (`arrv`), replacing `arr`

Status: **Phases A, B, C DONE; GATE C PASSED 2026-10-24** (both RSA end
theorems green over arrv with value tracking). **Phase D DONE 2026-10-26**
(RSA spikes, check_scalar, muladd — every example on tagged arrv, every end
theorem green; muladd restated via gen_prog_contract); **Phase D′ (the tag,
D14–D17) DONE 2026-10-26** — prediction confirmed, LoopN ≈1.13× arr warm.
Next: Phase E (delete `arr`) and the ONE full merge gate. Branch `issue/rsa` (the spike
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

D5 (2026-10-23, §5): O1 keep flip + `rev` peval; O2 no public-take lemma
(framing + the plain take suffice, §1.2 corrected and measured); O3 a
top-level `DArr` value is always a named contract variable.

D6 (2026-10-23, Phase B): of_bytes is PATTERN-form only — one new op
`bytes_of_words`; `of_bytes` matches a syntactic `bytes_of_words v` and
gives back the word array holding `v`, no leftover. No `words_of_bytes`, no
cancel rule; regrouping arbitrary bytes waits for a program that needs it.
(A "leftover of bytes_of_words v ~> []" rule would be UNSOUND: NonSyncVal
[] [] for a secret v, §1.1.)

D7 (2026-10-23): the word count. `to_bytes` gives the byte array count
`4 *ᵇ n`; `of_bytes` MATCHES `4 *ᵇ k` (and value `bytes_of_words v`) and
gives back count `k`. Byte counts are ring-normalised: `4·c` stays `4 *ᵇ c`
and a program's `slli c,2` normalises to the same term, but `4·(n+1)`
becomes `4 + 4·n` — for a word count that is a ring SUM the caller names it
(∃ c, c = n+1). AMENDED while proving it: `of_bytes` also needs
`k <u 2^30` — ·4 is not injective mod 2^32, so from count 4·k = 4·len the
word count k could be len + 2^30 (unsound without the bound; arr's byte
view had the same premise). Rejected: `m >> 2` (arr's form; `(4+4n)>>2` is not `n+1`
mod 2^32, so the caller could not use it).

D8 (2026-10-23): the op is GENERIC, `uop.regroup {σ τ} : UnOp (list σ)
(list τ)` — eval splits each `bvec m` cell into its little-endian bytes
(`bv.le_bytes`, the same `appView 8` recursion as `interp_ptstomem`) when
τ = bvec 8, and is `[]` (junk) for other type pairs. Reason: a list op with
a FIXED element type (`list (bvec 32) → list (bvec 8)`) makes Terms.v's
`Term_list_case`/`ListView` (Equations, generic σ) unbuildable — "unable
to build a covering", reproduced on a toy; a generic op fits like `rev`.
Covers every power-of-two width for free. `bytes_of_words` below means
`regroup` at σ = bvec 32.

D9–D11 (2026-10-24, Phase C, Emiel): O3 stands for TOP-LEVEL arrays too —
the bridge is CHANGED so it can name them (D9: `gen_prog_noninterferent`
fixes ι before the runs, so the array values must be chosen AFTER them);
`DArr` (and `DBytes`) are REPLACED IN PLACE, examples red until Phase D
(D10); the contract context is SPLIT `S ▻▻ V`, V = the arrays' value
variables, so no premise can mention a value — independence by typing
(D11).

D12 (2026-10-24, Phase C start, Emiel): V is POSITIONAL, not a parameter —
`DArr pub dir count (v : string)` / `DBytes pub count v` carry a NAME and
`V := data_vctx data` (one `v∷clemv_ty 4` / `clemv_ty 1` per array, list
order) is computed, so ιV is built by recursion over the data with no
premise and no default values (there is no generic inhabitant of `Val σ`,
which is what killed the membership form: a free V forces a "the arrays
enumerate V exactly" premise). `gen_data_at {S Σ} (ζ : Sub S Σ) (ν : Sub
(data_vctx ds) Σ)` so a block can point the arrays at its own variables.
Data terms are over R (was `R ▻ "a"`; no user mentioned "a"); the contract
is `@CFGVerifierContract (R ▻▻ data_vctx data)`.

D13 (2026-10-24, Gate C, Emiel): the ported spikes TRACK VALUES now, not
arr-parity ∃s: a read-only array comes back with its pre value (LoopN:
`VM = rev dM ++ rM`, a contract variable; the hand-back flips the done
array and JOINS it with the emptied source, so the post sees `rev dM ++ rM`),
only an overwritten array's value is ∃.  No secLeak inside LoopN/the callee
unless the code needs it — the caller keeps publicness by framing.

**Next step: Phase D** (state at `2d660f2f`, 2026-10-25). GREEN on the new
API: GenSegment, EndToEnd, GenCompose, GenProg, `MuladdParamLoopN.v` (arrv +
VM), `Example/Rsa/RsaSpikeSub{,2}{,Result}.v`. RED by design (D10), checked
by grep 2026-10-25:
- DONE 2026-10-25: `Example/Rsa/RsaSpikeSb.v` (green, controls rejected).
  It needed a SOLVER fix (`Solver.v` `ResimpSecLeak`, §1.2 correction):
  after a load, or with two same-shape arrays, `secLeak vs` was not
  passed to the parts of a take. The GREEN set above was rebuilt against
  it on 2026-10-25 (heavy chain incl.; both RSA Results, RsaSpikeArrv,
  the four ZZArrv probes): all green, all Fail controls still rejected,
  and every VC time UNCHANGED within noise (matched, same build:
  arr 13.2 / 2.9 s, arrv untracked 31.7 s, tracked 36.9 / 23.6 s). So
  the rule is cost-neutral and does NOT touch the open LoopN cost
  question below (RETRACTED 2026-10-26: "2.8x loop, 8.1x callee" compared
  a cold arr baseline with warm arrv VCs -- warm-vs-warm the loop is ≈3.7x,
  diagnostics/arrv-loop-cost-drivers.md; never requote). Examples
  outside this set still have not seen it (Gate D/E).
- DONE 2026-10-25: check_scalar — `CheckScalarParamLoop{1,2}.v`,
  `CheckScalar{Param,Ptr}{,VC,Result}.v`, all green. Array values are ∃
  (no post mentions them; recipe step 1). `CheckScalarParam.cs` is now a
  `gen_prog_contract` (Emiel): its end theorem is one
  `gen_prog_noninterferent` like the Ptr one, hand-written ImplPre gone;
  trusted statement unchanged. valid_l1 9.83 → 9.83 s, valid_l2 14.05 →
  17.25 s (matched).
- DONE 2026-10-26: muladd — `MuladdParamLoop{D,DAng,D0,I,K,M}.v`,
  `MuladdParamTail{,VC}.v`, `MuladdParam{,VC,Result}.v`, all green, trusted
  statement unchanged. Values ∃ throughout (no post mentions one; LoopN's VM
  is instantiated by the caller). Tags: "vm"/"vx" (the data's value names,
  D15), D's moved array "Dx", I/K/M's done arrays "Im"/"Ix" → "Km"/"Kx" →
  "Mm"/"Mx"; the tail reads every tag off the LoopN records (`hand_over L
  L'`), so caller and loops cannot drift. `sym6` is now a `gen_prog_contract`
  (Emiel; facts = b public + the code's branch conditions + the 1148 base
  bound), so `muladd_param_noninterferent` is one `gen_prog_noninterferent`
  (layout by `contig_data_layout` + `concretize_data_addrs`), hand-written
  ImplPre gone. Tail's m array no longer states `pub`: nothing in the tail
  branches on m's limbs, the caller keeps it by framing. VC CPU, matched
  cold (old arr template in `Example/Muladd/ZZLoop{I,K,M}Arr.v`):
  D 0.53 s, DAng 5.77 → 5.76, D0 8.66 → 8.89, I 17.63 → 18.65, K 13.46 →
  14.45, M 13.34 → 14.20 s (≈×1.06). Unmatched (record 2026-10-13):
  TailVC file 365 → 388 s / 7.5 → 8.1 GB; MuladdParamVC solve 483 → 366 s,
  file 657 → 533 s / 10.4 → 9.4 GB; Result 21 s / 7.7 GB.

Order (plan §4 Phase D): RsaSpikeSb → check_scalar → muladd, all DONE. Recipe, from
the RSA port (worked example `RsaSpikeSub.v`, diff `2d660f2f`):
1. `chunk_user (arr pub w s) [a;n;e]` → `clem_arrv w s t a n e vs` (tag `t`:
   the value name for a top-level array, D15; a template parameter or own
   name otherwise, D16); a value is
   a contract variable if a post must mention it, else `asn.exist`; public →
   `∗ secLeak vs` ONLY where the code itself needs it (caller frames the rest).
2. `clem_arr_<op> pub w s` → `clem_arrv_<op> w s t` (no `pub`; one tag per
   matched array, D17: `join w s t1 t2 t`, `lockstep w s t1 t2`, `pad w s t
   t'`); the old
   `drop` of an emptied source after a loop becomes `flip` + `join` when the
   array's value must come back (D13), `drop` otherwise.
3. top-level data: `DArr pub dir c "v"` (data over the contract's own ctx),
   define `CtxV := Ctx ▻▻ data_vctx data`, type the post and the record with
   it; Result files drop the `.["a" ↦ …]` from the valuation and
   `Term (Ctx ▻ "a")` annotations.
4. compile with `rocq_compile_file(…, timing=True)` (pet OOMs on example
   files; preamble mode for proof iteration) and record VC before/after.
Baselines: take them MATCHED, as `Example/Rsa/ZZArrvCost.v` does (the
HEAD~1 versions of loop/callee files compile in a probe module against the
new build as long as they use only CLems + LoopN-free contracts; a file
whose contract uses the old `DArr` cannot). Known baselines: check_scalar
VCs ~31 s total, MuladdParamVC 657 s / 10.4 GB (memory `project_compile_cost`,
`project_check_scalar_param`).

~~OPEN before muladd: arrv LoopN is 2.4× (36.6 s vs 13.0 s), its callee 7×.~~
RETRACTED 2026-10-26 (cold baseline vs warm arrv; never requote). DIAGNOSED
2026-10-26 (`diagnostics/arrv-loop-cost-drivers.md`): warm, LoopN is ≈3.7×
arr = angelic AMBIGUITY between same-shape arrays ×2.27, and the values ×1.63
ONLY BECAUSE of it (their equations sit inside the angelic choice, so 64
value ∃ survive solve_evars; with unambiguous arrays values cost ×1.00,
check_scalar Loop1). Decided (Emiel, 2026-10-26):
- **D14** `arrv w s (t : string)`: a Coq-level TAG index, ignored by the
  interpretation, so same-shape arrays are told apart as `arr`'s `pub` did.
  (Not a logic variable: a callee would bind it angelically and the
  ambiguity would come back.)
- **D15** a top-level `DArr`/`DBytes` array's tag is its value name.
- **D16** loop/callee templates take their arrays' tags as Coq parameters
  (e.g. LoopN record fields); a loop's internal done arrays get their own.
- **D17** (2026-10-26, Emiel) every lemma names the tag of EACH array it
  matches: `join w s t1 t2 t` (inputs t1, t2, result t), `lockstep w s t1
  t2`, `pad w s t t'` (each keeps its own); every single-array lemma takes
  one `t` and keeps it (flip/split/to_bytes/of_bytes included). No retag
  lemma. Supersedes this list's earlier "join/pad/lockstep: one shared
  tag", which would have made lockstep ambiguous by construction and could
  not express the RSA hand-back (`join "db" "vb" "vb"`).
**Phase D′ DONE 2026-10-26:** Sig + IrisInstanceBinary (tag ignored) →
Verifier CLems take tags (D17) → SpecIris (16 `_sound` lemmas gain tag
binders, proofs unchanged) → GenSegment `gen_data_at` (tag = value name) →
EndToEnd (two `change` patterns) / GenProg → ported examples (RSA spikes,
RsaSpikeSb, check_scalar, LoopN: four tag fields `ln_tm ln_tx ln_tdm
ln_tdx`; RSA `sub_mem ta tb`, hand-back `join "db" "vb" "vb"`;
check_scalar `"vN"`/`"vK"`, loop 1's done array `"dK"` kept through flip
into loop 2). Every Fail control still rejected; heavy chain through
GenProg and all four Result files green (each ~7.7 GB). PREDICTION
CONFIRMED (`diagnostics/arrv-loop-cost-drivers.md` §7, rig
`Example/Rsa/ZZArrvTagged.v`): surviving value ∃ 72 → 0, branch counts
back to arr's exactly, LoopN warm 9.7 s vs arr 8.6 s (≈1.13×, was ≈3.7×);
cold as shipped `valid_sub_loop` 36.9 → 14.8 s, `valid_sub` 23.6 → 3.4 s.

Then Phase E (delete `arr`, its 15 CLems and sound lemmas, skills) and the
ONE full merge gate (`scripts/gate.sh`, `GATE_JOBS=1`, MuladdParamVC built
first).

---

## §1. Facts the design must respect (each found the hard way)

1. **RelVal is not canonical.** `NonSyncVal v v ≠ SyncVal v`, and lifted
   `cons` is NOT injective: `cons x r = cons h ls` does not give `x = h`.
   Hence the two take forms, and hence **"an empty arrv holds `[]`" is
   UNSOUND** (`NonSyncVal [] []`). Never state it; absorb empty
   remainders instead (§3, `pad`/`join`).
2. **Publicness of a list is all-or-nothing** (`secLeak vs` iff vs is
   SyncVal), and it DOES pass to parts by the solver alone — no extra
   lemma. CORRECTED 2026-10-23 (the draft said the opposite, reasoning
   from projections): the take's equation is `formula_propeq`, which is
   LEIBNIZ on RelVal (`Formulas.v:155`), and a lifted op is SyncVal only
   if every argument is (`liftBinOpRV`, `TypeDecl.v:268`), so
   `cons (NonSyncVal h h) r` is NonSyncVal and cannot equal a public vs;
   the solver already has `secLeak (op t1 t2) ⊣⊢ secLeak t1 ∗ secLeak t2`
   (`simplify_secLeak`). Measured: `Example/Rsa/ZZArrvPubTake.v` — plain
   `take_first` from `arrv … vs ∗ secLeak vs` proves `secLeak x ∗ secLeak
   r` (0.05 s); secret vs rejected; non-vacuity control rejected. So
   framing keeps `secLeak vs` and the take's equation hands it to the
   parts (Emiel's O2 answer: "framing should do all the publicness").
   **CORRECTED 2026-10-25 (Phase D, RsaSpikeSb `valid_cpy`):** that held
   only by luck of tree shape. The take's `vs = x :: r` is a var-eq; the
   unifier's `wsubst` substitutes the OLDER `secLeak vs` into
   `secLeak (x :: r)` WITHOUT re-simplifying it, and a later `secLeak r` is
   then not found (assumption check is syntactic). ZZArrvPubTake passed
   because postprocess hoisted the var-eq above the older assume and
   `replay` re-assumed the substituted formula; a LOAD before the take
   (mem_read's deliberate `secLeak inv` becomes an `assert secLeak false`
   after solve_evars) blocks that hoist, and so does an angelic choice
   between two same-shape arrays (the var-eq sits inside the branch). A
   second replay fixes the first case only. FIXED in the solver:
   `solver_generic` appends the split of every `secLeak (var x)` whose x a
   unification replaced by a non-variable (`Solver.v`, `ResimpSecLeak`,
   secLeak only by decision).
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
| — | ~~`arrv_take_first_pub`~~ | — | NOT NEEDED: the plain take already gives public parts (§1.2) |
| add_first | `arrv_add_first` | `x :: vs` | DONE |
| add_last | `arrv_add_last` | `vs ++ [x]` | DONE |
| take_last | `arrv_take_last` (equation) | `vs = r ++ [x]` | DONE A (`arrv_snoc_split`) |
| nonempty | `arrv_nonempty` | unchanged | DONE A |
| empty | `arrv_empty` | `⊢ arrv a 0 a []` (needs `secLeak a`) | DONE A; `[]` here is SOUND (we choose it); `a` is bound by a later ANGELIC match |
| empty_elim | `arrv_empty_elim` | gives `⌜a = e⌝` ONLY — never `vs = []` | DONE A (control: `vs = []` rejected) |
| lockstep | `arrv_lockstep` | address fact only | DONE A |
| drop | `arrv_drop` | — | DONE A |
| flip | `arrv_flip` | `rev vs` (`uop.rev` exists) | DONE A + `peval_rev` (PartialEvaluation.v): `rev (x::t) ~> rev t ++ [x]`, `rev (a++b) ~> rev b ++ rev a`, `rev (rev v) ~> v` |
| join | `arrv_join` | `v1 ++ v2`; with n2 = 0 it is the "absorb an empty remainder" step | DONE A; NO overflow premise (count is length mod 2^32) |
| — | `arrv_pad` | `arrv a n e vs ∗ arrv b 0 c ws ⊢ arrv a n e (vs ++ ws) ∗ arrv b 0 c ws` | DONE A (memcpy exit). Needs w ≥ 1 (pre is False at w = 0): soundness bounds the LENGTH by pigeonhole (`interp_arrv_length`: disjoint in-range cells) so count 0 ⇒ length 0 (`interp_arrv_count0`) — Emiel's choice over an exact count |
| split (constant k) | `arrv_split` (equation: `∃ v1 v2, vs = v1 ++ v2`) | | DONE A (`arrv_app_split`) |
| bytes_of_words / to_bytes / of_bytes | value versions over `bytes_of_words` | words ⇄ bytes | Phase B (D3) |

## §4. Phases

Light check per phase (VCs + negative controls + the files touched build);
ONE full merge gate at the end (feedback: light gates).

### Phase A — complete the catalogue (no example changes yet)
- O1/O2 answered (§5).
- Add the NEW rows of §3 (except Phase B's) to `Verifier.v` + soundness in
  `SpecIris.v`, each with a 2–3-instruction VC + negative control in a
  probe on the `RsaSpikeArrv.v` template.
- Any peval rule a lemma needs (rev if O1 keeps flip) in
  `PartialEvaluation.v`, self-tested.
- GATE A: every new lemma used once in a green VC; heavy chain builds.
- **Status 2026-10-23:** all 10 lemmas in `Verifier.v` + `SpecIris.v`
  (`clemSem` complete); probe `Example/Rsa/ZZArrvCatalogue.v`: one VC per
  lemma + a negative control each (swapped value order, no ghost, secret
  vs, `vs = []` after empty_elim) + `peval_rev` self-test, all as expected.
  The probe uses plain `cfg_vc`: in a LOOP VC the exit-or-head disjunction
  hides the seed's angelic `a = p` from postprocessing (`mb_search` has no
  ∃ case) — a probe artifact, not a lemma problem.
  Proof traps met: `lia` fails on `length`s whose hidden type index
  differs (use `Nat.add_cancel_r` / `f_equal`); `ring` refuses goals
  typed at `Val ty_xlenbits` (state a `bv xlenbits` ring lemma, rewrite);
  `Set Implicit Arguments` in SpecIris makes helper list args implicit
  (call with `@`).

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
- **Status 2026-10-24:** DONE as decided in D6–D8 (the bullets above are the
  pre-decision sketch: no `words_of_bytes`, no cancel rule, no leftover
  array). `uop.regroup` (UnOps/Terms/Solver/Bitvector `bv.le_bytes`),
  `clem_arrv_to_bytes` / `clem_arrv_of_bytes` (with `k <u 2^30`, see D7's
  amendment), soundness in SpecIris (`arrv_cell_bytes`: a k-byte cell IS
  its le_bytes byte cells, by induction on k; `arrv_words_bytes`, both
  directions). GATE B probe `Example/Rsa/ZZArrvWords.v`: `valid_w` 4.6 s
  (a public header WORD survives a BYTE memcpy), controls secret-h and
  no-bound rejected, to_bytes;of_bytes round trip is the identity.

### Phase C — generators and the bridge

**Design (D9–D11, 2026-10-24) — supersedes the bullets below where they differ.**
- `data_spec S V`: counts, addresses, anchors, pointers and cell terms are
  `Term S`; `DArr pub dir count (v : vIn)` and `DBytes pub count (v : vIn)`
  name their VALUE by a variable of V (`v∷clemv_ty 4 ∈ V`, resp.
  `clemv_ty 1`). `gen_data_at` works at `S ▻▻ V`, weakening the S terms;
  an array is `arrv … (term_var v) ∗ (if pub then secLeak (term_var v))`.
  ArrDown's value lists cells from the TOP (descending addresses).
- `concretize_data`/`data_ok` read only `ιS` — unchanged in meaning.
- Bridge: `gen_prog_noninterferent` keeps `ι : Valuation S`; inside the runs
  it builds `ιV := data_vals ι off data μ1 μ2 : Valuation V` (each value
  `SyncVal L` if both runs' lists agree, else `NonSyncVal L R`; a public
  array's lists agree by HpubMem, so its secLeak holds) and runs the
  executor at `ι ▻▻ ιV`. Premises other than `valid` are about ιS only.
- `EndToEnd.gen_implpre_data` → arrv: an `interp_arrv_intro` from the cells
  (public cells via `ptstomem_sync_is_nonsync`), down-arrays by
  `interp_arrv_add_first` induction, byte arrays by `arrv_words_bytes`
  then a take of the first `count` bytes (value `firstn`).
- Users to port: GenSegment, GenProg, EndToEnd (+ Adequacy's data_spec
  mention), RsaSpikeSub/Sub2(+Result), MuladdParam(+Result),
  CheckScalarParam/Ptr(+Result).

Original sketch:
- `GenSegment`/`GenProg` `DArr pub …` → `arrv … vs ∗ (if pub then
  secLeak vs)` with `vs` a NAMED contract variable (O3).
- LoopN-style loop specs (`MuladdParamLoopN.v`) over arrv.
- `EndToEnd.v`: `interp_arrv_intro` (cells → arrv with the list of their
  values: `NonSyncVal (left list) (right list)`) replacing
  `interp_arr_intro` at the three sites.
- GATE C: the two RSA end theorems (`sub_call_noninterferent`,
  `sub_call2_noninterferent`) green over arrv.
- **Status 2026-10-24: DONE, GATE C PASSED.** As designed (D9–D12), plus:
  `gen_data_at {S Σ} ζ a ds ν`; `EndToEnd.data_vals` (public array =
  `SyncVal` of run 1's list, secret = `NonSyncVal L R`; down = `rev`, bytes =
  `firstn count` of `le_bytes`), `data_cells_arrv{,_down,_bytes}` (down by
  `interp_arrv_flip`, bytes by `interp_arrv_to_bytes` + `big_sepL_take_drop`),
  `gen_implpre_data` re-proved for ζ/ν; the five `arr` data helpers deleted
  (dead). `gen_prog_noninterferent` builds ιV after the intros and runs the
  core at `ι ►► ιV`. LoopN (D13) tracks m's value (`VM = rev dM ++ rM`),
  hand-back flip + join. RsaSpikeSub/Sub2 ported (`sub_mem_out`: a ∃, b keeps
  `vb`), new control: a claimed unchanged is rejected. Traps: GenSegment's
  `gen_prog_contract` HANGS coqc (>10 min, pet OOM) without `#[local]
  Existing Instance asn.sub_assertion` — an unresolved `Subst Assertion`
  instance search; `Set Implicit Arguments` in EndToEnd makes `k m` of
  `data_cells_arrv_bytes` implicit; the goal's `inst` carries a different
  instance than an `Ha : inst a ι = …` (rewrite fails) — restate with
  `pose proof (Ha : A = _)` at the goal's own term `A`.
- **Cost (Emiel: accept for now, 2026-10-24).** `valid_sub_loop` 13.0 →
  36.6 s, `valid_sub` 3.2 → 22.4 s, `valid_s1a` 0.1, `valid_sub2` 6.8 → 6.7,
  `valid_s1b` 0.3 (matched baseline: old arr LoopN/callee in the same build,
  `Example/Rsa/ZZArrvCost.v`, 13.0 / 3.2). Ablation: arrv LoopN WITHOUT the
  VM equation 30.7 s — value tracking is ~6 s, arr→arrv itself 2.4×
  (RETRACTED 2026-10-26: cold-vs-warm; ≈3.7× warm). Suspected (CONFIRMED
  2026-10-26, diagnostics/arrv-loop-cost-drivers.md): no `pub` index, so
  same-stride angelic matches (two `take_first`s, four arrays at the latch,
  flip/join) branch the VC.

### Phase D — migrate the examples (D2: directly)
- Order: RSA spikes (small, known) → check_scalar (byte loops) → muladd
  (largest, most hand-overs). Per file: record VC CPU before (from
  PLAN-rsa §5 / the file's Time lines) and after.
- An `arr true` site becomes `arrv … vs ∗ secLeak vs`; takes stay plain
  (§1.2: the parts come out public).
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

## §5. Open questions — ANSWERED 2026-10-23

- **O1 → keep flip + rev** (the proposal): old shapes keep `add_first` at
  −s + `arrv_flip` with peval rules for `rev`; new code uses `add_last`.
- **O2 → neither option; framing does it.** Emiel: "this should be solved
  in a principled way, such that framing does all the publicness stuff".
  It already is — §1.2 was wrong; no `_pub` lemma, no conditional post.
- **O3 → always a named contract variable** for a top-level `DArr`'s value
  (uniform; posts can always refer to it).

The original questions, for the record:

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
