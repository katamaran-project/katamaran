# PLAN-byte-memory — opt-in byte-granular data cells, for `lbu`/`sb` programs

Status: **§5.1/§5.2/§5.4 LANDED and §6 steps 1–3 GREEN; §5.3 (the Iris wiring)
NOT STARTED.** The go/no-go passed and BearSSL `check_scalar` loop 1 verifies at
real clang output, axiom-clean, at the real klen N = 32.

**Read §10 before anything else.** Headline finding, which changes what to do
next: the cost driver is NOT either of the two growth sources already eliminated
in this project (chunk-GC's `encodes_instr` leak, coalesce's 2^N mask term).
It is the SYMBOLIC POINTER COMPARE in clang's loop-exit test, which pushes one
undecidable path-condition formula per iteration. An ablation measures it at
**~3× of VC cost at N = 32** (2.3× end-to-end wall), and — more importantly —
removing it turns an ACCELERATING exponent into a roughly constant one (≈N^1.9).
The fix is a `bvadd` cancellation rule in the solver, which is unconditionally
sound because `bvadd` is injective.
§10 also records the two residual shapes the plan did not anticipate and one
design correction.

The original text below is left intact as the rationale record; where §10
contradicts it, §10 wins.

Every "VERIFIED" fact below was checked against the code on 2026-08-05 with the
file:line given; every "DESIGN" claim is a proposal that has not been compiled.

Read this first, then **`cfgver-gen-contract`** (the spec-list vocabulary) and
**`cfgver-memory`** (the public-memory / data-memory wiring). Both are short.
`cfgver-new-example` is the recipe for the instruction lists §6 needs.

---

## §1. The target, and the one thing it unblocks

BearSSL `check_scalar` (`ec_p256_m62.c:1610`, our `Example/BearSSLCheckScalar.v`)
indexes two 32-byte arrays:

```c
for (u = 0; u < klen; u++) z |= k[u];                          /* loop 1 */
for (u = 0; u < klen; u++) c |= -EQ0(c) & CMP(k[u], P256_N[u]); /* loop 2 */
```

Both use `lbu` — **byte** loads. Today only the loop *body* is verified
(`check_scalar_instrs`, operands already in registers, no memory at all). The
accumulator's `2^N` term wall was removed by `PLAN-coalesce.md`; byte-granular
memory ownership is what is left before either loop can be attempted.

**No example in the repo has ever used a byte load.** VERIFIED: `grep BYTE|LBU`
over `Example/` and `Tables.v` returns nothing, and `Tables.v:252-255`'s only
memory helpers are `LW`/`SW`, both hardcoded to `WORD`. So this is virgin
territory — expect first-use bugs in the `mem_read 1` path, not just plumbing.

---

## §2. The decisive constraint: do NOT touch the trusted statement surface

`mem_full_spec` is defined in **`Noninterference.v:95`**, not in `GenContract.v`,
and `noninterferent_strong` (`Noninterference.v:272`) consumes it directly.
VERIFIED. So its type appears in the *conclusion of every end theorem*. Changing
it would change what is being proved, invalidate the statements of all 13
axiom-clean end theorems, and force re-proof of `Cmovznz4` and
`KeyScheduleLoop` — the only two real examples with memory specs (VERIFIED:
`Cmovznz4.v:119,144,185`, `KeyScheduleLoop.v:111,125`; `ZZQ.v:9` is throwaway).

**And it is unnecessary, because `check_scalar`'s STATEMENT does not need byte
granularity — only its CONTRACT does.** This asymmetry is the whole design.

`get_word μ a` (`Noninterference.v:139`) is *defined* as the concatenation of
four `memory_ram μ` bytes — the trusted layer is already byte-based and words are
derived. VERIFIED. Given that:

- **`k` (32 secret bytes) → declared private.** `gen_public_addrs` keeps only
  `pub = true` (`Noninterference.v:155`) and `gen_init_mem` only `Some v`
  (`:189`), so a private unpinned cell imposes **no constraint at all** on
  μ1/μ2. Its declared granularity is *invisible* in the statement: 8 private
  words ≡ 32 private bytes. VERIFIED by inspection of those two filters.
- **`P256_N` (32 bytes of a public compile-time constant) → pinned, `Some v`.**
  As 8 words, `declare_init_memory` (`:172`) demands `get_word μ aᵢ = wᵢ`, which
  by `get_word`'s definition unfolds to exactly the 32 byte equalities. Same
  claim, in the form that already exists.

So the trusted layer stays word-granular and untouched. Only the chunks the
symbolic executor consumes have to become byte-wide.

---

## §3. Ground truth — why this is small, and where the one real gap is

Every layer from the machine semantics up to the primitive contract is already
byte-native and width-generic. **All VERIFIED:**

| layer | file:line | status |
|---|---|---|
| `fun_execute_LOAD` dispatches `BYTE → mem_read 1` (also HALF→2, WORD→4) | `Machine.v` | byte-native; `restrict_bytes_one` exists |
| `interp_ptsto` — **the primitive, one byte** | `IrisInstance.v:203` | — |
| `interp_ptstomem width` — a `Fixpoint` folding `width` × `interp_ptsto` | `IrisInstance.v:206-212` | word is a DERIVED fold |
| `sep_contract_mem_read {bytes}` — width-generic, written on `↦ₘ[ bytes ]` | `Spec.v:439` | — |
| precise-predicate table registers **both** `ptsto` (`[ty_byte]`) and `ptstomem width` | `Sig.v:360,365` | — |
| `ptstomem_bv_app` — the one-step word/byte split, **already `Qed`** | `IrisInstanceBinary.v:315` (relational) + `RiscvPmpIrisInstance.ptstomem_bv_app` (unary) | — |
| `intro_ptstomem_word{,_nonsync,2,2_nonsync}` | `Adequacy.v:643,671,714,738` | precedent for assembling words from bytes |

**The one real gap** is that width is part of the predicate index
(`MkPrecise [ty_xlenbits] [ty.bvec (width * byte)]`, `Sig.v:365`), so
`ptstomem 1` and `ptstomem 4` are *different predicates* and the symbolic chunk
matcher has no split rule. A resident `ptstomem 4 a w` cannot discharge a consume
of `ptstomem 1 a b`. The split exists only at the Iris level, where the adequacy
wiring assembles raw memory into words.

Exactly two places hardcode a width, both at the topmost (generator) layer:

- `Contracts.v:461` — `a ↦ₘ t := ptstomem bytes_per_word [a; t]`
- `GenContract.v:106` — `gen_mem_asn` emits `term_val ty_xlenbits a ↦ₘ term_val ty_xlenbits v`

The width-parameterised notation `↦ₘ[ bytes ]` already exists but is
**`Local` to `Spec.v:229`** — export it or add the twin next to `Contracts.v:461`.

---

## §4. Design — opt-in per SPEC ENTRY, not per program

DESIGN. The 4× chunk multiplier must be payable only where actually needed, so
the switch is per entry.

**Key simplification: a byte-expanded entry still describes 4 bytes at a
word-aligned address.** Only the number of chunks handed out changes, not the
layout. Consequences, all of which are why this design is cheap:

- the declaration unit stays a word ⇒ **stride stays 4** ⇒ `HDataAddrs`
  (`spec i` at `base + 4*|instrs| + 4*i`) is **unchanged**
- `gen_init_mem`, `declare_public_memory`, `declare_init_memory`, `mem_spec`,
  `gen_public_addrs` — all **unchanged**
- `check_scalar`'s 64 array bytes are **16 spec entries**, not 64. The 4× is in
  chunk count (16 → 64 chunks), not in list length.

**Two lists, same type, different contract interpretation.** Keep
`mem_full_spec` exactly as it is and add a second list of the same type whose
contract-side reading is byte-expanded:

```coq
(* trusted side, unchanged: the statement sees ONE list *)
mem_specs := word_specs ++ byte_specs

(* contract side: different builders per list *)
gen_mem_pre word_specs  ∗  gen_mem_pre_bytes byte_specs
```

Put `word_specs` first, then `byte_specs`, and keep both contiguous, so the
concatenation still satisfies `HDataAddrs`'s contiguous layout. For
`check_scalar`, `word_specs = []`.

---

## §5. Implementation, in order

### 5.1 `GenContract.v` — the byte-expanding builder (additive)

```coq
(* Expand ONE word spec into 4 byte assertions at a, a+1, a+2, a+3. *)
Definition gen_mem_asn_bytes {Σ} (s : mem_full_spec) : Assertion Σ :=
  let '(a, is_pub, opt_v) := s in
  match opt_v with
  | Some v =>   (* pinned: split the literal word into 4 literal bytes *)
      ...  (* byte i of v via bv.take/bv.drop or bv.appView *)
  | None =>     (* existential: 4 INDEPENDENT byte variables *)
      asn.exist "b0" ty_byte (... ∗ if is_pub then secLeakvar "b0" else ⊤) ∗ ...
  end.

Definition gen_mem_pre_bytes {Σ} (specs : list mem_full_spec) : Assertion Σ :=
  List.fold_right (fun s acc => gen_mem_asn_bytes s ∗ acc) ⊤ specs.
```

Use `↦ₘ[ 1 ]` (see §3 on exporting it). `ty_byte := ty.bvec byte` (`Base.v:615`).
Mind the **byte order**: `get_word` is
`app (ram a) (app (ram (a+1)) (app (ram (a+2)) (app (ram (a+3)) nil)))`
(`Noninterference.v:139`) and `interp_ptstomem` peels with
`bv.appView byte (w*byte)` (`IrisInstance.v:212`) — little-endian, lowest
address first. Get this wrong and §5.3 will not close.

### 5.2 A sibling generator (additive, zero breakage)

Adding a parameter to `gen_contract_rel` would break every call site. Define
instead:

```coq
Definition gen_contract_rel_bytes (init_addr) (reg_specs) (mem_specs)
    (byte_mem_specs) (instrs) (extra_exit_offs) (bound) (ec) (fl) := ...
```

identical to `gen_contract_rel` with `∗ gen_mem_pre_bytes byte_mem_specs` added
to the precondition. `check_scalar` is base-parametric with data after the code,
so `_rel` is the family it needs.

**Leave `gen_contract_rel` itself byte-identical.** Refactoring it to delegate to
the new one is tempting but perturbs a definition that nine `vm_compute` VC
proofs reduce through; accept the duplication.

### 5.3 `EndToEnd.v` — one Iris wiring lemma (additive)

`ImplPre` must produce the byte chunks from the word-granular
`interp_mem_with_public_memory` (`width := 4`). This is `ptstomem_bv_app`,
already proved relationally.

```coq
Lemma interp_mem_words_to_bytes `{sailGS2 Σ} μ1 μ2 specs :
  interp_mem_with_public_memory μ1 μ2 specs ⊢
  [∗ list] s ∈ specs, (four interp_ptsto chunks at s.1 .. s.1+3).
```

Then a `gen_contract_noninterferent_rel_bytes` bridge mirroring
`_rel_simple`'s premises, with `mem_specs ++ byte_mem_specs` in the conclusion.

**This fires ONCE at the wiring boundary, not per load.** That is the point of
doing it here rather than as a ghost lemma (§9).

### 5.4 `Tables.v` — an `LBU` assembler helper

`Tables.v:252` only has `LW`/`SW` at `WORD`. Add
`LBU rd rs imm := LOAD imm rs rd <unsigned> BYTE`. Check the `LOAD` field order
and which boolean is the sign flag against `Machine.v`'s `fun_execute_LOAD`
before assuming; `LW` passes `false`.

---

## §6. Acceptance criterion — do LOOP 1 first

**Loop 1 (`z |= k[u]`) is the probe, not loop 2.** It byte-loads but is *not*
term-walled (`z` occurs once, so ~32 nodes linear), so it isolates the byte
plumbing and measures driver 2 without loop 2's accumulator as a confound.
Neither loop's instruction list exists yet — produce them from real
`clang 18.1.3 --target=riscv32 -march=rv32i -mabi=ilp32 -O2` output with
`tools/asm_to_ast.py` (see `cfgver-new-example`).

Staged, cheapest first:

1. **Smallest possible byte example**: one `lbu` against one byte-expanded spec
   entry, VC discharging. This is the real go/no-go — it is the first exercise of
   `mem_read 1` in this repo.
2. **Loop 1 at N = 4, 8, 16** with byte specs. Record `vm_compute` wall, `Qed`
   wall, peak RSS, and chunk count per N. Fit the growth.
3. Extrapolate to N = 32 **before** attempting loop 2. Reference point:
   `modpow_win_full` = 122 steps / ~12-16 cells at 63 s `vm_compute` + 38 s
   `Qed`. Loop 2 full is ~416 steps against 64 chunks ⇒ steps × cells ≈ 15×
   that.
4. Only then loop 2, and only if (3) says it fits.

**Regression requirement:** `Cmovznz4` and `KeyScheduleLoop` must remain
byte-identical in statement and still discharge on their unchanged one-liners,
and the gate must stay green at 13 axiom-clean end theorems (14 if a
`check_scalar` loop lands).

---

## §7. Traps

- **`↦ₘ[ bytes ]` is `Local` to `Spec.v:229`** — invisible in `GenContract.v`.
  Export it or duplicate it; do not silently reintroduce a word-width `↦ₘ`.
- **Do NOT make `P256_N` readonly.** `↦ᵣ[bytes]`/`ptstomem_readonly` is
  `is_duplicable = true` (VERIFIED `Sig.v:340`, vs `ptstomem _ => false` and
  `ptsto => false`). Duplicable-and-never-removed-on-consume is *exactly* the
  `encodes_instr` pattern that caused the O(steps²) leak `chunk_gc` was written
  to fix (`PLAN-chunk-gc.md`). On 32 constant cells it would likely reintroduce
  it. Pinned non-readonly byte cells are the right call.
- **Discharge `valid_contract` FIRST** in any new `_noninterferent_*` bridge, by
  explicit goal number, before any bullet. `eapply` leaves metavariables shared
  across all goals and solving others first resolves them wrongly; the symptom is
  a `Qed` that **hangs** or fails with an import-dependent error, not a clean
  tactic failure. Cost a multi-hour session once. See `cfgver-gen-contract`
  ("CRITICAL") and `rocq-compile-oom` for the misdiagnosis.
- **Public *existential* word vs 4 public existential bytes.** A public unpinned
  word gives `secLeakvar` on the word; byte-expanded it gives `secLeakvar` on
  each byte. These ought to be equivalent (a word is Sync iff all its bytes are)
  but that needs a lemma. `check_scalar` does not need this case — `k` is
  private, `P256_N` is pinned — so **leave public-existential entries to the
  word builder** and only byte-expand private/pinned ones until someone proves it.
- **Byte order** — see §5.1. Little-endian, lowest address first, and both
  `get_word` and `interp_ptstomem` must agree with your split.
- `bv` traps (`lia` vs `2^32`, `cbn` unfolding `xlenbits`) → **bv-pitfalls** via
  **rocq-implementation**. Address arithmetic here is `bv.add`/`bv.of_N` heavy.
- **Build budget**: full gate ~20 min incremental, ~50 min cold, RAM-bound at
  `-j3` on a 15 GB box (`Cmovznz4` peaks 3.5 GB). Use `GATE_JOBS=2` if a browser
  is open. Do not start a second `coqc` beside a running gate — recompiling a
  dependency underneath it kills the run and looks exactly like a real failure.

---

## §8. What this does NOT fix

- **Driver 2, cells × steps.** This design *creates* a 4× chunk multiplier
  (16 → 64) and `chunk_gc` reclaims only `is_encodes_instr`
  (`Verifier.v:308`) — declared data cells stay resident and per-step cost is
  linear in heap size. **Widening `chunk_gc` to drop consumed data cells is the
  actual cost fix and is independent of this plan.** If §6 step 3 says loop 1
  already does not fit, do that first.
- **The `srl/sra by 31` masks inside `CMP`.** Already linear (2N) after
  `PLAN-coalesce.md`, and `PLAN-coalesce.md` §9 explains why collapsing them is
  not worth it: `CMP = GT(x,y) | -GT(y,x)` combines a 0/1 value with a mask, not
  two masks, so no homomorphism rule fires.
- **`sb` / stores.** Only `mem_read` is in scope here; `sep_contract_mem_write_value
  {bytes}` is width-generic too (`Spec.v:~466`) but untested at width 1.
- **HALF (2-byte) access.** The model supports it; nothing here exercises it.
  The design generalises (expand into 2 chunks) but do not build it unasked.

---

## §9. Alternatives considered and rejected

- **Change `mem_full_spec`'s type (add a width).** Rejected: it is trusted-surface
  (§2), the value type would have to become width-dependent
  (`option (Val ty_xlenbits)` → byte-indexed), and it buys nothing that §4's two
  lists do not.
- **Add a `byte_specs` parameter to the existing `gen_contract*`.** Rejected:
  breaks every call site for no benefit over a sibling definition.
- **Keep 16 word cells and split per load via a ghost lemma.** This is the
  `Lem`/`SepLemma` route — `lemma_open_ptsto_instr` (`Spec.v:645`) is the
  precedent, and `Machine.v:254` even has a commented-out width-parameterised
  `extract_pmp_ptsto (bytes : nat)`. Rejected for now on two grounds: `use lemma`
  is invoked from the **program statement** (`Machine.v:875`, inside `fun_fetch`),
  so it means editing the trusted machine model; and it pays a split/rejoin every
  iteration, trading chunk count for per-step work. Worth **measuring** against
  §4 on loop 1 if driver 2 turns out to dominate — it is the one option that
  keeps the chunk count at 16.
- **Rewrite the program to use word loads.** Rejected: `*_instrs` is trusted
  statement surface, so changing it changes what is verified — and clang emits
  `lbu` for a byte array.

---

## §10. What actually happened (2026-08-05)

### Landed

| § | What | Where |
|---|---|---|
| 5.4 | `LBU rd rs imm := LOAD imm rs rd true BYTE` | `Tables.v` |
| 5.1 | `word_byte`, `term_word_byte`, `byte_chunks`, `byte_addr_val`, `byte_addr_rel`, `gen_mem_asn{,_rel}_bytes`, `gen_mem_pre{,_rel}_bytes` | `GenContract.v` |
| 5.2 | `gen_contract_rel_bytes` | `GenContract.v` |
| — | `relval_neq_irrefl`; `relval_fetch_upper_{bare,add}` generalised | `Contracts.v` |
| 6.1 | minimal one-`lbu` probe, VC green in 1.0 s | `Example/ZZByteProbe.v` |
| 6.2 | `check_scalar` loop 1 from real clang output, N = 4/8/16/32 all green | `Example/ZZByteLoop1{Common,N4,N8,N16,N32}.v` |

`§5.3` (the `EndToEnd.v` Iris wiring) is **NOT done** — see "Next" below. So there
is a verified VC but no noninterference *end theorem* for a byte program yet, and
the gate is still at 13 axiom-clean end theorems. The `ZZ*` files are throwaway
probes, deliberately not in `_CoqProject`.

Regression requirement of §6 MET: `Cmovznz4`, `KeyScheduleLoop` and
`BearSSLCheckScalar` still discharge on their unchanged one-liners.

### The go/no-go passed on the first try, and §1's worry was unfounded

`mem_read 1` needed **no** fixes: `fun_execute_LOAD`'s `BYTE` branch,
`process_load 1` and `extend_value`'s `uop.zext 8→32` all worked as written.
§3's "one real gap" (width is part of the predicate index, so no chunk split
rule) is real, and handing out four `ptstomem 1` chunks does route around it
exactly as §4 predicted. No `secLeak`/`NonSyncVal` wall appeared on the byte path.

### Two residual shapes the plan did not anticipate

Both are in `solve_symbase_fetch`, both now fixed, both would have looked like
"the byte design doesn't work" to someone who did not read the goal.

1. **A byte access leaves an access bound with offset 1, not 4.**
   `sep_contract_mem_read`'s bound is `unsigned paddr + bytes ≤ maxAddr`
   (width-generic), but every `relval_fetch_upper_*` lemma hardcoded the word
   width 4. Fixed by making the GOAL-side offset a parameter `A`
   (`relval_fetch_upper_bare (v) (A B)`, `relval_fetch_upper_add (v) (cbv) (A B)`),
   which covers HALF (offset 2) for free. `_add` additionally needs `0 ≤ A`:
   its no-wrap step bounds `bin cbv + bin a` via `1024 - A`.
2. **A pointer-compare loop exit leaves `p+k ≠ p+k → False`.**
   clang's loop 1 exits on `bne a0, a1` with BOTH operands base-relative — not
   the counter-vs-zero shape `Example/KeyScheduleLoop.v` uses, which is why this
   never appeared before. New lemma `relval_neq_irrefl`; both `RelVal` cases are
   immediate. **Any future pointer-walking loop will hit this.**

Note what did NOT go wrong: the executor handled the base-relative pointer
compare fine, keeping `p+0x11 ≠ p+0x14` … as path-condition hypotheses per taken
iteration and discharging the byte load at each of `p+0x10 … p+0x13`.

### One design correction to §5.1

`byte_chunks` must emit each address in the executor's CANONICAL form —
`term_val <literal>` at a concrete base, `p + <single literal>` at a symbolic one.
The first version built `(p+k)+j`, which the load's computed address (folding to
`p+(k+j)`) need not match, so **only the `j = 0` chunk would ever have been
consumable**. The minimal probe passed anyway because it loads exactly one byte —
a reminder that §6.1 alone does not exercise the offsets. Hence `byte_chunks`
takes an `addr_of : N -> Term Σ ty_xlenbits` function, not a base term.

### Byte order: VERIFIED, not assumed

§5.1/§7 flagged this as the thing that would silently break §5.3. It is now
pinned by computational anchors next to `word_byte` in `GenContract.v`:
`word_byte 0 0xAABBCCDD = 0xDD` … `word_byte 3 = 0xAA`, plus reassembly
`app 0xDD (app 0xCC (app 0xBB (app 0xAA nil))) = 0xAABBCCDD`. Little-endian,
lowest address first, agreeing with `get_word` and `interp_ptstomem`.

### Measured cost — loop 1 FITS at the real N = 32

Separate file per N (so `-time` figures cannot contaminate each other), `coqc`
`/usr/bin/time`, this box. Chunk count = N (N/4 word entries × 4 bytes).

| N | chunks | `vm_compute; solve_vc` | `Qed` | wall | peak RSS |
|---|---|---|---|---|---|
| 4  | 4  | 7.30 s   | 0.54 s  | 13.8 s  | 3.06 GB |
| 8  | 8  | 11.45 s  | 1.73 s  | 19.1 s  | 3.17 GB |
| 16 | 16 | 30.07 s  | 6.99 s  | 43.3 s  | 3.59 GB |
| 32 | 32 | 143.40 s | 38.89 s | 189.1 s | 4.75 GB |

**N = 32 is the real `check_scalar` klen, and it lands in 189 s / 4.75 GB** —
lighter on RAM than `Cmovznz4` (126 s / 5.7 GB), so loop 1 is comfortably
affordable as a real example.

But the growth is **worse than quadratic and the exponent is RISING**, so do not
trust an extrapolation from these four points. Marginal cost per iteration
(`ΔVC/ΔN`) is 1.04 → 2.33 → 7.08 s, i.e. the per-step cost itself grows
super-linearly in N. Doubling-exponents `log2` of the VC ratio are 0.65 → 1.39 →
2.25. Two things grow together here — the resident chunk count (§8's driver 2)
AND the path condition, which gains one `bne` hypothesis per taken iteration —
which is the likely reason this is steeper than the pure `cells × steps` model.

### ABLATION: the dominant driver is the SYMBOLIC POINTER COMPARE, and it is removable

The rising exponent above is NOT explained by the two growth sources already
eliminated in this project. Neither covers it:

- **chunk-GC (2026-08-03)** reclaims ONLY `encodes_instr` — `gc_heap`
  (`Verifier.v:307`) is literally
  `filter (fun c => negb (is_encodes_instr c))`, and `is_encodes_instr` matches
  `chunk_user encodes_instr _` and nothing else. Declared data cells are never
  reclaimed. (This is §8, restated.)
- **coalesce/expand** killed the 2^N *term-size* blowup in the mask accumulator.
  Loop 1 has no mask accumulator — `z` occurs once per iteration — so coalesce
  is not load-bearing here at all.

Two candidate drivers were left. `Example/ZZByteCtr*.v` isolates them: identical
byte-chunk count per N and identical byte loads at an advancing symbolic address,
but the loop exits on a PINNED CONCRETE counter (`addi a4,a4,-1; bne a4,x0`, the
`KeyScheduleLoop` shape) instead of clang's pointer compare. That removes (B) and
keeps (A). The ablation body is 5 instructions to loop 1's 4, so it runs 25% MORE
steps — it is handicapped, not flattered.

**USER-CPU seconds** (the wall clock of one run was destroyed by a machine
suspend — 70 698 s wall against 27.1 s user — so CPU is the only trustworthy
column here; `CFGVer/CLAUDE.md` already says to judge on CPU/RSS, not wall):

| N | ptr VC | **ctr VC** | ptr Qed | **ctr Qed** | ptr peak RSS | ctr peak RSS |
|---|---|---|---|---|---|---|
| 4  | 7.25   | 7.25  | 0.54  | 0.57  | 3.06 GB | — |
| 8  | 11.38  | 9.23  | 1.70  | 1.61  | 3.17 GB | 3.18 GB |
| 16 | 29.87  | 16.33 | 6.80  | 5.78  | 3.59 GB | 3.57 GB |
| 32 | 142.37 | **42.78 / 45.75** | 35.13 | 27.12 / 27.43 | 4.75 GB | 5.19 GB |

N = 32 counter was measured TWICE (42.78u and 45.75u; Qed 27.12u and 27.43u) —
the first run's WALL clock was destroyed by the suspend, so it was repeated. The
~7% CPU spread between them is this box's ordinary run-to-run variance and is the
reason the shape claim below is stated as a range. Clean wall for the re-run:
81 s total, against the pointer variant's 189 s — 2.3x end to end.

Read the SHAPE, not the ~3x. Marginal VC cost per iteration:

- pointer: 1.03 → 2.31 → 7.03 s — ratios **2.24, 3.04**, clearly ACCELERATING
- counter: 0.50 → 0.89 → 1.65/1.84 s — ratios **1.79, 1.86–2.07**, roughly CONSTANT

So with (B) removed the cost is close to a fixed power law, total ≈ **N^1.9**;
with (B) present the exponent itself accelerates. That difference — not the 3x —
is why §6 step 3's "extrapolate before attempting loop 2" could not be answered
honestly from the pointer-variant numbers. Do not over-read the counter
exponent's precision: two points at 7% noise cannot distinguish N^1.85 from N^2.

`Qed` is nearly unaffected (35.1 → 27.1 s). **The two drivers hit different
phases**: (B) is a `vm_compute`/solver cost, (A) is a term-size/`Qed` cost.

**The fix for (B).** `bop.bvadd` currently gets `simplify_eq_binop_default`
(`Solver.v:822`) — no cancellation — so `bvadd p c1` vs `bvadd p c2` cannot be
decided and one formula per taken iteration enters the path condition. But
`bvadd` is INJECTIVE in each argument, so `p + c1 = p + c2 <-> c1 = c2` holds
UNCONDITIONALLY in Z/2^32 — no no-wrap side condition, unlike most bv rules.
With such a rule every iteration's branch decides on literals and (B) collapses.
Precedent for a cancellation rule on a bv operation already exists next door:
`simplify_eq_binop_bvapp'` cancels via `transparent.nat_add_cancel_l`
(`Solver.v:701-709`). Note the residual arrives as `formula_relop bop.neq`, and
`simplify_eq_relop` routes `neq`/`eq` through each other (`Solver.v:795-796`), so
check which of the two entry points to extend.

CAVEAT: the counter variant is a PROXY. It shows the headroom exists; it does not
prove the solver rule delivers it. And clang will almost certainly emit a pointer
compare for loop 2 as well, so this is not optional for loop 2 — it is what makes
loop 2's cost predictable.

Calibrating loop 2 off the counter column instead of the pointer one: ~3.25x the
steps (13 vs 4 instr/iter) and 2x the cells (64 chunks vs 32) puts it at roughly
6.5x of ~45 s ≈ 290 s of `vm_compute` under a stable steps x cells model.
Affordable. Off the pointer column it is both far worse and not extrapolatable.

### Next, in order

1. **§5.3, the `EndToEnd.v` Iris wiring** — the only thing between this and a
   14th axiom-clean end theorem. Scoping note that shortens it: for
   `PVExist` entries (all of loop 1's) you do **not** need `word_byte` at all.
   `get_word` (`Noninterference.v:139`) is *already* a nested `bv.app` of four
   `memory_ram` bytes, so `ptstomem_bv_app` (`IrisInstanceBinary.v:315`, proved,
   relational) applies three times directly to
   `interp_ptstomem (width := 4) (SyncVal a) (get_word μ a)` and yields the four
   `interp_ptsto` chunks with no subrange reasoning. `word_byte` is needed only
   for PINNED (`PVConst`) entries, where ImplPre must show
   `ram μ (a+j) = word_byte j v` from `get_word μ a = v` — provable via
   `bv.take_app` / `bv.drop_app` (`Bitvector.v:947,974`). Beware the address
   forms: `interp_ptstomem` peels with `bv.one + addr`, giving `1+(1+a)`, whereas
   the assertion says `bv.add a (bv.of_N j)` — commuting/associating those is the
   fiddly part. Do NOT try to prove the `vector_subrange`-reassembly lemma by
   `cbn`; it explodes into a multi-thousand-line `bv.view` match.
2. **§8's `chunk_gc` widening** (drop consumed data cells) is now the indicated
   cost lever, and it matters MORE for loop 2 than this measurement suggests:
   loop 2 needs 64 chunks (k *and* P256_N) against loop 1's 32, so the cells
   factor doubles on top of ~3× the steps.
3. Only then loop 2, and re-measure rather than extrapolating.
