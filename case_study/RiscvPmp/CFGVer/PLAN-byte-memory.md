# PLAN-byte-memory — opt-in byte-granular data cells, for `lbu`/`sb` programs

Status: **NOT STARTED.** This document is the handoff. Every "VERIFIED" fact
below was checked against the code on 2026-08-05 with the file:line given; every
"DESIGN" claim is a proposal that has not been compiled.

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
