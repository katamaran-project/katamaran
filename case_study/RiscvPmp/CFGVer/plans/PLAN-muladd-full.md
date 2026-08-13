# PLAN-muladd-full — BearSSL `br_i31_muladd_small` to a whole-function end theorem

Status: **DESIGN, not started. Written 2026-08-11.** No code exists yet for any
phase below. This corrects a previous conclusion (`project-bearssl-breaking-bad`
memory, 2026-08-03) that the whole function was **out** on rv32i — that
conclusion was too hasty and is superseded by §1 below. Written while parking
`PLAN-check-scalar-full.md`'s N=32 attempt as a TODO; this is separate, new
scope, not a phase of that plan.

Audience: a later session executing one phase at a time, same convention as
`PLAN-loop-invariant.md`. Each phase ends in an explicit GATE — reach it,
report, commit, stop.

---

## §0. The target

`br_i31_muladd_small` (BearSSL `src/int/i31_muladd.c`, commit `79c060e`, the
revision the paper analysed). Target 2 of 3 from the "Breaking Bad" BearSSL
disclosure (Schneider et al., ASIA CCS'25, arXiv:2410.13489, appendix A.5.3 /
Table 11). Computes `x <- (x*2^31 + z) mod m` over a multi-limb bignum, using
31-bit limbs stored in 32-bit words (BearSSL's `i31` representation — the
32-bit-machine-oriented one, as opposed to `i62`/`m62` for 64-bit machines;
`check_scalar`'s own source file, `ec_p256_m62.c`, is that other family).

**Already landed** (`Example/BearSSLMuladd.v` / `…Result.v`,
`muladd_q_noninterferent_param`, axiom-clean, in the gate's list): the
quotient-correction step only —

```c
g = br_div(a0 >> 1, a1 | (a0 << 31), b0);
q = MUX(EQ(a0, b0), 0x7FFFFFFF, MUX(EQ(g, 0), 0, g - 1));
```

12 branch-free instructions, `g`/`a0`/`b0` all taken as GIVEN inputs (already
in registers) — this snippet never computes a product itself. The paper's
compiler-induced finding reproduces exactly here: clang 18.1.3 at every
`-O1`–`-Ofast` level turns the `MUX` into a secret-dependent `bne`; the
verified version uses an inline-asm barrier on the mask
(`__asm__("" : "+r"(v))`) so InstCombine cannot re-form the select.

---

## §1. Why "muladd full is out" was wrong, and what actually blocks it

The 2026-08-03 memory's claim: `MUL31` is a 32×32→64 multiply, rv32i has no
`mul`, so clang emits `call __muldi3` inside the per-limb loop — "not a
self-contained instruction sequence." **True as stated, but it stops one step
too early**: it never asked whether a different, still-legitimate compile
target avoids the call.

**Tested 2026-08-11** (minimal synthetic snippet, not yet the real function —
see §2 Phase 1 for why that distinction matters):

```c
uint64_t mul64(uint32_t a, uint32_t b) { return (uint64_t)a * (uint64_t)b; }
```

| target | result |
|---|---|
| `--target=riscv32 -march=rv32i` | stack frame + arg shuffle, heading into `call __muldi3` |
| `--target=riscv32 -march=rv32im` | `mul a2,a1,a0; mulhu a1,a1,a0; mv a0,a2; ret` — **4 instructions, no call** |

`mul` gives the low 32 bits, `mulhu` the high 32 bits of the exact 64-bit
product — precisely what a `uint64_t` product needs, and both are already
real, faithfully-modelled opcodes in this codebase:

- `Machine.v:235,1135,1139,1469,1616` — `execute_MUL`/`fun_execute_MUL`, a real
  `Fun` with real semantics, not a stub.
- `Base.v:239-242` — `RISCV_MUL`/`MULH`/`MULHSU`/`MULHU` AST constructors exist.
- `tools/asm_to_ast.py`'s `MUL_OPS` dict already translates all four (no `div`/
  `rem` support — note for Phase 1 if the real function ever needs those).

**The M-extension is a per-example clang target flag, not a project-wide
decision.** It doesn't touch `Machine.v` (whose semantics are unconditional)
and has zero effect on any other example's own separately-compiled instruction
list. Enabling it for just this one function costs nothing elsewhere.

**Why the 64-bit width is genuinely load-bearing here (unlike some other
`uint64_t` uses in this codebase) — and why that's fine anyway.** Multiplying
two ~31-bit limbs produces an exact result up to ~62 bits; that's not a
generous margin to narrow away (contrast whatever made `precompute`'s
`uint64_t` narrowable to 32-bit — that value never needed more than 32 bits in
practice for the parameters in play). But the only operations on that 64-bit
value in a limb-multiply-accumulate step are `&`, `>>`, `+` — bit-slicing and
addition, never a comparison:

```c
uint32_t carry = 0;
for (u = 1; u <= mlen; u++) {
    uint64_t product = (uint64_t)x[u] * (uint64_t)q + (uint64_t)carry;
    x[u]  = (uint32_t)product & 0x7FFFFFFF;   /* this limb's new value */
    carry = (uint32_t)(product >> 31);         /* carries into next limb */
}
```
(Illustrative shape, not yet the verified real source — see Phase 0.) Nothing
here reaches `formula_bool`/`formula_relop`, so it should not hit the
`secret-data-walls` comparison-on-private-data gap that blocks other
64-bit-on-32-bit cases in this project (`TODO.md`'s Botan `CT::Mask` /
`precompute` note). This is a hypothesis to confirm against the real loop
(Phase 1), not yet a verified fact.

**Side finding, not this plan's business but worth recording so it isn't
re-derived:** the same pattern one level up (64-bit limbs, 128-bit product) is
clean on a native 64-bit target (`rv64im` → `mul`+`mulhu`, same 2-instruction
shape) but NOT expressible on a 32-bit one at all — `clang --target=riscv32
-march=rv32im` rejects `__int128` outright ("not supported on this target").
So `i62`/`m62`-family functions could never get this same easy fix on this
project's rv32 target; that is a fundamentally harder problem, not attempted
here or implied by this plan.

---

## §2. Phases

### Phase 0 — get the real source (BLOCKING, do this first)

No copy of `i31_muladd.c` is available locally (checked: not in this repo, not
cached by any local package manager, no network fetch available in-session).
Everything in §0/§1 about the *whole* function beyond the already-verified
snippet is inference from BearSSL's known design style, not a verified
transcript. **Do not translate a from-memory reconstruction and call it
`br_i31_muladd_small`** — get the actual source (user-provided, or a future
session with fetch access) before writing any AST list.

GATE 0: the real `br_i31_muladd_small` body (and its `br_div`/`inner.h`
helpers) in hand, diffed against whatever this plan guessed.

### Phase 1 — confirm the compiled shape, cheaply, before writing any Rocq

Compile the REAL source with `--target=riscv32 -march=rv32im -mabi=ilp32 -O2`
and inspect (not just skim) the listing for three things, any one of which is
a stop-and-reconsider if it fails:

1. The per-limb loop uses `mul`/`mulhu` with **no** leftover `__muldi3` (or any
   other `__*di3`/`__*di4`) call anywhere in the function.
2. `br_div` (the quotient-estimate helper feeding into the already-verified
   correction step) is a `static inline` bit-trick like every other BearSSL
   helper seen so far (`GT`/`CMP`/`EQ0`/`MUX`/`EQ`/`NOT`) and actually inlines
   at `-O2` — not a real division routine that would introduce its own
   out-of-table call. §1's claim that this is "plausible given BearSSL's
   style" is NOT yet confirmed against the real function.
3. The secret-dependent-branch finding the paper reports (and this repo's
   `muladd_q` already works around) does not reappear or move to a new
   location now that the function is bigger and inlines differently under
   `rv32im` versus the snippet's own isolated compile.

If (1)–(3) all hold: proceed. If any fails: report the actual listing and
STOP — do not improvise a fix in the same sitting (same discipline as
`PLAN-check-scalar-full.md`'s own "report WHY, don't weaken the statement"
rule).

GATE 1: the real compiled listing, annotated against (1)–(3), committed as a
throwaway `.s`/comment record (mirror how other plans keep the real assembly
in a header comment).

### Phase 2 — translate + contract shape

Mechanical if Phase 1 holds. `asm_to_ast.py` already supports the needed
opcodes (§1). One simplification versus `check_scalar`: `x[]`/`m[]` are 31-bit
values in whole 32-bit words, read via `lw` — **word-granular, not
byte-granular**, so this needs only the plain `gen_contract_rel` (see
**cfgver-gen-contract**), not the `_rel_bytes`/`byte_chunks` machinery
`check_scalar` needed for its `lbu` accesses. Follow **cfgver-new-example**'s
recipe; watch for full unrolling if `mlen` is baked in as a small compile-time
constant (keep it a genuine runtime parameter, pin small values in the
CONTRACT instead — the same trap `cfgver-new-example` already documents, and
the exact trap `check_scalar_full`'s guard branches needed the same discipline
for this session).

GATE 2: instrs list translated, contract built, `vm_compute` at least runs
(statement typechecks; VC need not close yet).

### Phase 3 — measure small before committing to real size

Apply this session's own hard-won lesson directly: get a real `Qed` at a small
limb count (`mlen` = 2, then 4) before anything realistic. BearSSL P-256 needs
roughly 9 31-bit limbs for a 256-bit value (256/31 ≈ 8.26 → 9; **approximate,
confirm against the real source's own size constant in Phase 0**, don't just
trust this arithmetic). Record the doubling ratio exactly as
`PLAN-check-scalar-full.md` §4 did — do not extrapolate past two points, and
budget for the same class of scaling surprise this project has hit repeatedly
(`cfgver-executor`'s `heap_size × (α·S + β·S²)` law).

**Trap already paid for once this session, don't re-pay it:** when hand-patching
a trip-count literal across multiple registers/instructions for a small-N
probe, **grep for every occurrence of the magic constant**, not just the ones
in the obvious loop-counter spot. `check_scalar_full`'s own small-N probes
silently mis-scaled TWICE from missed literals that had been dataflow-relocated
into a different register after the value was reused for something else
(P256_N's end-pointer offset, then the declared memory footprint) — both
produced a bare `False` residual that looked structural but was purely a test-rig
bug. Expect the analogous risk here: `mlen` likely feeds more than one
instruction (loop bound, some address computation, possibly a limb-count-derived
mask), and small-N memory declarations must be sized to the SAME `mlen`, not
copy-pasted from a bigger version.

GATE 3: real `Qed` at mlen=2 and mlen=4, cost curve recorded, no residual left
open.

### Phase 4 — decide on real size / promote

Owner decision from Phase 3's numbers, mirroring
`PLAN-check-scalar-full.md` §5's own decision rule: attempt the real ~9-limb
size directly if the curve lands comfortably, otherwise treat this as
evidence for whatever the general lever of the day is (region chunks,
composed per-iteration contracts — `PLAN-loop-invariant.md` if that lands
first and generalises). Promote to a real `Example/BearSSLMuladdFull.v` +
`…FullResult.v` (mirroring `check_scalar_loop1`'s promotion) only once GATE 3
is real; keep everything before that a throwaway `ZZ*.v` probe.

GATE 4: `muladd_noninterferent_param` (or similar name — do not collide with
the existing snippet's `muladd_q_noninterferent_param`) axiom-clean, gate
green, allowlist unchanged.

---

## §3. Do NOT

- **Do not reconstruct `br_i31_muladd_small` from memory and treat it as
  ground truth.** Phase 0 is blocking for exactly this reason.
- **Do not assume `br_div` is safe to skip verifying.** It feeds the
  already-landed correction step as a given input today; the whole-function
  target needs to verify ITS compiled form too, not just trust it produces
  the right `g`.
- **Do not attempt this for the `i62`/`m62` family.** §1's side finding is
  final on that: a 128-bit product isn't expressible on this project's rv32
  target at all, let alone in 2 instructions. Different, harder problem, out
  of scope here.
- **Do not fold this into `PLAN-check-scalar-full.md`'s phase numbering.**
  Cross-reference, don't merge — different function, different paper table,
  independent of that plan's N=32 TODO.

---

## §4. Related

- `Example/BearSSLMuladd.v` / `…Result.v` — the already-landed snippet this
  plan extends.
- `project-bearssl-breaking-bad` memory — **now superseded by this plan's §1**
  on the "muladd is out" point specifically; the rest of that memory (the
  three targets, the `fun_bool_to_bits`/`SLT*` unlock, `modpow_win_full`'s
  status) still stands.
- `PLAN-check-scalar-full.md` / `PLAN-loop-invariant.md` — sibling whole-function
  efforts this plan borrows measurement discipline from.
- Skills: **cfgver-new-example** (the recipe), **cfgver-gen-contract** (word
  vs byte granularity), **secret-data-walls** (why Phase 1's "no comparison on
  the product" hope needs checking against the real loop, not assuming).
