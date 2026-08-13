# PLAN-muladd-full — BearSSL `br_i31_muladd_small` to a whole-function end theorem

Status: **Phases 0–2 DONE, Phase 3 BLOCKED (2026-08-11 same day).** GATE 1 and
GATE 2 passed, but not as originally stated — see their sections below for
what actually needed fixing. GATE 3 is NOT reached: the whole function's
`vm_compute` times out at 300s even at the smallest synthetic size, and an
isolated diagnostic (`ZZDivremProbe2.v`) shows `br_divrem`'s own loop is
almost certainly the dominant cost (67.5s for just 2 trips of that loop
alone). This corrects a previous conclusion (`project-bearssl-breaking-bad`
memory, 2026-08-03) that the whole function was **out** on rv32i for a
DIFFERENT reason (a `__muldi3` libcall) — that specific conclusion was too
hasty and is superseded by §1 below, but the function turns out to be
blocked anyway, on a genuinely different, cost-scaling axis. Written while
parking `PLAN-check-scalar-full.md`'s N=32 attempt as a TODO; this is
separate, new scope, not a phase of that plan.

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

GATE 1: **PASSED, 2026-08-11, but not as originally stated — all three checks
needed a real fix, not just confirmation.** Real source fetched from
`bearssl.org/gitweb` (official, confirmed IDENTICAL to the paper's pinned
commit 79c060e for `i31_muladd.c` and `inner.h`'s MUX/EQ/GT — checked the
file histories: neither has had a substantive commit since 2016/2017, and
the repo's real HEAD, April 2026, only touched unrelated record-handling
code. So there is no newer, hardened upstream to switch to — this IS the
current state of the library).

1. **PASSES as stated.** `mul`/`mulhu`, no `__muldi3`.
2. **FAILED as stated, fixed differently than assumed.** `br_div`/`br_devrem`
   is NOT `static inline` — it is a real function in a separate file
   (`i32_div32.c`) and compiles to a genuine `call br_divrem` under a plain
   per-file compile. Fix: `-flto` (a standard flag, no source change) DOES
   fully inline it — confirmed two ways, a single-TU compile and a real
   `-flto` compile-then-`ld.lld`-link of the four separate objects, whose
   "undefined symbol" list omits `br_divrem` while still naming
   `memmove`/`br_i31_add`/`br_i31_sub` (until those are supplied too — see
   below). `br_i31_add`/`br_i31_sub` (whose own source was ALSO not on hand —
   Phase 0's gap silently extended past `i31_muladd.c` itself — fetched the
   same way) inline the same way.
3. **FAILED, and reappeared in a NEW, unanticipated place.** The already-known
   `EQ(a0,b0)` reformation (`muladd_q`'s own finding) reproduces verbatim in
   the whole-function build. But a SECOND, previously-unseen instance showed
   up only once `br_i31_add` is inlined: its own `MUX(ctl, naw & 0x7FFFFFFF,
   aw)` per-word select is branch-free when `br_i31_add.c` is compiled
   standalone, but reforms into a real per-iteration branch once inlined into
   this specific caller — same InstCombine behaviour, a different trigger.
   Fixed with the SAME barrier `muladd_q` already uses (`opaque(v) {
   __asm__("":"+r"(v)); return v; }`), applied at every sub-MUX site
   (`q`'s two `EQ`s, `tb`'s `EQ`, `over`/`under` at the `br_i31_add`/`_sub`
   call sites, PLUS `ctl = opaque(ctl);` added inside `br_i31_add`/`_sub`
   themselves as defense-in-depth, since that is exactly where the new leak
   was). Re-verified branch-free and call-free after hardening, both ways.

**A fourth thing Phase 1 never anticipated at all:** the array-shift
`memmove(x+2, x+1, (mlen-1)*sizeof *x)` compiles to two real `call memmove`
sites — a libc dependency, since this pipeline has no libc. Fixed by
supplying a local `static inline __attribute__((always_inline))` replacement,
written as a WORD-copy loop (not the byte-copy a general memmove needs) —
sound specifically because the one call site always passes 4-byte-aligned
`uint32_t*` pointers and an exact-multiple-of-4 size, the same guarantee a
real optimised memmove's aligned fast path checks. This is what keeps §2
below's "word-granular, no `_rel_bytes` needed" claim true — it was only
true BECAUSE of this choice, not for free.

Full real compiled listing, the exact `opaque()` diff, and the standalone-
vs-inlined `br_i31_add` comparison are session transcript only, not yet
committed as a header-comment record the way GATE 1 originally asked —
TODO for whoever picks this up: transcribe into a `.s`/comment block here
before trusting this account of GATE 1 a second time.

### Phase 2 — translate + contract shape

**GATE 2: PASSED, 2026-08-11.** `asm_to_ast.py` needed ONE unforeseen fix:
its `MUL_OPS` table emits the RAW 6-argument `Base.MUL rs2 rs1 rd high
signed1 signed2` form, but `Spec.v`'s `Assembly` module (which
`Example.Prelude` pulls in) shadows `MUL` with 3-argument, per-opcode smart
constructors (`MUL`/`MULH`/`MULHSU`/`MULHU`, args `rd rs1 rs2`, no booleans).
This was never hit before because **no existing example used a multiply
instruction at all** — `zzmuladdfulln{2,4}_instrs` are the first. Fixed by
hand-editing the two `MUL ...` lines to the matching named constructor after
translation (`MULHU T3 T2 T0` / `MUL T4 T2 T0`); `asm_to_ast.py` itself is
unpatched — a future session translating another `mul`/`mulh*` program will
hit this again and should fix the tool, not re-discover this.

§2's original "word-granular, plain `gen_contract_rel`" claim holds, given
Phase 1's memmove-replacement choice above. New wrinkle §2 didn't
anticipate: `br_i31_add`/`br_i31_sub` read `a[0]` for THEIR OWN loop bound
(`m = (a[0]+63)>>5`), so `x[0]` needs the SAME pinned bit-length as `m[0]`,
not left unconstrained — confirmed the two loop-bound formulas
((`bitlen+31)>>5` for `mlen`, `(bitlen+63)>>5 − 1` trips for add/sub) agree
at bitlen=63 (mlen=2) and bitlen=127 (mlen=4). Also unanticipated: this
whole-function build spills 4 registers to ITS OWN stack frame
(`addi sp,sp,-16` + 4 `sw`/`lw`) — no existing example needed this either;
mechanically it is just a THIRD `PVBaseOff` pointer register (`X2`/`sp`)
with its own small memory region, same shape as `A0`/`A2`, not a structural
blocker.

Landed as throwaway probes: `Example/ZZMuladdFullN2.v` (mlen=2, bitlen 63)
and `Example/ZZMuladdFullN4.v` (mlen=4, bitlen 127) — full deviation
disclosure (hardening, memmove, the post-compile division-loop trip-count
patch — see Phase 3) in each file's own header comment. `vos` mode
(statement-only typecheck) passes on both. Neither is in `_CoqProject`
(matching every other `ZZ*.v` probe) — no gate impact.

### Phase 3 — measure small before committing to real size — **BLOCKED, 2026-08-11**

**The `mlen`-doubling plan does not apply as written, because `br_divrem`'s
own loop trip count (fixed at 31 by the division algorithm) does not scale
with `mlen` at all** — unlike every prior small-N probe in this project,
shrinking `mlen` does not shrink the dominant cost. Since CORRECTNESS of the
quotient is irrelevant to a noninterference proof (only branch-freedom and
public loop bounds matter), the loop count was patched to match `mlen` AFTER
compilation — a pure numeral edit to the already-compiled `li <reg>, 32`
trip-count immediates (2 sites: the dead small-modulus path's own copy, and
the live main path), verified NOT to touch the branch structure the
optimiser already committed to (re-scanned the patched region: no stray
branches). Kept as a genuine loop, not compile-time-unrolled, to preserve
loop control-flow shape per `cfgver-new-example`'s unrolling warning.

**Result: `ZZMuladdFullN2.v`'s `vm_compute` TIMED OUT at 300s**, never
reaching `solve_vc`. Isolated the suspect with a second throwaway probe,
`Example/ZZDivremProbe2.v` — JUST `br_divrem`'s loop, patched to 2 trips (44
instructions), all register/memory values left maximally unconstrained
(`PVExist`), no attempt at a real noninterference story. **`vm_compute` +
`solve_vc` together took 67.5s** before failing on an unrelated
`solve_symbase_fetch` residual (an incomplete-contract issue in this
minimal probe, not the point of the measurement). 67.5s for 2 trips of a
44-instruction loop, IN ISOLATION, with everything else in the real function
stripped away, is already most of a 300s budget — strong evidence the
division loop is the genuine, dominant cost driver (not a bug in the
surrounding contract), consistent with `cfgver-executor`'s documented
`heap_size × (α·S + β·S²)` law: this loop's body is unusually dense (28
instructions/iteration of chained XOR/AND/OR/SLL/SRL, building large
symbolic terms since nothing is pinned) compared to the flat reproducer that
law was measured on.

**Not yet done, left for whoever picks this up next:**
- A real growth curve for `br_divrem` alone (1, 2, 3, 4 trips) — only the
  N=2 point exists. Do this BEFORE re-attempting the whole function at any
  size; it is far cheaper to iterate on `ZZDivremProbe2.v` alone.
- Fixing `ZZDivremProbe2.v`'s own `solve_symbase_fetch` residual (probably
  just a missing/miscounted memory or register spec in that minimal probe —
  not investigated since the timing question was answered before this
  mattered).
- Deciding whether to pursue the reverted, audited chunk-GC fix
  (`cfgver-executor`'s "LANDED 2026-08-03" note — wait, check current
  status before trusting that word; the fix for the LEAKED HEAP CHUNK
  driving the quadratic term is real and recoverable at commit `b24d0d15`)
  as a prerequisite, since it is specifically diagnosed as turning this
  class of cost from quadratic to linear in step count.

GATE 3: NOT REACHED. No `Qed` at any `mlen`, real or synthetic. This is a
genuine blocking finding for a future session/decision, not a mistake to
fix in the same sitting.

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
- **Do not assume shrinking `mlen` shrinks the dominant cost.** `br_divrem`'s
  loop trip count is fixed at 31 by the division algorithm, independent of
  `mlen` — confirmed 2026-08-11 that it (not the `mlen`-sized loops) is the
  likely dominant cost even at a synthetically-patched 2 trips. A future
  `mlen`=2-vs-4 comparison alone will NOT reveal this; measure `br_divrem`'s
  OWN trip-count curve separately (`ZZDivremProbe2.v` is the started point).
- **Do not re-attempt the whole function at a bigger size before getting
  `br_divrem`'s own growth curve.** It is far cheaper to iterate on the
  isolated loop than to re-run the ~280-instruction whole function each time.

---

## §4. Related

- `Example/BearSSLMuladd.v` / `…Result.v` — the already-landed snippet this
  plan extends.
- `Example/ZZMuladdFullN2.v` / `ZZMuladdFullN4.v` — this session's throwaway
  whole-function probes (GATE 2, `vos`-clean, `full` mode times out — see
  Phase 3). `Example/ZZDivremProbe2.v` — the isolated `br_divrem`-loop-only
  diagnostic that produced the 67.5s/2-trips number.
- `project-bearssl-breaking-bad` memory — **now superseded by this plan's §1**
  on the "muladd is out" point specifically; the rest of that memory (the
  three targets, the `fun_bool_to_bits`/`SLT*` unlock, `modpow_win_full`'s
  status) still stands.
- `PLAN-check-scalar-full.md` / `PLAN-loop-invariant.md` — sibling whole-function
  efforts this plan borrows measurement discipline from.
- Skills: **cfgver-new-example** (the recipe), **cfgver-gen-contract** (word
  vs byte granularity), **secret-data-walls** (why Phase 1's "no comparison on
  the product" hope needs checking against the real loop, not assuming).
