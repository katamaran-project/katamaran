# PLAN-rsa — BearSSL RSA private-key operation (`br_rsa_i31_private`), noninterferent

Status: **DRAFT, 2026-10-21. Not started.** Survey (§1) done and the four
top-level decisions (§2) taken by Emiel. Phases below are proposals; each
gate is a checkpoint with Emiel before the next phase starts.

Source: BearSSL `git clone https://www.bearssl.org/git/BearSSL`, HEAD
`7bea48e` (2026-04-06). The `src/int/i31_*` and `src/rsa/rsa_i31_priv.c`
files are unchanged since the paper's pinned commit `79c060e` for every file
checked in PLAN-muladd-full GATE 1; re-check the rest in Phase 0.

---

## §0. Glossary (names this plan introduces)

- **i31 integer** — BearSSL's bignum: a `uint32_t` array whose word 0 is the
  *header* (the "encoded bit length", public in every use below) and whose
  words 1..len are 31-bit *limbs* (secret when they hold key material).
  `len = (x[0] + 31) >> 5`.
- **callee contract** — a `CFGVerifierContract` for ONE C function, entered by
  `jal ra, f` and left by `ret` (= `jalr x0, 0(ra)`). Its logic context has a
  variable `r` with `ra ↦ r` in the precondition and `cfg_exit := term_var r`.
- **call-as-block** — using a callee contract as a `BlkAnnot` on the callee's
  first instruction, so every `jal` to it is ONE block step (`sexec_block`,
  `Verifier.v:1516`: consume pre under an angelic valuation, produce post,
  resume at `subst cfg_exit`). Not yet exercised for a return address.
- **core** — `br_rsa_i31_private` from just after its second `br_i31_decode`
  call to its `ret` (§2 D2). The statement starts there.
- **hardened build** — the BearSSL sources plus `opaque()` barriers
  (`__asm__("" : "+r"(v))`) at the sites PLAN-muladd-full GATE 1 found;
  **unmodified build** — the sources as cloned.

---

## §1. Survey (2026-10-21) — what the code is

### 1.1 Call tree of the core (i31, CRT)

```
br_rsa_i31_private
 ├ br_i31_decode ×2            ← before the core (D2), not verified
 ├ br_i31_zero (=memset), br_i31_mulacc ×2, br_i31_encode ×2, memmove
 ├ br_i31_ninv31 ×2
 ├ br_i31_decode_reduce ×3  → zero, br_i31_decode → br_i31_bit_length,
 │                             br_i31_muladd_small, br_i31_rshift
 ├ br_i31_modpow_opt ×2     → br_i31_to_monty → muladd_small (len times)
 │                             br_i31_montymul (4 sites), muladd_small,
 │                             memcpy ×3, memset ×2, br_ccopy,
 │                             br_i31_from_monty → br_i31_sub ×2
 ├ br_i31_reduce            → memcpy ×2, muladd_small
 ├ br_i31_sub, br_i31_add, br_i31_to_monty, br_i31_montymul
 └ muladd_small             → br_divrem ×2, memmove ×2, br_i31_add, br_i31_sub
```

### 1.2 Compiled shape (clang 18.1.3, `--target=riscv32 -march=rv32im -mabi=ilp32 -O2`, unmodified build, per-file, no LTO)

| function | instrs | cond. branches | mul | byte ops | calls |
|---|---|---|---|---|---|
| br_i31_sub / br_i31_add | 29 / 29 | 2 / 2 | 0 | 0 | — |
| br_i31_rshift | 26 | 3 | 0 | 0 | — |
| br_i31_bit_length | 72 | 2 | 0 | 0 | — |
| br_i31_decode | 45 | 5 | 0 | 1 | bit_length |
| br_i31_decode_reduce | 107 | 5 | 0 | 1 | memset, decode×2, muladd_small×2, rshift |
| br_i31_encode | 53 | 9 | 0 | 7 | memset |
| br_i31_ninv31 | 22 | **0** | 8 | 0 | — |
| br_i31_mulacc | 66 | 4 | 2 | 0 | — |
| br_i31_montymul | 230 | 7 | 22 | 0 | memset, sub×2 |
| br_i31_to_monty | 23 | 2 | 0 | 0 | muladd_small |
| br_i31_from_monty | 75 | 4 | 5 | 0 | sub×2 |
| br_i31_reduce | 72 | 6 | 0 | 0 | memcpy×2, muladd_small |
| br_i31_muladd_small | 166 | 7 | 2 | 0 | divrem×2, memmove×2, add, sub |
| br_divrem | 50 | 1 | 0 | 0 | — |
| br_ccopy | 14 | 2 | 0 | 3 | — |
| br_i31_modpow_opt | 253 | 19 | 1 | 1 | 13 call sites |
| br_rsa_i31_private | 218 | 12 | 2 | 4 | 20 call sites |

≈1,550 instructions in 18 functions, plus memcpy/memset/memmove (§2 D3).
Reproduce: the command above with `-ffreestanding -nostdinc -isystem
$(clang -print-resource-dir)/include -isystem <stub string.h> -I inc -I src -S`;
the stub only declares `memcpy/memmove/memset/memcmp/strlen`.

### 1.3 Findings that shape the plan

1. **Every loop bound is public header data** (`m[0]`, `elen`, `twlen`,
   `xlen`) — the pinned-`x[0]` pattern muladd already uses. Only VALUES are
   secret, so loop invariants need ownership + classification only, no
   functional correctness. This is what makes the whole thing plausible.
2. **The compiler-induced leak of the paper's Table 11 is present on this
   target**: `i31_muladd.s:147`, `bne s8, s3`, is `EQ(a0, b0)` reformed into
   a branch; `b0` is the top limb of the modulus, which in RSA-private is the
   secret prime. So the unmodified build is NOT constant time on rv32im -O2,
   reached through `to_monty`, `decode_reduce`, `reduce` and `modpow_opt`.
   `modpow_opt`'s own window lookup (`-EQ(u,bits)`) and `CCOPY(NEQ(bits,0))`
   compile to `snez`, branch-free. Branches of the other functions have NOT
   been audited by hand; the verifier is the audit (a secret branch makes the
   VC fail), so this is deliberately left to the phases.
3. **Secret-data wall before the core**: the leading-zero strip
   `while (plen > 0 && *p == 0)` branches on a key byte, and
   `br_i31_decode` sets `x[0] = bit_length(limbs)`, which bounds every later
   loop. BearSSL declares these lengths "not secret"; `val_spec` has only
   `Secret | Public | Known`. Hence D2. (Inside `decode_reduce`, decode's
   secret `x[0]` is overwritten with `m[0]` before use — no wall there.)
4. **Scale**: RSA-2048 → each prime 1024 bits → 34 words; window 5 → 33
   window tables; ~205 windows × 6 `montymul`s × ~1,100 inner iterations.
   Only loop contracts parametric in the length can work; the target is ONE
   theorem for every key size (precedent: parametric-mlen muladd).
5. **Reuse is heavy** (`montymul` 5 sites, `muladd_small` ≥5, `sub` ≥6,
   `modpow_opt` 2), so inlining (`-flto`, the muladd precedent) multiplies VC
   cost. Hence D1.
6. **Stack**: `br_rsa_i31_private` keeps all bignums in one stack array
   `tmp[1 + 8U]`, `U = 2 + (BR_MAX_RSA_FACTOR+30)/31` = 70 → 561 words
   (2.2 KB); callees spill callee-saved registers to their own frames.

---

## §2. Decisions (Emiel, 2026-10-21)

- **D1 — calls: callee-as-block.** Each helper gets a callee contract, verified
  once; call sites are block steps. Spike first (S1).
- **D2 — statement starts after the second decode.** Inputs: decoded `mq`,
  `p` (i31, public header, secret limbs) at their `tmp` slots; `dp`, `dq`,
  `iq` as secret byte strings with public lengths; `x` public input bytes
  (ciphertext / message representative). The strip loops, the two `decode`
  calls and `bit_length`'s use there are out of scope, said so in the writeup.
- **D3 — finish byte memory** rather than word-loop replacements: verify the
  real byte-wise `br_ccopy`, and byte-wise memcpy/memset/memmove.
- **D4 — both builds**: show the unmodified build REJECTED (a failing VC at
  the `muladd_small` q-step), then verify the hardened build.

Defaults taken without asking (say if wrong): key size parametric (∀ length);
leakage model = current `KatamaranRel` (no MUL leak); `-O2`.

---

## §3. Open — proposals, to decide at the named gate

- **O1 (Phase 2)** — which memcpy/memset/memmove. Proposal: the textbook
  byte loops in a local `mem.c`, compiled with `-fno-builtin` so clang does
  not turn them back into calls. Alternative: picolibc's (word fast path,
  alignment branches on public pointers — more realistic, more code).
- **O2 (Phase 7)** — how the top-level statement ends. The kernel's statement
  exits at a literal address; a function returns to `ra`. Proposal: a
  2-instruction harness `jal ra, br_rsa_i31_private; <exit>` in the program
  table, so nothing in `Noninterference.v` changes.
- **O3 (Phase 1)** — callee-saved registers. NI alone needs only publicness,
  but the CALLER dereferences pointers it keeps in `s0..s11`, so the callee
  contract must pin them: `s_i ↦ v_i` in pre AND post with the same logic
  variable. Proposal: a `gen_callee_contract` wrapper over `gen_seg_contract`
  that adds `ra`, `sp`, `s0..s11` pinning and the stack frame as `Gap`-style
  owned words below `sp`.

---

## §4. Phases

Each phase records its timing rows (§5). "Light check" per phase, ONE full
gate at the end (feedback: light gates).

### Phase 0 — record the compiled shape (cheap)
- Commit a `tools/bearssl/` build script (the §1.2 command, both builds, LTO
  off), the hardening patch as a `.patch` (PLAN-muladd-full GATE 1's diff
  was never committed — reconstruct it from that section), and the `.s`
  listings of both builds.
- Extend `asm_to_ast.py` to translate a LINKED program (`ld.lld` of the
  objects, `llvm-objdump -d`), keeping function symbols as offsets, so `jal`
  targets resolve. Fix its `MUL` naming bug (PLAN-muladd-full GATE 2) while
  there.
- GATE 0: both listings committed; the unmodified/hardened diff in branches is
  exactly the known `muladd_small` sites (or the new ones are listed).

### Phase 1 — Spike S1: call-as-block (the risk everything rests on)
- Target: the real tail of `br_i31_montymul`,
  `br_i31_sub(d, m, NEQ(dh,0) | NOT(br_i31_sub(d, m, 0)))` — two calls to a
  leaf with a loop, the second call's argument depending on the first's result.
- Build: (a) callee contract for `br_i31_sub` (loop + `ret`, exit `term_var
  r`, precondition `r ∉ [base, base + 4·29)` so the exit test is decidable);
  (b) a caller segment using it twice as a block; (c) its end theorem through
  the existing bridge.
- Things this must settle: `r` instantiated angelically from `ra`; the
  exit-test decidability; whether `blkValid`/`Validity.v` accept an exit term
  that is a variable; leakage of the callee covered by its own VC.
- GATE 1: green + axiom-clean, OR a written reason it cannot work (then STOP
  and revisit D1 with Emiel — the fallback is `-flto`).

### Phase 2 — byte memory, the remaining parts (D3)
- `sb` at width 1 (`sep_contract_mem_write_value`, untested at width 1).
- Mixed width: a word array touched by `lw` in `montymul` and byte-wise in
  `br_ccopy`/memcpy. Spike S2: decide where the word⇄4-bytes view change
  happens — a ghost split/join annotation at the call site, or the callee
  contract stated over words with the split inside its own VC. Check
  `PLAN-byte-memory.md` §9 (ghost lemmas rejected there FOR LOADS; reasons may
  not carry over).
- `Layout.v` `Bytes` is rounded up to words (D22 TODO) — fine for D2's
  inputs, recheck once `encode` writes a byte-exact output.
- Callee contracts for `br_ccopy`, memcpy, memset, memmove (O1 decided here).
- GATE 2: `br_ccopy` over a word array, called from a word-accessing caller,
  end to end.

### Phase 3 — `br_i31_montymul` (riskiest loop shape)
- Three loops (outer `u`, 4-unrolled inner `v`, tail `v`), nested, 22
  `mul`/`mulhu`, a stack frame, calls to memset and `sub` ×2 (S1's result).
- Spike S3 first if not already exercised: a loop block nested inside another
  loop's body (check `PLAN-loop-rule.md` / `PLAN-loop-automation.md`; the
  merged examples have sequential loops only, as far as checked).
- GATE 3: callee contract valid, cost per VC recorded.

### Phase 4 — the Montgomery helpers + the rejection demo (D4)
- `br_divrem`, `muladd_small` as a callee (re-cut the existing D/G/I/K/M/N
  segments with add/sub/divrem/memmove as calls instead of inlined),
  `to_monty`, `from_monty`.
- Rejection demo: the unmodified `muladd_small` q-step's VC fails, with the
  failing residual recorded (expected: `secLeak` on the top modulus limb —
  see `secret-data-walls`).
- GATE 4.

### Phase 5 — `br_i31_modpow_opt` (main milestone, publishable alone)
- Six loops, nesting depth 3 in its own code once callees are blocks
  (`while` → {squaring `for i<k`, lookup `for u` → `for v`}), window table
  `33·mwlen` words walked by `base += mwlen`.
- Statement: `x`, `m` i31 with public header and secret limbs, `e` secret
  bytes with public `elen`, `m0i` secret, `tmp`/`twlen` scratch, public.
- GATE 5: `modpow_opt_noninterferent` axiom-clean, ∀ length.

### Phase 6 — remaining helpers for the core
- `ninv31` (straight line), `rshift`, `bit_length`, `decode`,
  `decode_reduce`, `reduce`, `mulacc`, `encode`, `add`.

### Phase 7 — the core (`br_rsa_i31_private` after the second decode)
- Statement design WITH Emiel first (memory picture of the `tmp` slots,
  define-before-use): O2 decided here.
- GATE 7: end theorem, axiom-clean, both builds reported (unmodified fails
  in `muladd_small`).

### Phase 8 — writeup
- The timing table (§5), the per-function VC costs, the finding of §1.3.2.

Stretch, not planned: (a) the ARM7TDMI MUL-latency model (branch
`issue/mul-latency-leak`), where BearSSL's own `BR_CT_MUL31` variant is the
expected pass and the default `MUL31` the expected fail; (b) the strip/decode
prologue with a statement for "secret, known bit length" (revisits D2);
(c) `br_rsa_i31_public` (all public — NI is trivial, not worth it).

### Rough size

≈20 callee contracts and ≈35 loop contracts (counted from the C source:
modpow 6, muladd_small ~6 segments, montymul 3, from_monty/mulacc/reduce 2
each, the rest 1). Existing per-loop VC costs for comparison: muladd loops
K (`br_i31_add`) 21.4 s / 4.94 GB, M (`br_i31_sub`) 19.2 s / 4.94 GB
(PLAN-muladd-composed). No estimate is made for authoring time — that is
what §5 is for.

---

## §5. Timing protocol and log

Emiel wants both the RUN TIME of the proofs and the TIME TO WRITE the
annotations. Per step, record:

| column | how |
|---|---|
| start / end | `date -Iseconds` at the first and last tool call of the step |
| wall | end − start, minutes |
| wait | time spent in compiles/VCs inside the step (sum of their wall) |
| authoring | wall − wait — the annotation/spec/proof-writing time |
| VC CPU / peak RSS | `/usr/bin/time -f '%U %M'` on the file's `coqc`, or rocq-mcp's reported time; RSS in GB |
| annot LOC | lines of contracts, loop specs, invariants, glue added (`git diff --stat` on the phase's files, excluding the `*_instrs` lists, which are generated) |
| attempts | failed VC/compile attempts before green |
| user | time waiting on Emiel (questions), excluded from authoring |

Caveat to state in any writeup: authoring is MY wall-clock (an LLM session),
not a human's; LOC and attempts are the more transferable measures.

### Log

| date | step | start | end | wall | wait | authoring | VC CPU / RSS | annot LOC | attempts | notes |
|---|---|---|---|---|---|---|---|---|---|---|
| 2026-10-21 | survey: prior work + clone | 18:13:32 | 18:14:50 | 1.3 | 0.1 | 1.2 | — | — | — | clone ~10 s |
| 2026-10-21 | survey: read C sources + infra | 18:14:50 | 18:17:21 | 2.5 | 0 | 2.5 | — | — | — | |
| 2026-10-21 | compile + shape table + branch audit | 18:17:21 | 18:18:52 | 1.5 | <0.1 | 1.5 | — | — | 0 | 18 files compile in seconds |
| 2026-10-21 | decisions D1–D4 | 18:18:52 | ~18:27 | ~8 | — | — | — | — | — | user time |
| 2026-10-21 | byte-memory status + write plan | ~18:27 | 18:31:02 | ~4 | 0 | ~4 | — | — | — | |
| | **planning total** | 18:13:32 | 18:31:02 | 17.5 | ~0.2 | ~9 | | | | + ~8 min user |
