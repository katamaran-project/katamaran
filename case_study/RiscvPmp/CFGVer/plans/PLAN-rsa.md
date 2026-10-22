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

**GATE 0 PASSED, 2026-10-21** (branch `issue/rsa`). Delivered:
`tools/bearssl/build.sh` (pins `7bea48e`, both variants, `.s` + `.o`),
`tools/bearssl/hardening.patch` (reconstructed from PLAN-muladd-full GATE 1's
prose: `opaque()` in `inner.h`; `q`'s two `EQ`s, `tb`'s `EQ`, `over`/`under`
in `i31_muladd.c`; `ctl = opaque(ctl)` in `i31_add.c`/`i31_sub.c`),
`tools/bearssl/listings/{unmodified,hardened}/`, and `asm_to_ast.py --objdump`
(translates `llvm-objdump -d --no-show-raw-insn` of a LINKED ELF; labels per
address; emits `<name>_<fn>_off : N`) plus the `MUL` naming fix.
Only `i31_muladd/add/sub.s` differ between the variants. Branches:
- `muladd_small` unmodified 7 → hardened 5. The two removed are BOTH secret:
  `bne s8, s3` = `EQ(a0, b0)` in the q-step (our old `muladd_q` site) and
  `beq a4, a7` (`unmodified/i31_muladd.s:185`) = `tb = MUX(EQ(nxw, mw), …)`
  in the q·m loop — the paper's own Table-11 site. So BOTH reproduce on
  clang 18 rv32im -O2. The 5 left are public (`m_bitlen == 0`,
  `m_bitlen <= 31`, `mblr == 0`, two loop edges).
- `add`/`sub`: 2 branches each in both variants (header test, back-edge);
  the barrier changes no instruction count (29 → 29).
- Link check (spike S1's program, `ld.lld --relax`): the first call became
  `jal`, the SECOND became a tail call `j br_i31_sub` — so S1 also exercises a
  callee returning to its caller's `ra`, not to the call site.

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

**Status 2026-10-21 (in progress, `issue/rsa`).** Split into S1a (harness
`[jal ra, br_i31_sub ; j _etext]` + the real hardened `br_i31_sub`, no
caller frame) and S1b (the real `rsa_spike_sub2` caller: frame, callee-saved
registers, a TAIL call). Done so far:
- Facts checked: `Machine.v`'s JALR is `pc := rs1 + sext imm` (no `& ~1`, no
  alignment check), and `is_exit` is a syntactic `Term_eqb` after `peval`, so
  a callee stops exactly at `ret` and its VC needs NO "r ∉ code" premise.
  `blockSound`/`blkValid_of_loop_contract` accept any exit term; the only
  exit-specific obligation is `etable_rel` (the exit is a SyncVal).
- `GenSegment.gen_callee_contract` (exit := the return-address term, `secLeak
  ret` put in front of `extra_pre`, defined THROUGH gen_seg_contract so its
  precondition is a segment's by conversion) and
  `GenCompose.{callee_pre_ret, blockFaithful_of_callee, blkValid_of_callee}`.
  Compiled (heavy chain rebuilt: its `.vo`s predated the 10-15 imports merge).
- `Example/Rsa/RsaSpikeSub.v`: `valid_sub_loop` (the word loop on muladd's
  LoopN template, unchanged) **green first try, 9.2 s**.
- **OPEN, blocking:** `valid_sub` (the callee VC) fails at the loop block's
  entry: the angelic match of LoopN's PRIVATE source array
  `[4 + (eX − 4·mw); T; eX]` errors for every heap alternative, although the
  heap holds `arr false 4 4 [4 + xa; T; xa + 4·mw]` (dump: the
  `DebugCFGVerifierContract` recipe, scratchpad `dbg1.log`). Found on the way:
  the solver, given `4 + (eX − 4mw) = 4 + xa`, eliminates the PARAMETER `xa`
  (`tri_cons "xa" (eX − 4mw)`) rather than the evar `eX`. Four hypotheses
  tested and REFUTED in a preamble `combined_solver` harness: `sext h` vs `h`
  (fixed anyway, muladd's spelling), refutation of the start equation, of the
  end equation, and interference from the public array's residual
  `−4(−1+mw) + (xb + 4mw) = 4 + xb` (which the solver keeps undecided).
- **ROOT CAUSE (2026-10-21 23:40, preamble harness, all checks < 0.2 s):**
  the consume itself SUCCEEDS at construction; it emits
  `assert_vareq "xa" (eX − 4·mw)` -- the solver, given
  `4 + (eX − 4mw) = 4 + xa`, cancels the shared literal 4 and eliminates the
  one bare variable, which is the callee's ∀-PARAMETER `xa`, not the
  loop's angelic `eX`.  An assert_vareq on a demonic variable survives
  `cfg_postprocess` undischarged (`∀xa ∃eX. assert_vareq xa (eX − 4h)` stays;
  the eX-oriented `assert_vareq eX (xa + 4h)` postprocesses to `block`).
  The literal 4 appears on BOTH sides because the limb count is `mw − 1`, so
  `end − 4·count = end + 4 − 4mw`.  Muladd's tail never hits this by luck of
  literals: its counts are `mlen − 3` etc., so the constants differ, nothing
  cancels, no variable is bare, and the end argument binds eX first.
  Probes: `Example/Rsa/ZZCmpMuladdI.v`, `ZZCmpSub.v` (the latter has a
  `List.app` typo, unused).
- **FIXED 2026-10-22, two independent causes** (Emiel chose the solver fix):
  1. `Solver.v`: new `formula_propeq` rule `try_isolate_inner`: `x + s = y`
     (also under a shared literal `c + l = c + r`), x and y variables, x
     INNERMOST (smaller `ctx.in_at`), `secLeakT s` ⟶ `x = y + (−1)·s`.
     A completeness rule (both orientations state the same equation); the
     `secLeakT` guard is load-bearing (RelVal never normalises NonSyncVal v v,
     so `x + s = y ⇔ x = y − s` FAILS for a secret s; `relval_isolate`).
     Two placement/form lessons, each measured: it must run BEFORE
     `try_bvadd_cancel_val_propeq` (solver_generic unifies in the same pass
     as it simplifies, so a rule on that rule's OUTPUT never sees the
     equation), and it must emit `(−1)·s`, peval's ring normal form -- `bvsub`
     survives peval and the closers as a residual.
  2. Contract: an instruction carrying a block runs the block INSTEAD of
     itself, ghosts included (`Verifier.v`, the `Some b` branch), so the done
     seeds go in `ghost_after` of index 10, not `ghost_before` of 11 --
     muladd's tail places `build_i` the same way.
- **S1a VC side GREEN:** `valid_sub_loop` 13.4 s, `valid_sub` (the callee)
  3.0 s, `valid_s1a` (the whole program, callee as a block entered by the
  real `jal`) 0.1 s, under coqc; file 40.8 s / 4.9 GB. Two negative controls
  in the file (no block ⇒ fails; a post publishing a's secret limbs ⇒
  fails). OPEN: the end theorem (Result file: `blkValid_of_callee` +
  `ValidCFGVerifierContract_intro` + a bridge with array memory), the gate
  (the solver rule fires in every example), S1b.

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
| 2026-10-21 | Phase 0 (build script, patch, listings, `--objdump`, GATE 0) | 18:34:12 | 22:37:29 | 243 | <0.5 | **not measured** | — | ~60 tool + ~70 script, 71 patch | 0 | an idle gap of unknown length (approval prompt or pause) sits inside this step; ~25 tool calls. From here on: a `date` stamp every few calls, so a gap is bounded |

| 2026-10-21 | Phase 1: read executor/soundness for calls (JALR, is_exit, blockSound, etable_rel) | 22:37:53 | 22:43:00 | 5 | 0 | 5 | — | — | — | |
| 2026-10-21 | Phase 1: `gen_callee_contract` + 3 GenCompose lemmas | 22:43:00 | 22:47:58 | 5 | 0.1 | 5 | heavy-chain rebuild 459 s wall / 356 s user / 7.4 GB (stale `.vo`s, one-off) | GenSegment +33, GenCompose +109 | 3 (name, `[%H _]` pattern, notation in `change`) | interactive checks 0.1 s each; pet OOMs replaying GenCompose to line 2300 |
| 2026-10-21 | Phase 1: S1a link + `--tables-aliases` + spike file | 22:38 | 22:51:21 | ~10 (interleaved with the above) | 0 | ~10 | deps 35 s / 4.6 GB | spike 181 lines (31 generated instrs), tool +~30 | 0 | |
| 2026-10-21 | Phase 1: loop VC | 22:57:05 | 22:57:51 | 1 | 0.15 | 0.6 | `valid_sub_loop` 9.2 s | — | 0 | green first try |
| 2026-10-21 | Phase 1: callee VC debugging (OPEN) | 22:57:51 | 23:09:42 | 12 | ~2 (2 debug compiles ~1 min each) | ~10 | VC construction ~11 s | — | 4 hypotheses refuted | stopped to report |
| 2026-10-21 | Phase 1: root cause (muladd comparison + harness) | 23:19:13 | 23:40:33 | 21 | ~14 (muladd tail rebuild + 2 probes, 23:20→23:37) | ~7 | — | probes only | 0 | waiting dominated |
| 2026-10-22 | Phase 1: explain the rule to Emiel | 07:42:40 | ~08:28 | — | — | — | — | — | — | user time |
| 2026-10-22 | Phase 1: solver rule v1 (prototype + port + build) | 08:28:27 | 08:41:17 | 13 | 5.75 (Solver.vo 345 s) | 7 | Solver.vo 345 s / 3.66 GB | Solver.v +161 | ~8 preamble attempts (Equations bullets, `&&` notation, implicit args) | prototyped under `zz_` names, all proofs checked before the build |
| 2026-10-22 | Phase 1: v1 does not fire -- diagnose, v2 (shared literal, hook before val-cancel) | 08:41:17 | 08:58:20 | 17 | 13 (deps 389 s + Solver.vo 388 s) | 4 | — | +~45 | 1 (`ring` not declared at generic width) | |
| 2026-10-22 | Phase 1: deps rebuild killed by the low-memory reaper; restarted at -j1 | 08:58:20 | 09:08:03 | 10 | ~8 | — | deps -j1 216 s / 4.9 GB | — | — | user approval in between |
| 2026-10-22 | Phase 1: still red -- 2nd cause (ghosts on a block instr are skipped), `(−1)·s` output form, v3 | 09:08:03 | 09:30:36 | 22 | 13 (debug dump 117 s, Solver.vo 365 s, deps 418 s) | 9 | `valid_sub` 6.2 s | Solver.v +~40, spike 4 lines | 2 (ARopp argument order, numeral `-1`) | |
| 2026-10-22 | Phase 1: whole-program VC + negative controls + file compile | 09:30:36 | 09:32:33 | 2 | 0.7 | 1.3 | file 40.8 s / 4.9 GB; VCs 13.4 / 3.0 / 0.1 s | spike +~70 | 0 | `valid_s1a` green first try |

Protocol amendment (2026-10-21): wall time between two stamps is only
attributable to authoring if no idle gap can hide in it, so stamp at least
every ~5 tool calls and before/after anything that may wait on approval.
