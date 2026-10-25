# PLAN-rsa — BearSSL RSA private-key operation (`br_rsa_i31_private`), noninterferent

Status: **IN PROGRESS on branch `issue/rsa` (not merged, not pushed).**
**2026-10-23: Phase 2 is paused on `plans/PLAN-arrv.md` (arrays with named
values replace `arr`) — read that plan's HANDOFF next.**
Phase 0 done; Phase 1 CLOSED (2026-10-22: spikes S1a and S1b end to end,
axiom-clean; GATE 1 closed on light checks by Emiel, merge gate deferred to
the end of the plan). Next: Phase 2. Survey (§1), decisions (§2), phases (§4), timing log (§5).

## HANDOFF (2026-10-22, end of day) — read this first

**Where things stand: Phase 1 is CLOSED.** Both call-as-block spikes are
verified end to end and axiom-clean (last commit `bbbba2ad`). Emiel closed
GATE 1 on the light checks (VCs + negative controls + end theorems +
`Print Assumptions`) and said NOT to run the merge gate for it; the gate
last ran at `4af3dd9e`, before the S1a/S1b Result files and the
`peval_sext` rule. It runs once at the end of the plan (feedback: light
gates) — if a muladd VC breaks there, suspect a contract term that spells
`sext` (`t_mlen`), see the rule below.

| file | what | cost |
|---|---|---|
| `Example/Rsa/RsaSpikeSub.v` | S1a, light: `[jal ra, br_i31_sub; j end] ++ br_i31_sub` (31 instrs). `valid_sub_loop` (LoopN), `valid_sub` (function, exit `r`), `valid_s1a` (whole program, `gen_prog_contract`); 2 negative controls | 29 s user / 4.9 GB; VCs 13.9 / 2.9 / 0.1 s |
| `Example/Rsa/RsaSpikeSubResult.v` | S1a, heavy: `sub_loop_valid` → `sub_valid` → `s1a_valid` → `sub_call_noninterferent` (∀ h; a, b's limbs anywhere disjoint). Also `limbs`, `limbs_bv`, `data_layout_cell_cons` (reused by S1b) | 19 s / 7.5 GB |
| `Example/Rsa/RsaSpikeSub2.v` | S1b, light: `[jal ra, sub2; j end] ++ rsa_spike_sub2 ++ br_i31_sub` (51 instrs). `valid_sub2` (non-leaf function: frame, s0–s2 pinned, `br_i31_sub` a block entered twice, the 2nd a TAIL call), `valid_s1b`; 2 negative controls | 38 s / 5.0 GB; VCs 6.8 / 0.3 s |
| `Example/Rsa/RsaSpikeSub2Result.v` | S1b, heavy: `sub2_valid` → `s1b_valid` → `sub_call2_noninterferent` (∀ h; a, b, the stack frame anywhere disjoint) | 22 s / 7.5 GB |

All four are in `_CoqProject`; both Result files are in `Results.v` and in
`scripts/gate.sh`'s `AXIOM_CLEAN_THMS`.

**The function-contract recipe these establish** (also in skill
cfgver-gen-contract-internals, "The segment generator"):
- a function is `gen_seg_contract_at q q (term_var "r") code fl regs
  (secLeakvar "r" ∗ pre) post` with `X1 ↦ᵣ r` in pre and post; valid by
  `blkValid_of_seg_at` + `seg_exit_sync_pub`; it is a block on its first
  instruction in every caller (typed `MkBlkAnnotV blk valid` in the
  caller's annotation, as in the Result files);
- a NON-LEAF function's `code` is itself AND its callees as linked (a
  block's table must hold every pc the run reaches);
- pin `sp`, `s_i` to the SAME logic variable in pre and post; own the frame
  as `gen_data_at (t_add sp (-k)) [DCell Secret; …]` so a whole-program
  `gen_prog_contract` with `DPtr (sp − k)` + the same cells hands it over;
- the top level is ALWAYS `gen_prog_contract` (pointer args `PVVar`, arrays
  `DPtr`/`DCell (Known h)`/`DArr`), so the end theorem is one
  `gen_prog_noninterferent`; its proof is the Result files' template
  (pointer facts `Hxa`/`Hxb`/`Hf`, `Hc` the limb count, cells by
  `perm_of_eq`, layout by `data_layout_cell_cons` + `data_layout_runs`).

**Framework added on this branch** (all used by the spikes):
`Solver.v` `try_isolate_inner`; `GenSegment.gen_seg_contract_at` (the ONE
generator, exit a term); `GenCompose.blkValid_of_seg_at` +
`seg_exit_sync_off/pub`; **`PartialEvaluation.peval_sext`** (+ `width_cast`,
`bv.sext_same`/`unsigned_sext_same` in `Bitvector.v`): `peval` drops a
same-width `sext`. Every RV32 `lw` yields `sext v` at 32→32 (Machine.v
`extend_value`); without the rule a reloaded `ra` misses the syntactic exit.

**Tooling.** `tools/bearssl/build.sh <BearSSL checkout> <out>` (clone
BearSSL into the scratchpad, pinned `7bea48e`); `tools/bearssl/spike/`
(`harness_sub.s`, `harness_sub2.s`, `sub2.c` — compile `sub2.c` with
build.sh's CFLAGS against a hardened tree: copy `inc/`+`src/`, apply
`hardening.patch`); link `ld.lld --relax -Ttext=0 harness … callees…`,
`llvm-objdump-18 -d --no-show-raw-insn`, `asm_to_ast.py --objdump
--tables-aliases --name <x>`. Exact recipe: the header comments of
`RsaSpikeSub.v` / `RsaSpikeSub2.v`.

**Next step — Phase 2 (byte memory, D3), §4.** Concretely, in order:
1. ~~Ask Emiel O1~~ DONE 2026-10-22: picolibc 1.8.12's `-Os` RISC-V
   assembly (§3 O1, `tools/bearssl/picolibc.sh`).
2. ~~`sb` at width 1~~ DONE 2026-10-22, NO framework change:
   `Example/Rsa/RsaSpikeSb.v` (light) — memset's body (`sb; addi`) into a
   secret and into a public `arr _ 1 1` (take_first / store / add_first),
   memcpy's body (`lbu; sb`) between two PUBLIC stride-1 byte arrays (the
   angelic `arr` match copes with two same-shape candidates); VCs 0.08 /
   0.04 / 0.10 s, file 15.9 s user / 4.7 GB. Controls: secret byte → public
   array rejected; secret source → public destination rejected; both green
   VCs fail with `p ≠ p` / `d ≠ d` added to the post (not vacuous). Trap:
   a post `arr true` after a secret store is NOT a secrecy control —
   `arr true`/`arr false` are different predicates, it fails on the name.
3. Spike S2. **Decided (Emiel, 2026-10-22):** (a) the word⇄bytes view
   change happens AT THE CALL SITE (callee contracts over bytes; the
   `clem_arr_to_bytes`/`of_bytes` regroup ghosts around the call; §9's
   rejection was about `SepLemma`s in trusted `Machine.v`, not proof-side
   `AnnotCLemma`s). (b) Mixed publicness: every copy moves a PUBLIC header
   word + SECRET limbs, and `arr` has one flag. Emiel: framing should keep
   what the caller knew — a callee that does not need publicness must not
   erase it — so arrays carry their VALUES and a contract's post names
   them (no ∃): **`arrv`**, which will REPLACE `arr` (Emiel's choice), via
   a spike first, then a plan. See "Spike S2-arrv" below.
4. ~~Write the `arrv` plan~~ DRAFTED 2026-10-23: **`plans/PLAN-arrv.md`**
   — the migration arr → arrv in phases A–E (catalogue, words⇄bytes,
   generators + bridge, examples, delete arr). Start there; its O1–O3 go to
   Emiel first.
5. GATE 2 (§4): `br_ccopy` over a word array, called from a word-accessing
   caller, end to end — a Result file on the S1b template.

**Spike S2-arrv (2026-10-22/23) — VC side DONE, Iris side OPEN.**
- `Sig.v` `arrv (w : nat) (s : Z)`, args `[a; n; e; vs]`,
  `vs : list (bvec 8w)`, precise on `[a]`. `IrisInstanceBinary.interp_arrv`:
  cell i holds `NonSyncVal l_i r_i` of the two runs' lists, lengths = n.
  It reads only PROJECTIONS of vs, so the non-canonical `NonSyncVal v v`
  means the same as `SyncVal v` — required, because lifted `cons` is NOT
  injective (`cons x r = cons h ls` does not give `x = h`), and a lemma
  like "an empty arrv's value is nil" would be UNSOUND (`NonSyncVal [] []`).
- `Verifier.v` CLems (light): `clem_arrv_take_first` (by EQUATION, for a
  variable value: `∃ x r, … ∗ ⌜vs = x :: r⌝`), `clem_arrv_take_cons` (by
  PATTERN on a value that is syntactically `x :: r`, so `x` is bound to
  the caller's term; no `n≠0` premise — the length gives it),
  `clem_arrv_add_first` (`x :: vs`), `clem_arrv_add_last` (`vs ++ [x]`).
  Helpers `clemv_ty`/`clemv_ctx`/`clem_arrv(_angelic)`/`clem_ptsto`/
  `clem_nonzero`; `Verifier.v` has implicit arguments ON, so each helper
  needs `Arguments … w …` or `w` silently becomes implicit.
- `theories/`: `bv.leview_is_le` (`leview m (m+k) = is_le k`, by induction
  — `leview` with a non-variable index cannot be destructed) and
  `bv.take_zext`; `PartialEvaluation.peval_bvtake_zext` (`bvtake 8 (zext x)
  ~> x`: `lbu` then `sb` stores the byte it loaded) and `peval_append`
  (`[] ++ t`, `(x :: t) ++ u`, `(a ++ b) ++ u` right-associated; two values
  still fold), both proved sound with no NonSyncVal split (same leaves).
  The old general `peval_bvtake` stays unwired.
- `Example/Rsa/RsaSpikeArrv.v` (light), all green, file 44 s user / 4.9 GB:
  **v4** `valid_cl` — a public header byte h joined onto secret limbs ls
  (`add_first` → `h :: ls`), memcpy as a block with the VALUE contract
  `src ↦ vs ∗ dst ↦ ws ⊢ src ↦ vs ∗ dst ↦ vs` (a stand-in body), then
  `take_cons` on the destination: its first cell holds `h`, public by the
  FRAMED `secLeak h`. Controls: h secret → rejected; memcpy post with an
  ∃ value → rejected. **v3** `valid_mc_loop` — picolibc's real memcpy loop
  (`lbu; sb; addi ×3; bnez`) as a loop VC with invariant src = done ++
  rest, dst = done ++ old, `vs = done ++ rest`; 0.40 s, green FIRST try
  once the two peval rules existed. Controls: `vs = rest ++ done` in the
  post → rejected; post ∗ `s ≠ s` → rejected. Self-test: `peval`
  re-associates `(d ++ [x]) ++ r` to `d ++ (x :: r)` under vm_compute.
- Traps found: a BLOCK's precondition must use `chunk_angelic` for arrays
  whose address is a block variable (a plain chunk cannot search the heap);
  the stock `solve_mb_vc` already finds `take_cons`'s witnesses (cbn turns
  `cons ?x ?r = cons h ls` into a Coq unification).
- **Soundness DONE (2026-10-23):** `SpecIris.v` step lemmas
  `interp_arrv_take_first/_take_cons/_add_first/_add_last` (big_sepL
  cons/snoc over `zip`; `arrv_cons_split` picks SyncVal parts for a SyncVal
  list) + the 4 `clem_arrv_*_sound` + `clemSem` cases; `SpecIris.v`
  compiles (rocq_compile_file, full). `interp_arrv` now states the count
  as `bv.of_nat (length L) = n` and `length L = length R`, so `n + 1`
  wraps with the list and no add lemma needs a premise. Proved in PREAMBLE
  mode (pet OOMs on SpecIris.v at >7.6 GB): `From Katamaran Require Import
  Base Bitvector Iris.BinaryWeakestPre Iris.BinaryAdequacy
  Iris.BinaryInstance Syntax.Predicates RiscvPmp.Base RiscvPmp.Machine
  RiscvPmp.IrisModelBinary RiscvPmp.IrisInstance RiscvPmp.Sig
  RiscvPmp.IrisInstanceBinary` + iris proofmode, `Import RiscvPmpIrisBase2
  RiscvPmpIrisInstance2`. Trap: SpecIris.v has implicit arguments ON —
  call helpers with `@`. Heavy chain BUILT 2026-10-23 15:33 through
  `RsaSpikeSubResult`/`RsaSpikeSub2Result` (a first -j1 background run was
  reaped mid-`EndToEnd` after building up to GenCompose — its piped grep
  output was lost, so it LOOKED like nothing built; check .vo timestamps;
  rerun in the FOREGROUND in <10 min steps). S1 VCs after the peval rules:
  13.9→16.9 / 2.9→3.7 / 6.8→7.1 s — NOT a matched comparison (different
  RAM state), recorded, not concluded. muladd/check_scalar VCs not rerun
  (merge gate at the plan's end).
- Then: memcpy's FUNCTION contract (entry seeds of empty
  done arrays — needs an `arrv` empty-seed lemma, `[] ++ vs` — and the
  exit glue: drop/pad the empty rests; the `n = 0` path); the word⇄byte
  regroup WITH values (`bytes_of_words` as a list UnOp + a cancelling peval
  rule); memmove's rotated ±1-stride loop; ccopy's MUX (`MUX c x x ~> x`
  would make an equal header public again even under a secret ctl).
- Decided (Emiel, 2026-10-23): (Q1) MIGRATE DIRECTLY — replace `arr`
  everywhere, no cost probe first (the extra value existential per array
  is accepted; deal with a slowdown afterwards). (Q2) word arrays hold
  `list (bvec 32)`; the call-site regroup goes through a new list UnOp
  `bytes_of_words` with a peval rule cancelling the round trip.

**Known traps (each cost time).**
- An instruction carrying a block runs the block INSTEAD of itself, ghosts
  included — put seeds in `ghost_after` of the instruction before.
- Debugging a red function/segment VC: `cfg_vc` erases to a bare `False`;
  dump `DebugCFGVerifierContract c annot` after `vm_compute` with `Set
  Printing Depth 100000` via a one-off `coqc` (proof temporarily replaced by
  `match goal with |- ?G => idtac "ZZ:" G end`), and grep the `amsg`
  `debug_string_message` + its path condition. That is how the `sext r`
  exit miss was found in two runs.
- Memory: the background-shell reaper kills the gate at `MuladdParamVC`
  (~10 GB) or the axiom probes when RAM is short — build
  `MuladdParamVC.vo` first, run the gate's last stage in the foreground
  (`GATE_JOBS=1 GATE_PROBE_BATCH=18`). pet OOMs replaying `GenCompose.v`
  past line ~2300.
- Rebuild costs after a `theories/` edit: light chain to `RsaSpikeSub.vo`
  ~16 min at `-j2`, heavy chain to `RsaSpikeSubResult.vo` ~19 min at `-j1`.
  Prototype in preamble mode (`From Katamaran Require Import
  RiscvPmp.CFGVer.Example.Prelude` gives `Term`/`inst`/`≡`; name implicit
  arguments of `uop.sext` as `(m:=…) (n:=…) (p:=…)`).
- `Bitvector.v`'s `Section Integers` opens `Z_scope`: write `{m n : nat}`
  and `%nat` in any new width lemma there.
- Result-file proofs: `repeat constructor` overshoots on `ForallOrdPairs`
  of disjunctions, use `repeat (first [apply FOP_cons | apply FOP_nil |
  apply List.Forall_cons | apply List.Forall_nil])`; a goal's `bv.bin h`
  can carry a differently spelled width index than the hypothesis — close
  with `exact` (conversion), not `lia`.
- LoopN hard-codes the `m` array PUBLIC; in RSA the modulus is secret —
  Phase 3 needs a LoopN variant with both publicness flags.
- `Tables.v` has no `S4`–`S11` aliases yet (needed by montymul's listing).
- Solver.v builds take ~6 min and invalidate everything downstream.

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

- **O1 (Phase 2) — DECIDED 2026-10-22 (Emiel): picolibc 1.8.12's
  size-optimised RISC-V assembly.** BearSSL ships no memcpy/memset/memmove
  (it includes `<string.h>`; our freestanding build only declares them,
  `stubinc/string.h`), so the bodies are a choice. picolibc's
  `libc/machine/riscv/rv_string.h` picks, under `-Os` /
  `__PREFER_SIZE_OVER_SPEED`, hand-written byte loops; under plain `-O2`
  it picks C with a word fast path + alignment handling (and vector code
  with V). We take the `-Os` ones: real libc code, one loop each, byte
  access only. `tools/bearssl/picolibc.sh` assembles them (clang `-Os`
  rv32im; `LPAD` is empty without Zicfilp). Shapes:
  - `memset` (5): `mv a3,a0; beqz a2,done; L: sb a1,0(a3); addi a2,-1;
    addi a3,1; bnez a2,L; done: ret`
  - `memcpy` (7): same with `lbu a4,0(a1); sb a4,0(a3)` and `a1 += 1`
  - `memmove` (13): ONE loop, stride `a3 = ±1` chosen by `bltu a0,a1`
    (public pointers); the backward case first adds `n` to both pointers.
    The loop is ROTATED — entered at `.Lcopy` (`lbu; addi a2; sb; bnez`),
    back edge to `.Lincrement` (both pointers `+= a3`) — so its header is
    not its entry. Either one loop contract with a ±1 stride variable, or
    two (one per direction); decide when we get there.
  Writeup: "linked against picolibc's size-optimised mem*".
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
  fails). The gate PASSED with the solver rule (2026-10-22 10:49, 24 end
  theorems axiom-clean, 76 min wall at GATE_JOBS=1). OPEN: the end theorem
  (Result file: `blkValid_of_seg_at` + `ValidCFGVerifierContract_intro` + a
  bridge with array memory), S1b.

- **ONE GENERATOR, 2026-10-22 (Emiel: "you should be able to do everything
  with the same contracts").** The separate callee API is GONE. There is one
  generator, `GenSegment.gen_seg_contract_at base base_a ex code fl regs
  extra_pre post`, with the exit a TERM; `gen_seg_contract … target …` is
  its abbreviation at `exit_of_off base target` (all 20 call sites
  unchanged; 5 `cbn [gen_seg_contract …]` lists gained `gen_seg_contract_at`).
  One faithfulness/validity pair, `GenCompose.blockFaithful_of_seg_at` /
  `blkValid_of_seg_at`, with a premise `Hex`: the precondition makes the
  exit a SyncVal -- the only exit-specific obligation (etable_rel), and not
  special to functions. Two lemmas discharge it: `seg_exit_sync_off` (offset
  exit, from the placement) and `seg_exit_sync_pub` (an exit made public by a
  leading `secLeak ex_a` in extra_pre, e.g. a return address).
  `blockFaithful_of_seg` and `blkValid_of_loop_seg` keep their signatures,
  re-proved through these. A function is just `gen_seg_contract_at … (term_var
  "r") … (secLeakvar "r" ∗ pre) …`. Spike VCs unchanged (14.0 / 3.1 / 0.1 s).

**GATE 1 CLOSED 2026-10-22** (Emiel): green + axiom-clean on light checks
(`sub_call_noninterferent`, `sub_call2_noninterferent`); the merge gate was
NOT run after `peval_sext` -- deferred to the plan's single final gate.

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
| 2026-10-22 | gate #1 (solver rule) | 09:33:23 | 10:49:33 | 76 | 76 | 0 | 4569 s wall / 3442 s user / 10.0 GB (axiom probes) | — | — | PASSED, 24 theorems axiom-clean |
| 2026-10-22 | explain "why callee contracts differ" to Emiel | ~10:00 | ~10:20 | — | — | — | — | — | — | user time; Emiel: do it with one contract |
| 2026-10-22 | unify generators (gen_seg_contract_at, one lemma family) | 10:21:23 | 10:55:53 | 35 | 1.5 (GenCompose 34 s, spike 46 s) | ~33 | spike VCs 14.0 / 3.1 / 0.1 s, unchanged | GenSegment +~20 net, GenCompose ±~150 (callee lemmas deleted), 5 cbn lists, spike 6 lines | 0 | GenCompose and spike green FIRST try |
| 2026-10-22 | gate #2–#4 (unified generator): two reaper kills (MuladdParamVC 10 GB; axiom probes), heavy file built in between, last stage in the foreground | 10:54:51 | 13:19:41 | 145 | ~120 | — | MuladdParamVC 698 s / 9.1 GB; final gate 344 s / 9.8 GB | — | — | PASSED, 24 theorems axiom-clean; ~60 min of the window was a usage-limit pause |
| 2026-10-22 | Phase 1: S1a end theorem -- read handoff + templates, probe route A (VC via gen_prog_contract) | 13:24:55 | 13:28:06 | 3 | <0.1 | 3 | probe VC 0.2 s | — | 1 (missing solve_mb_vc import) | then the two decisions to Emiel |
| 2026-10-22 | Phase 1: S1a end theorem -- restate s1aRec, validity steps, statement, end theorem, gate list | ~13:29 | 13:46:14 | ~17 | ~2 (spike 46 s, Result compiles) | ~15 | spike file 29.4 s user / 4.9 GB; Result file 18.7 s user / 7.5 GB; VCs 13.5 / 3.0 / 0.1 s | spike ±~20, Result 330 lines (~200 proof) | 6 (notation `∗` out of scope, `secLeakvar` notation, `repeat_length` in two hyps, two `lia` on mismatched `bv.bin` width index -- fixed by `exact` up to conversion) | end theorem green on its FIRST full compile; axiom-clean |
| 2026-10-22 | Phase 1: S1b listing (clone, build, link, asm_to_ast) + caller contract + first VC run | 13:48:14 | ~14:05 | ~17 | ~1 | ~16 | — | spike2 ~120 | 1 (VC red) | |
| 2026-10-22 | Phase 1: S1b diagnosis (two coqc dumps: residual False, then DebugCFGVerifierContract → `sext r` exit miss) | ~14:05 | ~14:20 | ~15 | ~5 | ~10 | debug compiles ~1 min each | — | — | then explain to Emiel (3 options, then "why is the sext there") |
| 2026-10-22 | explain sext + options to Emiel | ~14:20 | 14:54:36 | — | — | — | — | — | — | user time |
| 2026-10-22 | peval_sext rule (preamble prototypes, Bitvector + PartialEvaluation edits) | 14:54:36 | 15:00:04 | 5.5 | 2.6 (3 builds) | 3 | PartialEvaluation.vo 46 s | Bitvector +15, PartialEvaluation +53 | 3 (Z_scope `m n : Z`, `I` for IsTrue, none in the proofs) | proofs first try after preamble |
| 2026-10-22 | rebuild light chain (Solver.v etc.) -j2 | 15:00:27 | 15:16:12 | 16 | 16 | 0 | 945 s wall / 1025 s user / 4.9 GB | — | — | S1a VCs unchanged 13.9 / 2.9 / 0.1 s |
| 2026-10-22 | S1b VCs green + negative controls; harness contract written during the rebuild | 15:00:51 | ~15:20 | — | ~0.3 | — | valid_sub2 6.8 s, valid_s1b 0.3 s; file 37.8 s user / 5.0 GB | spike2 ~210 total (51 generated instrs) | 0 | both VCs green FIRST try after the rule |
| 2026-10-22 | heavy chain rebuild -j1 (in background) + S1b Result file | 15:19:23 | 15:44:22 | 25 | ~19 (rebuild 1119 s) | ~6 interleaved | Result 21.5 s user / 7.5 GB | Result ~280 lines | 4 (`repeat constructor` overshoot, `repeat f_equal` on N, bv.unsigned_of_N_small missing, rewrite comma syntax) | axiom-clean |
| 2026-10-22 | Phase 2: O1 (explain + survey picolibc, pin 1.8.12, `picolibc.sh`, plan) | ~16:00 | 16:19:11 | ~19 | <0.5 | ~7 | — | script 30 | 0 | ~15 min of it user time (3 clarifying rounds: BearSSL has no mem*, which libc, why byte loops) |
| 2026-10-22 | Phase 2 step 2: `sb` width 1 (RsaSpikeSb.v: 3 VCs + 4 controls) | 16:19:11 | 16:23:53 | 4.7 | 0.5 (full compile 22 s) | 4.2 | VCs 0.08 / 0.04 / 0.10 s; file 15.9 s user / 4.7 GB | ~110 | 0 failed VCs; 1 control replaced (name-mismatch, not secrecy) | all green first try; one coqc-guard block (file appended after session start) |
| 2026-10-22 | Phase 2 S2: options + explanations (view change, mixed publicness, framing, value-carrying arrays) | 16:24 | ~16:45 | — | — | — | — | — | — | user time; decisions (a) call site, (b) arrv replacing arr, spike first |
| 2026-10-22 | S2-arrv v1+v4: Sig/IrisInstanceBinary arrv, 4 CLems, caller VC | 19:19:44 | 19:35 | ~16 (a gap 16:45→19:19 is idle, not counted) | ~8 (Sig→IrisInstanceBinary 188 s, Spec 44 s, light chain 76+94 s) | ~8 | v4 VC 0.56 s | Sig +12, IrisInstanceBinary +20, Verifier +75, spike ~110 | 4 (implicit `w`, block pre needs chunk_angelic, take_cons n≠0 premise, one `vos` round) | framing works; stock solve_mb_vc finds the cons witnesses |
| 2026-10-23 | S2-arrv v2+v3: bv lemmas + 2 peval rules (preamble prototypes), memcpy loop VC | ~13:50 | 14:27:29 | ~37 | ~17 (PartialEvaluation compile ~1 min, rebuild theories→light 889 s wall / 975 s user / 4.96 GB, spike files 58 s) | ~20 | valid_mc_loop 0.40 s, valid_cl 3.6 s (0.56 s interactively); files 44.5 s user / 4.9 GB | Bitvector +18, PartialEvaluation +70, spike +110 | 6 (Stdlib path, IsTrue import, noeqns blocks funelim, existT injectivity, cbn unfolds peval_binop', 3 paren-count rounds) | v3 green FIRST try once the rules existed; heavy chain red (clemSem) |
| 2026-10-23 | S2-arrv Iris soundness (4 step lemmas in preamble, 4 ValidLemma wrappers, interp count via of_nat) | 14:27:29 | 14:57 | ~30 | ~13 (IrisInstanceBinary chain 508 s user / 7.1 GB, Soundness deps 145 s, ShallowSoundness 28 s, SpecIris compile ×3 ~2 min each) | ~17 | — | SpecIris +230, IrisInstanceBinary ±4 | 7 (Stdlib/notation preamble ×3, cbn `in` syntax, of_Z_negate direction, length_zip name, skill-path-guard block, implicit args ×2) | pet OOM on SpecIris.v → preamble; heavy rebuild past SpecIris killed by the memory reaper |
| 2026-10-23 | heavy-chain rebuild (foreground, after the reaper kill) | 15:28:27 | 15:33:21 | 5 | 5 | 0 | EndToEnd 45 s / 7.6 GB; RSA Results 151 s user / 7.6 GB | — | 0 | green; VerifierRel..GenCompose had already been built by the reaped run |
| 2026-10-23 | arrv O1–O3 asked; O2 re-examined (Emiel: framing should do it) + probe ZZArrvPubTake.v | ~15:46 | 15:52 | ~6 | <1 (probe 0.05 s ×2) | ~3 (+~2 user) | valid_pt 0.05 s | probe 50 | 0 | plan §1.2 was WRONG: propeq is Leibniz on RelVal, plain take already yields public parts; arrv_take_first_pub dropped |
| 2026-10-23 | arrv Phase A: 10 CLems (take_last, nonempty, empty, empty_elim, lockstep, drop, flip, join, pad, split) + peval_rev + soundness (incl. pigeonhole length bound for pad), probe ZZArrvCatalogue.v | 15:52 | 16:58 | ~66 | ~30 (PartialEvaluation 47 s ×2, theories→Spec+IrisInstanceBinary ~26 min mostly overlapped, light chain ~5 min overlapped, SpecIris 282+145 s, heavy chain 508 s / 7.7 GB) | ~36 | probe VCs all < 1 s; SpecIris 137 s user / 8.9 GB | Verifier +~130, SpecIris +405, PartialEvaluation +27, probe ~150 | 3 builds (PartialEvaluation ssreflect-vs-std rewrite, probe seed plain-vs-angelic chunk + loop-VC ∃ artifact, SpecIris implicit args) + ~12 interactive (lia/ring hidden-index atoms) | pad needed a design choice (Emiel: bound lemma over exact count); everything else as drafted |
| 2026-10-23/24 | arrv Phase B: uop.regroup (generic list op; fixed-type op breaks Terms' Equations), bv.le_bytes, clem_arrv_to_bytes/of_bytes (+ k <u 2^30, found while proving), soundness, GATE B probe ZZArrvWords.v | 17:05 | 01:50 | ~159 active (a ~6 h gap 19:15→01:09 during the Solver.vo build is a machine suspend, not counted) | ~55 (Bitvector→Terms ~4 min, Solver.vo ~6 min est. [wall polluted by the suspend], theories→IrisInstanceBinary 970 s / 865 u, light chain ~5 min, SpecIris 333 s / 299 u / 9.1 GB, heavy chain 480 s / 402 u / 7.8 GB) | ~104 (incl. 3 user decisions) | valid_w 4.6 s; probe VCs < 1 s | Bitvector +11, UnOps +24, Terms +10, Solver +5, Verifier +~35, SpecIris +230, probe ~85 | 2 builds (Solver position-mode timeout → blind build OK; none failed) + ~20 interactive (implicit args ×3, lia/ring hidden-index atoms ×6, simpl over-unfolding) | decisions D6 pattern-form of_bytes, D7 count 4·k, D8 generic regroup; of_bytes needed a bound the plan had not foreseen |
| 2026-10-24/25 | arrv Phase C (D12 positional V, D13 value tracking): GenSegment data_spec/gen_data_at/gen_prog_contract, EndToEnd data_vals + ImplPre, GenProg bridge, LoopN arrv+VM, RSA spikes + Results, GATE C | ~09:58 | ~09:55 (+1 day) | ~3 h active (wall includes a ~23 h machine suspend during a Fail control) | ~35 (GenSegment 600 s TIMEOUT = the Subst-instance hang, then 2 min; EndToEnd ×3 ~4 min each; GenCompose, GenProg, LoopN; spikes 2×~2 min; probe ~2 min) | rest | valid_sub_loop 13.0 → 36.6 s, valid_sub 3.2 → 22.4 s (matched baseline ZZArrvCost.v), valid_s1a 0.1, valid_sub2 6.7, valid_s1b 0.3 | GenSegment ±~90, EndToEnd +~250 −~150, GenProg ±~60, LoopN ±~40, spikes ±~60, probe ~330 | ~25 interactive (instance-mismatched inst rewrites ×6, implicit args, String.length shadowing in a preamble) + 4 builds | 2 user decisions (positional V; track values) + 1 (accept the cost) |
| 2026-10-25 | arrv Phase D step 1: RsaSpikeSb ported (memset + memcpy bodies); valid_cpy exposed the unsplit-secLeak-after-substitution bug; traced (mem_read `secLeak inv` → solve_evars literal assert blocks the hoist; angelic same-shape arrays too); 2nd-replay fix tried + reverted; solver fix `ResimpSecLeak` (prototyped + proved in preamble, Solver.v) | ~09:50 (not stamped; RsaSpikeSb.v written 09:56:51) | 10:58:39 | ~68 | ~19 (baseline compile 0.3 min; Solver.vo 298 s FAILED on implicit args + 360 s; closure → RsaSpikeSb 437 s / 5.0 GB, 18 files) | ~49 incl. 5 user decisions | valid_sb_sec 0.080 → 0.281 s (0.103 s interactively), valid_sb_pub 0.035 → 0.041 s, valid_cpy 0.091 → 0.122 s (matched: old file compiled against the same build before the port) | RsaSpikeSb +50 −37, Solver +112 | 1 build (Local Set Implicit Arguments, absent from the preamble) + ~12 interactive (dependent-index destruct, unification reducing peval → timeouts ×3, flaky `now`) | the rule is secLeak-only by decision; the full rebuild is deferred to the Phase D/E gate, so other VCs have not yet seen it |
| 2026-10-25 | re-verify the green arrv set against ResimpSecLeak (heavy chain, GenCompose/GenProg/EndToEnd, LoopN, RsaSpikeArrv, RSA spikes + Results, 4 ZZArrv probes) | 11:10 | 22:31 | ~5 active (wall includes a ~10.5 h machine suspend inside RsaSpikeSub.vo: 40084 s real / 105 s user) | 27 files, user ~27 min, peak 9.1 GB (SpecIris); ZZ probes ~1 min | ~5 | UNCHANGED within noise, matched (same build): o_valid_sub_loop 13.2 s, o_valid_sub 2.9 s, nv_valid_sub_loop 31.7 s, valid_sub_loop 36.9 s, valid_sub 23.6 s, valid_sub2 6.8 s, valid_cl 3.7 s, valid_mc_loop 0.39 s, valid_w 4.7 s, valid_pt 0.05 s | 0 | 1 (hand-rolled coqc flags mangled `-arg "-w all"`; used rocq_compile_file) | all Fail controls still rejected; the solver rule is cost-neutral here |

Protocol amendment (2026-10-21): wall time between two stamps is only
attributable to authoring if no idle gap can hide in it, so stamp at least
every ~5 tool calls and before/after anything that may wait on approval.
