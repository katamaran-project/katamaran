# PLAN-rsa — BearSSL RSA private-key operation (`br_rsa_i31_private`), noninterferent

Status: **IN PROGRESS on branch `issue/rsa`.** Phases 0–1 CLOSED; Phase 2
resumes after its detour **PLAN-arrv (COMPLETE 2026-10-26, merged into local
`KatamaranRel` as `bc7faac1`, not pushed)**. Survey (§1), decisions (§2),
phases (§4), timing log (§5).

## HANDOFF (2026-10-26) — read this first

**Where things stand.** Everything up to and including PLAN-arrv is on
local `KatamaranRel` (`bc7faac1`, merged `--no-ff --no-verify` on Emiel's
instruction) and `issue/rsa` is fast-forwarded to it — keep working on
`issue/rsa`, merge into `KatamaranRel` with `--no-ff` (skill
branch-workflow), NEVER push or merge to `main`. Verified at merge: the
gate's whole build (75 files, `arr` deleted) and its hole scan. NOT
verified: the gate's axiom probes (26 end theorems) — killed by the memory
reaper, not rerun. Run them once early, in the FOREGROUND (everything is
built, ~6 min): `GATE_JOBS=1 GATE_PROBE_BATCH=18 ./scripts/gate.sh`.
Phase 2's spike S2 turned into PLAN-arrv; read that plan's §1 (facts) and
HANDOFF once, but you do not need its history to continue.

**What exists now (all green).**

| file | what |
|---|---|
| `Example/Rsa/RsaSpikeSub{,Result}.v` | S1a: `br_i31_sub` as a FUNCTION contract (exit `r`), called as a block; its loop is LoopN; the post hands b back with its own value (`flip` + `join "db" "vb" "vb"`, PLAN-arrv D13); `sub_call_noninterferent` (∀ h) |
| `Example/Rsa/RsaSpikeSub2{,Result}.v` | S1b: a non-leaf function calling `br_i31_sub` twice (2nd a tail call); `sub_call2_noninterferent` |
| `Example/Rsa/RsaSpikeSb.v` | `sb` at width 1: memset's body into a secret / public byte array, memcpy's body between two byte arrays; controls |
| `Example/Rsa/RsaSpikeArrv.v` | a public header byte survives a VALUE-contract memcpy by framing (`valid_cl`); picolibc's real memcpy LOOP with `vs = done ++ rest` (`valid_mc_loop`, 0.4 s); controls |
| `Example/Muladd/MuladdParamLoopN.v` | the lockstep-loop template: tags as record fields `ln_tm ln_tx ln_tdm ln_tdx`, read-only array's value tracked as contract variable `VM = rev dM ++ rM` |

**The array toolkit (`arrv`; skill cfgver-contracts "Arrays").**
`arrv w s t [a; n; e; vs]`: values NAMED (`vs : list (bvec 8w)`), no
publicness flag (a public array is `arrv … vs ∗ secLeak vs`; framing keeps
a caller's facts), a Coq-level string TAG `t` that only disambiguates the
executor's angelic chunk match (D14; mismatch = failed match). Conventions:
top-level `DArr`/`DBytes` tag = its value name (D15); templates take tags
as Coq parameters (D16); every ghost lemma names the tag of EACH array it
matches — `join w s t1 t2 t`, `lockstep w s t1 t2`, `pad w s t t'`, others
one `t`, kept through `flip` (D17). Catalogue `clem_arrv_*`: take_first /
take_cons / take_last, add_first / add_last, nonempty, empty, empty_elim,
lockstep, drop, flip, join, pad, split, and the word ⇄ byte VIEW
`to_bytes` (`arrv 4 4 … ws ⊢ arrv 1 1 … (4·n) (regroup ws)`) / `of_bytes`
(pattern form, needs `k <u 2^30`). WORDS ONLY: the halfword/doubleword
regroups went with `arr`. Give two same-shape live arrays DIFFERENT tags —
untagged ambiguity cost ×3.7 on LoopN (`diagnostics/arrv-loop-cost-drivers.md`).

**The function-contract recipe** (S1a/S1b; skill
cfgver-gen-contract-internals, "The segment generator"):
- a function is `gen_seg_contract_at q q (term_var "r") code fl regs
  (secLeakvar "r" ∗ pre) post` with `X1 ↦ᵣ r` in pre and post; valid by
  `blkValid_of_seg_at` + `seg_exit_sync_pub`; a block on its first
  instruction in every caller (`MkBlkAnnotV blk valid` in the caller's
  typed annotation, as in the Result files);
- a NON-LEAF function's `code` is itself AND its callees as linked;
- pin `sp`, `s_i` to the SAME logic variable in pre and post; own the frame
  as `gen_data_at (t_add sp (-k)) [DCell Secret; …]`;
- the top level is ALWAYS `gen_prog_contract` (pointer args `PVVar`, data
  `DPtr`/`DCell`/`DArr … "v"`), so the end theorem is one
  `gen_prog_noninterferent` (templates: the RSA Result files;
  `CheckScalarParamResult`/`MuladdParamResult` for contiguous data, layout
  by `contig_data_layout` + `concretize_data_addrs`);
- a post NAMES the values it hands back (no ∃) when a caller needs a fact
  about them (Emiel, memory `feedback-framing-keeps-info`); an overwritten
  array's value is just ∃.

**Next step — the rest of Phase 2 (§4), in this order. ASK EMIEL the
marked design questions BEFORE writing the contracts (memory
`feedback-involve-in-planning`).**
0. **STATUS 2026-10-27:** memcpy, memset, memmove (a)+(b) DONE (`RsaMemcpy.v`, `RsaMemset.v`, `RsaMemmove.v`); memcpy DONE (`Example/Rsa/RsaMemcpy.v`, D5 post);
   it needed `clem_arrv_empty_at` (seed at an existing array's start, so the
   n = 0 path's seeds have a known address). Its SpecIris soundness case is
   WRITTEN BUT NOT BUILT: the heavy chain is red until the next SpecIris
   build (planned together with the ccopy resync CLem, O4). Emiel
   2026-10-27: no gate needed; merge without it.
1. **memcpy as a FUNCTION** (picolibc 1.8.12 `-Os`, `tools/bearssl/
   picolibc.sh`), on the S1a template, over byte arrays (`arrv 1 1`). Its
   loop VC exists (`RsaSpikeArrv.valid_mc_loop`); what is new is the glue:
   entry seeds (`clem_arrv_empty` for the done array — in `ghost_after` of
   the instruction BEFORE the loop block), the `n = 0` path (the loop is
   skipped), exit glue (`pad`/`join`/`empty_elim` of the emptied rests),
   and a post `dst ↦ vs` naming the source's value. ASK: post shape — the
   destination holds exactly `vs` (value contract, as the spike's stand-in)?
2. **memset** the same way (its body is in `RsaSpikeSb.v`); post: the
   destination holds `repeat c n` — needs a list term for it, or a weaker
   post. ASK which.
3. **memmove**: its loop is ROTATED (entered at `.Lcopy`, mid-body) and
   walks +1 or −1 depending on overlap. ASK: one contract with a stride
   variable, or two (one per direction)? `arrv`'s stride is a Coq-level Z,
   so a stride variable would need a new form — two is the cheap route.
4. **br_ccopy** (`ctl ? src : dst`, word-wise MUX): needs a peval rule
   `MUX c x x ~> x` so that an EQUAL public header stays public under a
   secret `ctl`. ASK before touching `theories/` (Solver/PartialEvaluation
   builds take ~6 min and invalidate everything downstream).
5. **GATE 2:** `br_ccopy` over a WORD array called from a word-accessing
   caller, end to end — the word⇄byte view change at the CALL SITE
   (`to_bytes`/`of_bytes` ghosts around the call, D4/§2), a Result file on
   the S1b template. Then Phase 3 (`montymul`).

**Tooling.** `tools/bearssl/build.sh <BearSSL checkout> <out>` (clone
BearSSL into the scratchpad, pinned `7bea48e`); `tools/bearssl/spike/`
(`harness_sub.s`, `harness_sub2.s`, `sub2.c` — compile `sub2.c` with
build.sh's CFLAGS against a hardened tree: copy `inc/`+`src/`, apply
`hardening.patch`); link `ld.lld --relax -Ttext=0 harness … callees…`,
`llvm-objdump-18 -d --no-show-raw-insn`, `asm_to_ast.py --objdump
--tables-aliases --name <x>`. Exact recipe: the header comments of
`RsaSpikeSub.v` / `RsaSpikeSub2.v`. picolibc: `tools/bearssl/picolibc.sh`.

**Known traps (each cost time).**
- An instruction carrying a block runs the block INSTEAD of itself, ghosts
  included — put seeds in `ghost_after` of the instruction before.
- A block's precondition must use `chunk_angelic` (`clem_arrv_angelic`) for
  arrays whose address is a block variable — a plain chunk cannot search
  the heap.
- Debugging a red function/segment VC: `cfg_vc` erases to a bare `False`;
  dump `DebugCFGVerifierContract c annot` after `vm_compute` with `Set
  Printing Depth 100000` via a one-off `coqc` (proof temporarily replaced by
  `match goal with |- ?G => idtac "ZZ:" G end`), and grep the `amsg`
  `debug_string_message` + its path condition.
- MEMORY (14 GB box): the background-shell reaper kills long builds when
  RAM is short — `MuladdParamVC` needs ~9.4 GB (close Firefox), every
  `*Result.v` ~7.7 GB (build them `-j1`, never two at once), the gate's
  axiom probes ~7 GB (run that stage in the foreground). A reaped job is
  not a failure; ask Emiel before restarting it.
- Watchdogs: match `pgrep -x coqc` + the cmdline, never `pgrep -f <file>`
  (it matches the watchdog's own shell). Cutoff: kill above 1.5× a file's
  baseline USER CPU (memory `feedback-compile-cutoff`).
- Result files import iris proofmode: `rewrite` is SSReflect-style
  (`rewrite a -b`, not `rewrite a, <- b`); `cbn -[bv.of_N]` stops
  `bv.eqb (bv.of_N k) bv.zero` from computing (concretized `PVOff` regs).
- `Verifier.v` / `SpecIris.v` have implicit arguments ON: every helper needs
  `Arguments … w …` (Verifier) or `@` calls (SpecIris); SpecIris is proved
  in PREAMBLE mode (pet OOMs on it), preamble in the PLAN-arrv record.
- Result-file proofs: `repeat constructor` overshoots on `ForallOrdPairs`
  of disjunctions, use `repeat (first [apply FOP_cons | apply FOP_nil |
  apply List.Forall_cons | apply List.Forall_nil])`; a goal's `bv.bin h`
  can carry a differently spelled width index than the hypothesis — close
  with `exact` (conversion), not `lia`.
- `Bitvector.v`'s `Section Integers` opens `Z_scope`: write `{m n : nat}`
  and `%nat` in any new width lemma there.
- `Tables.v` has no `S4`–`S11` aliases yet (montymul's listing needs them).
- Rebuild costs: after a `Sig.v` edit ~1 h of serial rebuild; after a
  `theories/` edit the light chain to `RsaSpikeSub.vo` ~16 min at `-j2` and
  the heavy chain ~19 min at `-j1`. Prototype in preamble mode first.
- The `arr`-based ZZ probes (`Example/Rsa/ZZArrv{Cost,Ambig,AmbigSwap,
  Split}.v`, `Example/CheckScalar/ZZArrvInteract.v`,
  `Example/Muladd/ZZLoop{I,K,M}Arr.v`) no longer compile — rerun them at
  `f7fc0a65` if a measurement must be reproduced.

**Process (Emiel's standing rules).** Report before acting; ask at design
forks; light checks per phase, ONE full gate at the plan's end; no
per-phase `Print Assumptions`; commit `WIP (LLM):` freely with `git add -u`
+ named new files (never `git add -A`: untracked ZZ probes); log every
step in §5 (stamps, wait vs authoring, VC CPU/RSS, LOC, attempts).

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

- **D5 (2026-10-26, Phase 2 mem* contracts)** — facts first (BearSSL
  `7bea48e`): every `memset` call passes `c = 0`; both `memmove` sites have
  `dst > src` (backward only) — `i31_muladd.c:86,93` OVERLAPS (shifts
  `x[1..]` up one word, secret limbs), `rsa_i31_priv.c:136` is adjacent,
  disjoint, and moves `p` WITH its public header. Decided:
  memcpy post = EXACT value (`dst ↦ vs`, source unchanged, `a0 = dst`);
  memset post = `∃ vs. dst ↦ vs ∗ secLeak vs` under `secLeak c` (no
  `repeat` term); memmove = TWO backward contracts on the same code, the
  forward branch refuted by `src <u dst`: (a) disjoint with memcpy's value
  post (rsa_priv), (b) one-region overlapping shift with values ∃
  (muladd_small). br_ccopy: Emiel asked first WHY the existing bv rules do
  not reduce `((y^x)&m)^y` with `x ≡ y`, and whether earlier rules could
  have been more general — investigate before adding any rule.

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
- **O4 (Phase 2/5, found 2026-10-26) — br_ccopy hits the RelVal TAG, not a
  missing rule.** `br_ccopy` byte = `((y^x) & −ctl) ^ y`. With `ctl` secret,
  `liftBinOpRV` (`TypeDecl.v:268`) makes the header byte `NonSyncVal h h`
  even when `x ≡ y ≡ h`, and `secLeak (NonSyncVal _ _) = False`
  (`Formulas.v:117`). So NO peval/solver rewrite to `y` is sound under ≡
  (it would turn NonSyncVal into SyncVal) — the same reason ring
  normalisation pads `0·a` and `x − x` is not `0`. Survey: no xor rule
  exists at all; the generic `peval_bvand`/`peval_bvor` are commented out
  (`9478b8d2`, soundness never re-proved after the RelVal migration
  `196eae12`), and `t & 0 → 0` among them is itself unsound for secret `t`;
  the live bitwise rules are idiom-specific (mask algebra, coalesce, mulx)
  and are sound precisely because they keep secret inputs secret.
  Consequence beyond ccopy: modpow2.c:152 `CCOPY(NEQ(bits,0), x, t1, mlen)`
  then `br_i31_from_monty(x, …)` → `br_i31_sub(x, m, …)`, which reads
  `x[0]` as a LOOP BOUND (`i31_sub.c:35`) — so Phase 5 needs `x[0]` public
  after the ccopy. Under the tagged model that is unprovable. The parked
  RelVal-as-pair branch (`issue/relval-pair`, PLAN-relval-pair.md) makes
  `secLeak` = equal projections, after which the MUX identity (and
  `x^x→0`, `x&0→0`, `x−x→0`) are plain per-projection bv identities.
  DECIDED (Emiel, 2026-10-26): mem* now; `br_ccopy` now with an ∃-valued
  destination (no public header) so the function and GATE 2's view change
  are still exercised; revive relval-pair (rebase onto current
  `KatamaranRel`) as its own step BEFORE Phase 5.
  REVISED (Emiel, 2026-10-27): "go for the somewhat ad hoc rule for now" —
  a RESYNC ghost lemma (a cell/array holding `((y^y)&m)^y` becomes one
  holding `y`), sound IF the Iris memory interpretation reads only the two
  projections (tag-free, as relval-pair's notes say of the Iris model —
  CHECK that first). relval-pair stays the principled fix, not scheduled.
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
| 2026-10-25 | arrv Phase D step 2: check_scalar (Loop1, Loop2, Param+VC, Ptr+VC, both Results); array values ∃ (no post mentions them); Param's `cs` restated as gen_prog_contract (Emiel) so its end theorem is one gen_prog_noninterferent, hand-written ImplPre deleted | ~22:33 | 23:14:36 | ~41 | ~6 (baselines 2 × ~25 s; Loop1/Loop2/Param/ParamVC×2/Ptr/PtrVC (51 s)/ParamResult 29 s / 7.7 GB/PtrResult 30 s / 7.7 GB; Instrs stale .vo rebuilt) | ~35 incl. 1 user decision | valid_l1 9.83 → 9.83 s, valid_l2 14.05 → 17.25 s (matched, coqc); valid_cs 8.9 s + Qed 3.7 s, valid_csp 16.6 s + Qed 11.5 s (no matched baseline: the old Param no longer typechecks) | +104 −140 over 6 files (ParamResult −87 +40) | 0 failed VCs; 2 tool slips (stale CheckScalarParamInstrs.vo; a guessed state id) | every VC and both end theorems green first try; ZZCspDebug.v (untracked) not ported |
| 2026-10-26 | arrv Phase D′: string tag on arrv (D14–D17) — Sig, IrisInstanceBinary, Verifier CLems, SpecIris, GenSegment, EndToEnd, RSA spikes, RsaSpikeSb, check_scalar, LoopN; rig ZZArrvTagged.v; diagnostics §7 | not stamped (Sig.v/IrisInstanceBinary last edited 14:09) | 15:49 | — (not stamped) | light chain + examples (one -j2 build, output truncated by tail); heavy chain to GenProg -j2 killed by the memory reaper while two Result files ran (~7.7 GB each); Result files -j1 4 × 16–22 s user / 7.7 GB | — | valid_sub_loop 36.9 → 14.8 s, valid_sub 23.6 → 3.4 s (cold, as shipped); LoopN warm 31.7 → 9.7 s (arr 8.6 s); surviving value ∃ 72 → 0 | +210 −197 over 14 .v files (Verifier ±150, SpecIris ±64) | 2 guard denials (skill-path-guard on Verifier.v Edit — an earlier Bash edit had bypassed it; skill-bash-write-guard on a SKILL.md) + 1 memory kill; no failed VC | prediction confirmed; every Fail control still rejected; 1 user decision (D17 per-array tags) |
| 2026-10-26 | arrv Phase D step 3: muladd on tagged arrv (LoopD/DAng/D0, I/K/M tags, Tail + hand_over from the LoopN records, sym6 → gen_prog_contract, Result → one gen_prog_noninterferent); 3 matched arr baselines ZZLoop{I,K,M}Arr.v | ~16:00 (not stamped) | ~18:30 (not stamped) | — | Instrs+LoopG 75 u, TailVC 388 u / 8.1 GB, MuladdParamVC killed once by the memory reaper during Qed (VC already closed, 375 u), rerun 533 u / 9.4 GB after Firefox closed; Result 4 builds × ~21 u / 7.7 GB | — | matched cold: DAng 5.77→5.76, D0 8.66→8.89, I 17.63→18.65, K 13.46→14.45, M 13.34→14.20 s; unmatched: TailVC 365→388 s, MuladdParamVC solve 483→366 s, file 657→533 s | +144 −165 over 9 muladd files (Result −110 +~50) | 0 failed VCs; Result 3 rounds (ssreflect `rewrite -`, cbn blocking bv.of_N, missing GenProg import); 1 watchdog self-match (pgrep -f) caught before it mattered | trusted statement unchanged; 1 user decision (restate via gen_prog_contract) |
| 2026-10-26 | arrv Phase E: delete arr (Sig, IrisInstanceBinary, 15 CLems in Verifier, −836 lines SpecIris keeping 9 shared helpers; skills + archive) + gate E | not stamped | not stamped | — | light chain Sig→SpecIris ~6 min (SpecIris 112 u / 8.7 GB); gate prebuild 75 files -j1 (MuladdParamVC 538 u, TailVC 375 u, InvMixColumns 135 u, BearSSLCheckScalarLoop1 130 u); gate.sh build no-op + hole scan PASSED, axiom probes KILLED by the memory reaper | — | unchanged | −~1000 lines | 0 build failures | merged into local KatamaranRel on Emiel's instruction without the axiom step |
| 2026-10-26 | Phase 2 resume: handoff, mem*/ccopy call-site survey, D5 questions | 18:34 | 18:39 | 5 | 0 | ~3 | — | — | — | +user time on 4 questions |
| 2026-10-26 | ccopy: bv-rule survey (Explore agent) → O4 (tag wall, not a missing rule); "why relval-pair" | 18:39 | ~19:00 | ~20 | ~2 (agent) | ~10 | — | plan only | — | 2 user decisions (mem* now, pair before Ph5; later: ad hoc resync CLem instead) |
| 2026-10-26 | gate (axiom probes) started; turned into a FULL rebuild (the 18:23 merge/switch touched every source) | 18:39 | ~23:58 | — | — | 0 | rebuilt theories→MuladdParamTailVC; 18:43→22:55 a machine suspend | — | — | REAPED by the memory killer at MuladdParamVC while idle; Emiel: the gate is not needed, merge without it |
| 2026-10-26/27 | memcpy as a function (RsaMemcpy.v): picolibc link + asm_to_ast, loop/function/harness VCs; n = 0 path red → debug dump → new CLem `clem_arrv_empty_at` (Verifier.v; SpecIris case written, NOT YET BUILT) | ~23:00 | 00:33 | ~50 active | ~6 (debug coqc 236 s / 9.2 GB, light chain 81 s + GenSegment 15 s, file 20 s) | ~44 incl. 2 user questions | valid_ml_loop 5.1 s cold (1.35 s warm), valid_mf 0.27 s, valid_mcf 0.04 s; file 4.8 GB | RsaMemcpy 238 (11 generated instrs), Verifier +12, SpecIris +12 | 2 (loop arrays need chunk_angelic — the known trap; n = 0 seeds at an unbound address) | both Fail controls rejected (secret source; dst keeps old value) |
| 2026-10-27 | memset as a function (RsaMemset.v, D5 post: ∃ vs public) | 00:33 | ~00:37 | ~4 | ~0.5 (file 20 s) | ~3.5 | valid_msl_loop 4.4 s cold (1.0 s warm), valid_mfs 0.11 s, valid_msf 0.03 s | RsaMemset 202 (9 generated instrs) | 1 (paren count, vos) | green first full compile; both Fail controls rejected (secret fill value; loop without secLeak v) |
| 2026-10-27 | memmove (a) DISJOINT backward as a function (RsaMemmove.v): arrays flipped to stride -1 before the beqz, memcpy's loop at stride -1, value eq. vs = rev (done ++ rest) | ~00:37 | 00:41 | ~4 | ~0.5 (file 22 s) | ~3.5 | valid_mvl_loop 5.3 s cold (1.5 s warm), valid_mvf 1.05 s, valid_mmf 0.06 s | RsaMemmove ~250 (16 generated instrs) | 0 | green first try; both Fail controls rejected; no new lemma (peval_rev already has rev (rev v) ~> v) |
| 2026-10-27 | memmove (b) OVERLAPPING shift by 4 bytes (muladd_small): window M kept flipped, T seeded by empty_at on flipped M, values unnamed | 00:41 | 00:47 | ~6 | ~2 (pet restart at 5.3 GB, file 30 s) | ~4 | valid_mwl_loop 1.27 s, valid_mwf 0.90 s (coqc) | +~150 in RsaMemmove | 1 (paren count, vos) | green first try; Fail control rejected (window not at the low 4 bytes); no harness for (b) yet -- its caller is Phase 4 |

Protocol amendment (2026-10-21): wall time between two stamps is only
attributable to authoring if no idle gap can hide in it, so stamp at least
every ~5 tool calls and before/after anything that may wait on approval.
