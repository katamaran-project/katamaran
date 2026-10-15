# Next session briefing

CLAUDE.md is auto-loaded; the detailed CFGVer reference lives in the modular
`.claude/skills/cfgver*` skills (see CLAUDE.md header for the map).
This file tracks the approved task list and current starting point.

---

## Current state

All CFGVer noninterference proofs are one-liners via `gen_contract_noninterferent`.
All contracts are defined using `gen_contract`. See commit history for details.

First realistic example (from the "Breaking Bad" paper discussion) is done:
`cmovznz4` (HACL*'s constant-time conditional move), hand-translated from
`clang -O2 -march=rv32i` output into a `list AST`, proved noninterferent
end-to-end (`cmovznz4_noninterferent` in `CFGVer/Example/Cmovznz4.v`).

**Second "Breaking Bad" example done (2026-07-19):** `precompute`
(`CFGVer/Example/Precompute.v`) — a 32-bit-word analogue of Botan's
`GHASH::key_schedule` masking step (the real, currently-shipping
`CT::Mask`-based carry computation in `src/lib/utils/ghash/ghash.cpp`, fixed
in commit `53b0cfde58` which cites this exact case study's arXiv preprint;
the pre-fix code was `carry = R * (H1 & 1)`, byte-identical to the paper's
own Listing 3a). Compiled with clang 15.0.0 `-O2 -march=rv32i -mabi=ilp32`
(the SAME compiler/flags that still miscompile the pre-fix code into a
`beqz` branch): branch-free, 10 instructions, no memory. Proved
axiom-clean, both concrete and `_param` (universal base). See
"Botan CT::Mask / 64-bit-subtraction gap" below for why this is scaled to
`uint32_t` rather than the real `uint64_t`, and for the still-open full
`GHASH::key_schedule` loop.

**First WHOLE-FUNCTION example done (2026-08-03):** `modpow_win_full`
(`CFGVer/Example/BearSSLModpowFull.v` + `…FullResult.v`) — BearSSL's
`modpow_opt` window lookup as the COMPLETE nested loop, not the 5-instruction
body `BearSSLModpow.v` covers. 28 instructions, two levels of loop nesting, a
backward `JAL`, 122 executed steps, 16 data words, real loads/stores. Proved
axiom-clean end-to-end at an arbitrary base; gate green at 13 theorems.
Verified with the STANDARD one-liner tail
(`intros; vm_compute; solve_vc; solve_symbase_fetch`) on the first attempt —
63 s tactic + 38 s `Qed`. None of the three things expected to need work did:
backward `JAL` (only forward was exercised, in `Jumps.v`), two-level nesting
(every prior loop example is single-level), and base-relative addressing with a
pointer advanced by a REGISTER (`add a1, a1, a7`) rather than a constant.

Why the bounds are runtime arguments: with `mwlen`/`num_win` as compile-time
constants clang fully unrolls into ~50 straight-line instructions, which would
verify nothing about the loop control flow. The real code has them as runtime
values, so the C takes them as parameters and the CONTRACT pins them to public
constants (4 and 4). Cost matched the pre-build estimate from the `zzf` model
(~60 s `vm_compute` predicted), its first real test outside the `zz` probes.

**Two repo bugs fixed on the way:**
- `tools/asm_to_ast.py` could not translate ANY real loop: `DIRECTIVE_RE = ^\s*\.`
  was tested BEFORE the label pattern, so every clang local label (`.LBB0_2:`)
  was swallowed as a directive and every branch came back "undefined label".
  Never exercised before — `cmovznz4`/`precompute`/the three BearSSL snippets
  are branch-free, and `countdown`/`key_schedule_loop2` were hand-authored.
  Fixed by matching labels first (real directives never end in `:`).
- `Tables.v` was missing `T2`–`T6` (x7, x28–x31). The model has all 32 GPRs.

**`br_i31_muladd_small` (full) is OUT on rv32i — for a reason unrelated to any
scaling wall.** `MUL31` is a 32×32→64 multiply and rv32i has no `mul`, so
clang 18.1.3 `-O2` emits `call __muldi3` inside the word loop (verified locally,
not from memory). Two consequences: the function is not a self-contained
instruction sequence, so verifying it means translating compiler-rt's multiply
too; and that routine's conditional add is branch-free but its TRIP COUNT is
value-dependent (`bnez a0` on an operand), so if the loop operand is the secret
`q` it is a genuine secret-dependent branch. Neither `modpow_win` nor
`check_scalar` contains a multiply, so this affects only `muladd`.

**Full `check_scalar` is still blocked by the term wall**, and the GHASH solver
fold does NOT help it: `select_last_k` hardcodes `R = 0xE1000000`, so the
`EQ0`/`CMP` idiom would need its own recognizer and its own soundness proof.
Its trip count is fixed at 32 by P-256, so it cannot be scaled down either.
See `CFGVer/plans/PLAN-ksl64.md` §3 for the two-driver analysis this came out of.

## Botan CT::Mask / 64-bit-subtraction gap (2026-07-19)

While hunting the next "Breaking Bad" example, the REAL Botan
`GHASH::key_schedule` (`src/lib/utils/ghash/ghash.cpp`, current master)
turned out to already be fixed — commit `53b0cfde58` replaced the
paper's exact vulnerable line (`carry = R * (H1 & 1)`) with
`CT::Mask<uint64_t>::expand(H1 & 1).if_set_return(R)`, an inline-asm
value-barrier idiom (`value_barrier.h`: `asm("" : "+r"(x) :)`) that
empirically defeats the miscompilation on every clang/gcc version tried
(including the exact clang 15.0.0 that still breaks the raw-multiply form).

**The catch:** the real function operates on `uint64_t` (Botan's GHASH state
is two 64-bit words, `H0`/`H1`, living in register PAIRS under the RV32
ILP32 ABI). `CT::Mask`'s `ct_is_zero` needs a 64-bit `x - 1`, and RV32I has
no carry/borrow flag, so ANY compiler lowers a 64-bit subtract to: low-word
subtract, then an `sltu`-based borrow check, then high-word subtract-minus-
borrow. That `sltu`'s operands are secret-derived (from `H1`), and CFGVer's
`solve_vc` automation can only derive `secLeak (f t1 t2)` compositionally
*from* `secLeak t1`/`secLeak t2` already holding (`instprop_formula_secLeak_binop`,
`Contracts.v`) — there is no rule for "this comparison's two worlds may
legitimately disagree and that's fine, nothing downstream depends on which
way it went." Every existing CFGVer example either has no comparison at all,
or only uses one as an actual (public) branch predicate — none needed a
comparison used as a pure VALUE on private data, so this had never been
exercised. `precompute` sidesteps this by scaling `H` down to a native
`uint32_t`: a single-word `x - 1` is one plain RV32I `sub`, no borrow-chain
comparison at all, so no `sltu`-on-secret ever appears. Real Godbolt
investigation, both directions, is in this session's transcript.

**STILL OPEN:** verifying the genuine `uint64_t` version (and by extension
any real 64-bit-emulated-on-32-bit arithmetic on secret data) needs the
executor/`solve_vc` to support relops whose result may differ between the
two worlds without requiring `secLeak` — i.e., a rule for "case-split on a
comparison, then show non-interference holds no matter which branch,"
distinct from the current "prove the comparison is public first" rule. Not
attempted; likely a real (if modest) extension to the relop/`secLeak`
model in `Contracts.v`, not just a new example.

**MILESTONE (2026-07-04): genuine LOAD-of-secret verified.** `cin`, scratch
registers, AND the `x`/`y` data are now all **private** (`r` private too);
only addresses (hardcoded right after the code, see Priority 1) are public.
The secret words loaded from memory flow through `fun_extend_value`'s union
match `KMemValue (pat_var "result")` with NO `secLeak` on the loaded word —
this is the payoff of the method-Y pattern-match rework (see "Pattern-match
secLeak — RESOLVED" below). `Print Assumptions cmovznz4_noninterferent` shows
only the two standard framework model parameters (`Machine.pure_decode`,
`Base.mmioenv`); the non-interference statement, operational semantics, and
step relation were verified unchanged. Commits `f90a607e` (TCB rule),
`03582316` (`read_ram_sound` fix), `88c947bb` (secret x/y).

A script at `case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` mechanically
translates RV32I assembly (as pasted from Compiler Explorer) into the `list
AST` Coq literal, tagging each entry with its source line for auditability —
use it for future examples instead of hand-transcribing.

---

## TODO list

**Open items from the 2026-10-08 learning session, grouped (Emiel asked which
belong together). Order: D's relval-pair item → A+B → E → C → F's merge gate;
G and the rest of F anywhere.**
- **I. Loop-rule audit findings (2026-10-15 reading quiz, branch
  `issue/loop-rule`, before merge).** Options, not decisions.
  - **I1. The loop head is implicit.** `Verifier.is_head` (`Verifier.v:1082`)
    takes the head to be the table's FIRST key. That is the placement only
    because `CFG_VC_loop_triple` builds the table as `table_of_list p 0 i`
    (`Contracts.v:221`), and offset 0 comes first and collapses to `p`
    (`Tables.v:337`). Emiel: "brittle ... there is no real guarantee that the
    first instruction is the head, except that we always do it this way."
    Soundness does NOT depend on it: `rexFS` only uses that a head hit is a
    lookup hit (`is_head_lookup`), and the meaning "head = placement" comes
    from `loop_post`'s pc equation `an = p`; a wrong head makes the VC fail,
    never pass. So it is a readability/robustness issue. Options: (a) pass
    the head term (the placement) to `sexec_cfg_addr` explicitly instead of
    reading it off the table, persisted like `exits`; (b) compare against the
    entry pc `"a"` (might also make the `Hpl` placement premise of
    `blockSound_of_loop_vc` unnecessary, since `loop_post` could then say
    `an = a`; unverified); (c) keep, with a stronger comment.
  - **I2. "Where did the run stop" is carried two ways.** An ordinary
    contract carries it in the executor: the concrete stop guard
    `negb first && (loop || exit_hit cexit v)` (`VerifierRel.v:356–358`) and
    the fact `(loop || exit_hit ..) = true` that `sound_exec_cfg_addr_myWP2`
    hands its continuation (`Adequacy.v:1647`). A loop contract carries it in
    its post: `loop_post`'s pc equations `an = ex` / `an = p`
    (`Contracts.v:200–212`), read back in `blockSound_of_loop_vc` as
    `%Hex`/`%Hhd`; there the executor's fact is just `true`. Option: one
    mechanism for both, i.e. every contract's VC consumes a post carrying
    `an = exit`, and `exit_hit` leaves the concrete stop guard (which becomes
    `negb first`). Larger change, touches the non-loop soundness chain;
    unverified. Option: keep (two mechanisms, each local).
  - **I3. `loop_post`'s substitutions are unreadable.** Emiel: "I have no
    idea what wk or wk_a_an are." `wk_a_an : Sub Σ (Σ ▻ a ▻ an)` is the
    weakening into the post's context (`Contracts.v:197`), `wk t` applies it
    (`:205`), and `env.snoc wk_a_an "a" (term_var "an")` (`:211–212`) is
    "rebind a to an", i.e. Inv[a := an]; none of the three is explained at
    the point of use. Options: rename (e.g. `to_post_ctx`, `a_to_an`) and
    name the second substitution; a one-line comment per substitution;
    check whether the framework already has a two-step weakening to reuse.
  - **I4. `myWP2_step` duplicates `myWP2_loop_fix`'s step disjunct.** Emiel:
    "Why does myWP2_step exist? Is it not just the same as myWP2_loop?"
    `myWP2_step E` (`Adequacy.v:218`) copies the right disjunct of
    `myWP2_loop_fix` (`:111–124`) with `wp := myWP2_loop E`, so the reader
    must diff them by eye. Options: define one step combinator
    (`step_then wp`) and write `myWP2_loop_fix E wp := E ∨ step_then wp` and
    `myWP2_step E := step_then (myWP2_loop E)` (the Contractive proof must
    still go through); or keep, with a comment at both definitions naming
    the other.
  - **I5. The loop rule's proof is hard to read.** Emiel: "The proof of the
    loop rule is a little bit too chaotic." `blockSound_of_loop_vc`
    (`Adequacy.v:2158–2230`): its signature is mostly fully qualified paths
    (`Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition
    (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)` ...), and the proof
    restates the precondition in two `iAssert`s just to read a pure fact
    without consuming it. Options: short local names for the contract's
    fields (`pre b`, `post b`, `exit b`, `place b`) or importing the modules
    so the paths shrink; a lemma "pure fact from a persistent wand, keep the
    hypothesis" instead of the two `iAssert`s; the five-step outline
    (placement, faithfulness, run once, bind under ▷, case split) as
    comments at each step. The qualified-path part is now I6.
  - **I6. DECIDED (direction): import properly, no fully qualified
    prefixes, codebase-wide.** Emiel, 2026-10-15: "for readibility, we should
    avoid using things like this an instead import them properly. This
    holds for the whole codebase actually." Census (non-ZZ `.v`,
    `Katamaran.RiscvPmp.CFGVer.{Verifier,VerifierRel,Tables,Contracts,
    TablesRel}.`): Adequacy 192, SpecIris 51, GenCompose 23, VerifierRel 12,
    EndToEnd 10, TwoLoopsComposedResult 8, TablesRel 6, Swap/Countdown-
    ComposedResult 4 each, Contracts 2; `theories/` not yet surveyed. The
    original reason for qualifying is `CFGVer/CLAUDE.md` "Importing
    CFGVer.Verifier downstream": a name clash with BlockVer. BlockVer is out
    of the build (`_CoqProject:10–19`, zero active BlockVer lines), and the
    note itself says to switch to `Require Import` once BlockVer is gone, so
    the clash is moot; delete that note (and the skills' copies) with the
    fix. Watch for: new clashes between CFGVer modules once imported
    together, and the light/heavy layering (an Import never adds a Require,
    so layering is unaffected). Plan with Emiel before starting.
  - **I7. Three loop/non-loop wrapper pairs could collapse into one.**
    `blockSound_of_[loop_]contract` (`GenCompose.v:469/485`),
    `blkValid_of_[loop_]contract` (`:2217/2236`), `blkValid_of_[loop_]seg`
    (`:2260/2285`) differ only in the VC (`cfg_vc` vs `cfg_vc_loop`) and the
    loop's `Hpl` placement premise (free for generated segments, via
    `seg_pre_placement`). Emiel: "This collapsing would definitely be
    useful." Option: verify every BLOCK with `cfg_vc_loop` and drop the
    non-loop half. Sound for every contract (the loop rule is its proof).
    Price: a block whose run passes back through its own first instruction
    with the pre FALSE there (a loop verified by unrolling, pre pinning the
    trip count) is rejected by `cfg_vc_loop` and accepted by `cfg_vc`.
    UNVERIFIED: whether any current block relies on that; check by running
    each block's VC as a loop VC. Top-level programs stay on `cfg_vc` (the
    seal, `Validity.v`). Also price the disjunctive post (`asn.or`) and the
    per-step `is_head` test on the large blocks (muladd tail, `sym6`).
- **A + B: IMPLEMENTED 2026-10-09 on `issue/spec-layer`** (all phases, all
  18 Result files compile; NOT merged — waiting on Emiel's audit/read-through
  and the merge comprehension check). Implementation-time decisions:
  PLAN-spec-layer §2a.7. Still open from A: the frontmatter descriptions of
  `cfgver-gen-contract`/`cfgver-memory` (hook-gated). Decode assumption: no
  action (D13). The Priority-0 notes below are now HISTORY.
- **A. Spec-layer redesign — ONE pass** (`plans/PLAN-spec-layer.md`): sum type,
  `Reg` keys, mem plumbing, one word predicate, `concretize_data`/`data_ok`,
  visible checks, trusted-file comments. Together because the design
  decisions interlock and every item rewrites `Noninterference.v`, the
  `EndToEnd.v` bridges, the front-ends and all 21 Result statements.
- **B. Trusted-program readability — bundled into A's Phase 4**: literal
  `sym6_instrs` (no `set_nth` patch-of-a-patch, no `zz` name), exit as
  `init_addr + 4 * length instrs`, stale `MuladdParamResult.v` header.
  Logically orthogonal, but each changes a Result statement and A reviews
  them all anyway — a separate pass costs a second review + gate.
- **C. End-theorem proof automation — AFTER A**: `_simple` bridge for mixed
  front-ends + `data_spec`, one generic bv tactic, what the ~60 lines of
  `check_scalar_ptr_noninterferent` do (85 lines on issue/spec-layer;
  Emiel 2026-10-09: "still way too long, we should clean this up"). After, because A's Phase 2 rewrites
  these bridges.
- **D. Audit of past changes — independent** (agent findings, UNVERIFIED;
  `.claude/learning/commit-groups.md`): `1236c880` `fun_bool_to_bits`
  deviates from Sail (`Machine.v:620`); `27a2fd1a`/`af2a1187` changed example
  PROGRAMS; `0bc112da` changed swap/jmp_fwd/countdown_mem statements
  (`scripts/stmtdiff.py` confirms they changed; possibly just register
  aliases — check); 3 `Admitted` in `theories/` from the unquantify port;
  composed Result files are Iris-level statements on the axiom-clean list.
  relval-pair's "meaning changed" list stays with that branch (Emiel,
  2026-10-08: relval-pair parked on its branch; A is based on KatamaranRel).
- **E. Docs — in A's last commit**: CFGVer/CLAUDE.md's trusted-surface list
  misses `Tables.v` register names and `GenSegment`'s `concretize_*`
  (both are in end-theorem statements, per dpdgraph); grep skills for names
  A renames. Anytime: delete the dead `declare_public_registers` in
  `BlockVer/Examples.v:1477`.
- **F. Learning tooling**: merge-time comprehension gate (after A, its first
  use; touches load-bearing `git-workflow-guard.sh`); PocketFlow-style pilot
  on loop invariants (measure tokens first); decide whether
  `.claude/wyw.json` is committed or gitignored before writing a deck.
- **G. Small suspicions (UNVERIFIED)**: `.gitignore` ignores `Example/ZZ*`
  but not `Example/Muladd/ZZ*` / `Example/CheckScalar/ZZ*` (untracked probes
  show in `git status`); if `scripts/gate.sh`'s hole scan reads subdirectories
  of the filesystem, an untracked `Admitted` probe there could block the gate.
  The rocq `guardrails.sh` false positive on `checkout -- .` recurred.
- **H. Spec-layer readability — reading quiz 4 (2026-10-09, Emiel, on
  `issue/spec-layer`). Options only, NOT decided. Priority (Emiel): the
  DE-CLUTTER item is HIGH; every other bullet here is LOW:**
  - [LOW] `is_gpr` (`Noninterference.v:118`) packs into `existT` only because the
    sole register EqDec is `𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg)` (`Base.v:1064`).
    Options: an `EqDecision (Reg ty_xlenbits)` instance outside the kernel; a
    direct `match` rejecting pc/nextpc/mtvec/...; a 31-constructor `gpr` enum.
  - [LOW] `mem_cell` (`:219`) should carry an `Addr` (`Base.v:74`), not N — every
    consumer does `bv.of_N` (`:247`, `:273`); N is only needed for the block
    overlap test (`:198`).
  - **[HIGH]** De-clutter `noninterferent_strong` (`:355–360`): replace the 8
    `declare_*`/`gen_*` premises by two relational predicates
    (`regs_sat γ1 γ2 reg_specs`, `mem_sat μ1 μ2 mem`, matching on
    Secret/Public/Known directly) so no `gen_*` is on the trusted surface. Folded in (Emiel): this also
    merges `gen_public_addrs`/`gen_init_mem` (and the reg pair) and counts
    `Known` as public (already implied — make it said).
  - **TODO** (quiz 5, 2026-10-12) Make `ni_cells` (`EndToEnd.v:1747`)
    consistent with `noninterferent_strong`: it still states the OLD shape
    (eight `declare_*`/`gen_*` premises) and every bridge concludes it
    (8 `gen_contract_noninterferent_*` + `GenProg.gen_prog_noninterferent`);
    `ni_of_cells` translates at all 21 Result call sites. Option: restate it
    with `regs_sat γ1 γ2 regs'` / `cells_sat μ1 μ2 cs`, so `ni_of_cells` only
    permutes (+ `mem_sat_cells`) and the `declare_*` conversion moves inside
    the bridges (where the Iris side needs it anyway).
  - **TODO** [LOW] (quiz 5, 2026-10-12) `words_sat` reads words with the kernel's own
    `get_word`; `get_word_read_ram` (`Noninterference.v:154`) proves it equals
    the machine's load `fun_read_ram μ 4 a`. Option: state `words_sat` with
    `fun_read_ram` directly, so the statement trusts the Sail-derived reader
    instead of a second definition.
  - **TODO** (quiz 5 Q2, 2026-10-12) `check_scalar_ptr_noninterferent` has shape
    `in_range … → in_range … ∧ NI`, so its conjunct guards nothing, and unlike
    cmovznz4 (`_noninterferent`/`_at_start` at ia = 0/256) it has NO
    premise-free sanity instance: nothing shows its premise is ever
    satisfiable. Add one (e.g. ia = 0, ka = 176, l = 32). General rule: a
    parametric Result's conjuncts only guard in its premise-free instances.
  - [LOW] **Split statement data from proof data** (reopens D12): `Secret` entries
    are statement-level no-ops (registers: exactly; memory: they only feed
    `fits` and placement — cmovznz4's layout says only "code+48 bytes fits").
    They exist so D12's EQUALITY with the generator's specs holds. Option:
    statement lists only Public/Known; proof shows generator ⊇ statement with
    the rest Secret. Open (unverified): the proof likely still needs the
    working area below lenAddr, so a footprint/size premise may remain.
  - [LOW] Register pointers are literals independent of the layout (cmovznz4
    `A2 := ia+132`; muladd `A2/X2 := ia+1144` must hit m's `Known b` header):
    only the proof-side `*_cells` lemma ties them; the statement does not.
  - [LOW] Registers as a PARTIAL MAP `gpr ⇀ val_spec` (Emiel), absent =
    Secret: duplicate keys become unwritable (today `[(A0, Known 1); (A0,
    Known 2)]` is a writable VACUOUS statement — the bridges' NoDup premise
    does not protect the statement, a hand proof could exploit it; memory
    already has `blocks_ok`) and the all-Secret padding disappears.
  - [LOW] Wrap-around (quiz Q3): `blocks_disjoint`/`clear_of_code` are in N
    but memory is read via `bv.of_N` (mod 2^32), so blocks at a and a+2^32
    alias; conflicting Known words there (or vs. the code) = VACUOUS. Today
    prevented only by each Result's own lenAddr premises — `fits`, or in
    CheckScalarPtr two raw `< lenAddr` lines (`CheckScalarPtrResult.v:116-117`),
    which Emiel finds uninsightful: use a fits-style predicate there. Option:
    a kernel-level in-range predicate over a `mem_layout` (every block_end
    and the code end < lenAddr) — as a CONJUNCT of `noninterferent_strong`
    (D19 style: out of range ⇒ unprovable, not vacuous), with `Layout.fits`
    implying it.
  - [LOW] `Bytes (n) (s : val_spec Empty_set)` + `match e with end`
    (`Layout.v:38,56`) is a typing trick for "Secret|Public only"; a
    dedicated 2-constructor type would say it directly. Also P256_N is
    `Bytes 32 Secret` in CheckScalarParam but `repeat Secret 8` words in
    CheckScalarPtr — one footprint, two spellings.
  - [LOW] Real NON-VACUITY check (Emiel, quiz Q5): the `_noninterferent` /
    `_at_start` instances only show the `fits` premise is satisfiable (sanity
    for the parametric base — their comment "so it is not vacuous"
    OVERCLAIMS). Option: a lemma `∃ γ1 γ2 μ1 μ2 ws, <all premises>`. Blocked
    in part by `Axiom pure_decode` (`Machine.v:147`): `mem_has_instrs` is
    unprovable in Coq without it, so state it RELATIVE to
    `Forall (fun i => ∃ w, pure_decode w = inr i) instrs` — which makes D13's
    informal "decodable by construction" an explicit hypothesis. Satisfiable
    premises still allow a trivial theorem (world 1 takes 0 steps); a run
    reaching the exit cannot be exhibited while decode is an axiom.

**Priority 0 — simplify the trusted statement's spec plumbing (2026-10-08,
from Emiel's reading session on `Noninterference.v`; do it RIGHT AFTER that
session, planned WITH Emiel — design decisions are his). NOW A PLAN:
`case_study/RiscvPmp/CFGVer/plans/PLAN-spec-layer.md` — start at its Phase 0;
the notes below are its source material:**
- **Registers (urgent).** `noninterferent_strong` (`Noninterference.v:261`)
  goes spec `RegIdx` → `reg_convert` (`Base.v:1019`, `option (Reg ty_xlenbits)`)
  → `existT` into `{x : Ty & Reg x}` (`gen_public_regs`, `:109`) → unpacked
  again in `declare_public_registers` (`:250`). The sigma-typed list is BlockVer
  heritage; every CFGVer register here is `ty_xlenbits`. `reg_convert 00000 =
  None`, so an `X0` spec is silently dropped by both `gen_public_regs` and
  `gen_init_regs` (safe direction — drops a hypothesis — but invisible).
  Users: `Noninterference.v`, `EndToEnd.v` only. Dead duplicate
  `declare_public_registers` in `BlockVer/Examples.v:1477` (outside
  `_CoqProject`) — delete or ignore, it confuses grep.
- **Memory (less urgent).** `mem_spec = (addr, pub)` (`:140`) survives only so
  `gen_full_public_addrs` can drop `mem_full_spec`'s init field and call the
  old `gen_public_addrs` (`:179`). WIDER reach than the register side: the
  proof chain is stated in `mem_spec` (`EndToEnd.v`, `Adequacy.v`,
  `GenProg.v`, `GenContract.v`, `Example/BearSSLCheckScalarLoop1.v`, and the
  proof bodies of `MuladdParamResult`/`CheckScalarParamResult` pass
  `map mem_full_to_spec`).
- **Shared implications** (decide whether to bundle): both change the trusted
  `Noninterference.v` and the `EndToEnd.v` bridges, so both need the same
  statement review + full gate; the Result statements name only
  `noninterferent_strong` + spec lists, so they likely stay textually
  unchanged — CHECK (a `reg_spec` type change would show there).
- **Design question for the same pass:** a spec `(r, false, Some v)` reads as
  "r secret" but is effectively public (both worlds are forced to `v`,
  `:272–273`). Goal per Emiel: as few confusing conversions as possible on the
  trusted statement, which must stay easily readable — consider a spec shape
  where this misleading combination is unrepresentable. LIVE INSTANCE in a
  trusted statement: `cmovznz4_reg_specs_rel` (`Example/Cmovznz4.v:181–183`)
  flags the pointer registers A1–A3 `false` with `PVBaseOff 116/132/148` —
  public (init_addr + k in both worlds) while reading as secret. Use it as
  PLAN-spec-layer's Phase 0 before/after example. Emiel's constraint: a
  well-formedness PREMISE is no fix — a spec failing it makes the end theorem
  vacuously true. Candidates: (a) a sum type `Secret | Public | Known v`
  (nothing to check), (b) a decidable check proved as a CONJUNCT of the end
  theorem (`wf_specs = true ∧ noninterferent_strong …`, closed by
  `reflexivity`) so a bad spec makes it unprovable, not vacuous.
- **DECIDED (Emiel, 2026-10-08): sum type, for BOTH registers and memory, done
  in the same pass as the register + memory plumbing cleanups** (one statement
  review, one gate).
- **Duplicate machinery (Emiel):** `get_word` (`:133`, functional) and
  `mem_has_word` (`:118`, existential over 4 bytes via `bv.seqBv a 4`) serve
  the same purpose — public/init memory uses the first, code uses the second.
  Unify. The trusted file still carries an unanswered `(* byte order correct? *)`
  at `:121`; settle it in the same pass (the end-to-end proof forces
  consistency with the model's fetch; whether that is real RISC-V
  little-endian is a model question — check `bv.app`'s bit order).
- **Vacuity (from the reading session):** hypotheses that can be jointly
  unsatisfiable make an end theorem true for free — data overlapping code with
  a different value, a register/address given two different init values, and
  overlaps at BYTE level (a word spec at `a` and one at `a+2` share bytes), not
  just equal addresses. Consider a consistency check proved as a conjunct (same
  shape as option (b) above) or a per-Result non-vacuity witness. Emiel: an
  over-strict check is fine ("not allowing some legitimate but fishy
  behaviour"). NOT an alignment requirement — Emiel removed one before and
  does not want it back; BRAINSTORM the overlap check with him. Likely reason
  for the removal (unconfirmed): byte-granular data cells,
  `plans/PLAN-byte-memory.md` (1c69aa4b) — check_scalar's byte arrays.
- **X0 unrepresentable by type (Emiel):** key register specs by the machine's
  `Reg ty_xlenbits` (x1..x31, no x0) instead of `RegIdx`. That also removes
  `reg_convert` from the statement — same change as the plumbing cleanup.
  Cost: `Tables.v`'s `A0`/`T0`/… aliases are `RegIdx`; spec authors need
  `Reg`-level names.
- **State the decode trust assumption:** `pure_decode` is an `Axiom`
  (`Machine.v:147`, allow-listed in `scripts/gate.sh:277`), so nothing in Coq
  says a hand-written `instrs` is in the real decoder's image; if one AST has
  no encoding, no `ws` satisfies `:268` and the end theorem is vacuous for the
  real machine. Unfixable while decode is axiomatized — say it in a comment
  next to `noninterferent_strong`, so the trusted file states its assumptions.
- **Muladd's statement is not readable (reading quiz 2, 2026-10-08).** Feeds
  PLAN-spec-layer Phase 0; options only, Emiel decides:
  - `sym6_instrs := mb_instrs := set_nth 13 … (set_nth 132 … zzmuladdfulln2_instrs)`
    (`Example/Muladd/MuladdParamInstrs.v:356`): the probe-era list had two
    loop-count immediates patched 32→3 (PLAN-muladd-full deviation 3), and
    `set_nth` patches them BACK (PLAN-muladd-composed.md:90–95). The trusted
    program should be one literal list, with a non-`zz` name.
  - The exit address is the literal `init_addr + 1128`; CheckScalarPtrResult
    writes `init_addr + 4 * N.of_nat (length cs_instrs)`, which explains itself.
  - `A0` is hand-concretized and consed onto the rest (`sym_reg_specs`,
    `MuladdParamResult.v:299`) because `PVBaseOff k` only takes a CONSTANT k,
    and x's address `x_off b = 1148 + 4·mlenN b` depends on m's length.
  - `b` is BearSSL's ENCODED announced bit length, not a bit length
    (reading quiz 3; BearSSL `inner.h`: k is stored as
    `((k / 31) << 5) + (k % 31)`; checked via a GitHub mirror, not in-repo).
    So M = (b+31)>>5 is the limb count and mblr = b & 31 = k mod 31. Repo
    comments call it "bitlen" (`MuladdParamInstrs.v:317,325`,
    PLAN-muladd-full). The flat specs pin it to 63, whose low 5 bits are 31:
    NOT a valid encoding (no k produces it) — only in leftover definitions
    (`zzmuladdfulln2_{x,m}_specs_rel`) and the ZZ probe, no tracked end
    theorem. The parametric `64 < b < 65536` also admits invalid encodings:
    a harmless over-approximation (strictly more inputs), but worth a comment.
  - The verified property is WEAKER than BearSSL's documented contract for
    muladd (`inner.h`: "CT: only the common announced bit length of x and m
    leaks, not the values of x, z or m"). Ours makes m's limbs PUBLIC
    (`DArr true …`, `MuladdParam.v:72–73`). Options, Emiel decides: keep
    (modulus public is the usual threat model; say so in the Result
    header), or try m's limbs secret (b0 = m's top limbs feeds br_divrem —
    expect the secret-data walls).
  - x's address is stated THREE times (reading quiz 3, 2026-10-08):
    `DAt (term_var "x")` in `sym_data` (`MuladdParam.v:74`), `x ↦ ia + x_off b`
    in `sym_ι` (`MuladdParamResult.v:294`), and `(A0, true, Some (ia + x_off b))`
    in `sym_reg_specs` (`:300`). Only `data_ok`'s `DAt` case ties them
    together (proved in `sym_data_ok`); the statement shows the last two.
  - Statement-level no-ops: `DAt x` (skipped by `concretize_data`, means
    something only in `data_ok`) and `arr_dir` (`DArr pub _ c`). A reader
    sees them in the trusted spec list and assumes they constrain something.
  - `data_ok` (`GenSegment.v:1941` on KatamaranRel) mixes six concerns: per-cell range,
    pinned ⇒ public, pinned value and counts Sync, the `DAt` anchor, `DPtr`
    continuation, byte-vs-word bound. It is a bridge premise (`GenProg.v:111`)
    proved per Result, so `DCell false (Some t)` is UNPROVABLE (good, not
    vacuous) — the rule the rel/q front-ends lack, but enforced late.
  - Proof size vs `InvMixColumnsResult.v` (72 lines): ~140 lines of block
    validity + seal (heavy, so cannot live in the light example file), ~75
    lines of bv arithmetic for the symbolic sizes, and a manual `eapply` with
    an explicit valuation because no `_simple` bridge exists for mixed
    front-ends + `data_spec`. The last two are automation gaps. Emiel: the bv
    arithmetic "should be easy to resolve by using ring or by transporting it
    to a domain where lia works" — i.e. one generic tactic, not ~13
    hand-proved lemmas (check bv-pitfalls for the existing lia/2^32 traps).
  - Stale header: `MuladdParamResult.v:3` still says "Untracked probe".
  - **check_scalar too** (reading quiz 2): `CheckScalarPtrResult.v` 149 lines
    (end theorem ~60, `:87–149`), `CheckScalarParamResult.v` 266 — ~20× the
    InvMixColumns pattern although Ptr already uses the generator bridge.
    Find what the remaining 60 lines do; aim for the `_simple` shape.
  - **Deep vs shallow specs in the STATEMENT (Emiel: "valuation +
    concretize_data is very complex"):** the deep form (`Term`s + a
    `Valuation` of `RelVal`s, `csp_ι`) IS needed by the generator — it is what
    expresses an independent pointer (`DPtr`, `ka`) and symbolic sizes, which
    `PVBaseOff` (constant offset from the one base) cannot. But the trusted
    statement could take a SHALLOW spec (Coq functions of `ia`, `ka`, `l`)
    with a proved correspondence to the deep one. Candidate for
    PLAN-spec-layer Q1.
  - Outer premises on parameters (CheckScalarPtr's `ka … ≤ init_addr ∨
    init_addr + 176 ≤ ka`) are LEGITIMATE scope, unlike D5's premise on
    fixed specs: visible, checkable as satisfiable, and exactly the
    code+P256_N region. Evidence for Q4 option (c).
- **Doc fix, same file:** the comment on `noninterferent_strong` (`:258–260`)
  says "if world 1 reaches the exit address in n steps", but
  `RiscVNStepsWithExitCond` has a `refl` constructor and only checks the exit
  test BEFORE each step, so the theorem covers EVERY n-step prefix that has
  not yet hit the exit — including prefixes of non-terminating runs. The
  statement is stronger than its comment; the comment should say so.

**Priority 1 — pointer-argument memory ownership (init_addr parameterization**
**itself is done; see `project-init-addr-param`/`project-cfgver-symbolic-base-poc`**
**memory — this is a separate, still-open problem):**
- Note: we did NOT move from instruction lists to address maps; lists are
  fine — the table-of-terms design (`table_of_list`, **cfgver-executor**)
  handles the symbolic-base dispatch instead.
- **STILL OPEN — pointer-argument memory ownership is a DIFFERENT, narrower**
  **problem than the base parameterization above, and `cmovznz4_param` does**
  **NOT demonstrate it.** `cmovznz4_param` generalizes the CODE's own load
  address to a free variable `p`, but its data words (x/y/r) still sit at
  `p+116`/`p+132`/`p+148` — a `PVBaseOff k` spec, where `k` is a LITERAL
  offset baked into the contract at authoring time, i.e. still just a term
  built from the same single free variable `p`. That models "data statically
  co-located with the code at a fixed displacement" (position-independent
  code with an adjoining data segment) — it does NOT model a genuine
  calling-convention pointer argument, where a CALLER passes x/y/r addresses
  that live anywhere in memory, with no fixed relationship to where
  `cmovznz4`'s own code happens to be loaded. Verifying that case needs:
  (a) a FRESH per-pointer-argument symbolic variable (e.g. `Σ = ["p"; "q"]`,
  `q` unrelated to `p` by any literal offset) — every existing generator
  (`gen_contract`/`gen_contract_param`/`gen_contract_rel`) only anchors
  memory specs at a literal address or at `p+k`, never at an independent
  second free variable; (b) a new memory-ownership assertion builder keyed
  off that register's OWN value (`q ↦ₘ v`, both `v` and `q` existential)
  rather than off the code-placement term; (c) a matching TWO-WORLD
  memory-extraction lemma for `gen_contract_noninterferent`, since the
  concrete end-to-end bridge currently only knows how to instantiate ONE
  symbolic quantity (`p ↦ SyncVal (bv.of_N init_addr)`) — a genuine pointer
  argument would need `q` instantiated too (to a caller-chosen address) plus
  a disjointness argument against the code/data region. Sketched and then
  abandoned as out of scope for `cmovznz4` (see commit history around the
  parametric-base work) — still open for a future example that actually
  needs real pointer arguments.

**Cleanup / refactoring:**
- **DONE (BlockVer→CFGVer consolidation):** `CFGVer` no longer shares any
  identifiers, module names, or "block" terminology with `BlockVer` — full
  chain (`Spec.v` → `Results.v`) compiles clean. **Still open:** revisit
  whether `RiscvPmp/BlockVer/` itself can finally be deleted (still used by
  `FemtoKernel.v` directly — check that first).

**From `Verifier.v` inline TODOs — remaining open items** (doc fixes, the
`_tbl`/`SITable`/`SETable`/`Phase1SelfTests` rename work, and the dedupe/
dead-code removal are all DONE and full-compile verified; see git history
if archaeology is needed):
1. Split the `SInstrTable`/gmap/`SExitTable` machinery out into its own
   section, module, or file (explicitly flagged as deserving one).
2. Proof engineering (standalone, can happen last): `rexec_cfg_addr` was not
   written in rsolve style and is suspected to be missing `RefineCompat`
   instances for tables — investigate the gap, then use it as a golf target;
   same root cause is flagged at the `itable_rel_of_faith_forget` call site
   inside that proof.

**Modularity (longer term, discuss with Dominique):**
- ~~Parameterize hardcoded start PC at 0~~ — done for the universal-base case,
  see Priority 1 (the pointer-argument generator there is still open).
- Add exit resources (resources required when reaching the exit condition).
  Subtle: execution must stop *first time* exit condition is reached.
- Ask Dominique or Sander whether `AnnotInstr` is worth looking at.

**Known remaining Admits (expected):**
- `valid_jmp_fwd` (BlockVer): BlockVer cannot handle JAL. Intentional.

**Scattered inline code TODOs (not tracked here before 2026-07-17; low**
**priority, mostly stylistic/organizational — logged per the CLAUDE.md**
**"Where a new piece of knowledge goes" hygiene rule):**
- `Spec.v:205-206` — the commented-out `pmp_entries` definition should
  abstract away its concrete type (look into unions) and enforce a
  length-16-no-duplicates invariant on the list; currently unused/dead.
- `Spec.v:217-219` — the (commented-out) `'*↦ₘ['` notation collides in
  meaning with an existing notation of the same name in `asn.notations`;
  needs resolving before it can be uncommented.
- `Spec.v:237` — several mostly-commented-out `Local Notation`s
  (`asn_pmp_entries`/`asn_pmp_addr_access`/`asn_pmp_access`/etc.) are dead
  weight now that `asn_cur_privilege` is the one actually used; clean up so
  the TODO asking to do this can go away with them.
- `Spec.v:919` — a `read_ram_sound`-adjacent proof dispatches an `emp` goal
  via bare `auto`, with a comment flagging it as unclear *how* it discharges
  (works, but the "several admits for this below" phrasing suggests it dates
  from an admit-filling pass and deserves a cleaner tactic).
- `Spec.v:1039` — inside a commented-out (dead) proof alternative: `solve_bv`
  can't discharge a `bv.ult`-shaped goal needing concrete `minAddr`/`lenAddr`
  facts; flagged as "add simplifying `xlenbits` to `solve_bv`" (a
  `bv-pitfalls`-adjacent tactic gap). Not blocking — the live proof path
  doesn't use this branch.
- `Spec.v:1152` — `contractsSound` is proved by re-deriving through `sound`
  directly; TODO suggests it could instead reuse
  `TValidContractEnvSem_ValidContractEnvSem TcontractsSound` for a possibly
  shorter/more principled proof — golf candidate, unverified whether it
  actually applies.
- `Tables.v:295` — the `JAL`/`NOP`/`LW` AST-builder helpers are defined here
  but flagged to move into `Spec.v` (structural/organizational only).
- `Verifier.v:495` — `peval_eqb_inst` (used by `itable_rel`/`etable_rel`
  faithfulness proofs) is flagged as possibly belonging in
  `Symbolic/PartialEvaluation.v` or an instantiation-lemmas file instead of
  `Verifier.v` — a relocation, not a correctness issue.
- `Results.v:170,182,194` — `jmp_fwd_noninterferent_cfg`/
  `countdown_noninterferent`/`countdown_mem_noninterferent` all discharge
  the `valid_<prog>_cfg_contract` bullet of `eapply gen_contract_noninterferent`
  as step 5 *before* step 4, to dodge a wrong unification that would
  otherwise make step 5 impossible; flagged 3× as something that "probably
  needs handling on a higher level" (i.e. in `gen_contract_noninterferent`'s
  own premise/unification order) rather than worked around per call site.
- `Results.v:196` — `countdown_mem_noninterferent`'s `HDataAddrs` bullet
  hand-case-splits `i` through all 12 indices even though, per its own
  comment, a smaller case-split might suffice; flagged to hide behind a
  tactic or prove generally instead of the copy-pasted N-way pattern (the
  general form of this pattern is already documented under the "gotchas"
  heading elsewhere in this file).
- `Example/Jumps.v:80` — `jump_if_zero_cfg_contract` hardcodes
  `true_offset : bv 13` inside the definition; TODO wants it as an explicit
  parameter (`jump_if_zero (true_offset : bv 13) ...`) for reuse across
  different branch offsets.

## Pattern-match `secLeak` — RESOLVED (2026-07-04, method Y)

**Status: DONE.** Pattern matching used to demand full `secLeak` (both worlds
fully synchronized, `SyncVal`) on the scrutinee, which for `LOAD` forced the
loaded value to be public — the blocker for `cmovznz4` with secret `x`/`y`.
This is now fixed end-to-end via **method Y** and `cmovznz4` verifies with
secret loads (see MILESTONE above). No admits; only the two standard framework
model axioms remain.

**Root cause (for reference).** `secLeak` = fully synchronized, but a pattern
match only needs both worlds to select the *same case* (same constructor); the
payload it binds is a `RelVal` that may legitimately be `NonSyncVal` (differ per
world). `semWP2_pattern_match` already computes the two worlds' cases
independently, so soundness only needs case-agreement, not value sync. The
driving case: every `LOAD` runs `fun_extend_value` (`RiscvPmp/Machine.v:528`),
which matches the `KMemValue (pat_var "result")` union; the secret loaded word
is bound by that inner `pat_var`, and the union constructor is statically known,
so it is safe but the old rule rejected it.

**What method Y did (the axis is UNIQUE-REVERSIBILITY, not control flow):**
`pattern_match_relval` is RAW (`ty.nonsyncNamedEnv`): same-branch `NonSyncVal ⇒
Some (existT pc (nonsyncNamedEnv δ1 δ2))`, different branch ⇒ `None`. The
shallow + symbolic executors fast-path the uniquely-reversible patterns with raw
payloads and **no `secLeak`** (`pat_var`, `pat_unit`, statically-known-`K`
`pat_union` — the cmovznz4-critical one, recursing into its sub-pattern), and
keep `secLeak` as a conservative fallback for the rest (`pat_pair`/`pat_tuple`/
`pat_record` — a coinciding leaf makes `reverse` non-unique — and the genuinely
branching `pat_bool`/`pat_enum`/`pat_sum`/`pat_list`). This is symbolic
*incompleteness* on the fallback shapes, never unsoundness. Files touched:
`Syntax/Patterns.v`, `Shallow/Monads.v`, `Symbolic/Monads.v`,
`Refinement/Monads.v`, `MicroSail/ShallowExecutor.v`, `ShallowSoundness.v`.

**TCB rule also weakened (this session).** `Sep/Hoare.v` `rule_stm_pattern_match`
premise went from `⌜secLeak rv⌝` to `⌜is_Some (pattern_match_relval pat rv)⌝`,
and the continuation now carries the original `rv` + an equality hypothesis
(NOT a reversed payload — `reverse` is not a left inverse on the empty-context
`NonSyncVal v v` contamination case). New projection lemmas
`pattern_match_relval_projLeft/projRight` (`Patterns.v`) let
`iris_rule_stm_pattern_match` (`Iris/BinaryWeakestPre.v`) reduce the two
per-world matches; `sound_stm` (`Iris/BinaryInstance.v`) bridges the `Triple`
constructor's `->` to the rule's `bi_impl`. The one downstream TCB proof that
broke — `read_ram_sound` (`BlockVer/Spec.v`, whose `read_ram` contract uses
`asn.match_bool inv`) — was fixed by destructing the `pattern_match_relval`
result rather than `inv` itself. Full details in the
`project-pmr-canonicalization` memory note.

**METHOD X (DEFERRED, not needed) — uniform canonicalization.** The principled,
case-split-free alternative (canonicalize `pattern_match_relval` so `secLeak`
becomes *exact*). Doesn't localize: it cascades down to canonicalizing the
concrete RelVal algebra (`liftBinOp`/`liftUnOp`/`evalRel`/`inst_term`) — a
foundational trusted-base change, "scope with Dominique." The canon machinery
(`canonNamedEnv`, `canonRelVal`, `canonMatchResultRel`, `canonRelVal_idem`, …)
is left in `Patterns.v` as the base X would build on. Revisit only if we want to
remove the per-pattern case-split and make `secLeak` precise. Full X writeup:
git history around commit `95e2fd54` and the `project-pmr-canonicalization`
memory note.

**Gotchas found while proving `cmovznz4_noninterferent`:**
- `fuel` must exceed the raw instruction count, and it's not obvious by how
  much. Every existing example already had slack (jmp_fwd: 2 instrs/fuel 5,
  swap: 3/5, countdown_mem: 4/10); `cmovznz4` initially used `fuel = 29`
  (exactly the instruction count) and got stuck on a bare `False` VC goal
  deep in the proof that looked like a missing `secLeak` fact but wasn't --
  bumping to `fuel = 35` made it disappear entirely. No documented rule yet
  for how much slack is actually required; worth deriving one (or exposing a
  clearer error) instead of trial-and-error next time.
- `gen_contract_noninterferent`'s `HDataAddrs` proof obligation must case-split
  on *every* index in `mem_specs`, not just index 0 -- the pattern in
  `countdown_mem_noninterferent` (`intros [|i] ...`) only works because that
  example has exactly one memory entry. Copy-pasting it for a longer
  `mem_specs` list silently breaks (`discriminate` fails on real, in-bounds
  entries): destructure `i` through every concrete index instead, e.g.
  `intros [|[|[|...[|i]...]]] spec H; cbn in H; try (inversion H; subst;
  vm_compute; done); discriminate.` for N entries.

---

## Potential next tasks (not yet approved)

- ~~Prove `jmp_bwd` (backward jump / loop) as a second CFGVer example.~~
  STALE: `countdown`/`countdown_mem` already exercise a backward `BNE` branch
  (see the cfgver hub skill's "Example status") — turned out to need zero
  special handling once the parametric-base machinery was in place.
- The full real `GHASH::key_schedule` loop (128 iterations building the
  256-entry `m_HM` table, not just the single masking step `precompute`
  verifies) is its own open item, separate from the `sltu`/64-bit gap above:
  fully unrolling it (`#pragma clang loop unroll(full)`) produces 4,573
  branch-free instructions (confirmed on Godbolt) — almost certainly too
  large to hand-translate/symbolically-execute in practice. Verifying it as
  a genuine loop instead needs a contract/spec shape for a *symbolic
  iteration count* (CFGVer's existing backward-branch examples all have a
  fixed/concrete trip count baked into the contract, e.g. `countdown`'s
  literal counter value) — a bigger step than reusing the `countdown`
  pattern as-is. Not attempted.
  **Why the concrete-trip-count pattern can't just be scaled up instead —
  CORRECTED DIAGNOSIS (2026-07-19, probe session):** bumping the
  `key_schedule_loop2` (N=2) spike to N=64 via `gen_contract_rel` hits
  `vm_compute` >590s, with ~2-2.5x cost per +1 trip. An earlier same-day
  analysis blamed the core executor's `demonic_finite`/`demonic_pattern_match`
  forking on every BNE revisit — that was WRONG (superseded write-up archived
  in `.claude/archive/term-explosion-diagnosis-correction-2026-07-19.md`).
  A probe chain (memory `project-key-schedule-loop-scaling`) showed:
  concrete-counter backward-branch loops scale fine to 10+ trips in EVERY
  generator (dead forks are pruned at construction — `assume_formula` runs
  `combined_solver` and collapses refuted branches to `SymProp.block`), and
  the store-at-advancing-pointer shape is ~linear. The real mechanism is
  **symbolic term duplication**: the masking body rebuilds the secret `A0`
  from THREE copies of its own previous value each iteration, and the
  executor's register store keeps raw terms with no sharing, so term size
  (and all downstream peval/solver/vm_compute work) grows ~3^trips. Minimal
  pair: `A0 := A0>>1` is flat at 10 trips; `A0 := (A0>>1)^(A0&1)` grows
  ~1.7x/trip. Corrected write-ups: **cfgver-executor** "Backward-branch
  loops" + **core-executor-internals**. A follow-up probe also REFUTED the
  cheap "let-representation" fix (Coq's physical value-sharing saves memory,
  not traversal cost — opacity is what's needed). **Fix plan drafted (not
  started): `CFGVer/plans/PLAN-term-sharing.md`** — selective opaque naming at
  register writes, E1/E2 de-risk experiments first, hash-consing as Plan B. Consequences: (a) full unrolling
  does NOT dodge this — term growth is a property of the instruction
  sequence, not the loop encoding (3^128 either way), so the *symbolic
  iteration count* / loop-invariant redesign above is the only
  contract-level route for the real key_schedule; (b) the framework-level
  alternative is value naming/sharing at register writes (fresh symbolic
  name + defining equation per write, SSA-style — nontrivial because
  `unify_pathcondition` would substitute the definition straight back in
  unless handled), or hash-consing.
- **TODO: tell Dominique (Devriese) and Steven (Keuchel) about the
  term-duplication finding above.** This is a core-framework property
  (`theories/`, the generic executor's symbolic register store), not a
  CFGVer bug: register writes store raw terms with no value naming/sharing,
  so straight-line code that re-references a register k >= 2 times per step
  grows terms geometrically — a classic symbolic-execution engineering
  issue, usually solved SSA-style (fresh symbolic name per write + a
  defining equation) or by hash-consing, either of which means re-verifying
  refinement/soundness for whatever is touched and affects every case
  study. Do NOT report the earlier draft of this message (blind-forking
  choice combinators / missing eager path pruning): probes showed branch
  construction is already effectively pruned (assume/assert run
  `combined_solver` at construction and `block`/`error` refuted branches),
  and the `peval` fast path for `demonic_pattern_match'` floated alongside
  it would be a no-op for this problem. Both superseded write-ups:
  `.claude/archive/term-explosion-diagnosis-correction-2026-07-19.md`.
- Continue with more "Breaking Bad"-style realistic examples now that
  `cmovznz4`/`precompute` established the pattern (register/memory
  reg_specs split into public/private, `asm_to_ast.py` for translation).
  Real pointer arguments are still open -- see the Priority 1 note above --
  but NOTE: that gap is about genuinely caller-chosen, mutually-independent
  addresses; it does not gate examples that (like both existing ones) either
  have no memory at all or hardcode literal/base-relative addresses.
