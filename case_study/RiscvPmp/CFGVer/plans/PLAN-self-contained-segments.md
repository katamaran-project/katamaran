# PLAN — self-contained segments and loops, 2026-09-25

## The principle (Emiel's words)

"Each segment should be verified and their contract should be stated as if
that's the whole program, the rest of the program is not in scope, so
decisions made in the bigger program should not affect the verification or
contract of the segment in any way (it's simple modularity)."

So a segment/loop contract may name: ITS OWN code, ITS OWN code base (a logic
variable), ITS OWN load address, exit targets RELATIVE TO ITSELF, and data on
its own data-base variables. It may NOT name: the enclosing program's list,
an index or byte offset into it (`prog`/`skip`/`take`/`head`), targets
measured from the program's start, or data addresses measured from the
program's code base.

"Where does this segment sit in the program" becomes a COMPOSITION fact,
proved where two contracts are put together, and nowhere else.

Supersedes the narrower "re-base on own code base" of
PLAN-segment-generators.md §3f (which kept `prog`/`skip`/`take`) and the
TODOS.txt item on gen_seg_contract's `+ head`.

## What exists today (measured 2026-09-25)

- `gen_seg_contract base base_a ia head prog skip take targets bound fl regs
  extra_pre post` (GenSegment.v:405): placement `base + of_N head`,
  `cfg_init_addr := ia + head`, pc-eq `a = base_a + of_N head`, code
  `firstn take (skipn skip prog)`, exits `map (t - head) targets`,
  exitCond `seg_exitCond ia targets` (ia = the PROGRAM's load address).
- `LoopSpec` (GenSegment.v:853) carries `loop_prog` (the whole program),
  `loop_first_instr` (an index into it) and `loop_head_addr` (ABSOLUTE);
  `gen_loop_contract` calls gen_seg_contract with head 0 but skip
  `loop_first_instr`, so loops slice the enclosing program too.
- GenCompose.v: ~100 references to head/skip/loop_prog, in the table lemmas
  (instr_table_ok_at, seg_[instr|exit]_table_ok[_at], GenSegTables,
  seg_pre_placement, blockFaithful_of_seg) and the loop chain (LoopPlace,
  loop_one_trip, loop_body/final_trip, loop_enter_from_seg, seg_then_loop,
  loop_by_induction, loop_runs).
- The SOUNDNESS core does not care: `seg_run` (GenCompose.v:306) is generic
  in the gmap `L`/`cbase` it owns. A self-contained segment passes its OWN
  code and base there; the rest of the program's instruction ownership goes
  into the frame `Fr`, split off with `ptsto_instrs_w_split`
  (VerifierRel.v:2726) — the same move blockSound already makes.
- Tracked users: `Example/CountdownRec.v` (+Result) only. No tracked example
  uses LoopSpec / loop_runs.
- Untracked users: 73 probes (80 with their imports). Two families:
  - ALREADY self-contained in spirit — `ZZSegQ*` (+`_bad`), and the block
    probes built on them (`ZZBlk*`, `ZZT*`, `ZZDmp*`): own code, head 0,
    skip 0, take = length, targets relative, own data bases (`mb`, `xb`,
    `sp`). Port = delete arguments.
  - SHARED-BASE muladd chain — `ZZMladDvGen`, `ZZMladDvLoop2`, `ZZMladTail`,
    `ZZEnterFG*`, `ZZTailPorted`, `ZZSpikeA3`, `ZZSpikeEnter2`, the
    `ZZLoop*Probe`s, `ZZDv*`, `ZZAddk*`: program-absolute placement (e.g.
    head 540) and data at `p+1128…`. Port needs per-segment DATA bases
    (§3f Result 3: `X2 ↦ q+96` vs `X2 ↦ r+44` makes iFrame silently do
    nothing). This is the real proof work.

## Target shapes

```coq
Definition gen_seg_contract {Σ} (base : Term Σ ty_xlenbits)
    (base_a : Term (Σ ▻ "a") ty_xlenbits)
    (ia : N)                  (* the SEGMENT's own load address *)
    (code : list AST)         (* the segment's own code *)
    (targets : list N)        (* exit offsets RELATIVE to the segment *)
    (bound : N) (fl : nat) (regs : list reg_spec_rel)
    (extra_pre : …) (post : …) : @CFGVerifierContract Σ :=
  MkCFGVerifierContract ia base (exits_of_offs base targets)
    (asn_pc_eq base_a ∗ gen_base_bound base_a bound ∗ extra_pre ∗ gen_regs_at base_a regs)
    code (seg_exitCond ia targets) fl (post ∗ minimal_pre).
```

- conjunct ORDER of the precondition is kept exactly (consume is
  order-sensitive; the VCs were tuned against it).
- `base`/`base_a` stay two arguments in this pass (weakening is its own TODO,
  ordered after the gen_seg_contract bridge).
- OPEN, decide in Phase 1 by grep: every call site seen has
  `bound = 4 * length code`. If ALL do, derive it and drop the argument; if
  any does not, keep it and record why.

`LoopSpec`: replace `loop_prog` / `loop_first_instr` / `loop_num_instrs` by
`loop_code : list AnnotInstr` (the loop's OWN annotated code);
`loop_head_addr` becomes the loop's own load address. `gen_loop_contract`
calls the new gen_seg_contract on `strip (loop_code ls)`.

Composition side, new: ONE lemma family "segment k..k+n of a program":
`firstn n (skipn k prog) = code` and `pia + 4k = ia` give
(a) `instrs_of_list (of_N ia) code ⊆ instrs_of_list (of_N pia) prog`
    (from Tables.v instrs_of_list_prefix/_suffix + split_id), and
(b) the ptsto_instrs_w split of the program into the segment's span ∗ rest
    (ptsto_instrs_w_split), so the rest can be passed as `Fr` to seg_run.
`seg_placement_ok` shrinks to the segment's own decidable facts
(size ≤ bound, targets well-formed); the head = 4*skip conjunct moves to the
composition lemma.

## SCOPE DECISION (Emiel, 2026-09-25)

"The segments from the muladd program are good enough. Just migrate it,
it's no problem if you break some probes even the muladd ones."
So: core (Phases 1–3) + the eight self-contained muladd segments
`ZZSegQ{A,BC,E,F,H,J,L,N}` (and their `_bad` controls) as the test of the new
generator. Every other probe MAY break and is not ported (block probes,
LoopSpec probes, the ZZMladTail / ZZEnterFG composition chain).
No up-front probe baseline (started, then stopped as not worth its cost). Partial result
before it was stopped, at HEAD acc3a37c: ZZMladCommon, ZZSegQA, ZZSegQBC, ZZTNoBlk,
ZZTBCblk, ZZTBCblk250 green; the old-style muladd loop probes (ZZLoopA/B/TailProbe,
ZZDvLoopSpec, ZZMladSubBody, …) were ALREADY red, still calling the VC by its
pre-2026-09-22 name `ValidCFGVerifierContract` (now `cfg_vc`).

## Phases and gates

- **0. Baseline — DROPPED** (see scope decision).
- **1. Segment generator (light) + its projections.** GenSegment.v:
  new gen_seg_contract, GenSegProjections, seg_placement_ok, and
  gen_loop_contract's call (still passing a slice until Phase 2).
  GATE 1: GenSegment.vo builds; all light files downstream build.
- **2. LoopSpec + loop chain.** GenSegment.v LoopSpec/gen_loop_contract and
  friends; GenCompose.v table lemmas, the new composition lemma family,
  blockFaithful_of_seg, and the loop chain. GATE 2: GenCompose.vo builds.
- **3. Tracked examples.** CountdownRec.v / CountdownRecResult.v on the new
  generator: cd_add0, N.add_0_r and the `+0` placement should disappear.
  GATE 3: `make Results.vo`; Print Assumptions countdown_rec_noninterferent_param
  = pure_decode, mmioenv; scripts/gate.sh at GATE_JOBS=1.
- **4. The muladd segments** `ZZSegQ{A,BC,E,F,H,J,L,N}`: drop the
  `0 … 0 <len>` arguments. GATE 4: all eight `Qed`; each `_bad` control
  still REJECTED.
- **5. Other probes — OUT OF SCOPE** (may break; see scope decision).
- **6. Docs travel with code.** grep skills/CLAUDE.md/memory for
  gen_seg_contract, head, skip, loop_prog, loop_first_instr, seg_placement_ok
  and fix; TODOS.txt: remove the superseded `+ head` item; memory note.

## STATUS 2026-09-25 — phases 1–4 and 6 DONE

- **1+2 together** (they could not be split: deriving the code bound made
  `gen_loop_contract`'s bound `4*|firstn … (skipn …)|` while the loop
  invariant said `loop_code_extent = 4*loop_num_instrs` -- equal, not
  syntactically, and the loop proofs frame these by name).
  - GenSegment.v: `gen_seg_contract base base_a ia code targets fl regs
    extra_pre post`; bound DERIVED (all 11 call sites had bound = 4*|code|).
    `LoopSpec.loop_code` replaces loop_prog/loop_first_instr/loop_num_instrs;
    `loop_code_extent := 4 * |strip (loop_code ls)|`, spelled to match the
    generator's bound syntactically. All projections are eq_refl now.
  - GenCompose.v: `seg_exit_table_ok` is the re-based one (placement ↦ of_N ia;
    old head-shifted form, `_at` and `_head` gone); `GenSegTables`,
    `seg_pre_placement`, `blockFaithful_of_seg` lose head/prog/skip/take/
    bound/Hle. `LoopPlace` DELETED: a loop owns `loop_instr_block` = its own
    code at its own head, and its only placement fact is `Hfit :
    seg_fits_memory (loop_head_addr ls) (loop_code_extent ls)`.
    `loop_enter_from_seg` / `seg_then_loop` take the predecessor's own code
    `Lp`/`cp` and an explicit SPAN SWAP `Hswap : Fin ∗ ptsto(pred span) ⊢
    Fin' ∗ loop_instr_block` -- the composition fact, stated at the cut.
    `seg_instr_table_ok` / `instr_table_ok_at` / `seg_placement_ok` KEPT: they
    are composition lemmas (a slice of a program), not contract fields.
- **3**: CountdownRec.v / CountdownRecResult.v ported; `cd_add0` deleted,
  `N.add_0_r` → `eq_refl`, placement → `reflexivity`. `make Results.vo` green.
- **4**: all eight ZZSegQ{A,BC,E,F,H,J,L,N} `Qed`; all eight `_bad` controls
  REJECTED. Two PRE-EXISTING breakages fixed on the way: E…N (and every
  `_bad`) declared their code `list AnnotInstr` (broken since cfg_instrs became
  `list AST`, 2026-09-22) and E…N stated their VC as `ValidCFGVerifierContract`
  (the pre-rename name). The `_bad` controls were plain `Lemma … Qed` meant
  to break the build -- which the rename had made them do for the WRONG
  reason; they are now `Goal … Fail solve_param_vc. Abort.`, so a green
  compile IS the rejection check.
- **6**: core-executor-internals skill (the `+ of_N 0` history), CFGVer/CLAUDE.md
  file table, TODOS.txt (the `+ head` item → DONE), supersession notes on
  PLAN-segment-generators.md and PLAN-loop-automation.md.
- Not ported, and now certainly broken: every other probe using
  gen_seg_contract / LoopSpec / LoopPlace (block probes, ZZLoop*, ZZDv*,
  ZZMladTail, ZZEnterFG*, …), per the scope decision.

## Out of scope (separate TODOS items)

deriving base_a by weakening; minimal_post; removing blk_off / etable_rel
for blocks; the gen_seg_contract end-to-end bridge.

## Risks

- Conjunct order: kept identical, but the pc-eq term changes from
  `base_a + of_N 0` to `base_a`; peval already folded the `+0`, so the VC
  should be unchanged — if a VC regresses, check this first.
- Probes are untracked: breakage is invisible to git. The baseline table is
  the only record; keep it until Phase 5 is done.
